#!/usr/bin/env python3
"""oran_sfn_from_gps_tool_v8.py

O-RAN CUS (O-RAN.WG4.CUS.0-R003 / ETSI TS 103 859) - SFN/FrameNumber from GPS time
Implements clause 11.7.2 "System frame number calculation from GPS time".

Core equation:
  FrameNumber = floor((GPSseconds - beta*0.01 - alpha/1.2288e9) / 0.01) mod 1024

This version keeps the original CLI + Tk GUI, and adds a **built-in web server** mode.

Web server:
  python oran_sfn_from_gps_tool_v8.py --serve --port 8080
  Open: http://localhost:8080

No external dependencies.
"""

from __future__ import annotations

import argparse
import json
import os
import signal
import textwrap
import threading
from decimal import Decimal, ROUND_FLOOR, getcontext
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import socket
from urllib.parse import parse_qs, urlparse

# Use higher precision to avoid boundary issues around 10ms edges
getcontext().prec = 50

FRAME_PERIOD = Decimal("0.01")              # 10 ms radio frame
MAX_SFN = 1023                               # SFN modulo 1024
MAX_FRAMEID = 255                            # frameId modulo 256 (8-bit)
ALPHA_CLK_HZ = Decimal("1228800000")        # 1.2288e9 Hz, tick = 1/ALPHA_CLK_HZ
UNIX_GPS_EPOCH_DIFF = Decimal("315964800")  # seconds between 1970-01-01 and 1980-01-06
GPS_MINUS_TAI = Decimal("-19")              # GPS = TAI - 19s


def _to_decimal(x) -> Decimal:
    if isinstance(x, Decimal):
        return x
    return Decimal(str(x))


def gps_week_tow_to_gps_seconds(gps_week: int, tow_seconds) -> Decimal:
    """GPSseconds since GPS epoch from (GPS week, TOW seconds)."""
    tow = _to_decimal(tow_seconds)
    return Decimal(gps_week) * Decimal(7 * 24 * 60 * 60) + tow


def ptp_to_gps_seconds(
    ptp_seconds_since_1970,
    ptp_nanoseconds: int = 0,
    ptp_scale: str = "TAI",
    gps_minus_utc_seconds: int = 18,
) -> Decimal:
    """Convert PTP time-of-day (seconds since 1970-01-01) to GPSseconds since GPS epoch.

    - If ptp_scale == "TAI": GPS = TAI - 19s
    - If ptp_scale == "UTC": GPS = UTC + (GPS-UTC)
    """
    sec = _to_decimal(ptp_seconds_since_1970)
    ns = Decimal(ptp_nanoseconds) / Decimal("1e9")
    tod_1970 = sec + ns

    scale = ptp_scale.strip().upper()
    if scale == "TAI":
        gps_tod_1970 = tod_1970 + GPS_MINUS_TAI
    elif scale == "UTC":
        gps_tod_1970 = tod_1970 + Decimal(gps_minus_utc_seconds)
    else:
        raise ValueError("ptp_scale must be 'TAI' or 'UTC'.")

    return gps_tod_1970 - UNIX_GPS_EPOCH_DIFF


def unix_epoch_utc_to_gps_seconds(unix_epoch_seconds_utc, gps_minus_utc_seconds: int = 18) -> Decimal:
    """Convert Unix epoch time in UTC (Wireshark Epoch Arrival Time) to GPSseconds since GPS epoch.

    GPSseconds = (UnixUTC + (GPS-UTC)) - 315964800
    """
    unix_utc = _to_decimal(unix_epoch_seconds_utc)
    gps_tod_1970 = unix_utc + Decimal(gps_minus_utc_seconds)
    return gps_tod_1970 - UNIX_GPS_EPOCH_DIFF


def compute_sfn_from_gps(gps_seconds, alpha_ticks: int = 0, beta_frames: int = 0) -> dict:
    """Compute SFN/frameId from GPSseconds per O-RAN 11.7.2."""
    gps = _to_decimal(gps_seconds)
    alpha_sec = Decimal(alpha_ticks) / ALPHA_CLK_HZ
    beta_sec = Decimal(beta_frames) * FRAME_PERIOD

    shifted = gps - beta_sec - alpha_sec
    abs_frame = int((shifted / FRAME_PERIOD).to_integral_value(rounding=ROUND_FLOOR))
    sfn = abs_frame % (MAX_SFN + 1)
    frame_id = sfn % (MAX_FRAMEID + 1)
    frame_start = Decimal(abs_frame) * FRAME_PERIOD + beta_sec + alpha_sec

    offset = gps - frame_start
    if offset < Decimal("0") and offset > Decimal("-1e-15"):
        offset = Decimal("0")

    return {
        "sfn": sfn,
        "frame_id": frame_id,
        "abs_frame": abs_frame,
        "frame_start_gps_seconds": frame_start,
        "offset_in_frame_seconds": offset,
        "alpha_seconds": alpha_sec,
        "beta_seconds": beta_sec,
    }


def _format_decimal(d: Decimal, places: int = 12) -> str:
    q = Decimal(1) / (Decimal(10) ** places)
    return str(d.quantize(q))


def _compute_subframe(offset_in_frame: Decimal) -> int:
    sf = int((offset_in_frame / Decimal("0.001")).to_integral_value(rounding=ROUND_FLOOR))
    return min(9, max(0, sf))


def _get_first(params: dict, key: str, default=None):
    """Helper for parse_qs dict (values are lists)."""
    if key not in params:
        return default
    v = params[key]
    if isinstance(v, list):
        return v[0] if v else default
    return v


def _validate_inputs(alpha: int, ptp_ns: int | None = None, port: int | None = None) -> None:
    """Minimal sanity checks for numeric ranges."""
    if not (0 <= alpha <= 12_288_000):
        raise ValueError("alpha must be in range 0..12288000.")
    if ptp_ns is not None and not (0 <= ptp_ns <= 999_999_999):
        raise ValueError("ptp_ns must be in range 0..999999999.")
    if port is not None and not (1 <= port <= 65535):
        raise ValueError("port must be in range 1..65535.")


def compute_from_params(params: dict) -> dict:
    """Compute output from web params (or programmatic dict).

    Expected keys:
      mode: one of gps_seconds|unix_epoch|gps_week_tow|ptp
      gps_seconds, epoch_seconds, gps_week, tow, ptp_seconds, ptp_ns, ptp_scale
      alpha, beta, gps_minus_utc
    """
    mode = str(_get_first(params, "mode", "unix_epoch")).strip()
    alpha = int(str(_get_first(params, "alpha", "0")).strip())
    beta = int(str(_get_first(params, "beta", "0")).strip())
    gps_minus_utc = int(str(_get_first(params, "gps_minus_utc", "18")).strip())
    _validate_inputs(alpha=alpha)

    if mode == "gps_seconds":
        gps = _to_decimal(str(_get_first(params, "gps_seconds", "")).strip())
        src_desc = "GPSseconds (direct)"
    elif mode == "unix_epoch":
        epoch = str(_get_first(params, "epoch_seconds", "")).strip()
        gps = unix_epoch_utc_to_gps_seconds(epoch, gps_minus_utc_seconds=gps_minus_utc)
        src_desc = "Unix epoch (UTC)"
    elif mode == "gps_week_tow":
        week = int(str(_get_first(params, "gps_week", "")).strip())
        tow = _to_decimal(str(_get_first(params, "tow", "")).strip())
        gps = gps_week_tow_to_gps_seconds(week, tow)
        src_desc = "GPS week + TOW"
    elif mode == "ptp":
        ptp_sec = _to_decimal(str(_get_first(params, "ptp_seconds", "")).strip())
        ptp_ns = int(str(_get_first(params, "ptp_ns", "0")).strip())
        _validate_inputs(alpha=alpha, ptp_ns=ptp_ns)
        scale = str(_get_first(params, "ptp_scale", "TAI")).strip().upper()
        gps = ptp_to_gps_seconds(ptp_sec, ptp_nanoseconds=ptp_ns, ptp_scale=scale, gps_minus_utc_seconds=gps_minus_utc)
        src_desc = f"PTP time ({scale})"
    else:
        raise ValueError("mode must be one of gps_seconds, unix_epoch, gps_week_tow, ptp")

    out = compute_sfn_from_gps(gps, alpha_ticks=alpha, beta_frames=beta)
    subframe = _compute_subframe(out["offset_in_frame_seconds"])

    return {
        "input": {
            "mode": mode,
            "src_desc": src_desc,
            "alpha": alpha,
            "beta": beta,
            "gps_minus_utc": gps_minus_utc,
        },
        "gps_seconds": str(gps),
        "alpha_seconds": _format_decimal(out["alpha_seconds"]),
        "beta_seconds": _format_decimal(out["beta_seconds"]),
        "abs_frame": out["abs_frame"],
        "sfn": out["sfn"],
        "frame_id": out["frame_id"],
        "frame_start_gps_seconds": _format_decimal(out["frame_start_gps_seconds"]),
        "offset_in_frame_seconds": _format_decimal(out["offset_in_frame_seconds"]),
        "subframe": subframe,
    }


def render_text_block(result: dict) -> str:
    """Human-readable block (same style as CLI)."""
    inp = result["input"]
    return (
        "=== O-RAN SFN from GPS time (11.7.2) ===\n"
        f"Input source: {inp['src_desc']}\n"
        f"Input GPSseconds: {result['gps_seconds']}\n"
        f"alpha ticks: {inp['alpha']}  -> alpha seconds: {result['alpha_seconds']}\n"
        f"beta frames: {inp['beta']}   -> beta seconds: {result['beta_seconds']}\n"
        "---------------------------------------\n"
        f"Absolute frame index: {result['abs_frame']}\n"
        f"SFN (mod 1024):       {result['sfn']}\n"
        f"frameId (mod 256):    {result['frame_id']}\n"
        f"Frame start (GPS s):  {result['frame_start_gps_seconds']}\n"
        f"Offset in frame (s):  {result['offset_in_frame_seconds']}\n"
        f"Subframe (0..9):      {result['subframe']}\n"
    )


HTML_PAGE = """<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>O-RAN SFN from GPS time (11.7.2)</title>
  <style>
    :root {
      --bg: #f4f6fb;
      --panel: #ffffff;
      --ink: #101828;
      --muted: #475467;
      --line: #d0d5dd;
      --accent: #0f172a;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      background: var(--bg);
      color: var(--ink);
      font-family: Inter, ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
      line-height: 1.45;
    }
    .wrap { max-width: 1400px; margin: 0 auto; padding: 24px 20px 40px; }
    .hero {
      background: linear-gradient(120deg, #0f172a, #1d2939);
      color: #f8fafc;
      border-radius: 16px;
      padding: 22px;
      margin-bottom: 18px;
    }
    .hero h1 { margin: 0 0 8px; font-size: 1.4rem; }
    .hero p { margin: 0; color: #cbd5e1; }
    .pill {
      display: inline-block;
      margin-left: 8px;
      padding: 2px 10px;
      border: 1px solid #94a3b8;
      border-radius: 999px;
      font-size: .8rem;
      color: #e2e8f0;
    }
    .layout { display: grid; grid-template-columns: 1fr; gap: 16px; }
    @media (min-width: 1100px) { .layout { grid-template-columns: minmax(760px, 1.75fr) minmax(360px, 0.85fr); gap: 18px; align-items: start; } }
    .card {
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 14px;
      padding: 16px;
      box-shadow: 0 1px 2px rgba(16,24,40,.06);
    }
    @media (min-width: 1100px) {
      .input-card { position: sticky; top: 14px; align-self: start; }
    }
    .result-card { max-width: 520px; width: 100%; justify-self: end; }
    @media (max-width: 1099px) { .result-card { max-width: none; justify-self: stretch; } }
    .card h2 { margin: 0 0 12px; font-size: 1.05rem; }
    .section-title { margin: 12px 0 8px; font-size: .9rem; color: var(--muted); }
    .grid { display: grid; grid-template-columns: 1fr; gap: 10px 12px; }
    @media (min-width: 760px) { .grid.two-col { grid-template-columns: 1fr 1fr; } }
    label { font-size: .88rem; color: var(--muted); display: block; margin-bottom: 4px; }
    input, select {
      width: 100%;
      padding: 10px 11px;
      border: 1px solid #cbd5e1;
      border-radius: 10px;
      background: #fff;
    }
    .muted { color: var(--muted); font-size: .88rem; }
    .actions { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 14px; }
    button {
      border: 1px solid var(--accent);
      border-radius: 10px;
      padding: 10px 14px;
      background: var(--accent);
      color: #fff;
      cursor: pointer;
      font-weight: 600;
    }
    button.secondary { background: #fff; color: var(--accent); }
    button.warn { border-color: #b42318; background: #fff5f5; color: #b42318; }
    .mode-block { display: none; }
    .mode-block.active { display: block; }
    pre {
      margin: 0;
      background: #0b1020;
      color: #e7eaf6;
      padding: 14px;
      border-radius: 12px;
      overflow: auto;
      min-height: 220px;
      max-height: 74vh;
    }
    code { background:#eef2ff; padding: 1px 6px; border-radius: 6px; }
  </style>
</head>
<body>
  <div class="wrap">
    <div class="hero">
      <h1>O-RAN SFN from GPS time <span class="pill">11.7.2</span></h1>
      <p>입력값은 Reset 전까지 유지됩니다. Alpha/Beta를 바꿔가며 반복 계산해서 결과를 빠르게 비교해보세요.</p>
    </div>

    <div class="layout">
      <div class="card input-card">
        <h2>입력 파라미터</h2>
        <form method="GET" action="/" id="calc-form" autocomplete="off">
          <div class="grid two-col">
            <div>
              <label for="mode">Input mode</label>
              <select id="mode" name="mode" onchange="syncMode()">
                <option value="unix_epoch">Unix epoch (UTC)</option>
                <option value="gps_seconds">GPSseconds</option>
                <option value="gps_week_tow">GPS week + TOW</option>
                <option value="ptp">PTP time (TAI/UTC)</option>
              </select>
            </div>
            <div>
              <label>Access token (optional)</label>
              <input name="token" placeholder="Only if server started with --token" />
            </div>
          </div>

          <div class="section-title">Mode-specific inputs</div>
          <div id="mode-unix_epoch" class="mode-block">
            <label>Unix epoch seconds (UTC)</label>
            <input name="epoch_seconds" placeholder="e.g. 1771271246.102474" />
          </div>

          <div id="mode-gps_seconds" class="mode-block">
            <label>GPSseconds (since 1980-01-06)</label>
            <input name="gps_seconds" placeholder="e.g. 1455306464.102474" />
          </div>

          <div id="mode-gps_week_tow" class="mode-block">
            <div class="grid two-col">
              <div>
                <label>GPS week</label>
                <input name="gps_week" placeholder="e.g. 0" />
              </div>
              <div>
                <label>TOW seconds</label>
                <input name="tow" placeholder="e.g. 0" />
              </div>
            </div>
          </div>

          <div id="mode-ptp" class="mode-block">
            <div class="grid two-col">
              <div>
                <label>PTP seconds since 1970</label>
                <input name="ptp_seconds" placeholder="e.g. 1747440512" />
              </div>
              <div>
                <label>PTP nanoseconds</label>
                <input name="ptp_ns" placeholder="e.g. 312144323" />
              </div>
            </div>
            <label style="margin-top:8px">PTP timescale</label>
            <select name="ptp_scale">
              <option value="TAI">TAI</option>
              <option value="UTC">UTC</option>
            </select>
          </div>

          <div class="section-title">Offsets</div>
          <div class="grid two-col">
            <div>
              <label>GPS-UTC (seconds)</label>
              <input name="gps_minus_utc" value="18" />
            </div>
            <div>
              <label>alpha (ticks @ 1.2288 GHz)</label>
              <input name="alpha" value="0" />
            </div>
            <div>
              <label>beta (frames, 10ms units)</label>
              <input name="beta" value="0" />
            </div>
          </div>

          <div class="actions">
            <button type="submit">Compute</button>
            <button class="secondary" type="button" onclick="fillExample()">Fill sample</button>
            <button class="warn" type="button" onclick="resetInputs()">Reset</button>
          </div>
          <p class="muted" style="margin:10px 0 0">API endpoint: <code>/api/compute</code> (GET/POST JSON)</p>
        </form>
      </div>

      <div class="card result-card">
        <h2>결과 / 안내</h2>
        <p class="muted" style="margin-top:0">결과를 확인하면서 왼쪽 입력값(특히 alpha/beta)을 수정해 반복 계산할 수 있습니다.</p>
        %RESULT_BLOCK%
      </div>
    </div>
  </div>

<script>
  const STORAGE_KEY = 'oran-sfn-form-v1';

  function syncMode(){
    const mode = document.getElementById('mode').value;
    document.querySelectorAll('.mode-block').forEach(el => el.classList.remove('active'));
    const active = document.getElementById('mode-' + mode);
    if(active){ active.classList.add('active'); }
  }

  function getFormFields(){
    const form = document.getElementById('calc-form');
    return Array.from(form.querySelectorAll('input[name], select[name]'));
  }

  function saveFormState(){
    const state = {};
    getFormFields().forEach(el => {
      state[el.name] = el.value;
    });
    localStorage.setItem(STORAGE_KEY, JSON.stringify(state));
  }

  function loadFormState(){
    try {
      return JSON.parse(localStorage.getItem(STORAGE_KEY) || '{}');
    } catch (_e) {
      return {};
    }
  }

  function getStateFromQuery(){
    const params = new URLSearchParams(window.location.search);
    const state = {};
    for (const [k, v] of params.entries()) {
      state[k] = v;
    }
    return state;
  }

  function applyState(state){
    const fields = getFormFields();
    fields.forEach(el => {
      if(Object.prototype.hasOwnProperty.call(state, el.name)){
        el.value = state[el.name];
      }
    });
  }

  function attachAutoSave(){
    getFormFields().forEach(el => {
      el.addEventListener('input', saveFormState);
      el.addEventListener('change', saveFormState);
    });
  }

  function fillExample(){
    const form = document.getElementById('calc-form');
    form.mode.value = 'unix_epoch';
    form.epoch_seconds.value = '1771271246.102474';
    form.gps_minus_utc.value = '18';
    form.alpha.value = '0';
    form.beta.value = '0';
    syncMode();
    saveFormState();
  }

  function resetInputs(){
    localStorage.removeItem(STORAGE_KEY);
    window.location.href = '/';
  }

  (function(){
    const urlState = getStateFromQuery();
    const hasQuery = Object.keys(urlState).length > 0;
    if (hasQuery) {
      applyState(urlState);
      saveFormState();
    } else {
      applyState(loadFormState());
    }

    if(!document.getElementById('mode').value){
      document.getElementById('mode').value = 'unix_epoch';
    }
    syncMode();
    attachAutoSave();
  })();
</script>
</body>
</html>
"""


def _html_escape(s: str) -> str:
    return (
        s.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
        .replace("'", "&#39;")
    )


class OranHandler(BaseHTTPRequestHandler):
    server_version = "oran-sfn-web/1.2"

    def _is_authorized(self, qs: dict | None = None, body_params: dict | None = None) -> bool:
        """Optional token-based access control.

        If server.auth_token is set (non-empty), requests must provide the same token via:
          - Query param: token=...
          - Header: X-Auth-Token: ...
          - Header: Authorization: Bearer ...
          - JSON body field: token (for POST)
        """
        token = getattr(self.server, "auth_token", "")
        if not token:
            return True

        # 1) Query string token
        if qs is not None:
            t = _get_first(qs, "token", None)
            if t is not None and str(t) == str(token):
                return True

        # 2) Header token
        hdr = self.headers.get("X-Auth-Token")
        if hdr and hdr == token:
            return True
        auth = self.headers.get("Authorization")
        if auth and auth.lower().startswith("bearer "):
            parts = auth.split(None, 1)
            if len(parts) == 2 and parts[1].strip() == token:
                return True

        # 3) JSON/form body token
        if body_params is not None:
            t2 = body_params.get("token")
            if t2 is not None and str(t2) == str(token):
                return True

        return False

    def _send_unauthorized(self, is_json: bool = False):
        if is_json:
            self._send_json(
                HTTPStatus.UNAUTHORIZED,
                {
                    "error": "unauthorized",
                    "hint": "Provide token via ?token=..., X-Auth-Token, Authorization: Bearer, or JSON field 'token'.",
                },
            )
        else:
            body = (
                "<html><body style='font-family:system-ui; margin:24px'>"
                "<h3>401 Unauthorized</h3>"
                "<p>This server is protected by a token.</p>"
                "<p>Provide it as <code>?token=...</code> or HTTP header <code>X-Auth-Token</code>.</p>"
                "</body></html>"
            ).encode("utf-8")
            self._send(HTTPStatus.UNAUTHORIZED, body)

    def _send(self, status: int, body: bytes, content_type: str = "text/html; charset=utf-8"):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _send_json(self, status: int, obj):
        body = json.dumps(obj, indent=2).encode("utf-8")
        self._send(status, body, "application/json; charset=utf-8")

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path
        qs = parse_qs(parsed.query)

        if not self._is_authorized(qs=qs):
            # For API endpoints return JSON; otherwise HTML
            self._send_unauthorized(is_json=(path == "/api/compute"))
            return

        if path == "/api/compute":
            try:
                result = compute_from_params(qs)
                self._send_json(HTTPStatus.OK, result)
            except Exception as e:
                self._send_json(HTTPStatus.BAD_REQUEST, {"error": str(e)})
            return

        if path != "/":
            self._send(HTTPStatus.NOT_FOUND, b"Not Found", "text/plain; charset=utf-8")
            return

        # Render HTML page; if query provided, compute and show
        result_block = "<pre>입력값을 채운 뒤 Compute를 눌러주세요.</pre>"
        if parsed.query:
            try:
                result = compute_from_params(qs)
                text = render_text_block(result)
                result_block = (
                    f"<pre>{_html_escape(text)}</pre>"
                    "<div class=\"muted\" style=\"margin-top:10px\">Tip: same parameters via API: <code>/api/compute?" + _html_escape(parsed.query) + "</code></div>"
                )
            except Exception as e:
                result_block = (
                    "<div class=\"muted\" style=\"margin-bottom:8px;color:#b42318\">입력 오류가 발생했습니다.</div>"
                    f"<pre>{_html_escape(str(e))}</pre>"
                )

        page = HTML_PAGE.replace("%RESULT_BLOCK%", result_block)
        self._send(HTTPStatus.OK, page.encode("utf-8"))

    def do_POST(self):
        parsed = urlparse(self.path)
        if parsed.path != "/api/compute":
            self._send(HTTPStatus.NOT_FOUND, b"Not Found", "text/plain; charset=utf-8")
            return
        qs = parse_qs(parsed.query)

        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length) if length > 0 else b"{}"
        ctype = (self.headers.get("Content-Type") or "").split(";")[0].strip().lower()

        try:
            payload_dict = {}
            if ctype == "application/json":
                payload_dict = json.loads(raw.decode("utf-8"))
                if not isinstance(payload_dict, dict):
                    raise ValueError("JSON body must be an object.")
                # convert to parse_qs-like mapping for reuse
                params = {k: [str(v)] for k, v in payload_dict.items()}
            else:
                # also accept application/x-www-form-urlencoded
                params = parse_qs(raw.decode("utf-8"))
                payload_dict = {k: (v[0] if isinstance(v, list) and v else v) for k, v in params.items()}

            if not self._is_authorized(qs=qs, body_params=payload_dict):
                self._send_unauthorized(is_json=True)
                return

            result = compute_from_params(params)
            self._send_json(HTTPStatus.OK, result)
        except Exception as e:
            self._send_json(HTTPStatus.BAD_REQUEST, {"error": str(e)})

    def log_message(self, fmt, *args):
        # Keep logs concise
        msg = fmt % args
        print(f"[{self.address_string()}] {msg}")


def _guess_lan_ip() -> str:
    """Best-effort LAN IP detection for printing a helpful URL."""
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            # No packets are actually sent; connect() just selects an egress interface.
            s.connect(("8.8.8.8", 80))
            return s.getsockname()[0]
    except Exception:
        try:
            return socket.gethostbyname(socket.gethostname())
        except Exception:
            return "127.0.0.1"


def run_server(host: str, port: int, token: str = "", pidfile: str = "") -> None:
    # ThreadingHTTPServer already supports concurrent requests.
    # Allow quick restart on Linux (avoid TIME_WAIT bind issues).
    ThreadingHTTPServer.allow_reuse_address = True
    httpd = ThreadingHTTPServer((host, port), OranHandler)
    httpd.daemon_threads = True
    httpd.auth_token = token or ""  # for handler access

    # Optional PID file (useful for systemd/nohup management)
    if pidfile:
        try:
            with open(pidfile, "w", encoding="utf-8") as f:
                f.write(str(os.getpid()))
        except Exception as e:
            print(f"Warning: could not write pidfile {pidfile}: {e}")

    # Graceful stop on SIGTERM (systemd/service stop)
    def _handle_sigterm(_signum, _frame):
        print("Received SIGTERM, shutting down...")
        threading.Thread(target=httpd.shutdown, daemon=True).start()

    try:
        signal.signal(signal.SIGTERM, _handle_sigterm)
    except Exception:
        pass

    sa = httpd.socket.getsockname()
    print("=== O-RAN SFN Web Server ===")
    if sa[0] in ("0.0.0.0", "::"):
        lan_ip = _guess_lan_ip()
        print(f"Listening on http://{sa[0]}:{sa[1]} (all interfaces)")
        print(f"Try from another device: http://{lan_ip}:{sa[1]}/")
    else:
        print(f"Listening on http://{sa[0]}:{sa[1]}")
    if token:
        print("Auth: ENABLED (token required)")
        print("  Use: http://<ip>:<port>/?token=YOUR_TOKEN")
    print("Endpoints:")
    print("  /             (HTML UI)")
    print("  /api/compute   (GET/POST JSON)")
    print("Press Ctrl+C to stop.")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()
        if pidfile:
            try:
                os.remove(pidfile)
            except Exception:
                pass


def run_cli(args: argparse.Namespace) -> None:
    _validate_inputs(alpha=args.alpha, ptp_ns=args.ptp_ns)

    # Choose one input source
    if args.gps_seconds is not None:
        gps = _to_decimal(args.gps_seconds)
        src_desc = "GPSseconds (direct)"
    elif args.epoch_seconds is not None:
        gps = unix_epoch_utc_to_gps_seconds(args.epoch_seconds, gps_minus_utc_seconds=args.gps_minus_utc)
        src_desc = "Unix epoch (UTC)"
    elif args.ptp_seconds is not None:
        gps = ptp_to_gps_seconds(
            args.ptp_seconds,
            ptp_nanoseconds=args.ptp_ns,
            ptp_scale=args.ptp_scale,
            gps_minus_utc_seconds=args.gps_minus_utc,
        )
        src_desc = f"PTP time ({args.ptp_scale})"
    else:
        gps = gps_week_tow_to_gps_seconds(args.gps_week, args.tow)
        src_desc = "GPS week + TOW"

    out = compute_sfn_from_gps(gps, alpha_ticks=args.alpha, beta_frames=args.beta)
    subframe = _compute_subframe(out["offset_in_frame_seconds"])

    print("=== O-RAN SFN from GPS time (11.7.2) ===")
    print(f"Input source: {src_desc}")
    print(f"Input GPSseconds: {gps}")
    print(f"alpha ticks: {args.alpha}  -> alpha seconds: {_format_decimal(out['alpha_seconds'])}")
    print(f"beta frames: {args.beta}   -> beta seconds: {_format_decimal(out['beta_seconds'])}")
    print("---------------------------------------")
    print(f"Absolute frame index: {out['abs_frame']}")
    print(f"SFN (mod 1024):       {out['sfn']}")
    print(f"frameId (mod 256):    {out['frame_id']}")
    print(f"Frame start (GPS s):  {_format_decimal(out['frame_start_gps_seconds'])}")
    print(f"Offset in frame (s):  {_format_decimal(out['offset_in_frame_seconds'])}")
    print(f"Subframe (0..9):      {subframe}")


def run_gui() -> None:
    import tkinter as tk
    from tkinter import ttk, messagebox

    root = tk.Tk()
    root.title("O-RAN SFN from GPS time (11.7.2)")

    pad = {"padx": 10, "pady": 6}
    mode = tk.StringVar(value="gps_seconds")

    frm = ttk.Frame(root)
    frm.grid(row=0, column=0, sticky="nsew")
    root.columnconfigure(0, weight=1)
    root.rowconfigure(0, weight=1)
    frm.columnconfigure(1, weight=1)
    frm.rowconfigure(13, weight=1)

    # Mode selection
    ttk.Label(frm, text="Input mode").grid(row=0, column=0, sticky="w", **pad)
    modes = ttk.Frame(frm)
    modes.grid(row=0, column=1, sticky="w", **pad)
    ttk.Radiobutton(modes, text="GPSseconds", variable=mode, value="gps_seconds").grid(row=0, column=0, sticky="w")
    ttk.Radiobutton(modes, text="Unix epoch (UTC)", variable=mode, value="unix_epoch").grid(row=0, column=1, sticky="w", padx=10)
    ttk.Radiobutton(modes, text="GPS week + TOW", variable=mode, value="gps_week_tow").grid(row=0, column=2, sticky="w", padx=10)
    ttk.Radiobutton(modes, text="PTP (TAI/UTC)", variable=mode, value="ptp").grid(row=0, column=3, sticky="w", padx=10)

    # Inputs
    ttk.Label(frm, text="GPSseconds (since 1980-01-06 00:00:00)").grid(row=1, column=0, sticky="w", **pad)
    gps_seconds_var = tk.StringVar(value="10.002")
    gps_entry = ttk.Entry(frm, textvariable=gps_seconds_var, width=34)
    gps_entry.grid(row=1, column=1, sticky="w", **pad)

    ttk.Label(frm, text="Unix epoch seconds (UTC) (Wireshark Epoch Arrival Time)").grid(row=2, column=0, sticky="w", **pad)
    unix_epoch_var = tk.StringVar(value="1747440475.220877")
    unix_entry = ttk.Entry(frm, textvariable=unix_epoch_var, width=34)
    unix_entry.grid(row=2, column=1, sticky="w", **pad)

    ttk.Label(frm, text="GPS week").grid(row=3, column=0, sticky="w", **pad)
    gps_week_var = tk.StringVar(value="0")
    week_entry = ttk.Entry(frm, textvariable=gps_week_var, width=14)
    week_entry.grid(row=3, column=1, sticky="w", **pad)

    ttk.Label(frm, text="Seconds-of-week (TOW)").grid(row=4, column=0, sticky="w", **pad)
    tow_var = tk.StringVar(value="0")
    tow_entry = ttk.Entry(frm, textvariable=tow_var, width=34)
    tow_entry.grid(row=4, column=1, sticky="w", **pad)

    ttk.Label(frm, text="PTP seconds since 1970-01-01").grid(row=5, column=0, sticky="w", **pad)
    ptp_sec_var = tk.StringVar(value="1747440512")
    ptp_sec_entry = ttk.Entry(frm, textvariable=ptp_sec_var, width=34)
    ptp_sec_entry.grid(row=5, column=1, sticky="w", **pad)

    ttk.Label(frm, text="PTP nanoseconds").grid(row=6, column=0, sticky="w", **pad)
    ptp_ns_var = tk.StringVar(value="312144323")
    ptp_ns_entry = ttk.Entry(frm, textvariable=ptp_ns_var, width=18)
    ptp_ns_entry.grid(row=6, column=1, sticky="w", **pad)

    ttk.Label(frm, text="PTP timescale").grid(row=7, column=0, sticky="w", **pad)
    ptp_scale_var = tk.StringVar(value="TAI")
    ptp_scale_combo = ttk.Combobox(frm, textvariable=ptp_scale_var, values=["TAI", "UTC"], state="readonly", width=10)
    ptp_scale_combo.grid(row=7, column=1, sticky="w", **pad)

    ttk.Label(frm, text="GPS-UTC offset seconds (used for UTC/epoch)").grid(row=8, column=0, sticky="w", **pad)
    gps_minus_utc_var = tk.StringVar(value="18")
    gps_minus_utc_entry = ttk.Entry(frm, textvariable=gps_minus_utc_var, width=10)
    gps_minus_utc_entry.grid(row=8, column=1, sticky="w", **pad)

    ttk.Separator(frm).grid(row=9, column=0, columnspan=2, sticky="ew", padx=10, pady=10)

    ttk.Label(frm, text="alpha (ticks @ 1.2288 GHz)").grid(row=10, column=0, sticky="w", **pad)
    alpha_var = tk.StringVar(value="0")
    alpha_entry = ttk.Entry(frm, textvariable=alpha_var, width=18)
    alpha_entry.grid(row=10, column=1, sticky="w", **pad)

    ttk.Label(frm, text="beta (frames, 10ms units)").grid(row=11, column=0, sticky="w", **pad)
    beta_var = tk.StringVar(value="0")
    beta_entry = ttk.Entry(frm, textvariable=beta_var, width=18)
    beta_entry.grid(row=11, column=1, sticky="w", **pad)

    # Output
    out_box = tk.Text(frm, width=78, height=10)
    out_box.grid(row=13, column=0, columnspan=2, sticky="nsew", padx=10, pady=10)

    def refresh_state(*_):
        m = mode.get()
        gps_entry.configure(state="normal" if m == "gps_seconds" else "disabled")
        unix_entry.configure(state="normal" if m == "unix_epoch" else "disabled")
        week_entry.configure(state="normal" if m == "gps_week_tow" else "disabled")
        tow_entry.configure(state="normal" if m == "gps_week_tow" else "disabled")
        ptp_sec_entry.configure(state="normal" if m == "ptp" else "disabled")
        ptp_ns_entry.configure(state="normal" if m == "ptp" else "disabled")
        ptp_scale_combo.configure(state="readonly" if m == "ptp" else "disabled")
        gps_minus_utc_entry.configure(state="normal" if m in ("ptp", "unix_epoch") else "disabled")

    def compute():
        try:
            alpha = int(alpha_var.get().strip())
            beta = int(beta_var.get().strip())
            gps_minus_utc = int(gps_minus_utc_var.get().strip())
            _validate_inputs(alpha=alpha)

            m = mode.get()
            if m == "gps_seconds":
                gps = _to_decimal(gps_seconds_var.get().strip())
                src_desc = "GPSseconds (direct)"
            elif m == "unix_epoch":
                gps = unix_epoch_utc_to_gps_seconds(unix_epoch_var.get().strip(), gps_minus_utc_seconds=gps_minus_utc)
                src_desc = "Unix epoch (UTC)"
            elif m == "gps_week_tow":
                week = int(gps_week_var.get().strip())
                tow = _to_decimal(tow_var.get().strip())
                gps = gps_week_tow_to_gps_seconds(week, tow)
                src_desc = "GPS week + TOW"
            else:
                ptp_sec = _to_decimal(ptp_sec_var.get().strip())
                ptp_ns = int(ptp_ns_var.get().strip())
                _validate_inputs(alpha=alpha, ptp_ns=ptp_ns)
                scale = ptp_scale_var.get().strip().upper()
                gps = ptp_to_gps_seconds(ptp_sec, ptp_nanoseconds=ptp_ns, ptp_scale=scale, gps_minus_utc_seconds=gps_minus_utc)
                src_desc = f"PTP time ({scale})"

            out = compute_sfn_from_gps(gps, alpha_ticks=alpha, beta_frames=beta)
            subframe = _compute_subframe(out["offset_in_frame_seconds"])

            text = (
                "=== O-RAN SFN from GPS time (11.7.2) ===\n"
                f"Input source: {src_desc}\n"
                f"Input GPSseconds: {gps}\n"
                f"alpha ticks: {alpha}  -> alpha seconds: {_format_decimal(out['alpha_seconds'])}\n"
                f"beta frames: {beta}   -> beta seconds: {_format_decimal(out['beta_seconds'])}\n"
                "---------------------------------------\n"
                f"Absolute frame index: {out['abs_frame']}\n"
                f"SFN (mod 1024):       {out['sfn']}\n"
                f"frameId (mod 256):    {out['frame_id']}\n"
                f"Frame start (GPS s):  {_format_decimal(out['frame_start_gps_seconds'])}\n"
                f"Offset in frame (s):  {_format_decimal(out['offset_in_frame_seconds'])}\n"
                f"Subframe (0..9):      {subframe}\n"
            )
            out_box.delete("1.0", "end")
            out_box.insert("1.0", text)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    btns = ttk.Frame(frm)
    btns.grid(row=12, column=0, columnspan=2, sticky="w", padx=10, pady=6)
    ttk.Button(btns, text="Compute", command=compute).grid(row=0, column=0)
    ttk.Button(btns, text="Quit", command=root.destroy).grid(row=0, column=1, padx=10)

    mode.trace_add("write", refresh_state)
    refresh_state()
    compute()

    root.minsize(820, 520)
    root.mainloop()


def main():
    p = argparse.ArgumentParser(
        description="Compute O-RAN SFN (FrameNumber) from GPS time (clause 11.7.2).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent(
            """\
            Examples:
              # CLI
              python oran_sfn_from_gps_tool_v8.py --epoch-seconds 1771271246.102474 --gps-minus-utc 18 --alpha 0 --beta 163

              # Web server
              # Local-only:
              python oran_sfn_from_gps_tool_v8.py --serve --host 127.0.0.1 --port 8080

              # Remote/LAN access:
              python oran_sfn_from_gps_tool_v8.py --serve --host 0.0.0.0 --port 8080

              # Remote + token:
              python oran_sfn_from_gps_tool_v8.py --serve --host 0.0.0.0 --port 8080 --token mysecret
            """
        ),
    )

    # Server mode
    p.add_argument("--serve", action="store_true", help="Run as a local web server (HTML UI + JSON API).")
    p.add_argument(
        "--host",
        default=os.environ.get("ORAN_SFN_HOST", "0.0.0.0"),
        help="Host/interface to bind (default 0.0.0.0 for LAN access). Use 127.0.0.1 for local-only.",
    )
    p.add_argument("--port", type=int, default=int(os.environ.get("ORAN_SFN_PORT", "8080")), help="Port to listen on (default 8080).")
    p.add_argument(
        "--token",
        default=os.environ.get("ORAN_SFN_TOKEN", ""),
        help="Optional access token. If set, requests must include it via ?token=... or X-Auth-Token header.",
    )
    p.add_argument("--pidfile", default="", help="Write server PID to this file (Linux service/nohup helper).")


    # Inputs (choose exactly one for CLI)
    p.add_argument("--gps-seconds", help="GPSseconds since GPS epoch (1980-01-06).")
    p.add_argument("--gps-week", type=int, help="GPS week number.")
    p.add_argument("--tow", help="GPS time-of-week in seconds.")
    p.add_argument("--ptp-seconds", help="PTP seconds since 1970-01-01 (time-of-day).")
    p.add_argument("--ptp-ns", type=int, default=0, help="PTP nanoseconds part (0..999999999).")
    p.add_argument("--ptp-scale", choices=["TAI", "UTC"], default="TAI", help="Timescale of PTP timestamp.")
    p.add_argument("--epoch-seconds", help="Unix epoch seconds in UTC (Wireshark Epoch Arrival Time).")

    # Offsets per 11.7.2
    p.add_argument("--alpha", type=int, default=0, help="alpha ticks @ 1.2288 GHz (0..12288000 for 0..10ms).")
    p.add_argument("--beta", type=int, default=0, help="beta frame offset in 10ms units (signed).")

    # GPS-UTC (used for UTC/epoch inputs)
    p.add_argument("--gps-minus-utc", type=int, default=18, help="GPS-UTC offset seconds (default 18).")

    p.add_argument("--gui", action="store_true", help="Launch a simple GUI (Tkinter)")

    args = p.parse_args()
    _validate_inputs(alpha=args.alpha, ptp_ns=args.ptp_ns, port=args.port)

    if args.serve:
        run_server(args.host, args.port, token=args.token, pidfile=args.pidfile)
        return

    if args.gui:
        run_gui()
        return

    # Validate exactly one input style
    provided = sum(
        [
            1 if args.gps_seconds is not None else 0,
            1 if (args.gps_week is not None and args.tow is not None) else 0,
            1 if args.ptp_seconds is not None else 0,
            1 if args.epoch_seconds is not None else 0,
        ]
    )
    if provided != 1:
        p.error(
            "Provide exactly one input: --gps-seconds OR (--gps-week and --tow) OR --ptp-seconds OR --epoch-seconds."
        )

    if args.gps_week is not None and args.tow is None:
        p.error("If --gps-week is provided, you must also provide --tow.")
    if args.tow is not None and args.gps_week is None:
        p.error("If --tow is provided, you must also provide --gps-week.")

    run_cli(args)


if __name__ == "__main__":
    main()
