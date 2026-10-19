"""
Minimalist Retro Web Server for Harold Birkett's Manufacturing Report Program (Version 2.1).
Uses only Python's standard library (http.server, json, webbrowser) so zero external packages are required.
"""
from __future__ import annotations

import json
import mimetypes
import sys
import threading
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse

from mfr_engine import MFRSession, ROOT_DIR


STATIC_DIR = ROOT_DIR / "static"
PORT = 8220  # Homage to the Wang 2200!

SESSION = MFRSession()
SESSION_LOCK = threading.Lock()


class MFRRequestHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt: str, *args) -> None:
        # Keep console output clean and dated
        sys.stdout.write(f"[WANG-2200 HTTPD] {self.address_string()} - {fmt % args}\n")

    def _send_json(self, payload: dict, status: int = 200) -> None:
        raw = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(raw)

    def _serve_file(self, file_path: Path) -> None:
        if not file_path.exists() or not file_path.is_file():
            self.send_error(404, "File Not Found")
            return
        ctype, _ = mimetypes.guess_type(str(file_path))
        if not ctype:
            ctype = "application/octet-stream"
        data = file_path.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path

        if path in ("/", "/index.html"):
            self._serve_file(STATIC_DIR / "index.html")
        elif path.startswith("/static/"):
            rel = path[len("/static/") :]
            target = (STATIC_DIR / rel).resolve()
            if str(target).startswith(str(STATIC_DIR.resolve())):
                self._serve_file(target)
            else:
                self.send_error(403, "Forbidden")
        elif path == "/api/status":
            with SESSION_LOCK:
                self._send_json(SESSION.get_status_payload())
        elif path.startswith("/api/disk_file/"):
            fname = path[len("/api/disk_file/") :].strip()
            with SESSION_LOCK:
                if fname.upper() == "MRPARAMS":
                    p = SESSION.data_root / "MRPARAMS.json"
                else:
                    p = SESSION.get_disk_dir() / f"{fname}.json"
                if p.exists():
                    self._send_json({"name": fname, "content": json.loads(p.read_text(encoding="utf-8"))})
                else:
                    self._send_json({"error": f"File {fname} not found"}, status=404)
        else:
            self.send_error(404, "Not Found")

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path
        length = int(self.headers.get("Content-Length", "0"))
        body_bytes = self.rfile.read(length) if length > 0 else b"{}"
        try:
            data = json.loads(body_bytes.decode("utf-8"))
        except Exception:
            data = {}

        if path == "/api/input":
            user_input = str(data.get("input", data.get("value", "")))
            with SESSION_LOCK:
                payload = SESSION.handle_input(user_input)
                self._send_json(payload)

        elif path == "/api/action":
            act = str(data.get("action", ""))
            with SESSION_LOCK:
                if act in ("reset_menu", "reset_to_menu"):
                    SESSION.show_main_menu()
                    SESSION.top_bar_row1 = "LOADED MODULE: MRSTART (MAIN MENU)"
                elif act in ("toggle_strict", "toggle_strict_mode"):
                    strict_val = data.get("strict", data.get("strict_mode", not SESSION.strict_wang_mode))
                    SESSION.strict_wang_mode = bool(strict_val)
                    mode_lbl = "STRICT WANG BASIC-2 MODE" if SESSION.strict_wang_mode else "ENTER-TO-KEEP CONVENIENCE MODE"
                    SESSION.top_bar_row1 = f"INPUT MODE SET TO: {mode_lbl}"
                elif act == "seed_st_mary":
                    SESSION.seed_st_mary_oct2015()
                    SESSION.top_bar_row1 = "RESTORED OCT 2015 ST. MARY SUGAR CO-OP DEMO DATA (DAYS 1-6)"
                elif act == "seed_raceland":
                    SESSION.seed_raceland_platter()
                    SESSION.top_bar_row1 = "LOADED RACELAND RAW SUGAR (PLATTER1.BS2) PARAMETERS"
                elif act == "clear_printer":
                    SESSION.printer_jobs = []
                    SESSION.top_bar_row1 = "CLEARED LINE PRINTER (215) OUTPUT TRAY"
                elif act in ("quick_print_demo_pack", "run_all_sample_reports"):
                    # Generate Daily Report #6 (10/11/15) and Weekly Report #1 (10/06/15-10/10/15) onto printer tray
                    if not SESSION.day_file_exists(6):
                        SESSION.seed_st_mary_oct2015()
                    for dt_s in ("10/06/15", "10/07/15", "10/08/15", "10/09/15", "10/10/15", "10/11/15"):
                        SESSION.show_main_menu()
                        SESSION.handle_input("5")
                        SESSION.handle_input("Y")
                        SESSION.handle_input(dt_s)
                        SESSION.handle_input("Y")
                        SESSION.handle_input("1")
                    # Also Weekly Report #1 (10/06/15 to 10/10/15)
                    SESSION.show_main_menu()
                    SESSION.handle_input("6")
                    SESSION.handle_input("Y")
                    SESSION.handle_input("10/10/15")
                    SESSION.handle_input("Y")
                    SESSION.handle_input("10/06/15")
                    SESSION.handle_input("Y")
                    SESSION.handle_input("1")
                    SESSION.handle_input("1")
                    SESSION.handle_input("Y")
                    SESSION.handle_input("RAW COLOR 2348")
                    SESSION.handle_input("ASH  0.31")
                    SESSION.handle_input("SAFETY FACTOR .32        MOIST .41")
                    SESSION.handle_input("")
                    SESSION.handle_input("DEX 0.99%")
                    SESSION.handle_input("")
                    SESSION.show_main_menu()
                    SESSION.top_bar_row1 = "BATCH PRINTED ALL 6 DAILY REPORTS + WEEKLY REPORT #1 TO LINE PRINTER"

                self._send_json(SESSION.get_status_payload())
        else:
            self.send_error(404, "Not Found")


def main() -> None:
    # Pre-print Daily Report #6 (10/11/15) on initial launch if printer tray is empty
    with SESSION_LOCK:
        if not SESSION.printer_jobs and SESSION.day_file_exists(6):
            SESSION.handle_input("5")
            SESSION.handle_input("Y")
            SESSION.handle_input("10/11/15")
            SESSION.handle_input("Y")
            SESSION.handle_input("1")
            SESSION.show_main_menu()
            SESSION.top_bar_row1 = "READY - OCT 2015 ST. MARY SUGAR CO-OP DATA LOADED ON DISK D12"

    url = f"http://127.0.0.1:{PORT}"
    print("=" * 72)
    print("  HAROLD BIRKETT'S MANUFACTURING REPORT PROGRAM (VERSION 2.1)")
    print("  Wang 2200 / Niakwa BASIC-2 Minimalist Web Terminal & Line Printer")
    print(f"  Listening on: {url}")
    print("=" * 72)

    if "--no-browser" not in sys.argv:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()

    server = ThreadingHTTPServer(("127.0.0.1", PORT), MFRRequestHandler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down server...")
        server.server_close()


if __name__ == "__main__":
    main()
