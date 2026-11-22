"""Serve the studio on this machine: its files, and its API over HTTP on 127.0.0.1.

Every API request is answered by api.handle, the same code the web studio runs in the browser.
"""

import argparse
import json
import os
import sys
import threading
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from mimetypes import guess_type
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import api  # noqa: E402

# Set when the server starts; tests and other callers get a checkout with Lean if it is there.
BACKEND = api.Backend.local()


def codespace_origin(port: int) -> str | None:
    """Where a GitHub Codespace forwards the studio's port, when it runs in one."""
    name = os.environ.get("CODESPACE_NAME")
    domain = os.environ.get("GITHUB_CODESPACES_PORT_FORWARDING_DOMAIN")
    return f"https://{name}-{port}.{domain}" if name and domain else None


class Editor(BaseHTTPRequestHandler):
    def respond(self, data, content_type="application/json", status=200):
        body = data if isinstance(data, bytes) else json.dumps(data).encode()
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def trusted(self) -> bool:
        """A request from the studio's own page, not from another website.

        Forms on other sites cannot send JSON, and a script on another site must say where it
        comes from. Requests without an origin come from tests and command-line tools. In a
        GitHub Codespace the page is also served from the port's forwarded address.
        """
        if self.headers.get("Content-Type", "").split(";")[0].strip() != "application/json":
            return False
        origin = self.headers.get("Origin")
        if origin is None:
            return True
        scheme, _, rest = origin.partition("://")
        host = rest.rsplit(":", 1)[0] if rest.count(":") == 1 else rest
        if scheme == "http" and host in {"127.0.0.1", "localhost"}:
            return True
        server = getattr(self, "server", None)
        return server is not None and origin == codespace_origin(server.server_address[1])

    def do_GET(self):
        path = self.path.partition("?")[0]
        if path.startswith("/api/"):
            status, result = api.handle("GET", path.removeprefix("/api/"), None, BACKEND)
            return self.respond(result, status=status)
        asset = path[1:] or "index.html"
        if asset not in api.ASSETS:
            return self.send_error(404)
        self.respond((api.ROOT / asset).read_bytes(), guess_type(asset)[0] or "text/plain")

    def do_POST(self):
        if not self.trusted():
            return self.send_error(HTTPStatus.FORBIDDEN, "Requests must come from the studio page.")
        if not self.path.startswith("/api/"):
            return self.send_error(404)
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            length = 0
        if not 0 < length <= api.MAX_SOURCE:
            return self.respond(
                {"error": "Document exceeds the 4 MiB request limit."},
                status=HTTPStatus.REQUEST_ENTITY_TOO_LARGE,
            )
        try:
            body = self.rfile.read(length).decode("utf-8")
        except UnicodeDecodeError:
            body = ""
        status, result = api.handle_json("POST", self.path.removeprefix("/api/"), body, BACKEND)
        try:
            self.respond(result.encode(), status=status)
        except (BrokenPipeError, ConnectionResetError):
            # The editor cancels stale requests while typing.
            return


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=4180)
    parser.add_argument(
        "--no-lean",
        action="store_true",
        help="run as the web studio does: no Lean, so proofs report that they need it",
    )
    args = parser.parse_args()
    BACKEND = api.Backend.local(lean=not args.no_lean)
    # The palette's hints take a few seconds to work out; start before the first request.
    threading.Thread(target=api.block_fits, daemon=True).start()
    with ThreadingHTTPServer(("127.0.0.1", args.port), Editor) as server:
        lean = "with Lean proofs" if BACKEND.lean else "without Lean proofs"
        print(f"StatClaim Studio at http://127.0.0.1:{args.port} ({lean})", flush=True)
        server.serve_forever()
