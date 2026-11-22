"""Dispatch one editor API request over an in-memory HTTP connection."""

import json
import sys
from http.client import HTTPResponse
from io import BytesIO
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from server import Editor


class BufferSocket:
    def __init__(self, data):
        self.stream = BytesIO(data)

    def makefile(self, mode, *args):
        return self.stream

    def sendall(self, data):
        self.output.write(data)


class SilentEditor(Editor):
    def log_message(self, *args):
        pass


request = json.load(sys.stdin)
body = request.get("body", "").encode()
method = request["method"]
path = request["path"]
headers = (
    f"{method} {path} HTTP/1.0\r\n"
    f"Content-Type: application/json\r\nContent-Length: {len(body)}\r\n\r\n"
)
connection = BufferSocket(headers.encode() + body)
connection.output = BytesIO()
SilentEditor(connection, ("127.0.0.1", 0), None)
response = HTTPResponse(BufferSocket(connection.output.getvalue()))
response.begin()
print(json.dumps({"status": response.status, "body": response.read().decode()}))
