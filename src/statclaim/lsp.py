"""Small stdio LSP transport. Editor requests never enter the execution runtime."""

import json
import sys
import traceback
from typing import BinaryIO

from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source
from statclaim.lsp_features import Document, TextMap


class ProtocolError(ValueError):
    pass


class JsonError(ProtocolError):
    pass


def read_message(stream: BinaryIO) -> dict | None:
    headers = {}
    while True:
        line = stream.readline(8193)
        if not line:
            if headers:
                raise ProtocolError("Truncated message headers")
            return None
        if len(line) > 8192:
            raise ProtocolError("Message header too long")
        if line in (b"\r\n", b"\n"):
            break
        try:
            name, value = line.decode("ascii").split(":", 1)
        except (UnicodeError, ValueError) as error:
            raise ProtocolError("Malformed message header") from error
        headers[name.lower()] = value.strip()
    try:
        length = int(headers["content-length"])
    except (KeyError, ValueError) as error:
        raise ProtocolError("Missing or invalid Content-Length") from error
    if not 0 <= length <= 16 * 1024 * 1024:
        raise ProtocolError("Content-Length out of bounds")
    body = stream.read(length)
    if len(body) != length:
        raise ProtocolError("Truncated message body")
    try:
        return json.loads(body)
    except (UnicodeError, ValueError) as error:
        raise JsonError("Invalid JSON body") from error


def write_message(stream: BinaryIO, message: dict) -> None:
    body = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    stream.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body)
    stream.flush()


class Server:
    def __init__(self, send):
        self.send = send
        self.documents: dict[str, Document] = {}
        # The text as opened or last saved; change impact is measured against it.
        self.baselines: dict[str, str] = {}
        self.initialized = False
        self.shutting_down = False
        self.exited = False

    def notify(self, method: str, params: dict):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def publish(self, document: Document):
        self.notify(
            "textDocument/publishDiagnostics",
            {
                "uri": document.uri,
                "version": document.version,
                "diagnostics": document.diagnostics(),
            },
        )

    def handle(self, message: dict):
        identifier = message.get("id")
        is_request = "id" in message
        method = message.get("method")
        params = message.get("params", {})
        try:
            if method == "exit":
                self.exited = True
                return
            if method == "initialize":
                if self.initialized:
                    raise ProtocolError("Server is already initialized")
                self.initialized = True
                result = {
                    "capabilities": {
                        "positionEncoding": "utf-16",
                        "textDocumentSync": {"openClose": True, "change": 1, "save": True},
                        "completionProvider": {"triggerCharacters": [".", "(", ",", "="]},
                        "hoverProvider": True,
                        "definitionProvider": True,
                    },
                    "serverInfo": {"name": "StatClaim", "version": "0.1.0"},
                }
            elif not self.initialized:
                if is_request:
                    self.error(identifier, -32002, "Server not initialized")
                return
            elif method == "shutdown":
                self.shutting_down = True
                result = None
            elif self.shutting_down:
                if is_request:
                    self.error(identifier, -32600, "Server is shutting down")
                return
            elif method in ("initialized", "$/cancelRequest", "$/setTrace"):
                return
            elif method == "textDocument/didOpen":
                data = params["textDocument"]
                existing = self.documents.get(data["uri"])
                if existing and data["version"] <= existing.version:
                    return
                document = Document(data["uri"], data["version"], data["text"])
                self.documents[document.uri] = document
                self.baselines[document.uri] = document.text
                self.publish(document)
                return
            elif method == "textDocument/didSave":
                saved = self.documents.get(params["textDocument"]["uri"])
                if saved is not None:
                    self.baselines[saved.uri] = saved.text
                return
            elif method == "textDocument/didChange":
                data = params["textDocument"]
                previous = self.documents.get(data["uri"])
                if previous is None or data["version"] <= previous.version:
                    return
                text = previous.text
                for change in params["contentChanges"]:
                    if "range" in change:
                        mapping = TextMap(Source(text))
                        start = mapping.offset(change["range"]["start"])
                        end = mapping.offset(change["range"]["end"])
                        if start > end:
                            raise ProtocolError("Invalid edit range")
                        text = text[:start] + change["text"] + text[end:]
                    else:
                        text = change["text"]
                document = Document(data["uri"], data["version"], text)
                self.documents[document.uri] = document
                self.publish(document)
                return
            elif method == "textDocument/didClose":
                uri = params["textDocument"]["uri"]
                self.documents.pop(uri, None)
                self.baselines.pop(uri, None)
                self.notify("textDocument/publishDiagnostics", {"uri": uri, "diagnostics": []})
                return
            elif method in (
                "textDocument/completion",
                "textDocument/hover",
                "textDocument/definition",
                "statclaim/inspect",
                "statclaim/explain",
                "statclaim/impact",
            ):
                document = self.documents.get(params["textDocument"]["uri"])
                if document is None:
                    result = None
                else:
                    feature = method.rsplit("/", 1)[1]
                    if method == "statclaim/inspect":
                        result = document.inspection()
                    elif method == "statclaim/explain":
                        result = document.explain(params.get("position"))
                    elif method == "statclaim/impact":
                        from statclaim.contract_reports import impact, impact_markdown

                        baseline = self.baselines.get(document.uri, document.text)
                        result = impact(
                            compile_source(Source(baseline, document.uri)), document.compilation
                        )
                        result["markdown"] = impact_markdown(result)
                    else:
                        result = getattr(document, feature)(params["position"])
            else:
                if is_request:
                    self.error(identifier, -32601, f"Method not found: {method}")
                return
            if is_request:
                self.send({"jsonrpc": "2.0", "id": identifier, "result": result})
        except (KeyError, TypeError, ValueError, IndexError) as error:
            if is_request:
                self.error(identifier, -32602, f"Invalid parameters: {error}")
            else:
                self.notify("window/logMessage", {"type": 2, "message": str(error)})
        except Exception:
            traceback.print_exc(file=sys.stderr)
            if is_request:
                self.error(identifier, -32603, "Internal StatClaim error; see server stderr")

    def error(self, identifier, code: int, message: str):
        self.send({"jsonrpc": "2.0", "id": identifier, "error": {"code": code, "message": message}})


def run_stdio() -> int:
    server = Server(lambda message: write_message(sys.stdout.buffer, message))
    while not server.exited:
        try:
            message = read_message(sys.stdin.buffer)
            if message is None:
                break
            if not isinstance(message, dict) or message.get("jsonrpc") != "2.0":
                server.error(None, -32600, "Invalid JSON-RPC message")
                continue
            server.handle(message)
        except JsonError:
            server.error(None, -32700, "Invalid JSON body")
        except ProtocolError as error:
            # Bad framing cannot safely be resynchronized. Exit without polluting
            # stdout with non-protocol output; the client can restart the server.
            print(f"StatClaim LSP: {error}", file=sys.stderr)
            return 1
    return 0 if server.shutting_down else 1
