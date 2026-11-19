"""Protocol/editor contracts, with no verification on the editing path."""

import io
import subprocess
import sys
from pathlib import Path

import pytest

from statclaim.language_syntax import Source, tokenize
from statclaim.lsp import ProtocolError, Server, read_message, write_message
from statclaim.lsp_features import Document, TextMap

ROOT = Path(__file__).resolve().parents[1]
URI = "file:///tmp/statclaim%20study.stat"
BASE = (ROOT / "tests/fixtures/fisher.stat").read_text()
PREFIX = BASE[: BASE.index("let analysis")]


def position(document, substring, *, last=False):
    offset = document.text.rindex(substring) if last else document.text.index(substring)
    return document.mapping.position(offset)


def complete(text):
    document = Document(URI, 1, text)
    response = document.completion(document.mapping.position(len(text)))
    return {item["label"]: item for item in response["items"]}


@pytest.fixture(autouse=True)
def forbid_editor_execution(monkeypatch, request):
    if request.node.name.startswith("test_real_stdio_cli"):
        return

    def forbidden(*args, **kwargs):
        pytest.fail("editing must never calculate, invoke subprocesses, or execute a program")

    monkeypatch.setattr(subprocess, "Popen", forbidden)
    for name in (
        "check_source",
        "test_design",
        "verify_design",
        "verify_design_only",
        "verify_family",
    ):
        monkeypatch.setattr(f"statclaim.language_runner.{name}", forbidden)
    monkeypatch.setattr("statclaim.report.fisher_exact", forbidden)


@pytest.fixture
def connection():
    messages = []
    server = Server(messages.append)

    def send(method, params=None, identifier=None):
        data = {"jsonrpc": "2.0", "method": method, "params": params or {}}
        if identifier is not None:
            data["id"] = identifier
        server.handle(data)
        return messages[-1] if messages else None

    send("initialize", {"capabilities": {}}, 1)
    return server, messages, send


def open_document(send, text=BASE, version=1):
    return send(
        "textDocument/didOpen",
        {"textDocument": {"uri": URI, "version": version, "languageId": "statclaim", "text": text}},
    )


def test_initialize_declares_utf16_and_editor_features(connection):
    _, messages, _ = connection
    capabilities = messages[0]["result"]["capabilities"]
    assert capabilities["positionEncoding"] == "utf-16"
    assert capabilities["textDocumentSync"]["change"] == 1
    assert capabilities["completionProvider"]
    assert capabilities["hoverProvider"] is True
    assert capabilities["definitionProvider"] is True
    assert "executeCommandProvider" not in capabilities


def test_open_edit_clear_and_close_diagnostics_are_versioned(connection):
    server, messages, send = connection
    response = open_document(send, BASE.replace("alpha=1/20", "alpha=2"))
    assert response["params"]["version"] == 1
    assert response["params"]["diagnostics"][0]["code"] == "domain"
    send(
        "textDocument/didChange",
        {"textDocument": {"uri": URI, "version": 3}, "contentChanges": [{"text": BASE}]},
    )
    assert messages[-1]["params"] == {"uri": URI, "version": 3, "diagnostics": []}
    count = len(messages)
    send(
        "textDocument/didChange",
        {
            "textDocument": {"uri": URI, "version": 2},
            "contentChanges": [{"text": "let invalid = missing"}],
        },
    )
    assert len(messages) == count
    assert server.documents[URI].version == 3
    assert server.documents[URI].text == BASE
    send("textDocument/didClose", {"textDocument": {"uri": URI}})
    assert messages[-1]["params"] == {"uri": URI, "diagnostics": []}
    assert URI not in server.documents
    send(
        "textDocument/didChange",
        {"textDocument": {"uri": URI, "version": 4}, "contentChanges": [{"text": BASE}]},
    )
    assert URI not in server.documents
    open_document(send, BASE, 1)
    assert server.documents[URI].version == 1


@pytest.mark.parametrize(
    "example,code", [("adaptive", "sampling_scope"), ("overallocated", "allocation")]
)
def test_requirements_are_warnings_not_proof_failures(connection, example, code):
    _, _, send = connection
    text = (ROOT / f"examples/{example}.stat").read_text()
    diagnostic = open_document(send, text)["params"]["diagnostics"][0]
    assert diagnostic["severity"] == 2
    assert diagnostic["source"] == "statclaim requirements"
    assert diagnostic["code"] == code
    assert (
        "evidence of inflated error" in diagnostic["message"]
        or "does not prove" in diagnostic["message"]
    )


@pytest.mark.parametrize(
    "text",
    [
        "",
        "use ",
        "let x = ",
        "let x = fisher(",
        'let x = "🧪',
        PREFIX + "let output = [verify(typeI(",
    ],
)
def test_incomplete_input_keeps_all_editor_requests_responsive(connection, text):
    server, _, send = connection
    open_document(send, text)
    cursor = server.documents[URI].mapping.position(len(text))
    for index, method in enumerate(("completion", "hover", "definition"), 10):
        result = send(
            f"textDocument/{method}", {"textDocument": {"uri": URI}, "position": cursor}, index
        )
        assert result["id"] == index
        assert "error" not in result


def test_module_constructor_and_builtin_completion_use_registry():
    assert set(complete("use tests.")) == {
        "tests.fisher",
        "tests.binomial",
        "tests.difference",
        "tests.t",
        "tests.survival",
        "tests.mixed_model",
        "tests.logistic",
        "tests.declared",
        "tests.randomisation",
        "tests.cluster",
    }
    assert set(complete("use models.")) == {
        "models.two_arm_binomial",
        "models.two_arm_continuous",
        "models.two_arm_survival",
    }
    assert "fisher" not in complete("let x = fi")
    assert "fisher" in complete(PREFIX + "let x = fi")
    assert "verify" in complete("let x = ver")
    assert "calculate" in complete("let x = cal")
    assert "null" not in complete("let early = nu\n" + PREFIX[:0])


def test_named_argument_and_expected_type_completion():
    fields = complete(PREFIX + "let a = fisher(")
    assert {"design", "null", "alpha"} <= fields.keys()
    assert fields["design"]["textEdit"]["newText"] == "design="
    plans = complete(PREFIX + "let a = fisher(design=")
    assert {"plan", "fixed", "adaptive"} <= plans.keys()
    assert not ({"study", "null", "verify", "equal_proportions"} & plans.keys())
    fields = complete(PREFIX + "let a = fisher(design=plan, ")
    assert "design" not in fields
    assert {"null", "alpha"} <= fields.keys()
    partial = complete(PREFIX + "let a = fisher(des")
    assert set(partial) == {"design"}
    assert partial["design"]["textEdit"]["range"]["start"]["character"] == len("let a = fisher(")


def test_scope_claim_and_exact_level_completion():
    text = BASE.replace("verify typeI(analysis)", "let claim = typeI(analysis)")
    claims = complete(text + "let checked = verify(")
    assert "claim" in claims
    assert "analysis" not in claims
    assert "typeI" in claims
    assert "fisher" not in claims
    results = complete(text + "let checked = verify(claim)\nlet later = verify(")
    assert "checked" not in results
    levels = complete(PREFIX + "let count = 100\nlet level = 0.05\nlet a = fisher(alpha=")
    assert "level" in levels
    assert "count" not in levels


@pytest.mark.parametrize(
    "expression,fragment,label",
    [
        ("let a = fis|her(design=plan)", "fisher", "fisher"),
        ("let a = fisher(design=pl|an)", "plan", "plan"),
        ("let a = fisher(des|ign=plan)", "design", "design"),
    ],
)
def test_completion_inside_a_token_replaces_the_suffix_without_duplicating_equals(
    expression, fragment, label
):
    cursor = len(PREFIX) + expression.index("|")
    document = Document(URI, 1, PREFIX + expression.replace("|", ""))
    result = document.completion(document.mapping.position(cursor))
    item = next(item for item in result["items"] if item["label"] == label)
    replacement = item["textEdit"]
    start = document.mapping.offset(replacement["range"]["start"])
    end = document.mapping.offset(replacement["range"]["end"])
    assert document.text[start:end] == fragment
    assert replacement["newText"] == label


def test_completion_ignores_comments_strings_and_later_declarations():
    assert complete(PREFIX + "# fisher(") == {}
    assert complete(PREFIX + 'let s = "fisher("') == {}
    text = PREFIX + "let a = fisher(design=pl\nlet future = fixed(study)\n"
    document = Document(URI, 1, text)
    cursor = document.mapping.position(text.index("design=pl") + len("design=pl"))
    labels = {i["label"] for i in document.completion(cursor)["items"]}
    assert "plan" in labels
    assert "future" not in labels


def test_hover_types_signatures_and_statistical_meanings():
    text = BASE.replace(
        "verify typeI(analysis)", "let validity = typeI(analysis)\nlet checked = verify(validity)"
    )
    document = Document(URI, 1, text)
    hover = document.hover(position(document, "validity", last=True))["contents"]["value"]
    assert "Required assumptions" in hover
    assert "<= 1/20" in hover
    assert "not a proof" in hover
    assert "StudyDesign" in document.hover(position(document, "plan"))["contents"]["value"]
    hover = document.hover(position(document, "fisher("))["contents"]["value"]
    assert "design: StudyDesign" in hover and "alpha: level" in hover
    hover = document.hover(position(document, "checked"))["contents"]["value"]
    assert "VerificationResult" in hover and "does not execute" in hover


def test_definition_selects_declaration_identifier_and_not_argument_labels():
    document = Document(URI, 1, BASE)
    definition = document.definition(position(document, "plan", last=True))
    assert definition["uri"] == URI
    assert definition["range"]["start"] == {"line": 6, "character": 4}
    assert definition["range"]["end"] == {"line": 6, "character": 8}
    assert (
        document.definition(position(document, "analysis)", last=True))["range"]["start"]["line"]
        == 8
    )
    text = "let alpha = 0.05\n" + BASE.replace("alpha=1/20", "alpha=alpha")
    document = Document(URI, 1, text)
    assert document.definition(position(document, "alpha=alpha")) is None
    assert (
        document.definition(position(document, "alpha)", last=True))["range"]["start"]["line"] == 0
    )
    assert document.definition(position(document, "fisher(")) is None


def test_utf16_crlf_diagnostics_hover_definition_and_incremental_changes(connection):
    text = 'let marker = "🧪"\r\nlet alias = marker\r\nlet invalid = ["🧪", missing]\r\n'
    document = Document(URI, 1, text)
    for offset in (
        0,
        text.index("🧪"),
        text.index("🧪") + 1,
        text.index("let alias"),
        text.index("missing"),
        len(text),
    ):
        assert document.mapping.offset(document.mapping.position(offset)) == offset
    diagnostic = document.diagnostics()[0]
    assert diagnostic["range"]["start"] == {"line": 2, "character": 21}
    assert document.definition(position(document, "marker", last=True))["range"]["start"] == {
        "line": 0,
        "character": 4,
    }
    server, _, send = connection
    open_document(send, text)
    start = document.mapping.position(text.index("missing"))
    end = document.mapping.position(text.index("missing") + len("missing"))
    response = send(
        "textDocument/didChange",
        {
            "textDocument": {"uri": URI, "version": 2},
            "contentChanges": [{"range": {"start": start, "end": end}, "text": "marker"}],
        },
    )
    assert response["params"]["diagnostics"] == []
    assert '["🧪", marker]\r\n' in server.documents[URI].text


def test_trivia_tokens_do_not_change_default_lexer_results():
    source = Source('let x = "🧪" # text\r\n')
    plain, diagnostics = tokenize(source)
    with_trivia, other_diagnostics = tokenize(source, include_trivia=True)
    assert plain == [t for t in with_trivia if t.kind not in ("SPACE", "COMMENT")]
    assert diagnostics == other_diagnostics == []


def test_lifecycle_unknown_requests_and_invalid_parameters(connection):
    server, messages, send = connection
    assert send("unknown", {}, 2)["error"]["code"] == -32601
    assert send("textDocument/hover", {}, 3)["error"]["code"] == -32602
    assert (
        send(
            "textDocument/hover",
            {"textDocument": {"uri": URI}, "position": {"line": 0, "character": 0}},
            4,
        )["result"]
        is None
    )
    assert send("shutdown", {}, 5)["result"] is None
    assert send("textDocument/completion", {}, 6)["error"]["code"] == -32600
    send("exit")
    assert server.exited
    other = Server(messages.append)
    other.handle({"jsonrpc": "2.0", "id": 7, "method": "textDocument/hover"})
    assert messages[-1]["error"]["code"] == -32002


def test_transport_counts_utf8_bytes_and_reads_consecutive_messages():
    stream = io.BytesIO()
    message = {"jsonrpc": "2.0", "id": 1, "result": "🧪"}
    write_message(stream, message)
    write_message(stream, message)
    stream.seek(0)
    assert read_message(stream) == message
    assert read_message(stream) == message
    assert read_message(stream) is None


@pytest.mark.parametrize(
    "data",
    [
        b"Broken\r\n\r\n",
        b"Content-Length: x\r\n\r\n",
        b"Content-Length: -1\r\n\r\n",
        b"Content-Length: 5\r\n\r\n{}",
        b"Content-Length: 2\r\n\r\nxx",
    ],
)
def test_transport_rejects_invalid_frames(data):
    with pytest.raises(ProtocolError):
        read_message(io.BytesIO(data))


@pytest.mark.parametrize("bad_json", [False, True])
def test_real_stdio_cli_exchanges_protocol_only_and_exits_cleanly(bad_json):
    def message(method, params=None, identifier=None):
        data = {"jsonrpc": "2.0", "method": method, "params": params or {}}
        if identifier is not None:
            data["id"] = identifier
        return data

    requests = [
        message("initialize", {"capabilities": {}}, 1),
        message(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": URI,
                    "version": 1,
                    "text": BASE.replace("alpha=1/20", "alpha=2"),
                }
            },
        ),
        message(
            "textDocument/didChange",
            {"textDocument": {"uri": URI, "version": 2}, "contentChanges": [{"text": BASE}]},
        ),
        message("shutdown", {}, 2),
        message("exit"),
    ]
    wire = io.BytesIO()
    if bad_json:
        wire.write(b"Content-Length: 2\r\n\r\nxx")
    for request in requests:
        write_message(wire, request)
    completed = subprocess.run(
        [str(Path(sys.executable).parent / "statclaim"), "lsp"],
        input=wire.getvalue(),
        capture_output=True,
        timeout=10,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr.decode()
    output = io.BytesIO(completed.stdout)
    responses = []
    while (response := read_message(output)) is not None:
        responses.append(response)
    if bad_json:
        assert responses.pop(0)["error"]["code"] == -32700
    assert responses[0]["id"] == 1
    assert responses[1]["params"]["version"] == 1
    assert responses[2]["params"] == {"uri": URI, "version": 2, "diagnostics": []}
    assert responses[-1] == {"jsonrpc": "2.0", "id": 2, "result": None}
    assert completed.stderr == b""


def test_position_map_clamps_to_content_and_never_splits_surrogates():
    mapping = TextMap(Source("🧪x\r\nnext\n"))
    assert mapping.offset({"line": 0, "character": 1}) == 0
    assert mapping.offset({"line": 0, "character": 2}) == 1
    assert mapping.offset({"line": 0, "character": 100}) == 2
    assert mapping.offset({"line": 100, "character": 0}) == len(mapping.source.text)


def test_typed_field_completion_and_optional_evidence_chains(connection):
    _, _, send = connection
    base = BASE + "let checked = verify(typeI(analysis))\n"
    for suffix, expected in (
        ("analysis.", {"alpha": "exact number", "design": "StudyDesign"}),
        ("checked.", {"status": "string", "evidence": "Option[Evidence]"}),
        ("checked.evidence.", {"certificate": "Option[CertificateReference]"}),
        ("checked.evidence.certificate.", {"file": "Option[string]"}),
    ):
        items = complete(base + "let field = " + suffix)
        for label, kind in expected.items():
            assert items[label]["detail"] == kind
    open_document(send, base + "let field = checked.evidence\n")
    result = send("statclaim/inspect", {"textDocument": {"uri": URI}}, 50)["result"]
    assert result["version"] == 1
    assert all("evidence" not in claim for claim in result["claims"])


def test_field_completion_in_the_middle_of_a_chain_preserves_following_fields():
    text = (
        BASE
        + "let checked = verify(typeI(analysis))\nlet path = checked.evidence.cer|tificate.file\n"
    )
    cursor = text.index("|")
    document = Document(URI, 1, text.replace("|", ""))
    items = document.completion(document.mapping.position(cursor))["items"]
    item = next(i for i in items if i["label"] == "certificate")
    start = document.mapping.offset(item["textEdit"]["range"]["start"])
    end = document.mapping.offset(item["textEdit"]["range"]["end"])
    assert document.text[start:end] == "certificate"
    assert document.text[end:].startswith(".file")


def test_field_hover_is_typed_and_definition_resolves_the_root_declaration():
    text = (
        BASE
        + "let checked = verify(typeI(analysis))\nlet path = checked.evidence.certificate.file\n"
    )
    document = Document(URI, 1, text)
    hover = document.hover(position(document, "evidence"))["contents"]["value"]
    assert "Option[Evidence]" in hover
    assert "Absent on unmet requirements" in hover
    definition = document.definition(position(document, "checked.evidence"))
    assert definition["range"]["start"]["line"] == len(BASE.splitlines())


def test_claim_inspection_groups_aliases_and_reports_unrequested_requirements(connection):
    _, _, send = connection
    text = BASE.replace(
        "verify typeI(analysis)",
        "let validity = typeI(analysis)\nlet alias = validity\nlet checked = verify(alias)",
    )
    open_document(send, text.replace("fixed(", "adaptive("))
    result = send("statclaim/inspect", {"textDocument": {"uri": URI}, "version": 0}, 60)["result"]
    assert result["version"] == 1
    assert result["status"] == "unresolved_obligation"
    assert len(result["claims"]) == 1
    claim = result["claims"][0]
    assert claim["names"] == ["validity", "alias"]
    assert claim["requirements"][0]["code"] == "sampling_scope"
    assert "range" in claim["requirements"][0]
    assert claim["requests"][0]["names"] == ["checked"]
    assert claim["assumptions"]
    text = text.replace("let checked = verify(alias)", "")
    send(
        "textDocument/didChange",
        {
            "textDocument": {"uri": URI, "version": 2},
            "contentChanges": [{"text": text.replace("fixed(", "adaptive(")}],
        },
    )
    unrequested = send("statclaim/inspect", {"textDocument": {"uri": URI}}, 61)["result"]
    assert unrequested["claims"][0]["requests"] == []
    assert unrequested["claims"][0]["requirements"][0]["code"] == "sampling_scope"
