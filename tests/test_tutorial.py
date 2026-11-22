"""The tutorial's lesson files stay valid and match the code shown on the page."""

import html
import importlib.util
import re
from pathlib import Path

import pytest

from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source

ROOT = Path(__file__).resolve().parents[1]
LESSONS = sorted((ROOT / "examples/tutorial").glob("*.stat"))
EXPECTED = {
    "03_wrong_null": "invalid",
    "03_optional_stopping": "unresolved_obligation",
    "06_changed_levels": "unresolved_obligation",
}


@pytest.mark.parametrize("path", LESSONS, ids=lambda path: path.stem)
def test_lesson_compiles_as_described(path):
    compilation = compile_source(Source(path.read_text(), str(path)))
    assert compilation.status == EXPECTED.get(path.stem, "elaborated")


def test_the_page_is_in_step_with_the_lessons():
    """Figures, contents and lede follow the lesson files: scripts/tutorial.py sync."""
    spec = importlib.util.spec_from_file_location("tutorial", ROOT / "scripts/tutorial.py")
    tutorial = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tutorial)
    assert tutorial.check() == []


def test_page_shows_the_lesson_files():
    page = html.unescape(re.sub(r"<[^>]+>", "", (ROOT / "docs/tutorial.html").read_text()))
    for path in LESSONS:
        text = path.read_text()
        if path.stem == "06_changed_levels":
            # The page shows only the three analyses that differ from lesson 5.
            text = text[text.index("let response") : text.index("let endpoints")]
        for line in text.splitlines():
            if line.strip():
                assert line in page, f"{path.name}: {line}"
