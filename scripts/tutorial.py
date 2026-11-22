"""Keep docs/tutorial.html in step with the lesson files in examples/tutorial/.

uv run python scripts/tutorial.py sync      # rewrite the page's code figures and lede
uv run python scripts/tutorial.py check     # fail if the page has drifted from the lessons
uv run python scripts/tutorial.py outputs   # rerun lessons and check the outputs shown

A code figure shows a whole lesson file or a contiguous slice of it. `sync` highlights
the lesson's current text into each figure: a figure whose text is no longer in the file
is rewritten with the whole file when it starts like the file, and reported otherwise.
`outputs` reruns every lesson that needs no Lean backend and checks that each line an
output block shows, other than "...", is a line of the fresh run.
"""

import html
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAGE = ROOT / "docs/tutorial.html"
LESSONS = ROOT / "examples/tutorial"
FIGURE = re.compile(
    r'(<figure class="code"><figcaption>examples/tutorial/(?P<name>[^<]+)</figcaption>'
    r'<div class="scroll"><pre><code>)(?P<code>.*?)(</code></pre></div></figure>)',
    re.S,
)
OUTPUT = re.compile(r'<div class="scroll output"><pre><code>(?P<code>.*?)</code></pre></div>', re.S)
SECTION = re.compile(r'<section class="lesson" id="[^"]+">.*?</section>', re.S)
LEDE = re.compile(r'(<p class="lede">)([A-Z][a-z-]+)( short lessons\.)')
NUMBERS = (
    "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen "
    "fifteen sixteen seventeen eighteen nineteen"
).split()
TENS = "twenty thirty forty fifty sixty seventy eighty ninety".split()


def number_words(n: int) -> str:
    """Twenty-one, forty-five: the lede's count of lessons, spelled out."""
    if n < 20:
        return NUMBERS[n]
    tens, ones = divmod(n, 10)
    return TENS[tens - 2] + (f"-{NUMBERS[ones]}" if ones else "")


def highlight(text: str) -> str:
    """Comments, keywords and calls, marked up as the page's stylesheet expects."""
    lines = []
    for line in text.rstrip("\n").split("\n"):
        if line.lstrip().startswith("#"):
            lines.append(f'<span class="c">{html.escape(line, quote=True)}</span>')
            continue
        marked = html.escape(line, quote=True)
        marked = re.sub(r"^(\s*)(use|let)\b", r'\1<span class="k">\2</span>', marked)
        marked = re.sub(r"\b([A-Za-z_][A-Za-z0-9_]*)\(", r'<span class="f">\1</span>(', marked)
        lines.append(marked)
    return "\n".join(lines)


def plain(markup: str) -> str:
    return html.unescape(re.sub(r"<[^>]+>", "", markup))


def _shown(name: str, current: str) -> str | None:
    """The lesson text a figure should show: the slice it shows, or the whole file."""
    lines = (LESSONS / name).read_text().rstrip("\n").split("\n")
    shown = current.split("\n")
    for start in range(len(lines) - len(shown) + 1):
        if lines[start : start + len(shown)] == shown:
            return "\n".join(shown)
    if shown and lines and shown[0] == lines[0]:
        return "\n".join(lines)
    return None


def lesson_count() -> int:
    """Lessons are numbered by their files' prefixes; two files may share a lesson."""
    return len({path.name.split("_", 1)[0] for path in LESSONS.glob("*.stat")})


def synced(page: str) -> tuple[str, list[str]]:
    problems: list[str] = []

    def replace(match: re.Match) -> str:
        name, current = match["name"], plain(match["code"])
        if not (LESSONS / name).is_file():
            problems.append(f"{name}: no such lesson file")
            return match.group(0)
        text = _shown(name, current)
        if text is None:
            problems.append(f"{name}: a figure no longer matches the file; update it by hand")
            return match.group(0)
        return match.group(1) + highlight(text) + match.group(4)

    page = FIGURE.sub(replace, page)
    page = LEDE.sub(
        lambda m: m.group(1) + number_words(lesson_count()).capitalize() + m.group(3), page
    )
    shown = {m["name"] for m in FIGURE.finditer(page)}
    problems += [
        f"{path.name}: no figure shows this lesson"
        for path in sorted(LESSONS.glob("*.stat"))
        if path.name not in shown
    ]
    entries = len(re.findall(r'<li><a href="#[^"]+"><span class="n">', page))
    if entries != lesson_count():
        problems.append(f"the contents list {entries} lessons, the files {lesson_count()}")
    return page, problems


def sync() -> int:
    page, problems = synced(PAGE.read_text())
    PAGE.write_text(page)
    for problem in problems:
        print(problem)
    return 1 if problems else 0


def check() -> list[str]:
    """What has drifted, without changing the page."""
    current = PAGE.read_text()
    page, problems = synced(current)
    if page != current:
        problems.append("docs/tutorial.html is out of step; run 'python scripts/tutorial.py sync'")
    return problems


def outputs() -> int:
    """Rerun each lesson that needs no Lean backend; every shown output line must appear."""
    sys.path.insert(0, str(ROOT / "src"))
    from statclaim.language_compiler import compile_source
    from statclaim.language_runner import check_source, render_report
    from statclaim.language_syntax import Source

    problems, checked, skipped = [], 0, []
    for section in SECTION.findall(PAGE.read_text()):
        names = list(dict.fromkeys(m["name"] for m in FIGURE.finditer(section)))
        blocks = [plain(m["code"]) for m in OUTPUT.finditer(section)]
        if not names or not blocks:
            continue
        sources = [Source((LESSONS / name).read_text(), name) for name in names]
        programs = [compile_source(source).program for source in sources]
        if any(
            p is not None and any(r.operation == "verify" for r in p.requests) for p in programs
        ):
            skipped.append(names[0])
            continue
        rendered = []
        for source in sources:
            with tempfile.TemporaryDirectory() as directory:
                report = check_source(source, project=ROOT, output=Path(directory) / "run")
            rendered.append(render_report(report, source))
        # Long messages wrap on the page, and "..." stands for text left out.
        fresh = " ".join(" ".join(rendered).split())
        checked += 1
        for block in blocks:
            for line in block.split("\n"):
                parts = [" ".join(part.split()) for part in line.split("...")]
                if any(part and part not in fresh for part in parts):
                    problems.append(f"{names[0]}: output line not in a fresh run: {line.strip()}")
    for problem in problems:
        print(problem)
    print(f"Checked the outputs of {checked} lessons; {len(skipped)} need Lean and were skipped.")
    return 1 if problems else 0


def main() -> int:
    command = sys.argv[1] if len(sys.argv) > 1 else "check"
    if command == "sync":
        return sync()
    if command == "outputs":
        return outputs()
    problems = check()
    for problem in problems:
        print(problem)
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
