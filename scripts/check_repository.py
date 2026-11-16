"""Reject private assistant files, build output and attribution trailers in git."""

import re
import subprocess
from pathlib import PurePosixPath

PRIVATE = {"agents.md", "agents.local.md", "memory.md", "memory.local.md"}
DIRECTORIES = {
    ".codex",
    ".claude",
    ".agents",
    ".agent",
    "memory",
    ".venv",
    "node_modules",
    ".lake",
    ".statclaim",
    "__pycache__",
    ".pytest_cache",
    ".ruff_cache",
    "dist",
}
files = subprocess.check_output(["git", "ls-files", "-z"]).decode().split("\0")
bad = []
for file in filter(None, files):
    path = PurePosixPath(file.lower())
    if (
        path.name in PRIVATE
        or (path.name.startswith("memory") and path.suffix == ".md")
        or path.name.endswith("_memory.md")
        or set(path.parts) & DIRECTORIES
        or path.suffix in {".vsix", ".pyc"}
        or path.name == ".env"
        or (path.name.startswith(".env.") and path.name != ".env.example")
    ):
        bad.append(file)
messages = subprocess.check_output(["git", "log", "--format=%B", "HEAD"]).decode()
if re.search(r"^\s*(co-authored-by|coauthor|contributor):", messages, re.I | re.M):
    bad.append("commit history contains a co-author/contributor trailer")
if bad:
    raise SystemExit("Repository policy failed:\n" + "\n".join(bad))
print("Repository policy passed")
