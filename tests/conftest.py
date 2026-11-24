"""Tests not marked lean never start Lean, even in a StatClaim checkout with lake installed.
Every check builds its program in Lean, so without this a calculation would start a build."""

import pytest


@pytest.fixture(autouse=True)
def lean_only_when_marked(request, monkeypatch):
    if request.node.get_closest_marker("lean") is None:
        monkeypatch.setattr("statclaim.language_runner.lean_available", lambda project: False)
