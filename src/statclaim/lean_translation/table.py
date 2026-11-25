"""The Lean meaning or evidence boundary of every DSL constructor and operation.

Each constructor states its entry where it is defined (`Constructor.lean`, with the
vocabulary of language/coverage.py); this module collects them.
"""

from statclaim.language.coverage import (  # noqa: F401  (re-exported)
    PLANNED,
    ROLES,
    InLean,
    NotInLean,
)
from statclaim.language.registry import MODULES, OPERATIONS


def _table() -> dict[str, InLean | NotInLean | None]:
    found = {c.name: c.lean for module in MODULES.values() for c in module.constructors}
    found.update((name, c.lean) for name, c in OPERATIONS.items())
    return found


TABLE = _table()


def summary() -> dict[str, int]:
    """How many constructors and operations have each role, and how many have none."""
    counts: dict[str, int] = {}
    for entry in TABLE.values():
        key = entry.role if isinstance(entry, InLean) else "not in Lean"
        counts[key] = counts.get(key, 0) + 1
    return counts
