"""Registry of cited methods and outcomes. To add one, write it and list it here.

A method file exports MODULE, a MethodModule. A new test over an existing outcome
and null needs no change outside this package. A new kind of outcome is an entry
in outcomes.py. See docs/cited-methods.md.
"""

from statclaim.methods import assumptions, survival, t_tests
from statclaim.methods.core import Assumption, CitedMethod, MethodModule, NullForm, Outcome
from statclaim.methods.outcomes import OUTCOMES as _OUTCOMES

METHOD_MODULES: tuple[MethodModule, ...] = (t_tests.MODULE, survival.MODULE)

OUTCOMES: dict[str, Outcome] = {outcome.key: outcome for outcome in _OUTCOMES}
# Every null form by its constructor name, with the outcome it belongs to.
NULL_FORMS: dict[str, tuple[Outcome, NullForm]] = {}
for _outcome in _OUTCOMES:
    for _form in _outcome.nulls:
        if _form.key in NULL_FORMS:
            raise ValueError(f"Null form {_form.key!r} is defined twice.")
        NULL_FORMS[_form.key] = (_outcome, _form)

METHODS: dict[str, CitedMethod] = {}
for _module in METHOD_MODULES:
    for _method in _module.methods:
        if _method.key in METHODS or _method.module != _module.name:
            raise ValueError(f"Method {_method.key!r} is duplicated or names the wrong module.")
        if NULL_FORMS.get(_method.null, (None,))[0] is not OUTCOMES.get(_method.outcome):
            raise ValueError(f"Method {_method.key!r} names a null its outcome does not have.")
        METHODS[_method.key] = _method

# Every assumption in use, by id. Two different assumptions may not share an id.
ASSUMPTIONS: dict[str, Assumption] = {
    value.id: value for value in vars(assumptions).values() if isinstance(value, Assumption)
}
for _method in METHODS.values():
    for _assumption in _method.assumptions:
        if ASSUMPTIONS.setdefault(_assumption.id, _assumption) != _assumption:
            raise ValueError(f"Assumption id {_assumption.id!r} has two meanings.")


def methods_for(outcome: str) -> list[CitedMethod]:
    return [method for method in METHODS.values() if method.outcome == outcome]
