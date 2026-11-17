"""Registry of cited methods and outcomes. To add one, write it and list it here.

A method file exports MODULE, a MethodModule. A new test over an existing outcome
and null needs no change outside this package. A new kind of outcome is an entry
in outcomes.py. A power formula is an entry in power.py, named by the methods it
serves. See docs/cited-methods.md.
"""

import hashlib
import inspect

from statclaim.methods import assumptions, logistic, mixed_models, survival, t_tests
from statclaim.methods.core import (
    Assumption,
    CitedMethod,
    MethodModule,
    NullForm,
    Outcome,
    PowerFormula,
)
from statclaim.methods.outcomes import OUTCOMES as _OUTCOMES

METHOD_MODULES: tuple[MethodModule, ...] = (
    t_tests.MODULE,
    mixed_models.MODULE,
    survival.MODULE,
    logistic.MODULE,
)

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

# The planning point each outcome's power formulas take.
POINT_OF_OUTCOME = {
    "continuous": "mean_difference",
    "binary": "binomial_rates",
    "survival": "hazard_ratio",
}
POWER_FORMULAS: dict[str, PowerFormula] = {}
for _method in METHODS.values():
    _formula = _method.power
    if _formula is None:
        continue
    if _formula.point != POINT_OF_OUTCOME.get(_method.outcome):
        raise ValueError(f"Method {_method.key!r} has a power formula for another outcome.")
    if POWER_FORMULAS.setdefault(_formula.key, _formula) is not _formula:
        raise ValueError(f"Power formula {_formula.key!r} is defined twice.")

# Every assumption in use, by id. Two different assumptions may not share an id.
ASSUMPTIONS: dict[str, Assumption] = {
    value.id: value for value in vars(assumptions).values() if isinstance(value, Assumption)
}
for _item in (*METHODS.values(), *POWER_FORMULAS.values()):
    for _assumption in _item.assumptions:
        if ASSUMPTIONS.setdefault(_assumption.id, _assumption) != _assumption:
            raise ValueError(f"Assumption id {_assumption.id!r} has two meanings.")


def methods_for(outcome: str) -> list[CitedMethod]:
    return [method for method in METHODS.values() if method.outcome == outcome]


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def versions() -> dict:
    """Each entry's version and a hash of its content, for tests/fixtures/method_versions.json.

    A power formula's hash covers its function's source and the methods that use it.
    """
    recorded = {
        key: {"version": method.version, "sha256": _sha256(repr(method))}
        for key, method in METHODS.items()
    }
    for key, formula in POWER_FORMULAS.items():
        users = sorted(m.key for m in METHODS.values() if m.power is formula)
        content = repr(formula) + inspect.getsource(formula.function) + repr(users)
        recorded[f"power:{key}"] = {"version": formula.version, "sha256": _sha256(content)}
    return recorded
