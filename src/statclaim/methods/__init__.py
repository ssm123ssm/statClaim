"""Registry of cited methods and outcomes. To add one, write it and list it here.

A method file exports MODULE, a MethodModule. A new test over an existing outcome
and null needs no change outside this package. A new kind of outcome is an entry
in outcomes.py. A power formula is an entry in power.py, named by the methods it
serves. See docs/cited-methods.md.
"""

import hashlib
import inspect

from statclaim import simulation as engine
from statclaim.methods import (
    assumptions,
    cluster,
    logistic,
    mixed_models,
    survival,
    t_distribution,
    t_tests,
)
from statclaim.methods.core import (
    NORMAL_APPROXIMATION,
    Assumption,
    CitedMethod,
    MethodModule,
    NullForm,
    Outcome,
    PowerFormula,
    SimulationModel,
)
from statclaim.methods.observational import METHODS as OBSERVATIONAL
from statclaim.methods.outcomes import OUTCOMES as _OUTCOMES
from statclaim.methods.outcomes import SHARP_NULL

METHOD_MODULES: tuple[MethodModule, ...] = (
    t_tests.MODULE,
    mixed_models.MODULE,
    survival.MODULE,
    logistic.MODULE,
    cluster.MODULE,
)

OUTCOMES: dict[str, Outcome] = {outcome.key: outcome for outcome in _OUTCOMES}
# Every null form by its constructor name, with the outcome it belongs to.
NULL_FORMS: dict[str, tuple[Outcome, NullForm]] = {}
for _outcome in _OUTCOMES:
    for _form in _outcome.nulls:
        if _form.key in NULL_FORMS:
            raise ValueError(f"Null form {_form.key!r} is defined twice.")
        NULL_FORMS[_form.key] = (_outcome, _form)
# The sharp null is no outcome's null, so a cited method can never name it.
if SHARP_NULL.key in NULL_FORMS:
    raise ValueError("The sharp null may not be listed as an outcome's null.")

METHODS: dict[str, CitedMethod] = {}
for _module in METHOD_MODULES:
    for _method in _module.methods:
        if _method.key in METHODS or _method.module != _module.name:
            raise ValueError(f"Method {_method.key!r} is duplicated or names the wrong module.")
        for _null in _method.nulls:
            if NULL_FORMS.get(_null, (None,))[0] is not OUTCOMES.get(_method.outcome):
                raise ValueError(f"Method {_method.key!r} names a null its outcome does not have.")
        if _method.mirrored_null and {NULL_FORMS[n][1].favours for n in _method.nulls} != {
            "higher",
            "lower",
        }:
            raise ValueError(f"Method {_method.key!r}: a mirrored null must face the other way.")
        METHODS[_method.key] = _method

# The planning point each outcome's power formulas take: the first is the main one, and
# simulation models take it too. A survival outcome can also be planned at its times.
POINTS_OF_OUTCOME = {
    "continuous": ("mean_difference",),
    "binary": ("binomial_rates",),
    "survival": ("hazard_ratio", "exponential_survival"),
}
POINT_OF_OUTCOME = {outcome: points[0] for outcome, points in POINTS_OF_OUTCOME.items()}
POWER_FORMULAS: dict[str, PowerFormula] = {}
for _method in METHODS.values():
    if _method.power is None and _method.more_power:
        raise ValueError(f"Method {_method.key!r} has further formulas but no main one.")
    if _method.power is not None and _method.power.point != POINT_OF_OUTCOME[_method.outcome]:
        raise ValueError(f"Method {_method.key!r} has a main power formula at another point.")
    _points = [_formula.point for _formula in _method.formulas]
    if len(set(_points)) != len(_points):
        raise ValueError(f"Method {_method.key!r} has two power formulas at one point.")
    for _formula in _method.formulas:
        if _formula.point not in POINTS_OF_OUTCOME.get(_method.outcome, ()):
            raise ValueError(f"Method {_method.key!r} has a power formula for another outcome.")
        if POWER_FORMULAS.setdefault(_formula.key, _formula) is not _formula:
            raise ValueError(f"Power formula {_formula.key!r} is defined twice.")

# Simulation models, by key. Each serves methods at its outcome's planning point.
SIMULATIONS: dict[str, SimulationModel] = {}
for _method in METHODS.values():
    _model = _method.simulation
    if _model is None:
        continue
    if _model.point != POINT_OF_OUTCOME.get(_method.outcome):
        raise ValueError(f"Method {_method.key!r} has a simulation model for another outcome.")
    if SIMULATIONS.setdefault(_model.key, _model) is not _model:
        raise ValueError(f"Simulation model {_model.key!r} is defined twice.")

# Every assumption in use, by id. Two different assumptions may not share an id.
ASSUMPTIONS: dict[str, Assumption] = {
    value.id: value for value in vars(assumptions).values() if isinstance(value, Assumption)
}
ASSUMPTIONS.update({value.id: value for value in assumptions.ACCOUNTS_FOR.values()})
for _item in (*METHODS.values(), *POWER_FORMULAS.values(), *SIMULATIONS.values()):
    for _assumption in _item.assumptions:
        if ASSUMPTIONS.setdefault(_assumption.id, _assumption) != _assumption:
            raise ValueError(f"Assumption id {_assumption.id!r} has two meanings.")


def methods_for(outcome: str) -> list[CitedMethod]:
    return [method for method in METHODS.values() if method.outcome == outcome]


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def method_content(method: CitedMethod) -> str:
    """What a method's version vouches for. A mirrored null counts only when it is set."""
    mirror = f" mirrored_null={method.mirrored_null!r}" if method.mirrored_null else ""
    unit = f" unit={method.unit!r}" if method.unit != "participant" else ""
    return repr(method) + mirror + unit


def versions() -> dict:
    """Each entry's version and a hash of its content, for tests/fixtures/method_versions.json.

    A power formula's hash covers its function's source and the methods that use it.
    """
    recorded = {
        key: {"version": method.version, "sha256": _sha256(method_content(method))}
        for key, method in METHODS.items()
    }
    for key, formula in POWER_FORMULAS.items():
        users = sorted(m.key for m in METHODS.values() if any(f is formula for f in m.formulas))
        content = repr(formula) + inspect.getsource(formula.function) + repr(users)
        if formula.approximation != NORMAL_APPROXIMATION:
            content += f" approximation={formula.approximation!r}"
        recorded[f"power:{key}"] = {"version": formula.version, "sha256": _sha256(content)}
    for key, model in SIMULATIONS.items():
        users = sorted(m.key for m in METHODS.values() if m.simulation is model)
        content = (
            repr(model)
            + inspect.getsource(model.trial)
            + inspect.getsource(model.scenario)
            + repr(users)
        )
        recorded[f"simulation:{key}"] = {"version": model.version, "sha256": _sha256(content)}
    # Power formulas of the cited observational tests, which take the total and covariates.
    known = {f.key: f for m in OBSERVATIONAL.values() for f in m.formulas}
    for formula in known.values():
        users = sorted(
            m.key for m in OBSERVATIONAL.values() if any(f is formula for f in m.formulas)
        )
        content = repr(formula) + inspect.getsource(formula.function) + repr(users)
        if formula.approximation != NORMAL_APPROXIMATION:
            content += f" approximation={formula.approximation!r}"
        recorded[f"power:{formula.key}"] = {"version": formula.version, "sha256": _sha256(content)}
    # The t distribution behind the power of tests of cluster summaries.
    recorded["power:t_distribution"] = {
        "version": t_distribution.VERSION,
        "sha256": _sha256(inspect.getsource(t_distribution)),
    }
    # The engine draws every simulated study; any change to it can change results.
    recorded["simulation:engine"] = {
        "version": engine.ENGINE_VERSION,
        "sha256": _sha256(inspect.getsource(engine)),
    }
    return recorded
