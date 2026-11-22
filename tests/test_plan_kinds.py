"""The table of planning kinds: every entry resolves, and every plannable analysis has one."""

import inspect

import pytest

from statclaim import language
from statclaim.plan_kinds import KINDS, kind_of, resolve


@pytest.mark.parametrize("kind", KINDS, ids=lambda kind: kind.name)
def test_every_entry_names_real_functions(kind):
    for path in (
        kind.describe,
        kind.derive,
        kind.calculate,
        kind.check_calculate,
        kind.check_simulate,
        kind.when,
    ):
        if path is not None:
            assert callable(resolve(path)), path
    assert inspect.isclass(resolve(kind.details))
    assert all(hasattr(language, name) for name in kind.classes), kind.classes
    # A kind either runs calculate(...) or says why it cannot.
    assert kind.calculate is not None or kind.refuse_calculate
    assert kind.check_simulate is not None or kind.refuse_simulate


# Shared bases, never an analysis themselves.
ABSTRACT = {"PlannableIR", "TwoArmTestIR", "FamilyLikeIR"}


def test_every_plannable_analysis_has_a_kind():
    plannable = [
        cls
        for cls in vars(language).values()
        if inspect.isclass(cls)
        and issubclass(cls, language.PlannableIR)
        and cls.__name__ not in ABSTRACT
    ]
    assert len(plannable) >= 10
    names = {name for kind in KINDS for name in kind.classes}
    for cls in plannable:
        assert {base.__name__ for base in cls.__mro__} & names, cls.__name__


def test_order_puts_the_narrower_kind_first():
    names = [kind.name for kind in KINDS]
    # A design with looks is also a family; a margin test is also a two-arm analysis.
    assert names.index("looks") < names.index("family")
    assert names.index("margin") < names.index("fisher")
    assert kind_of.__doc__
