"""Registry of cited methods. To add one, write a method file and list it here.

A method file exports MODULE, a MethodModule. Nothing else in the codebase needs
to change for a new test over an existing model and null. See docs/cited-methods.md.
"""

from statclaim.methods import assumptions, t_tests
from statclaim.methods.core import Assumption, CitedMethod, MethodModule

METHOD_MODULES: tuple[MethodModule, ...] = (t_tests.MODULE,)

METHODS: dict[str, CitedMethod] = {}
for _module in METHOD_MODULES:
    for _method in _module.methods:
        if _method.key in METHODS or _method.module != _module.name:
            raise ValueError(f"Method {_method.key!r} is duplicated or names the wrong module.")
        METHODS[_method.key] = _method

# Every assumption in use, by id. Two different assumptions may not share an id.
ASSUMPTIONS: dict[str, Assumption] = {
    value.id: value for value in vars(assumptions).values() if isinstance(value, Assumption)
}
for _method in METHODS.values():
    for _assumption in _method.assumptions:
        if ASSUMPTIONS.setdefault(_assumption.id, _assumption) != _assumption:
            raise ValueError(f"Assumption id {_assumption.id!r} has two meanings.")
