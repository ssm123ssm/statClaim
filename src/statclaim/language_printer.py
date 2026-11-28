"""Print a canonical program as StatClaim source.

The canonical program is the record a .stat file compiles to: what a certificate binds and
what Lean reads. This module writes it back as source, so a reader sees exactly what was
checked: every number exact and every value spelled out where it is used, with nothing the
record does not hold. A value equal to an earlier binding is written as that binding's name.

The printer reads the record alone and imports nothing from the compiler, so it is a second,
independent reading of the canonical form. Compiling the printed source must give the same
record again; the tests check this on every program in the repository and on respellings of
them. A mismatch means the compiler and this reading disagree about what a file says.
"""

import json
from collections.abc import Callable, Sequence
from contextvars import ContextVar
from random import Random
from typing import Any

from statclaim.wald import PROPORTION_Z_TESTS

RESULTS = ("VerificationResultIR", "CalculationResultIR")
PIECES = {
    "two_arm_binomial": "binary_outcome",
    "two_arm_continuous": "continuous_outcome",
    "two_arm_survival": "survival_outcome",
}
# What the two-arm shorthands take; any other entry needs two_arm(assignment, outcome).
SHORTHAND = {"module", "n_control", "n_treatment", "better", "population", "outcome_name"}
LOOKS = ("alpha_spending", "group_sequential")
NOT_FISHER = {"greater": "fisher_one_sided", "margin": "difference_test"}
UNNAMED = "<expression>"


class Unprintable(ValueError):
    """The record holds a value this printer does not know how to write."""


# Set only while printing with a seed: the keyword order of every call is then shuffled.
_ORDER: ContextVar[Random | None] = ContextVar("statclaim_printer_order", default=None)


def program_source(
    program: dict, *, share: bool = True, seed: int | None = None, hoist: bool = False
) -> str:
    """The program as source: its modules, then its statements in their original order.

    With share=False a value is written in place even when an earlier binding holds it, except
    where the record keeps the name: a family's members, a claim's subject and a result. A seed
    shuffles every call's keywords. With hoist=True every value inside another is bound to a
    name of its own first, so the record gains bindings of every kind of value. All three are
    for tests: every spelling must compile to the same record, up to those bindings.
    """
    token = _ORDER.set(None if seed is None else Random(seed))
    try:
        return _Printer(program, share, hoist).text()
    finally:
        _ORDER.reset(token)


def _string(value: object) -> str:
    if not isinstance(value, str):
        raise Unprintable(f"Expected a string, found {value!r}.")
    return json.dumps(value, ensure_ascii=False)


def _integer(value: object) -> str:
    if type(value) is not int:
        raise Unprintable(f"Expected a whole number, found {value!r}.")
    return str(value)


def _number(value: object) -> str:
    """An exact number: an integer, or a fraction recorded as text such as "3/1000"."""
    if type(value) is int:
        return str(value)
    if not isinstance(value, str) or not value:
        raise Unprintable(f"Expected an exact number, found {value!r}.")
    numerator, _, denominator = value.partition("/")
    for part in (numerator.removeprefix("-"), denominator or "1"):
        if not part.isdigit():
            raise Unprintable(f"Expected an exact number, found {value!r}.")
    return value


def _strings(value: object) -> str:
    return "[" + ", ".join(_string(item) for item in _list(value)) + "]"


def _numbers(value: object) -> str:
    return "[" + ", ".join(_number(item) for item in _list(value)) + "]"


def _rows(value: object) -> str:
    return "[" + ", ".join(_numbers(row) for row in _list(value)) + "]"


def _list(value: object) -> list:
    if not isinstance(value, list):
        raise Unprintable(f"Expected a list, found {value!r}.")
    return value


def _call(name: str, arguments: list[tuple[str, str | None]]) -> str:
    written = [f"{key}={text}" for key, text in arguments if text]
    order = _ORDER.get()
    if order is not None:
        order.shuffle(written)
    return f"{name}(" + ", ".join(written) + ")"


Writer = Callable[[Any], str | None]


class _Printer:
    def __init__(self, program: dict, share: bool = True, hoist: bool = False):
        self.program = program
        self.share = share
        self.hoist = hoist
        self.pending: list[str] = []  # bindings a hoisted statement needs first
        self.hoisted = 0
        self.requests = {request["request_id"]: request for request in program["requests"]}
        self.bound: list[tuple[str, object]] = []  # earlier bindings: name and value

    # Statements ---------------------------------------------------------------------------

    def text(self) -> str:
        lines = [f"use {module}" for module in self.program["modules"]]
        statements = [(b["source"], "let", b) for b in self.program["bindings"]]
        inside = [
            r
            for r in self.program["requests"]
            if any(_within(r["source"], b["source"]) for b in self.program["bindings"])
        ]
        statements += [
            (r["source"], "request", r) for r in self.program["requests"] if r not in inside
        ]
        statements.sort(key=lambda item: (item[0]["line"], item[0]["column"]))
        for _, kind, item in statements:
            if kind == "let":
                written = f"let {item['name']} = {self.binding(item)}"
                lines += [*self.pending, written]
                self.pending.clear()
                self.bound.append((item["name"], item["value"]))
            else:
                written = self.request(item)
                lines += [*self.pending, written]
                self.pending.clear()
        return "\n".join(lines) + "\n"

    def binding(self, binding: dict) -> str:
        kind, value = binding["type"], binding["value"]
        if kind in RESULTS:
            # Another name for a result already requested: requesting it again would not.
            name = self.reference(value, share=True)
            return name or self.request(self.requests[value["request_id"]])
        if isinstance(value, dict) and "field" in value:
            return self.field(value)
        if kind in ("int", "Option[integer]", "integer"):
            return _integer(value)
        if kind in ("Fraction", "Option[exact number]", "exact number", "number"):
            return _number(value)
        if kind in ("str", "string", "Option[string]"):
            return _string(value)
        if kind in ("tuple", "list", "Option[list]"):
            return self.items(value)
        return self.value(value, inline=True)

    def request(self, request: dict) -> str:
        claim = self.reference(request["claim"]) or self.claim(request["claim"])
        if request["operation"] == "simulate":
            settings = request["settings"]
            return _call(
                "simulate",
                [
                    ("claim", claim),
                    ("seed", _integer(settings["seed"])),
                    ("runs", _integer(settings["runs"])),
                ],
            )
        return f"{request['operation']}({claim})"

    def field(self, value: dict) -> str:
        subject = value["subject"]
        if isinstance(subject, dict) and "field" in subject:
            return f"{self.field(subject)}.{value['field']}"
        if isinstance(subject, dict) and set(subject) == {"request_id"}:
            name = self.reference(subject, share=True)
            text = name if name else self.request(self.requests[subject["request_id"]])
            return f"{text}.{value['field']}"
        return f"{self.value(subject)}.{value['field']}"

    def items(self, value: object) -> str:
        return "[" + ", ".join(self.value(item) for item in _list(value)) + "]"

    # Values -------------------------------------------------------------------------------

    def reference(
        self, value: object, prefer: str | None = None, share: bool | None = None
    ) -> str | None:
        """`prefer` when that earlier binding holds this value; otherwise, when sharing, the
        latest earlier binding that does."""
        names = [name for name, bound in self.bound if bound == value]
        if prefer in names:
            return prefer
        share = self.share if share is None else share
        return names[-1] if names and share else None

    def value(self, value: object, prefer: str | None = None, inline: bool = False) -> str:
        if not inline and isinstance(value, dict):
            name = self.reference(value, prefer)
            if name:
                return name
        if not isinstance(value, dict):
            raise Unprintable(f"Expected a value with fields, found {value!r}.")
        if "field" in value:
            return self.field(value)
        if set(value) == {"request_id"}:
            # A result is requested once; every later use names it.
            name = self.reference(value, share=True)
            return name or self.request(self.requests[value["request_id"]])
        text = self.call(value)
        if inline or not self.hoist:
            return text
        self.hoisted += 1
        name = f"hoisted_{self.hoisted}"
        self.pending.append(f"let {name} = {text}")
        self.bound.append((name, value))
        return name

    def call(self, value: dict) -> str:
        for key, write in self.SHAPES:
            if key in value:
                return write(self, value)
        if any(key in value for key in self.POINTS):
            return self.point(value)
        raise Unprintable(f"No constructor writes a value with fields {sorted(value)}.")

    def arguments(
        self, value: dict, fields: Sequence[tuple[str, str, Any]]
    ) -> list[tuple[str, str | None]]:
        """(argument, text) for each field present: (record key, argument name, writer)."""
        unknown = set(value) - {key for key, _, _ in fields}
        if unknown:
            raise Unprintable(f"Unexpected fields {sorted(unknown)} in {value!r}.")
        return [(name, write(value[key])) for key, name, write in fields if name and key in value]

    def nested(self, value: object) -> str:
        return self.value(value)

    # Models and studies -------------------------------------------------------------------

    def model(self, value: dict) -> str:
        module = value["module"]
        if module == "one_arm_binomial":
            return _call(module, self.arguments(value, [("module", "", str), ("n", "n", _integer)]))
        if module == "two_stage_binomial":
            fields = [("n_stage1", "n_stage1", _integer), ("n_stage2", "n_stage2", _integer)]
            return _call(module, self.arguments(value, [("module", "", str), *fields]))
        if module not in PIECES:
            raise Unprintable(f"Unknown model {module!r}.")
        if set(value) <= SHORTHAND:
            fields = [
                ("n_control", "n_control", _integer),
                ("n_treatment", "n_treatment", _integer),
                ("better", "better", _string),
                ("population", "population", _string),
                ("outcome_name", "name", _string),
            ]
            rest = {key: item for key, item in value.items() if key != "module"}
            return _call(module, self.arguments(rest, fields))
        assignment = {
            key: value[key]
            for key in (
                "clusters_control",
                "clusters_treatment",
                "n_control",
                "n_treatment",
                "randomisation",
                "strata",
                "block_size",
                "population",
            )
            if key in value
        }
        outcome = {
            key: value[key] for key in ("better", "measurements", "outcome_name") if key in value
        }
        unknown = set(value) - set(assignment) - set(outcome) - {"module"}
        if unknown:
            raise Unprintable(f"Unexpected fields {sorted(unknown)} in a model.")
        return _call(
            "two_arm",
            [
                ("assignment", self.assignment(assignment)),
                ("outcome", self.outcome(module, outcome)),
            ],
        )

    def assignment(self, value: dict) -> str:
        clustered = "clusters_control" in value
        fields = [
            *(
                [
                    ("clusters_control", "clusters_control", _integer),
                    ("clusters_treatment", "clusters_treatment", _integer),
                ]
                if clustered
                else []
            ),
            ("n_control", "n_control", _integer),
            ("n_treatment", "n_treatment", _integer),
            ("randomisation", "randomisation", _string),
            ("strata", "strata", self.strata),
            ("block_size", "block_size", _integer),
            ("population", "population", _string),
        ]
        return _call(
            "cluster_assignment" if clustered else "assignment", self.arguments(value, fields)
        )

    def strata(self, value: object) -> str:
        written = []
        for stratum in _list(value):
            control, treatment = _list(stratum)
            written.append(
                _call(
                    "stratum", [("control", _integer(control)), ("treatment", _integer(treatment))]
                )
            )
        return "[" + ", ".join(written) + "]"

    def outcome(self, module: str, value: dict) -> str:
        fields = [
            ("better", "better", _string),
            ("measurements", "measurements", _integer),
            ("outcome_name", "name", _string),
        ]
        return _call(PIECES[module], self.arguments(value, fields))

    def study(self, value: dict) -> str:
        fields = [
            ("study", "", str),
            *(
                (key, key, _integer)
                for key in ("n", "exposed", "unexposed", "cases", "controls", "pairs", "clusters")
            ),
            *(
                (key, key, _string)
                for key in ("exposure", "outcome", "exposure_scale", "outcome_scale", "survey")
            ),
        ]
        return _call(value["study"], self.arguments(value, fields))

    # Nulls, designs and analyses ----------------------------------------------------------

    def null(self, value: dict) -> str:
        fields = [
            ("predicate", "", str),
            ("model", "model", self.nested),
            ("value", "value", _number),
        ]
        return _call(value["predicate"], self.arguments(value, fields))

    def plan(self, value: dict) -> str:
        stopping = {"fixed": "fixed", "data_dependent": "adaptive"}.get(value["stopping"])
        if stopping is None:
            raise Unprintable(f"Unknown stopping {value['stopping']!r}.")
        fields = [("stopping", "", str), ("model", "model", self.nested)]
        return _call(stopping, self.arguments(value, fields))

    def analysis(self, value: dict) -> str:
        test = value["test"]
        common = [
            ("test", "", str),
            ("design", "design", self.nested),
            ("null", "null", self.nested),
            ("alpha", "alpha", _number),
        ]
        if test == "fisher":
            name = NOT_FISHER.get(value.get("alternative", "two_sided"), "fisher")
            if "alternative" in value and value["alternative"] not in NOT_FISHER:
                raise Unprintable(f"Unknown alternative {value['alternative']!r}.")
            return _call(name, self.arguments(value, [*common, ("alternative", "", str)]))
        if test in (*PROPORTION_Z_TESTS, "mcnemar_asymptotic", "farrington_manning"):
            return _call(
                test,
                self.arguments(value, [*common, ("squared_cutoff", "squared_cutoff", _number)]),
            )
        if test == "randomisation":
            fields = [*common, ("draws", "draws", _integer)]
            return _call("randomisation_test", self.arguments(value, fields))
        if test == "two_stage":
            fields = [
                ("test", "", str),
                ("design", "design", self.nested),
                ("rule", "rule", self.rule),
                ("null_rate", "null_rate", _number),
            ]
            return _call("two_stage_test", self.arguments(value, fields))
        if test in ("binomial_exact_one_sided", "binomial_score_test"):
            fields = [
                ("test", "", str),
                ("model", "model", self.nested),
                ("null_rate", "null_rate", _number),
                ("alpha", "alpha", _number),
            ]
            if test == "binomial_score_test":
                fields.append(("squared_cutoff", "squared_cutoff", _number))
                return _call(test, self.arguments(value, fields))
            return _call("binomial_test", self.arguments(value, fields))
        if "method" in value:
            references = _list(value.get("references", []))
            if len(references) > 1:
                raise Unprintable("A declared test names at most one reference.")
            arguments = self.arguments(
                {key: item for key, item in value.items() if key != "references"},
                [
                    *common,
                    ("method", "method", _string),
                    ("scope", "scope", _string),
                ],
            )
            if references:
                arguments.append(("reference", _string(references[0])))
            return _call(test, arguments)
        fields = [*common, ("adjusted_for", "adjusted_for", _strings)]
        return _call(test, self.arguments(value, fields))

    def rule(self, value: object) -> str:
        if not isinstance(value, dict):
            raise Unprintable(f"Expected a stage rule, found {value!r}.")
        if value.get("kind") == "threshold":
            fields = [
                ("kind", "", str),
                ("continue_above", "continue_above", _integer),
                ("reject_above", "reject_above", _integer),
            ]
            return _call("threshold_rule", self.arguments(value, fields))
        if value.get("kind") == "posterior":
            prior = _call(
                "beta_prior",
                [("a", _integer(value["prior_a"])), ("b", _integer(value["prior_b"]))],
            )
            fields = [
                ("kind", "", str),
                ("prior_a", "", str),
                ("prior_b", "", str),
                ("reference", "reference", _number),
                ("continue_at_least", "continue_at_least", _number),
                ("success_at_least", "success_at_least", _number),
            ]
            return _call("posterior_rule", [("prior", prior), *self.arguments(value, fields)])
        raise Unprintable(f"Unknown stage rule {value!r}.")

    def combination(self, value: dict) -> str:
        method = value["method"]
        members = "[" + ", ".join(self.member(member) for member in _list(value["analyses"])) + "]"
        fields = [
            ("method", "", str),
            ("composition", "", str),
            ("analyses", "", str),
            ("alpha", "alpha", _number),
            ("weights", "weights", _numbers),
            ("transitions", "transitions", _rows),
            ("spending", "spending", _string),
            ("joint_law", "joint_law", lambda law: None if law is None else _string(law)),
        ]
        key = "looks" if method in LOOKS else "analyses"
        return _call(method, [(key, members), *self.arguments(value, fields)])

    def member(self, member: object) -> str:
        if not isinstance(member, dict) or set(member) != {"name", "analysis"}:
            raise Unprintable(f"Expected a named member, found {member!r}.")
        name = self.reference(member["analysis"], member["name"])
        if name is None or name != member["name"]:
            raise Unprintable(f"The member {member['name']!r} is not an earlier binding.")
        return name

    # Observations -------------------------------------------------------------------------

    def observed(self, value: dict) -> str:
        """A table, pairs, events or responses observed for an analysis or a study."""
        keys = set(value)
        fields: list[tuple[str, str, Writer]]
        if {"control_successes", "treatment_successes", "analysis"} == keys:
            fields = [
                ("analysis", "analysis", self.nested),
                ("control_successes", "control_successes", _integer),
                ("treatment_successes", "treatment_successes", _integer),
            ]
            return _call("observe", self.arguments(value, fields))
        if "stage1_responses" in keys:
            fields = [
                ("analysis", "analysis", self.nested),
                ("stage1_responses", "stage1_responses", _integer),
                (
                    "stage2_responses",
                    "stage2_responses",
                    lambda count: None if count is None else _integer(count),
                ),
            ]
            name = (
                "stopped_at_interim"
                if value.get("stage2_responses") is None
                else "completed_stages"
            )
            return _call(name, self.arguments(value, fields))
        if keys == {"analysis", "responses"}:
            fields = [("analysis", "analysis", self.nested), ("responses", "count", _integer)]
            return _call("responses", self.arguments(value, fields))
        if "exposed_events" in keys:
            fields = [
                ("model", "model", self.nested),
                ("exposed_events", "exposed_events", _integer),
                ("exposed_time", "exposed_time", _number),
                ("unexposed_events", "unexposed_events", _integer),
                ("unexposed_time", "unexposed_time", _number),
            ]
            return _call("observed_events", self.arguments(value, fields))
        if "both_exposed" in keys:
            cells = ("both_exposed", "case_exposed_only", "control_exposed_only", "neither_exposed")
            fields = [("model", "model", self.nested), *((c, c, _integer) for c in cells)]
            return _call("observed_pairs", self.arguments(value, fields))
        if "exposed_cases" in keys:
            cells = ("exposed_cases", "exposed_noncases", "unexposed_cases", "unexposed_noncases")
            fields = [("model", "model", self.nested), *((c, c, _integer) for c in cells)]
            return _call("observed_table", self.arguments(value, fields))
        raise Unprintable(f"No constructor writes an observation with fields {sorted(keys)}.")

    # Planning -----------------------------------------------------------------------------

    POINTS: dict[str, tuple[str, list[tuple[str, str, Writer]]]] = {
        "p_control": (
            "binomial_rates",
            [
                ("p_control", "p_control", _number),
                ("p_treatment", "p_treatment", _number),
                ("icc", "icc", _number),
                ("cluster_size_cv", "cluster_size_cv", _number),
            ],
        ),
        "response_rate": ("response_rate", [("response_rate", "value", _number)]),
        "risk_unexposed": (
            "risks",
            [
                ("risk_unexposed", "unexposed", _number),
                ("risk_exposed", "exposed", _number),
                ("exposed_share", "exposed_share", _number),
            ],
        ),
        "prevalence_unexposed": (
            "outcome_prevalence",
            [
                ("prevalence_unexposed", "unexposed", _number),
                ("prevalence_exposed", "exposed", _number),
                ("exposed_share", "exposed_share", _number),
                ("design_effect", "design_effect", _number),
            ],
        ),
        "exposure_controls": (
            "exposure_prevalence",
            [("exposure_controls", "controls", _number), ("exposure_cases", "cases", _number)],
        ),
        "discordant": (
            "discordant_pairs",
            [("discordant", "share", _number), ("odds_ratio", "odds_ratio", _number)],
        ),
        "rate_ratio": (
            "incidence_rates",
            [
                ("rate_ratio", "rate_ratio", _number),
                ("exposed_time", "exposed_time", _number),
                ("unexposed_time", "unexposed_time", _number),
                ("events", "events", _integer),
            ],
        ),
        "mean_difference": (
            "mean_difference",
            [
                ("mean_difference", "value", _number),
                ("sd", "sd", _number),
                ("icc", "icc", _number),
                ("cluster_size_cv", "cluster_size_cv", _number),
                ("sd_treatment", "sd_treatment", _number),
                ("skewness", "skewness", _number),
            ],
        ),
        "control_median": (
            "exponential_survival",
            [
                ("hazard_ratio", "hazard_ratio", _number),
                ("control_median", "control_median", _number),
                ("accrual", "accrual", _number),
                ("follow_up", "follow_up", _number),
                ("dropout", "dropout", _number),
                ("dropout_time", "dropout_time", _number),
                ("effect_delay", "effect_delay", _number),
            ],
        ),
        "hazard_ratio": (
            "hazard_ratio",
            [("hazard_ratio", "value", _number), ("events", "events", _integer)],
        ),
        "correlation": (
            "correlation",
            [
                ("correlation", "value", _number),
                ("skewness", "skewness", _number),
                ("exposure_skewness", "exposure_skewness", _number),
            ],
        ),
        "mean_unexposed": (
            "outcome_means",
            [
                ("mean_unexposed", "unexposed", _number),
                ("mean_exposed", "exposed", _number),
                ("sd", "sd", _number),
                ("exposed_share", "exposed_share", _number),
                ("design_effect", "design_effect", _number),
            ],
        ),
        "odds_ratio_per_sd": (
            "odds_per_sd",
            [
                ("odds_ratio_per_sd", "odds_ratio", _number),
                ("baseline", "baseline", _number),
                ("exposure_r2", "exposure_r2", _number),
                ("design_effect", "design_effect", _number),
            ],
        ),
        "slope": (
            "slope",
            [
                ("slope", "value", _number),
                ("exposure_sd", "exposure_sd", _number),
                ("residual_sd", "residual_sd", _number),
                ("exposure_r2", "exposure_r2", _number),
                ("design_effect", "design_effect", _number),
                ("skewness", "skewness", _number),
                ("exposure_skewness", "exposure_skewness", _number),
            ],
        ),
        "proportion": (
            "proportion",
            [
                ("proportion", "value", _number),
                ("design_effect", "design_effect", _number),
                ("population_size", "population_size", _integer),
            ],
        ),
    }

    def point(self, value: dict) -> str:
        if "endpoints" in value:
            points = "[" + ", ".join(self.value(item) for item in _list(value["endpoints"])) + "]"
            written = [("endpoints", "", str), ("correlation", "correlation", _number)]
            return _call("endpoint_points", [("at", points), *self.arguments(value, written)])
        if "null_scenarios" in value:
            points = "[" + ", ".join(self.value(i) for i in _list(value["null_scenarios"])) + "]"
            return _call("null_scenarios", [("at", points)])
        for key, (name, fields) in self.POINTS.items():
            if key in value:
                return _call(name, self.arguments(value, fields))
        raise Unprintable(f"No planning point has fields {sorted(value)}.")

    def target(self, value: dict) -> str:
        if "minimum_power" in value:
            nulls = value.get("nulls")
            fields = [
                ("at", "at", self.nested),
                ("minimum_power", "minimum", _number),
                ("maximum_typeI", "maximum_typeI", _number),
                ("nulls", "", str),
                ("rejecting", "rejecting", _string),
            ]
            arguments = self.arguments(value, fields)
            if nulls is not None:
                points = "[" + ", ".join(self.value(item) for item in _list(nulls)) + "]"
                arguments.append(("nulls", _call("null_scenarios", [("at", points)])))
            return _call("power_target", arguments)
        fields = [
            ("at", "at", self.nested),
            ("level", "level", _number),
            ("margin_of_error", "margin_of_error", _number),
            ("relative_margin_of_error", "relative_margin_of_error", _number),
            ("assurance", "assurance", _number),
        ]
        return _call("precision_target", self.arguments(value, fields))

    def planned_interval(self, value: dict) -> str:
        fields = [
            ("interval", "measure", _string),
            ("model", "model", self.nested),
            ("method", "method", _string),
            ("group", "group", _string),
        ]
        return _call("planned_interval", self.arguments(value, fields))

    def candidates(self, value: dict) -> str:
        """A space of sizes to search, written with the constructor its fields name."""
        analysis = ("analysis", "analysis", self.nested)
        keys = set(value)
        if "allocation" in keys:
            allocation = value["allocation"]
            if allocation == "equal_arms":
                fields = [
                    analysis,
                    ("allocation", "", str),
                    ("min_per_arm", "min_per_arm", _integer),
                    ("max_per_arm", "max_per_arm", _integer),
                ]
                return _call("equal_arm_sizes", self.arguments(value, fields))
            ratio = str(allocation).removeprefix("1:")
            fields = [
                analysis,
                ("allocation", "", str),
                ("min_per_arm", "min_control", _integer),
                ("max_per_arm", "max_control", _integer),
            ]
            arguments = self.arguments(value, fields)
            return _call(
                "allocated_arm_sizes", [*arguments, ("treatment_per_control", _integer(int(ratio)))]
            )
        if "step" in keys:
            fields = [
                ("analysis", "design", self.nested),
                ("min_per_arm", "min_per_arm", _integer),
                ("max_per_arm", "max_per_arm", _integer),
                ("step", "step", _integer),
                ("criterion", "criterion", _string),
            ]
            return _call("look_sizes", self.arguments(value, fields))
        if "min_clusters_per_arm" in keys:
            fields = [
                analysis,
                ("cluster_size", "cluster_size", _integer),
                ("min_clusters_per_arm", "min_per_arm", _integer),
                ("max_clusters_per_arm", "max_per_arm", _integer),
            ]
            return _call("cluster_counts", self.arguments(value, fields))
        if "min_cluster_size" in keys:
            fields = [
                analysis,
                ("min_cluster_size", "min_size", _integer),
                ("max_cluster_size", "max_size", _integer),
            ]
            return _call("cluster_sizes", self.arguments(value, fields))
        for name, low, high, ratio in (
            ("cohort_sizes", "min_exposed", "max_exposed", "unexposed_per_exposed"),
            ("case_control_sizes", "min_cases", "max_cases", "controls_per_case"),
        ):
            if low in keys:
                fields = [
                    analysis,
                    (low, low, _integer),
                    (high, high, _integer),
                    (ratio, ratio, _integer),
                ]
                return _call(name, self.arguments(value, fields))
        for name, unit in (("matched_sizes", "pairs"), ("event_counts", "events")):
            if f"min_{unit}" in keys:
                fields = [
                    analysis,
                    (f"min_{unit}", f"min_{unit}", _integer),
                    (f"max_{unit}", f"max_{unit}", _integer),
                ]
                return _call(name, self.arguments(value, fields))
        if "min_n" in keys:
            one_arm = value["analysis"].get("test") == "binomial_exact_one_sided"
            fields = [analysis, ("min_n", "min_n", _integer), ("max_n", "max_n", _integer)]
            return _call(
                "sample_sizes" if one_arm else "total_sizes", self.arguments(value, fields)
            )
        if "interval" in keys:
            fields = [
                ("interval", "interval", self.nested),
                ("min_size", "min_size", _integer),
                ("max_size", "max_size", _integer),
                # One per group is what leaving ratio out means, and all a one-size search takes.
                ("ratio", "ratio", lambda ratio: None if ratio == 1 else _integer(ratio)),
            ]
            return _call("interval_sizes", self.arguments(value, fields))
        if value.get("design") == "two_stage_threshold":
            fields = [
                ("design", "", str),
                ("null_rate", "null_rate", _number),
                ("max_total", "max_total", _integer),
                ("criterion", "criterion", _string),
            ]
            return _call("two_stage_designs", self.arguments(value, fields))
        raise Unprintable(f"No size search has fields {sorted(keys)}.")

    def reestimation(self, value: dict) -> str:
        fields = [
            ("rule", "", str),
            ("analysis", "analysis", self.nested),
            ("interim_per_arm", "interim_per_arm", _integer),
            ("difference", "difference", _number),
            ("power", "power", _number),
            ("max_per_arm", "max_per_arm", _integer),
        ]
        return _call(value["rule"], self.arguments(value, fields))

    # Claims -------------------------------------------------------------------------------

    def claim(self, claim: dict) -> str:
        kind, subject, name = claim["kind"], claim["subject"], claim["subject_name"]
        prefer = None if name == UNNAMED else name

        def part(item: object) -> str:
            # The part the claim is named after: by that name, or else written in place.
            if prefer is not None:
                name = self.reference(item, prefer)
                if name:
                    return name
            return self.value(item, inline=True)

        if kind == "typeI":
            return _call("typeI", [("analysis", part(subject))])
        if kind == "familywise":
            return _call("familywise", [("family", part(subject))])
        if kind == "meets":
            fields = [("analysis", "analysis", part), ("target", "target", self.nested)]
            return _call("meets", self.arguments(subject, fields))
        if kind == "sample_size":
            sizing = {"sufficient": "sample_size", "smallest_in_range": "smallest_sample_size"}
            fields = [
                ("candidates", "candidates", part),
                ("target", "target", self.nested),
                ("claim", "", str),
            ]
            return _call(sizing[subject["claim"]], self.arguments(subject, fields))
        if kind == "result":
            return self.result(subject, part)
        if kind == "interval":
            return self.interval(subject, part)
        raise Unprintable(f"Unknown claim kind {kind!r}.")

    def result(self, subject: dict, part: Writer) -> str:
        keys = set(subject)
        # The claim is named after the observed values, or else after the analysis.
        if "events" in keys:
            fields = [("analysis", "analysis", part), ("events", "events", part)]
            return _call("rate_result", self.arguments(subject, fields))
        if "pairs" in keys:
            fields = [("analysis", "analysis", part), ("pairs", "pairs", part)]
            return _call("matched_result", self.arguments(subject, fields))
        if "table" in keys:
            fields = [("analysis", "analysis", part), ("table", "table", part)]
            return _call("association_result", self.arguments(subject, fields))
        if "stage1_responses" in keys:
            return _call("two_stage_result", [("observation", part(subject))])
        if "responses" in keys:
            return _call("binomial_result", [("observation", part(subject))])
        return _call("result", [("observation", part(subject))])

    def interval(self, subject: dict, part: Writer) -> str:
        keys = set(subject)
        if "measure" in keys and "table" in keys:
            fields = [("measure", "", str), ("table", "table", part), ("level", "level", _number)]
            return _call(subject["measure"], self.arguments(subject, fields))
        if "measure" in keys:
            fields = [
                ("measure", "", str),
                ("model", "model", part),
                ("cases", "cases", _integer),
                ("level", "level", _number),
                ("group", "group", _string),
            ]
            return _call(subject["measure"], self.arguments(subject, fields))
        if keys == {"pairs", "level"}:
            fields = [("pairs", "pairs", part), ("level", "level", _number)]
            return _call("conditional_odds_ratio", self.arguments(subject, fields))
        if keys == {"events", "level"}:
            fields = [("events", "events", part), ("level", "level", _number)]
            return _call("rate_ratio", self.arguments(subject, fields))
        if "control_successes" in keys:
            fields = [
                ("model", "model", part),
                ("control_successes", "control_successes", _integer),
                ("treatment_successes", "treatment_successes", _integer),
                ("level", "level", _number),
            ]
            return _call("difference_interval", self.arguments(subject, fields))
        if "responses" in keys:
            fields = [
                ("model", "model", part),
                ("responses", "count", _integer),
                ("level", "level", _number),
            ]
            return _call("confidence_interval", self.arguments(subject, fields))
        raise Unprintable(f"No interval has fields {sorted(keys)}.")

    def claim_value(self, value: dict) -> str:
        return self.claim(value)

    def piece(self, value: dict) -> str:
        pieces = {"binary": "binary_outcome", "continuous": "continuous_outcome"}
        name = pieces.get(value["outcome"], "survival_outcome")
        if value["outcome"] not in (*pieces, "survival"):
            raise Unprintable(f"Unknown outcome {value['outcome']!r}.")
        fields = [
            ("outcome", "", str),
            ("better", "better", _string),
            ("measurements", "measurements", _integer),
            ("name", "name", _string),
        ]
        return _call(name, self.arguments(value, fields))

    def prior(self, value: dict) -> str:
        fields = [("distribution", "", str), ("a", "a", _integer), ("b", "b", _integer)]
        return _call("beta_prior", self.arguments(value, fields))

    def stratum(self, value: dict) -> str:
        fields = [("control", "control", _integer), ("treatment", "treatment", _integer)]
        return _call("stratum", self.arguments(value, fields))

    # Which writer a value's fields call for, in order: the first key present decides.
    SHAPES: list[tuple[str, Callable[[Any, dict], str]]] = [
        ("subject_name", claim_value),
        ("module", model),
        ("study", study),
        ("predicate", null),
        ("stopping", plan),
        ("test", analysis),
        ("analyses", combination),
        ("rule", reestimation),
        ("kind", rule),
        ("distribution", prior),
        ("outcome", piece),
        ("n_control", assignment),
        ("control", stratum),
        ("minimum_power", target),
        ("margin_of_error", target),
        ("relative_margin_of_error", target),
        ("min_per_arm", candidates),
        ("min_control", candidates),
        ("allocation", candidates),
        ("min_clusters_per_arm", candidates),
        ("min_cluster_size", candidates),
        ("min_exposed", candidates),
        ("min_cases", candidates),
        ("min_pairs", candidates),
        ("min_events", candidates),
        ("min_n", candidates),
        ("min_size", candidates),
        ("max_total", candidates),
        ("interval", planned_interval),
        ("exposed_events", observed),
        ("both_exposed", observed),
        ("exposed_cases", observed),
        ("control_successes", observed),
        ("stage1_responses", observed),
        ("responses", observed),
        ("endpoints", point),
        ("null_scenarios", point),
    ]


def _within(inner: dict, outer: dict) -> bool:
    start = (inner["line"], inner["column"])
    end = (inner["end_line"], inner["end_column"])
    return (outer["line"], outer["column"]) <= start and end <= (
        outer["end_line"],
        outer["end_column"],
    )
