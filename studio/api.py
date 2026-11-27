"""The studio's API: every request the page makes, without a transport.

studio/server.py answers these over HTTP on this machine; the web studio answers them in the
browser, where Lean is not available; scripts/build_studio_site.py writes the GET answers into
the published site. One implementation keeps all three the same.
"""

# Import the language from this checkout when running the server directly.
# ruff: noqa: E402
import dataclasses
import importlib.metadata
import itertools
import json
import sys
import tempfile
import threading
import traceback
from fractions import Fraction
from functools import cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "src"))

from statclaim.catalogue import CLAIM_TYPES, catalogue
from statclaim.contract_reports import explain
from statclaim.language import (
    LANGUAGE_VERSION,
    MODULES,
    OPERATION_BACKENDS,
    OPERATIONS,
    CalculationResultIR,
    ClaimIR,
    FieldIR,
    LocatedValue,
    ProportionZAnalysisIR,
    ValueType,
    VerificationResultIR,
    _typed,
    is_deferred,
)
from statclaim.language_compiler import compile_source
from statclaim.language_fields import SCHEMAS, fields_for, project
from statclaim.language_runner import check_source
from statclaim.language_syntax import (
    Call,
    FieldAccess,
    LanguageError,
    ListExpr,
    Literal,
    Reference,
    Source,
    Span,
    parse,
)
from statclaim.lean_report import described
from statclaim.lsp_features import Document
from statclaim.reference import PARAMETER_CHOICES
from statclaim.verification import lean_available

ASSETS = {
    "index.html",
    "editor.js",
    "document.js",
    "palette.js",
    "ui.js",
    "wizard.js",
    "designs.js",
    "backend.js",
    "worker.js",
    "python.js",
    "document.css",
    "studio.css",
}
EXAMPLES = ROOT.parent / "examples"
# Case studies and cross-checks: each folder of replication/ that holds .stat files.
REPLICATION = ROOT.parent / "replication"
# Runs build Lean proofs in the checkout; one at a time keeps lake builds from colliding.
RUN_LOCK = threading.Lock()
# The largest study a request may carry, the same for every transport.
MAX_SOURCE = 4 * 1024 * 1024
LEAN_OPERATIONS = frozenset(op for op, needs in OPERATION_BACKENDS.items() if needs == "lean")


@dataclasses.dataclass(frozen=True)
class Backend:
    """Where the studio's checks run, and whether Lean can build proofs there."""

    where: str  # "server": studio/server.py on this machine; "browser": the web studio
    project: Path | None  # the StatClaim checkout that holds the Lean project
    lean: bool

    @classmethod
    def local(cls, project: Path = ROOT.parent, lean: bool = True) -> "Backend":
        """studio/server.py in a checkout; Lean when it is installed and not turned off."""
        return cls("server", project, lean and lean_available(project))


BROWSER = Backend("browser", None, False)


def project_links() -> dict:
    """Where to go for proofs: the repository, its Codespace and how to install StatClaim."""
    try:
        urls = importlib.metadata.metadata("statclaim").get_all("Project-URL") or []
    except importlib.metadata.PackageNotFoundError:
        return {}
    named = dict(url.split(", ", 1) for url in urls if ", " in url)
    repository = named.get("Repository")
    if not repository or not repository.startswith("https://github.com/"):
        return {}
    slug = repository.removeprefix("https://github.com/").strip("/")
    owner, name = slug.split("/", 1)
    return {
        "repository": repository,
        "codespaces": f"https://codespaces.new/{slug}?quickstart=1",
        "install": repository + "#try-it",
        # The web studio, published on GitHub Pages; ?open=<link> opens a shipped study.
        "studio": f"https://{owner}.github.io/{name}/",
    }


def needs_lean(backend: Backend) -> str:
    """Why a check that builds a proof did not run here, and what to do instead."""
    if backend.where == "browser":
        return (
            "This check builds a formal proof with Lean, which the web studio cannot run. Open "
            "the study in the full studio in Codespaces, or install StatClaim with Lean."
        )
    return (
        "This check builds a formal proof with Lean, which is not installed here. Run make "
        "setup in this checkout, then restart the studio."
    )


def capabilities(backend: Backend) -> dict:
    """What this studio can do, so the page can say what needs Lean before anything runs."""
    return {
        "where": backend.where,
        "lean": backend.lean,
        "lean_operations": sorted(LEAN_OPERATIONS),
        "needs_lean": None if backend.lean else needs_lean(backend),
        "language_version": LANGUAGE_VERSION,
        "links": project_links(),
    }


def kind_key(kind):
    return kind if isinstance(kind, str) else kind.__name__


def constructor_groups():
    return {
        **{name: module.constructors for name, module in MODULES.items()},
        "": OPERATIONS.values(),
    }


@cache
def manifest():
    catalog = catalogue()
    schemas = {ValueType(kind).label: kind for kind in SCHEMAS}
    schemas.update(dict.fromkeys(CLAIM_TYPES, ClaimIR))
    groups = constructor_groups()
    results = {c.result for group in groups.values() for c in group}

    def describe(group, entries):
        output = {entry["name"]: dict(entry) for entry in entries}
        for constructor in groups[group]:
            output[constructor.name]["input_kinds"] = {
                p.name: kind_key(p.kind) for p in constructor.parameters
            }
            output[constructor.name]["accepted_results"] = {
                p.name: sorted(
                    name
                    for name in results
                    if isinstance(p.kind, type)
                    and name in schemas
                    and issubclass(schemas[name], p.kind)
                )
                for p in constructor.parameters
            }
        return output

    return {
        "version": LANGUAGE_VERSION,
        "modules": {m["name"]: describe(m["name"], m["constructors"]) for m in catalog["modules"]},
        "module_info": {
            m["name"]: {k: m[k] for k in ("classification", "support")} for m in catalog["modules"]
        },
        "operations": describe("", catalog["operations"]),
        "objects": {o["name"]: o for o in catalog["objects"]},
        "enumerations": catalog["enumerations"],
        # The registry's own wording for results, so the editor never paraphrases a grade.
        **{
            key: catalog[key]
            for key in (
                "parameter_choices",
                "program_statuses",
                "result_statuses",
                "evidence_grades",
                "scopes",
                "assumption_kinds",
            )
        },
    }


@cache
def parameter_targets():
    targets = {}
    for module, constructors in constructor_groups().items():
        for constructor in constructors:
            for parameter in constructor.parameters:
                targets.setdefault(parameter.kind, []).append(
                    (module, constructor.name, parameter.name)
                )
    return targets


def accepted_kinds(located):
    if is_deferred(located.value):
        return
    for kind in parameter_targets():
        try:
            _typed(located, kind, "input")
        except LanguageError:
            continue
        yield kind


def compatible_sockets(binding):
    accepts = {}
    located = LocatedValue(binding.value, binding.span, binding.name)
    for kind in accepted_kinds(located):
        for module, constructor, parameter in parameter_targets()[kind]:
            accepts.setdefault(module, {}).setdefault(constructor, []).append(parameter)
    return accepts


# What a value fits. The palette hints the blocks that take the selected value. Types alone
# would offer Fisher's test for a continuous study, so Python builds each block with the
# value and simple numbers, and a hint never claims more than the compiler accepts.
PROBE_SPAN = Span("<probe>", 1, 1, 1, 1)
# The value being probed has its own span, so a failure can be told apart from the fillers'.
PROBE_TARGET = Span("<probe value>", 1, 1, 1, 1)
SCALAR_KINDS = ("integer", "level", "number", "string")
PROBE_INTEGERS = {
    **dict.fromkeys(("clusters_control", "clusters_treatment"), 6),
    **dict.fromkeys(("min_per_arm", "min_n", "min_control", "n_stage1", "n_stage2"), 10),
    **dict.fromkeys(("max_per_arm", "max_n", "max_control"), 40),
    # Searches of observational designs: cases, exposed participants, pairs or events.
    **dict.fromkeys(("min_cases", "min_exposed", "min_pairs", "min_events"), 10),
    **dict.fromkeys(("max_cases", "max_exposed", "max_pairs", "max_events"), 40),
    **dict.fromkeys(("controls_per_case", "unexposed_per_exposed"), 1),
    **dict.fromkeys(("count", "control_successes", "treatment_successes"), 5),
    **dict.fromkeys(("stage1_responses", "stage2_responses"), 2),
    **dict.fromkeys(("a", "b", "continue_above", "treatment_per_control"), 1),
    "events": 50,
    "population_size": 50000,
    "draws": 100,
    "measurements": 3,
    "block_size": 4,
    "max_total": 60,
    "reject_above": 4,
}
PROBE_NUMBERS = {
    "sd": Fraction(1),
    "p_control": Fraction(3, 10),
    "p_treatment": Fraction(1, 2),
    "null_rate": Fraction(3, 10),
    "minimum": Fraction(4, 5),
    "level": Fraction(19, 20),
    # Observational planning points: probabilities in each group, a ratio, a share exposed.
    "unexposed": Fraction(1, 10),
    "exposed": Fraction(3, 10),
    "controls": Fraction(1, 5),
    "cases": Fraction(1, 3),
    "share": Fraction(1, 4),
    "odds_ratio": Fraction(2),
    "rate_ratio": Fraction(2),
    "exposed_time": Fraction(1),
    "unexposed_time": Fraction(3),
    # A cluster test's planning point also takes the intracluster correlation.
    "icc": Fraction(1, 20),
    # Survival times: a hazard ratio, the control median, accrual, follow-up and dropout.
    "hazard_ratio": Fraction(7, 10),
    "control_median": Fraction(12),
    "accrual": Fraction(24),
    "follow_up": Fraction(12),
    "dropout": Fraction(1, 10),
    "dropout_time": Fraction(12),
    # A regression slope's standard deviations, and the share the covariates explain.
    "exposure_sd": Fraction(4),
    "residual_sd": Fraction(15),
    "exposure_r2": Fraction(1, 10),
    "baseline": Fraction(1, 10),
    "design_effect": Fraction(2),
    # A precision target's margins and assurance.
    "margin_of_error": Fraction(3, 100),
    "relative_margin_of_error": Fraction(1, 2),
    "assurance": Fraction(4, 5),
}
# Lists of numbers; every other list holds values, such as a family's analyses.
PROBE_LISTS = {"weights": (Fraction(1, 2), Fraction(1, 2)), "transitions": ((0, 1), (1, 0))}
# Failures of the probe's own numbers. Two entries for one value repeat it, which is allowed
# to fail: it shows the value passed the type check of an entry.
PROBE_NUMERIC = {"domain", "never_rejects", "family_size"}


def probe_entries():
    return [(module, c) for module, group in constructor_groups().items() for c in group]


def probe_list(items, span=PROBE_SPAN, named=False):
    """A list as the compiler passes it: each entry located, and named when it is a value."""

    def entry(index, item):
        if isinstance(item, tuple):
            return probe_list(item, span)
        return LocatedValue(item, span, f"probe_{index}" if named else None)

    return LocatedValue(tuple(entry(i, item) for i, item in enumerate(items)), span)


def probe_typed(value, parameter, span=PROBE_SPAN):
    try:
        return _typed(LocatedValue(value, span), parameter.kind, parameter.name)
    except LanguageError:
        return None


def probe_options(parameter, pool):
    """What a probe may pass for an input it does not test."""
    choices = PARAMETER_CHOICES.get(parameter.name)
    if parameter.optional:
        if parameter.kind == "integer":
            # Some blocks need one of several optional sizes, such as a cohort's groups or n.
            return [None, PROBE_INTEGERS.get(parameter.name, 20)]
        if parameter.kind == "number" and parameter.name in PROBE_NUMBERS:
            # A planning point needs one of two optional inputs, such as exposed or risk_ratio.
            return [None, PROBE_NUMBERS[parameter.name]]
        return [None, *choices] if parameter.kind == "string" and choices else [None]
    if parameter.kind == "integer":
        return [PROBE_INTEGERS.get(parameter.name, 20)]
    if parameter.kind == "level":
        return [Fraction(1, 20)]
    if parameter.kind == "number":
        known = PROBE_NUMBERS.get(parameter.name)
        return [known] if known is not None else [0, Fraction(1, 2)]
    if parameter.kind == "string":
        return list(choices or ["probe"])
    if parameter.kind == "list":
        return [probe_list(PROBE_LISTS.get(parameter.name, ())).value]
    return pool


def takes_any(constructor, values):
    """Whether the block's main input, the one sample_inputs fills, takes any of the values."""
    for parameter in constructor.parameters:
        if parameter.optional or parameter.kind in SCALAR_KINDS or parameter.name in PROBE_LISTS:
            continue
        if parameter.kind == "list":
            return False
        return any(probe_typed(value, parameter) is not None for value in values)
    return False


def sample_kind(value):
    """What by_kind tells apart: the value's type, its model's type and their features."""
    item = getattr(value, "value", value)
    inner = getattr(item, "model", None)
    features = getattr(item, "features", None)
    if not isinstance(features, tuple):
        features = getattr(inner, "features", ())
    return type(item), type(inner), features if isinstance(features, tuple) else ()


def by_kind(values):
    """Values with one of each kind first, such as a design of each study model, so a capped
    probe still meets every kind: McNemar's test among many trial designs, or a cluster test
    among designs of participants."""
    firsts = {}
    for value in values:
        # Clustered or repeated designs are kinds of their own: a cluster test needs one.
        firsts.setdefault(sample_kind(value), value)
    chosen = list(firsts.values())
    return chosen + [v for v in values if all(v is not c for c in chosen)]


def probe_build(constructor, given, pool, own=frozenset(), cap=48):
    """Build with `given` and the other inputs from `pool`: the value, True if it failed only
    on the probe's numbers, or False if nothing fits. Values in `own` were built from the
    probed value, so their failures are its own."""

    def locate(parameter, value):
        if value is None:
            return LocatedValue(None, PROBE_SPAN)
        return probe_typed(value, parameter, PROBE_TARGET if id(value) in own else PROBE_SPAN)

    choices = []
    for parameter in constructor.parameters:
        if parameter.name in given:
            continue
        located = [(parameter.name, locate(parameter, v)) for v in probe_options(parameter, pool)]
        located = by_kind([option for option in located if option[1] is not None])[:8]
        if not located:
            return False
        choices.append(located)
    numeric = False
    for combination in itertools.islice(itertools.product(*choices), cap):
        fields = {**given, **dict(combination)}
        try:
            if constructor.hypothesis_contract:
                constructor.hypothesis_contract.check(constructor.name, fields)
            return constructor.build(fields, PROBE_SPAN)
        except LanguageError as error:
            code, span = error.diagnostic.code, error.diagnostic.span
            numeric = numeric or (code in PROBE_NUMERIC and span != PROBE_TARGET)
            numeric = numeric or code == "duplicate_analysis"
        except Exception:  # A probe must never break compilation.
            continue
    return numeric


def probe_inputs(value):
    """Each input of each block that could take `value`, located as the probed value."""
    for module, constructor in probe_entries():
        for parameter in constructor.parameters:
            if parameter.kind == "list" and parameter.name not in PROBE_LISTS:
                items = probe_list((value, value), PROBE_TARGET, named=True)
                yield module, constructor, parameter, items
            elif parameter.kind not in SCALAR_KINDS + ("list",):
                if (argument := probe_typed(value, parameter, PROBE_TARGET)) is not None:
                    yield module, constructor, parameter, argument


def probe_parts(value, depth=2):
    yield value
    if depth and dataclasses.is_dataclass(value):
        for field in dataclasses.fields(value):
            inner = getattr(value, field.name)
            if dataclasses.is_dataclass(inner) and not isinstance(inner, type):
                yield from probe_parts(inner, depth - 1)


def probe_neighbours(value):
    """Values one block away from `value` or its parts, needing only numbers or text besides."""
    made = []
    for part in probe_parts(value):
        for _, constructor, parameter, argument in probe_inputs(part):
            others = [p for p in constructor.parameters if not p.optional and p is not parameter]
            if parameter.kind == "list" or any(p.kind not in SCALAR_KINDS for p in others):
                continue
            built = probe_build(constructor, {parameter.name: argument}, [])
            if not isinstance(built, bool):
                made.append((constructor.name, part is value, built))
    return made


def probe_takes(value, pool, own=frozenset()):
    found = {}
    for module, constructor, parameter, argument in probe_inputs(value):
        if probe_build(constructor, {parameter.name: argument}, pool, own) is not False:
            found.setdefault((module, constructor), []).append(parameter.name)
    return found


def value_fits(value, pool=()):
    """{module: {block: {"inputs": [...], "via": block?}}}: blocks that take `value`, directly
    or through one block, such as a test that takes a study through its design."""
    if is_deferred(value) or not dataclasses.is_dataclass(value):
        return {}
    near = probe_neighbours(value)
    own = frozenset(id(built) for *_, built in near)
    pool = [built for *_, built in near] + list(pool)
    routes = {key: (0, inputs, None) for key, inputs in probe_takes(value, pool, own).items()}
    for via, direct, built in near:
        if not direct:
            continue
        for (module, constructor), inputs in probe_takes(built, pool, own).items():
            # Prefer the route into a block's first input, such as a test's design.
            main = next(
                (p.name for p in constructor.parameters if p.kind not in SCALAR_KINDS), None
            )
            rank = 1 if inputs[0] == main else 2
            key = (module, constructor)
            if module and rank < routes.get(key, (3,))[0]:
                routes[key] = (rank, inputs, via)
    fits = {}
    for (module, constructor), (_, inputs, via) in routes.items():
        entry = {"inputs": inputs, **({"via": via} if via else {})}
        fits.setdefault(module, {})[constructor.name] = entry
    return fits


def sample_inputs(constructor, pool):
    """Ways to fill a block's first input that takes other blocks, to make sample values."""
    for parameter in constructor.parameters:
        if parameter.optional or parameter.kind in SCALAR_KINDS or parameter.name in PROBE_LISTS:
            continue
        if parameter.kind == "list":
            # Two distinct values of one type, such as two analyses for a family.
            firsts, pairs = {}, {}
            for value in pool:
                first = firsts.setdefault(type(value), value)
                if first is not value:
                    pairs.setdefault(type(value), (first, value))
            for a, b in pairs.values():
                yield {parameter.name: probe_list((a, b), named=True)}
        else:
            typed = [t for v in pool if (t := probe_typed(v, parameter)) is not None]
            for argument in by_kind(typed)[:24]:
                yield {parameter.name: argument}
        return
    yield {}


@cache
def block_fits():
    """For each palette block, the blocks that take what it makes, from sample values."""
    samples, pool, kinds, fresh = {}, [], set(), []
    for _ in range(8):
        for module, constructor in probe_entries():
            if not module:
                continue
            # A block sampled in an earlier round is sampled again only when the pool has
            # gained a kind of value its main input takes, such as a clustered model for a
            # design of a cluster trial.
            if (module, constructor.name) in samples and not takes_any(constructor, fresh):
                continue
            made = []
            for given in sample_inputs(constructor, pool):
                # Inputs built from the given value, such as a null about a design's model.
                near = [b for v in given.values() for *_, b in probe_neighbours(v.value)]
                made.append(probe_build(constructor, given, near + pool))
            made = by_kind([value for value in made if not isinstance(value, bool)])[:10]
            if (module, constructor.name) in samples:
                # Keep what was sampled, and add one value of each new kind.
                known = samples[module, constructor.name]
                seen = {sample_kind(v) for v in known}
                made = known + [
                    v for v in made if sample_kind(v) not in seen and not seen.add(sample_kind(v))
                ]
            if made:
                samples[module, constructor.name] = made
        grown = [v for values in samples.values() for v in values]
        fresh = [v for v in grown if sample_kind(v) not in kinds]
        if len(grown) == len(pool) and not fresh:
            break
        pool, kinds = grown, {sample_kind(v) for v in grown}
    table = {}
    for (module, name), values in samples.items():
        merged = table.setdefault(module, {}).setdefault(name, {})
        for value in values:
            for target_module, blocks in value_fits(value, pool).items():
                for block, entry in blocks.items():
                    known = merged.setdefault(target_module, {}).get(block)
                    if known is None or ("via" in known and "via" not in entry):
                        merged[target_module][block] = entry
    # A block without a sample shares the hints of blocks that make the same type.
    for module, constructor in probe_entries():
        if module and constructor.name not in table.get(module, {}):
            alike = [
                table[m][c.name]
                for m, c in probe_entries()
                if c.result == constructor.result and c.name in table.get(m, {})
            ]
            table.setdefault(module, {})[constructor.name] = {
                k: v for hints in alike for k, v in hints.items()
            }
    return table


# A plain-English reading of each value, shown on its stack. Values without one show none.
OUTCOME_WORDS = {"binary": "yes-or-no", "continuous": "continuous", "survival": "time-to-event"}
FAMILY_WORDS = {
    "family": "Bonferroni family",
    "fixed_sequence": "Fixed-sequence family",
    "graphical": "Graphical procedure",
}


def level(alpha):
    return f"{alpha} ({float(alpha) * 100:.3g}%)"


def analysis_title(value):
    if hasattr(value, "method"):
        return value.method.title
    if isinstance(value, ProportionZAnalysisIR):
        return "Pooled score test" if value.test == "score_test" else "Unpooled Wald test"
    if type(value).__name__ == "RandomisationAnalysisIR":
        return "Randomisation test"
    alternative = getattr(value, "alternative", "two_sided")
    if alternative == "margin":
        return "Exact difference test"
    return "Fisher's exact test" if alternative == "two_sided" else "One-sided Fisher's exact test"


def fixed_by(study):
    """What an observational design fixed, in words."""
    if study.design == "person_time_cohort":
        return "events over person-time"
    if study.design == "matched_case_control":
        return f"{study.pairs} matched pairs"
    if study.design == "case_control":
        return f"{study.cases} cases and {study.controls} controls"
    if study.groups is not None:
        return f"{study.exposed} exposed and {study.unexposed} unexposed"
    return f"a total of {study.n}"


def observational_reading(value):
    kind = type(value).__name__
    if kind == "CrossSectionalStudyIR":
        text = (
            f"A cross-sectional sample of {value.n}: {value.exposure} and {value.outcome} "
            "measured at once"
        )
        if value.survey != "simple_random":
            text += f", by {value.survey} sampling"
            if value.clusters:
                text += f" of {value.clusters} clusters"
        return text
    if kind == "CohortStudyIR":
        if value.groups is None:
            return (
                f"A cohort of {value.n} followed for {value.outcome}, with {value.exposure} "
                "measured, not fixed"
            )
        return (
            f"A cohort of {value.exposed} exposed to {value.exposure} and {value.unexposed} "
            f"not, followed for {value.outcome}"
        )
    if kind == "CitedAssociationIR":
        study = value.plan.model
        adjusted = f", adjusted for {', '.join(value.covariates)}" if value.covariates else ""
        return (
            f"{value.method.title}: {study.exposure} and {study.outcome}{adjusted}, at level "
            f"{level(value.alpha)} (cited)"
        )
    if kind == "PersonTimeStudyIR":
        return (
            f"A cohort followed over person-time for {value.outcome}, with and without "
            f"{value.exposure}"
        )
    if kind == "ObservedEventsIR":
        return (
            f"Observed: {value.exposed_events} events in {value.exposed_time} exposed and "
            f"{value.unexposed_events} in {value.unexposed_time} unexposed person-time"
        )
    if kind == "RateAnalysisIR":
        study = value.plan.model
        return (
            f"Exact test of equal rates of {study.outcome} with and without {study.exposure}, "
            f"at level {level(value.alpha)}"
        )
    if kind == "MatchedStudyIR":
        return (
            f"{value.pairs} cases of {value.outcome}, each matched to one control, asked about "
            f"{value.exposure}"
        )
    if kind == "MatchedPairsIR":
        _, b, c, _ = value.cells
        return f"Observed: {b + c} discordant pairs, {b} with only the case exposed"
    if kind == "MatchedAnalysisIR":
        study = value.plan.model
        return (
            f"McNemar's exact test of association between {study.exposure} and "
            f"{study.outcome} within pairs, at level {level(value.alpha)}"
        )
    if kind == "CaseControlStudyIR":
        return (
            f"{value.cases} cases of {value.outcome} and {value.controls} controls, asked "
            f"about {value.exposure}"
        )
    if kind == "PlanIR":
        return f"A fixed sample: {fixed_by(value.model)}"
    if kind == "AssociationTableIR":
        study = value.model
        a, b, c, d = value.cells
        return f"Observed: {a} of {a + b} exposed and {c} of {c + d} unexposed had {study.outcome}"
    if kind == "AssociationNullIR":
        study = value.model
        return f"Null: no association between {study.exposure} and {study.outcome}"
    if kind == "AssociationAnalysisIR":
        study = value.plan.model
        return (
            f"Fisher's exact test of association between {study.exposure} and "
            f"{study.outcome}, at level {level(value.alpha)}"
        )
    return None


def _odds(p):
    return p / (1 - p)


def _ratio_words(first, second, noun):
    """What a point implies, such as "risk ratio 2", when it is finite."""
    return f" ({noun} ratio {short_fraction(second / first)})" if first else ""


def short_fraction(value):
    return str(value) if value.denominator <= 1000 else f"{float(value):.3g}"


def _each(value, other):
    return f", {value.ratio} {other} for each" if value.ratio != 1 else ""


def _skew_words(v) -> str:
    """Skewed data, for a simulation: the exposure's and the error's skewness."""
    parts = [
        f"{label} skewness {getattr(v, name)}"
        for name, label in (("exposure_skewness", "exposure"), ("skewness", "error"))
        if getattr(v, name, None)
    ]
    return "; " + ", ".join(parts) if parts else ""


def _design_words(v):
    """A survey's design effect, when the point gives one."""
    effect = getattr(v, "design_effect", None)
    return f"; design effect {effect}" if effect is not None else ""


# Readings of observational planning points and searches; the points are inputs, not facts.
PLANNING_READINGS = {
    "RisksIR": lambda v: (
        f"Risk of the outcome {v.exposed} with exposure and {v.unexposed} without"
        + _ratio_words(v.unexposed, v.exposed, "risk")
        + (f"; {v.exposed_share} of participants exposed" if v.exposed_share else "")
    ),
    "ExposurePrevalenceIR": lambda v: (
        f"Exposed: {v.cases} of cases and {v.controls} of controls"
        + (
            f" (odds ratio {short_fraction(_odds(v.cases) / _odds(v.controls))})"
            if 0 < v.controls < 1 and 0 < v.cases < 1
            else ""
        )
    ),
    "OutcomePrevalenceIR": lambda v: (
        f"Prevalence {v.exposed} with exposure and {v.unexposed} without"
        + _ratio_words(v.unexposed, v.exposed, "prevalence")
        + f"; {v.exposed_share} of participants exposed"
        + _design_words(v)
    ),
    "DiscordantPairsIR": lambda v: (
        f"{v.share} of pairs discordant, with a conditional odds ratio of {v.odds_ratio}"
    ),
    "IncidenceRatesIR": lambda v: (
        f"Rate ratio {v.rate_ratio}, with "
        f"{short_fraction(v.exposed_time / (v.exposed_time + v.unexposed_time))} of person-time "
        "exposed" + (f", given {v.events} events" if v.events else "")
    ),
    "GroupCandidatesIR": lambda v: (
        f"From {v.min_size} to {v.max_size} cases" + _each(v, "controls")
        if v.analysis.plan.model.design == "case_control"
        else f"From {v.min_size} to {v.max_size} exposed" + _each(v, "unexposed")
    ),
    "CountCandidatesIR": lambda v: f"From {v.min_size} to {v.max_size} {v.unit}",
    "LookCandidatesIR": lambda v: (
        f"Every choice of {len(v.design.analyses)} look sizes from {v.min_per_arm} to "
        f"{v.max_per_arm} per control arm in steps of {v.step}, ranked {v.criterion}"
    ),
    "ClusterCandidatesIR": lambda v: (
        f"From {v.low} to {v.high} clusters per arm, each of {v.cluster_size} participants"
        if v.cluster_size is not None
        else f"The declared clusters, with {v.low} to {v.high} participants in each"
    ),
    "ExponentialSurvivalIR": lambda v: (
        f"Hazard ratio {v.hazard_ratio}, control median {v.control_median}; entry over "
        f"{v.accrual}, then {v.follow_up} of follow-up"
        + (f"; {v.dropout} drop out by {v.dropout_time}" if v.dropout is not None else "")
        + (f"; the effect starts {v.effect_delay} after entry" if v.effect_delay else "")
    ),
    "CorrelationIR": lambda v: (
        f"A correlation of {v.value} between exposure and outcome" + _skew_words(v)
    ),
    "SingleProportionIR": lambda v: (
        f"A proportion of {v.value}"
        + _design_words(v)
        + (f"; a population of {v.population_size}" if v.population_size is not None else "")
    ),
    "PrecisionTargetIR": lambda v: (
        f"A {short_fraction(v.level * 100)}% interval with "
        + (
            f"a margin of error of at most {v.margin}"
            if v.margin is not None
            else f"a relative margin of error of at most {v.relative}"
        )
        + (f", with assurance {v.assurance}" if v.assurance is not None else "")
    ),
    "PlannedIntervalIR": lambda v: (
        f"The {'exact' if v.method == 'exact' else 'normal'} interval for the "
        f"{v.measure.replace('_', ' ')}" + (f" of the {v.group} group" if v.group else "")
    ),
    "IntervalCandidatesIR": lambda v: (
        f"Sizes from {v.min_size} to {v.max_size}"
        + (f", {v.ratio} of the other group for each" if v.ratio != 1 else "")
    ),
    "OutcomeMeansIR": lambda v: (
        f"Outcome mean {v.exposed} with exposure and {v.unexposed} without, SD {v.sd}"
        + (f"; {v.exposed_share} of participants exposed" if v.exposed_share is not None else "")
        + _design_words(v)
    ),
    "OddsPerSdIR": lambda v: (
        f"An odds ratio of {v.odds_ratio} per standard deviation of exposure, outcome "
        f"probability {v.baseline} at its mean"
        + (
            f"; covariates explain {v.exposure_r2} of the exposure"
            if v.exposure_r2 is not None
            else ""
        )
        + _design_words(v)
    ),
    "SlopeIR": lambda v: (
        f"A slope of {v.value} per unit of exposure, exposure SD {v.exposure_sd}, residual SD "
        f"{v.residual_sd}"
        + (
            f"; covariates explain {v.exposure_r2} of the exposure"
            if v.exposure_r2 is not None
            else ""
        )
        + _design_words(v)
        + _skew_words(v)
    ),
    "MeanDifferenceIR": lambda v: (
        f"A mean difference of {v.value}, with standard deviation {v.sd}"
        + (f" ({v.sd_treatment} in treatment)" if v.sd_treatment is not None else "")
        + (f" and intracluster correlation {v.icc}" if v.icc is not None else "")
        + (f"; cluster sizes vary with CV {v.cluster_size_cv}" if v.cluster_size_cv else "")
        + (f"; skewness {v.skewness}" if v.skewness else "")
    ),
    "TotalCandidatesIR": lambda v: f"Totals from {v.min_n} to {v.max_n} participants",
}


def reading(value, expression):
    kind = type(value).__name__
    # A planned interval and its sizes read the same for trials and observational studies.
    if kind in ("PlannedIntervalIR", "IntervalCandidatesIR"):
        return PLANNING_READINGS[kind](value)
    if getattr(value, "observational", False) or getattr(
        getattr(value, "model", None) or getattr(getattr(value, "plan", None), "model", None),
        "observational",
        False,
    ):
        return observational_reading(value)
    if kind in {"ModelIR", "OutcomeModelIR"}:
        measured = value.measured
        text = (
            f"Two arms of {value.n_control} (control) and {value.n_treatment} (treatment), "
            f"with a {OUTCOME_WORDS.get(measured.kind, measured.kind)} outcome"
        )
        if measured.name:
            text += f" named {measured.name}"
        assignment = value.assignment
        if assignment.clustered:
            text += (
                f", in {assignment.clusters_control} and {assignment.clusters_treatment} clusters"
            )
        return text + (f"; {value.better} is better" if value.better else "")
    if kind == "OneArmModelIR":
        return f"One arm of {value.n} participants"
    if kind == "TwoStageModelIR":
        return f"Two stages: {value.n_stage1} participants, then up to {value.n_stage2} in all"
    if kind == "PlanIR":
        model = value.model
        sizes = f"{model.n_control} and {model.n_treatment}"
        return f"A fixed sample of {sizes}" if value.stopping == "fixed" else f"Sampling of {sizes}"
    if hasattr(value, "statement") and hasattr(value, "predicate"):
        return f"Null: {value.statement}"
    if isinstance(value, ProportionZAnalysisIR):
        return (
            f"{analysis_title(value)} of {value.hypothesis.statement}, "
            f"with squared cutoff {value.squared_cutoff} and claimed Type I error "
            f"at most {level(value.alpha)}"
        )
    if hasattr(value, "hypothesis") and hasattr(value, "alpha"):
        statement, at = value.hypothesis.statement, level(value.alpha)
        return f"{analysis_title(value)} of {statement}, at level {at}"
    if kind == "OneSampleAnalysisIR":
        return (
            f"Exact binomial test that the response rate exceeds {value.null_rate}, "
            f"at level {level(value.alpha)}, with {value.model.n} participants"
        )
    if kind == "TwoStageAnalysisIR":
        return f"Two-stage test of a response rate above {value.null_rate}"
    if kind == "FamilyIR":
        count = len(value.analyses)
        return f"Bonferroni family of {count} analyses sharing level {level(value.alpha)}"
    if kind == "SequentialIR":
        if value.spending:
            rule = "O'Brien-Fleming" if value.spending == "obrien_fleming" else "Pocock"
            return (
                f"One test at {len(value.analyses)} looks with {rule} boundaries, which use "
                f"the correlation between looks, at level {level(value.alpha)} in all"
            )
        return (
            f"One test at {len(value.analyses)} looks, spending level {level(value.alpha)} in all"
        )
    if kind == "ReestimationIR":
        return (
            f"Student's t-test, its size re-estimated blind after {value.interim_per_arm} per arm: "
            f"{value.initial_per_arm} to {value.max_per_arm} per arm, for a difference of "
            f"{value.difference} with power {value.power}"
        )
    if kind == "EndpointPointsIR":
        count = len(value.points)
        return f"One planning point for each of {count} endpoints, correlation {value.correlation}"
    if kind == "NullScenariosIR":
        sds = ", ".join(str(point.sd) for point in value.points if hasattr(point, "sd"))
        return f"{len(value.points)} null scenarios" + (
            f", standard deviations {sds}" if sds else ""
        )
    if kind == "ComposedFamilyIR":
        words = FAMILY_WORDS.get(value.mode, value.mode.replace("_", " ").capitalize())
        return f"{words} of {len(value.analyses)} analyses at level {level(value.alpha)}"
    if kind == "ClaimIR" and type(value.subject).__name__ == "EffectIntervalIR":
        words = value.subject.measure.replace("_", " ")
        return f"The {words} with its interval at level {value.subject.level}"
    if kind == "ClaimIR" and type(value.subject).__name__ == "ProportionIR":
        words = value.subject.measure.replace("_", " ")
        return f"The {words} of {value.subject.model.outcome}, at level {value.subject.level}"
    if kind == "ClaimIR" and type(value.subject).__name__ == "RateRatioIR":
        return f"The incidence rate ratio with its interval at level {value.subject.level}"
    if kind == "ClaimIR" and type(value.subject).__name__ == "RateResultIR":
        return "The exact p-value and decision of the rate test for the observed events"
    if kind == "ClaimIR" and type(value.subject).__name__ == "MatchedIntervalIR":
        return f"The conditional odds ratio with its interval at level {value.subject.level}"
    if kind == "ClaimIR" and type(value.subject).__name__ == "MatchedResultIR":
        return "The exact p-value and decision of McNemar's test for the observed pairs"
    if kind == "ClaimIR" and type(value.subject).__name__ == "AssociationResultIR":
        return "The exact p-value and decision of Fisher's test for the observed table"
    if kind == "ClaimIR":
        return value.guarantee.sentence
    if kind == "ObservationIR":
        return (
            f"Observed {value.control_successes} control and "
            f"{value.treatment_successes} treatment successes"
        )
    if kind == "OneSampleObservationIR":
        return f"Observed {value.responses} responses"
    if kind == "RatesIR":
        return (
            f"Success rates of {value.p_control} (control) and {value.p_treatment} (treatment)"
            + (f", intracluster correlation {value.icc}" if value.icc is not None else "")
            + (
                f"; cluster sizes vary with CV {value.cluster_size_cv}"
                if value.cluster_size_cv
                else ""
            )
        )
    if kind == "PowerTargetIR":
        return (
            f"Power of at least {value.minimum} at that point, "
            f"with Type I error at most {value.maximum_typeI}"
        )
    if kind == "CandidatesIR":
        return f"Arm sizes from {value.min_per_arm} to {value.max_per_arm} per arm"
    if kind in PLANNING_READINGS:
        return PLANNING_READINGS[kind](value)
    if kind == "ClaimIR" and value.kind in ("meets", "sample_size"):
        target = value.subject.target
        if type(target).__name__ == "PrecisionTargetIR":
            if value.kind == "meets":
                return f"Whether {value.name} reaches the precision target"
            smallest = "smallest" if value.subject.minimal else "a sufficient"
            return f"The {smallest} size in the range that reaches the precision target"
        if value.kind == "meets":
            return (
                f"Whether {value.name} has power of at least {target.minimum} at the planning point"
            )
        smallest = "smallest" if value.subject.minimal else "a sufficient"
        return f"The {smallest} size in the range with power of at least {target.minimum}"
    if kind in {"VerificationResultIR", "CalculationResultIR"} and isinstance(expression, Call):
        verb = {"verify": "Checks", "simulate": "Simulates"}.get(expression.name, "Calculates")
        subject = expression.arguments[0].value if expression.arguments else None
        return f"{verb} {spoken(subject)}" if subject is not None else verb
    if kind == "FieldIR" and isinstance(expression, FieldAccess):
        return f"The {expression.name.replace('_', ' ')} of {spoken(expression.subject)}"
    return None


CLAIM_WORDS = {
    "typeI": "the Type I error bound of",
    "familywise": "the familywise error bound of",
    "power": "the power of",
    "meets": "whether the power target is met by",
}


def spoken(node):
    """Reads an expression aloud: a name, a field path, or a claim about a name."""
    if isinstance(node, Reference):
        return node.name
    if isinstance(node, FieldAccess):
        return f"{spoken(node.subject)}.{node.name}"
    if isinstance(node, Call):
        inner = spoken(node.arguments[0].value) if node.arguments else ""
        words = CLAIM_WORDS.get(node.name, node.name.replace("_", " ") + " of")
        return f"{words} {inner}".strip()
    return "a value"


def compile_document(source):
    result = compile_source(source)
    statements, _ = parse(source)
    expressions = {getattr(s, "name", None): getattr(s, "expression", None) for s in statements}
    bindings = {}
    for binding in result.program.bindings:
        value = binding.value
        optional = isinstance(value, FieldIR) and value.value_type.optional
        kind = "list" if isinstance(value, tuple) else type(value)
        field_inputs = {}
        for field in fields_for(value):
            try:
                projected = project(value, field, binding.span, result.program.requests)
            except LanguageError:
                continue
            field_inputs[field] = [
                kind_key(k)
                for k in accepted_kinds(LocatedValue(projected, binding.span, binding.name))
            ]
        bindings[binding.name] = {
            "type": value.value_type.label if isinstance(value, FieldIR) else ValueType(kind).label,
            "fields": {
                name: ValueType(spec.kind, spec.optional or optional).label
                for name, spec in fields_for(value).items()
            },
            "accepts": compatible_sockets(binding),
            "field_inputs": field_inputs,
        }
        try:
            text = reading(value, expressions.get(binding.name))
        except (AttributeError, TypeError, ValueError):
            text = None
        if text:
            bindings[binding.name]["reading"] = text
    return {
        "status": result.status,
        "diagnostics": [d.to_dict() for d in result.diagnostics],
        "bindings": bindings,
    }


def fits_document(source, name):
    """The blocks that take one declaration's value, for the palette's hints."""
    compilation = compile_source(source)
    if compilation.program is None:
        return {"fits": {}}
    bindings = compilation.program.bindings
    pool = [b.value for b in bindings]
    found = next((b for b in bindings if b.name == name), None)
    return {"fits": value_fits(found.value, pool) if found else {}}


def explain_document(source, name=None):
    """Why each contract passed: the checked derivation of one declaration, or of all of them."""
    compilation = compile_source(source)
    if compilation.program is None:
        return {"entries": []}
    return {"entries": explain(compilation, name or None)}


def tutorial(path, name=None):
    return parse_document(Source(path.read_text(encoding="utf-8"), name or path.name))


def parse_document(source):
    text = source.text
    statements, diagnostics = parse(source)

    def extent(span):
        return {
            "start": source.line_starts[span.line - 1] + span.column - 1,
            "end": source.line_starts[span.end_line - 1] + span.end_column - 1,
        }

    def expression(node):
        return {**extent(node.span), "kind": type(node).__name__, **payload(node)}

    def payload(node):
        if isinstance(node, Literal):
            positions = extent(node.span)
            return {"literal": text[positions["start"] : positions["end"]]}
        if isinstance(node, Reference):
            return {"label": node.name}
        if isinstance(node, FieldAccess):
            return {"label": "." + node.name, "children": [expression(node.subject)]}
        if isinstance(node, ListExpr):
            return {"label": "List", "children": [expression(item) for item in node.items]}
        if isinstance(node, Call):
            return {
                "label": node.name,
                "children": [
                    {
                        **expression(arg.value),
                        "argument": arg.name,
                        "argument_span": extent(arg.span),
                    }
                    for arg in node.arguments
                ],
            }
        raise TypeError(type(node))

    return {
        "name": source.path,
        "uses": [{**extent(s.span), "name": s.name} for s in statements if s.kind == "use"],
        "source": text,
        "imports": [s.name for s in statements if s.kind == "use"],
        "statements": [
            {
                **extent(statement.span),
                "kind": statement.kind,
                "name": statement.name,
                "expression": expression(statement.expression),
            }
            for statement in statements
            if statement.expression is not None
        ],
        "parse_errors": [d.to_dict() for d in diagnostics],
    }


def holders(studio):
    """The `let` that holds a check at a span, so the page can show it as on the canvas."""
    statements, _ = parse(studio)

    def holder(span):
        here = (span["line"], span["column"])
        for statement in statements:
            s = statement.span
            if (s.line, s.column) <= here <= (s.end_line, s.end_column):
                return statement.name
        return None

    return holder


def reads_result(value):
    """Whether a value reads a field of a check's result, so only a run can know it.

    The checks themselves are left out; the tray under each one shows its result."""
    if not isinstance(value, FieldIR):
        return False
    while isinstance(value, FieldIR):
        value = value.subject
    return isinstance(value, (VerificationResultIR, CalculationResultIR))


def run_document(source, backend, only=None):
    """Run every check in the study, as `statclaim check` does, and keep what the editor shows.

    With only="calculate", or where Lean is not available, only the operations that need no
    Lean run, in a scratch folder that is removed afterwards: the studio recalculates this way
    after a number is dragged, so values follow the edit. Where Lean is not available, each
    check that needs it is reported as "needs_lean", with what to do instead."""
    # A path that cannot exist on disk, so the runner never compares against a real file.
    studio = Source(source.text, "<studio>/" + Path(source.path).name)
    operations = None
    if only or not backend.lean:
        operations = set(OPERATIONS) - LEAN_OPERATIONS
    with RUN_LOCK:
        if operations is not None:
            with tempfile.TemporaryDirectory() as scratch:
                report = check_source(
                    studio,
                    project=backend.project or Path(scratch),
                    output=Path(scratch) / "run",
                    timeout=300,
                    operations=operations,
                )
            report.pop("run_directory", None)
            for request in report["requests"]:
                (request["report"].get("certificate") or {}).pop("directory", None)
        else:
            report = check_source(studio, project=backend.project, timeout=300)
    holder = holders(studio)
    requests = []
    for request in report["requests"]:
        details = request["report"]
        value = request["value"]
        status = value.get("status") or request["status"]
        message = (details.get("verification") or {}).get("message")
        if (
            status == "not_executed"
            and request["operation"] in LEAN_OPERATIONS
            and not backend.lean
        ):
            status, message = "needs_lean", needs_lean(backend)
        requests.append(
            {
                **{k: request.get(k) for k in ("request_id", "operation", "claim", "subject")},
                "name": holder(request["source"]),
                "source": request["source"],
                "status": status,
                "weakest_link": request.get("weakest_link"),
                "evidence": value.get("evidence"),
                **(
                    {"counterexample": value["counterexample"]} if "counterexample" in value else {}
                ),
                "target": details.get("target_property"),
                "established": details.get("established_properties") or [],
                "assumptions": details.get("required_assumptions") or [],
                "references": details.get("references") or [],
                "certificate": (details.get("certificate") or {}).get("directory"),
                "calculation": details.get("calculation"),
                "decision": details.get("decision"),
                "message": message,
            }
        )
    # Values a run fills in: fields read from a check's result, e.g. recommendation.calculation.n.
    values = report.get("values") or {}
    program = compile_source(studio).program
    realized = {
        binding.name: values[binding.name]
        for binding in program.bindings
        if binding.name in values and reads_result(binding.value)
    }
    # A proof that could not be built leaves its claim open, as `statclaim check` reports it
    # without Lean; the page says which checks need Lean.
    unproved = any(request["status"] == "needs_lean" for request in requests)
    return {
        "status": "unresolved_obligation" if unproved else report["status"],
        "requests": requests,
        "values": realized,
        "diagnostics": report["diagnostics"],
        "run_directory": report.get("run_directory"),
        "certificate_issued": report["certificate_issued"],
        "lean": whole_study(report.get("lean"), program, holder),
    }


def whole_study(lean, program, holder):
    """What the run's one Lean build of the study shows, as `statclaim report --lean` says
    it, with each claim named by its block; why Lean checked nothing when the build failed;
    None when the run built nothing in Lean."""
    if not lean:
        return None
    if lean["status"] == "failed":
        return {"status": "failed", "stage": lean["stage"], "error": lean["error"]}
    bundle = Path(lean["certificate_directory"])
    issued = json.loads((bundle / "certificate.json").read_text())
    shown = described(issued, bundle, program)
    for claim in shown["claims"]:
        claim["name"] = holder(claim["source"])
    return shown


def language_feature(kind, source, line, character):
    """Completion or hover from the language server's backend-free features."""
    document = Document(source.path, 1, source.text)
    position = {"line": line, "character": character}
    if kind == "complete":
        items = document.completion(position)["items"]
        return {
            "items": [
                {
                    "label": item["label"],
                    "detail": item.get("detail"),
                    "documentation": (item.get("documentation") or {}).get("value")
                    if isinstance(item.get("documentation"), dict)
                    else item.get("documentation"),
                    "text": item["textEdit"]["newText"],
                    "range": item["textEdit"]["range"],
                }
                for item in items[:60]
            ]
        }
    hover = document.hover(position)
    return {"markdown": hover["contents"]["value"] if hover else None}


GETS = {
    "tutorials": lambda backend: [
        tutorial(path) for path in sorted((EXAMPLES / "tutorial").glob("*.stat"))
    ],
    "examples": lambda backend: [tutorial(path) for path in sorted(EXAMPLES.glob("*.stat"))],
    # The programs the StatClaim article shows, and the studies in replication/.
    "paper": lambda backend: [
        tutorial(path) for path in sorted((EXAMPLES / "paper").glob("*.stat"))
    ],
    "replication": lambda backend: [
        tutorial(path, f"{path.parent.name}/{path.name}")
        for path in sorted(REPLICATION.glob("*/*.stat"))
    ],
    "blocks": lambda backend: manifest(),
    "block-fits": lambda backend: block_fits(),
    "capabilities": capabilities,
}
POSTS = {"parse", "compile", "run", "explain", "fits", "complete", "hover"}


def handle(method: str, path: str, payload: object, backend: Backend) -> tuple[int, object]:
    """Answer one request from the page: a status code and a JSON-ready body.

    `path` is the endpoint's name, such as "compile". Every transport calls this, so a request
    is checked and answered the same way on this machine and in the web studio."""
    if method == "GET":
        if path not in GETS:
            return 404, {"error": f"There is no {path!r} here."}
        return 200, GETS[path](backend)
    if path not in POSTS:
        return 404, {"error": f"There is no {path!r} here."}
    try:
        if not isinstance(payload, dict):
            raise ValueError
        source = Source(payload["source"], payload.get("name", "<input>"))
        if not isinstance(source.text, str) or not isinstance(source.path, str):
            raise ValueError
        position = (int(payload.get("line", 0)), int(payload.get("character", 0)))
    except (ValueError, KeyError, TypeError):
        return 400, {"error": "Expected a JSON object containing source text."}
    if len(source.text.encode("utf-8")) > MAX_SOURCE:
        return 413, {"error": "Document exceeds the 4 MiB request limit."}
    only = payload.get("only")
    if path == "run" and only not in (None, "calculate"):
        return 400, {"error": "Only calculations can run on their own."}
    try:
        if path == "parse":
            return 200, parse_document(source)
        if path == "compile":
            return 200, compile_document(source)
        if path == "run":
            return 200, run_document(source, backend, only=only)
        if path == "explain":
            return 200, explain_document(source, payload.get("declaration"))
        if path == "fits":
            return 200, fits_document(source, payload.get("declaration"))
        return 200, language_feature(path, source, *position)
    except Exception:
        traceback.print_exc(file=sys.stderr)
        failure = "The run" if path == "run" else "Compilation"
        return 500, {"error": failure + " failed internally."}


def handle_json(method: str, path: str, body: str, backend: Backend) -> tuple[int, str]:
    """handle(...) with the body as JSON text, for transports that pass strings."""
    try:
        payload = json.loads(body) if body else None
    except ValueError:
        return 400, json.dumps({"error": "Expected a JSON object containing source text."})
    status, result = handle(method, path, payload, backend)
    return status, json.dumps(result)
