"""What a compiled program states in Lean. Trusted: see the trusted base in
docs/proposals/lean-translation.md.

Every statement of a translated file is decided here: the program's abstract parts
(fields of `Instance`), its definitions, the contract facts the Python compiler checks,
the premises the claims rest on, and the claims. How each is proved is left to
`prove.py`, which this module never consults: a wrong proof fails the build, while a
wrong statement here could let a proof of the wrong thing pass.

Abstract parts are the laws of outcomes Lean does not fix, and the rejection event and
slack of each cited or declared test. Premise names start with their kind, `cited_` or
`declared_`, which the grade rule in `grades.py` reads.
"""

import json
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

from statclaim.language import (
    AnalysisIR,
    AssociationAnalysisIR,
    AssociationNullIR,
    CitedAnalysisIR,
    CitedAssociationIR,
    ClaimIR,
    ComposedFamilyIR,
    FamilyIR,
    HypothesisIR,
    ModelIR,
    ObservationalStudyIR,
    OutcomeNullIR,
    PlanIR,
    ProgramIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
    SequentialIR,
    VerificationResultIR,
    normalize,
)
from statclaim.language.ir import TwoArmModelIR
from statclaim.language_compiler import requirements
from statclaim.lean_translation import exact
from statclaim.lean_translation.emit import Namer, comment, rational, real
from statclaim.lean_translation.emit import name as lean
from statclaim.lean_translation.exact import ExactAnalysis
from statclaim.methods import METHODS

CORE = "StatClaim.Core"
INTERFACE = "StatClaim.Interface"
GENERATED = "StatClaim.Generated"
BINOMIAL = "StatClaim.Modules.TwoArmBinomial"
FISHER = "StatClaim.Modules.Fisher"
SCOPES = {"finite_sample": "finiteSample", "asymptotic": "largeSample"}
BINOMIAL_NULLS = {
    "equal_proportions": f"{BINOMIAL}.equalProportions",
    "proportion_difference": f"{BINOMIAL}.proportionDifference",
    "proportion_difference_at_most": f"{BINOMIAL}.proportionDifferenceAtMost",
}
# Names the file itself uses; a binding with one of these names is renamed. Bound
# variables in statements use letters a .stat name cannot contain, such as Θ and v₀.
STRUCTURAL = frozenset(
    {
        "Instance",
        "Premises",
        "Claims",
        "witness",
        "program",
        "i",
        "premises",
        "parameter",
        "StatClaim",
        "MeasurableSpace",
    }
)
# Values that are not study objects of their own: results, fields read from them, and
# the parts of a model, which are stated with the model that uses them.
IGNORED = {
    "VerificationResultIR",
    "CalculationResultIR",
    "FieldIR",
    "AssignmentIR",
    "OutcomeIR",
    "StratumIR",
}


class Untranslated(Exception):
    """A value, or a claim about it, that the translator does not handle yet."""


def subscript(number: int) -> str:
    return str(number).translate(str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉"))


def key(value: object) -> str:
    return json.dumps(normalize(value), sort_keys=True)


def view(index: int) -> str:
    return f"v{subscript(index)}"


def vector(items: list[str], separator: str = ", ") -> str:
    return f"![{separator.join(items)}]"


def graph_events(combination: "Combination") -> str:
    """The events on which a graph rejects its members, in the claim's joint study."""
    assert combination.graph is not None
    views = " ".join(view(part.view) for part in combination.parts)
    return f"(i.{lean(combination.graph.procedure)} Θ Ω σ {views})"


def combination_claim(combination: "Combination") -> str:
    """What a combination claims about the joint study σ."""
    nulls = vector([part_null(part) for part in combination.parts], ",\n        ")
    if combination.rule == "graph":
        assert combination.graph is not None
        return (
            f"{INTERFACE}.familywiseClaim σ.law\n        {nulls}\n        "
            f"{graph_events(combination)}\n        "
            f"({real(combination.alpha)} + i.{lean(combination.graph.slack)})"
        )
    events = vector([part_event(part) for part in combination.parts], ",\n        ")
    slacks = vector([part_slack(part) for part in combination.parts])
    claimed = "sequenceClaim" if combination.rule == "sequence" else "familywiseClaim"
    return (
        f"{INTERFACE}.{claimed} σ.law\n        {nulls}\n        {events}\n        "
        f"({real(combination.alpha)} + ∑ k, {slacks} k)"
    )


def part_null(part: "Part") -> str:
    """A member's null at the joint parameter θ. A design with looks is under its null
    when every look is; a family in a sequence when any of its members is."""
    if part.leaf is not None:
        return f"fun θ => {part.leaf.null_ref()} ({view(part.view)}.parameter θ)"
    assert part.combination is not None
    nulls = vector([part_null(inner) for inner in part.combination.parts])
    quantifier = "∀" if part.kind == "looks" else "∃"
    return f"fun θ => {quantifier} k, {nulls} k θ"


def part_event(part: "Part") -> str:
    """A member's rejection, on the joint outcome. A design with looks rejects when any
    look rejects; a family in a sequence passes only when every member rejects."""
    if part.leaf is not None:
        return f"{view(part.view)}.outcome ⁻¹' {part.leaf.reject()}"
    combination = part.combination
    assert combination is not None
    if combination.rule == "graph":
        events = graph_events(combination)
    else:
        events = vector([part_event(inner) for inner in combination.parts])
    operation = "⋃" if part.kind == "looks" else "⋂"
    return f"({operation} k, {events} k)"


def part_slack(part: "Part") -> str:
    if part.leaf is not None:
        return part.leaf.slack_ref()
    combination = part.combination
    assert combination is not None
    if combination.graph is not None:
        return f"i.{lean(combination.graph.slack)}"
    return f"(∑ k, {vector([part_slack(inner) for inner in combination.parts])} k)"


@dataclass
class Model:
    name: str
    abstract: bool
    kind: str  # an outcome kind for two-arm models, a design for observational studies
    parameter: str  # the Lean type of parameters, as a field name when abstract
    outcome: str
    sizes: str = ""  # the FixedSampleDesign of a binomial model

    def ref(self) -> str:
        return f"i.{lean(self.name)}" if self.abstract else lean(self.name)

    def core(self) -> str:
        return f"{self.ref()}.toModel" if self.abstract else self.ref()

    def law(self) -> str:
        return f"{self.ref()}.law"

    def parameter_type(self) -> str:
        return f"i.{self.parameter}" if self.abstract else self.parameter

    def outcome_type(self) -> str:
        return f"i.{self.outcome}" if self.abstract else self.outcome


@dataclass
class Value:
    """A program definition, which takes the instance when it depends on abstract parts."""

    name: str
    abstract: bool

    def ref(self) -> str:
        return f"({lean(self.name)} i)" if self.abstract else lean(self.name)


@dataclass
class Design(Value):
    model: Model
    compatible: Value | None  # absent when the plan supplies no sampling law


@dataclass
class Null(Value):
    model: Model


@dataclass
class Analysis:
    name: str
    kind: str  # cited, declared or fisher
    model: Model
    design: Design
    null: Null
    alpha: Fraction
    scope: str
    test: str = ""  # the instance field holding a test seen from outside
    slack: str = ""
    premise: str = ""
    level: str = ""  # the SignificanceLevel of an exact test

    def null_ref(self) -> str:
        """The null its guarantee is about: Fisher's own, which the declared null agrees with."""
        return f"{lean(self.name)}.hypothesis" if self.kind == "fisher" else self.null.ref()

    def reject(self) -> str:
        if self.kind == "fisher":
            return f"{lean(self.name)}.procedure.rejectionEvent"
        return f"i.{lean(self.test)}.reject"

    def slack_ref(self) -> str:
        return "0" if self.kind == "fisher" else f"i.{lean(self.slack)}"


@dataclass
class Abstract:
    """An abstract part of the instance, which the witness gives a value."""

    name: str
    kind: str  # model, test, slack or procedure
    structure: str = ""
    parameter: str = ""
    outcome: str = ""
    arity: int = 0  # a procedure's explicit arguments


@dataclass
class Contract:
    name: str
    facts: list[str]
    check: str  # decide, norm_num, fisher_null, fisher_requires, same_null, splits,
    # grouped_splits or comment
    unfold: str = ""  # a definition norm_num may unfold
    predicate: str = ""  # fisher_null: the declared binomial null
    compatible: str = ""  # fisher_requires: the compatibility that meets the requirement


@dataclass
class Premise:
    name: str
    statement: str
    level: Fraction
    kind: str = "level"  # level, or graph: a graphical procedure's guarantee
    members: int = 0  # a graph's members


@dataclass
class Graph:
    """A graphical procedure: an abstract function giving, for any joint study, the events
    on which the declared graph rejects each member, with a cited premise about it."""

    name: str
    procedure: str  # the instance field holding the procedure
    slack: str
    premise: str
    scope: str


@dataclass
class Part:
    """A member of a combination, as the combination's statement reads it."""

    kind: str  # leaf, looks, family, sequence or graph
    level: Fraction
    leaf: Analysis | None = None
    view: int = -1  # a leaf's view among the claim's leaves
    combination: "Combination | None" = None


@dataclass
class Combination:
    rule: str  # union (a family, or a design with looks), sequence or graph
    alpha: Fraction
    parts: list[Part]
    graph: Graph | None = None


@dataclass
class Claim:
    name: str
    statement: str
    kind: str  # typeI or familywise
    request_id: int
    grade: str  # the grade the translator expects Lean's dependencies to give
    own: str | None = None  # the claim's own premise: a single cited or declared test, or a graph
    analysis: "Analysis | ExactAnalysis | None" = None
    combination: Combination | None = None
    leaves: list[Analysis] = field(default_factory=list)
    space: str = ""  # a namespace of its own, for the checks an exact test's proof uses


@dataclass
class Denotation:
    fields: list[str] = field(default_factory=list)
    instances: list[str] = field(default_factory=list)
    abstracts: list[Abstract] = field(default_factory=list)
    defs: list[str] = field(default_factory=list)
    contracts: list[Contract] = field(default_factory=list)
    premises: list[Premise] = field(default_factory=list)
    claims: list[Claim] = field(default_factory=list)
    skipped: dict[str, str] = field(default_factory=dict)


class Denoter:
    def __init__(self, program: ProgramIR):
        self.program = program
        self.namer = Namer([*STRUCTURAL, *(b.name for b in program.bindings)])
        self.memo: dict[str, object] = {}
        self.out = Denotation()

    def own(self, preferred: str | None, kind: str) -> str:
        """A binding's own name, unless the file needs it; otherwise a fresh one."""
        if preferred is None or preferred in STRUCTURAL:
            return self.namer.fresh(preferred or kind)
        return preferred

    # Values -----------------------------------------------------------------------------
    def abstract(self, base: str, structure: str, kind: str) -> Model:
        """A model whose law Lean does not fix: fields of the instance."""
        parameter = self.namer.fresh(f"{base}_Parameter")
        outcome = self.namer.fresh(f"{base}_Outcome")
        space = self.namer.fresh(f"{base}_space")
        self.out.fields += [
            f"{lean(parameter)} : Type",
            f"{lean(outcome)} : Type",
            f"[{lean(space)} : MeasurableSpace {lean(outcome)}]",
            f"{lean(base)} : {INTERFACE}.{structure} {lean(parameter)} {lean(outcome)}",
        ]
        self.out.instances.append(f"attribute [instance] Instance.{lean(space)}")
        self.out.abstracts.append(
            Abstract(base, "model", structure, lean(parameter), lean(outcome))
        )
        return Model(base, True, kind, lean(parameter), lean(outcome))

    def model(self, ir: object, preferred: str | None = None) -> Model:
        if not isinstance(ir, (TwoArmModelIR, ObservationalStudyIR)):
            raise Untranslated(f"{type(ir).__name__} models are not translated yet.")
        k = key(ir)
        if k in self.memo:
            return self.memo[k]  # type: ignore[return-value]
        if isinstance(ir, ObservationalStudyIR):
            # Cited tests of association need no law; exact ones come with milestone 5.
            result = self.abstract(self.own(preferred, "study"), "ObservationalModel", ir.design)
        else:
            assignment, measured = ir.assignment, ir.measured
            # A binomial law needs independent participants measured once; otherwise the
            # law is left abstract, as for continuous and survival outcomes.
            concrete = (
                isinstance(ir, ModelIR) and not assignment.clustered and measured.measurements == 1
            )
            base = self.own(preferred, "model")
            if concrete:
                sizes = self.namer.fresh(f"{base}_sizes")
                self.out.defs.append(
                    f"def {lean(sizes)} : StatClaim.FixedSampleDesign :=\n"
                    f"  ⟨{ir.n_control}, {ir.n_treatment}, by decide, by decide⟩"
                )
                self.out.defs.append(
                    f"noncomputable def {lean(base)} := {BINOMIAL}.model {lean(sizes)}"
                )
                result = Model(
                    base, False, "binary", f"{BINOMIAL}.Parameters", f"{BINOMIAL}.Counts", sizes
                )
            else:
                result = self.abstract(base, "TwoArmModel", measured.kind)
        self.memo[k] = result
        return result

    def design(self, ir: object, preferred: str | None = None) -> Design:
        if not isinstance(ir, PlanIR):
            raise Untranslated(f"{type(ir).__name__} designs are not translated yet.")
        k = key(ir)
        if k in self.memo:
            return self.memo[k]  # type: ignore[return-value]
        model = self.model(ir.model)
        base = self.own(preferred, "design")
        arguments = "(i : Instance) " if model.abstract else ""
        design = Value(base, model.abstract)
        if ir.stopping == "fixed":
            self.out.defs.append(
                f"noncomputable def {lean(base)} {arguments}:=\n"
                f"  {CORE}.StudyDesign.fixed {model.core()}"
            )
            compatible: Value | None = Value(self.namer.fresh(f"{base}_compatible"), model.abstract)
            assert compatible is not None
            self.out.defs.append(
                f"noncomputable def {lean(compatible.name)} {arguments}:\n"
                f"    {CORE}.Compatibility {design.ref()} :=\n"
                f"  {CORE}.Compatibility.fixed _"
            )
        else:
            # Data-dependent stopping without a stated rule supplies no sampling law, so no
            # Type I claim about it can be stated (Core.no_compatibility_without_law).
            self.out.defs.append(
                f"noncomputable def {lean(base)} {arguments}:=\n"
                f"  {CORE}.StudyDesign.unresolvedAdaptive {model.core()}"
            )
            compatible = None
        result = Design(base, model.abstract, model, compatible)
        self.memo[k] = result
        return result

    def null(self, ir: object, preferred: str | None = None) -> Null:
        k = key(ir)
        if k in self.memo:
            return self.memo[k]  # type: ignore[return-value]
        if not isinstance(ir, (OutcomeNullIR, HypothesisIR, AssociationNullIR)):
            raise Untranslated(f"{type(ir).__name__} nulls are not translated yet.")
        model = self.model(ir.model)
        base = self.own(preferred, "null")
        if isinstance(ir, AssociationNullIR):
            self.out.defs.append(
                f"def {lean(base)} (i : Instance) :=\n  {model.ref()}.noAssociation"
            )
        elif model.abstract:
            shape = f"{GENERATED}.NullKey.{ir.predicate}.shape"
            self.out.defs.append(
                f"def {lean(base)} (i : Instance) :=\n"
                f"  {model.ref()}.null {shape} {rational(ir.value)}"
            )
        else:
            term = BINOMIAL_NULLS[ir.predicate]
            if ir.predicate != "equal_proportions":
                term += f" {rational(ir.value)}"
            self.out.defs.append(
                f"def {lean(base)} : {CORE}.Hypothesis {model.parameter} :=\n  {term}"
            )
        result = Null(base, model.abstract, model)
        self.memo[k] = result
        return result

    def analysis(self, ir: object, preferred: str | None = None) -> "Analysis | ExactAnalysis":
        # One declaration, one test: two identical declarations are two endpoints, as
        # Python's combinations count them, so tests are told apart by declaration.
        k = f"analysis:{id(ir)}"
        if k in self.memo:
            return self.memo[k]  # type: ignore[return-value]
        result: Analysis | ExactAnalysis
        if isinstance(ir, CitedAnalysisIR):
            result = self.cited(ir, preferred)
        elif isinstance(ir, CitedAssociationIR):
            result = self.cited_association(ir, preferred)
        elif isinstance(ir, AnalysisIR) and ir.alternative == "two_sided":
            result = self.fisher(ir, preferred)
        else:
            result = self.exact(ir, preferred)
        self.memo[k] = result
        return result

    def exact(self, ir: object, preferred: str | None) -> ExactAnalysis:
        """An exact test and its Type I claim. See `exact.py`."""
        if not exact.is_exact(ir):
            raise Untranslated(f"{type(ir).__name__} analyses are not translated yet.")
        if exact.stopping(ir) != "fixed":
            raise Untranslated(
                "An exact test's guarantee is for a fixed design; this design stops on the data."
            )
        base = self.own(preferred, "analysis")
        test: Any = (
            ir.margin_test(observed=None)
            if isinstance(ir, AnalysisIR) and (ir.alternative == "margin")
            else ir.lower()  # type: ignore[attr-defined]
        )
        level = self.namer.fresh(f"{base}_level")
        self.out.defs.append(
            f"def {lean(level)} : StatClaim.SignificanceLevel :=\n  {exact.level(test.alpha)}"
        )
        names: dict[str, str] = {}
        bound = exact.bound(lean(level))
        modules = exact.MODULES
        if isinstance(ir, AnalysisIR):
            kind = "one_sided" if ir.alternative == "greater" else "margin"
            design = self.design(ir.plan)
            if design.model.abstract:
                raise Untranslated(
                    "This exact test needs the binomial model of independent participants."
                )
            null = self.null(ir.hypothesis)
            sizes = lean(design.model.sizes)
            names["sizes"] = sizes
            if kind == "one_sided":
                term = f"{modules}.FisherOneSided.analysis {sizes} {lean(level)}"
            else:
                thresholds = self.namer.fresh(f"{base}_thresholds")
                names["thresholds"] = lean(thresholds)
                listed = ", ".join(str(t) for t in test.thresholds)
                # The test itself: with x control successes, reject at the x-th threshold.
                self.out.defs.append(f"def {lean(thresholds)} : List ℕ := [{listed}]")
                term = (
                    f"{modules}.DifferenceTest.analysis {sizes} {lean(thresholds)} "
                    f"{rational(test.margin)}"
                )
            self.out.defs.append(f"noncomputable def {lean(base)} :=\n  {term}")
            self.out.contracts.append(
                Contract(
                    self.namer.fresh(f"{base}_null"),
                    [f"∀ parameter, {null.ref()} parameter ↔ {lean(base)}.hypothesis parameter"],
                    "same_null",
                )
            )
            statement = f"({lean(base)}.typeIClaim {bound}).statement"
        elif isinstance(ir, AssociationAnalysisIR) and test.groups is not None:
            kind = "groups"
            first, second = test.groups
            for suffix in ("groups", "study", "design", "compatible"):
                names[suffix] = lean(self.namer.fresh(f"{base}_{suffix}"))
            self.out.defs += [
                "-- Fixed groups make the table two independent binomial counts, and no\n"
                "-- association makes their probabilities equal: the model of Fisher's test\n"
                "-- (StatClaim.Modules.Association).\n"
                f"def {names['groups']} : StatClaim.FixedSampleDesign :=\n"
                f"  ⟨{first}, {second}, by decide, by decide⟩",
                f"noncomputable def {names['study']} := {BINOMIAL}.model {names['groups']}",
                f"noncomputable def {names['design']} :=\n"
                f"  {CORE}.StudyDesign.fixed {names['study']}",
                f"noncomputable def {names['compatible']} :\n"
                f"    {CORE}.Compatibility {names['design']} :=\n"
                f"  {CORE}.Compatibility.fixed _",
                f"noncomputable def {lean(base)} :=\n"
                f"  {FISHER}.analysis {names['groups']} {names['design']} {lean(level)}",
            ]
            statement = f"({lean(base)}.typeIClaim {names['compatible']} {bound}).statement"
        elif isinstance(ir, AssociationAnalysisIR):
            kind = "mixture"
            # Only the total is fixed: the number exposed is binomial too.
            statement = (
                f"∀ q p : unitInterval, ({modules}.Association.mixtureLaw {test.n} q p).real\n"
                f"      ({modules}.Association.mixtureRejection {test.n} {lean(level)}.value) ≤ "
                f"{bound}"
            )
        elif isinstance(ir, RandomisationAnalysisIR):
            kind = "randomisation"
            self.randomisation_contracts(base, test)
            statement = exact.randomisation(test, lean(level))
        elif isinstance(ir, RateAnalysisIR):
            kind = "rate"
            # For every total rate and every share of person-time, under equal rates.
            statement = (
                f"∀ (total : NNReal) (share : unitInterval),\n"
                f"      ({modules}.Incidence.ratesLaw total share).real\n"
                f"        ({modules}.Incidence.given (fun n =>\n"
                f"          {modules}.Incidence.rejectionAt share n {bound})) ≤ {bound}"
            )
        else:
            kind = "matched"
            # For every probability that a pair is discordant, under no association.
            statement = (
                f"∀ δ : unitInterval,\n"
                f"      ({modules}.Matched.pairsLaw {test.pairs} δ {modules}.Matched.half).real\n"
                f"        ({modules}.Matched.pairsRejection {test.pairs} {bound}) ≤ {bound}"
            )
        return ExactAnalysis(base, kind, lean(level), statement, test, names)

    def randomisation_contracts(self, base: str, test) -> None:
        """The assignment is valid, and the level is attainable: some p-value can reach it."""
        modules = exact.MODULES
        if test.grouped:
            groups = "[" + ", ".join(f"({size}, {treated})" for size, treated in test.groups) + "]"
            self.out.contracts.append(
                Contract(
                    self.namer.fresh(f"{base}_groups"),
                    [f"∀ group ∈ ({groups} : {modules}.Randomisation.Groups), group.2 ≤ group.1"],
                    "decide",
                )
            )
            splits = f"({modules}.Randomisation.groupedSplits {groups}).card = {test.splits}"
            check = "grouped_splits"
        else:
            self.out.contracts.append(
                Contract(
                    self.namer.fresh(f"{base}_sizes"),
                    [f"0 < {test.treated}", f"{test.treated} < {test.units}"],
                    "decide",
                )
            )
            splits = (
                f"({modules}.Randomisation.splits {test.units} {test.treated}).card = {test.splits}"
            )
            check = "splits"
        self.out.contracts.append(Contract(self.namer.fresh(f"{base}_splits"), [splits], check))
        smallest = f"(1 : ℚ) / {test.draws + 1 if test.draws else test.splits}"
        self.out.contracts.append(
            Contract(
                self.namer.fresh(f"{base}_attainable"),
                [f"{smallest} ≤ {rational(test.alpha)}"],
                "norm_num",
            )
        )

    def tested(
        self, base: str, kind: str, model: Model, null: Null, alpha: Fraction, scope: str
    ) -> tuple[str, str, str]:
        """A test seen from outside: its rejection event and slack, and its premise."""
        test = self.namer.fresh(f"{base}_test")
        slack = self.namer.fresh(f"{base}_slack")
        self.out.fields += [
            f"{lean(test)} : {INTERFACE}.TestInterface {model.outcome}",
            f"{lean(slack)} : ℝ",
        ]
        self.out.abstracts += [Abstract(lean(test), "test"), Abstract(lean(slack), "slack")]
        premise = self.namer.fresh(f"{kind}_{base}_level")
        self.out.premises.append(
            Premise(
                premise,
                f"{INTERFACE}.LevelPremise {scope} {model.law()} {null.ref()}\n"
                f"    i.{lean(test)} {rational(alpha)} i.{lean(slack)}",
                alpha,
            )
        )
        return test, slack, premise

    def level_range(self, base: str, alpha: Fraction, extra: list[str], unfold: str = "") -> None:
        self.out.contracts.append(
            Contract(
                self.namer.fresh(f"{base}_values"),
                [f"(0 : ℚ) < {rational(alpha)}", f"{rational(alpha)} < 1", *extra],
                "norm_num",
                unfold,
            )
        )

    def cited(self, ir: CitedAnalysisIR, preferred: str | None) -> Analysis:
        design = self.design(ir.plan)
        null = self.null(ir.hypothesis)
        model = design.model
        # design() and null() accept only two-arm models and their nulls here.
        two_arm, hypothesis = ir.plan.model, ir.hypothesis
        assert isinstance(two_arm, TwoArmModelIR)
        assert isinstance(hypothesis, (OutcomeNullIR, HypothesisIR))
        base = self.own(preferred, "analysis")
        method = ir.method
        declared = method.key not in METHODS
        if declared:
            scope = f"{INTERFACE}.Scope.{SCOPES[method.scope]}"
            source = f"Declared by the author: {comment(method.title)}"
            if method.references:
                source += f". Reference: {comment(method.references[0])}"
            self.out.contracts.append(Contract("", [f"{source}."], "comment"))
            self.level_range(base, ir.alpha, [])
        else:
            entry = f"{GENERATED}.Methods.{method.key}"
            scope = f"{entry}.scope"
            clustered = model.abstract and two_arm.assignment.clustered
            counts = (
                (two_arm.assignment.clusters_control, two_arm.assignment.clusters_treatment)
                if method.unit == "cluster"
                else (two_arm.n_control, two_arm.n_treatment)
            )
            facts = [
                f"{GENERATED}.NullKey.{hypothesis.predicate} ∈ {entry}.nulls",
                f"{GENERATED}.NullKey.{hypothesis.predicate}.outcome = {entry}.outcome",
                f"{GENERATED}.OutcomeKind.{model.kind} = {entry}.outcome",
                f"{entry}.unit = .{'cluster' if clustered else 'participant'}",
                f"{entry}.minPerArm ≤ {counts[0]}",
                f"{entry}.minPerArm ≤ {counts[1]}",
                f"{entry}.minTotal ≤ {counts[0]} + {counts[1]}",
            ]
            extra: list[str] = []
            if method.null_value is None:
                facts.append(f"{entry}.nullValue = none")
            else:
                extra.append(f"{entry}.nullValue = some {rational(hypothesis.value)}")
            self.out.contracts.append(
                Contract(self.namer.fresh(f"{base}_contract"), facts, "decide")
            )
            # Unfold the method's entry only when a fact reads its rational null value.
            self.level_range(base, ir.alpha, extra, entry if extra else "")
        kind = "declared" if declared else "cited"
        test, slack, premise = self.tested(base, kind, model, null, ir.alpha, scope)
        return Analysis(
            base, kind, model, design, null, ir.alpha, method.scope, test, slack, premise
        )

    def cited_association(self, ir: CitedAssociationIR, preferred: str | None) -> Analysis:
        design = self.design(ir.plan)
        null = self.null(ir.hypothesis)
        model = design.model
        study = ir.plan.model
        assert isinstance(study, ObservationalStudyIR)
        base = self.own(preferred, "analysis")
        method = ir.method
        entry = f"{GENERATED}.Methods.{method.key}"
        facts = [
            f"{GENERATED}.ObservationalDesign.{study.design} ∈ {entry}.designs",
            f"{GENERATED}.Scale.{study.outcome_scale} ∈ {entry}.outcomeScales",
            f"{GENERATED}.Scale.{study.exposure_scale} ∈ {entry}.exposureScales",
            f"{GENERATED}.Survey.{study.survey} ∈ {entry}.surveys",
        ]
        if study.design == "matched_case_control":
            total = getattr(study, "pairs", None)
        elif study.design == "person_time_cohort":
            total = None
        else:
            total = study.total
        if total is not None:
            facts.append(f"{entry}.minTotal ≤ {total}")
        if method.min_clusters is not None and study.survey == "cluster":
            facts += [
                f"{entry}.minClusters = some {method.min_clusters}",
                f"{method.min_clusters} ≤ {study.clusters}",
            ]
        if ir.covariates:
            facts.append(f"{entry}.covariates = true")
        self.out.contracts.append(Contract(self.namer.fresh(f"{base}_contract"), facts, "decide"))
        self.level_range(base, ir.alpha, [])
        test, slack, premise = self.tested(base, "cited", model, null, ir.alpha, f"{entry}.scope")
        return Analysis(
            base, "cited", model, design, null, ir.alpha, method.scope, test, slack, premise
        )

    def fisher(self, ir: AnalysisIR, preferred: str | None) -> Analysis:
        design = self.design(ir.plan)
        null = self.null(ir.hypothesis)
        model = design.model
        if model.abstract:
            raise Untranslated(
                "Fisher's test needs the binomial model of independent participants."
            )
        if not (
            ir.hypothesis.predicate == "equal_proportions"
            or (ir.hypothesis.predicate == "proportion_difference" and ir.hypothesis.value == 0)
        ):
            raise Untranslated("Fisher's test supports only the null of equal proportions.")
        base = self.own(preferred, "analysis")
        level = self.namer.fresh(f"{base}_level")
        self.out.defs.append(
            f"def {lean(level)} : StatClaim.SignificanceLevel :=\n"
            f"  ⟨{rational(ir.alpha)}, by norm_num, by norm_num⟩"
        )
        self.out.defs.append(
            f"noncomputable def {lean(base)} :=\n"
            f"  {FISHER}.analysis {lean(model.sizes)} {design.ref()} {lean(level)}"
        )
        # The declared null is the one Fisher's guarantee is about.
        self.out.contracts.append(
            Contract(
                self.namer.fresh(f"{base}_null"),
                [f"∀ parameter, {null.ref()} parameter ↔ {lean(base)}.hypothesis parameter"],
                "fisher_null",
                predicate=ir.hypothesis.predicate,
            )
        )
        if design.compatible is not None:
            self.out.contracts.append(
                Contract(
                    self.namer.fresh(f"{base}_contract"),
                    [
                        f"({FISHER}.module {lean(model.sizes)} {lean(level)}).Requires\n"
                        f"      {design.ref()}"
                    ],
                    "fisher_requires",
                    compatible=design.compatible.ref(),
                )
            )
        return Analysis(base, "fisher", model, design, null, ir.alpha, "finite_sample", level=level)

    # Claims -----------------------------------------------------------------------------
    def type_i(self, name: str, request_id: int, analysis: "Analysis | ExactAnalysis") -> None:
        if isinstance(analysis, ExactAnalysis):
            space = self.namer.fresh(f"{name}_checks")
            self.out.claims.append(
                Claim(
                    name,
                    analysis.statement,
                    "typeI",
                    request_id,
                    "proved",
                    analysis=analysis,
                    space=space,
                )
            )
            return
        compatible = analysis.design.compatible
        if compatible is None:
            raise Untranslated(
                "The design leaves data-dependent stopping unspecified, so it supplies no "
                "sampling law and no Type I claim can be stated."
            )
        if analysis.kind == "fisher":
            statement = (
                f"({lean(analysis.name)}.typeIClaim {compatible.ref()}\n"
                f"      ({lean(analysis.level)}.value : ℝ)).statement"
            )
            self.out.claims.append(
                Claim(name, statement, "typeI", request_id, "proved", analysis=analysis)
            )
            return
        test = f"i.{lean(analysis.test)}"
        bound = real(analysis.alpha)
        # A large-sample guarantee carries its slack; only a finite-sample one is stated
        # at the level itself, and Lean refuses the latter for a large-sample method.
        if analysis.scope != "finite_sample":
            bound = f"({bound} + i.{lean(analysis.slack)})"
        statement = (
            f"{INTERFACE}.typeIClaim {compatible.ref()} {analysis.null.ref()} {test} {bound}"
        )
        self.out.claims.append(
            Claim(
                name,
                statement,
                "typeI",
                request_id,
                analysis.kind,
                analysis.premise,
                analysis=analysis,
            )
        )

    def combination(self, family: object, leaves: list[Analysis], within: str = "") -> Combination:
        """A combination's parts, with its leaves added to the claim's list in order.

        `within` is the rule of the combination this one is a member of: a family,
        sequence or graph can be a member only of a fixed sequence, where it passes when
        every member rejects; a design with looks can be a member of any combination.
        """
        if not isinstance(family, (FamilyIR, ComposedFamilyIR)):
            raise Untranslated(f"{type(family).__name__} combinations are not translated yet.")
        looks = isinstance(family, SequentialIR)
        mode = "family" if isinstance(family, FamilyIR) else family.mode
        if within and not looks and within != "sequence":
            raise Untranslated(
                "A family or graph is translated as a member only of a fixed sequence."
            )
        rule = {
            "family": "union",
            "sequential": "union",
            "fixed_sequence": "sequence",
            "graphical": "graph",
        }.get(mode)
        if rule is None:
            raise Untranslated(f"{mode} combinations are not translated yet.")
        parts = []
        for _, member in family.analyses:
            if isinstance(member, ComposedFamilyIR):
                kind = (
                    "looks"
                    if isinstance(member, SequentialIR)
                    else (
                        "sequence"
                        if member.mode == "fixed_sequence"
                        else "graph"
                        if member.mode == "graphical"
                        else "family"
                    )
                )
                inner = self.combination(member, leaves, rule)
                parts.append(Part(kind, member.alpha, combination=inner))
                continue
            analysis = self.analysis(member)
            if isinstance(analysis, ExactAnalysis):
                raise Untranslated(
                    f"Exact member {analysis.name} joins combinations in a later part."
                )
            if analysis.design.compatible is None:
                raise Untranslated(f"Member {analysis.name} has no sampling law to combine.")
            parts.append(Part("leaf", member.alpha, analysis, len(leaves)))
            leaves.append(analysis)
        graph = None
        if rule == "graph":
            assert isinstance(family, ComposedFamilyIR)
            graph = self.graph(family, parts)
        return Combination(rule, family.alpha, parts, graph)

    def graph(self, family: ComposedFamilyIR, parts: list[Part]) -> Graph:
        """A graphical procedure: its facts, decided by Lean, and its cited guarantee."""
        k = f"graph:{id(family)}"
        if k in self.memo:
            return self.memo[k]  # type: ignore[return-value]
        leaves = [part.leaf for part in parts]
        if any(leaf is None for leaf in leaves):
            raise Untranslated("A graph's members are translated only when each is one test.")
        base = self.namer.fresh("graph")
        weights, rows = list(family.weights), [list(row) for row in family.transitions]
        # The starting shares of the level: none negative, and at most the whole level.
        shares = [f"(0 : ℚ) ≤ {rational(w)}" for w in weights]
        shares.append(" + ".join(rational(w) for w in weights) + " ≤ 1")
        # Each row: what a rejected test passes on. None to itself, none negative, at most all.
        passes = []
        for index, row in enumerate(rows):
            passes.append(f"{rational(row[index])} = 0")
            passes += [f"(0 : ℚ) ≤ {rational(t)}" for t in row]
            passes.append(" + ".join(rational(t) for t in row) + " ≤ 1")
        # Every test is declared at the graph's level; the weights say what share it starts with.
        levels = [f"{rational(part.level)} = {rational(family.alpha)}" for part in parts]
        for suffix, facts in (("weights", shares), ("transitions", passes), ("levels", levels)):
            self.out.contracts.append(
                Contract(self.namer.fresh(f"{base}_{suffix}"), facts, "norm_num")
            )
        procedure = self.namer.fresh(f"{base}_procedure")
        slack = self.namer.fresh(f"{base}_slack")
        views = " → ".join(
            f"{INTERFACE}.MemberView Θ Ω {leaf.model.parameter} {leaf.model.outcome}"
            for leaf in leaves
            if leaf is not None
        )
        self.out.fields += [
            f"{lean(procedure)} : ∀ (Θ Ω : Type) [MeasurableSpace Ω], "
            f"{INTERFACE}.JointStudy Θ Ω → {views} → Fin {len(parts)} → Set Ω",
            f"{lean(slack)} : ℝ",
        ]
        self.out.abstracts += [
            # Θ, Ω, the measurable space, σ, each member's view, and the member asked about.
            Abstract(lean(procedure), "procedure", arity=4 + len(parts) + 1),
            Abstract(lean(slack), "slack"),
        ]
        large = any(leaf.scope != "finite_sample" for leaf in leaves if leaf is not None)
        scope = f"{INTERFACE}.Scope.{'largeSample' if large else 'finiteSample'}"
        premise = self.namer.fresh(f"cited_{base}_rule")
        result = Graph(base, procedure, slack, premise, scope)
        self.memo[k] = result
        # The premise quantifies over the graph's own members, so their views count from zero.
        own = [Part("leaf", part.level, part.leaf, index) for index, part in enumerate(parts)]
        combination = Combination("graph", family.alpha, own, result)
        members = [leaf for leaf in leaves if leaf is not None]
        self.out.premises.append(
            Premise(
                premise,
                f"{scope}.permits i.{lean(slack)} ∧\n    " + self.joint(combination, members),
                family.alpha,
                "graph",
                len(parts),
            )
        )
        return result

    def joint(self, combination: Combination, leaves: list[Analysis]) -> str:
        """A claim over every joint study whose marginals are the leaves' declared laws."""
        binders = " ".join(
            f"({view(index)} : {INTERFACE}.MemberView Θ Ω {leaf.model.parameter_type()} "
            f"{leaf.model.outcome_type()})"
            for index, leaf in enumerate(leaves)
        )
        marginals = " →\n      ".join(
            f"{view(index)}.Marginal σ {leaf.model.law()}" for index, leaf in enumerate(leaves)
        )
        return (
            f"∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : {INTERFACE}.JointStudy Θ Ω)\n"
            f"      {binders},\n"
            f"      {marginals} →\n"
            f"      {combination_claim(combination)}"
        )

    def familywise(self, name: str, request_id: int, family: object) -> None:
        """A family, a fixed sequence, a graph or a design with looks, over its members."""
        leaves: list[Analysis] = []
        combination = self.combination(family, leaves)
        assumed = any(leaf.kind in ("cited", "declared") for leaf in leaves)
        graphs = self.graphs(combination)
        own = None
        if combination.graph is not None:
            own, grade = combination.graph.premise, "cited"
        elif assumed or graphs:
            grade = "conditional"
        else:
            grade = "proved"
        self.out.claims.append(
            Claim(
                name,
                self.joint(combination, leaves),
                "familywise",
                request_id,
                grade,
                own=own,
                combination=combination,
                leaves=leaves,
            )
        )

    def graphs(self, combination: Combination) -> list[Graph]:
        """The graphs inside a combination, whose cited guarantees its claim rests on."""
        found = []
        for part in combination.parts:
            if part.combination is not None:
                if part.combination.graph is not None:
                    found.append(part.combination.graph)
                found += self.graphs(part.combination)
        return found

    # The program ------------------------------------------------------------------------
    def run(self) -> Denotation:
        holders: dict[int, str] = {}
        for binding in self.program.bindings:
            if isinstance(binding.value, VerificationResultIR):
                holders.setdefault(binding.value.request_id, binding.name)
        for binding in self.program.bindings:
            value = binding.value
            try:
                if isinstance(value, (TwoArmModelIR, ObservationalStudyIR)):
                    self.model(value, binding.name)
                elif isinstance(value, PlanIR):
                    self.design(value, binding.name)
                elif isinstance(value, (OutcomeNullIR, HypothesisIR, AssociationNullIR)):
                    self.null(value, binding.name)
                elif isinstance(value, (CitedAnalysisIR, AnalysisIR, CitedAssociationIR)) or (
                    exact.is_exact(value)
                ):
                    self.analysis(value, binding.name)
                elif isinstance(value, (FamilyIR, ComposedFamilyIR)):
                    self.combination(value, [])
                elif (
                    type(value).__module__.startswith("statclaim")
                    and not isinstance(value, ClaimIR)
                    and type(value).__name__ not in IGNORED
                ):
                    self.out.skipped[binding.name] = (
                        f"{type(value).__name__} is not translated yet."
                    )
            except Untranslated as reason:
                self.out.skipped[binding.name] = str(reason)
        for request_id, request in enumerate(self.program.requests, 1):
            holder = holders.get(request_id, f"request_{request_id}")
            if request.operation != "verify":
                continue
            try:
                # Python's open requirements stay open: Lean is never asked to prove them.
                open_requirements = requirements(self.program, request)
                if open_requirements:
                    raise Untranslated(open_requirements[0].message)
                name = self.namer.fresh(f"{holder}_claim")
                subject = request.claim.subject
                if request.claim.kind == "typeI" and isinstance(subject, SequentialIR):
                    # One question at several looks: the union bound over the looks.
                    self.familywise(name, request_id, subject)
                elif request.claim.kind == "typeI":
                    self.type_i(name, request_id, self.analysis(subject))
                elif request.claim.kind == "familywise":
                    self.familywise(name, request_id, request.claim.subject)
                else:
                    raise Untranslated(f"{request.claim.kind} claims are not translated yet.")
            except Untranslated as reason:
                self.out.skipped[holder] = str(reason)
        return self.out


def denote(program: ProgramIR) -> Denotation:
    """Everything a compiled program states in Lean, and what it leaves out."""
    return Denoter(program).run()
