"""Translate a compiled program into Lean. Milestone 3 of docs/proposals/lean-translation.md.

The program's abstract parts become fields of an `Instance` structure: the laws of
outcomes Lean does not fix, and the rejection event and slack of each cited or declared
test. Their guarantees become fields of a `Premises` structure. Each Type I claim that a
`verify` requests becomes its own theorem, and the file ends in a `ProgramTheorem` with a
witness that the premises can hold together.

What this translates so far: two-arm models, fixed and unspecified sampling plans, nulls,
cited and declared tests, the two-sided Fisher test, and their Type I claims. Anything
else is listed in `skipped` with the reason, never left out silently.
"""

import json
from dataclasses import dataclass, field
from fractions import Fraction

from statclaim.language import (
    AnalysisIR,
    CitedAnalysisIR,
    ClaimIR,
    HypothesisIR,
    ModelIR,
    OutcomeNullIR,
    PlanIR,
    ProgramIR,
    normalize,
)
from statclaim.language.ir import TwoArmModelIR
from statclaim.lean_translation.emit import Namer, comment, rational, real
from statclaim.lean_translation.emit import name as lean
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


# Names the file itself uses; a binding with one of these names is renamed.
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


class Untranslated(Exception):
    """A value, or a claim about it, that this translator does not handle yet."""


@dataclass
class Model:
    name: str
    abstract: bool
    kind: str  # the outcome kind: continuous, survival or binary
    parameter: str
    outcome: str
    sizes: str = ""  # the FixedSampleDesign of a binomial model

    def ref(self) -> str:
        return f"i.{lean(self.name)}" if self.abstract else lean(self.name)

    def core(self) -> str:
        return f"{self.ref()}.toModel" if self.abstract else self.ref()

    def law(self) -> str:
        return f"{self.ref()}.law"


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
    analysis: str = ""  # the Lean analysis of an exact test


@dataclass
class Translation:
    lean: str
    claims: dict[str, str] = field(default_factory=dict)  # claim name → grade
    skipped: dict[str, str] = field(default_factory=dict)  # binding or request → reason


def key(value: object) -> str:
    return json.dumps(normalize(value), sort_keys=True)


class Translator:
    def __init__(self, program: ProgramIR):
        self.program = program
        self.namer = Namer([*STRUCTURAL, *(b.name for b in program.bindings)])
        self.memo: dict[str, object] = {}
        self.fields: list[str] = []  # Instance fields
        self.instances: list[str] = []  # instance attributes of Instance fields
        self.witness: list[str] = []  # the witness's field values
        self.defs: list[str] = []
        self.contracts: list[str] = []
        self.premises: list[str] = []  # Premises fields
        self.premise_proofs: list[str] = []  # each premise, met by the witness
        self.claims: list[tuple[str, str, str]] = []  # name, statement, proof
        self.grades: dict[str, str] = {}

    def own(self, preferred: str | None, kind: str) -> str:
        """A binding's own name, unless the file needs it; otherwise a fresh one."""
        if preferred is None or preferred in STRUCTURAL:
            return self.namer.fresh(preferred or kind)
        return preferred

    # Values -----------------------------------------------------------------------------
    def model(self, ir: object, preferred: str | None = None) -> Model:
        if not isinstance(ir, TwoArmModelIR):
            raise Untranslated(f"{type(ir).__name__} models are not translated yet.")
        k = key(ir)
        if k in self.memo:
            return self.memo[k]  # type: ignore[return-value]
        assignment, measured = ir.assignment, ir.measured
        # A binomial law needs independent participants measured once; otherwise the law
        # is left abstract, as for continuous and survival outcomes.
        concrete = (
            isinstance(ir, ModelIR) and not assignment.clustered and measured.measurements == 1
        )
        base = self.own(preferred, "model")
        if concrete:
            sizes = self.namer.fresh(f"{base}_sizes")
            self.defs.append(
                f"def {lean(sizes)} : StatClaim.FixedSampleDesign :=\n"
                f"  ⟨{ir.n_control}, {ir.n_treatment}, by decide, by decide⟩"
            )
            self.defs.append(f"noncomputable def {lean(base)} := {BINOMIAL}.model {lean(sizes)}")
            result = Model(
                base, False, "binary", f"{BINOMIAL}.Parameters", f"{BINOMIAL}.Counts", sizes
            )
        else:
            parameter = self.namer.fresh(f"{base}_Parameter")
            outcome = self.namer.fresh(f"{base}_Outcome")
            space = self.namer.fresh(f"{base}_space")
            self.fields += [
                f"{lean(parameter)} : Type",
                f"{lean(outcome)} : Type",
                f"[{lean(space)} : MeasurableSpace {lean(outcome)}]",
                f"{lean(base)} : {INTERFACE}.TwoArmModel {lean(parameter)} {lean(outcome)}",
            ]
            self.instances.append(f"attribute [instance] Instance.{lean(space)}")
            self.witness += [
                f"{lean(parameter)} := Unit",
                f"{lean(outcome)} := Unit",
                f"{lean(base)} := {INTERFACE}.TwoArmModel.trivial",
            ]
            result = Model(base, True, measured.kind, lean(parameter), lean(outcome))
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
        if ir.stopping == "fixed":
            self.defs.append(
                f"noncomputable def {lean(base)} {arguments}:=\n"
                f"  {CORE}.StudyDesign.fixed {model.core()}"
            )
            compatible = Value(self.namer.fresh(f"{base}_compatible"), model.abstract)
            design = Value(base, model.abstract)
            self.defs.append(
                f"noncomputable def {lean(compatible.name)} {arguments}:\n"
                f"    {CORE}.Compatibility {design.ref()} :=\n"
                f"  {CORE}.Compatibility.fixed _"
            )
        else:
            # Data-dependent stopping without a stated rule supplies no sampling law, so no
            # Type I claim about it can be stated (Core.no_compatibility_without_law).
            self.defs.append(
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
        if not isinstance(ir, (OutcomeNullIR, HypothesisIR)):
            raise Untranslated(f"{type(ir).__name__} nulls are not translated yet.")
        model = self.model(ir.model)
        base = self.own(preferred, "null")
        if model.abstract:
            term = (
                f"{model.ref()}.null {GENERATED}.NullKey.{ir.predicate}.shape {rational(ir.value)}"
            )
            self.defs.append(f"def {lean(base)} (i : Instance) :=\n  {term}")
        else:
            term = BINOMIAL_NULLS[ir.predicate]
            if ir.predicate != "equal_proportions":
                term += f" {rational(ir.value)}"
            self.defs.append(f"def {lean(base)} : {CORE}.Hypothesis {model.parameter} :=\n  {term}")
        result = Null(base, model.abstract, model)
        self.memo[k] = result
        return result

    def analysis(self, ir: object, preferred: str | None = None) -> Analysis:
        k = key(ir)
        if k in self.memo:
            return self.memo[k]  # type: ignore[return-value]
        if isinstance(ir, CitedAnalysisIR):
            result = self.cited(ir, preferred)
        elif isinstance(ir, AnalysisIR) and ir.alternative == "two_sided":
            result = self.fisher(ir, preferred)
        else:
            raise Untranslated(f"{type(ir).__name__} analyses are not translated yet.")
        self.memo[k] = result
        return result

    def cited(self, ir: CitedAnalysisIR, preferred: str | None) -> Analysis:
        design = self.design(ir.plan)
        null = self.null(ir.hypothesis)
        model = design.model
        # design() and null() accept only two-arm models and their nulls.
        two_arm, hypothesis = ir.plan.model, ir.hypothesis
        assert isinstance(two_arm, TwoArmModelIR)
        assert isinstance(hypothesis, (OutcomeNullIR, HypothesisIR))
        base = self.own(preferred, "analysis")
        method = ir.method
        declared = method.key not in METHODS
        test = self.namer.fresh(f"{base}_test")
        slack = self.namer.fresh(f"{base}_slack")
        self.fields += [
            f"{lean(test)} : {INTERFACE}.TestInterface {model.outcome}",
            f"{lean(slack)} : ℝ",
        ]
        self.witness += [
            f"{lean(test)} := {INTERFACE}.TestInterface.neverRejects _",
            f"{lean(slack)} := 0",
        ]
        values = [f"(0 : ℚ) < {rational(ir.alpha)}", f"{rational(ir.alpha)} < 1"]
        if declared:
            scope = f"{INTERFACE}.Scope.{SCOPES[method.scope]}"
            source = f"Declared by the author: {comment(method.title)}"
            if method.references:
                source += f". Reference: {comment(method.references[0])}"
            self.contracts.append(f"-- {source}.")
        else:
            entry = f"{GENERATED}.Methods.{method.key}"
            scope = f"{entry}.scope"
            clustered = model.abstract and two_arm.assignment.clustered
            counts = (
                (
                    two_arm.assignment.clusters_control,
                    two_arm.assignment.clusters_treatment,
                )
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
            if method.null_value is None:
                facts.append(f"{entry}.nullValue = none")
            else:
                values.append(f"{entry}.nullValue = some {rational(hypothesis.value)}")
            self.contracts.append(
                f"theorem {lean(self.namer.fresh(f'{base}_contract'))} :\n    "
                + " ∧\n    ".join(facts)
                + " := by decide"
            )
        # Unfold the method's entry only when a fact reads its rational null value.
        unfold = "" if len(values) == 2 else f" [{GENERATED}.Methods.{method.key}]"
        self.contracts.append(
            f"theorem {lean(self.namer.fresh(f'{base}_values'))} :\n    "
            + " ∧\n    ".join(values)
            + f" := by norm_num{unfold}"
        )
        premise = self.namer.fresh(f"{base}_level")
        self.premises.append(
            f"{lean(premise)} : {INTERFACE}.LevelPremise {scope} {model.law()} {null.ref()}\n"
            f"    i.{lean(test)} {rational(ir.alpha)} i.{lean(slack)}"
        )
        self.premise_proofs.append(f"{INTERFACE}.neverRejects_meets_level _ _ _ _ (by norm_num)")
        return Analysis(
            base,
            "declared" if declared else "cited",
            model,
            design,
            null,
            ir.alpha,
            method.scope,
            test,
            slack,
            premise,
        )

    def fisher(self, ir: AnalysisIR, preferred: str | None) -> Analysis:
        design = self.design(ir.plan)
        null = self.null(ir.hypothesis)
        model = design.model
        if model.abstract:
            raise Untranslated(
                "Fisher's test needs the binomial model of independent participants."
            )
        base = self.own(preferred, "analysis")
        level = self.namer.fresh(f"{base}_level")
        self.defs.append(
            f"def {lean(level)} : StatClaim.SignificanceLevel :=\n"
            f"  ⟨{rational(ir.alpha)}, by norm_num, by norm_num⟩"
        )
        analysis = f"{FISHER}.analysis {lean(model.sizes)} {design.ref()} {lean(level)}"
        self.defs.append(f"noncomputable def {lean(base)} :=\n  {analysis}")
        # Fisher's test supports equal proportions; a zero difference is the same null.
        if ir.hypothesis.predicate == "equal_proportions":
            agreement = "Iff.rfl"
        elif ir.hypothesis.predicate == "proportion_difference" and ir.hypothesis.value == 0:
            agreement = f"{BINOMIAL}.proportionDifference_zero_iff parameter"
        else:
            raise Untranslated("Fisher's test supports only the null of equal proportions.")
        self.contracts.append(
            f"theorem {lean(self.namer.fresh(f'{base}_null'))} :\n"
            f"    ∀ parameter, {null.ref()} parameter ↔ {lean(base)}.hypothesis parameter :=\n"
            f"  fun parameter => {agreement}"
        )
        if design.compatible is not None:
            self.contracts.append(
                f"theorem {lean(self.namer.fresh(f'{base}_contract'))} :\n"
                f"    ({FISHER}.module {lean(model.sizes)} {lean(level)}).Requires\n"
                f"      {design.ref()} :=\n"
                f"  ⟨{design.compatible.ref()}⟩"
            )
        return Analysis(
            base,
            "fisher",
            model,
            design,
            null,
            ir.alpha,
            "finite_sample",
            level=level,
            analysis=base,
        )

    # Claims -----------------------------------------------------------------------------
    def type_i(self, claim_name: str, analysis: Analysis) -> None:
        compatible = analysis.design.compatible
        if compatible is None:
            raise Untranslated(
                "The design leaves data-dependent stopping unspecified, so it supplies no "
                "sampling law and no Type I claim can be stated."
            )
        if analysis.kind == "fisher":
            statement = (
                f"({lean(analysis.analysis)}.typeIClaim {compatible.ref()}\n"
                f"      ({lean(analysis.level)}.value : ℝ)).statement"
            )
            proof = (
                f"{FISHER}.typeI_statement {lean(analysis.model.sizes)} "
                f"{analysis.design.ref()} {compatible.ref()} {lean(analysis.level)}"
            )
            self.grades[claim_name] = "proved"
        else:
            test = f"i.{lean(analysis.test)}"
            premise = f"premises.{lean(analysis.premise)}"
            null = analysis.null.ref()
            if analysis.scope == "finite_sample":
                bound = real(analysis.alpha)
                statement = f"{INTERFACE}.typeIClaim {compatible.ref()} {null} {test} {bound}"
                proof = f"{INTERFACE}.typeI_of_finite_premise {compatible.ref()} rfl {premise}"
            else:
                bound = f"({real(analysis.alpha)} + i.{lean(analysis.slack)})"
                statement = f"{INTERFACE}.typeIClaim {compatible.ref()} {null} {test} {bound}"
                proof = f"{INTERFACE}.typeI_of_premise {compatible.ref()} {premise}"
            self.grades[claim_name] = analysis.kind
        self.claims.append((claim_name, statement, proof))

    # The program ------------------------------------------------------------------------
    def run(self) -> Translation:
        skipped: dict[str, str] = {}
        holders: dict[int, str] = {}
        for binding in self.program.bindings:
            request_id = getattr(binding.value, "request_id", None)
            if request_id is not None and type(binding.value).__name__ == "VerificationResultIR":
                holders.setdefault(request_id, binding.name)
        for binding in self.program.bindings:
            value = binding.value
            try:
                if isinstance(value, TwoArmModelIR):
                    self.model(value, binding.name)
                elif isinstance(value, PlanIR):
                    self.design(value, binding.name)
                elif isinstance(value, (OutcomeNullIR, HypothesisIR)):
                    self.null(value, binding.name)
                elif isinstance(value, (CitedAnalysisIR, AnalysisIR)):
                    self.analysis(value, binding.name)
                elif (
                    type(value).__module__.startswith("statclaim")
                    and not isinstance(value, ClaimIR)
                    and type(value).__name__ not in IGNORED
                ):
                    skipped[binding.name] = f"{type(value).__name__} is not translated yet."
            except Untranslated as reason:
                skipped[binding.name] = str(reason)
        for request_id, request in enumerate(self.program.requests, 1):
            claim_name = holders.get(request_id, f"request_{request_id}")
            if request.operation != "verify":
                continue
            try:
                if request.claim.kind != "typeI":
                    raise Untranslated(f"{request.claim.kind} claims are not translated yet.")
                self.type_i(
                    self.namer.fresh(f"{claim_name}_claim"), self.analysis(request.claim.subject)
                )
            except Untranslated as reason:
                skipped[claim_name] = str(reason)
        return Translation(self.render(), dict(self.grades), skipped)

    def render(self) -> str:
        out = ["set_option linter.unusedVariables false", ""]
        out += [
            "/-- The program's abstract parts: laws Lean does not fix, and the tests seen",
            "from outside. -/",
            "structure Instance where",
        ]
        out += [f"  {f}" for f in self.fields]
        out += [*self.instances, ""]
        for definition in self.defs:
            out += [definition, ""]
        if self.contracts:
            out += ["-- Contract facts the Python compiler checks, decided by Lean.", ""]
            for contract in self.contracts:
                out += [contract, ""]
        out += [
            "/-- The premises the claims rest on: cited and declared guarantees. -/",
            "structure Premises (i : Instance) : Prop where",
        ]
        out += [f"  {p}" for p in self.premises]
        out.append("")
        for claim_name, statement, proof in self.claims:
            out += [
                f"theorem {lean(claim_name)} (i : Instance) (premises : Premises i) :",
                f"    {statement} :=",
                f"  {proof}",
                "",
            ]
        conjuncts = [statement for _, statement, _ in self.claims] or ["True"]
        out += [
            "/-- What the program claims. -/",
            "def Claims (i : Instance) : Prop :=",
            "  " + " ∧\n  ".join(f"({c})" if len(conjuncts) > 1 else c for c in conjuncts),
            "",
        ]
        out.append("/-- One instance meeting every premise, so the claims are not vacuous. -/")
        if self.witness:
            out.append("noncomputable def witness : Instance where")
            out += [f"  {w}" for w in self.witness]
        else:
            out.append("noncomputable def witness : Instance := ⟨⟩")
        out.append("")
        proofs = [f"{lean(n)} i premises" for n, _, _ in self.claims]
        implies = (
            proofs[0] if len(proofs) == 1 else (f"⟨{', '.join(proofs)}⟩" if proofs else "trivial")
        )
        out += [
            f"theorem program : {INTERFACE}.ProgramTheorem Premises Claims where",
            f"  implies := fun i premises => {implies}",
            f"  satisfiable := ⟨witness, ⟨{', '.join(self.premise_proofs)}⟩⟩",
        ]
        return "\n".join(out) + "\n"


# Values that are not study objects: results, fields read from them, and plain numbers.
IGNORED = {"VerificationResultIR", "CalculationResultIR", "FieldIR"}


def translate(program: ProgramIR) -> Translation:
    """The Lean text of a compiled program, its claims' grades and what it leaves out."""
    return Translator(program).run()
