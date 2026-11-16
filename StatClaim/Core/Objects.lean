module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Minimal shared statistical objects. Parameter and outcome domains are Lean
types; admissibility refines the outcome domain. Sampling plans may lack a law,
so compatibility must be supplied before creating a design-level probability
claim. Nothing here proves that real observations follow a declared model.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Core

open MeasureTheory

universe u v w

/-- A family of probability laws and its admissible observation domain. -/
structure Model (Parameter : Type u) (Outcome : Type v) [MeasurableSpace Outcome] where
  law : Parameter → Measure Outcome
  probability : ∀ parameter, IsProbabilityMeasure (law parameter)
  admissible : Set Outcome
  admissible_measurable : MeasurableSet admissible
  supported : ∀ parameter, (law parameter).real admissible = 1

/-- A law attributed to the observation mechanism, before matching it to a model. -/
structure SamplingLaw (Parameter : Type u) (Outcome : Type v) [MeasurableSpace Outcome] where
  law : Parameter → Measure Outcome
  probability : ∀ parameter, IsProbabilityMeasure (law parameter)

/-- Descriptive categories, not proofs of the observation mechanism. -/
inductive SamplingKind where
  | fixedSample
  | dataDependent
  deriving DecidableEq, Repr

/-- A declared plan may leave its induced law unresolved. The category alone
does not establish that its law agrees with a particular statistical model. -/
structure SamplingPlan (Parameter : Type u) (Outcome : Type v) [MeasurableSpace Outcome] where
  kind : SamplingKind
  inducedLaw : Option (SamplingLaw Parameter Outcome)

variable {Parameter : Type u} {Outcome : Type v} [MeasurableSpace Outcome]

/-- A model paired with a declared sampling plan; compatibility is a separate object. -/
structure StudyDesign (model : Model Parameter Outcome) where
  sampling : SamplingPlan Parameter Outcome

/-- Evidence that the supplied plan law agrees with the model for every parameter. -/
structure Compatibility {model : Model Parameter Outcome} (design : StudyDesign model) where
  samplingLaw : SamplingLaw Parameter Outcome
  supplied : design.sampling.inducedLaw = some samplingLaw
  agrees : ∀ parameter, samplingLaw.law parameter = model.law parameter

/-- Declare a fixed plan with the model's sampling law. Following this law in a
real study remains an explicit assumption of any application of its guarantees. -/
def StudyDesign.fixed (model : Model Parameter Outcome) : StudyDesign model where
  sampling := {
    kind := .fixedSample
    inducedLaw := some ⟨model.law, model.probability⟩ }

def Compatibility.fixed (model : Model Parameter Outcome) :
    Compatibility (StudyDesign.fixed model) where
  samplingLaw := ⟨model.law, model.probability⟩
  supplied := rfl
  agrees := fun _ => rfl

/-- Changing to an unspecified adaptive mechanism drops the supplied sampling
law; it does not silently retain the fixed-plan law or its compatibility evidence. -/
def StudyDesign.unresolvedAdaptive (model : Model Parameter Outcome) : StudyDesign model where
  sampling := {kind := .dataDependent, inducedLaw := none}

/-- Missing law information prevents use of the compatibility contract. This is
not a statement that the real procedure has an inflated error probability. -/
theorem no_compatibility_without_law {model : Model Parameter Outcome}
    (design : StudyDesign model) (missing : design.sampling.inducedLaw = none) :
    ¬ Nonempty (Compatibility design) := by
  rintro ⟨compatibility⟩
  have supplied := compatibility.supplied
  rw [missing] at supplied
  cases supplied

/-- A tested hypothesis restricts parameters; it is not asserted as a fact about data. -/
abbrev Hypothesis (Parameter : Type u) := Parameter → Prop

/-- A specified statistic and rejection rule. Its measurability is a requirement
of the definition, and invalid observations are excluded from its rejection event. -/
structure Procedure (model : Model Parameter Outcome) where
  Output : Type w
  evaluate : Outcome → Output
  reject : Output → Prop
  rejection_measurable : MeasurableSet {outcome | model.admissible outcome ∧ reject (evaluate outcome)}

def Procedure.rejectionEvent {model : Model Parameter Outcome} (procedure : Procedure model) :
    Set Outcome :=
  {outcome | model.admissible outcome ∧ procedure.reject (procedure.evaluate outcome)}

/-- Bind the design, tested hypothesis, and mathematical procedure. -/
structure Analysis (model : Model Parameter Outcome) where
  design : StudyDesign model
  hypothesis : Hypothesis Parameter
  procedure : Procedure.{u, v, w} model

/-- Observations carry a checked domain-membership proof, not a sampling-law proof. -/
abbrev Observation (model : Model Parameter Outcome) := {outcome // model.admissible outcome}

/-- A proposed result. Its value is deliberately not assumed equal to the formal
evaluation; that equality is a separate claim requiring evidence. -/
structure Result {model : Model Parameter Outcome} (analysis : Analysis.{u, v, w} model) where
  observation : Observation model
  value : analysis.procedure.Output

/-- A mathematical proposition. Human labels and artifact identifiers belong in
the reporting layer and cannot replace the proposition or a proof of it. -/
structure Claim where
  statement : Prop

/-- Logical evidence for precisely this claim. Bundle provenance and version
bindings remain the responsibility of the existing certificate pipeline. -/
structure Certificate (claim : Claim) : Prop where
  establishes : claim.statement

/-- Assumed and unresolved claims provide no projection to a mathematical proof. -/
inductive Assessment (claim : Claim) where
  | verified (certificate : Certificate claim)
  | violation (refutation : ¬ claim.statement)
  | unresolved (obligations : List String)
  | assumed

def Result.exactClaim {model : Model Parameter Outcome} {analysis : Analysis.{u, v, w} model}
    (result : Result analysis) : Claim :=
  ⟨result.value = analysis.procedure.evaluate result.observation.val⟩

/-- Quantify over the null while using the actual supplied sampling law. An
explicit compatibility object is needed to create this claim. -/
def Analysis.typeIClaim {model : Model Parameter Outcome} (analysis : Analysis.{u, v, w} model)
    (compatibility : Compatibility analysis.design) (bound : ℝ) : Claim :=
  ⟨∀ parameter, analysis.hypothesis parameter →
    (compatibility.samplingLaw.law parameter).real analysis.procedure.rejectionEvent ≤ bound⟩

/-- A checked design-level guarantee with its required compatibility evidence. -/
structure TypeIGuarantee {model : Model Parameter Outcome}
    (analysis : Analysis.{u, v, w} model) (bound : ℝ) where
  compatibility : Compatibility analysis.design
  certificate : Certificate (analysis.typeIClaim compatibility bound)

/-- A reusable typed provider. Its output can require certificates, so module
metadata alone cannot establish any statistical property. -/
structure Module (Input : Type u) where
  name : String
  version : String
  Requires : Input → Prop
  Output : Input → Type v
  provide : (input : Input) → Requires input → Output input

end StatClaim.Core
