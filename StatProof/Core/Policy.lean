module

public import StatProof.Core.Objects

/-!
Complete sampling and decision policies. A policy states the law of all
potential data and a measurable rule mapping those data to the record actually
observed. The record has its own type, so stopping rules and interim decisions
are part of the design rather than exceptions to a fixed-sample model.

Fixed sampling is the special case whose record is the potential data.
Operating characteristics are claims about the policy's induced law; they are
established by a theorem for that policy, not by resemblance to another design.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Core

open MeasureTheory

universe u v w

/-- Potential data, their law, and the rule producing the observed record. -/
structure Policy (Parameter : Type u) (Potential : Type v) (Record : Type w)
    [MeasurableSpace Potential] [MeasurableSpace Record] where
  potentialLaw : Parameter → Measure Potential
  probability : ∀ parameter, IsProbabilityMeasure (potentialLaw parameter)
  record : Potential → Record
  record_measurable : Measurable record

variable {Parameter : Type u} {Potential : Type v} {Record : Type w}
  [MeasurableSpace Potential] [MeasurableSpace Record]

/-- The law of the observed record, derived from the potential-data law. -/
noncomputable def Policy.law (policy : Policy Parameter Potential Record)
    (parameter : Parameter) : Measure Record :=
  (policy.potentialLaw parameter).map policy.record

theorem Policy.law_probability (policy : Policy Parameter Potential Record)
    (parameter : Parameter) : IsProbabilityMeasure (policy.law parameter) :=
  (Measure.isProbabilityMeasure_map_iff policy.record_measurable.aemeasurable).mpr
    (policy.probability parameter)

/-- The induced law in the form used by composition modules. -/
noncomputable def Policy.samplingLaw (policy : Policy Parameter Potential Record) :
    SamplingLaw Parameter Record :=
  ⟨policy.law, policy.law_probability⟩

/-- Events about the record are events about the potential data. -/
theorem Policy.law_real_apply (policy : Policy Parameter Potential Record)
    (parameter : Parameter) {event : Set Record} (measurable : MeasurableSet event) :
    (policy.law parameter).real event =
      (policy.potentialLaw parameter).real (policy.record ⁻¹' event) :=
  map_measureReal_apply policy.record_measurable measurable

/-- A tested hypothesis and the records leading to its rejection. -/
structure PolicyAnalysis (policy : Policy Parameter Potential Record) where
  hypothesis : Hypothesis Parameter
  rejection : Set Record
  rejection_measurable : MeasurableSet rejection

variable {policy : Policy Parameter Potential Record}

/-- Rejection probability is at most the bound throughout the hypothesis. -/
def PolicyAnalysis.typeIClaim (analysis : PolicyAnalysis policy) (bound : ℝ) : Claim :=
  ⟨∀ parameter, analysis.hypothesis parameter →
    (policy.law parameter).real analysis.rejection ≤ bound⟩

/-- Rejection probability is at least the bound throughout a declared
alternative. A single planning point is the alternative `(· = point)`. -/
def PolicyAnalysis.powerClaim (analysis : PolicyAnalysis policy)
    (alternative : Hypothesis Parameter) (bound : ℝ) : Claim :=
  ⟨∀ parameter, alternative parameter →
    bound ≤ (policy.law parameter).real analysis.rejection⟩

/-- Both planning components, kept as separate certificates. -/
structure OperatingCharacteristics (analysis : PolicyAnalysis policy)
    (alternative : Hypothesis Parameter) (typeI power : ℝ) : Prop where
  typeI : Certificate (analysis.typeIClaim typeI)
  power : Certificate (analysis.powerClaim alternative power)

variable {Outcome : Type v} [MeasurableSpace Outcome]

/-- Fixed sampling: the record is the model's outcome. -/
def Policy.fixed (model : Model Parameter Outcome) : Policy Parameter Outcome Outcome where
  potentialLaw := model.law
  probability := model.probability
  record := id
  record_measurable := measurable_id

theorem Policy.fixed_law (model : Model Parameter Outcome) (parameter : Parameter) :
    (Policy.fixed model).law parameter = model.law parameter :=
  Measure.map_id

/-- View a fixed-sample analysis as a policy analysis. -/
def PolicyAnalysis.ofFixed {model : Model Parameter Outcome}
    (analysis : Analysis.{u, v, w} model) : PolicyAnalysis (Policy.fixed model) where
  hypothesis := analysis.hypothesis
  rejection := analysis.procedure.rejectionEvent
  rejection_measurable := analysis.procedure.rejection_measurable

/-- Existing fixed-sample guarantees are policy guarantees. -/
theorem TypeIGuarantee.toPolicy {model : Model Parameter Outcome}
    {analysis : Analysis.{u, v, w} model} {bound : ℝ}
    (guarantee : TypeIGuarantee analysis bound) :
    ((PolicyAnalysis.ofFixed analysis).typeIClaim bound).statement := by
  intro parameter null
  have established := guarantee.certificate.establishes parameter null
  rw [guarantee.compatibility.agrees] at established
  rw [Policy.fixed_law]
  exact established

end StatProof.Core
