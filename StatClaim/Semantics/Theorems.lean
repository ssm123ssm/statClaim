module

public import StatClaim.Semantics.Meaning

/-!
What holds for every program, proved once. Not trusted: Lean checks these proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Interface

noncomputable section

/-- A one-point instance: trivial laws, tests and graphs that never reject, no slack. -/
noncomputable def Instance.trivial : Instance where
  laws := fun _ => { Parameter := Unit, Outcome := Unit, model := TwoArmModel.trivial }
  studies := fun _ => { Parameter := Unit, Outcome := Unit, model := ObservationalModel.trivial }
  test := fun _ _ => TestInterface.neverRejects _
  studyTest := fun _ _ => TestInterface.neverRejects _
  member := fun _ => ⟨⟨Unit, Unit, TwoArmModel.trivial⟩, fun _ => False,
    TestInterface.neverRejects _⟩
  slack := fun _ => 0
  graph := fun _ _ _ _ _ _ _ _ _ => ∅

theorem ForallViews.intro {Θ Ω : Type} [MeasurableSpace Ω] :
    ∀ (vs : List View) (body : Views Θ Ω vs → Prop), (∀ ws, body ws) → ForallViews Θ Ω vs body
  | [], _, h => h _
  | _ :: vs, body, h => fun w => ForallViews.intro vs (fun ws => body (w, ws)) (fun _ => h _)

theorem Marginals.intro {Θ Ω : Type} [MeasurableSpace Ω] (σ : JointStudy Θ Ω) :
    ∀ (vs : List View) (ws : Views Θ Ω vs) {claim : Prop}, claim → Marginals σ vs ws claim
  | [], _, _, h => h
  | _ :: vs, ws, _, h => fun _ => Marginals.intro σ vs ws.2 h

theorem Premise.trivial_holds_procedure (name : String) (rule : Generated.Procedure)
    (members : List Test) (alpha : SignificanceLevel) :
    (Premise.procedure name rule members alpha).Holds Instance.trivial := by
  refine ⟨Scope.permits_zero _, ?_⟩
  intro Θ Ω _ σ
  refine ForallViews.intro _ _ fun ws => Marginals.intro σ _ ws ?_
  exact familywise_of_nothing σ.law _ (by
    have := alpha.nonnegative
    simp only [Instance.trivial, add_zero]
    exact_mod_cast this)

theorem Premise.trivial_holds (q : Premise) : q.Holds Instance.trivial := by
  cases q with
  | level name method model null alpha =>
    exact neverRejects_meets_level _ _ _ _ alpha.nonnegative
  | association name method study alpha =>
    exact neverRejects_meets_level _ _ _ _ alpha.nonnegative
  | member name alpha =>
    exact neverRejects_meets_level _ _ _ _ alpha.nonnegative
  | procedure name rule members alpha =>
    exact Premise.trivial_holds_procedure name rule members alpha

theorem Premise.allHold_trivial : ∀ premises : List Premise, Premise.AllHold Instance.trivial premises
  | [] => trivial
  | q :: qs => ⟨q.trivial_holds, Premise.allHold_trivial qs⟩

/-- Every request's premises hold together, so no claim is vacuous. -/
theorem Program.satisfiable (p : Program) (r : ℕ) :
    Premise.AllHold Instance.trivial (p.premisesAt r) :=
  Premise.allHold_trivial _

/-- A request about a design that stops by a rule depending on the data is refuted: it
claims `False`, and its premises can all hold. -/
theorem Program.refuted (p : Program) (r : ℕ)
    (stops : (p.requests[r]?.map Request.fixed) = some false) : ¬ p.Claim r := by
  intro claim
  have holds := claim Instance.trivial (Program.satisfiable p r)
  unfold Program.claimAt at holds
  cases found : p.requests[r]? with
  | none => rw [found] at stops; cases stops
  | some q =>
    rw [found] at stops holds
    have fixed : q.fixed = false := Option.some.inj stops
    change q.Holds Instance.trivial at holds
    unfold Request.Holds at holds
    rw [fixed] at holds
    exact holds

def Program.checkProportionZCounterexample (program : Program) (r : ℕ) (rate reported : ℚ) : Bool :=
  match program.requests[r]? with
  | some (.typeI (.exact _ (.proportionZ pooled cutoff) design _ alpha)) =>
    let sizes := design.model.sizes
    decide (design.stopping = .fixed ∧ sizes.nTreatment = sizes.nControl) &&
      Modules.Wald.checkCounterexample sizes.nControl cutoff.num.toNat cutoff.den
        alpha.value rate reported (Modules.Wald.varianceAdjustment pooled cutoff.num.toNat)
  | _ => false

/-- A checked rational witness refutes the Type I claim of a fixed proportion test. -/
theorem Program.proportionZ_refuted (program : Program) (r : ℕ) (rate reported : ℚ)
    (valid : program.checkProportionZCounterexample r rate reported = true) :
    ¬ program.Claim r := by
  intro claim
  have holds := claim Instance.trivial (program.satisfiable r)
  unfold Program.checkProportionZCounterexample at valid
  split at valid
  next name pooled cutoff design null alpha found =>
    obtain ⟨compatible, checked⟩ := Bool.and_eq_true_iff.mp valid
    obtain ⟨stopping, balanced⟩ := of_decide_eq_true compatible
    obtain ⟨θ, equal, _, exactRate, excess⟩ := Modules.Wald.exact_at_of_check
      design.model.sizes balanced cutoff.num.toNat cutoff.den cutoff.den_pos
      alpha.value rate reported (Modules.Wald.varianceAdjustment pooled cutoff.num.toNat) checked
    unfold Program.claimAt at holds
    rw [found] at holds
    simp only [Request.Holds, Request.fixed, Request.test, Option.all_some, Test.fixed,
      stopping, beq_self_eq_true, Test.typeI, ExactKind.moduleSpec, ExactKind.input,
      ProportionZExact.moduleSpec, ProportionZExact.typeI, ProportionZExact.region] at holds
    exact (not_le_of_gt (exactRate ▸ excess)) (holds θ equal)
  next => contradiction

theorem Program.wald_refuted (program : Program) (r : ℕ) (rate reported : ℚ)
    (valid : program.checkProportionZCounterexample r rate reported = true) : ¬ program.Claim r :=
  program.proportionZ_refuted r rate reported valid

def Program.checkMcNemarCounterexample (program : Program) (r : ℕ) (rate reported : ℚ) : Bool :=
  match program.requests[r]? with
  | some (.typeI (.exactStudy _ (.matchedAsymptotic cutoff) design _ alpha)) =>
    decide (design.stopping = .fixed) &&
      AsymptoticMcNemar.checkCounterexample ⟨design.model.pairs.getD 0, alpha, cutoff⟩ rate reported
  | _ => false

theorem Program.mcnemarAsymptotic_refuted (program : Program) (r : ℕ) (rate reported : ℚ)
    (valid : program.checkMcNemarCounterexample r rate reported = true) : ¬ program.Claim r := by
  intro claim
  have holds := claim Instance.trivial (program.satisfiable r)
  unfold Program.checkMcNemarCounterexample at valid
  split at valid
  next name cutoff design null alpha found =>
    obtain ⟨compatible, checked⟩ := Bool.and_eq_true_iff.mp valid
    have stopping := of_decide_eq_true compatible
    unfold Program.claimAt at holds
    rw [found] at holds
    simp only [Request.Holds, Request.fixed, Request.test, Option.all_some, Test.fixed,
      stopping, beq_self_eq_true, Test.typeI, ExactStudyKind.moduleSpec, ExactStudyKind.input,
      AsymptoticMcNemar.moduleSpec] at holds
    exact AsymptoticMcNemar.counterexample _ rate reported checked holds
  next => contradiction

def Program.checkFarringtonManningCounterexample (program : Program) (r : ℕ)
    (rate reported : ℚ) (h : Modules.FarringtonManning.RegionHint) : Bool :=
  match program.requests[r]? with
  | some (.typeI (.exact _ (.farringtonManning margin cutoff) design _ alpha)) =>
    decide (design.stopping = .fixed) &&
      FarringtonManningExact.checkCounterexample ⟨design.model.sizes, alpha, margin, cutoff⟩
        h rate reported
  | _ => false

theorem Program.farringtonManning_refuted (program : Program) (r : ℕ) (rate reported : ℚ)
    (h : Modules.FarringtonManning.RegionHint)
    (valid : program.checkFarringtonManningCounterexample r rate reported h = true) :
    ¬ program.Claim r := by
  intro claim
  have holds := claim Instance.trivial (program.satisfiable r)
  unfold Program.checkFarringtonManningCounterexample at valid
  split at valid
  next name margin cutoff design null alpha found =>
    obtain ⟨compatible, checked⟩ := Bool.and_eq_true_iff.mp valid
    have stopping := of_decide_eq_true compatible
    unfold Program.claimAt at holds
    rw [found] at holds
    simp only [Request.Holds, Request.fixed, Request.test, Option.all_some, Test.fixed,
      stopping, beq_self_eq_true, Test.typeI, ExactKind.moduleSpec, ExactKind.input,
      FarringtonManningExact.moduleSpec] at holds
    exact FarringtonManningExact.counterexample _ h rate reported checked holds
  next => contradiction

def Program.checkOneSampleScoreCounterexample (p : Program) (r : ℕ) (rate reported : ℚ) : Bool :=
  match p.requests[r]? with
  | some (.typeI (.oneSampleScore _ n reference alpha cutoff)) =>
    OneSampleScoreExact.checkCounterexample ⟨n, reference, alpha, cutoff⟩ rate reported
  | _ => false

theorem Program.oneSampleScore_refuted (p : Program) (r : ℕ) (rate reported : ℚ)
    (checked : p.checkOneSampleScoreCounterexample r rate reported = true) : ¬ p.Claim r := by
  intro claim
  have holds := claim Instance.trivial (p.satisfiable r)
  unfold Program.checkOneSampleScoreCounterexample at checked
  split at checked
  next name n reference alpha cutoff found =>
    unfold Program.claimAt at holds
    rw [found] at holds
    exact OneSampleScoreExact.counterexample ⟨n, reference, alpha, cutoff⟩ rate reported checked holds
  next => contradiction

def Program.checkPearsonCounterexample (p : Program) (r : ℕ) (rate reported : ℚ) : Bool :=
  match p.requests[r]? with
  | some (.typeI (.exact _ (.pearson corrected cutoff) design _ alpha)) =>
    decide (design.stopping = .fixed) &&
      BinomialPolynomialExact.checkCounterexample ⟨design.model.sizes, alpha, cutoff, .pearson corrected⟩ rate reported
  | _ => false

theorem Program.pearson_refuted (p : Program) (r : ℕ) (rate reported : ℚ)
    (valid : p.checkPearsonCounterexample r rate reported = true) : ¬ p.Claim r := by
  intro claim
  have holds := claim Instance.trivial (p.satisfiable r)
  unfold Program.checkPearsonCounterexample at valid
  split at valid
  next name corrected cutoff design null alpha found =>
    obtain ⟨compatible, checked⟩ := Bool.and_eq_true_iff.mp valid
    have stopping := of_decide_eq_true compatible
    unfold Program.claimAt at holds
    rw [found] at holds
    simp only [Request.Holds, Request.fixed, Request.test, Option.all_some, Test.fixed,
      stopping, beq_self_eq_true, Test.typeI, ExactKind.moduleSpec, ExactKind.input,
      BinomialPolynomialExact.moduleSpec] at holds
    exact BinomialPolynomialExact.counterexample _ rate reported checked holds
  next => contradiction

def Program.checkLikelihoodRatioCounterexample (p : Program) (r : ℕ) (rate reported : ℚ) : Bool :=
  match p.requests[r]? with
  | some (.typeI (.exact _ (.likelihoodRatio cutoff) design _ alpha)) =>
    decide (design.stopping = .fixed) &&
      BinomialPolynomialExact.checkCounterexample ⟨design.model.sizes, alpha, cutoff, .likelihoodRatio⟩ rate reported
  | _ => false

theorem Program.likelihoodRatio_refuted (p : Program) (r : ℕ) (rate reported : ℚ)
    (valid : p.checkLikelihoodRatioCounterexample r rate reported = true) : ¬ p.Claim r := by
  intro claim
  have holds := claim Instance.trivial (p.satisfiable r)
  unfold Program.checkLikelihoodRatioCounterexample at valid
  split at valid
  next name cutoff design null alpha found =>
    obtain ⟨compatible, checked⟩ := Bool.and_eq_true_iff.mp valid
    have stopping := of_decide_eq_true compatible
    unfold Program.claimAt at holds
    rw [found] at holds
    simp only [Request.Holds, Request.fixed, Request.test, Option.all_some, Test.fixed,
      stopping, beq_self_eq_true, Test.typeI, ExactKind.moduleSpec, ExactKind.input,
      BinomialPolynomialExact.moduleSpec] at holds
    exact BinomialPolynomialExact.counterexample _ rate reported checked holds
  next => contradiction

end

end StatClaim.Semantics
