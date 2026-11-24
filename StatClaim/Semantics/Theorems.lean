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
  test := fun _ _ => TestInterface.neverRejects _
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

theorem Premise.trivial_holds (q : Premise) : q.Holds Instance.trivial := by
  cases q with
  | level name method model null alpha =>
    exact neverRejects_meets_level _ _ _ _ alpha.nonnegative
  | graph name members alpha =>
    refine ⟨?_, ?_⟩
    · cases members.all Test.finiteSample <;> exact Scope.permits_zero _
    · intro Θ Ω _ σ
      refine ForallViews.intro _ _ fun ws => Marginals.intro σ _ ws ?_
      exact familywise_of_nothing σ.law _ (by
        have := alpha.nonnegative
        simp only [Instance.trivial, add_zero]
        exact_mod_cast this)

/-- Every program's premises hold together, so no claim is vacuous. -/
theorem Program.satisfiable (p : Program) (uses : List ℕ) : p.Using Instance.trivial uses := by
  induction uses with
  | nil => trivial
  | cons k ks rest =>
    refine ⟨?_, rest⟩
    unfold Program.premiseAt
    cases p.premises[k]? with
    | none => trivial
    | some q => exact q.trivial_holds

end

end StatClaim.Semantics
