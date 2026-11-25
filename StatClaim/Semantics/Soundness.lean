module

public import StatClaim.Semantics.Meaning
public import StatClaim.Semantics.Contracts

/-!
Soundness, proved once for every program: when a program's contracts hold, each request
whose designs stop at fixed sizes holds for every instance meeting the premises of the
tests it involves (`Program.sound`). A certificate proves its claims with this theorem
and `decide +kernel` on the contracts, so it needs no proof of its own.

Not trusted: Lean checks these proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Interface

noncomputable section

variable {Θ Ω : Type} [MeasurableSpace Ω]

/-! ## Views and premises -/

/-- Each view's marginal is its model's law. -/
def AllMarginals (σ : JointStudy Θ Ω) : (vs : List View) → Views Θ Ω vs → Prop
  | [], _ => True
  | v :: vs, ws => ws.1.Marginal σ v.base.law ∧ AllMarginals σ vs ws.2

theorem forallViews_iff : ∀ (vs : List View) (body : Views Θ Ω vs → Prop),
    ForallViews Θ Ω vs body ↔ ∀ ws, body ws
  | [], _ => ⟨fun h _ => h, fun h => h _⟩
  | _ :: vs, body =>
    ⟨fun h ws => (forallViews_iff vs fun rest => body (ws.1, rest)).1 (h ws.1) ws.2,
      fun h w => (forallViews_iff vs fun rest => body (w, rest)).2 fun rest => h (w, rest)⟩

theorem marginals_iff (σ : JointStudy Θ Ω) :
    ∀ (vs : List View) (ws : Views Θ Ω vs) (claim : Prop),
      Marginals σ vs ws claim ↔ (AllMarginals σ vs ws → claim)
  | [], _, _ => ⟨fun h _ => h, fun h => h trivial⟩
  | _ :: vs, ws, claim => by
    simp only [Marginals, AllMarginals, marginals_iff σ vs ws.2 claim, and_imp]

theorem joint_iff (vs : List View)
    (claim : ∀ {Θ Ω : Type} [MeasurableSpace Ω], JointStudy Θ Ω → Views Θ Ω vs → Prop) :
    Joint vs claim ↔ ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : JointStudy Θ Ω)
      (ws : Views Θ Ω vs), AllMarginals σ vs ws → claim σ ws := by
  simp only [Joint, forallViews_iff, marginals_iff]

theorem AllMarginals.split (σ : JointStudy Θ Ω) :
    ∀ (a b : List View) (ws : Views Θ Ω (a ++ b)), AllMarginals σ (a ++ b) ws →
      AllMarginals σ a (Views.split a b ws).1 ∧ AllMarginals σ b (Views.split a b ws).2
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: a, b, ws, h =>
    have rest := AllMarginals.split σ a b ws.2 h.2
    ⟨⟨h.1, rest.1⟩, rest.2⟩

theorem Premise.allHold_append (i : Instance) :
    ∀ (a b : List Premise), Premise.AllHold i (a ++ b) ↔ Premise.AllHold i a ∧ Premise.AllHold i b
  | [], _ => by simp [Premise.AllHold]
  | _ :: a, b => by
    simp only [List.cons_append, Premise.AllHold, Premise.allHold_append i a b, and_assoc]

/-! ## Levels -/

/-- The members' levels, as a vector. -/
def Test.alphas : (ts : List Test) → Fin ts.length → ℚ
  | [] => ![]
  | t :: ts => Matrix.vecCons t.alpha (Test.alphas ts)

theorem Test.alpha_nonnegative (t : Test) : 0 ≤ t.alpha := by
  exact t.level.nonnegative

theorem Test.alphas_nonnegative : ∀ (ts : List Test) (k : Fin ts.length), 0 ≤ Test.alphas ts k
  | [], k => k.elim0
  | t :: ts, k => Fin.cases (by simpa [Test.alphas] using t.alpha_nonnegative)
      (fun k => by simpa [Test.alphas] using Test.alphas_nonnegative ts k) k

theorem Test.sum_alphas : ∀ ts : List Test, ∑ k, Test.alphas ts k = (ts.map Test.alpha).sum
  | [] => by simp [Test.alphas]
  | t :: ts => by simp [Test.alphas, Fin.sum_univ_succ, Test.sum_alphas ts]

theorem Test.alphas_eq (alpha : ℚ) :
    ∀ ts : List Test, ts.all (fun t => decide (t.alpha = alpha)) = true →
      ∀ k, Test.alphas ts k = alpha
  | [], _, k => k.elim0
  | t :: ts, h, k => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Fin.cases (by simpa [Test.alphas] using h.1)
      (fun k => by simpa [Test.alphas] using Test.alphas_eq alpha ts h.2 k) k

/-! ## Levels within budget -/

mutual
/-- The shares of every family and design with looks within a test add up to at most its
level. Python leaves a claim without this open, so the semantics proves only claims that
have it; a definition too permissive here would make the proofs below fail. -/
def Test.allocated : Test → Bool
  | .bonferroni _ members alpha _ =>
    decide ((members.map Test.alpha).sum ≤ alpha.value) && Test.allAllocated members
  | .looks _ members alpha =>
    decide ((members.map Test.alpha).sum ≤ alpha.value) && Test.allAllocated members
  | .graphical _ members _ _ _ => Test.allAllocated members
  | .sequence _ members _ => Test.allAllocated members
  | _ => true
termination_by structural t => t

def Test.allAllocated : List Test → Bool
  | [] => true
  | t :: ts => Test.allocated t && Test.allAllocated ts
termination_by structural ts => ts
end

/-! ## Exact checks -/

mutual
def Test.Hints : Test → Type
  | .exact _ kind .. => kind.moduleSpec.typeI.Hint
  | .exactStudy _ kind .. => kind.moduleSpec.typeI.Hint
  | .bonferroni _ members .. | .looks _ members .. | .sequence _ members .. => Test.MemberHints members
  | _ => PUnit
termination_by structural t => t

def Test.MemberHints : List Test → Type
  | [] => PUnit
  | t :: ts => t.Hints × Test.MemberHints ts
termination_by structural ts => ts
end

mutual
def Test.emptyHints : (t : Test) → t.Hints
  | .exact _ .fisherOneSided .. => []
  | .exact _ (.margin ..) .. => ⟨0, 0, 0, []⟩
  | .exactStudy _ .fisherGroups .. | .exactStudy _ .fisherMixture ..
  | .exactStudy _ .matched .. | .exactStudy _ .incidence .. => PUnit.unit
  | .bonferroni _ members .. | .looks _ members .. | .sequence _ members .. => Test.emptyMemberHints members
  | .fisher .. | .randomised .. | .member .. | .assumed .. | .associated .. | .graphical ..
  | .oneSample .. | .twoStage .. => PUnit.unit
termination_by structural t => t

def Test.emptyMemberHints : (ts : List Test) → Test.MemberHints ts
  | [] => PUnit.unit
  | t :: ts => (t.emptyHints, Test.emptyMemberHints ts)
termination_by structural ts => ts
end

mutual
def Test.checkHints : (t : Test) → t.Hints → Bool
  | .exact _ kind design _ alpha, hints =>
    kind.moduleSpec.typeI.check (kind.input design.model.sizes alpha) hints
  | .exactStudy _ kind design _ alpha, hints =>
    kind.moduleSpec.typeI.check (kind.input design.model alpha) hints
  | .bonferroni _ members .., hints | .looks _ members .., hints | .sequence _ members .., hints =>
    Test.checkMemberHints members hints
  | _, _ => true
termination_by structural t => t

def Test.checkMemberHints : (ts : List Test) → Test.MemberHints ts → Bool
  | [], _ => true
  | t :: ts, hints => t.checkHints hints.1 && Test.checkMemberHints ts hints.2
termination_by structural ts => ts
end

def Request.Hints : Request → Type
  | .typeI t | .familywise t => t.Hints
  | .result .. => OneSided.result.Hint
  | .checkedResult _ t d => (t.checkedResult d).Hint
  | .interval _ d => d.checked.Hint
  | .planned _ q target selected => (q.checked target selected).Hint

def Request.emptyHints : (q : Request) → q.Hints
  | .typeI t | .familywise t => t.emptyHints
  | .result .. => []
  | .checkedResult _ t d => (t.checkedResult d).empty
  | .interval _ d => d.checked.empty
  | .planned _ q target selected => (q.checked target selected).empty

def Request.checkHints : (q : Request) → q.Hints → Bool
  | .typeI t, h | .familywise t, h => t.checkHints h
  | .result _ (.exact _ .fisherOneSided design _ alpha) observed reported, h =>
    OneSided.result.check ((design.model.sizes, alpha), observed, reported) h
  | .checkedResult _ t d, h => (t.checkedResult d).check () h
  | .interval _ d, h => d.checked.check () h
  | .planned _ q target selected, h => (q.checked target selected).check () h
  | _, _ => false

/-! ## Every test, seen as a member -/

/-- A member's guarantee: its slack is nonnegative, and under its null it rejects with
probability at most its level plus its slack. -/
def Bound (σ : JointStudy Θ Ω) (o : Outside Θ Ω) (level : ℚ) : Prop :=
  0 ≤ o.slack ∧ ∀ θ, o.null θ → (σ.law θ).real o.reject ≤ level + o.slack

theorem fisher_bound (sizes : FixedSampleDesign) (alpha : SignificanceLevel)
    (σ : JointStudy Θ Ω)
    (view : MemberView Θ Ω (binomialView sizes).Parameter (binomialView sizes).Outcome)
    (marginal : view.Marginal σ (binomialView sizes).base.law) :
    ∀ θ, (fisherAnalysis sizes alpha).hypothesis (view.parameter θ) →
      (σ.law θ).real (view.outcome ⁻¹' (fisherAnalysis sizes alpha).procedure.rejectionEvent) ≤
        alpha.value := by
  have claim := Modules.Fisher.typeI_statement sizes
    (Core.StudyDesign.fixed (Modules.TwoArmBinomial.model sizes)) (Core.Compatibility.fixed _) alpha
  exact MemberView.bound view marginal (fisherAnalysis sizes alpha).procedure.rejection_measurable
    (model_bound (Core.Compatibility.fixed _) claim)

mutual
theorem Test.outside_bound (i : Instance) (σ : JointStudy Θ Ω) :
    ∀ (t : Test) (ws : Views Θ Ω (t.leaves i)), t.check = true → t.allocated = true →
      ∀ h : t.Hints, t.checkHints h = true →
      Premise.AllHold i t.premises → AllMarginals σ _ ws → Bound σ (t.outside i σ ws) t.alpha
  | .fisher _ design _ alpha, ws, _, _, _, _, _, marginals => by
    refine ⟨le_refl 0, fun θ holds => ?_⟩
    simpa [Test.outside, Test.alpha, Test.level] using
      fisher_bound design.model.sizes alpha σ ws.1 marginals.1 θ holds
  | .exact _ kind design _ alpha, ws, _, _, hints, checked, _, marginals => by
    let input := kind.input design.model.sizes alpha
    have level := kind.moduleSpec.typeI.sound input hints checked
    exact ⟨le_refl 0, fun θ holds => by
      change (σ.law θ).real (ws.1.outcome ⁻¹' (kind.moduleSpec.procedure input).reject) ≤
        (alpha.value : ℝ) + 0
      rw [← kind.input_level design.model.sizes alpha, add_zero]
      exact MemberView.bound ws.1 marginals.1 (kind.moduleSpec.procedure input).measurable
        (kind.moduleSpec.bound input level) θ holds⟩
  | .exactStudy _ kind design _ alpha, ws, _, _, hints, checked, _, marginals => by
    let input := kind.input design.model alpha
    have level := kind.moduleSpec.typeI.sound input hints checked
    exact ⟨le_refl 0, fun θ holds => by
      change (σ.law θ).real (ws.1.outcome ⁻¹' (kind.moduleSpec.procedure input).reject) ≤
        (alpha.value : ℝ) + 0
      rw [← kind.input_level design.model alpha, add_zero]
      exact MemberView.bound ws.1 marginals.1 (kind.moduleSpec.procedure input).measurable
        (kind.moduleSpec.bound input level) θ holds⟩
  | .randomised .., _, _, _, _, _, _, _ => ⟨le_refl 0, fun _ holds => holds.elim⟩
  | .oneSample .., _, _, _, _, _, _, _ | .twoStage .., _, _, _, _, _, _, _ =>
    ⟨le_refl 0, fun _ holds => holds.elim⟩
  | .member t, ws, _, _, _, _, premises, marginals => by
    have premise := premises.1
    exact ⟨Scope.permits_nonnegative premise.1,
      MemberView.bound ws.1 marginals.1 (i.member t.name).procedure.measurable premise.2⟩
  | .assumed name _ design _ alpha, ws, _, _, _, _, premises, marginals => by
    have premise := premises.1
    exact ⟨Scope.permits_nonnegative premise.1,
      MemberView.bound ws.1 marginals.1 (i.test name design.model).measurable premise.2⟩
  | .associated name _ design _ alpha _, ws, _, _, _, _, premises, marginals => by
    have premise := premises.1
    exact ⟨Scope.permits_nonnegative premise.1,
      MemberView.bound ws.1 marginals.1 (i.studyTest name design.model).measurable premise.2⟩
  | .bonferroni _ members alpha _, ws, contracts, allocated, hints, checked, premises, marginals => by
    simp only [Test.check, Bool.and_eq_true] at contracts
    simp only [Test.allocated, Bool.and_eq_true, decide_eq_true_eq] at allocated
    have each := Test.members_bound i σ members ws contracts.1 allocated.2 hints checked premises marginals
    have family := familywise_of_members σ _ _ (Test.alphas members) _
      (Test.alphas_nonnegative members) (fun k => (each k).1) (fun k => (each k).2) alpha.value
      (by rw [Test.sum_alphas]; exact allocated.1)
    exact ⟨(Finset.sum_nonneg fun k _ => (each k).1 :
      0 ≤ ∑ k, (Test.members i σ members ws).slacks k), family_member σ family⟩
  | .looks _ members alpha, ws, contracts, allocated, hints, checked, premises, marginals => by
    simp only [Test.check, Bool.and_eq_true] at contracts
    simp only [Test.allocated, Bool.and_eq_true, decide_eq_true_eq] at allocated
    have each := Test.members_bound i σ members ws contracts.1.1.1 allocated.2 hints checked premises marginals
    have family := familywise_of_members σ _ _ (Test.alphas members) _
      (Test.alphas_nonnegative members) (fun k => (each k).1) (fun k => (each k).2) alpha.value
      (by rw [Test.sum_alphas]; exact allocated.1)
    exact ⟨(Finset.sum_nonneg fun k _ => (each k).1 :
      0 ≤ ∑ k, (Test.members i σ members ws).slacks k), looks_member family⟩
  | .graphical name members _ _ alpha, ws, _, _, _, _, premises, marginals => by
    have graph := ((Premise.allHold_append i _ _).1 premises).2.1
    have family := (joint_iff _ _).1 graph.2 Θ Ω σ ws marginals
    exact ⟨Scope.permits_nonnegative graph.1, family_member σ family⟩
  | .sequence _ members alpha, ws, contracts, allocated, hints, checked, premises, marginals => by
    simp only [Test.check, Bool.and_eq_true] at contracts
    simp only [Test.allocated] at allocated
    have each := Test.members_bound i σ members ws contracts.1.1 allocated hints checked premises marginals
    have levels := Test.alphas_eq alpha.value members contracts.2
    have sequence := sequence_of_members σ _ _ alpha.value _ alpha.nonnegative
      (fun k => (each k).1) (fun k θ holds => by simpa [levels k] using (each k).2 θ holds)
    exact ⟨(Finset.sum_nonneg fun k _ => (each k).1 :
      0 ≤ ∑ k, (Test.members i σ members ws).slacks k), sequence_member σ sequence⟩
termination_by structural t => t

theorem Test.members_bound (i : Instance) (σ : JointStudy Θ Ω) :
    ∀ (ts : List Test) (ws : Views Θ Ω (Test.leavesOf i ts)), Test.checkAll ts = true →
      Test.allAllocated ts = true →
      ∀ h : Test.MemberHints ts, Test.checkMemberHints ts h = true →
      Premise.AllHold i (Test.premisesOf ts) → AllMarginals σ _ ws → ∀ k,
        0 ≤ (Test.members i σ ts ws).slacks k ∧ ∀ θ, (Test.members i σ ts ws).nulls k θ →
          (σ.law θ).real ((Test.members i σ ts ws).rejects k) ≤
            Test.alphas ts k + (Test.members i σ ts ws).slacks k
  | [], _, _, _, _, _, _, _, k => k.elim0
  | t :: ts, ws, contracts, allocated, hints, checked, premises, marginals, k => by
    simp only [Test.checkAll, Bool.and_eq_true] at contracts
    simp only [Test.allAllocated, Bool.and_eq_true] at allocated
    simp only [Test.checkMemberHints, Bool.and_eq_true] at checked
    have parts := (Premise.allHold_append i _ _).1 premises
    have split := AllMarginals.split σ _ _ ws marginals
    have head := Test.outside_bound i σ t _ contracts.1 allocated.1 hints.1 checked.1 parts.1 split.1
    have tail := Test.members_bound i σ ts _ contracts.2 allocated.2 hints.2 checked.2 parts.2 split.2
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa [Test.members, Test.alphas, Bound] using head
    · simpa [Test.members, Test.alphas] using tail k
termination_by structural ts => ts
end

/-! ## Requests and programs -/

/-- A family or a design with looks: the union bound over its members, at shares of the
level that add up to at most the whole. -/
theorem Test.union_sound (i : Instance) (members : List Test) (alpha : SignificanceLevel)
    (checked : Test.checkAll members = true) (inner : Test.allAllocated members = true)
    (allocation : (members.map Test.alpha).sum ≤ alpha.value)
    (hints : Test.MemberHints members) (valid : Test.checkMemberHints members hints = true)
    (premises : Premise.AllHold i (Test.premisesOf members)) : Test.union i members alpha := by
  unfold Test.union
  refine (joint_iff _ _).2 fun Θ Ω _ σ ws marginals => ?_
  have each := Test.members_bound i σ members ws checked inner hints valid premises marginals
  exact familywise_of_members σ _ _ (Test.alphas members) _ (Test.alphas_nonnegative members)
    (fun k => (each k).1) (fun k => (each k).2) alpha.value
    (by rw [Test.sum_alphas]; exact allocation)

def Request.allocated (q : Request) : Bool :=
  match q with
  | .planned _ _ _ selected => selected.isSome && q.test.all Test.allocated
  | _ => q.test.all Test.allocated

theorem Request.check_test {q : Request} (checked : q.check = true) : q.test.all Test.check = true := by
  cases q <;> simp only [Request.check, Request.test, Bool.and_eq_true, Option.all] at checked ⊢
  all_goals first | assumption | exact checked.2

theorem Request.sound (q : Request) (contracts : q.check = true) (fixed : q.fixed = true)
    (allocated : q.allocated = true) (hints : q.Hints) (valid : q.checkHints hints = true) (i : Instance)
    (premises : Premise.AllHold i q.premises) : q.Holds i := by
  have checked := Request.check_test contracts
  unfold Request.Holds
  rw [fixed]
  cases q with
  | typeI t =>
    cases t with
    | fisher _ design _ alpha =>
      exact Modules.Fisher.typeI_statement design.model.sizes _ (Core.Compatibility.fixed _) alpha
    | exact _ kind design _ alpha =>
      exact kind.moduleSpec.typeI.sound (kind.input design.model.sizes alpha) hints valid
    | exactStudy _ kind design _ alpha =>
      exact kind.moduleSpec.typeI.sound (kind.input design.model alpha) hints valid
    | randomised _ r => exact Randomised.typeI.sound r hints valid
    | assumed name guarantee design null alpha =>
      have premise := premises.1
      simp only [Test.typeI]
      split
      · next finite => exact typeI_of_finite_premise _ finite premise
      · exact typeI_of_premise _ premise
    | associated name method design null alpha adjusted =>
      have premise := premises.1
      simp only [Test.typeI]
      split
      · next finite => exact typeI_of_finite_premise _ finite premise
      · exact typeI_of_premise _ premise
    | looks _ members alpha =>
      simp only [Request.test, Option.all, Test.check, Bool.and_eq_true] at checked
      simp only [Request.allocated, Request.test, Option.all, Test.allocated, Bool.and_eq_true,
        decide_eq_true_eq] at allocated
      exact Test.union_sound i members alpha checked.1.1.1 allocated.2 allocated.1 hints valid premises
    | _ => simp [Request.check, Test.hasTypeI, Test.single, Test.isLooks] at contracts
  | familywise t =>
    cases t with
    | bonferroni _ members alpha _ =>
      simp only [Request.test, Option.all, Test.check, Bool.and_eq_true] at checked
      simp only [Request.allocated, Request.test, Option.all, Test.allocated, Bool.and_eq_true,
        decide_eq_true_eq] at allocated
      exact Test.union_sound i members alpha checked.1 allocated.2 allocated.1 hints valid premises
    | graphical name members _ _ alpha =>
      exact ((Premise.allHold_append i _ _).1 premises).2.1.2
    | sequence _ members alpha =>
      simp only [Request.test, Option.all, Test.check, Bool.and_eq_true] at checked
      simp only [Request.allocated, Request.test, Option.all, Test.allocated] at allocated
      refine (joint_iff _ _).2 fun Θ Ω _ σ ws marginals => ?_
      have each := Test.members_bound i σ members ws checked.1.1 allocated hints valid premises marginals
      have levels := Test.alphas_eq alpha.value members checked.2
      exact sequence_of_members σ _ _ alpha.value _ alpha.nonnegative
        (fun k => (each k).1) (fun k θ holds => by simpa [levels k] using (each k).2 θ holds)
    | _ => simp [Request.check, Test.single, Test.isLooks] at contracts
  | result _ t observed reported =>
    cases t with
    | exact _ kind design _ alpha =>
      cases kind with
      | fisherOneSided =>
        exact OneSided.result.sound ((design.model.sizes, alpha), observed, reported) hints valid
      | margin => simp [Request.check, Test.isOneSidedFisher] at contracts
    | _ => simp [Request.check, Test.isOneSidedFisher] at contracts
  | checkedResult _ t d => exact (t.checkedResult d).sound () hints valid
  | interval _ d => exact d.checked.sound () hints valid
  | planned _ q target selected => exact (q.checked target selected).sound () hints valid
/-- Whether request `r` exists, every design it involves stops at fixed sizes, and its
levels are within budget: what Python requires before a claim can be proved. -/
def Program.readyAt (p : Program) (r : ℕ) : Bool :=
  match p.requests[r]? with
  | some q => q.fixed && q.allocated
  | none => false

def Program.Hints (p : Program) (r : ℕ) : Type :=
  p.requests[r]?.elim PUnit Request.Hints

def Request.emptyHintsOf : (entry : Option Request) → entry.elim PUnit Request.Hints
  | some q => q.emptyHints
  | none => PUnit.unit

def Request.checkHintsOf : (entry : Option Request) → entry.elim PUnit Request.Hints → Bool
  | some q => q.checkHints
  | none => fun _ => false

def Program.emptyHints (p : Program) (r : ℕ) : p.Hints r :=
  Request.emptyHintsOf p.requests[r]?

def Program.checkAt (p : Program) (r : ℕ) : p.Hints r → Bool :=
  Request.checkHintsOf p.requests[r]?

/-- Soundness: when the contracts hold, every request whose designs stop at fixed sizes and
whose levels are within budget follows from the premises of the tests it involves. -/
theorem Program.sound (p : Program) (contracts : p.Contracts) (r : ℕ)
    (ready : p.readyAt r = true) (hints : p.Hints r := p.emptyHints r)
    (valid : p.checkAt r hints = true := by decide +kernel) :
    p.Claim r := by
  have sound (entry : Option Request) (found : p.requests[r]? = entry)
      (h : entry.elim PUnit Request.Hints) (ok : Request.checkHintsOf entry h = true) : p.Claim r := by
    intro i premises
    unfold Program.claimAt
    unfold Program.premisesAt at premises
    unfold Program.readyAt at ready
    cases entry with
    | none => simp [found] at ready
    | some q =>
      simp only [found, Bool.and_eq_true] at premises ready ⊢
      have member : q ∈ p.requests := List.mem_of_getElem? found
      have requests : p.requests.all Request.check = true := by
        unfold Program.Contracts at contracts
        simp only [Bool.and_eq_true] at contracts
        exact contracts.2
      have checked : q.check = true := List.all_eq_true.1 requests q member
      exact Request.sound q checked ready.1 ready.2 h ok i premises
  exact sound _ rfl hints valid

end

end StatClaim.Semantics
