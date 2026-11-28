module

public import StatClaim.Semantics.Encode

/-!
# The canonical form determines the program

Not trusted: Lean checks these proofs.

The audit compares the form a build prints (`Program.form`, `Encode.lean`) with the
certificate's canonical program. That binds a certificate to its program only if two
different programs never print the same form. `Program.form_injective` proves it for
programs in canonical form.

Some fields of the data are not printed because the printed ones determine them: hints
that Lean checks (the level a p-value is compared with, a share computed from times or
odds, the margin of a test on a grid), the member wrapper of an exact test in a
conditional combination, the name of a result's or plan's test, and which registry
entry a cited method is. `Program.Canonical` requires each one to be the value the
printed fields give, and every certificate decides it for its program (`canonical`).
Neither the definition of `Canonical` nor these proofs need review: if `Canonical` said
too little, `form_injective` would not hold.

A form becomes JSON text by Lean's printer, which refuses an object whose keys do not
increase; two different forms whose objects all have increasing keys are different JSON
values, and the audit compares JSON values with types (`true` is not `1`).
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

/-! ## Printing rationals -/

theorem digits_isDigit (n : ℕ) : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true :=
  fun _ h => Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem digits_inj {a b : ℕ} (h : Nat.toDigits 10 a = Nat.toDigits 10 b) : a = b := by
  have := congrArg (fun l => Nat.ofDigitChars 10 l 0) h
  simpa [Nat.ofDigitChars_toDigits] using this

/-- An integer's characters: a minus sign when negative, then its digits. -/
def intChars (z : ℤ) : List Char :=
  (if z < 0 then ['-'] else []) ++ Nat.toDigits 10 z.natAbs

theorem repr_int_toList (z : ℤ) : z.repr.toList = intChars z := by
  rw [Int.repr_eq_ite]
  unfold intChars
  by_cases h : 0 ≤ z
  · have h' : ¬ z < 0 := by omega
    have e : z.toNat = z.natAbs := by omega
    simp [h, h', e]
  · have h' : z < 0 := by omega
    have e : (-z).toNat = z.natAbs := by omega
    simp [h, h', e, String.toList_append]

theorem intChars_no_slash (z : ℤ) : '/' ∉ intChars z := by
  intro h
  simp only [intChars, List.mem_append] at h
  rcases h with h | h
  · split_ifs at h <;> simp_all
  · have := digits_isDigit _ _ h; revert this; decide

theorem intChars_inj {a b : ℤ} (h : intChars a = intChars b) : a = b := by
  have sign : ∀ z : ℤ, (intChars z).head? = some '-' ↔ z < 0 := by
    intro z
    unfold intChars
    split_ifs with neg
    · simp [neg]
    · simp only [List.nil_append, neg, iff_false]
      intro head
      have := digits_isDigit z.natAbs '-' (List.mem_of_head? head)
      revert this; decide
  have signs : a < 0 ↔ b < 0 := by rw [← sign, ← sign, h]
  unfold intChars at h
  have abs : a.natAbs = b.natAbs := by
    apply digits_inj
    split_ifs at h <;> simp_all
  omega

theorem takeWhile_intChars (z : ℤ) (rest : List Char) (h : ∀ c ∈ rest.head?, c = '/') :
    (intChars z ++ rest).takeWhile (· ≠ '/') = intChars z := by
  rw [List.takeWhile_append_of_pos]
  · cases rest with
    | nil => simp
    | cons c rest => simp_all
  · intro c mem
    have := intChars_no_slash z
    simp only [ne_eq, decide_eq_true_eq]
    rintro rfl
    exact this mem

/-- Rationals print as different strings. -/
theorem ratString_injective : Function.Injective ratString := by
  intro a b h
  have chars := congrArg String.toList h
  have parts : ∀ q : ℚ, (ratString q).toList =
      intChars q.num ++ (if q.den = 1 then [] else '/' :: Nat.toDigits 10 q.den) := by
    intro q
    unfold ratString
    split_ifs <;> simp [String.toList_append, repr_int_toList]
  rw [parts, parts] at chars
  have nums : a.num = b.num := by
    apply intChars_inj
    have := congrArg (List.takeWhile (· ≠ '/')) chars
    rwa [takeWhile_intChars, takeWhile_intChars] at this <;> split_ifs <;> simp
  rw [nums] at chars
  have rest := List.append_cancel_left chars
  have dens : a.den = b.den := by
    by_cases h₁ : a.den = 1 <;> by_cases h₂ : b.den = 1 <;>
      simp only [h₁, h₂, ite_true, ite_false] at rest
    · omega
    · simp at rest
    · simp at rest
    · exact digits_inj (List.cons.inj rest).2
  exact Rat.ext nums dens

theorem allocationString_injective {a b : ℕ} (h : allocationString a = allocationString b) :
    a = b := by
  unfold allocationString at h
  split_ifs at h with ha hb hb
  · omega
  · have := congrArg String.toList h; simp [String.toList_append] at this
  · have := congrArg String.toList h; simp [String.toList_append] at this
  · have := congrArg String.toList h
    simp [String.toList_append] at this
    exact digits_inj this

/-! ## Values -/

theorem ProbabilityFraction.ext_value {p q : ProbabilityFraction} (h : p.value = q.value) :
    p = q := by
  obtain ⟨pn, pd, _, hp, rp⟩ := p
  obtain ⟨qn, qd, _, hq, rq⟩ := q
  have := Rat.div_int_inj (a := pn) (b := pd) (c := qn) (d := qd) (by exact_mod_cast hp)
    (by exact_mod_cast hq) (by simpa using rp) (by simpa using rq)
    (by simp only [ProbabilityFraction.value] at h; push_cast; exact h)
  simp only [Nat.cast_inj] at this
  obtain ⟨rfl, rfl⟩ := this
  rfl

theorem SignificanceLevel.ext_value {a b : SignificanceLevel} (h : a.value = b.value) : a = b := by
  cases a; cases b; simp_all

theorem FixedSampleDesign.ext_sizes {a b : FixedSampleDesign} (h₁ : a.nControl = b.nControl)
    (h₂ : a.nTreatment = b.nTreatment) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem Form.rat_inj {a b : ℚ} : Form.rat a = Form.rat b ↔ a = b :=
  ⟨fun h => ratString_injective (Form.str.inj h), (· ▸ rfl)⟩

@[simp] theorem Form.prob_inj {a b : ProbabilityFraction} : Form.prob a = Form.prob b ↔ a = b :=
  ⟨fun h => ProbabilityFraction.ext_value (Form.rat_inj.1 h), (· ▸ rfl)⟩

@[simp] theorem Form.level_inj {a b : SignificanceLevel} : Form.level a = Form.level b ↔ a = b :=
  ⟨fun h => SignificanceLevel.ext_value (Form.rat_inj.1 h), (· ▸ rfl)⟩

theorem option_map_inj {α : Type} {f : α → Form} (hf : ∀ a b, f a = f b → a = b)
    {a b : Option α} : a.map f = b.map f ↔ a = b :=
  (Option.map_injective (fun a b h => hf a b h)).eq_iff

theorem list_map_inj {α : Type} {f : α → Form} (hf : ∀ a b, f a = f b → a = b)
    {a b : List α} : a.map f = b.map f ↔ a = b :=
  (List.map_injective_iff.2 (fun a b h => hf a b h)).eq_iff

@[simp] theorem map_str {a b : Option String} : a.map Form.str = b.map Form.str ↔ a = b :=
  option_map_inj fun _ _ h => Form.str.inj h

@[simp] theorem map_nat {a b : Option ℕ} : a.map Form.nat = b.map Form.nat ↔ a = b :=
  option_map_inj fun _ _ h => Form.nat.inj h

@[simp] theorem map_rat {a b : Option ℚ} : a.map Form.rat = b.map Form.rat ↔ a = b :=
  option_map_inj fun _ _ h => Form.rat_inj.1 h

@[simp] theorem map_prob {a b : Option ProbabilityFraction} :
    a.map Form.prob = b.map Form.prob ↔ a = b :=
  option_map_inj fun _ _ h => Form.prob_inj.1 h

@[simp] theorem list_str {a b : List String} : a.map Form.str = b.map Form.str ↔ a = b :=
  list_map_inj fun _ _ h => Form.str.inj h

@[simp] theorem list_nat {a b : List ℕ} : a.map Form.nat = b.map Form.nat ↔ a = b :=
  list_map_inj fun _ _ h => Form.nat.inj h

@[simp] theorem list_rat {a b : List ℚ} : a.map Form.rat = b.map Form.rat ↔ a = b :=
  list_map_inj fun _ _ h => Form.rat_inj.1 h

@[simp] theorem list_rows {a b : List (List ℚ)} :
    a.map (fun row => Form.arr (row.map .rat)) = b.map (fun row => Form.arr (row.map .rat)) ↔
      a = b :=
  list_map_inj fun _ _ h => list_rat.1 (Form.arr.inj h)

/-! ## Objects -/

/-- The first value an object's entries give a key. -/
def firstSome (key : String) : List (String × Option Form) → Option Form
  | [] => none
  | (k, v) :: rest => if k = key then v.or (firstSome key rest) else firstSome key rest

def findField (key : String) : List (String × Form) → Option Form
  | [] => none
  | (k, v) :: rest => if k = key then some v else findField key rest

/-- The value an object gives a key. -/
def Form.get (key : String) : Form → Option Form
  | .obj fields => findField key fields
  | _ => none

@[simp] theorem get_object (key : String) (e : List (String × Option Form)) :
    (Form.object e).get key = firstSome key e := by
  induction e with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨k, v⟩ := head
    cases v <;> simp_all [Form.object, Form.get, firstSome, findField]

@[simp] theorem firstSome_nil (key : String) : firstSome key [] = none := rfl

@[simp] theorem firstSome_cons (key k : String) (v : Option Form) (rest) :
    firstSome key ((k, v) :: rest) =
      if k = key then v.or (firstSome key rest) else firstSome key rest := rfl

/-- Equal objects with the same keys, in an order without repeats, have equal entries. -/
theorem object_inj {e₁ e₂ : List (String × Option Form)}
    (keys : e₁.map Prod.fst = e₂.map Prod.fst) (nodup : (e₁.map Prod.fst).Nodup)
    (h : Form.object e₁ = Form.object e₂) : e₁.map Prod.snd = e₂.map Prod.snd := by
  induction e₁ generalizing e₂ with
  | nil => cases e₂ <;> simp_all
  | cons head rest ih =>
    obtain ⟨k, v⟩ := head
    cases e₂ with
    | nil => simp at keys
    | cons head₂ rest₂ =>
      obtain ⟨k₂, w⟩ := head₂
      simp only [List.map_cons, List.cons.injEq] at keys nodup ⊢
      obtain ⟨rfl, keys⟩ := keys
      simp only [List.nodup_cons] at nodup
      have absent : ∀ (l : List (String × Option Form)) (x : Form),
          l.map Prod.fst = rest.map Prod.fst →
          (k, x) ∉ l.filterMap (fun (key, value) => value.map (key, ·)) := by
        intro l x same mem
        simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at mem
        obtain ⟨⟨k', v'⟩, mem', _, _, rfl, rfl⟩ := mem
        exact nodup.1 (same ▸ List.mem_map_of_mem (f := Prod.fst) mem')
      cases v <;> cases w <;>
        simp only [Form.object, List.filterMap_cons, Option.map_none, Option.map_some,
          Form.obj.injEq, List.cons.injEq, Prod.mk.injEq, true_and] at h ⊢
      · exact ih keys nodup.2 (by simpa [Form.object] using h)
      · exact absurd (h ▸ List.mem_cons_self) (absent _ _ rfl)
      · exact absurd (h ▸ List.mem_cons_self) (absent _ _ keys.symm)
      · exact ⟨congrArg some h.1, ih keys nodup.2 (by simpa [Form.object] using h.2)⟩

/-- Equal objects written with the same literal keys: their entries, as equations. -/
syntax "same_object " ident " as " ident : tactic
macro_rules
  | `(tactic| same_object $h as $entries) => `(tactic| (
      have $entries:ident := object_inj (h := $h) (keys := ?keys) (nodup := ?nodup)
      case keys => rfl
      case nodup => simp only [List.map_cons, List.map_nil]; decide
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true,
        Option.some.injEq] at $entries:ident))

/-- Two objects that give a key different values. -/
syntax "separate " ident " [" str,* "]" : tactic
macro_rules
  | `(tactic| separate $h [$keys,*]) => do
    let tactics ← keys.getElems.mapM fun key =>
      `(tactic| (have seen := congrArg (Form.get $key) $h; simp at seen; done))
    `(tactic| first $[| $tactics:tactic]*)

/-! ## Records -/

theorem Generated.OutcomeKind.constructor_inj {a b : Generated.OutcomeKind}
    (h : a.constructor = b.constructor) : a = b := by
  cases a <;> cases b <;> simp_all [Generated.OutcomeKind.constructor]

theorem Generated.NullKey.key_inj {a b : Generated.NullKey} (h : a.key = b.key) : a = b := by
  cases a <;> cases b <;> simp_all [Generated.NullKey.key]

theorem Generated.ObservationalDesign.key_inj {a b : Generated.ObservationalDesign}
    (h : a.key = b.key) : a = b := by
  cases a <;> cases b <;> simp_all [Generated.ObservationalDesign.key]

theorem Generated.Scale.key_inj {a b : Generated.Scale} (h : a.key = b.key) : a = b := by
  cases a <;> cases b <;> simp_all [Generated.Scale.key]

theorem Generated.Survey.key_inj {a b : Generated.Survey} (h : a.key = b.key) : a = b := by
  cases a <;> cases b <;> simp_all [Generated.Survey.key]

@[simp] theorem strata_inj {a b : List (ℕ × ℕ)} :
    a.map (fun x => Form.arr [.nat x.1, .nat x.2]) =
      b.map (fun x => Form.arr [.nat x.1, .nat x.2]) ↔ a = b :=
  (List.map_injective_iff.2 (fun x y h => by
    simp only [Form.arr.injEq, List.cons.injEq, Form.nat.injEq, and_true] at h
    exact Prod.ext h.1 h.2)).eq_iff

theorem pairs_inj {a b : Option (ℕ × ℕ)}
    (h₁ : a.map (fun x => Form.nat x.1) = b.map (fun x => Form.nat x.1))
    (h₂ : a.map (fun x => Form.nat x.2) = b.map (fun x => Form.nat x.2)) : a = b := by
  cases a <;> cases b <;> simp_all [Prod.ext_iff]

@[simp] theorem Model.form_inj {a b : Model} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold Model.form at h
  same_object h as entries
  obtain ⟨o, ⟨c, t, _, _⟩, cl, r, st, bs, p, be, m, n⟩ := a
  obtain ⟨o', ⟨c', t', _, _⟩, cl', r', st', bs', p', be', m', n'⟩ := b
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := entries
  simp only [map_str, map_nat, Form.str.injEq, Form.nat.injEq] at *
  have := Generated.OutcomeKind.constructor_inj h6
  have := pairs_inj h3 h4
  have : st = st' := by
    by_cases e : st = [] <;> by_cases e' : st' = [] <;>
      simp_all [List.isEmpty_iff]
  subst_vars
  rfl

@[simp] theorem Study.form_inj {a b : Study} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold Study.form at h
  same_object h as entries
  obtain ⟨d, n, ca, co, e, u, p, x, o, xs, os, s, cl⟩ := a
  obtain ⟨d', n', ca', co', e', u', p', x', o', xs', os', s', cl'⟩ := b
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := entries
  simp only [map_nat, Form.str.injEq] at *
  have := Generated.ObservationalDesign.key_inj h11
  have : xs = xs' := by
    cases xs <;> cases xs' <;> simp_all [Generated.Scale.key]
  have : os = os' := by
    cases os <;> cases os' <;> simp_all [Generated.Scale.key]
  have : s = s' := by
    cases s <;> cases s' <;> simp_all [Generated.Survey.key]
  subst_vars
  rfl

@[simp] theorem Stopping.form_inj {a b : Stopping} : a.form = b.form ↔ a = b := by
  cases a <;> cases b <;> simp [Stopping.form]

@[simp] theorem Design.form_inj {a b : Design} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold Design.form at h
  same_object h as entries
  cases a; cases b
  simp_all

@[simp] theorem StudyDesign.form_inj {a b : StudyDesign} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold StudyDesign.form at h
  same_object h as entries
  cases a; cases b
  simp_all

@[simp] theorem StudyNull.form_inj {a b : StudyNull} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold StudyNull.form at h
  same_object h as entries
  cases a; cases b
  simp_all

@[simp] theorem Null.form_inj {a b : Null} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold Null.form at h
  same_object h as entries
  obtain ⟨k, m, v⟩ := a
  obtain ⟨k', m', v'⟩ := b
  simp only [Model.form_inj, Form.str.injEq, map_rat] at entries
  obtain ⟨rfl, hk, rfl⟩ := entries
  rw [Generated.NullKey.key_inj hk]

@[simp] theorem scopeForm_inj {a b : Interface.Scope} : scopeForm a = scopeForm b ↔ a = b := by
  cases a <;> cases b <;> simp [scopeForm]

@[simp] theorem Stages.form_inj {a b : Stages} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold Stages.form at h
  same_object h as entries
  cases a; cases b
  simp_all

@[simp] theorem StageRule.form_inj {a b : StageRule} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  cases a <;> cases b <;> simp only [StageRule.form] at h
  · same_object h as entries; simp_all
  · separate h ["kind"]
  · separate h ["kind"]
  · same_object h as entries; simp_all

@[simp] theorem oneArmForm_inj {a b : ℕ} : oneArmForm a = oneArmForm b ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold oneArmForm at h
  same_object h as entries
  simp_all

/-! ## Canonical programs -/

deriving instance DecidableEq for Generated.TrialMethod
deriving instance DecidableEq for Generated.AssociationMethod

/-- The tests a conditional combination assumes as members, wrapped in `Test.member`. -/
def Test.isExactMember : Test → Bool
  | .exact .. | .exactStudy .. | .randomised .. => true
  | _ => false

/-- Whether an exact test of association is the one for its study: fixed groups when the
study is a case-control study or fixes both exposure groups. -/
def ExactStudyKind.matchesStudy (kind : ExactStudyKind) (study : Study) : Bool :=
  let groups := study.design == .case_control || (study.exposed.isSome && study.unexposed.isSome)
  match kind with
  | .fisherGroups => groups
  | .fisherMixture => !groups
  | _ => true

mutual
/-- A test in canonical form: the margin its kind records is its null's, its exact test
of association is the one for its study, a cited method is a registry entry, and the
members of a conditional combination are wrapped exactly when they are exact. -/
def Test.canonical : Test → Bool
  | .exact _ (.margin margin _) _ null _
  | .exact _ (.farringtonManning margin _) _ null _ => null.value == some margin
  | .exactStudy _ kind design .. => kind.matchesStudy design.model
  | .member _ => false
  | .assumed _ (.cited method) .. => Generated.trialMethods.contains method
  | .associated _ method .. => Generated.associationMethods.contains method
  | .bonferroni _ members _ none | .looks _ members _ | .sequence _ members _ =>
    Test.canonicalMembers true members
  | .procedure _ rule members _ weights rows =>
    Test.canonicalMembers true members && (rule.graph || (weights.isEmpty && rows.isEmpty))
  | .bonferroni _ members _ (some _) => Test.canonicalMembers false members
  | _ => true
termination_by structural t => t

def Test.canonicalMembers (conditional : Bool) : List Test → Bool
  | [] => true
  | .member t :: ts => conditional && t.isExactMember && Test.canonical t &&
      Test.canonicalMembers conditional ts
  | t :: ts => !(conditional && t.isExactMember) && Test.canonical t &&
      Test.canonicalMembers conditional ts
termination_by structural ts => ts
end

/-- A result's hints are the values its test and data give. -/
def ResultData.fits (t : Test) : ResultData → Bool
  | .fisher _ _ _ _ bound => bound.value == t.alpha
  | .margin _ _ bound gridded => bound.value == t.alpha &&
      (match t with
      | .exact _ (.margin value _) .. => gridded == value
      | _ => false)
  | .rate events share _ => share.value == events.share
  | _ => true

/-- The keys of a study's planning point, as the canonical program names them. -/
def associationKeys : List (String × String) :=
  [("risk_unexposed", "risk_exposed"), ("prevalence_unexposed", "prevalence_exposed"),
    ("exposure_controls", "exposure_cases")]

def PlanningPoint.canonical : PlanningPoint → Bool
  | .association first second .. => associationKeys.contains (first, second)
  | .matched _ odds caseShare => caseShare.value == odds / (1 + odds)
  | .rate ratio exposedTime unexposedTime _ nullShare alternativeShare =>
    nullShare.value == exposedTime / (exposedTime + unexposedTime) &&
      alternativeShare.value == ratio * exposedTime / (ratio * exposedTime + unexposedTime)
  | _ => true

def Test.isOneSample : Test → Bool
  | .oneSample .. => true
  | _ => false

/-- A search's kind and range as the canonical program gives them: only searches of arms
and groups have a ratio, and a search of one arm is about a one-sample test. -/
def SearchKind.fits (kind : SearchKind) (t : Test) (range : SearchRange) : Bool :=
  match kind with
  | .arms | .groups => true
  | .oneSample => range.ratio == 1 && t.isOneSample
  | .total => range.ratio == 1 && !t.isOneSample
  | .pairs | .events => range.ratio == 1

/-- A request in canonical form: its test is named as the request and is canonical, and
its hints are the values its data gives. -/
def Request.canonical : Request → Bool
  | .typeI t | .familywise t => t.canonical
  | .result name t .. => t.name == name && t.canonical
  | .checkedResult name t data => t.name == name && t.canonical && data.fits t
  | .interval .. => true
  | .planned name (.meets t) target _ => t.name == name && t.canonical && target.point.canonical
  | .planned name (.search t kind range) target _ =>
    t.name == name && t.canonical && kind.fits t range && target.point.canonical
  | .planned _ (.stageSearch ..) target _ => target.point.canonical

/-- A program in canonical form: every request and declaration is. Certificates decide
it for their program. -/
def Program.Canonical (p : Program) : Prop :=
  (p.requests.all Request.canonical && p.declarations.all Test.canonical) = true

instance (p : Program) : Decidable p.Canonical :=
  inferInstanceAs (Decidable (_ = true))

/-! ## Tests -/

/-- Registry facts: the key of a cited method names one entry, and no cited method has
the key of another kind of test. -/
theorem trial_key_inj : ∀ m₁ ∈ Generated.trialMethods, ∀ m₂ ∈ Generated.trialMethods,
    m₁.key = m₂.key → m₁ = m₂ := by decide +kernel

theorem association_key_inj : ∀ m₁ ∈ Generated.associationMethods,
    ∀ m₂ ∈ Generated.associationMethods, m₁.key = m₂.key → m₁ = m₂ := by decide +kernel

/-- The keys of the tests a canonical program writes by name, other than cited ones. -/
def reservedKeys : List String :=
  ["fisher", "wald_test", "score_test", "pearson_test", "farrington_manning", "fisher_exact",
    "mcnemar", "mcnemar_asymptotic", "rate_test", "randomisation",
    "binomial_exact_one_sided", "binomial_score_test", "two_stage", "declared_test"]

def trialKeys : List String := Generated.trialMethods.map (·.key)

theorem trial_key_free : ∀ m ∈ Generated.trialMethods, m.key ∉ reservedKeys := by decide +kernel

theorem association_key_free : ∀ m ∈ Generated.associationMethods,
    m.key ∉ reservedKeys ∧ m.key ∉ trialKeys := by decide +kernel

/-! ## Cited procedures -/

/-- The value a cited procedure's constant entries give a key. -/
def _root_.StatClaim.Generated.Procedure.field (rule : Generated.Procedure) (key : String) : Option String :=
  (rule.fields.find? (·.1 == key)).map (·.2)

/-- Every key a cited procedure writes, and every method one names. -/
def procedureKeys : List String := Generated.procedures.flatMap fun r => r.fields.map (·.1)

def procedureMethods : List String := Generated.procedures.filterMap (·.field "method")

/-- The keys a combination writes itself, and the key of a single test. -/
def combinationKeys : List String :=
  ["alpha", "analyses", "composition", "test", "transitions", "weights"]

theorem procedure_listed (rule : Generated.Procedure) : rule ∈ Generated.procedures := by
  cases rule <;> decide

/-- Registry facts: a procedure's entries tell it from every other, never repeat a key, and
never use a key the combination writes itself; no procedure names a proved combination. -/
theorem procedure_determined : ∀ r₁ ∈ Generated.procedures, ∀ r₂ ∈ Generated.procedures,
    (∀ key ∈ procedureKeys, r₁.field key = r₂.field key) → r₁ = r₂ := by decide +kernel

theorem procedure_keys_nodup : ∀ r ∈ Generated.procedures,
    (["alpha", "analyses", "composition"] ++ r.fields.map (·.1) ++
      ["transitions", "weights"]).Nodup := by decide +kernel

theorem procedure_keys_outside : ∀ key ∈ procedureKeys, key ∉ combinationKeys := by
  decide +kernel

theorem procedure_methods_free :
    "bonferroni" ∉ procedureMethods ∧ "alpha_spending" ∉ procedureMethods ∧
      "fixed_sequence" ∉ procedureMethods := by decide +kernel

theorem firstSome_append (key : String) : ∀ a b : List (String × Option Form),
    firstSome key (a ++ b) = (firstSome key a).or (firstSome key b)
  | [], b => by simp
  | (k, v) :: rest, b => by
    simp only [List.cons_append, firstSome_cons, firstSome_append key rest b]
    split <;> simp [Option.or_assoc]

theorem firstSome_entries (key : String) (rule : Generated.Procedure) :
    firstSome key rule.entries = (rule.field key).map Form.str := by
  unfold Generated.Procedure.entries Generated.Procedure.field
  induction rule.fields with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨k, v⟩ := head
    by_cases same : k = key <;> simp_all

/-- The value a procedure's form gives one of its own keys. -/
theorem procedure_get {key : String} (outside : key ∉ combinationKeys)
    (rule : Generated.Procedure) (a m t w : Option Form) :
    firstSome key ([("alpha", a), ("analyses", m), ("composition", some (.str "conditional"))] ++
      rule.entries ++ [("transitions", t), ("weights", w)]) = (rule.field key).map Form.str := by
  simp only [combinationKeys, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨h₁, h₂, h₃, -, h₄, h₅⟩ := outside
  rw [firstSome_append, firstSome_append, firstSome_entries]
  simp [Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, Ne.symm h₄, Ne.symm h₅]

/-- The text a form gives a key. -/
def Form.text (key : String) (f : Form) : Option String :=
  match f.get key with
  | some (.str s) => some s
  | _ => none

/-- Which kind of test a canonical test's form is. -/
def Form.tag (f : Form) : ℕ :=
  match f.text "test" with
  | some s =>
    if s = "fisher" then
      if f.get "alternative" = none then 0 else 1
    else if s = "wald_test" ∨ s = "score_test" ∨ s = "farrington_manning" ∨ s = "pearson_test" then 1
    else if s ∈ ["fisher_exact", "mcnemar", "mcnemar_asymptotic", "rate_test"] then 3
    else if s = "randomisation" then 4
    else if s = "binomial_exact_one_sided" then 5
    else if s = "two_stage" then 6
    else if s = "binomial_score_test" then 15
    else if s = "declared_test" ∨ s ∈ trialKeys then 8
    else 9
  | none =>
    if f.text "method" = some "bonferroni" then 10
    else if f.text "method" = some "alpha_spending" then 12
    else if (f.text "method").any (procedureMethods.contains ·) then 13
    else 14

def Test.tag : Test → ℕ
  | .fisher .. => 0
  | .exact .. => 1
  | .exactStudy .. => 3
  | .randomised .. => 4
  | .oneSample .. => 5
  | .oneSampleScore .. => 15
  | .twoStage .. => 6
  | .member _ => 7
  | .assumed .. => 8
  | .associated .. => 9
  | .bonferroni .. => 10
  | .looks .. => 12
  | .procedure .. => 13
  | .sequence .. => 14

theorem Test.tag_form : (t : Test) → t.canonical → t.form.tag = t.tag
  | .exact _ .fisherOneSided .., _ | .exact _ (.margin ..) .., _ => by
    simp [Test.form, Form.tag, Form.text, Test.tag]
  | .exact _ (.farringtonManning ..) .., _ | .exact _ (.pearson ..) .., _ => by
    simp [Test.form, Form.tag, Form.text, Test.tag]
  | .exact _ (.proportionZ pooled _) .., _ => by
    cases pooled <;> simp [Test.form, Form.tag, Form.text, Test.tag, ExactKind.key]
  | .exactStudy _ kind .., _ => by
    cases kind <;> simp [Test.form, Form.tag, Form.text, Test.tag, ExactStudyKind.key]
  | .member _, c => by simp [Test.canonical] at c
  | .assumed _ (.cited m) .., c => by
    simp only [Test.canonical, List.contains_iff_mem] at c
    have free := trial_key_free m c
    have listed : m.key ∈ trialKeys := List.mem_map_of_mem c
    simp only [reservedKeys, List.mem_cons, List.not_mem_nil, or_false, not_or] at free
    simp [Test.form, Form.tag, Form.text, Test.tag, free, listed]
  | .assumed _ (.declared ..) .., _ => by simp [Test.form, Form.tag, Form.text, Test.tag]
  | .associated _ m .., c => by
    simp only [Test.canonical, List.contains_iff_mem] at c
    have free := association_key_free m c
    simp only [reservedKeys, List.mem_cons, List.not_mem_nil, or_false, not_or] at free
    simp [Test.form, Form.tag, Form.text, Test.tag, free]
  | .procedure _ rule .., _ => by
    cases rule <;> simp [Test.form, Form.tag, Form.text, Test.tag, procedureMethods,
      Generated.procedures, Generated.Procedure.entries, Generated.Procedure.fields,
      Generated.Procedure.graph, Generated.Procedure.field]
  | .bonferroni _ _ _ none, _ | .bonferroni _ _ _ (some _), _ | .fisher .., _
  | .randomised .., _ | .oneSample .., _ | .oneSampleScore .., _ | .twoStage .., _ | .looks .., _
  | .sequence .., _ => by
    simp [Test.form, Form.tag, Form.text, Test.tag, procedure_methods_free]

theorem tag_eq {t₁ t₂ : Test} (c₁ : t₁.canonical) (c₂ : t₂.canonical) (h : t₁.form = t₂.form) :
    t₁.tag = t₂.tag := by
  rw [← Test.tag_form t₁ c₁, ← Test.tag_form t₂ c₂, h]

def Test.isWrapper : Test → Bool
  | .member _ => true
  | _ => false

theorem canonicalMembers_cons {c : Bool} {t : Test} {ts : List Test}
    (h : Test.canonicalMembers c (t :: ts) = true) :
    ((∃ u, t = .member u ∧ c = true ∧ u.isExactMember = true ∧ u.canonical = true) ∨
      (t.isWrapper = false ∧ (c && t.isExactMember) = false ∧ t.canonical = true)) ∧
    Test.canonicalMembers c ts = true := by
  cases t
  case member u =>
    simp only [Test.canonicalMembers, Bool.and_eq_true] at h
    exact ⟨Or.inl ⟨u, rfl, h.1.1.1, h.1.1.2, h.1.2⟩, h.2⟩
  all_goals
    simp only [Test.canonicalMembers, Bool.and_eq_true] at h
    exact ⟨Or.inr ⟨rfl, by simp [Test.isExactMember] at h ⊢; try exact h.1.1, h.1.2⟩, h.2⟩

@[simp] theorem adjusted_inj {a b : List String} :
    (if a = [] then none else some (Form.arr (a.map .str))) =
      (if b = [] then none else some (Form.arr (b.map .str))) ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  by_cases e : a = [] <;> by_cases e' : b = [] <;> simp_all

/-- What equal forms tell about two canonical tests with the same name: whether they are
exact members, how many threshold entries they print, and, once those agree, the test. -/
structure Agree (t₁ t₂ : Test) : Prop where
  exact : t₁.isExactMember = t₂.isExactMember
  length : t₁.thresholds.length = t₂.thresholds.length
  same : t₁.thresholds = t₂.thresholds → t₁ = t₂

structure AgreeAll (l₁ l₂ : List Test) : Prop where
  length : (Test.allThresholds l₁).length = (Test.allThresholds l₂).length
  same : Test.allThresholds l₁ = Test.allThresholds l₂ → l₁ = l₂

theorem Agree.of_eq {t₁ t₂ : Test} (h : t₁ = t₂) : Agree t₁ t₂ := h ▸ ⟨rfl, rfl, fun _ => rfl⟩

mutual
theorem Test.agree (t₁ t₂ : Test) (c₁ : t₁.canonical = true) (c₂ : t₂.canonical = true)
    (hn : t₁.name = t₂.name) (h : t₁.form = t₂.form) : Agree t₁ t₂ := by
  have tags := tag_eq c₁ c₂ h
  cases t₁ <;> cases t₂ <;> simp only [Test.tag] at tags <;> (try omega) <;>
    simp only [Test.name] at hn <;> (try subst hn)
  -- fisher
  · unfold Test.form at h; same_object h as e
    simp at e; casesm* _ ∧ _; subst_vars; exact Agree.of_eq rfl
  -- exact
  · rename_i k₁ d₁ nl₁ a₁ k₂ d₂ nl₂ a₂
    cases k₁ <;> cases k₂
    all_goals repeat cases ‹Bool›
    all_goals simp only [Test.form, ExactKind.key, Bool.false_eq_true, ite_false, ite_true] at h
    all_goals try separate h ["correction"]
    all_goals try separate h ["squared_cutoff"]
    all_goals same_object h as e
    all_goals simp at e
    all_goals casesm* _ ∧ _
    all_goals subst_vars
    all_goals simp_all [Test.canonical]
    all_goals try exact Agree.of_eq rfl
    subst_vars
    exact ⟨rfl, rfl, fun th => by simp_all [Test.thresholds, Form.object]⟩
  -- exactStudy
  · rename_i k₁ d₁ nl₁ a₁ k₂ d₂ nl₂ a₂
    cases k₁ <;> cases k₂
    all_goals simp only [Test.form, ExactStudyKind.key] at h
    all_goals try separate h ["squared_cutoff"]
    all_goals same_object h as e
    all_goals simp at e
    all_goals casesm* _ ∧ _
    all_goals subst_vars
    all_goals
      first
      | exact Agree.of_eq rfl
      | (simp only [Test.canonical, ExactStudyKind.matchesStudy] at c₁ c₂
         first | (rw [c₁] at c₂; simp at c₂) | (rw [c₂] at c₁; simp at c₁))
  -- randomised
  · rename_i r₁ r₂
    unfold Test.form at h; same_object h as e
    simp [Form.object] at e; casesm* _ ∧ _
    obtain ⟨_, _, _, _⟩ := r₁; obtain ⟨_, _, _, _⟩ := r₂
    simp_all; subst_vars; exact Agree.of_eq rfl
  -- oneSample
  · unfold Test.form at h; same_object h as e
    simp at e; casesm* _ ∧ _; subst_vars; exact Agree.of_eq rfl
  -- oneSampleScore
  · unfold Test.form at h; same_object h as e
    simp at e; casesm* _ ∧ _; subst_vars; exact Agree.of_eq rfl
  -- twoStage
  · unfold Test.form at h; same_object h as e
    simp at e; casesm* _ ∧ _; subst_vars; exact Agree.of_eq rfl
  -- member
  · simp [Test.canonical] at c₁
  -- assumed
  · rename_i g₁ d₁ nl₁ a₁ g₂ d₂ nl₂ a₂
    cases g₁ <;> cases g₂ <;> simp only [Test.form] at h
    · rename_i m₁ m₂
      same_object h as e
      simp at e; casesm* _ ∧ _; subst_vars
      simp only [Test.canonical, List.contains_iff_mem] at c₁ c₂
      rw [trial_key_inj m₁ c₁ m₂ c₂ (by assumption)]
      exact Agree.of_eq rfl
    · separate h ["scope"]
    · separate h ["scope"]
    · same_object h as e
      simp at e; casesm* _ ∧ _; subst_vars; exact Agree.of_eq rfl
  -- associated
  · rename_i m₁ d₁ nl₁ a₁ ad₁ m₂ d₂ nl₂ a₂ ad₂
    unfold Test.form at h; same_object h as e
    simp at e; casesm* _ ∧ _; subst_vars
    simp only [Test.canonical, List.contains_iff_mem] at c₁ c₂
    rw [association_key_inj m₁ c₁ m₂ c₂ (by assumption)]
    exact Agree.of_eq rfl
  -- bonferroni
  · rename_i ms₁ a₁ j₁ ms₂ a₂ j₂
    cases j₁ <;> cases j₂ <;> simp only [Test.form] at h
    · same_object h as e
      simp at e; casesm* _ ∧ _; subst_vars
      simp only [Test.canonical] at c₁ c₂
      have all := Test.agreeMembers true ms₁ ms₂ c₁ c₂ (by assumption)
      exact ⟨rfl, by simpa [Test.thresholds] using all.length,
        fun th => by rw [all.same (by simpa [Test.thresholds] using th)]⟩
    · separate h ["composition"]
    · separate h ["composition"]
    · same_object h as e
      simp at e; casesm* _ ∧ _; subst_vars
      simp only [Test.canonical] at c₁ c₂
      have all := Test.agreeMembers false ms₁ ms₂ c₁ c₂ (by assumption)
      exact ⟨rfl, by simpa [Test.thresholds] using all.length,
        fun th => by rw [all.same (by simpa [Test.thresholds] using th)]⟩
  -- looks
  · rename_i ms₁ a₁ ms₂ a₂
    unfold Test.form at h; same_object h as e
    simp at e; casesm* _ ∧ _; subst_vars
    simp only [Test.canonical] at c₁ c₂
    have all := Test.agreeMembers true ms₁ ms₂ c₁ c₂ (by assumption)
    exact ⟨rfl, by simpa [Test.thresholds] using all.length,
      fun th => by rw [all.same (by simpa [Test.thresholds] using th)]⟩
  -- procedure
  · rename_i r₁ ms₁ a₁ w₁ rs₁ r₂ ms₂ a₂ w₂ rs₂
    -- The registry entries the two forms write tell the procedures apart.
    have same : r₁ = r₂ := by
      refine procedure_determined r₁ (procedure_listed r₁) r₂ (procedure_listed r₂)
        fun key listed => ?_
      have seen := congrArg (Form.get key) h
      simp only [Test.form, get_object] at seen
      rw [procedure_get (procedure_keys_outside key listed),
        procedure_get (procedure_keys_outside key listed)] at seen
      exact Option.map_injective (fun _ _ e => by injection e) seen
    subst same
    unfold Test.form at h
    have e := object_inj (h := h) (keys := by simp [Generated.Procedure.entries])
      (nodup := by
        simpa [Generated.Procedure.entries, Function.comp_def] using
          procedure_keys_nodup r₁ (procedure_listed r₁))
    simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq, Option.some.injEq, List.append_cancel_left_eq] at e
    obtain ⟨ea, em, -, et, ew, -⟩ := e
    simp only [Test.canonical, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at c₁ c₂
    have all := Test.agreeMembers true ms₁ ms₂ c₁.1 c₂.1 (by simpa using em)
    have alphas : a₁ = a₂ := by simpa using ea
    have shares : w₁ = w₂ ∧ rs₁ = rs₂ := by
      cases graph : r₁.graph
      · simp only [graph, Bool.false_eq_true, false_or] at c₁ c₂
        exact ⟨c₁.2.1.trans c₂.2.1.symm, c₁.2.2.trans c₂.2.2.symm⟩
      · simp only [graph, ite_true, Option.some.injEq] at et ew
        exact ⟨by simpa using ew, by simpa using et⟩
    obtain ⟨rfl, rfl⟩ := shares
    subst alphas
    exact ⟨rfl, by simpa [Test.thresholds] using all.length,
      fun th => by rw [all.same (by simpa [Test.thresholds] using th)]⟩
  -- sequence
  · rename_i ms₁ a₁ ms₂ a₂
    unfold Test.form at h; same_object h as e
    simp at e; casesm* _ ∧ _; subst_vars
    simp only [Test.canonical] at c₁ c₂
    have all := Test.agreeMembers true ms₁ ms₂ c₁ c₂ (by assumption)
    exact ⟨rfl, by simpa [Test.thresholds] using all.length,
      fun th => by rw [all.same (by simpa [Test.thresholds] using th)]⟩
termination_by sizeOf t₁

theorem Test.agreeMembers (c : Bool) (l₁ l₂ : List Test)
    (c₁ : Test.canonicalMembers c l₁ = true) (c₂ : Test.canonicalMembers c l₂ = true)
    (h : Test.formMembers l₁ = Test.formMembers l₂) : AgreeAll l₁ l₂ := by
  match l₁, l₂ with
  | [], [] => exact ⟨rfl, fun _ => rfl⟩
  | [], _ :: _ => simp [Test.formMembers] at h
  | _ :: _, [] => simp [Test.formMembers] at h
  | e₁ :: r₁, e₂ :: r₂ =>
    simp only [Test.formMembers, List.cons.injEq] at h
    obtain ⟨head, tail⟩ := h
    simp [Form.object] at head
    obtain ⟨hf, hn⟩ := head
    obtain ⟨k₁, c₁'⟩ := canonicalMembers_cons c₁
    obtain ⟨k₂, c₂'⟩ := canonicalMembers_cons c₂
    have rest := Test.agreeMembers c r₁ r₂ c₁' c₂' tail
    have first : e₁.thresholds.length = e₂.thresholds.length ∧
        (e₁.thresholds = e₂.thresholds → e₁ = e₂) := by
      rcases k₁ with ⟨u₁, rfl, hc, x₁, cu₁⟩ | ⟨w₁, x₁, cu₁⟩ <;>
        rcases k₂ with ⟨u₂, rfl, _, x₂, cu₂⟩ | ⟨w₂, x₂, cu₂⟩
      · have a := Test.agree u₁ u₂ cu₁ cu₂ (by simpa [Test.name] using hn)
          (by simpa [Test.form] using hf)
        refine ⟨by simpa [Test.thresholds] using a.length, fun th => ?_⟩
        rw [a.same (by simpa [Test.thresholds] using th)]
      · have a := Test.agree u₁ e₂ cu₁ cu₂ (by simpa [Test.name] using hn)
          (by simpa [Test.form] using hf)
        have := a.exact
        simp_all
      · have a := Test.agree e₁ u₂ cu₁ cu₂ (by simpa [Test.name] using hn)
          (by simpa [Test.form] using hf)
        have := a.exact
        simp_all
      · have a := Test.agree e₁ e₂ cu₁ cu₂ hn hf
        exact ⟨a.length, a.same⟩
    refine ⟨by simp [Test.allThresholds, first.1, rest.length], fun th => ?_⟩
    simp only [Test.allThresholds] at th
    obtain ⟨h₁, h₂⟩ := List.append_inj th first.1
    rw [first.2 h₁, rest.same h₂]
termination_by sizeOf l₁
end

/-! ## Observed data and reported values -/

@[simp] theorem AssociationTable.form_inj {a b : AssociationTable} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold AssociationTable.form at h; same_object h as e
  cases a; cases b; simp_all

@[simp] theorem PairCounts.form_inj {a b : PairCounts} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold PairCounts.form at h; same_object h as e
  cases a; cases b; simp_all

@[simp] theorem EventCounts.form_inj {a b : EventCounts} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  unfold EventCounts.form at h; same_object h as e
  cases a; cases b; simp_all

@[simp] theorem Endpoints.form_inj {a b : Endpoints} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  cases a; cases b; simp_all [Endpoints.form]

@[simp] theorem getD_nat_inj {a b : Option ℕ} :
    (a.map Form.nat).getD .null = (b.map Form.nat).getD .null ↔ a = b := by
  cases a <;> cases b <;> simp

@[simp] theorem getD_rat_inj {a b : Option ℚ} :
    (a.map Form.rat).getD .null = (b.map Form.rat).getD .null ↔ a = b := by
  cases a <;> cases b <;> simp [Form.rat_inj] <;> simp [Form.rat]

theorem fits_bound {t : Test} {a b : ProbabilityFraction} (h₁ : (a.value == t.alpha) = true)
    (h₂ : (b.value == t.alpha) = true) : a = b :=
  ProbabilityFraction.ext_value ((beq_iff_eq.1 h₁).trans (beq_iff_eq.1 h₂).symm)

theorem ResultData.agree {t : Test} {d₁ d₂ : ResultData} (k₁ : d₁.fits t) (k₂ : d₂.fits t)
    (hs : d₁.subject t.form = d₂.subject t.form) (hr : d₁.reported = d₂.reported) : d₁ = d₂ := by
  revert k₁ k₂ hs hr
  cases d₁ <;> cases d₂ <;> intro k₁ k₂ hs hr <;>
    simp only [ResultData.subject, ResultData.reported, ObservedCounts.fields] at hs hr <;>
    (try (first
      | separate hs ["control_successes", "table", "pairs", "events", "responses",
          "stage1_responses"]
      | separate hr ["p_value", "support_max"]))
  -- fisher
  · rename_i o₁ r₁ l₁ u₁ b₁ o₂ r₂ l₂ u₂ b₂
    same_object hs as e₁; same_object hr as e₂
    simp only [ResultData.fits] at k₁ k₂
    obtain ⟨c₁, t₁⟩ := o₁; obtain ⟨c₂, t₂⟩ := o₂
    obtain ⟨⟨p₁, j₁⟩, m₁⟩ := r₁; obtain ⟨⟨p₂, j₂⟩, m₂⟩ := r₂
    simp at e₁ e₂; casesm* _ ∧ _; subst_vars
    rw [fits_bound k₁ k₂]
  -- margin
  · rename_i o₁ j₁ b₁ g₁ o₂ j₂ b₂ g₂
    same_object hs as e₁; same_object hr as e₂
    simp only [ResultData.fits, Bool.and_eq_true] at k₁ k₂
    obtain ⟨kb₁, kg₁⟩ := k₁; obtain ⟨kb₂, kg₂⟩ := k₂
    obtain ⟨c₁, t₁⟩ := o₁; obtain ⟨c₂, t₂⟩ := o₂
    simp at e₁ e₂; casesm* _ ∧ _; subst_vars
    rw [fits_bound kb₁ kb₂]
    cases t <;> simp_all
    rename_i kind _ _ _
    cases kind <;> simp_all
  -- association
  · rename_i a₁ r₁ a₂ r₂
    same_object hs as e₁; same_object hr as e₂
    obtain ⟨⟨p₁, j₁⟩, m₁⟩ := r₁; obtain ⟨⟨p₂, j₂⟩, m₂⟩ := r₂
    simp at e₁ e₂; casesm* _ ∧ _; subst_vars; rfl
  -- matched
  · rename_i a₁ r₁ a₂ r₂
    same_object hs as e₁; same_object hr as e₂
    obtain ⟨⟨p₁, j₁⟩, u₁, w₁⟩ := r₁; obtain ⟨⟨p₂, j₂⟩, u₂, w₂⟩ := r₂
    simp at e₁ e₂; casesm* _ ∧ _; subst_vars; rfl
  -- rate
  · rename_i a₁ s₁ r₁ a₂ s₂ r₂
    same_object hs as e₁; same_object hr as e₂
    simp only [ResultData.fits, beq_iff_eq] at k₁ k₂
    obtain ⟨⟨p₁, j₁⟩, u₁, w₁⟩ := r₁; obtain ⟨⟨p₂, j₂⟩, u₂, w₂⟩ := r₂
    simp at e₁ e₂; casesm* _ ∧ _; subst_vars
    rw [ProbabilityFraction.ext_value (k₁.trans k₂.symm)]
  -- oneSample
  · rename_i x₁ c₁ r₁ x₂ c₂ r₂
    same_object hs as e₁; same_object hr as e₂
    obtain ⟨p₁, j₁⟩ := r₁; obtain ⟨p₂, j₂⟩ := r₂
    simp at e₁ e₂; casesm* _ ∧ _; subst_vars; rfl
  -- twoStage
  · same_object hs as e₁; same_object hr as e₂
    simp at e₁ e₂; casesm* _ ∧ _; subst_vars; rfl

theorem ObservedCounts.ext' {a b : ObservedCounts} (h₁ : a.control = b.control)
    (h₂ : a.treatment = b.treatment) : a = b := by
  cases a; cases b; simp_all

theorem Endpoints.ext_values {a b : Endpoints} (h₁ : a.lower.value = b.lower.value)
    (h₂ : a.upper.value = b.upper.value) : a = b := by
  obtain ⟨l, u⟩ := a; obtain ⟨l', u'⟩ := b
  simp only at h₁ h₂
  rw [ProbabilityFraction.ext_value h₁, ProbabilityFraction.ext_value h₂]

theorem IntervalData.agree {d₁ d₂ : IntervalData} (hs : d₁.form = d₂.form)
    (hr : d₁.reported = d₂.reported) : d₁ = d₂ := by
  revert hs hr
  cases d₁ <;> cases d₂ <;> intro hs hr <;> simp only [IntervalData.form] at hs <;>
    (try separate hs ["responses", "cases", "control_successes", "table", "pairs", "events"])
  all_goals
    have tail := congrArg (Form.get "tail") hr
    have lower := congrArg (Form.get "lower") hr
    have upper := congrArg (Form.get "upper") hr
    have arm := congrArg (Form.get "arm") hr
    have control := congrArg (Form.get "control") hr
    have treatment := congrArg (Form.get "treatment") hr
    same_object hs as e
    simp [IntervalData.reported, oneIntervalOutputs, twoIntervalOutputs] at tail lower upper arm control treatment e
    casesm* _ ∧ _
    subst_vars
  · rw [Endpoints.ext_values lower upper]
  · rw [Endpoints.ext_values lower upper]
  all_goals first
    | rfl
    | (congr 1; apply ObservedCounts.ext' <;> assumption)

/-! ## Planning -/

@[simp] theorem BinomialPoint.prob_inj {a b : BinomialPoint} :
    (a.control = b.control ∧ a.treatment = b.treatment) ↔ a = b := by
  cases a; cases b; simp

theorem association_keys {f s : String} (h : associationKeys.contains (f, s) = true) :
    (f = "risk_unexposed" ∧ s = "risk_exposed") ∨
      (f = "prevalence_unexposed" ∧ s = "prevalence_exposed") ∨
      (f = "exposure_controls" ∧ s = "exposure_cases") := by
  simpa [associationKeys] using h

theorem BinomialPoint.ext' {a b : BinomialPoint} (h₁ : a.control = b.control)
    (h₂ : a.treatment = b.treatment) : a = b := by
  cases a; cases b; simp_all

theorem PlanningPoint.agree {a b : PlanningPoint} (c₁ : a.canonical) (c₂ : b.canonical)
    (h : a.form = b.form) : a = b := by
  revert c₁ c₂ h
  cases a <;> cases b <;> intro c₁ c₂ h <;> simp only [PlanningPoint.form] at h
  all_goals
    try (obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := association_keys c₁)
  all_goals
    try (obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := association_keys c₂)
  all_goals try separate h ["p_control", "response_rate", "discordant", "rate_ratio",
    "risk_exposed", "prevalence_exposed", "exposure_cases"]
  all_goals
    same_object h as e
    simp at e
    try casesm* _ ∧ _
    subst_vars
  all_goals first
    | rfl
    | (congr 1; apply BinomialPoint.ext' <;> assumption)
    | (simp only [PlanningPoint.canonical, beq_iff_eq] at c₁ c₂
       rw [ProbabilityFraction.ext_value (c₁.trans c₂.symm)])
    | (simp only [PlanningPoint.canonical, Bool.and_eq_true, beq_iff_eq] at c₁ c₂
       rw [ProbabilityFraction.ext_value (c₁.1.trans c₂.1.symm),
         ProbabilityFraction.ext_value (c₁.2.trans c₂.2.symm)])

theorem PlanningTarget.agree {a b : PlanningTarget} (c₁ : a.point.canonical)
    (c₂ : b.point.canonical) (h : a.form = b.form) : a = b := by
  unfold PlanningTarget.form at h; same_object h as e
  obtain ⟨p₁, w₁, r₁⟩ := a; obtain ⟨p₂, w₂, r₂⟩ := b
  simp only [Form.prob_inj] at e
  obtain ⟨hp, rfl, rfl⟩ := e
  obtain rfl : p₁ = p₂ := PlanningPoint.agree c₁ c₂ hp
  rfl

theorem Stages.ext' {a b : Stages} (h₁ : a.first = b.first) (h₂ : a.second = b.second) :
    a = b := by
  cases a; cases b; simp_all

@[simp] theorem PlanSelection.form_inj {a b : PlanSelection} : a.form = b.form ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  cases a <;> cases b <;> simp only [PlanSelection.form] at h <;>
    (try separate h ["n_control", "critical_value", "n_stage1", "n"])
  all_goals
    same_object h as e
    simp at e
    try casesm* _ ∧ _
    subst_vars
  all_goals first
    | rfl
    | (congr 1; apply FixedSampleDesign.ext_sizes <;> assumption)
    | (congr 1; apply Stages.ext' <;> assumption)

/-- A search's candidates give its kind and range, but whether it asks for the smallest
size, which the claim says. -/
theorem SearchKind.agree {t : Test} {k₁ k₂ : SearchKind} {r₁ r₂ : SearchRange}
    (f₁ : k₁.fits t r₁) (f₂ : k₂.fits t r₂) (h : k₁.form t r₁ = k₂.form t r₂) :
    k₁ = k₂ ∧ r₁.low = r₂.low ∧ r₁.high = r₂.high ∧ r₁.ratio = r₂.ratio := by
  revert f₁ f₂ h
  cases k₁ <;> cases k₂ <;> intro f₁ f₂ h <;> simp only [SearchKind.form] at h <;>
    cases hc : t.isCohort <;> (try simp only [hc, ite_true, ite_false, Bool.false_eq_true] at h) <;>
    (try separate h ["allocation", "controls_per_case", "unexposed_per_exposed", "max_n",
      "max_pairs", "max_events"])
  all_goals try
    (simp only [SearchKind.fits, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at f₁ f₂
     simp_all)
  all_goals
    same_object h as e
    simp at e
    try casesm* _ ∧ _
  all_goals simp_all [SearchKind.fits]
  all_goals exact allocationString_injective ‹_›

theorem SearchRange.ext' {a b : SearchRange} (h₁ : a.low = b.low) (h₂ : a.high = b.high)
    (h₃ : a.ratio = b.ratio) (h₄ : a.minimal = b.minimal) : a = b := by
  cases a; cases b; simp_all

theorem ResultData.subject_analysis (d : ResultData) (f : Form) :
    (d.subject f).get "analysis" = some f := by
  cases d <;> simp [ResultData.subject, ObservedCounts.fields]

theorem SearchKind.form_analysis (k : SearchKind) (t : Test) (r : SearchRange) :
    (k.form t r).get "analysis" = some t.form := by
  cases k <;> simp [SearchKind.form]
  split <;> simp

theorem ResultData.reported_ne (d : ResultData) (p : ProbabilityFraction) (b : Bool) :
    d.reported ≠ Form.object [("p_value", some (.prob p)), ("reject_null", some (.bool b))] := by
  intro h
  cases d <;> simp only [ResultData.reported] at h <;>
    separate h ["support_max", "p_value", "observed_table_probability", "upper_tail",
      "critical_value"]

/-! ## Requests -/

/-- The threshold entries a request prints: its test's. -/
def Request.thresholds (r : Request) : List Form := (r.test.map Test.thresholds).getD []

structure RAgree (r₁ r₂ : Request) : Prop where
  length : r₁.thresholds.length = r₂.thresholds.length
  same : r₁.thresholds = r₂.thresholds → r₁ = r₂

def Request.kindKey : Request → String
  | .typeI _ => "typeI"
  | .familywise _ => "familywise"
  | .result .. | .checkedResult .. => "result"
  | .interval .. => "interval"
  | .planned _ q target _ => (q.form target).1

def Request.subject : Request → Form
  | .typeI t | .familywise t => t.form
  | .result _ t observed _ => .object (("analysis", some t.form) :: observed.fields)
  | .checkedResult _ t d => d.subject t.form
  | .interval _ d => d.form
  | .planned _ q target _ => (q.form target).2

theorem Request.form_eq (r : Request) : r.form = .object [("kind", some (.str r.kindKey)),
    ("subject", some r.subject), ("subject_name", some (.str r.name))] := by
  cases r <;> rfl

theorem PlanQuery.form_kind (q : PlanQuery) (target : PlanningTarget) :
    (q.form target).1 = "meets" ∨ (q.form target).1 = "sample_size" := by
  cases q <;> simp [PlanQuery.form]

theorem RAgree.of_test {r₁ r₂ : Request} {t₁ t₂ : Test} (e₁ : r₁.test = some t₁)
    (e₂ : r₂.test = some t₂) (a : Agree t₁ t₂) (same : t₁ = t₂ → r₁ = r₂) : RAgree r₁ r₂ :=
  ⟨by simp [Request.thresholds, e₁, e₂, a.length],
    fun th => same (a.same (by simpa [Request.thresholds, e₁, e₂] using th))⟩

theorem Request.agree {r₁ r₂ : Request} (c₁ : r₁.canonical) (c₂ : r₂.canonical)
    (h : r₁.form = r₂.form) (hr : r₁.reported = r₂.reported) : RAgree r₁ r₂ := by
  rw [Request.form_eq, Request.form_eq] at h
  same_object h as e
  simp only [Form.str.injEq] at e
  obtain ⟨hk, hs, hn⟩ := e
  revert c₁ c₂ hr hk hs hn
  cases r₁ <;> cases r₂ <;> intro c₁ c₂ hr hk hs hn
  case typeI.typeI t₁ t₂ =>
    exact RAgree.of_test rfl rfl (Test.agree t₁ t₂ c₁ c₂ hn hs) (by rintro rfl; rfl)
  case familywise.familywise t₁ t₂ =>
    exact RAgree.of_test rfl rfl (Test.agree t₁ t₂ c₁ c₂ hn hs) (by rintro rfl; rfl)
  case result.result n₁ t₁ o₁ f₁ n₂ t₂ o₂ f₂ =>
    simp only [Request.canonical, Bool.and_eq_true, beq_iff_eq] at c₁ c₂
    simp only [Request.subject, ObservedCounts.fields] at hs
    simp only [Request.reported, Option.some.injEq] at hr
    same_object hs as e₁; same_object hr as e₂
    simp only [Request.name] at hn
    simp at e₁ e₂
    obtain ⟨hf, hc, ht⟩ := e₁
    refine RAgree.of_test rfl rfl
      (Test.agree t₁ t₂ c₁.2 c₂.2 (by rw [c₁.1, c₂.1, hn]) hf) ?_
    rintro rfl
    obtain ⟨_, _⟩ := o₁; obtain ⟨_, _⟩ := o₂; obtain ⟨_, _⟩ := f₁; obtain ⟨_, _⟩ := f₂
    simp_all
  case result.checkedResult =>
    simp only [Request.reported, Option.some.injEq] at hr
    exact absurd hr.symm (ResultData.reported_ne _ _ _)
  case checkedResult.result =>
    simp only [Request.reported, Option.some.injEq] at hr
    exact absurd hr (ResultData.reported_ne _ _ _)
  case checkedResult.checkedResult n₁ t₁ d₁ n₂ t₂ d₂ =>
    simp only [Request.canonical, Bool.and_eq_true, beq_iff_eq] at c₁ c₂
    simp only [Request.subject] at hs
    simp only [Request.reported, Option.some.injEq] at hr
    simp only [Request.name] at hn
    have hf := congrArg (Form.get "analysis") hs
    simp only [ResultData.subject_analysis, Option.some.injEq] at hf
    refine RAgree.of_test rfl rfl
      (Test.agree t₁ t₂ c₁.1.2 c₂.1.2 (by rw [c₁.1.1, c₂.1.1, hn]) hf) ?_
    rintro rfl
    rw [hn, ResultData.agree c₁.2 c₂.2 hs hr]
  case interval.interval n₁ d₁ n₂ d₂ =>
    simp only [Request.subject] at hs
    simp only [Request.reported, Option.some.injEq] at hr
    simp only [Request.name] at hn
    exact ⟨rfl, fun _ => by rw [hn, IntervalData.agree hs hr]⟩
  case planned.planned n₁ q₁ g₁ s₁ n₂ q₂ g₂ s₂ =>
    simp only [Request.name] at hn
    simp only [Request.reported] at hr
    have selected : s₁ = s₂ := (option_map_inj fun _ _ h => PlanSelection.form_inj.1 h).1 hr
    subst hn selected
    cases q₁ <;> cases q₂ <;>
      simp only [Request.kindKey, Request.subject, PlanQuery.form] at hk hs <;>
      (try simp at hk)
    case meets.meets t₁ t₂ =>
      simp only [Request.canonical, Bool.and_eq_true, beq_iff_eq] at c₁ c₂
      same_object hs as e
      obtain ⟨hf, hg⟩ := e
      refine RAgree.of_test rfl rfl
        (Test.agree t₁ t₂ c₁.1.2 c₂.1.2 (by rw [c₁.1.1, c₂.1.1]) hf) ?_
      rintro rfl
      rw [PlanningTarget.agree c₁.2 c₂.2 hg]
    case search.search t₁ k₁ r₁ t₂ k₂ r₂ =>
      simp only [Request.canonical, Bool.and_eq_true, beq_iff_eq] at c₁ c₂
      same_object hs as e
      obtain ⟨hc, hm, hg⟩ := e
      have hf := congrArg (Form.get "analysis") hc
      simp only [SearchKind.form_analysis, Option.some.injEq] at hf
      refine RAgree.of_test rfl rfl
        (Test.agree t₁ t₂ c₁.1.1.2 c₂.1.1.2 (by rw [c₁.1.1.1, c₂.1.1.1]) hf) ?_
      rintro rfl
      obtain ⟨rfl, low, high, ratio⟩ := SearchKind.agree c₁.1.2 c₂.1.2 hc
      have minimal : r₁.minimal = r₂.minimal := by
        cases h₁ : r₁.minimal <;> cases h₂ : r₂.minimal <;> simp_all
      rw [SearchRange.ext' low high ratio minimal, PlanningTarget.agree c₁.2 c₂.2 hg]
    case search.stageSearch =>
      same_object hs as e
      have := congrArg (Form.get "analysis") e.1
      simp [SearchKind.form_analysis] at this
    case stageSearch.search =>
      same_object hs as e
      have := congrArg (Form.get "analysis") e.1
      simp [SearchKind.form_analysis] at this
    case stageSearch.stageSearch =>
      simp only [Request.canonical] at c₁ c₂
      same_object hs as e
      simp [Form.object] at e
      obtain ⟨⟨rfl, rfl, rfl⟩, hg⟩ := e
      exact ⟨rfl, fun _ => by rw [PlanningTarget.agree c₁ c₂ hg]⟩
  all_goals
    simp only [Request.kindKey] at hk
    first
    | (simp at hk; done)
    | (rcases PlanQuery.form_kind ‹PlanQuery› ‹PlanningTarget› with k | k <;> rw [k] at hk <;>
        simp at hk)

/-! ## Programs -/

theorem Request.reported_ne_null (r : Request) : r.reported ≠ some .null := by
  cases r with
  | checkedResult _ _ d => cases d <;> simp [Request.reported, ResultData.reported, Form.object]
  | interval _ d =>
    cases d <;> simp [Request.reported, IntervalData.reported, oneIntervalOutputs,
      twoIntervalOutputs, Form.object]
  | planned _ _ _ s =>
    cases s with
    | none => simp [Request.reported]
    | some s => cases s <;> simp [Request.reported, PlanSelection.form, Form.object]
  | _ => simp [Request.reported, Form.object]

theorem outputs_inj {xs ys : List (Option Form)} (hx : ∀ x ∈ xs, x ≠ some .null)
    (hy : ∀ y ∈ ys, y ≠ some .null) (h : xs.map (·.getD .null) = ys.map (·.getD .null)) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons, forall_eq_or_imp] at hx hy
      refine congrArg₂ _ ?_ (ih hx.2 hy.2 h.2)
      cases x <;> cases y <;> simp_all [eq_comm]

theorem none_of_any {xs : List (Option Form)} (h : ¬ xs.any Option.isSome = true) :
    xs = List.replicate xs.length none := by
  rw [List.eq_replicate_iff]
  refine ⟨rfl, fun x mem => ?_⟩
  simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true,
    Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
  exact h x mem

theorem reported_inj {rs₁ rs₂ : List Request} (lengths : rs₁.length = rs₂.length)
    (h : (if (rs₁.map Request.reported).any Option.isSome then
        some (Form.arr ((rs₁.map Request.reported).map (·.getD .null))) else none) =
      (if (rs₂.map Request.reported).any Option.isSome then
        some (Form.arr ((rs₂.map Request.reported).map (·.getD .null))) else none)) :
    rs₁.map Request.reported = rs₂.map Request.reported := by
  have nonnull : ∀ rs : List Request, ∀ x ∈ rs.map Request.reported, x ≠ some .null := by
    intro rs x mem
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 mem
    exact r.reported_ne_null
  by_cases h₁ : (rs₁.map Request.reported).any Option.isSome = true <;>
    by_cases h₂ : (rs₂.map Request.reported).any Option.isSome = true <;>
    simp only [h₁, h₂, ite_true, ite_false, Bool.false_eq_true] at h
  · simp only [Option.some.injEq, Form.arr.injEq] at h
    exact outputs_inj (nonnull rs₁) (nonnull rs₂) h
  · simp at h
  · simp at h
  · rw [none_of_any h₁, none_of_any h₂]
    simp [lengths]

theorem requests_agree : ∀ (rs₁ rs₂ : List Request), rs₁.all Request.canonical = true →
    rs₂.all Request.canonical = true → rs₁.map Request.form = rs₂.map Request.form →
    rs₁.map Request.reported = rs₂.map Request.reported →
    (rs₁.flatMap Request.thresholds).length = (rs₂.flatMap Request.thresholds).length ∧
      (rs₁.flatMap Request.thresholds = rs₂.flatMap Request.thresholds → rs₁ = rs₂)
  | [], [], _, _, _, _ => ⟨rfl, fun _ => rfl⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | r₁ :: rs₁, r₂ :: rs₂, c₁, c₂, h, hr => by
    simp only [List.all_cons, Bool.and_eq_true] at c₁ c₂
    simp only [List.map_cons, List.cons.injEq] at h hr
    have first := Request.agree c₁.1 c₂.1 h.1 hr.1
    have rest := requests_agree rs₁ rs₂ c₁.2 c₂.2 h.2 hr.2
    refine ⟨by simp [first.length, rest.1], fun th => ?_⟩
    simp only [List.flatMap_cons] at th
    obtain ⟨t₁, t₂⟩ := List.append_inj th first.length
    rw [first.same t₁, rest.2 t₂]

theorem declarations_agree : ∀ (ds₁ ds₂ : List Test), ds₁.all Test.canonical = true →
    ds₂.all Test.canonical = true → ds₁.map Test.declaration = ds₂.map Test.declaration →
    AgreeAll ds₁ ds₂
  | [], [], _, _, _ => ⟨rfl, fun _ => rfl⟩
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | d₁ :: ds₁, d₂ :: ds₂, c₁, c₂, h => by
    simp only [List.all_cons, Bool.and_eq_true] at c₁ c₂
    simp only [List.map_cons, List.cons.injEq] at h
    have head := h.1
    simp [Test.declaration, Form.object] at head
    have first := Test.agree d₁ d₂ c₁.1 c₂.1 head.1 head.2.2
    have rest := declarations_agree ds₁ ds₂ c₁.2 c₂.2 h.2
    refine ⟨by simp [Test.allThresholds, first.length, rest.length], fun th => ?_⟩
    simp only [Test.allThresholds] at th
    obtain ⟨t₁, t₂⟩ := List.append_inj th first.length
    rw [first.same t₁, rest.same t₂]

theorem allThresholds_filterMap (rs : List Request) :
    Test.allThresholds (rs.filterMap Request.test) = rs.flatMap Request.thresholds := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    cases e : r.test <;>
      simp [e, Request.thresholds, Test.allThresholds, ih]

theorem thresholds_inj {a b : List Form} :
    (if a.isEmpty then none else some (Form.arr a)) =
      (if b.isEmpty then none else some (Form.arr b)) → a = b := by
  intro h
  by_cases e : a = [] <;> by_cases e' : b = [] <;> simp_all

/-- Two programs in canonical form with the same form are the same program: the form a
certificate's build prints determines the data its statements are about. -/
theorem Program.form_injective {p q : Program} (hp : p.Canonical) (hq : q.Canonical)
    (h : p.form = q.form) : p = q := by
  obtain ⟨rs₁, ds₁⟩ := p
  obtain ⟨rs₂, ds₂⟩ := q
  simp only [Program.Canonical, Bool.and_eq_true] at hp hq
  unfold Program.form at h
  dsimp only at h
  same_object h as e
  obtain ⟨hc, hd, ht, hr⟩ := e
  simp only [Form.arr.injEq] at hc hd
  have lengths : rs₁.length = rs₂.length := by simpa using congrArg List.length hc
  have requests := requests_agree rs₁ rs₂ hp.1 hq.1 hc (reported_inj lengths hr)
  have declarations := declarations_agree ds₁ ds₂ hp.2 hq.2 hd
  have thresholds := thresholds_inj ht
  rw [allThresholds_filterMap, allThresholds_filterMap] at thresholds
  obtain ⟨t₁, t₂⟩ := List.append_inj thresholds declarations.length
  rw [declarations.same t₁, requests.2 t₂]

end StatClaim.Semantics
