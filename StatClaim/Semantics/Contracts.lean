module

public import StatClaim.Semantics.Syntax

/-!
The contract checks of a program, computed from its data. `decide +kernel` evaluates
them; plain `decide` cannot reduce rational arithmetic.

Trusted. See docs/proposals/lean-semantics.md.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Interface

/-- Whole clusters were assigned. The model's law is then one the instance gives. -/
def Model.clustered (model : Model) : Bool :=
  model.clusters.isSome

/-- The declared design features a test's assumptions can contradict. -/
def Model.features (model : Model) : List Generated.DesignFeature :=
  (match model.measurements with
    | some count => if 1 < count then [.repeated_measures] else []
    | none => []) ++
  (if model.clusters.isSome then [.clusters] else [])

/-- What a cited test's minimum sizes count, in each arm. -/
def Model.counts (model : Model) (unit : Generated.CountUnit) : ℕ × ℕ :=
  match unit with
  | .cluster => model.clusters.getD (0, 0)
  | .participant => (model.sizes.nControl, model.sizes.nTreatment)

/-- A null fits a test on a design: it is about the design's model, and it has a value
exactly when its form takes one. -/
def Null.fits (null : Null) (design : Design) : Bool :=
  decide (null.model = design.model) && decide (null.value.isSome = null.key.takesValue)

/-- A row of a graph passes nothing to its own test, nothing negative, and at most all. -/
def rowFits (index : ℕ) (row : List ℚ) : Bool :=
  decide (row[index]? = some 0) && row.all (fun t => decide (0 ≤ t)) && decide (row.sum ≤ 1)

/-- A single test, not a combination. -/
def Test.single : Test → Bool
  | .fisher .. => true
  | .exact .. => true
  | .exactStudy .. => true
  | .randomised .. | .member .. | .oneSample .. | .oneSampleScore .. | .twoStage .. => true
  | .assumed .. => true
  | .associated .. => true
  | _ => false

/-- What a cited test of association's minimum total counts: the pairs of a matched
study, nothing for a person-time cohort, otherwise the fixed group sizes or `n`. -/
def Study.total (study : Study) : Option ℕ :=
  match study.design with
  | .matched_case_control => study.pairs
  | .person_time_cohort => none
  | .case_control => some (study.cases.getD 0 + study.controls.getD 0)
  | .cohort =>
    match study.exposed, study.unexposed with
    | some exposed, some unexposed => some (exposed + unexposed)
    | _, _ => study.n
  | .cross_sectional => study.n

def ExactStudyKind.fits (kind : ExactStudyKind) (study : Study) : Bool :=
  match kind with
  | .fisherGroups =>
    match study.groups with
    | some (first, second) => decide (0 < first ∧ 0 < second)
    | none => false
  | .fisherMixture =>
    study.groups.isNone && decide (study.design = .cohort ∨ study.design = .cross_sectional) &&
    decide (0 < study.n.getD 0)
  | .matched => decide (study.design = .matched_case_control ∧ 0 < study.pairs.getD 0)
  | .matchedAsymptotic cutoff =>
    decide (study.design = .matched_case_control ∧ 0 < study.pairs.getD 0 ∧ 0 < cutoff)
  | .incidence => decide (study.design = .person_time_cohort)

/-- A design with looks. -/
def Test.isLooks : Test → Bool
  | .looks .. => true
  | .procedure _ rule .. => rule.question == .looks
  | _ => false

def Test.composable : Test → Bool
  | .randomised .. | .oneSample .. | .oneSampleScore .. | .twoStage .. => false
  | t => t.single

def Test.assumableMember : Test → Bool
  | .exact .. | .exactStudy .. | .randomised .. => true
  | _ => false

def Test.isMember : Test → Bool
  | .member .. => true
  | _ => false

def Test.hasTypeI : Test → Bool
  | .member .. | .oneSample .. | .twoStage .. => false
  | t => t.single || t.isLooks

def ProbabilityFraction.interior (p : ProbabilityFraction) : Bool :=
  decide (0 < p.num ∧ p.num < p.den)

def StageRule.check (r : StageRule) (s : Stages) : Bool :=
  match r with
  | .threshold interim final => decide (interim < s.first ∧ interim ≤ final ∧
      final < s.first + s.second)
  | .posterior a b reference interim final =>
    decide (0 < a ∧ 0 < b) && reference.interior && interim.interior && final.interior

/-- The declared scheme determines the groups and the attainable p-values. -/
def Randomised.check (r : Randomised) : Bool :=
  let m := r.design.model
  let (c, t) := r.sizes
  let validParts := r.parts.all (fun (a, b) => decide (0 < a + b)) &&
    decide ((r.parts.map Prod.fst).sum = c ∧ (r.parts.map Prod.snd).sum = t)
  let validScheme := match m.randomisation with
    | some "complete" => m.strata.isEmpty && m.blockSize.isNone
    | some "stratified" => decide (2 ≤ m.strata.length) && m.blockSize.isNone && validParts
    | some "blocked" =>
      match m.blockSize with
      | some b => decide (2 ≤ b) && validParts && r.parts.all (fun (a, t) =>
          decide ((a + t) % b = 0 ∧ (t * b) % (a + t) = 0))
      | none => false
    | _ => false
  let denominator := match r.draws with
    | some b => b + 1
    | none => (r.groups.map (fun (a, b) => Nat.fast_choose a b)).prod
  decide (r.nullModel = m ∧ 0 < c ∧ 0 < t ∧ c + t ≤ 10000) &&
  (m.population.isNone || m.population == some "randomised") && validScheme &&
  decide (r.groups.length ≤ 1000) &&
  (match r.draws with | some b => decide (0 < b ∧ b ≤ 10000000) | none => true) &&
  decide (0 < r.alpha.value ∧ r.alpha.value < 1 ∧ (1 : ℚ) / denominator ≤ r.alpha.value)

/-- The question a look asks: its test, and its null's form and value. -/
def Test.question : Test → Option (String × Generated.NullKey × Option ℚ)
  | .fisher _ _ null _ => some ("fisher", null.key, null.value)
  | .exact _ kind _ null _ => some (kind.key, null.key, null.value)
  | .assumed _ (.cited method) _ null _ => some (method.key, null.key, null.value)
  | .assumed _ (.declared method ..) _ null _ => some (method, null.key, null.value)
  | .member t => t.question
  | _ => none

/-- The arm sizes a look is taken at. -/
def Test.sizes : Test → Option (ℕ × ℕ)
  | .fisher _ design .. => some (design.model.sizes.nControl, design.model.sizes.nTreatment)
  | .exact _ _ design .. => some (design.model.sizes.nControl, design.model.sizes.nTreatment)
  | .assumed _ _ design .. => some (design.model.sizes.nControl, design.model.sizes.nTreatment)
  | .member t => t.sizes
  | _ => none

/-- Each look is taken at no fewer participants in either arm, and more in all. -/
def growing : List (ℕ × ℕ) → Bool
  | a :: b :: rest =>
    decide (a.1 ≤ b.1 ∧ a.2 ≤ b.2 ∧ a.1 + a.2 < b.1 + b.2) && growing (b :: rest)
  | _ => true

mutual
def Test.check : Test → Bool
  | .fisher _ design null _ =>
    null.fits design && decide (design.model.outcome = .binary) &&
    decide (null.key = .equal_proportions) && design.model.features.isEmpty
  | .exact _ .fisherOneSided design null alpha =>
    null.fits design && decide (design.model.outcome = .binary) &&
    decide (null.key = .proportion_difference_at_most) && decide (null.value = some 0) &&
    design.model.features.isEmpty && decide (0 < alpha.value) && decide (alpha.value < 1)
  | .exact _ (.margin margin thresholds) design null alpha =>
    let sizes := design.model.sizes
    null.fits design && decide (design.model.outcome = .binary) &&
    decide (null.key = .proportion_difference_at_most ∧ null.value = some margin) &&
    design.model.features.isEmpty && decide (0 < alpha.value ∧ alpha.value < 1) &&
    decide (sizes.nControl ≤ 120 ∧ sizes.nTreatment ≤ 120 ∧ -1 < margin ∧ margin < 1) &&
    decide (thresholds.length = sizes.nControl + 1) &&
    thresholds.all (fun t => decide (t ≤ sizes.nTreatment + 1))
  | .exact _ (.proportionZ _ cutoff) design null _ =>
    let sizes := design.model.sizes
    null.fits design && decide (design.model.outcome = .binary) &&
    decide (null.key = .equal_proportions) && design.model.features.isEmpty &&
    decide (sizes.nControl = sizes.nTreatment ∧ 0 < cutoff)
  | .exact _ (.pearson _ cutoff) design null _ =>
    null.fits design && decide (design.model.outcome = .binary) &&
    decide (null.key = .equal_proportions) && design.model.features.isEmpty && decide (0 < cutoff)
  | .exact _ (.farringtonManning margin cutoff) design null alpha =>
    null.fits design && decide (design.model.outcome = .binary) &&
    decide (null.key = .proportion_difference_at_most ∧ null.value = some margin) &&
    design.model.features.isEmpty && decide (-1 < margin ∧ margin < 0 ∧ 0 < cutoff) &&
    decide (0 < alpha.value ∧ alpha.value < 1)
  | .exactStudy _ kind design null alpha =>
    let study := design.model
    decide (null.model = study) && decide (study.survey = .simple_random) &&
    decide (study.exposureScale = .binary) && decide (study.outcomeScale = .binary) &&
    kind.fits study && decide (0 < alpha.value ∧ alpha.value < 1)
  | .randomised _ r => r.check
  | .oneSample _ n reference alpha => decide (0 < n ∧ n ≤ 1000) && reference.interior && alpha.interior
  | .oneSampleScore _ n reference _ cutoff =>
    decide (0 < n ∧ n ≤ 1000 ∧ 0 < cutoff) && reference.interior
  | .twoStage _ s rule reference =>
    decide (0 < s.first ∧ s.first ≤ 200 ∧ 0 < s.second ∧ s.second ≤ 200) &&
    reference.interior && rule.check s
  | .member t => t.assumableMember && t.check
  | .assumed _ (.declared ..) design null alpha =>
    null.fits design && decide (0 < alpha.value) && decide (alpha.value < 1)
  | .assumed _ (.cited method) design null alpha =>
    let counts := design.model.counts method.unit
    null.fits design && method.nulls.contains null.key &&
    decide (null.key.outcome = method.outcome) &&
    decide (design.model.outcome = method.outcome) &&
    decide (method.unit = if design.model.clustered then .cluster else .participant) &&
    decide (method.minPerArm ≤ counts.1) && decide (method.minPerArm ≤ counts.2) &&
    decide (method.minTotal ≤ counts.1 + counts.2) &&
    design.model.features.all (fun feature =>
      method.assumptions.all fun assumption => !(feature.contradicts.contains assumption)) &&
    (match method.nullValue with
      | none => true
      | some value => decide (null.value = some value)) &&
    decide (0 < alpha.value) && decide (alpha.value < 1)
  | .associated _ method design null alpha adjusted =>
    let study := design.model
    decide (null.model = study) && method.designs.contains study.design &&
    method.outcomeScales.contains study.outcomeScale &&
    method.exposureScales.contains study.exposureScale && method.surveys.contains study.survey &&
    (match study.total with
      | some total => decide (method.minTotal ≤ total)
      | none => true) &&
    (match method.minClusters with
      | some least => study.survey != .cluster || decide (least ≤ study.clusters.getD 0)
      | none => true) &&
    (adjusted.isEmpty || method.covariates) &&
    decide (0 < alpha.value) && decide (alpha.value < 1)
  | .bonferroni _ members _ _ =>
    Test.checkAll members && members.all (fun t => t.composable || t.isLooks)
  | .looks _ members _ =>
    Test.checkAll members && members.all Test.composable &&
    (match members with
      | [] => false
      | first :: rest =>
        first.question.isSome && rest.all (fun look => look.question == first.question)) &&
    (match members.mapM Test.sizes with
      | some sizes => growing sizes
      | none => false)
  | .procedure _ rule members alpha weights rows =>
    Test.checkAll members && members.all Test.composable &&
    -- Looks ask one question at growing sizes.
    (match rule.question with
      | .looks =>
        (match members with
          | [] => false
          | first :: rest =>
            first.question.isSome && rest.all (fun look => look.question == first.question)) &&
        (match members.mapM Test.sizes with
          | some sizes => growing sizes
          | none => false)
      | .family => true) &&
    (match rule.levels with
      | .equal => members.all (fun t => decide (t.alpha = alpha.value))
      | .atMost => members.all (fun t => decide (t.alpha ≤ alpha.value))) &&
    -- A graph's shares of the level add up to at most the whole, and so do the shares
    -- each test passes on; other procedures take neither.
    (if rule.graph then
      decide (weights.length = members.length) &&
      weights.all (fun w => decide (0 ≤ w)) && decide (weights.sum ≤ 1) &&
      decide (rows.length = members.length) &&
      (List.range rows.length).all (fun index => rowFits index (rows.getD index []))
    else weights.isEmpty && rows.isEmpty)
  | .sequence _ members alpha =>
    (Test.checkAll members && members.all (fun t => !t.single || t.composable)) &&
    members.all (fun t => decide (t.alpha = alpha.value))
termination_by structural t => t

def Test.checkAll : List Test → Bool
  | [] => true
  | t :: ts => Test.check t && Test.checkAll ts
termination_by structural ts => ts
end

def Test.isOneSidedFisher : Test → Bool
  | .exact _ .fisherOneSided .. => true
  | _ => false

/-- A Type I claim is about a single test or a design with looks, and a familywise claim
about another combination. -/
def Request.check : Request → Bool
  | .typeI t => t.hasTypeI && t.check
  | .familywise t => !t.single && !t.isLooks && t.check
  | .result _ t .. => t.isOneSidedFisher && t.check
  | .checkedResult _ t .. => t.single && t.check
  | .interval .. => true
  | .planned _ q .. => q.test.all Test.check

mutual

/-- Conditional compositions carry a named premise for exact members. A declared
binomial joint law instead uses the concrete two-sided Fisher tests. The canonical
program records the composition, so these choices are checked in Lean. -/
def Test.memberRoles : Test → Bool
  | .bonferroni _ members _ joint =>
    (joint.isNone || joint == some "binomial_marginals") &&
    Test.validMemberRoles joint.isNone members
  | .looks _ members _ | .procedure _ _ members ..
  | .sequence _ members _ => Test.validMemberRoles true members
  | _ => true
termination_by structural t => t

def Test.validMemberRoles (conditional : Bool) : List Test → Bool
  | [] => true
  | t :: ts =>
    let role := if conditional then !t.assumableMember else
      match t with
      | .fisher .. => true
      | _ => false
    role && t.memberRoles && Test.validMemberRoles conditional ts
termination_by structural ts => ts

end

def Test.rootRole (t : Test) : Bool := !t.isMember && t.memberRoles

/-- Every declared test and combination meets its contracts, and every request has its
shape. -/
def Program.Contracts (p : Program) : Prop :=
  (p.declarations.all (fun t => t.check && t.rootRole) &&
    p.requests.all (fun q => q.test.all Test.rootRole) &&
    p.requests.all Request.check) = true

instance (p : Program) : Decidable p.Contracts :=
  inferInstanceAs (Decidable (_ = true))

end StatClaim.Semantics
