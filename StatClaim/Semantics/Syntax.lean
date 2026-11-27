module

public import StatClaim.Design
public import StatClaim.Generated.Methods
public import StatClaim.Interface.Premises

/-!
A compiled program as Lean data: its models, designs, nulls, tests and requested
claims, field for field as in the canonical program a certificate binds. A key the
canonical program writes only when it is declared is an `Option` or a list here, so
two different programs in canonical form never have the same canonical form
(`Injective.lean`).

Tests are identified by name, and models by everything they declare, as the Python
compiler identifies them.

Trusted: with `Meaning`, `Contracts` and `Grades`, this decides what a certificate
says. See docs/proposals/lean-semantics.md.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

instance : DecidableEq FixedSampleDesign := fun a b =>
  decidable_of_iff (a.nControl = b.nControl ∧ a.nTreatment = b.nTreatment) (by
    cases a; cases b; simp)

/-- A two-arm model as declared: its outcome, its arm sizes, and whatever else the file
declares about the assignment and the outcome. -/
structure Model where
  outcome : Generated.OutcomeKind
  sizes : FixedSampleDesign
  /-- Clusters per arm, when whole clusters were assigned. -/
  clusters : Option (ℕ × ℕ) := none
  randomisation : Option String := none
  /-- Randomised units per arm in each stratum, when strata are declared. -/
  strata : List (ℕ × ℕ) := []
  blockSize : Option ℕ := none
  population : Option String := none
  better : Option String := none
  /-- Measurements per participant, when there is more than one. -/
  measurements : Option ℕ := none
  /-- The outcome's name, when the file gives one. -/
  name : Option String := none
  deriving DecidableEq

/-- How a design stops: at its fixed sizes, or by a rule that depends on the data. -/
inductive Stopping where
  | fixed
  | data_dependent
  deriving DecidableEq, Repr

structure Design where
  model : Model
  stopping : Stopping
  deriving DecidableEq

/-- A null form, the model it is about, and its value when the form takes one. -/
structure Null where
  key : Generated.NullKey
  model : Model
  value : Option ℚ := none
  deriving DecidableEq

/-- An observational study as declared: what its design fixed, the exposure and the
outcome, and how they were measured and sampled. A size the design does not fix is
absent, as in the canonical program. -/
structure Study where
  design : Generated.ObservationalDesign
  n : Option ℕ := none
  cases : Option ℕ := none
  controls : Option ℕ := none
  exposed : Option ℕ := none
  unexposed : Option ℕ := none
  pairs : Option ℕ := none
  exposure : String
  outcome : String
  exposureScale : Generated.Scale := .binary
  outcomeScale : Generated.Scale := .binary
  survey : Generated.Survey := .simple_random
  clusters : Option ℕ := none
  deriving DecidableEq

structure StudyDesign where
  model : Study
  stopping : Stopping
  deriving DecidableEq

/-- No association between a study's exposure and outcome: the only null of a study. -/
structure StudyNull where
  model : Study
  deriving DecidableEq

/-- Group sizes in the order used by the conditional table law. -/
def Study.groups (study : Study) : Option (ℕ × ℕ) :=
  match study.design with
  | .case_control => (·, ·) <$> study.controls <*> study.cases
  | .cohort => (·, ·) <$> study.unexposed <*> study.exposed
  | _ => none

def Study.groupSizes (study : Study) : FixedSampleDesign :=
  let sizes := study.groups.getD (0, 0)
  ⟨max 1 sizes.1, max 1 sizes.2, by omega, by omega⟩

inductive ExactStudyKind where
  | fisherGroups
  | fisherMixture
  | matched
  | incidence
  deriving DecidableEq

def ExactStudyKind.key : ExactStudyKind → String
  | .fisherGroups | .fisherMixture => "fisher_exact"
  | .matched => "mcnemar"
  | .incidence => "rate_test"

def ExactStudyKind.binding : ExactStudyKind → String
  | .fisherGroups | .fisherMixture => "AssociationAnalysisIR"
  | .matched => "MatchedAnalysisIR"
  | .incidence => "RateAnalysisIR"

/-- Where an assumed test's guarantee comes from: a method in the registry, or the
author's own declaration, with the scope and references the file gives. -/
inductive Guarantee where
  | cited (method : Generated.TrialMethod)
  | declared (method : String) (scope : Interface.Scope) (references : List String)

def Guarantee.scope : Guarantee → Interface.Scope
  | .cited method => method.scope
  | .declared _ scope _ => scope

inductive ExactKind where
  | fisherOneSided
  | margin (value : ℚ) (thresholds : List ℕ)
  | proportionZ (pooled : Bool) (squaredCutoff : ℚ)

abbrev ExactKind.wald (cutoff : ℚ) : ExactKind := .proportionZ false cutoff
abbrev ExactKind.score (cutoff : ℚ) : ExactKind := .proportionZ true cutoff

def ExactKind.key : ExactKind → String
  | .fisherOneSided => "fisher_one_sided"
  | .margin .. => "difference_test"
  | .proportionZ pooled _ => if pooled then "score_test" else "wald_test"

/-- A probability represented by the natural numbers used in the kernel checks, in
lowest terms, so its value determines it. -/
structure ProbabilityFraction where
  num : ℕ
  den : ℕ
  bounded : num ≤ den
  positive : 0 < den
  reduced : Nat.Coprime num den
  deriving DecidableEq

def ProbabilityFraction.value (p : ProbabilityFraction) : ℚ := (p.num : ℚ) / p.den

structure ObservedCounts where
  control : ℕ
  treatment : ℕ

structure ReportedResult where
  pValue : ProbabilityFraction
  reject : Bool

structure ReportedTable extends ReportedResult where
  mass : ProbabilityFraction

structure AssociationTable where
  model : Study
  exposedCases : ℕ
  exposedNoncases : ℕ
  unexposedCases : ℕ
  unexposedNoncases : ℕ

def AssociationTable.exposed (t : AssociationTable) : ℕ := t.exposedCases + t.exposedNoncases
def AssociationTable.unexposed (t : AssociationTable) : ℕ := t.unexposedCases + t.unexposedNoncases
def AssociationTable.total (t : AssociationTable) : ℕ := t.exposed + t.unexposed

def AssociationTable.sides (t : AssociationTable) : ℕ × ℕ × ObservedCounts :=
  if t.model.design = .case_control then
    (t.exposedNoncases + t.unexposedNoncases, t.exposedCases + t.unexposedCases,
      ⟨t.exposedNoncases, t.exposedCases⟩)
  else (t.unexposed, t.exposed, ⟨t.unexposedCases, t.exposedCases⟩)

structure PairCounts where
  model : Study
  both : ℕ
  caseOnly : ℕ
  controlOnly : ℕ
  neither : ℕ

def PairCounts.discordant (p : PairCounts) : ℕ := p.caseOnly + p.controlOnly
def PairCounts.total (p : PairCounts) : ℕ := p.both + p.discordant + p.neither

structure EventCounts where
  model : Study
  exposed : ℕ
  unexposed : ℕ
  exposedTime : ℚ
  unexposedTime : ℚ

def EventCounts.total (e : EventCounts) : ℕ := e.exposed + e.unexposed
def EventCounts.share (e : EventCounts) : ℚ := e.exposedTime / (e.exposedTime + e.unexposedTime)

structure ReportedTails extends ReportedResult where
  upper : ℕ
  lower : ℕ

inductive StageRule where
  | threshold (interim final : ℕ)
  | posterior (priorA priorB : ℕ) (reference interim final : ProbabilityFraction)
  deriving DecidableEq

structure Stages where
  first : ℕ
  second : ℕ
  deriving DecidableEq

inductive ResultData where
  | fisher (observed : ObservedCounts) (reported : ReportedTable) (low high : ℕ)
      (bound : ProbabilityFraction)
  | margin (observed : ObservedCounts) (reject : Bool) (bound : ProbabilityFraction)
      (gridded : ℚ)
  | association (observed : AssociationTable) (reported : ReportedTable)
  | matched (observed : PairCounts) (reported : ReportedTails)
  | rate (observed : EventCounts) (share : ProbabilityFraction) (reported : ReportedTails)
  | oneSample (responses critical : ℕ) (reported : ReportedResult)
  | twoStage (first : ℕ) (second : Option ℕ) (continued reject : Bool) (bound : ProbabilityFraction)

structure Endpoints where
  lower : ProbabilityFraction
  upper : ProbabilityFraction

inductive IntervalData where
  | binomial (n x : ℕ) (level tail : ProbabilityFraction) (endpoints : Endpoints)
  | proportion (study : Study) (measure : String) (group : Option String) (cases : ℕ) (level tail : ProbabilityFraction)
      (endpoints : Endpoints)
  | difference (model : Model) (observed : ObservedCounts) (level tail : ProbabilityFraction)
      (control treatment : Endpoints)
  | association (table : AssociationTable) (measure : String) (level tail : ProbabilityFraction)
      (control treatment : Endpoints)
  | matched (pairs : PairCounts) (level tail : ProbabilityFraction) (endpoints : Endpoints)
  | rate (events : EventCounts) (level tail : ProbabilityFraction) (endpoints : Endpoints)

structure BinomialPoint where
  control : ProbabilityFraction
  treatment : ProbabilityFraction

structure Randomised where
  design : Design
  nullModel : Model
  alpha : SignificanceLevel
  draws : Option ℕ

def Randomised.sizes (r : Randomised) : ℕ × ℕ :=
  let model := r.design.model
  model.clusters.getD (model.sizes.nControl, model.sizes.nTreatment)

def Randomised.parts (r : Randomised) : List (ℕ × ℕ) :=
  if r.design.model.strata.isEmpty then [r.sizes] else r.design.model.strata

def Randomised.groups (r : Randomised) : List (ℕ × ℕ) :=
  match r.design.model.blockSize with
  | none => r.parts.map (fun (c, t) => (c + t, t))
  | some block => r.parts.flatMap (fun (c, t) =>
      List.replicate ((c + t) / block) (block, t * block / (c + t)))

inductive Test where
  | fisher (name : String) (design : Design) (null : Null) (alpha : SignificanceLevel)
  | exact (name : String) (kind : ExactKind) (design : Design) (null : Null)
      (alpha : SignificanceLevel)
  | exactStudy (name : String) (kind : ExactStudyKind) (design : StudyDesign) (null : StudyNull)
      (alpha : SignificanceLevel)
  | randomised (name : String) (test : Randomised)
  | oneSample (name : String) (n : ℕ) (nullRate alpha : ProbabilityFraction)
  | twoStage (name : String) (stages : Stages) (rule : StageRule) (nullRate : ProbabilityFraction)
  /-- A conditional composition supplies a view and level premise for this test. -/
  | member (test : Test)
  /-- A test whose level is a premise: cited from the registry or declared by the author. -/
  | assumed (name : String) (guarantee : Guarantee) (design : Design) (null : Null)
      (alpha : SignificanceLevel)
  /-- A cited test of association in an observational study, adjusted for the listed
  covariates. -/
  | associated (name : String) (method : Generated.AssociationMethod) (design : StudyDesign)
      (null : StudyNull) (alpha : SignificanceLevel) (adjusted : List String)
  /-- A family at shares of the level. A family of Fisher tests records the joint law it
  declares (`binomial_marginals`); its claim holds whatever the joint law, so the
  meaning reads nothing from it. -/
  | bonferroni (name : String) (members : List Test) (alpha : SignificanceLevel)
      (joint : Option String)
  /-- A design with looks: one question asked at growing sizes, each look at its share. -/
  | looks (name : String) (members : List Test) (alpha : SignificanceLevel)
  /-- A combination by a cited procedure from the generated registry: a graphical procedure,
  or boundaries from an error-spending function. The semantics cites the procedure's
  guarantee and does not compute it; `rule` says what the contracts read. Only a graph
  takes `weights` and `transitions`. -/
  | procedure (name : String) (rule : Generated.Procedure) (members : List Test)
      (alpha : SignificanceLevel) (weights : List ℚ) (transitions : List (List ℚ))
  | sequence (name : String) (members : List Test) (alpha : SignificanceLevel)

inductive PlanningPoint where
  | arms (point : BinomialPoint)
  | response (rate : ProbabilityFraction)
  | association (firstKey secondKey : String) (point : BinomialPoint)
      (exposed : Option ProbabilityFraction)
  | matched (discordant : ProbabilityFraction) (odds : ℚ) (caseShare : ProbabilityFraction)
  | rate (ratio exposedTime unexposedTime : ℚ) (events : Option ℕ)
      (nullShare alternativeShare : ProbabilityFraction)

structure PlanningTarget where
  point : PlanningPoint
  power : ProbabilityFraction
  error : ProbabilityFraction

structure SearchRange where
  low : ℕ
  high : ℕ
  ratio : ℕ
  positive : 0 < ratio
  minimal : Bool

inductive SearchKind where
  | arms | groups | total | pairs | events | oneSample

inductive PlanQuery where
  | meets (test : Test)
  | search (test : Test) (kind : SearchKind) (range : SearchRange)
  | stageSearch (reference : ProbabilityFraction) (maxTotal : ℕ) (criterion : String)

def PlanQuery.test : PlanQuery → Option Test
  | .meets t | .search t .. => some t
  | .stageSearch .. => none

inductive PlanSelection where
  | arms (sizes : FixedSampleDesign)
  | oneSample (n critical : ℕ)
  | stages (sizes : Stages) (rule : StageRule)
  | count (n : ℕ)

inductive Request where
  | typeI (test : Test)
  | familywise (test : Test)
  | result (name : String) (test : Test) (observed : ObservedCounts) (reported : ReportedResult)
  | checkedResult (name : String) (test : Test) (data : ResultData)
  | interval (name : String) (data : IntervalData)
  | planned (name : String) (query : PlanQuery) (target : PlanningTarget)
      (selected : Option PlanSelection)

/-- A program's `verify` requests, in order, and every test and combination it declares,
in the order of its bindings. -/
structure Program where
  requests : List Request
  declarations : List Test

def Request.test : Request → Option Test
  | .typeI t | .familywise t => some t
  | .result _ t .. | .checkedResult _ t .. => some t
  | .interval .. => none
  | .planned _ q .. => q.test

def Test.name : Test → String
  | .fisher name .. => name
  | .exact name .. => name
  | .exactStudy name .. => name
  | .randomised name .. => name
  | .oneSample name .. | .twoStage name .. => name
  | .member test => test.name
  | .assumed name .. => name
  | .associated name .. => name
  | .bonferroni name .. => name
  | .looks name .. => name
  | .procedure name .. => name
  | .sequence name .. => name

def Request.name : Request → String
  | .result name .. | .checkedResult name .. | .interval name .. => name
  | .planned name .. => name
  | .typeI t | .familywise t => t.name

def Test.level : Test → SignificanceLevel
  | .fisher _ _ _ alpha => alpha
  | .exact _ _ _ _ alpha => alpha
  | .exactStudy _ _ _ _ alpha => alpha
  | .randomised _ r => r.alpha
  | .oneSample .. | .twoStage .. => defaultLevel
  | .member test => test.level
  | .assumed _ _ _ _ alpha => alpha
  | .associated _ _ _ _ alpha _ => alpha
  | .bonferroni _ _ alpha _ => alpha
  | .looks _ _ alpha => alpha
  | .procedure _ _ _ alpha _ _ => alpha
  | .sequence _ _ alpha => alpha

def Test.alpha (t : Test) : ℚ := t.level.value

end StatClaim.Semantics
