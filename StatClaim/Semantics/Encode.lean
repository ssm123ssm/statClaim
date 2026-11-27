module

public import StatClaim.Semantics.Syntax
public import Lean.Data.Json

/-!
The canonical form of a program's data: the claims of its `verify` requests, as the
canonical program a certificate binds writes them. A build prints it, and the audit
compares it with the certificate's program, so the data Python wrote is the program
the certificate is about.

The data is first written as a `Form`, a JSON value whose objects list their keys in
increasing order. `Injective.lean` proves that two programs in canonical form never have
the same form, and the printer refuses an object whose keys are out of order, so two
different printed objects are never the same JSON object.

Trusted: it decides which program a certificate's statements are about. The printer
runs in Lean's interpreter, as the premise collector does, not in the kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open Lean (Json)

/-- A JSON value as the encoder builds it. An object lists its entries in order. -/
inductive Form where
  | null
  | bool (b : Bool)
  | nat (n : ℕ)
  | str (s : String)
  | arr (items : List Form)
  | obj (fields : List (String × Form))

/-- An object from its entries in order; an entry without a value is left out. -/
def Form.object (entries : List (String × Option Form)) : Form :=
  .obj (entries.filterMap fun (key, value) => value.map (key, ·))

/-- A rational as Python's `str(Fraction)` writes it: `-1/10`, `3`, `0`. -/
def ratString (q : ℚ) : String :=
  if q.den = 1 then toString q.num else toString q.num ++ "/" ++ toString q.den

def Form.rat (q : ℚ) : Form := .str (ratString q)

def Form.prob (p : ProbabilityFraction) : Form := .rat p.value

def Form.level (a : SignificanceLevel) : Form := .rat a.value

/-- Whether an object's keys increase strictly, as the printer requires. -/
def keysIncrease : List (String × Form) → Bool
  | [] | [_] => true
  | (a, _) :: (b, v) :: rest => decide (a < b) && keysIncrease ((b, v) :: rest)

mutual
/-- The JSON of a form, or `none` when an object's keys are out of order. -/
def Form.json? : Form → Option Json
  | .null => some .null
  | .bool b => some (.bool b)
  | .nat n => some (Lean.toJson n)
  | .str s => some (.str s)
  | .arr items => (Form.jsonItems? items).map fun js => Json.arr js.toArray
  | .obj fields =>
    if keysIncrease fields then (Form.jsonFields? fields).map Json.mkObj else none

def Form.jsonItems? : List Form → Option (List Json)
  | [] => some []
  | f :: fs => do
    let j ← Form.json? f
    let js ← Form.jsonItems? fs
    pure (j :: js)

def Form.jsonFields? : List (String × Form) → Option (List (String × Json))
  | [] => some []
  | (k, f) :: fs => do
    let j ← Form.json? f
    let js ← Form.jsonFields? fs
    pure ((k, j) :: js)
end

def Model.form (model : Model) : Form :=
  .object [("better", model.better.map .str), ("block_size", model.blockSize.map .nat),
    ("clusters_control", model.clusters.map (.nat ·.1)),
    ("clusters_treatment", model.clusters.map (.nat ·.2)),
    ("measurements", model.measurements.map .nat),
    ("module", some (.str model.outcome.constructor)),
    ("n_control", some (.nat model.sizes.nControl)),
    ("n_treatment", some (.nat model.sizes.nTreatment)),
    ("outcome_name", model.name.map .str), ("population", model.population.map .str),
    ("randomisation", model.randomisation.map .str),
    ("strata", if model.strata.isEmpty then none else
      some (.arr (model.strata.map fun (control, treatment) => .arr [.nat control, .nat treatment])))]

def Study.form (study : Study) : Form :=
  .object [("cases", study.cases.map .nat), ("clusters", study.clusters.map .nat),
    ("controls", study.controls.map .nat), ("exposed", study.exposed.map .nat),
    ("exposure", some (.str study.exposure)),
    ("exposure_scale", if study.exposureScale = .binary then none else
      some (.str study.exposureScale.key)),
    ("n", study.n.map .nat), ("outcome", some (.str study.outcome)),
    ("outcome_scale", if study.outcomeScale = .binary then none else
      some (.str study.outcomeScale.key)),
    ("pairs", study.pairs.map .nat), ("study", some (.str study.design.key)),
    ("survey", if study.survey = .simple_random then none else some (.str study.survey.key)),
    ("unexposed", study.unexposed.map .nat)]

def Stopping.form : Stopping → Form
  | .fixed => .str "fixed"
  | .data_dependent => .str "data_dependent"

def Design.form (design : Design) : Form :=
  .object [("model", some design.model.form), ("stopping", some design.stopping.form)]

def StudyDesign.form (design : StudyDesign) : Form :=
  .object [("model", some design.model.form), ("stopping", some design.stopping.form)]

def StudyNull.form (null : StudyNull) : Form :=
  .object [("model", some null.model.form), ("predicate", some (.str "no_association"))]

def Null.form (null : Null) : Form :=
  .object [("model", some null.model.form), ("predicate", some (.str null.key.key)),
    ("value", null.value.map .rat)]

def scopeForm : Interface.Scope → Form
  | .finiteSample => .str "finite_sample"
  | .largeSample => .str "asymptotic"

def Stages.form (s : Stages) : Form :=
  .object [("module", some (.str "two_stage_binomial")), ("n_stage1", some (.nat s.first)),
    ("n_stage2", some (.nat s.second))]

def StageRule.form : StageRule → Form
  | .threshold interim final => .object [("continue_above", some (.nat interim)),
      ("kind", some (.str "threshold")), ("reject_above", some (.nat final))]
  | .posterior a b reference interim final => .object [
      ("continue_at_least", some (.prob interim)), ("kind", some (.str "posterior")),
      ("prior_a", some (.nat a)), ("prior_b", some (.nat b)), ("reference", some (.prob reference)),
      ("success_at_least", some (.prob final))]

def oneArmForm (n : ℕ) : Form :=
  .object [("module", some (.str "one_arm_binomial")), ("n", some (.nat n))]

/-- A cited procedure's constant entries: its method and what names it within the method. -/
def _root_.StatClaim.Generated.Procedure.entries (rule : Generated.Procedure) : List (String × Option Form) :=
  rule.fields.map fun (key, value) => (key, some (.str value))

mutual
def Test.form : Test → Form
  | .fisher _ design null alpha => .object [("alpha", some (.level alpha)),
      ("design", some design.form), ("null", some null.form), ("test", some (.str "fisher"))]
  | .exact _ (.proportionZ pooled cutoff) design null alpha => .object [("alpha", some (.level alpha)),
      ("design", some design.form), ("null", some null.form), ("squared_cutoff", some (.rat cutoff)),
      ("test", some (.str (ExactKind.proportionZ pooled cutoff).key))]
  | .exact _ kind design null alpha => .object [("alpha", some (.level alpha)),
      ("alternative", some (.str
        (match kind with | .fisherOneSided => "greater" | _ => "margin"))),
      ("design", some design.form), ("null", some null.form), ("test", some (.str "fisher"))]
  | .exactStudy _ kind design null alpha => .object [("alpha", some (.level alpha)),
      ("design", some design.form), ("null", some null.form), ("test", some (.str kind.key))]
  | .randomised _ r => .object [("alpha", some (.level r.alpha)),
      ("design", some r.design.form), ("draws", r.draws.map .nat),
      ("null", some (.object [("model", some r.nullModel.form),
        ("predicate", some (.str "no_effect"))])),
      ("test", some (.str "randomisation"))]
  | .member t => Test.form t
  | .oneSample _ n reference alpha => .object [("alpha", some (.prob alpha)),
      ("model", some (oneArmForm n)), ("null_rate", some (.prob reference)),
      ("test", some (.str "binomial_exact_one_sided"))]
  | .twoStage _ stages rule reference => .object [("design", some stages.form),
      ("null_rate", some (.prob reference)), ("rule", some rule.form),
      ("test", some (.str "two_stage"))]
  | .assumed _ (.cited method) design null alpha => .object [("alpha", some (.level alpha)),
      ("design", some design.form), ("null", some null.form), ("test", some (.str method.key))]
  | .assumed _ (.declared method scope references) design null alpha => .object [
      ("alpha", some (.level alpha)), ("design", some design.form),
      ("method", some (.str method)), ("null", some null.form),
      ("references", some (.arr (references.map .str))), ("scope", some (scopeForm scope)),
      ("test", some (.str "declared_test"))]
  | .associated _ method design null alpha adjusted => .object [
      ("adjusted_for", if adjusted.isEmpty then none else some (.arr (adjusted.map .str))),
      ("alpha", some (.level alpha)), ("design", some design.form), ("null", some null.form),
      ("test", some (.str method.key))]
  | .bonferroni _ members alpha none => .object [("alpha", some (.level alpha)),
      ("analyses", some (.arr (Test.formMembers members))),
      ("composition", some (.str "conditional")), ("method", some (.str "bonferroni"))]
  | .bonferroni _ members alpha (some joint) => .object [("alpha", some (.level alpha)),
      ("analyses", some (.arr (Test.formMembers members))), ("joint_law", some (.str joint)),
      ("method", some (.str "bonferroni"))]
  | .looks _ members alpha => .object [("alpha", some (.level alpha)),
      ("analyses", some (.arr (Test.formMembers members))),
      ("composition", some (.str "conditional")), ("method", some (.str "alpha_spending"))]
  | .procedure _ rule members alpha weights rows => .object ([("alpha", some (.level alpha)),
      ("analyses", some (.arr (Test.formMembers members))),
      ("composition", some (.str "conditional"))] ++ rule.entries ++
      [("transitions", if rule.graph then some (.arr (rows.map fun row => .arr (row.map .rat)))
        else none),
       ("weights", if rule.graph then some (.arr (weights.map .rat)) else none)])
  | .sequence _ members alpha => .object [("alpha", some (.level alpha)),
      ("analyses", some (.arr (Test.formMembers members))),
      ("composition", some (.str "conditional")), ("method", some (.str "fixed_sequence"))]
termination_by structural t => t

/-- A combination's members, each with its name. -/
def Test.formMembers : List Test → List Form
  | [] => []
  | t :: ts =>
    .object [("analysis", some (Test.form t)), ("name", some (.str t.name))] :: Test.formMembers ts
termination_by structural ts => ts
end

def ObservedCounts.fields (o : ObservedCounts) : List (String × Option Form) :=
  [("control_successes", some (.nat o.control)), ("treatment_successes", some (.nat o.treatment))]

def AssociationTable.form (o : AssociationTable) : Form :=
  .object [("exposed_cases", some (.nat o.exposedCases)),
    ("exposed_noncases", some (.nat o.exposedNoncases)), ("model", some o.model.form),
    ("unexposed_cases", some (.nat o.unexposedCases)),
    ("unexposed_noncases", some (.nat o.unexposedNoncases))]

def PairCounts.form (o : PairCounts) : Form :=
  .object [("both_exposed", some (.nat o.both)), ("case_exposed_only", some (.nat o.caseOnly)),
    ("control_exposed_only", some (.nat o.controlOnly)), ("model", some o.model.form),
    ("neither_exposed", some (.nat o.neither))]

def EventCounts.form (o : EventCounts) : Form :=
  .object [("exposed_events", some (.nat o.exposed)), ("exposed_time", some (.rat o.exposedTime)),
    ("model", some o.model.form), ("unexposed_events", some (.nat o.unexposed)),
    ("unexposed_time", some (.rat o.unexposedTime))]

/-- A result's subject: the analysis and the observed data. -/
def ResultData.subject (analysis : Form) : ResultData → Form
  | .fisher o .. | .margin o .. => .object (("analysis", some analysis) :: o.fields)
  | .association table _ => .object [("analysis", some analysis), ("table", some table.form)]
  | .matched pairs _ => .object [("analysis", some analysis), ("pairs", some pairs.form)]
  | .rate events _ _ => .object [("analysis", some analysis), ("events", some events.form)]
  | .oneSample responses .. => .object [("analysis", some analysis),
      ("responses", some (.nat responses))]
  | .twoStage first second .. => .object [("analysis", some analysis),
      ("stage1_responses", some (.nat first)),
      ("stage2_responses", some ((second.map Form.nat).getD .null))]

def ResultData.reported : ResultData → Form
  | .fisher _ r low high _ => .object [("observed_table_probability", some (.prob r.mass)),
      ("p_value", some (.prob r.pValue)), ("reject_null", some (.bool r.reject)),
      ("support_max", some (.nat high)), ("support_min", some (.nat low))]
  | .margin _ reject .. => .object [("reject_null", some (.bool reject))]
  | .association _ r => .object [("observed_table_probability", some (.prob r.mass)),
      ("p_value", some (.prob r.pValue)), ("reject_null", some (.bool r.reject))]
  | .matched _ r | .rate _ _ r => .object [("lower_tail", some (.nat r.lower)),
      ("p_value", some (.prob r.pValue)), ("reject_null", some (.bool r.reject)),
      ("upper_tail", some (.nat r.upper))]
  | .oneSample _ critical r => .object [("critical_value", some (.nat critical)),
      ("p_value", some (.prob r.pValue)), ("reject_null", some (.bool r.reject))]
  | .twoStage _ _ continued reject bound => .object [("continued", some (.bool continued)),
      ("reject_null", some (.bool reject)), ("typeI_bound", some (.prob bound))]

def IntervalData.form : IntervalData → Form
  | .binomial n x level .. => .object [("level", some (.prob level)),
      ("model", some (oneArmForm n)), ("responses", some (.nat x))]
  | .proportion study measure group cases level .. => .object [("cases", some (.nat cases)),
      ("group", group.map .str), ("level", some (.prob level)), ("measure", some (.str measure)),
      ("model", some study.form)]
  | .difference model observed level .. => .object [
      ("control_successes", some (.nat observed.control)), ("level", some (.prob level)),
      ("model", some model.form), ("treatment_successes", some (.nat observed.treatment))]
  | .association table measure level .. => .object [("level", some (.prob level)),
      ("measure", some (.str measure)), ("table", some table.form)]
  | .matched pairs level .. => .object [("level", some (.prob level)), ("pairs", some pairs.form)]
  | .rate events level .. => .object [("events", some events.form), ("level", some (.prob level))]

def oddsRat (q : ℚ) : ℚ := q / (1 - q)

def Endpoints.form (ends : Endpoints) : Form := .arr [.prob ends.lower, .prob ends.upper]

def twoIntervalOutputs (measure : String) (tail : ProbabilityFraction) (c t : Endpoints) : Form :=
  let cl := c.lower.value
  let cu := c.upper.value
  let tl := t.lower.value
  let tu := t.upper.value
  let (lower, upper) :=
    if measure == "odds_ratio" then
      (if cu < 1 then oddsRat tl / oddsRat cu else 0,
        if 0 < cl && tu < 1 then some (oddsRat tu / oddsRat cl) else none)
    else if measure == "risk_ratio" || measure == "prevalence_ratio" then
      (tl / cu, if 0 < cl then some (tu / cl) else none)
    else (tl - cu, some (tu - cl))
  .object [("control", some c.form), ("lower", some (.rat lower)), ("tail", some (.prob tail)),
    ("treatment", some t.form), ("upper", some ((upper.map Form.rat).getD .null))]

def oneIntervalOutputs (tail : ProbabilityFraction) (lower : ℚ) (upper : Option ℚ)
    (arm : Option Endpoints) : Form :=
  .object [("arm", arm.map Endpoints.form), ("lower", some (.rat lower)),
    ("tail", some (.prob tail)), ("upper", some ((upper.map Form.rat).getD .null))]

def IntervalData.reported : IntervalData → Form
  | .binomial _ _ _ tail e | .proportion _ _ _ _ _ tail e =>
    oneIntervalOutputs tail e.lower.value (some e.upper.value) none
  | .difference _ _ _ tail c t => twoIntervalOutputs "difference" tail c t
  | .association _ measure _ tail c t => twoIntervalOutputs measure tail c t
  | .matched _ _ tail e =>
    oneIntervalOutputs tail (oddsRat e.lower.value)
      (if e.upper.value < 1 then some (oddsRat e.upper.value) else none) (some e)
  | .rate events _ tail e =>
    let scale := events.unexposedTime / events.exposedTime
    oneIntervalOutputs tail (oddsRat e.lower.value * scale)
      (if e.upper.value < 1 then some (oddsRat e.upper.value * scale) else none) (some e)

/-- A planning point. The keys of a study's point are its own; the canonical form lists
the treatment or exposed one first, as their names sort. -/
def PlanningPoint.form : PlanningPoint → Form
  | .arms point => .object [("p_control", some (.prob point.control)),
      ("p_treatment", some (.prob point.treatment))]
  | .response r => .object [("response_rate", some (.prob r))]
  | .association first second point exposed => .object [("exposed_share", exposed.map .prob),
      (second, some (.prob point.treatment)), (first, some (.prob point.control))]
  | .matched discordant odds _ => .object [("discordant", some (.prob discordant)),
      ("odds_ratio", some (.rat odds))]
  | .rate ratio exposedTime unexposedTime events .. => .object [("events", events.map .nat),
      ("exposed_time", some (.rat exposedTime)), ("rate_ratio", some (.rat ratio)),
      ("unexposed_time", some (.rat unexposedTime))]

def PlanningTarget.form (target : PlanningTarget) : Form :=
  .object [("at", some target.point.form), ("maximum_typeI", some (.prob target.error)),
    ("minimum_power", some (.prob target.power))]

def PlanSelection.form : PlanSelection → Form
  | .arms sizes => .object [("n_control", some (.nat sizes.nControl)),
      ("n_treatment", some (.nat sizes.nTreatment))]
  | .oneSample n critical => .object [("critical_value", some (.nat critical)), ("n", some (.nat n))]
  | .count n => .object [("n", some (.nat n))]
  | .stages sizes rule => .object [("n_stage1", some (.nat sizes.first)),
      ("n_stage2", some (.nat sizes.second)), ("rule", some rule.form)]

/-- Whether a search's analysis is about a cohort, whose groups are the exposed. -/
def Test.isCohort : Test → Bool
  | .exactStudy _ _ design .. => design.model.design == .cohort
  | _ => false

def allocationString (ratio : ℕ) : String :=
  if ratio = 1 then "equal_arms" else "1:" ++ toString ratio

/-- The candidates of a size search: the analysis and the range searched. -/
def SearchKind.form (kind : SearchKind) (t : Test) (range : SearchRange) : Form :=
  let analysis := ("analysis", some t.form)
  match kind with
  | .arms => .object [("allocation", some (.str (allocationString range.ratio))), analysis,
      ("max_per_arm", some (.nat range.high)), ("min_per_arm", some (.nat range.low))]
  | .groups =>
    if t.isCohort then .object [analysis, ("max_exposed", some (.nat range.high)),
      ("min_exposed", some (.nat range.low)), ("unexposed_per_exposed", some (.nat range.ratio))]
    else .object [analysis, ("controls_per_case", some (.nat range.ratio)),
      ("max_cases", some (.nat range.high)), ("min_cases", some (.nat range.low))]
  | .total | .oneSample => .object [analysis, ("max_n", some (.nat range.high)),
      ("min_n", some (.nat range.low))]
  | .pairs => .object [analysis, ("max_pairs", some (.nat range.high)),
      ("min_pairs", some (.nat range.low))]
  | .events => .object [analysis, ("max_events", some (.nat range.high)),
      ("min_events", some (.nat range.low))]

/-- A planning request's kind and subject. -/
def PlanQuery.form (q : PlanQuery) (target : PlanningTarget) : String × Form :=
  match q with
  | .meets t => ("meets", .object [("analysis", some t.form), ("target", some target.form)])
  | .search t kind range => ("sample_size", .object [("candidates", some (kind.form t range)),
      ("claim", some (.str (if range.minimal then "smallest_in_range" else "sufficient"))),
      ("target", some target.form)])
  | .stageSearch reference maxTotal criterion => ("sample_size", .object [
      ("candidates", some (.object [("criterion", some (.str criterion)),
        ("design", some (.str "two_stage_threshold")), ("max_total", some (.nat maxTotal)),
        ("null_rate", some (.prob reference))])),
      ("claim", some (.str "sufficient")), ("target", some target.form)])

def Request.form (request : Request) : Form :=
  let (kind, subject) : String × Form := match request with
    | .typeI t => ("typeI", t.form)
    | .familywise t => ("familywise", t.form)
    | .result _ t observed _ => ("result", .object (("analysis", some t.form) :: observed.fields))
    | .checkedResult _ t d => ("result", d.subject t.form)
    | .interval _ d => ("interval", d.form)
    | .planned _ q target _ => q.form target
  .object [("kind", some (.str kind)), ("subject", some subject),
    ("subject_name", some (.str request.name))]

def Request.reported : Request → Option Form
  | .result _ _ _ found => some (.object [("p_value", some (.prob found.pValue)),
      ("reject_null", some (.bool found.reject))])
  | .checkedResult _ _ d => some d.reported
  | .interval _ d => some d.reported
  | .planned _ _ _ selected => selected.map PlanSelection.form
  | _ => none

/-- The type of the binding that declares a test. -/
def Test.binding : Test → String
  | .fisher .. => "AnalysisIR"
  | .exact _ (.proportionZ pooled _) .. => if pooled then "ScoreAnalysisIR" else "WaldAnalysisIR"
  | .exact .. => "AnalysisIR"
  | .exactStudy _ kind .. => kind.binding
  | .randomised .. => "RandomisationAnalysisIR"
  | .member t => t.binding
  | .oneSample .. => "OneSampleAnalysisIR"
  | .twoStage .. => "TwoStageAnalysisIR"
  | .assumed .. => "CitedAnalysisIR"
  | .associated .. => "CitedAssociationIR"
  | .bonferroni _ _ _ (some _) => "FamilyIR"
  | .looks .. => "SequentialIR"
  | .procedure _ rule .. =>
    match rule.question with
    | .looks => "SequentialIR"
    | .family => "ComposedFamilyIR"
  | _ => "ComposedFamilyIR"

mutual
/-- The rejection thresholds of the tests with a margin, each with its test's name. -/
def Test.thresholds : Test → List Form
  | .exact name (.margin _ thresholds) .. =>
    [.object [("name", some (.str name)), ("thresholds", some (.arr (thresholds.map .nat)))]]
  | .member t => Test.thresholds t
  | .bonferroni _ members .. | .looks _ members .. | .procedure _ _ members ..
  | .sequence _ members .. => Test.allThresholds members
  | _ => []
termination_by structural t => t

def Test.allThresholds : List Test → List Form
  | [] => []
  | t :: ts => t.thresholds ++ Test.allThresholds ts
termination_by structural ts => ts
end

def Test.declaration (t : Test) : Form :=
  .object [("name", some (.str t.name)), ("type", some (.str t.binding)), ("value", some t.form)]

/-- The claims and reported outputs of the `verify` requests, in order, and the declarations. -/
def Program.form (program : Program) : Form :=
  let outputs := program.requests.map Request.reported
  let thresholds := Test.allThresholds program.declarations ++
    Test.allThresholds (program.requests.filterMap Request.test)
  .object [("claims", some (.arr (program.requests.map Request.form))),
    ("declarations", some (.arr (program.declarations.map Test.declaration))),
    ("rejection_thresholds", if thresholds.isEmpty then none else some (.arr thresholds)),
    ("reported", if outputs.any Option.isSome then some (.arr (outputs.map (·.getD .null)))
      else none)]

/-- The printed form, or `null` when an object's keys are out of order, which no canonical
program matches. -/
def Program.encode (program : Program) : Json :=
  program.form.json?.getD .null

end StatClaim.Semantics
