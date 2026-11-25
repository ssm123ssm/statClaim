module

public import StatClaim.Semantics.Syntax
public import Lean.Data.Json

/-!
The canonical form of a program's data: the claims of its `verify` requests, as the
canonical program a certificate binds writes them. A build prints it, and the audit
compares it with the certificate's program, so the data Python wrote is the program
the certificate is about.

Every field of the data is written, and an optional one exactly when it is present, so
two different programs never print the same form.

Trusted: it decides which program a certificate's statements are about. It runs in
Lean's interpreter, as the premise collector does, not in the kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open Lean (Json ToJson toJson)

/-- A rational as Python's `str(Fraction)` writes it: `-1/10`, `3`, `0`. -/
def ratString (q : ℚ) : String :=
  if q.den = 1 then toString q.num else toString q.num ++ "/" ++ toString q.den

def ratJson (q : ℚ) : Json :=
  Json.str (ratString q)

/-- The entries an optional field adds: none when it is absent. -/
def optional {α : Type} (key : String) (encode : α → Json) : Option α → List (String × Json)
  | some value => [(key, encode value)]
  | none => []

def Model.encode (model : Model) : Json :=
  Json.mkObj <|
    [("module", Json.str model.outcome.constructor),
      ("n_control", toJson model.sizes.nControl),
      ("n_treatment", toJson model.sizes.nTreatment)] ++
    (match model.clusters with
      | some (control, treatment) =>
        [("clusters_control", toJson control), ("clusters_treatment", toJson treatment)]
      | none => []) ++
    optional "randomisation" Json.str model.randomisation ++
    (match model.strata with
      | [] => []
      | strata =>
        [("strata", Json.arr (strata.map fun (control, treatment) =>
          Json.arr #[toJson control, toJson treatment]).toArray)]) ++
    optional "block_size" toJson model.blockSize ++
    optional "population" Json.str model.population ++
    optional "better" Json.str model.better ++
    optional "measurements" toJson model.measurements ++
    optional "outcome_name" Json.str model.name

def Study.encode (study : Study) : Json :=
  Json.mkObj <|
    [("study", Json.str study.design.key)] ++
    optional "n" toJson study.n ++ optional "cases" toJson study.cases ++
    optional "controls" toJson study.controls ++ optional "exposed" toJson study.exposed ++
    optional "unexposed" toJson study.unexposed ++ optional "pairs" toJson study.pairs ++
    [("exposure", Json.str study.exposure), ("outcome", Json.str study.outcome)] ++
    (if study.exposureScale = .binary then [] else
      [("exposure_scale", Json.str study.exposureScale.key)]) ++
    (if study.outcomeScale = .binary then [] else
      [("outcome_scale", Json.str study.outcomeScale.key)]) ++
    (if study.survey = .simple_random then [] else [("survey", Json.str study.survey.key)]) ++
    optional "clusters" toJson study.clusters

def Stopping.encode : Stopping → Json
  | .fixed => Json.str "fixed"
  | .data_dependent => Json.str "data_dependent"

def Design.encode (design : Design) : Json :=
  Json.mkObj [("model", design.model.encode), ("stopping", design.stopping.encode)]

def StudyDesign.encode (design : StudyDesign) : Json :=
  Json.mkObj [("model", design.model.encode), ("stopping", design.stopping.encode)]

def StudyNull.encode (null : StudyNull) : Json :=
  Json.mkObj [("predicate", Json.str "no_association"), ("model", null.model.encode)]

def Null.encode (null : Null) : Json :=
  Json.mkObj <|
    [("predicate", Json.str null.key.key), ("model", null.model.encode)] ++
    optional "value" ratJson null.value

/-- A test written as an analysis: its fields, without its name. -/
def analysis (test : String) (design : Design) (null : Null) (alpha : SignificanceLevel) : Json :=
  Json.mkObj [("test", Json.str test), ("design", design.encode), ("null", null.encode),
    ("alpha", ratJson alpha.value)]

/-- A combination's fields. Python writes every combination as conditional. -/
def combination (method : String) (alpha : SignificanceLevel) (members : Json)
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj <|
    [("method", Json.str method), ("composition", Json.str "conditional"),
      ("alpha", ratJson alpha.value), ("analyses", members)] ++ extra

def scopeJson : Interface.Scope → Json
  | .finiteSample => Json.str "finite_sample"
  | .largeSample => Json.str "asymptotic"

/-- An assumed test: a cited one names its registry method; a declared one is described
by the file. -/
def assumedJson (guarantee : Guarantee) (design : Design) (null : Null) (alpha : SignificanceLevel) :
    Json :=
  match guarantee with
  | .cited method => analysis method.key design null alpha
  | .declared method scope references =>
    (analysis "declared_test" design null alpha).mergeObj
      (Json.mkObj [("method", Json.str method), ("scope", scopeJson scope),
        ("references", Json.arr (references.map Json.str).toArray)])

def Stages.encode (s : Stages) : Json :=
  Json.mkObj [("module", Json.str "two_stage_binomial"), ("n_stage1", toJson s.first),
    ("n_stage2", toJson s.second)]

def StageRule.encode : StageRule → Json
  | .threshold interim final => Json.mkObj [("kind", Json.str "threshold"),
      ("continue_above", toJson interim), ("reject_above", toJson final)]
  | .posterior a b reference interim final => Json.mkObj [("kind", Json.str "posterior"),
      ("prior_a", toJson a), ("prior_b", toJson b), ("reference", ratJson reference.value),
      ("continue_at_least", ratJson interim.value), ("success_at_least", ratJson final.value)]

def ObservedCounts.fields (o : ObservedCounts) : List (String × Json) :=
  [("control_successes", toJson o.control), ("treatment_successes", toJson o.treatment)]

def AssociationTable.encode (o : AssociationTable) : Json :=
  Json.mkObj [("model", o.model.encode), ("exposed_cases", toJson o.exposedCases),
    ("exposed_noncases", toJson o.exposedNoncases), ("unexposed_cases", toJson o.unexposedCases),
    ("unexposed_noncases", toJson o.unexposedNoncases)]

def PairCounts.encode (o : PairCounts) : Json :=
  Json.mkObj [("model", o.model.encode), ("both_exposed", toJson o.both),
    ("case_exposed_only", toJson o.caseOnly), ("control_exposed_only", toJson o.controlOnly),
    ("neither_exposed", toJson o.neither)]

def EventCounts.encode (o : EventCounts) : Json :=
  Json.mkObj [("model", o.model.encode), ("exposed_events", toJson o.exposed),
    ("unexposed_events", toJson o.unexposed), ("exposed_time", ratJson o.exposedTime),
    ("unexposed_time", ratJson o.unexposedTime)]

def ResultData.fields : ResultData → List (String × Json)
  | .fisher o .. | .margin o .. => o.fields
  | .association table _ => [("table", table.encode)]
  | .matched pairs _ => [("pairs", pairs.encode)]
  | .rate events _ _ => [("events", events.encode)]
  | .oneSample responses .. => [("responses", toJson responses)]
  | .twoStage first second .. => [("stage1_responses", toJson first),
      ("stage2_responses", (second.map toJson).getD Json.null)]

def ReportedResult.fields (r : ReportedResult) : List (String × Json) :=
  [("p_value", ratJson r.pValue.value), ("reject_null", toJson r.reject)]

def ReportedTable.fields (r : ReportedTable) : List (String × Json) :=
  r.toReportedResult.fields ++ [("observed_table_probability", ratJson r.mass.value)]

def ResultData.reported : ResultData → Json
  | .fisher _ r low high _ => Json.mkObj (r.fields ++
      [("support_min", toJson low), ("support_max", toJson high)])
  | .margin _ reject .. => Json.mkObj [("reject_null", toJson reject)]
  | .association _ r => Json.mkObj r.fields
  | .matched _ r | .rate _ _ r => Json.mkObj (r.toReportedResult.fields ++
      [("upper_tail", toJson r.upper), ("lower_tail", toJson r.lower)])
  | .oneSample _ critical r => Json.mkObj (r.fields ++ [("critical_value", toJson critical)])
  | .twoStage _ _ continued reject bound => Json.mkObj [("continued", toJson continued),
      ("reject_null", toJson reject), ("typeI_bound", ratJson bound.value)]

def IntervalData.encode : IntervalData → Json
  | .binomial n x level .. => Json.mkObj [("model", Json.mkObj
      [("module", Json.str "one_arm_binomial"), ("n", toJson n)]),
      ("responses", toJson x), ("level", ratJson level.value)]
  | .proportion study measure group cases level .. => Json.mkObj <| [("model", study.encode),
      ("measure", Json.str measure), ("cases", toJson cases), ("level", ratJson level.value)] ++
      optional "group" Json.str group
  | .difference model observed level .. => Json.mkObj
      ([("model", model.encode), ("level", ratJson level.value)] ++ observed.fields)
  | .association table measure level .. => Json.mkObj [("table", table.encode),
      ("measure", Json.str measure), ("level", ratJson level.value)]
  | .matched pairs level .. => Json.mkObj [("pairs", pairs.encode), ("level", ratJson level.value)]
  | .rate events level .. => Json.mkObj [("events", events.encode), ("level", ratJson level.value)]

def oddsRat (q : ℚ) : ℚ := q / (1 - q)

def intervalOutputs (tail : ProbabilityFraction) (lower : ℚ) (upper : Option ℚ)
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("tail", ratJson tail.value), ("lower", ratJson lower),
    ("upper", (upper.map ratJson).getD Json.null)] ++ extra)

def Endpoints.reported (ends : Endpoints) : Json :=
  Json.arr #[ratJson ends.lower.value, ratJson ends.upper.value]

def twoIntervalOutputs (measure : String) (tail : ProbabilityFraction)
    (c t : Endpoints) : Json :=
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
  intervalOutputs tail lower upper [("control", c.reported), ("treatment", t.reported)]

def IntervalData.reported : IntervalData → Json
  | .binomial _ _ _ tail e | .proportion _ _ _ _ _ tail e =>
    intervalOutputs tail e.lower.value (some e.upper.value)
  | .difference _ _ _ tail c t => twoIntervalOutputs "difference" tail c t
  | .association _ measure _ tail c t => twoIntervalOutputs measure tail c t
  | .matched _ _ tail e =>
    intervalOutputs tail (oddsRat e.lower.value)
      (if e.upper.value < 1 then some (oddsRat e.upper.value) else none) [("arm", e.reported)]
  | .rate events _ tail e =>
    let scale := events.unexposedTime / events.exposedTime
    intervalOutputs tail (oddsRat e.lower.value * scale)
      (if e.upper.value < 1 then some (oddsRat e.upper.value * scale) else none) [("arm", e.reported)]

def PlanningPoint.encode : PlanningPoint → Json
  | .arms point => Json.mkObj [("p_control", ratJson point.control.value),
      ("p_treatment", ratJson point.treatment.value)]
  | .response r => Json.mkObj [("response_rate", ratJson r.value)]
  | .association first second point exposed => Json.mkObj <|
      [(first, ratJson point.control.value), (second, ratJson point.treatment.value)] ++
        optional "exposed_share" (fun p => ratJson p.value) exposed
  | .matched discordant odds _ => Json.mkObj [("discordant", ratJson discordant.value),
      ("odds_ratio", ratJson odds)]
  | .rate ratio exposedTime unexposedTime events .. => Json.mkObj <|
      [("rate_ratio", ratJson ratio), ("exposed_time", ratJson exposedTime),
        ("unexposed_time", ratJson unexposedTime)] ++ optional "events" toJson events

def PlanningTarget.encode (target : PlanningTarget) : Json :=
  Json.mkObj [("at", target.point.encode), ("minimum_power", ratJson target.power.value),
    ("maximum_typeI", ratJson target.error.value)]

def PlanSelection.reported : PlanSelection → Json
  | .arms sizes => Json.mkObj [("n_control", toJson sizes.nControl), ("n_treatment", toJson sizes.nTreatment)]
  | .oneSample n critical => Json.mkObj [("n", toJson n), ("critical_value", toJson critical)]
  | .count n => Json.mkObj [("n", toJson n)]
  | .stages sizes rule => Json.mkObj [("n_stage1", toJson sizes.first), ("n_stage2", toJson sizes.second),
      ("rule", rule.encode)]

mutual
def Test.encode : Test → Json
  | .fisher _ design null alpha => analysis "fisher" design null alpha
  | .exact _ .fisherOneSided design null alpha =>
    (analysis "fisher" design null alpha).mergeObj (Json.mkObj [("alternative", Json.str "greater")])
  | .exact _ (.margin ..) design null alpha =>
    (analysis "fisher" design null alpha).mergeObj (Json.mkObj [("alternative", Json.str "margin")])
  | .exactStudy _ kind design null alpha =>
    Json.mkObj [("test", Json.str kind.key), ("design", design.encode), ("null", null.encode),
      ("alpha", ratJson alpha.value)]
  | .randomised _ r =>
    Json.mkObj <| [("test", Json.str "randomisation"), ("design", r.design.encode),
      ("null", Json.mkObj [("predicate", Json.str "no_effect"), ("model", r.nullModel.encode)]),
      ("alpha", ratJson r.alpha.value)] ++ optional "draws" toJson r.draws
  | .member t => Test.encode t
  | .oneSample _ n reference alpha =>
    Json.mkObj [("test", Json.str "binomial_exact_one_sided"),
      ("model", Json.mkObj [("module", Json.str "one_arm_binomial"), ("n", toJson n)]),
      ("null_rate", ratJson reference.value), ("alpha", ratJson alpha.value)]
  | .twoStage _ stages rule reference =>
    Json.mkObj [("test", Json.str "two_stage"), ("design", stages.encode),
      ("rule", rule.encode), ("null_rate", ratJson reference.value)]
  | .assumed _ guarantee design null alpha => assumedJson guarantee design null alpha
  | .associated _ method design null alpha adjusted =>
    Json.mkObj <|
      [("test", Json.str method.key), ("design", design.encode), ("null", null.encode),
        ("alpha", ratJson alpha.value)] ++
      (if adjusted.isEmpty then [] else
        [("adjusted_for", Json.arr (adjusted.map Json.str).toArray)])
  | .bonferroni _ members alpha none =>
    combination "bonferroni" alpha (Json.arr (Test.encodeMembers members).toArray)
  | .bonferroni _ members alpha (some joint) =>
    Json.mkObj [("method", Json.str "bonferroni"), ("alpha", ratJson alpha.value),
      ("joint_law", Json.str joint), ("analyses", Json.arr (Test.encodeMembers members).toArray)]
  | .looks _ members alpha =>
    combination "alpha_spending" alpha (Json.arr (Test.encodeMembers members).toArray)
  | .graphical _ members weights rows alpha =>
    combination "graphical" alpha (Json.arr (Test.encodeMembers members).toArray)
      [("weights", Json.arr (weights.map ratJson).toArray),
        ("transitions", Json.arr (rows.map fun row => Json.arr (row.map ratJson).toArray).toArray)]
  | .sequence _ members alpha =>
    combination "fixed_sequence" alpha (Json.arr (Test.encodeMembers members).toArray)
termination_by structural t => t

/-- A combination's members, each with its name. -/
def Test.encodeMembers : List Test → List Json
  | [] => []
  | t :: ts =>
    Json.mkObj [("name", Json.str t.name), ("analysis", Test.encode t)] :: Test.encodeMembers ts
termination_by structural ts => ts
end

def SearchKind.fields (kind : SearchKind) (t : Test) (range : SearchRange) : List (String × Json) :=
  match kind with
  | .arms => [("allocation", Json.str (if range.ratio = 1 then "equal_arms" else s!"1:{range.ratio}")),
      ("min_per_arm", toJson range.low), ("max_per_arm", toJson range.high)]
  | .groups =>
    let isCohort : Bool := match t with
      | .exactStudy _ _ design .. => design.model.design == .cohort
      | _ => false
    let (low, high, ratio) := if isCohort then
      ("min_exposed", "max_exposed", "unexposed_per_exposed")
      else ("min_cases", "max_cases", "controls_per_case")
    [(low, toJson range.low), (high, toJson range.high), (ratio, toJson range.ratio)]
  | .total | .oneSample => [("min_n", toJson range.low), ("max_n", toJson range.high)]
  | .pairs => [("min_pairs", toJson range.low), ("max_pairs", toJson range.high)]
  | .events => [("min_events", toJson range.low), ("max_events", toJson range.high)]

def PlanQuery.encode (q : PlanQuery) (target : PlanningTarget) : String × Json :=
  match q with
  | .meets t => ("meets", Json.mkObj [("analysis", t.encode), ("target", target.encode)])
  | .search t kind range =>
    let candidates := Json.mkObj (("analysis", t.encode) :: kind.fields t range)
    ("sample_size", Json.mkObj [("candidates", candidates), ("target", target.encode),
      ("claim", Json.str (if range.minimal then "smallest_in_range" else "sufficient"))])
  | .stageSearch reference maxTotal criterion =>
    let candidates := Json.mkObj [("design", Json.str "two_stage_threshold"),
      ("null_rate", ratJson reference.value), ("max_total", toJson maxTotal), ("criterion", Json.str criterion)]
    ("sample_size", Json.mkObj [("candidates", candidates), ("target", target.encode),
      ("claim", Json.str "sufficient")])

def Request.encode (request : Request) : Json :=
  let (kind, subject) := match request with
    | .typeI t => ("typeI", t.encode)
    | .familywise t => ("familywise", t.encode)
    | .result _ t observed _ =>
      ("result", Json.mkObj [("analysis", t.encode), ("control_successes", toJson observed.control),
        ("treatment_successes", toJson observed.treatment)])
    | .checkedResult _ t d => ("result", Json.mkObj (("analysis", t.encode) :: d.fields))
    | .interval _ d => ("interval", d.encode)
    | .planned _ q target _ => q.encode target
  Json.mkObj [("kind", Json.str kind), ("subject_name", Json.str request.name), ("subject", subject)]

def Request.reported : Request → Option Json
  | .result _ _ _ found =>
    some (Json.mkObj [("p_value", ratJson found.pValue.value), ("reject_null", toJson found.reject)])
  | .checkedResult _ _ d => some d.reported
  | .interval _ d => some d.reported
  | .planned _ _ _ selected => selected.map PlanSelection.reported
  | _ => none

/-- The type of the binding that declares a test. -/
def Test.binding : Test → String
  | .fisher .. => "AnalysisIR"
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
  | _ => "ComposedFamilyIR"

mutual
def Test.thresholds : Test → List Json
  | .exact name (.margin _ thresholds) .. =>
    [Json.mkObj [("name", Json.str name), ("thresholds", toJson thresholds)]]
  | .member t => Test.thresholds t
  | .bonferroni _ members .. | .looks _ members ..
  | .graphical _ members .. | .sequence _ members .. => Test.allThresholds members
  | _ => []
termination_by structural t => t

def Test.allThresholds : List Test → List Json
  | [] => []
  | t :: ts => t.thresholds ++ Test.allThresholds ts
termination_by structural ts => ts
end

/-- The claims and reported outputs of the `verify` requests, in order, and the declarations. -/
def Program.encode (program : Program) : Json :=
  let outputs := program.requests.map Request.reported
  let thresholds := Test.allThresholds program.declarations ++
    Test.allThresholds (program.requests.filterMap Request.test)
  Json.mkObj <| [("claims", Json.arr (program.requests.map Request.encode).toArray),
    ("declarations", Json.arr (program.declarations.map fun t =>
      Json.mkObj [("name", Json.str t.name), ("type", Json.str t.binding), ("value", t.encode)]).toArray)] ++
    (if outputs.any Option.isSome then
      [("reported", Json.arr (outputs.map (·.getD Json.null)).toArray)] else []) ++
    (if thresholds.isEmpty then [] else [("rejection_thresholds", Json.arr thresholds.toArray)])

end StatClaim.Semantics
