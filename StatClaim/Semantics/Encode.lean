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

mutual
def Test.encode : Test → Json
  | .fisher _ design null alpha => analysis "fisher" design null alpha
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

def Request.encode (request : Request) : Json :=
  let kind := match request with
    | .typeI _ => "typeI"
    | .familywise _ => "familywise"
  Json.mkObj [("kind", Json.str kind), ("subject_name", Json.str request.test.name),
    ("subject", request.test.encode)]

/-- The type of the binding that declares a test. -/
def Test.binding : Test → String
  | .fisher .. => "AnalysisIR"
  | .assumed .. => "CitedAnalysisIR"
  | .associated .. => "CitedAssociationIR"
  | .bonferroni _ _ _ (some _) => "FamilyIR"
  | .looks .. => "SequentialIR"
  | _ => "ComposedFamilyIR"

/-- The claims of a program's `verify` requests, in order, and its declarations. -/
def Program.encode (program : Program) : Json :=
  Json.mkObj [("claims", Json.arr (program.requests.map Request.encode).toArray),
    ("declarations", Json.arr (program.declarations.map fun t =>
      Json.mkObj [("name", Json.str t.name), ("type", Json.str t.binding),
        ("value", t.encode)]).toArray)]

end StatClaim.Semantics
