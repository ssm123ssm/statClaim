-- Statements frozen from the phase 1 translator.
-- check_lean_semantics.py inserts each pinned program before its statements.

-- program: examples/analysis_population.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def response_sizes : StatClaim.FixedSampleDesign :=
  ⟨30, 30, by decide, by decide⟩

noncomputable def response := StatClaim.Modules.TwoArmBinomial.model response_sizes

def primary_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

def completers_sizes : StatClaim.FixedSampleDesign :=
  ⟨26, 24, by decide, by decide⟩

noncomputable def completers := StatClaim.Modules.TwoArmBinomial.model completers_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed completers

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def supportive_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def supportive :=
  StatClaim.Modules.Fisher.analysis completers_sizes design supportive_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 60 → (Fin 60 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 60 Value)
      (sharp : StatClaim.Modules.Randomisation.SharpNull outcomes),
      (MeasureTheory.Measure.pi (fun _ : Fin (9999 + 1) => StatClaim.Modules.Randomisation.law 60 30)).real
        (StatClaim.Modules.Randomisation.drawnRejection 9999 statistic outcomes primary_level.value) ≤
      (primary_level.value : ℝ)) ∧
  ((supportive.typeIClaim design_compatible
      (supportive_level.value : ℝ)).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/case_control.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.studies { design := .case_control, cases := some 120, controls := some 240, exposure := "mobile phone use", outcome := "glioma" }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.studies { design := .case_control, cases := some 120, controls := some 240, exposure := "mobile phone use", outcome := "glioma" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.studies { design := .case_control, cases := some 120, controls := some 240, exposure := "mobile phone use", outcome := "glioma" }).space
def Instance.study (i : Instance) := (i.studies { design := .case_control, cases := some 120, controls := some 240, exposure := "mobile phone use", outcome := "glioma" }).model

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def analysis_groups : StatClaim.FixedSampleDesign :=
  ⟨240, 120, by decide, by decide⟩

noncomputable def analysis_study := StatClaim.Modules.TwoArmBinomial.model analysis_groups

noncomputable def analysis_design :=
  StatClaim.Core.StudyDesign.fixed analysis_study

noncomputable def analysis_compatible :
    StatClaim.Core.Compatibility analysis_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis analysis_groups analysis_design analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((analysis.typeIClaim analysis_compatible (analysis_level.value : ℝ)).statement) ∧
  ((∀ (pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 240 120 pc pt).real
      ({a | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 240 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
        {b | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 240 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 112)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 64)
      (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1),
      StatClaim.Modules.Association.odds (((1069 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ)) / StatClaim.Modules.Association.odds (((5409 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds pt / StatClaim.Modules.Association.odds pc ∧
      StatClaim.Modules.Association.odds pt / StatClaim.Modules.Association.odds pc ≤ StatClaim.Modules.Association.odds (((637 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) / StatClaim.Modules.Association.odds (((787 : ℕ) : ℝ) / ((2000 : ℕ) : ℝ))))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/cluster_trial.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.practice_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).Parameter
def Instance.practice_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.practice_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).space
def Instance.practice (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).model
def Instance.summaries_test (i : Instance) :=
  i.test "summaries" { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }
def Instance.summaries_slack (i : Instance) : ℝ := i.slack "summaries"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.practice.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.practice.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

def permuted_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where
  cited_summaries_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.cluster_t_test.scope i.practice.law (null i)
    i.summaries_test ((1 : ℚ) / 20) i.summaries_slack

def Claims (i : Instance) : Prop :=
  (StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.summaries_test (↑((1 : ℚ) / 20) : ℝ)) ∧
  (∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 12 → (Fin 12 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 12 Value)
      (sharp : StatClaim.Modules.Randomisation.SharpNull outcomes),
      (StatClaim.Modules.Randomisation.law 12 6).real
        (StatClaim.Modules.Randomisation.rejection 12 6 statistic outcomes permuted_level.value) ≤
      (permuted_level.value : ℝ))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_summaries_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/cohort.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.followed_Parameter (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 150, unexposed := some 300, exposure := "statin use", outcome := "dementia" }).Parameter
def Instance.followed_Outcome (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 150, unexposed := some 300, exposure := "statin use", outcome := "dementia" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.followed_Outcome i) :=
  (i.studies { design := .cohort, exposed := some 150, unexposed := some 300, exposure := "statin use", outcome := "dementia" }).space
def Instance.followed (i : Instance) := (i.studies { design := .cohort, exposed := some 150, unexposed := some 300, exposure := "statin use", outcome := "dementia" }).model

def test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def test_groups : StatClaim.FixedSampleDesign :=
  ⟨300, 150, by decide, by decide⟩

noncomputable def test_study := StatClaim.Modules.TwoArmBinomial.model test_groups

noncomputable def test_design :=
  StatClaim.Core.StudyDesign.fixed test_study

noncomputable def test_compatible :
    StatClaim.Core.Compatibility test_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def test :=
  StatClaim.Modules.Fisher.analysis test_groups test_design test_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((test_groups.nControl = 300 ∧ test_groups.nTreatment = 150 ∧ 0 < test_groups.nControl ∧
    0 < test_groups.nTreatment) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw test_groups.nControl test_groups.nTreatment p).real
        (StatClaim.fisherRejectionRegionAt test_groups.nControl test_groups.nTreatment test_level.value) ≤
      (test_level.value : ℝ)) ∧
    (StatClaim.hypergeometricPValue 300 150 42 33 =
    (8231711943668545221180826504133087942756 : ℚ) / 68245851794690510331224106897866727741889) ∧
    (StatClaim.hypergeometricMass 300 150 42 33 =
    (2168340912957357409923888271981926530550 : ℚ) / 68245851794690510331224106897866727741889) ∧
    (((33, 9) ∈ StatClaim.fisherRejectionRegionAt 300 150 ((1 : ℚ) / 20)) ↔ False)) ∧
  ((∀ (pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 300 150 pc pt).real
      ({a | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 300 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
        {b | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 150 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 300 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 33)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 150 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 9)
      (positive : 0 < (pc : ℝ)),
      (((123 : ℕ) : ℝ) / ((5000 : ℕ) : ℝ)) / (((1571 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) ≤ (pt : ℝ) / pc ∧
      (pt : ℝ) / pc ≤ (((593 : ℕ) : ℝ) / ((5000 : ℕ) : ℝ)) / (((729 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ))))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/complex_survey.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.survey_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }).Parameter
def Instance.survey_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.survey_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }).space
def Instance.survey (i : Instance) := (i.studies { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }).model
def Instance.weighted_test (i : Instance) :=
  i.studyTest "weighted" { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }
def Instance.weighted_slack (i : Instance) : ℝ := i.slack "weighted"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.survey.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.survey.noAssociation

structure Premises (i : Instance) : Prop where
  cited_weighted_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.survey_linear.scope i.survey.law (null i)
    i.weighted_test ((1 : ℚ) / 20) i.weighted_slack

def Claims (i : Instance) : Prop :=
  StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.weighted_test ((↑((1 : ℚ) / 20) : ℝ) + i.weighted_slack)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_weighted_level, trivial⟩

-- program: examples/confidence_interval.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The number of participants in the arm. -/
def study : ℕ := 35

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ (p : unitInterval),
      1 - 2 * (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) ≤
      (ProbabilityTheory.binomial 35 p).real
        {count | p ∈ StatClaim.Modules.BinomialInterval.confidenceSet 35 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) count}) ∧
    (∀ (p : unitInterval)
      (member : p ∈ StatClaim.Modules.BinomialInterval.confidenceSet 35 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) 14),
      StatClaim.ratPoint 2387 10000 (by decide) (by decide) ≤ p ∧
      p ≤ StatClaim.ratPoint 5789 10000 (by decide) (by decide))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/confirmatory_trial.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.interim_cohort_Parameter (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }).Parameter
def Instance.interim_cohort_Outcome (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.interim_cohort_Outcome i) :=
  (i.laws { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }).space
def Instance.interim_cohort (i : Instance) := (i.laws { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }).model
def Instance.full_cohort_Parameter (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter
def Instance.full_cohort_Outcome (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.full_cohort_Outcome i) :=
  (i.laws { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }).space
def Instance.full_cohort (i : Instance) := (i.laws { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }).model
def Instance.interim_test (i : Instance) :=
  i.test "interim" { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }
def Instance.interim_slack (i : Instance) : ℝ := i.slack "interim"
def Instance.final_test (i : Instance) :=
  i.test "final" { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.final_slack (i : Instance) : ℝ := i.slack "final"
def Instance.scores_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter
def Instance.scores_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.scores_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).space
def Instance.scores (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.interim_cohort.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.interim_cohort.null StatClaim.Generated.NullKey.equal_survival.shape (0 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.full_cohort.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.full_cohort.null StatClaim.Generated.NullKey.equal_survival.shape (0 : ℚ)

noncomputable def design_2 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.scores.toModel

noncomputable def design_2_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_2 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_2 (i : Instance) :=
  i.scores.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨300, 300, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design_3 :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_3_compatible :
    StatClaim.Core.Compatibility design_3 :=
  StatClaim.Core.Compatibility.fixed _

def null_3 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis responders_sizes design_3 response_level

structure Premises (i : Instance) : Prop where
  cited_interim_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.log_rank.scope i.interim_cohort.law (null i)
    i.interim_test ((1 : ℚ) / 200) i.interim_slack
  cited_final_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.log_rank.scope i.full_cohort.law (null_1 i)
    i.final_test ((9 : ℚ) / 200) i.final_slack
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.scores.law (null_2 i)
    i.symptoms_test ((1 : ℚ) / 20) i.symptoms_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.interim_cohort_Parameter i.interim_cohort_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.full_cohort_Parameter i.full_cohort_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.scores_Parameter i.scores_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ i.interim_cohort.law →
      v₁.Marginal σ i.full_cohort.law →
      v₂.Marginal σ i.scores.law →
      v₃.Marginal σ responders.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∀ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null_1 i) (v₁.parameter θ)] k θ,
        fun θ => (null_2 i) (v₂.parameter θ),
        fun θ => response.hypothesis (v₃.parameter θ)]
        ![(⋃ k, ![v₀.outcome ⁻¹' i.interim_test.reject, v₁.outcome ⁻¹' i.final_test.reject] k),
        v₂.outcome ⁻¹' i.symptoms_test.reject,
        v₃.outcome ⁻¹' response.procedure.rejectionEvent]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![(∑ k, ![i.interim_slack, i.final_slack] k), i.symptoms_slack, 0] k)) ∧
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.interim_cohort_Parameter i.interim_cohort_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.full_cohort_Parameter i.full_cohort_Outcome),
      v₀.Marginal σ i.interim_cohort.law →
      v₁.Marginal σ i.full_cohort.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.interim_test.reject,
        v₁.outcome ⁻¹' i.final_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.interim_slack, i.final_slack] k)) ∧
  ((response.typeIClaim design_3_compatible
      (response_level.value : ℝ)).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_interim_level, h.cited_final_level, h.cited_symptoms_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_interim_level, h.cited_final_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/cross_sectional.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.survey_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 800, exposure := "night shifts", outcome := "insomnia" }).Parameter
def Instance.survey_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 800, exposure := "night shifts", outcome := "insomnia" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.survey_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 800, exposure := "night shifts", outcome := "insomnia" }).space
def Instance.survey (i : Instance) := (i.studies { design := .cross_sectional, n := some 800, exposure := "night shifts", outcome := "insomnia" }).model
def Instance.population_Parameter (i : Instance) : Type := (i.studies { design := .cohort, n := some 2500, exposure := "air pollution", outcome := "childhood asthma" }).Parameter
def Instance.population_Outcome (i : Instance) : Type := (i.studies { design := .cohort, n := some 2500, exposure := "air pollution", outcome := "childhood asthma" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.population_Outcome i) :=
  (i.studies { design := .cohort, n := some 2500, exposure := "air pollution", outcome := "childhood asthma" }).space
def Instance.population (i : Instance) := (i.studies { design := .cohort, n := some 2500, exposure := "air pollution", outcome := "childhood asthma" }).model

def prevalence_test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

def risk_test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ (q p : unitInterval),
      (StatClaim.Modules.Association.mixtureLaw 800 q p).real
        (StatClaim.Modules.Association.mixtureRejection 800 prevalence_test_level.value) ≤
      (prevalence_test_level.value : ℝ)) ∧
  (∀ (q p : unitInterval),
      (StatClaim.Modules.Association.mixtureLaw 2500 q p).real
        (StatClaim.Modules.Association.mixtureRejection 2500 risk_test_level.value) ≤
      (risk_test_level.value : ℝ)) ∧
  ((∀ (q pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤
      (StatClaim.Modules.Association.mixture 800 q (fun k => StatClaim.productBinomial (800 - k) k pc pt)).real
        (StatClaim.Modules.Association.given 800 (fun k =>
          {a | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet (800 - k) (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
            {b | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet k (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b}))) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 600 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 90)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 200 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 62)
      (positive : 0 < (pc : ℝ)),
      (((477 : ℕ) : ℝ) / ((2000 : ℕ) : ℝ)) / (((1857 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) ≤ (pt : ℝ) / pc ∧
      (pt : ℝ) / pc ≤ (((243 : ℕ) : ℝ) / ((625 : ℕ) : ℝ)) / (((297 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ))))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/declared_design.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.visits_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, better := some "lower", measurements := some 3 }).Parameter
def Instance.visits_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, better := some "lower", measurements := some 3 }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.visits_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, better := some "lower", measurements := some 3 }).space
def Instance.visits (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, better := some "lower", measurements := some 3 }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, better := some "lower", measurements := some 3 }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"
def Instance.practice_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12), better := some "higher" }).Parameter
def Instance.practice_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12), better := some "higher" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.practice_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12), better := some "higher" }).space
def Instance.practice (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12), better := some "higher" }).model
def Instance.adherence_test (i : Instance) :=
  i.test "adherence" { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12), better := some "higher" }
def Instance.adherence_slack (i : Instance) : ℝ := i.slack "adherence"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.visits.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.visits.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.practice.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.practice.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test.scope i.visits.law (null i)
    i.symptoms_test ((1 : ℚ) / 20) i.symptoms_slack
  declared_adherence_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.practice.law (null_1 i)
    i.adherence_test ((1 : ℚ) / 20) i.adherence_slack

def Claims (i : Instance) : Prop :=
  (StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.symptoms_test ((↑((1 : ℚ) / 20) : ℝ) + i.symptoms_slack)) ∧
  (StatClaim.Interface.typeIClaim (design_1_compatible i) (null_1 i) i.adherence_test ((↑((1 : ℚ) / 20) : ℝ) + i.adherence_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_symptoms_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.declared_adherence_level, trivial⟩

-- program: examples/declared_test.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).space
def Instance.study (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).model
def Instance.pain_test (i : Instance) :=
  i.test "pain" { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }
def Instance.pain_slack (i : Instance) : ℝ := i.slack "pain"
def Instance.function_test (i : Instance) :=
  i.test "function" { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }
def Instance.function_slack (i : Instance) : ℝ := i.slack "function"

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  declared_pain_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.study.law (null i)
    i.pain_test ((1 : ℚ) / 40) i.pain_slack
  cited_function_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.study.law (null i)
    i.function_test ((1 : ℚ) / 40) i.function_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome),
      v₀.Marginal σ i.study.law →
      v₁.Marginal σ i.study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.pain_test.reject,
        v₁.outcome ⁻¹' i.function_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.pain_slack, i.function_slack] k)) ∧
  (StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.pain_test ((↑((1 : ℚ) / 40) : ℝ) + i.pain_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.declared_pain_level, h.cited_function_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.declared_pain_level, trivial⟩

-- program: examples/difference_interval.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ (pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 50 50 pc pt).real
      ({x | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) x} ×ˢ
        {y | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) y})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 12)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 24),
      ((797 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ) - ((4013 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) ≤
        (pt : ℝ) - (pc : ℝ) ∧
      (pt : ℝ) - (pc : ℝ) ≤
        ((6443 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - ((1189 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/fields.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨100, 100, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes plan analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim plan_compatible
      (analysis_level.value : ℝ)).statement

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/first_class.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨100, 100, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes plan analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((analysis.typeIClaim plan_compatible
      (analysis_level.value : ℝ)).statement) ∧
  ((0 < 100 ∧ 0 < 100 ∧ 10 ≤ 100 ∧ 25 ≤ 100) ∧
    (∀ (k : ℕ),
      k ∈ StatClaim.hypergeometricSupport 100 100 35 ↔
      0 ≤ k ∧ k ≤ 35) ∧
    (StatClaim.hypergeometricPValue 100 100 35 10 =
    (19912805355158606332329 : ℚ) / 2341699062001756564467919) ∧
    (StatClaim.hypergeometricMass 100 100 35 10 =
    (537397138428741731448 : ℚ) / 180130697077058197266763) ∧
    (((10, 25) ∈ StatClaim.fisherRejectionRegionAt 100 100 ((1 : ℚ) / 20)) ↔ True) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw 100 100 p).real (StatClaim.fisherRejectionRegionAt 100 100 (( 1 : ℚ) / 20)) ≤
      ((1 : ℝ) / 20)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/fisher.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨100, 100, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes plan analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim plan_compatible
      (analysis_level.value : ℝ)).statement

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/fisher_result.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨100, 100, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes plan analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (0 < 100 ∧ 0 < 100 ∧ 10 ≤ 100 ∧ 25 ≤ 100) ∧
    (∀ (k : ℕ),
      k ∈ StatClaim.hypergeometricSupport 100 100 35 ↔
      0 ≤ k ∧ k ≤ 35) ∧
    (StatClaim.hypergeometricPValue 100 100 35 10 =
    (19912805355158606332329 : ℚ) / 2341699062001756564467919) ∧
    (StatClaim.hypergeometricMass 100 100 35 10 =
    (537397138428741731448 : ℚ) / 180130697077058197266763) ∧
    (((10, 25) ∈ StatClaim.fisherRejectionRegionAt 100 100 ((1 : ℚ) / 20)) ↔ True) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw 100 100 p).real (StatClaim.fisherRejectionRegionAt 100 100 (( 1 : ℚ) / 20)) ≤
      ((1 : ℝ) / 20))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/hypothesis_zero.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨100, 100, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes plan analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim plan_compatible
      (analysis_level.value : ℝ)).statement

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/incidence_rates.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.workers_Parameter (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).Parameter
def Instance.workers_Outcome (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.workers_Outcome i) :=
  (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).space
def Instance.workers (i : Instance) := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).model

def test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ (total : NNReal) (share : unitInterval),
      (StatClaim.Modules.Incidence.ratesLaw total share).real
        (StatClaim.Modules.Incidence.given (fun n => StatClaim.Modules.Incidence.rejectionAt share n (test_level.value : ℝ))) ≤
      (test_level.value : ℝ)) ∧
  ((∀ (total : NNReal) (share : unitInterval),
      (StatClaim.Modules.Incidence.ratesLaw total share).real
        (StatClaim.Modules.Incidence.given (fun n => StatClaim.Modules.Incidence.rejectionAt share n (test_level.value : ℝ))) ≤
      (test_level.value : ℝ)) ∧
    (StatClaim.Modules.OneSampleBinomial.tailNumerator 53 33686 138927 19 = 14452695193718051843752386405865057014495796398165617358583265144219598599073398664895210216350636736722060652148994692605105744026908658627622709944948649357656867892153596578733189882298124144765365014332614769899289497192938057984519213592145652886884712639811849027584 ∧
    StatClaim.Modules.BinomialInterval.lowerNumerator 53 33686 138927 19 = 362217866287361495016497180997714958804180013122805619766687802855989568013657036868962519695720428204431080276468920786726382454155333798276518405718487823462120338546488502748575920600415634089755984522043899237903705680575802923968818334344672726691720187246199213647983) ∧
    (((53, 19) ∈ StatClaim.Modules.Incidence.given (fun n => StatClaim.Modules.Incidence.rejectionAt (StatClaim.ratPoint 33686 138927 (by decide) (by decide)) n
      (test_level.value : ℝ))) ↔ False)) ∧
  ((∀ (total : NNReal) (π : unitInterval),
      (((39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) ≤ (StatClaim.Modules.Incidence.ratesLaw total π).real
      (StatClaim.Modules.Incidence.given (fun n => {x | π ∈ StatClaim.Modules.BinomialInterval.confidenceSet n (((1 : ℕ) : ℝ) / ((80 : ℕ) : ℝ)) x}))) ∧
    (∀ (π : unitInterval)
      (member : π ∈ StatClaim.Modules.BinomialInterval.confidenceSet 53 (((1 : ℕ) : ℝ) / ((80 : ℕ) : ℝ)) 19) (below : (π : ℝ) < 1),
      StatClaim.Modules.Association.odds (((1081 : ℕ) : ℝ) / ((5000 : ℕ) : ℝ)) * (((105241 : ℕ) : ℝ) / ((33686 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds π * (((105241 : ℕ) : ℝ) / ((33686 : ℕ) : ℝ)) ∧
      StatClaim.Modules.Association.odds π * (((105241 : ℕ) : ℝ) / ((33686 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds (((5213 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) * (((105241 : ℕ) : ℝ) / ((33686 : ℕ) : ℝ))))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/interim_look.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.halfway_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }).Parameter
def Instance.halfway_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.halfway_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }).space
def Instance.halfway (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }).model
def Instance.complete_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).Parameter
def Instance.complete_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.complete_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).space
def Instance.complete (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).model
def Instance.interim_test (i : Instance) :=
  i.test "interim" { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }
def Instance.interim_slack (i : Instance) : ℝ := i.slack "interim"
def Instance.final_test (i : Instance) :=
  i.test "final" { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }
def Instance.final_slack (i : Instance) : ℝ := i.slack "final"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.halfway.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.halfway.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.complete.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.complete.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_interim_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.halfway.law (null i)
    i.interim_test ((1 : ℚ) / 200) i.interim_slack
  cited_final_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.complete.law (null_1 i)
    i.final_test ((9 : ℚ) / 200) i.final_slack

def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.halfway_Parameter i.halfway_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.complete_Parameter i.complete_Outcome),
      v₀.Marginal σ i.halfway.law →
      v₁.Marginal σ i.complete.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.interim_test.reject,
        v₁.outcome ⁻¹' i.final_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.interim_slack, i.final_slack] k)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_interim_level, h.cited_final_level, trivial⟩

-- program: examples/log_rank.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨200, 200, by decide, by decide⟩ }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨200, 200, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.laws { outcome := .survival, sizes := ⟨200, 200, by decide, by decide⟩ }).space
def Instance.study (i : Instance) := (i.laws { outcome := .survival, sizes := ⟨200, 200, by decide, by decide⟩ }).model
def Instance.analysis_test (i : Instance) :=
  i.test "analysis" { outcome := .survival, sizes := ⟨200, 200, by decide, by decide⟩ }
def Instance.analysis_slack (i : Instance) : ℝ := i.slack "analysis"

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.equal_survival.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_analysis_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.log_rank.scope i.study.law (null i)
    i.analysis_test ((1 : ℚ) / 20) i.analysis_slack

def Claims (i : Instance) : Prop :=
  StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.analysis_test ((↑((1 : ℚ) / 20) : ℝ) + i.analysis_slack)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_analysis_level, trivial⟩

-- program: examples/lower_is_better.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨400, 400, by decide, by decide⟩, better := some "lower" }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨400, 400, by decide, by decide⟩, better := some "lower" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨400, 400, by decide, by decide⟩, better := some "lower" }).space
def Instance.study (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨400, 400, by decide, by decide⟩, better := some "lower" }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨400, 400, by decide, by decide⟩, better := some "lower" }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.mean_difference_at_least.shape ((1 : ℚ) / 10)

structure Premises (i : Instance) : Prop where
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.study.law (null i)
    i.symptoms_test ((1 : ℚ) / 40) i.symptoms_slack

def Claims (i : Instance) : Prop :=
  StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.symptoms_test ((↑((1 : ℚ) / 40) : ℝ) + i.symptoms_slack)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_symptoms_level, trivial⟩

-- program: examples/matched_case_control.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.paired_Parameter (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }).Parameter
def Instance.paired_Outcome (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.paired_Outcome i) :=
  (i.studies { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }).space
def Instance.paired (i : Instance) := (i.studies { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }).model

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((220 = 220 ∧ 0 < 220) ∧
    (∀ (δ π : unitInterval),
      StatClaim.Modules.Matched.pairsLaw 220 δ π Set.univ = 1) ∧
    (∀ (δ : unitInterval),
      (StatClaim.Modules.Matched.pairsLaw 220 δ StatClaim.Modules.Matched.half).real
        (StatClaim.Modules.Matched.pairsRejection 220 (analysis_level.value : ℝ)) ≤ (analysis_level.value : ℝ)) ∧
    (StatClaim.Modules.OneSampleBinomial.tailNumerator 48 1 2 31 = 8368726082346 ∧
    StatClaim.Modules.BinomialInterval.lowerNumerator 48 1 2 31 = 277350672112822) ∧
    (((48, 31) ∈ StatClaim.Modules.Matched.pairsRejection 220 (analysis_level.value : ℝ)) ↔ False)) ∧
  ((∀ (δ π : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.Modules.Matched.pairsLaw 220 δ π).real
      (StatClaim.Modules.Association.given 220
        (fun d => {x | π ∈ StatClaim.Modules.BinomialInterval.confidenceSet d (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) x}))) ∧
    (∀ (π : unitInterval)
      (member : π ∈ StatClaim.Modules.BinomialInterval.confidenceSet 48 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) 31) (below : (π : ℝ) < 1),
      StatClaim.Modules.Association.odds (((989 : ℕ) : ℝ) / ((2000 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds π ∧
      StatClaim.Modules.Association.odds π ≤ StatClaim.Modules.Association.odds (((973 : ℕ) : ℝ) / ((1250 : ℕ) : ℝ))))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/mixed_endpoints.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.scores_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).Parameter
def Instance.scores_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.scores_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).space
def Instance.scores (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨120, 120, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis responders_sizes design response_level

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.scores.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.scores.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.scores.law (null_1 i)
    i.symptoms_test ((1 : ℚ) / 40) i.symptoms_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω i.scores_Parameter i.scores_Outcome),
      v₀.Marginal σ responders.law →
      v₁.Marginal σ i.scores.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' i.symptoms_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, i.symptoms_slack] k)) ∧
  ((response.typeIClaim design_compatible
      (response_level.value : ℝ)).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_symptoms_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/non_inferiority.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨60, 60, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost ((-1 : ℚ) / 10)

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

def analysis_thresholds : List ℕ := [0, 0, 2, 3, 5, 6, 8, 9, 11, 12, 13, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 46, 47, 48, 49, 50, 50, 51, 52, 53, 53, 54, 55, 55, 56, 57, 57, 58, 59, 59]

noncomputable def analysis :=
  StatClaim.Modules.DifferenceTest.analysis study_sizes analysis_thresholds ((-1 : ℚ) / 10)

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((analysis.typeIClaim (analysis_level.value : ℝ)).statement) ∧
  ((study_sizes.nControl = 60 ∧ study_sizes.nTreatment = 60 ∧
    0 < study_sizes.nControl ∧ 0 < study_sizes.nTreatment) ∧
    (((StatClaim.Modules.DifferenceTest.analysis study_sizes analysis_thresholds ((((0 : ℕ) : ℚ) - ((100 : ℕ) : ℚ)) / ((1000 : ℕ) : ℚ))).typeIClaim (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ))).statement) ∧
    (StatClaim.Modules.DifferenceTest.rejects 60 analysis_thresholds 50 52 = false))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/observational_power.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.studies { design := .case_control, cases := some 50, controls := some 100, exposure := "night shift work", outcome := "breast cancer" }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.studies { design := .case_control, cases := some 50, controls := some 100, exposure := "night shift work", outcome := "breast cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.studies { design := .case_control, cases := some 50, controls := some 100, exposure := "night shift work", outcome := "breast cancer" }).space
def Instance.study (i : Instance) := (i.studies { design := .case_control, cases := some 50, controls := some 100, exposure := "night shift work", outcome := "breast cancer" }).model
def Instance.followed_Parameter (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 100, unexposed := some 200, exposure := "solvent exposure", outcome := "kidney disease" }).Parameter
def Instance.followed_Outcome (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 100, unexposed := some 200, exposure := "solvent exposure", outcome := "kidney disease" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.followed_Outcome i) :=
  (i.studies { design := .cohort, exposed := some 100, unexposed := some 200, exposure := "solvent exposure", outcome := "kidney disease" }).space
def Instance.followed (i : Instance) := (i.studies { design := .cohort, exposed := some 100, unexposed := some 200, exposure := "solvent exposure", outcome := "kidney disease" }).model
def Instance.paired_Parameter (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 60, exposure := "benzodiazepine use", outcome := "hip fracture" }).Parameter
def Instance.paired_Outcome (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 60, exposure := "benzodiazepine use", outcome := "hip fracture" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.paired_Outcome i) :=
  (i.studies { design := .matched_case_control, pairs := some 60, exposure := "benzodiazepine use", outcome := "hip fracture" }).space
def Instance.paired (i : Instance) := (i.studies { design := .matched_case_control, pairs := some 60, exposure := "benzodiazepine use", outcome := "hip fracture" }).model
def Instance.workers_Parameter (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "shift work", outcome := "type 2 diabetes" }).Parameter
def Instance.workers_Outcome (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "shift work", outcome := "type 2 diabetes" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.workers_Outcome i) :=
  (i.studies { design := .person_time_cohort, exposure := "shift work", outcome := "type 2 diabetes" }).space
def Instance.workers (i : Instance) := (i.studies { design := .person_time_cohort, exposure := "shift work", outcome := "type 2 diabetes" }).model
def Instance.survey_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 60, exposure := "night shifts", outcome := "insomnia" }).Parameter
def Instance.survey_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 60, exposure := "night shifts", outcome := "insomnia" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.survey_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 60, exposure := "night shifts", outcome := "insomnia" }).space
def Instance.survey (i : Instance) := (i.studies { design := .cross_sectional, n := some 60, exposure := "night shifts", outcome := "insomnia" }).model

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def analysis_groups : StatClaim.FixedSampleDesign :=
  ⟨100, 50, by decide, by decide⟩

noncomputable def analysis_study := StatClaim.Modules.TwoArmBinomial.model analysis_groups

noncomputable def analysis_design :=
  StatClaim.Core.StudyDesign.fixed analysis_study

noncomputable def analysis_compatible :
    StatClaim.Core.Compatibility analysis_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis analysis_groups analysis_design analysis_level

def test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def test_groups : StatClaim.FixedSampleDesign :=
  ⟨200, 100, by decide, by decide⟩

noncomputable def test_study := StatClaim.Modules.TwoArmBinomial.model test_groups

noncomputable def test_design :=
  StatClaim.Core.StudyDesign.fixed test_study

noncomputable def test_compatible :
    StatClaim.Core.Compatibility test_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def test :=
  StatClaim.Modules.Fisher.analysis test_groups test_design test_level

def pairs_test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

def rates_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

def survey_test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

namespace smallest_claim_plan

def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩

end smallest_claim_plan

namespace fewest_pairs_claim_plan

def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩

end fewest_pairs_claim_plan

namespace rates_power_claim_plan

def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 40, by norm_num, by norm_num⟩

end rates_power_claim_plan

namespace survey_power_claim_plan

def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩

end survey_power_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((100 = 100 ∧ 50 = 50 ∧ 0 < 100 ∧
    0 < 50) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw 100 50 p).real
        (StatClaim.fisherRejectionRegionAt 100 50 smallest_claim_plan.declaredLevel.value) ≤
      (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))) ∧
    ((((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) ≤
      (StatClaim.productBinomial 100 50 (StatClaim.ratPoint 1 5 (by decide) (by decide)) (StatClaim.ratPoint 3 7 (by decide) (by decide))).real
        (StatClaim.fisherRejectionRegionAt 100 50 smallest_claim_plan.declaredLevel.value)) ∧
    (∀ (n : ℕ) (lower : 40 ≤ n) (upper : n < 50),
      (StatClaim.productBinomial (2 * n) n (StatClaim.ratPoint 1 5 (by decide) (by decide)) (StatClaim.ratPoint 3 7 (by decide) (by decide))).real
        (StatClaim.fisherRejectionRegionAt (2 * n) n smallest_claim_plan.declaredLevel.value) <
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))) ∧
  ((∀ (δ : unitInterval),
      (StatClaim.Modules.Matched.pairsLaw 67 δ StatClaim.Modules.Matched.half).real
        (StatClaim.Modules.Matched.pairsRejection 67 (fewest_pairs_claim_plan.declaredLevel.value : ℝ)) ≤ (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))) ∧
    ((((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) ≤ (StatClaim.Modules.Matched.pairsLaw 67 (StatClaim.ratPoint 1 2 (by decide) (by decide)) (StatClaim.ratPoint 3 4 (by decide) (by decide))).real
        (StatClaim.Modules.Matched.pairsRejection 67 (fewest_pairs_claim_plan.declaredLevel.value : ℝ))) ∧
    (∀ (m : ℕ) (lower : 55 ≤ m) (upper : m < 67),
      (StatClaim.Modules.Matched.pairsLaw m (StatClaim.ratPoint 1 2 (by decide) (by decide)) (StatClaim.ratPoint 3 4 (by decide) (by decide))).real
        (StatClaim.Modules.Matched.pairsRejection m (fewest_pairs_claim_plan.declaredLevel.value : ℝ)) < (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))) ∧
  ((∀ (total : NNReal) (share : unitInterval),
      (StatClaim.Modules.Incidence.ratesLaw total share).real
        (StatClaim.Modules.Incidence.given (fun n => StatClaim.Modules.Incidence.rejectionAt share n (rates_power_claim_plan.declaredLevel.value : ℝ))) ≤
      (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ))) ∧
    ((((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) ≤ (ProbabilityTheory.binomial 100 (StatClaim.ratPoint 2 5 (by decide) (by decide))).real
        (StatClaim.Modules.Incidence.rejectionAt (StatClaim.ratPoint 1 4 (by decide) (by decide)) 100 (rates_power_claim_plan.declaredLevel.value : ℝ)))) ∧
  ((60 = 60 ∧ 0 < 60) ∧
    (∀ (q p : unitInterval),
      (StatClaim.Modules.Association.mixtureLaw 60 q p).real
        (StatClaim.Modules.Association.mixtureRejection 60 survey_power_claim_plan.declaredLevel.value) ≤
      (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))) ∧
    ((((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) ≤
      (StatClaim.Modules.Association.mixture 60 (StatClaim.ratPoint 3 10 (by decide) (by decide))
        (fun k => StatClaim.productBinomial (60 - k) k (StatClaim.ratPoint 1 10 (by decide) (by decide)) (StatClaim.ratPoint 1 2 (by decide) (by decide)))).real
        (StatClaim.Modules.Association.mixtureRejection 60 survey_power_claim_plan.declaredLevel.value)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i ∧ program.claimAt 3 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 3) := trivial

-- program: examples/one_sample.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The number of participants in the arm. -/
def study : ℕ := 25

def analysis_design : StatClaim.Modules.OneSampleBinomial.Design :=
  StatClaim.Modules.OneSampleBinomial.levelDesign study 1 5 1 20

noncomputable def analysis :=
  StatClaim.Modules.OneSampleBinomial.analysis analysis_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

namespace verification_claim_plan

def declaredDesign : StatClaim.Modules.OneSampleBinomial.Design :=
  ⟨35, 12⟩
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 5 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.OneSampleBinomial.analysis declaredDesign nullRate

end verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (verification_claim_plan.declaredDesign.n = 35 ∧ verification_claim_plan.declaredDesign.critical = 12) ∧
    ((verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((verification_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 2 5 (by decide) (by decide))
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement) ∧
    (StatClaim.Modules.OneSampleBinomial.criticalValue 35 1 5 1 20 = 12) ∧
    (∀ (n : ℕ) (lower : 10 ≤ n) (upper : n < 35),
      (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) <
        ((StatClaim.Modules.OneSampleBinomial.policy (StatClaim.Modules.OneSampleBinomial.levelDesign n 1 5 1 20)).law
          (StatClaim.ratPoint 1 5 (by decide) (by decide))).real
          {count | (StatClaim.Modules.OneSampleBinomial.levelDesign n 1 5 1 20).critical ≤ count} ∨
      ((StatClaim.Modules.OneSampleBinomial.policy (StatClaim.Modules.OneSampleBinomial.levelDesign n 1 5 1 20)).law
          (StatClaim.ratPoint 2 5 (by decide) (by decide))).real
          {count | (StatClaim.Modules.OneSampleBinomial.levelDesign n 1 5 1 20).critical ≤ count} <
        (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/one_sample_result.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The number of participants in the arm. -/
def study : ℕ := 35

def analysis_design : StatClaim.Modules.OneSampleBinomial.Design :=
  StatClaim.Modules.OneSampleBinomial.levelDesign study 1 5 1 20

noncomputable def analysis :=
  StatClaim.Modules.OneSampleBinomial.analysis analysis_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (((StatClaim.Modules.OneSampleBinomial.policy ⟨35, 14⟩).law (StatClaim.ratPoint 1 5 (by decide) (by decide))).real
        {count | 14 ≤ count} = (((3060372398554814309273 : ℕ) : ℝ) / ((582076609134674072265625 : ℕ) : ℝ))) ∧
    (StatClaim.Modules.OneSampleBinomial.criticalValue 35 1 5 1 20 = 12) ∧
    (12 ≤ 14) ∧
    (((StatClaim.Modules.OneSampleBinomial.analysis ⟨35, 12⟩ (StatClaim.ratPoint 1 5 (by decide) (by decide))).typeIClaim
      (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/one_sided.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨36, 36, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.FisherOneSided.analysis study_sizes analysis_level

namespace sizing_claim_plan

def declaredSizes : StatClaim.FixedSampleDesign := ⟨36, 36, by decide, by decide⟩
def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 40, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := StatClaim.Modules.FisherOneSided.analysis declaredSizes declaredLevel
noncomputable def planningPoint : StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.FisherPower.ratePoint 1 10 2 5 (by decide) (by decide) (by decide) (by decide)

end sizing_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((analysis.typeIClaim (analysis_level.value : ℝ)).statement) ∧
  ((sizing_claim_plan.declaredSizes.nControl = 36 ∧ sizing_claim_plan.declaredSizes.nTreatment = 36 ∧
    0 < sizing_claim_plan.declaredSizes.nControl ∧ 0 < sizing_claim_plan.declaredSizes.nTreatment) ∧
    ((sizing_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ))).statement) ∧
    ((sizing_claim_plan.declaredAnalysis.powerClaim (fun parameter => parameter = sizing_claim_plan.planningPoint)
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement) ∧
    (∀ (n : ℕ) (positive : 0 < n) (lower : 20 ≤ n) (upper : n < 36),
      ((StatClaim.Core.Policy.fixed (StatClaim.Modules.TwoArmBinomial.model
        ⟨n, 1 * n, positive, Nat.mul_pos (by decide) positive⟩)).law sizing_claim_plan.planningPoint).real
        (StatClaim.Modules.FisherOneSided.analysis ⟨n, 1 * n, positive, Nat.mul_pos (by decide) positive⟩
          sizing_claim_plan.declaredLevel).rejection <
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))) ∧
  ((0 < 36 ∧ 0 < 36 ∧ 4 ≤ 36 ∧ 14 ≤ 36) ∧
    (StatClaim.Modules.FisherOneSided.lowerPValue 36 36 18 4 =
    (4212885 : ℚ) / 650576834) ∧
    ((StatClaim.Modules.FisherOneSided.lowerPValue 36 36 18 4 ≤ (1 : ℚ) / 40) ↔ True) ∧
    ((analysis.typeIClaim (analysis_level.value : ℝ)).statement))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/paper/fisher_design.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim design_compatible
      (analysis_level.value : ℝ)).statement

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/paper/fisher_observed.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (0 < 50 ∧ 0 < 50 ∧ 12 ≤ 50 ∧ 24 ≤ 50) ∧
    (∀ (k : ℕ),
      k ∈ StatClaim.hypergeometricSupport 50 50 36 ↔
      0 ≤ k ∧ k ≤ 36) ∧
    (StatClaim.hypergeometricPValue 50 50 36 12 =
    (1255807221238 : ℚ) / 58971773773923) ∧
    (StatClaim.hypergeometricMass 50 50 36 12 =
    (30660923252400 : ℚ) / 4108366906249969) ∧
    (((12, 24) ∈ StatClaim.fisherRejectionRegionAt 50 50 ((1 : ℚ) / 20)) ↔ True) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw 50 50 p).real (StatClaim.fisherRejectionRegionAt 50 50 (( 1 : ℚ) / 20)) ≤
      ((1 : ℝ) / 20))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/paper/fisher_sample_size.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

namespace sizing_verification_claim_plan

def declaredSizes : StatClaim.FixedSampleDesign := ⟨36, 36, by decide, by decide⟩
def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := StatClaim.Modules.FisherPower.analysis declaredSizes declaredLevel
noncomputable def planningPoint : StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.FisherPower.ratePoint 1 10 2 5 (by decide) (by decide) (by decide) (by decide)

end sizing_verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (sizing_verification_claim_plan.declaredSizes.nControl = 36 ∧ sizing_verification_claim_plan.declaredSizes.nTreatment = 36 ∧
    0 < sizing_verification_claim_plan.declaredSizes.nControl ∧ 0 < sizing_verification_claim_plan.declaredSizes.nTreatment) ∧
    ((sizing_verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((sizing_verification_claim_plan.declaredAnalysis.powerClaim (fun parameter => parameter = sizing_verification_claim_plan.planningPoint)
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement) ∧
    (∀ (n : ℕ) (positive : 0 < n) (lower : 2 ≤ n) (upper : n < 36),
      ((StatClaim.Core.Policy.fixed (StatClaim.Modules.TwoArmBinomial.model
        ⟨n, 1 * n, positive, Nat.mul_pos (by decide) positive⟩)).law sizing_verification_claim_plan.planningPoint).real
        (StatClaim.Modules.FisherPower.analysis ⟨n, 1 * n, positive, Nat.mul_pos (by decide) positive⟩
          sizing_verification_claim_plan.declaredLevel).rejection <
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/paper/simon_design.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The participants in the first and the second stage. -/
def stages : ℕ × ℕ := (9, 15)

def analysis_design : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign stages.1 stages.2 0 2

noncomputable def analysis :=
  StatClaim.Modules.TwoStageBinomial.analysisAtMost analysis_design (StatClaim.ratPoint 1 20 (by decide) (by decide))

namespace checked_claim_plan

def declaredDesign : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign 9 15 0 2
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 20 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.TwoStageBinomial.analysisAtMost declaredDesign nullRate

end checked_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (checked_claim_plan.declaredDesign.nFirst = 9 ∧ checked_claim_plan.declaredDesign.nSecond = 15) ∧
    ((checked_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement) ∧
    ((checked_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 1 4 (by decide) (by decide))
      (((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/paper/simon_search.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The participants in the first and the second stage. -/
def stages : ℕ × ℕ := (9, 15)

def analysis_design : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign stages.1 stages.2 0 2

noncomputable def analysis :=
  StatClaim.Modules.TwoStageBinomial.analysisAtMost analysis_design (StatClaim.ratPoint 1 20 (by decide) (by decide))

namespace checked_claim_plan

def declaredDesign : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign 9 15 0 2
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 20 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.TwoStageBinomial.analysisAtMost declaredDesign nullRate

end checked_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (checked_claim_plan.declaredDesign.nFirst = 9 ∧ checked_claim_plan.declaredDesign.nSecond = 15) ∧
    ((checked_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement) ∧
    ((checked_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 1 4 (by decide) (by decide))
      (((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/planning.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨20, 20, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

namespace sizing_verification_claim_plan

def declaredSizes : StatClaim.FixedSampleDesign := ⟨36, 36, by decide, by decide⟩
def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := StatClaim.Modules.FisherPower.analysis declaredSizes declaredLevel
noncomputable def planningPoint : StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.FisherPower.ratePoint 1 10 2 5 (by decide) (by decide) (by decide) (by decide)

end sizing_verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (sizing_verification_claim_plan.declaredSizes.nControl = 36 ∧ sizing_verification_claim_plan.declaredSizes.nTreatment = 36 ∧
    0 < sizing_verification_claim_plan.declaredSizes.nControl ∧ 0 < sizing_verification_claim_plan.declaredSizes.nTreatment) ∧
    ((sizing_verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((sizing_verification_claim_plan.declaredAnalysis.powerClaim (fun parameter => parameter = sizing_verification_claim_plan.planningPoint)
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement) ∧
    (∀ (n : ℕ) (positive : 0 < n) (lower : 2 ≤ n) (upper : n < 36),
      ((StatClaim.Core.Policy.fixed (StatClaim.Modules.TwoArmBinomial.model
        ⟨n, 1 * n, positive, Nat.mul_pos (by decide) positive⟩)).law sizing_verification_claim_plan.planningPoint).real
        (StatClaim.Modules.FisherPower.analysis ⟨n, 1 * n, positive, Nat.mul_pos (by decide) positive⟩
          sizing_verification_claim_plan.declaredLevel).rejection <
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/playground.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨20, 20, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes plan analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim plan_compatible
      (analysis_level.value : ℝ)).statement

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/randomisation.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.pain_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨20, 20, by decide, by decide⟩, randomisation := some "complete", better := some "lower" }).Parameter
def Instance.pain_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨20, 20, by decide, by decide⟩, randomisation := some "complete", better := some "lower" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.pain_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨20, 20, by decide, by decide⟩, randomisation := some "complete", better := some "lower" }).space
def Instance.pain (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨20, 20, by decide, by decide⟩, randomisation := some "complete", better := some "lower" }).model
def Instance.practice_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).Parameter
def Instance.practice_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.practice_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).space
def Instance.practice (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).model

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

def clustered_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 40 → (Fin 40 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 40 Value)
      (sharp : StatClaim.Modules.Randomisation.SharpNull outcomes),
      (MeasureTheory.Measure.pi (fun _ : Fin (9999 + 1) => StatClaim.Modules.Randomisation.law 40 20)).real
        (StatClaim.Modules.Randomisation.drawnRejection 9999 statistic outcomes analysis_level.value) ≤
      (analysis_level.value : ℝ)) ∧
  (∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 12 → (Fin 12 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 12 Value)
      (sharp : StatClaim.Modules.Randomisation.SharpNull outcomes),
      (StatClaim.Modules.Randomisation.law 12 6).real
        (StatClaim.Modules.Randomisation.rejection 12 6 statistic outcomes clustered_level.value) ≤
      (clustered_level.value : ℝ))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/randomisation_family.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.pain_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩, randomisation := some "blocked", blockSize := some 4, better := some "lower" }).Parameter
def Instance.pain_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩, randomisation := some "blocked", blockSize := some 4, better := some "lower" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.pain_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩, randomisation := some "blocked", blockSize := some 4, better := some "lower" }).space
def Instance.pain (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩, randomisation := some "blocked", blockSize := some 4, better := some "lower" }).model
def Instance.primary_member_Parameter (i : Instance) : Type := (i.member "primary").law.Parameter
def Instance.primary_member_Outcome (i : Instance) : Type := (i.member "primary").law.Outcome
instance (i : Instance) : MeasurableSpace (Instance.primary_member_Outcome i) :=
  (i.member "primary").law.space
def Instance.primary_member (i : Instance) := (i.member "primary").law.model
def Instance.primary_member_hypothesis (i : Instance) := (i.member "primary").null
def Instance.primary_member_test (i : Instance) := (i.member "primary").procedure
def Instance.primary_member_slack (i : Instance) : ℝ := i.slack "primary"

def relief_sizes : StatClaim.FixedSampleDesign :=
  ⟨60, 60, by decide, by decide⟩

noncomputable def relief := StatClaim.Modules.TwoArmBinomial.model relief_sizes

def primary_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed relief

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def secondary_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def secondary :=
  StatClaim.Modules.Fisher.analysis relief_sizes design secondary_level

def primary_member_null (i : Instance) :=
  i.primary_member_hypothesis

structure Premises (i : Instance) : Prop where
  member_primary_member_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.finiteSample i.primary_member.law (primary_member_null i)
    i.primary_member_test ((1 : ℚ) / 20) i.primary_member_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.primary_member_Parameter i.primary_member_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ i.primary_member.law →
      v₁.Marginal σ relief.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => (primary_member_null i) (v₀.parameter θ),
        fun θ => secondary.hypothesis (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.primary_member_test.reject,
        v₁.outcome ⁻¹' secondary.procedure.rejectionEvent]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.primary_member_slack, 0] k)) ∧
  (∀ {Record : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.GroupedAssignment [(4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2)] → Record → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.GroupedAssignment [(4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2)] → Record)
      (sharp : ∀ first second, outcomes first = outcomes second),
      (MeasureTheory.Measure.pi (fun _ : Fin (9999 + 1) => StatClaim.Modules.Randomisation.groupedLaw [(4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2)])).real
        (StatClaim.Modules.Randomisation.drawnRejection 9999 statistic outcomes primary_level.value) ≤
      (primary_level.value : ℝ))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.member_primary_member_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/recycling.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.per_protocol_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter
def Instance.per_protocol_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.per_protocol_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).space
def Instance.per_protocol (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).model
def Instance.everyone_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter
def Instance.everyone_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.everyone_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).space
def Instance.everyone (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).model
def Instance.trough_not_worse_test (i : Instance) :=
  i.test "trough_not_worse" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.trough_not_worse_slack (i : Instance) : ℝ := i.slack "trough_not_worse"
def Instance.peak_not_worse_test (i : Instance) :=
  i.test "peak_not_worse" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.peak_not_worse_slack (i : Instance) : ℝ := i.slack "peak_not_worse"
def Instance.peak_better_test (i : Instance) :=
  i.test "peak_better" { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }
def Instance.peak_better_slack (i : Instance) : ℝ := i.slack "peak_better"
def Instance.graph_procedure (i : Instance) (Θ Ω : Type) [MeasurableSpace Ω]
    (σ : StatClaim.Interface.JointStudy Θ Ω) (v0 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome) (v1 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome) (v2 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome) :
    Fin 3 → Set Ω :=
  i.graph "primary" [(StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ })] 3 Θ Ω σ (v0, v1, v2, PUnit.unit)
def Instance.graph_slack (i : Instance) : ℝ := i.slack "primary"
def Instance.capacity_test (i : Instance) :=
  i.test "capacity" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.capacity_slack (i : Instance) : ℝ := i.slack "capacity"
def Instance.onset_member_Parameter (i : Instance) : Type := (i.member "onset").law.Parameter
def Instance.onset_member_Outcome (i : Instance) : Type := (i.member "onset").law.Outcome
instance (i : Instance) : MeasurableSpace (Instance.onset_member_Outcome i) :=
  (i.member "onset").law.space
def Instance.onset_member (i : Instance) := (i.member "onset").law.model
def Instance.onset_member_hypothesis (i : Instance) := (i.member "onset").null
def Instance.onset_member_test (i : Instance) := (i.member "onset").procedure
def Instance.onset_member_slack (i : Instance) : ℝ := i.slack "onset"

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨500, 500, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.per_protocol.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-50 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.everyone.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.everyone.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

def onset_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def design_2 :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_2_compatible :
    StatClaim.Core.Compatibility design_2 :=
  StatClaim.Core.Compatibility.fixed _

def null_2 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

noncomputable def onset :=
  StatClaim.Modules.FisherOneSided.analysis responders_sizes onset_level

def onset_member_null (i : Instance) :=
  i.onset_member_hypothesis

structure Premises (i : Instance) : Prop where
  cited_trough_not_worse_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.trough_not_worse_test ((1 : ℚ) / 40) i.trough_not_worse_slack
  cited_peak_not_worse_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.peak_not_worse_test ((1 : ℚ) / 40) i.peak_not_worse_slack
  cited_peak_better_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.everyone.law (null_1 i)
    i.peak_better_test ((1 : ℚ) / 40) i.peak_better_slack
  cited_graph_rule : StatClaim.Interface.Scope.largeSample.permits i.graph_slack ∧
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)
  cited_capacity_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.capacity_test ((1 : ℚ) / 40) i.capacity_slack
  member_onset_member_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.finiteSample i.onset_member.law (onset_member_null i)
    i.onset_member_test ((1 : ℚ) / 40) i.onset_member_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)) ∧
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₄ : StatClaim.Interface.MemberView Θ Ω i.onset_member_Parameter i.onset_member_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      v₃.Marginal σ i.per_protocol.law →
      v₄.Marginal σ i.onset_member.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => (onset_member_null i) (v₄.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.capacity_test.reject,
        v₄.outcome ⁻¹' i.onset_member_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.capacity_slack, i.onset_member_slack] k))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_trough_not_worse_level, h.cited_peak_not_worse_level, h.cited_peak_better_level, h.cited_graph_rule, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_trough_not_worse_level, h.cited_peak_not_worse_level, h.cited_peak_better_level, h.cited_graph_rule, h.cited_capacity_level, h.member_onset_member_level, trivial⟩

-- program: examples/regression.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.paired_Parameter (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }).Parameter
def Instance.paired_Outcome (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.paired_Outcome i) :=
  (i.studies { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }).space
def Instance.paired (i : Instance) := (i.studies { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }).model
def Instance.conditional_test (i : Instance) :=
  i.studyTest "conditional" { design := .matched_case_control, pairs := some 220, exposure := "benzodiazepine use", outcome := "hip fracture" }
def Instance.conditional_slack (i : Instance) : ℝ := i.slack "conditional"
def Instance.workers_Parameter (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).Parameter
def Instance.workers_Outcome (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.workers_Outcome i) :=
  (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).space
def Instance.workers (i : Instance) := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).model
def Instance.rates_test (i : Instance) :=
  i.studyTest "rates" { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }
def Instance.rates_slack (i : Instance) : ℝ := i.slack "rates"
def Instance.followed_Parameter (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 600, unexposed := some 1200, exposure := "statin use", outcome := "dementia" }).Parameter
def Instance.followed_Outcome (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 600, unexposed := some 1200, exposure := "statin use", outcome := "dementia" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.followed_Outcome i) :=
  (i.studies { design := .cohort, exposed := some 600, unexposed := some 1200, exposure := "statin use", outcome := "dementia" }).space
def Instance.followed (i : Instance) := (i.studies { design := .cohort, exposed := some 600, unexposed := some 1200, exposure := "statin use", outcome := "dementia" }).model
def Instance.risk_test (i : Instance) :=
  i.studyTest "risk" { design := .cohort, exposed := some 600, unexposed := some 1200, exposure := "statin use", outcome := "dementia" }
def Instance.risk_slack (i : Instance) : ℝ := i.slack "risk"
def Instance.clinic_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }).Parameter
def Instance.clinic_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.clinic_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }).space
def Instance.clinic (i : Instance) := (i.studies { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }).model
def Instance.fitted_test (i : Instance) :=
  i.studyTest "fitted" { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }
def Instance.fitted_slack (i : Instance) : ℝ := i.slack "fitted"
def Instance.unadjusted_test (i : Instance) :=
  i.studyTest "unadjusted" { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }
def Instance.unadjusted_slack (i : Instance) : ℝ := i.slack "unadjusted"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.paired.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.paired.noAssociation

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.workers.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.workers.noAssociation

noncomputable def design_2 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.followed.toModel

noncomputable def design_2_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_2 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_2 (i : Instance) :=
  i.followed.noAssociation

noncomputable def design_3 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.clinic.toModel

noncomputable def design_3_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_3 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_3 (i : Instance) :=
  i.clinic.noAssociation

structure Premises (i : Instance) : Prop where
  cited_conditional_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.conditional_logistic.scope i.paired.law (null i)
    i.conditional_test ((1 : ℚ) / 20) i.conditional_slack
  cited_rates_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.poisson_rate_regression.scope i.workers.law (null_1 i)
    i.rates_test ((1 : ℚ) / 20) i.rates_slack
  cited_risk_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.modified_poisson.scope i.followed.law (null_2 i)
    i.risk_test ((1 : ℚ) / 20) i.risk_slack
  cited_fitted_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.linear_association.scope i.clinic.law (null_3 i)
    i.fitted_test ((1 : ℚ) / 20) i.fitted_slack
  cited_unadjusted_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.linear_association.scope i.clinic.law (null_3 i)
    i.unadjusted_test ((1 : ℚ) / 20) i.unadjusted_slack

def Claims (i : Instance) : Prop :=
  (StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.conditional_test ((↑((1 : ℚ) / 20) : ℝ) + i.conditional_slack)) ∧
  (StatClaim.Interface.typeIClaim (design_1_compatible i) (null_1 i) i.rates_test ((↑((1 : ℚ) / 20) : ℝ) + i.rates_slack)) ∧
  (StatClaim.Interface.typeIClaim (design_2_compatible i) (null_2 i) i.risk_test ((↑((1 : ℚ) / 20) : ℝ) + i.risk_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_conditional_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_rates_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := ⟨h.cited_risk_level, trivial⟩

-- program: examples/shared_assignment.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.scores_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower", name := some "symptom score" }).Parameter
def Instance.scores_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower", name := some "symptom score" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.scores_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower", name := some "symptom score" }).space
def Instance.scores (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower", name := some "symptom score" }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower", name := some "symptom score" }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨120, 120, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis responders_sizes design response_level

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.scores.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.scores.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.scores.law (null_1 i)
    i.symptoms_test ((1 : ℚ) / 40) i.symptoms_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω i.scores_Parameter i.scores_Outcome),
      v₀.Marginal σ responders.law →
      v₁.Marginal σ i.scores.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' i.symptoms_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, i.symptoms_slack] k)) ∧
  ((response.typeIClaim design_compatible
      (response_level.value : ℝ)).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_symptoms_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/stratified_randomisation.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.pain_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨24, 24, by decide, by decide⟩, randomisation := some "blocked", strata := [(10, 10), (14, 14)], blockSize := some 4, better := some "lower" }).Parameter
def Instance.pain_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨24, 24, by decide, by decide⟩, randomisation := some "blocked", strata := [(10, 10), (14, 14)], blockSize := some 4, better := some "lower" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.pain_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨24, 24, by decide, by decide⟩, randomisation := some "blocked", strata := [(10, 10), (14, 14)], blockSize := some 4, better := some "lower" }).space
def Instance.pain (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨24, 24, by decide, by decide⟩, randomisation := some "blocked", strata := [(10, 10), (14, 14)], blockSize := some 4, better := some "lower" }).model
def Instance.practice_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "blocked", blockSize := some 2, better := some "higher" }).Parameter
def Instance.practice_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "blocked", blockSize := some 2, better := some "higher" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.practice_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "blocked", blockSize := some 2, better := some "higher" }).space
def Instance.practice (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "blocked", blockSize := some 2, better := some "higher" }).model

def blocked_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

def matched_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ {Record : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.GroupedAssignment [(4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2)] → Record → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.GroupedAssignment [(4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2)] → Record)
      (sharp : ∀ first second, outcomes first = outcomes second),
      (StatClaim.Modules.Randomisation.groupedLaw [(4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2)]).real
        (StatClaim.Modules.Randomisation.uniformRejection (StatClaim.Modules.Randomisation.groupedSplits [(4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2)]) statistic outcomes
          blocked_level.value) ≤ (blocked_level.value : ℝ)) ∧
  (∀ {Record : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.GroupedAssignment [(2, 1), (2, 1), (2, 1), (2, 1), (2, 1), (2, 1)] → Record → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.GroupedAssignment [(2, 1), (2, 1), (2, 1), (2, 1), (2, 1), (2, 1)] → Record)
      (sharp : ∀ first second, outcomes first = outcomes second),
      (StatClaim.Modules.Randomisation.groupedLaw [(2, 1), (2, 1), (2, 1), (2, 1), (2, 1), (2, 1)]).real
        (StatClaim.Modules.Randomisation.uniformRejection (StatClaim.Modules.Randomisation.groupedSplits [(2, 1), (2, 1), (2, 1), (2, 1), (2, 1), (2, 1)]) statistic outcomes
          matched_level.value) ≤ (matched_level.value : ℝ))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/t_test.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }).space
def Instance.study (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }).model
def Instance.analysis_test (i : Instance) :=
  i.test "analysis" { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }
def Instance.analysis_slack (i : Instance) : ℝ := i.slack "analysis"
def Instance.welch_test (i : Instance) :=
  i.test "welch" { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }
def Instance.welch_slack (i : Instance) : ℝ := i.slack "welch"
def Instance.small_arm_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨20, 40, by decide, by decide⟩ }).Parameter
def Instance.small_arm_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨20, 40, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.small_arm_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨20, 40, by decide, by decide⟩ }).space
def Instance.small_arm (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨20, 40, by decide, by decide⟩ }).model
def Instance.student_test (i : Instance) :=
  i.test "student" { outcome := .continuous, sizes := ⟨20, 40, by decide, by decide⟩ }
def Instance.student_slack (i : Instance) : ℝ := i.slack "student"

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

def margin (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-2 : ℚ)

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.small_arm.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.small_arm.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_analysis_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.study.law (null i)
    i.analysis_test ((1 : ℚ) / 20) i.analysis_slack
  cited_welch_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.study.law (margin i)
    i.welch_test ((1 : ℚ) / 40) i.welch_slack
  cited_student_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.small_arm.law (null_1 i)
    i.student_test ((1 : ℚ) / 20) i.student_slack

def Claims (i : Instance) : Prop :=
  (StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.analysis_test (↑((1 : ℚ) / 20) : ℝ)) ∧
  (StatClaim.Interface.typeIClaim (plan_compatible i) (margin i) i.welch_test ((↑((1 : ℚ) / 40) : ℝ) + i.welch_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_analysis_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_welch_level, trivial⟩

-- program: examples/three_outcomes.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨150, 150, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis study_sizes plan response_level

def remission_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 80), by norm_num, by norm_num⟩

noncomputable def remission :=
  StatClaim.Modules.Fisher.analysis study_sizes plan remission_level

def relapse_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 80), by norm_num, by norm_num⟩

noncomputable def relapse :=
  StatClaim.Modules.Fisher.analysis study_sizes plan relapse_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₂ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ study.law →
      v₁.Marginal σ study.law →
      v₂.Marginal σ study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => remission.hypothesis (v₁.parameter θ),
        fun θ => relapse.hypothesis (v₂.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' remission.procedure.rejectionEvent,
        v₂.outcome ⁻¹' relapse.procedure.rejectionEvent]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, 0, 0] k)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/trial_models.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.measured_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter
def Instance.measured_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.measured_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).space
def Instance.measured (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).model
def Instance.lung_function_test (i : Instance) :=
  i.test "lung_function" { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.lung_function_slack (i : Instance) : ℝ := i.slack "lung_function"
def Instance.response_test (i : Instance) :=
  i.test "response" { outcome := .binary, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.response_slack (i : Instance) : ℝ := i.slack "response"

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨300, 300, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.measured.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.measured.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-50 : ℚ)

noncomputable def design_1 :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_1_compatible :
    StatClaim.Core.Compatibility design_1 :=
  StatClaim.Core.Compatibility.fixed _

def null_1 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_lung_function_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.measured.law (null i)
    i.lung_function_test ((1 : ℚ) / 40) i.lung_function_slack
  cited_response_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.logistic_regression_one_sided.scope responders.law null_1
    i.response_test ((1 : ℚ) / 40) i.response_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.measured_Parameter i.measured_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ i.measured.law →
      v₁.Marginal σ responders.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => null_1 (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.lung_function_test.reject,
        v₁.outcome ⁻¹' i.response_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.lung_function_slack, i.response_slack] k)) ∧
  (StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.lung_function_test ((↑((1 : ℚ) / 40) : ℝ) + i.lung_function_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_lung_function_level, h.cited_response_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_lung_function_level, trivial⟩

-- program: examples/tutorial/01_first_claim.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim design_compatible
      (analysis_level.value : ℝ)).statement

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/02_reading_results.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim design_compatible
      (analysis_level.value : ℝ)).statement

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/04_observed_data.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (0 < 50 ∧ 0 < 50 ∧ 12 ≤ 50 ∧ 24 ≤ 50) ∧
    (∀ (k : ℕ),
      k ∈ StatClaim.hypergeometricSupport 50 50 36 ↔
      0 ≤ k ∧ k ≤ 36) ∧
    (StatClaim.hypergeometricPValue 50 50 36 12 =
    (1255807221238 : ℚ) / 58971773773923) ∧
    (StatClaim.hypergeometricMass 50 50 36 12 =
    (30660923252400 : ℚ) / 4108366906249969) ∧
    (((12, 24) ∈ StatClaim.fisherRejectionRegionAt 50 50 ((1 : ℚ) / 20)) ↔ True) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw 50 50 p).real (StatClaim.fisherRejectionRegionAt 50 50 (( 1 : ℚ) / 20)) ≤
      ((1 : ℝ) / 20))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/05_several_endpoints.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis study_sizes design response_level

def remission_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 80), by norm_num, by norm_num⟩

noncomputable def remission :=
  StatClaim.Modules.Fisher.analysis study_sizes design remission_level

def relapse_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 80), by norm_num, by norm_num⟩

noncomputable def relapse :=
  StatClaim.Modules.Fisher.analysis study_sizes design relapse_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₂ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ study.law →
      v₁.Marginal σ study.law →
      v₂.Marginal σ study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => remission.hypothesis (v₁.parameter θ),
        fun θ => relapse.hypothesis (v₂.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' remission.procedure.rejectionEvent,
        v₂.outcome ⁻¹' relapse.procedure.rejectionEvent]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, 0, 0] k)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/07_sample_size.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨25, 25, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

namespace verification_claim_plan

def declaredSizes : StatClaim.FixedSampleDesign := ⟨36, 36, by decide, by decide⟩
def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := StatClaim.Modules.FisherPower.analysis declaredSizes declaredLevel
noncomputable def planningPoint : StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.FisherPower.ratePoint 1 10 2 5 (by decide) (by decide) (by decide) (by decide)

end verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (verification_claim_plan.declaredSizes.nControl = 36 ∧ verification_claim_plan.declaredSizes.nTreatment = 36 ∧
    0 < verification_claim_plan.declaredSizes.nControl ∧ 0 < verification_claim_plan.declaredSizes.nTreatment) ∧
    ((verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((verification_claim_plan.declaredAnalysis.powerClaim (fun parameter => parameter = verification_claim_plan.planningPoint)
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement) ∧
    (∀ (n : ℕ) (positive : 0 < n) (lower : 20 ≤ n) (upper : n < 36),
      ((StatClaim.Core.Policy.fixed (StatClaim.Modules.TwoArmBinomial.model
        ⟨n, 1 * n, positive, Nat.mul_pos (by decide) positive⟩)).law verification_claim_plan.planningPoint).real
        (StatClaim.Modules.FisherPower.analysis ⟨n, 1 * n, positive, Nat.mul_pos (by decide) positive⟩
          verification_claim_plan.declaredLevel).rejection <
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/08_better_or_not_worse.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨36, 36, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def no_better : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

def superiority_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def superiority :=
  StatClaim.Modules.FisherOneSided.analysis study_sizes superiority_level

def trial_sizes : StatClaim.FixedSampleDesign :=
  ⟨60, 60, by decide, by decide⟩

noncomputable def trial := StatClaim.Modules.TwoArmBinomial.model trial_sizes

def too_much_worse : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost ((-1 : ℚ) / 10)

def non_inferiority_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def design_1 :=
  StatClaim.Core.StudyDesign.fixed trial

noncomputable def design_1_compatible :
    StatClaim.Core.Compatibility design_1 :=
  StatClaim.Core.Compatibility.fixed _

def non_inferiority_thresholds : List ℕ := [0, 0, 2, 3, 5, 6, 8, 9, 11, 12, 13, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 46, 47, 48, 49, 50, 50, 51, 52, 53, 53, 54, 55, 55, 56, 57, 57, 58, 59, 59]

noncomputable def non_inferiority :=
  StatClaim.Modules.DifferenceTest.analysis trial_sizes non_inferiority_thresholds ((-1 : ℚ) / 10)

namespace planned_claim_plan

def declaredSizes : StatClaim.FixedSampleDesign := ⟨36, 36, by decide, by decide⟩
def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 40, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := StatClaim.Modules.FisherOneSided.analysis declaredSizes declaredLevel
noncomputable def planningPoint : StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.FisherPower.ratePoint 1 10 2 5 (by decide) (by decide) (by decide) (by decide)

end planned_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((planned_claim_plan.declaredSizes.nControl = 36 ∧ planned_claim_plan.declaredSizes.nTreatment = 36 ∧
    0 < planned_claim_plan.declaredSizes.nControl ∧ 0 < planned_claim_plan.declaredSizes.nTreatment) ∧
    ((planned_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ))).statement) ∧
    ((planned_claim_plan.declaredAnalysis.powerClaim (fun parameter => parameter = planned_claim_plan.planningPoint)
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement)) ∧
  ((0 < 36 ∧ 0 < 36 ∧ 4 ≤ 36 ∧ 14 ≤ 36) ∧
    (StatClaim.Modules.FisherOneSided.lowerPValue 36 36 18 4 =
    (4212885 : ℚ) / 650576834) ∧
    ((StatClaim.Modules.FisherOneSided.lowerPValue 36 36 18 4 ≤ (1 : ℚ) / 40) ↔ True) ∧
    ((superiority.typeIClaim (superiority_level.value : ℝ)).statement)) ∧
  ((trial_sizes.nControl = 60 ∧ trial_sizes.nTreatment = 60 ∧
    0 < trial_sizes.nControl ∧ 0 < trial_sizes.nTreatment) ∧
    (((StatClaim.Modules.DifferenceTest.analysis trial_sizes non_inferiority_thresholds ((((0 : ℕ) : ℚ) - ((100 : ℕ) : ℚ)) / ((1000 : ℕ) : ℚ))).typeIClaim (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ))).statement) ∧
    (StatClaim.Modules.DifferenceTest.rejects 60 non_inferiority_thresholds 50 52 = false))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/tutorial/09_single_arm.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The number of participants in the arm. -/
def pilot : ℕ := 25

def test_design : StatClaim.Modules.OneSampleBinomial.Design :=
  StatClaim.Modules.OneSampleBinomial.levelDesign pilot 1 5 1 20

noncomputable def test :=
  StatClaim.Modules.OneSampleBinomial.analysis test_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

/-- The number of participants in the arm. -/
def study : ℕ := 35

def analysis_design : StatClaim.Modules.OneSampleBinomial.Design :=
  StatClaim.Modules.OneSampleBinomial.levelDesign study 1 5 1 20

noncomputable def analysis :=
  StatClaim.Modules.OneSampleBinomial.analysis analysis_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

namespace plan_claim_plan

def declaredDesign : StatClaim.Modules.OneSampleBinomial.Design :=
  ⟨35, 12⟩
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 5 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.OneSampleBinomial.analysis declaredDesign nullRate

end plan_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((plan_claim_plan.declaredDesign.n = 35 ∧ plan_claim_plan.declaredDesign.critical = 12) ∧
    ((plan_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((plan_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 2 5 (by decide) (by decide))
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement) ∧
    (StatClaim.Modules.OneSampleBinomial.criticalValue 35 1 5 1 20 = 12) ∧
    (∀ (n : ℕ) (lower : 10 ≤ n) (upper : n < 35),
      (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) <
        ((StatClaim.Modules.OneSampleBinomial.policy (StatClaim.Modules.OneSampleBinomial.levelDesign n 1 5 1 20)).law
          (StatClaim.ratPoint 1 5 (by decide) (by decide))).real
          {count | (StatClaim.Modules.OneSampleBinomial.levelDesign n 1 5 1 20).critical ≤ count} ∨
      ((StatClaim.Modules.OneSampleBinomial.policy (StatClaim.Modules.OneSampleBinomial.levelDesign n 1 5 1 20)).law
          (StatClaim.ratPoint 2 5 (by decide) (by decide))).real
          {count | (StatClaim.Modules.OneSampleBinomial.levelDesign n 1 5 1 20).critical ≤ count} <
        (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))) ∧
  ((((StatClaim.Modules.OneSampleBinomial.policy ⟨35, 14⟩).law (StatClaim.ratPoint 1 5 (by decide) (by decide))).real
        {count | 14 ≤ count} = (((3060372398554814309273 : ℕ) : ℝ) / ((582076609134674072265625 : ℕ) : ℝ))) ∧
    (StatClaim.Modules.OneSampleBinomial.criticalValue 35 1 5 1 20 = 12) ∧
    (12 ≤ 14) ∧
    (((StatClaim.Modules.OneSampleBinomial.analysis ⟨35, 12⟩ (StatClaim.ratPoint 1 5 (by decide) (by decide))).typeIClaim
      (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement)) ∧
  ((∀ (p : unitInterval),
      1 - 2 * (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) ≤
      (ProbabilityTheory.binomial 35 p).real
        {count | p ∈ StatClaim.Modules.BinomialInterval.confidenceSet 35 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) count}) ∧
    (∀ (p : unitInterval)
      (member : p ∈ StatClaim.Modules.BinomialInterval.confidenceSet 35 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) 14),
      StatClaim.ratPoint 2387 10000 (by decide) (by decide) ≤ p ∧
      p ≤ StatClaim.ratPoint 5789 10000 (by decide) (by decide)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/tutorial/10_stopping_early.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The participants in the first and the second stage. -/
def stages : ℕ × ℕ := (13, 30)

def proposed_design : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign stages.1 stages.2 3 12

noncomputable def proposed :=
  StatClaim.Modules.TwoStageBinomial.analysisAtMost proposed_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

namespace verification_claim_plan

def declaredDesign : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign 13 30 3 12
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 5 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.TwoStageBinomial.analysisAtMost declaredDesign nullRate

end verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (verification_claim_plan.declaredDesign.nFirst = 13 ∧ verification_claim_plan.declaredDesign.nSecond = 30) ∧
    ((verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((verification_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 2 5 (by decide) (by decide))
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/11_bayesian_rule.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The participants in the first and the second stage. -/
def stages : ℕ × ℕ := (10, 20)

def analysis_design : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.posteriorDesign stages.1 stages.2 1 1 1 5 1 2 19 20

noncomputable def analysis :=
  StatClaim.Modules.TwoStageBinomial.analysisAtMost analysis_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

namespace verification_claim_plan

def declaredDesign : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.posteriorDesign 10 20 1 1 1 5 1 2 19 20
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 5 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.TwoStageBinomial.analysisAtMost declaredDesign nullRate

end verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (verification_claim_plan.declaredDesign.nFirst = 10 ∧ verification_claim_plan.declaredDesign.nSecond = 20) ∧
    ((verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement) ∧
    ((verification_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 2 5 (by decide) (by decide))
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/12_continuous_outcome.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }).space
def Instance.study (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }).model
def Instance.analysis_test (i : Instance) :=
  i.test "analysis" { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }
def Instance.analysis_slack (i : Instance) : ℝ := i.slack "analysis"
def Instance.robust_test (i : Instance) :=
  i.test "robust" { outcome := .continuous, sizes := ⟨60, 60, by decide, by decide⟩ }
def Instance.robust_slack (i : Instance) : ℝ := i.slack "robust"

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_analysis_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.study.law (null i)
    i.analysis_test ((1 : ℚ) / 20) i.analysis_slack
  cited_robust_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test.scope i.study.law (null i)
    i.robust_test ((1 : ℚ) / 20) i.robust_slack

def Claims (i : Instance) : Prop :=
  (StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.analysis_test (↑((1 : ℚ) / 20) : ℝ)) ∧
  (StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.robust_test ((↑((1 : ℚ) / 20) : ℝ) + i.robust_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_analysis_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_robust_level, trivial⟩

-- program: examples/tutorial/13_mixed_endpoints.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.scores_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).Parameter
def Instance.scores_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.scores_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).space
def Instance.scores (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨120, 120, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis responders_sizes design response_level

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.scores.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.scores.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.scores.law (null_1 i)
    i.symptoms_test ((1 : ℚ) / 40) i.symptoms_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω i.scores_Parameter i.scores_Outcome),
      v₀.Marginal σ responders.law →
      v₁.Marginal σ i.scores.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' i.symptoms_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, i.symptoms_slack] k)) ∧
  ((response.typeIClaim design_compatible
      (response_level.value : ℝ)).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_symptoms_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/tutorial/14_interim_look.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.halfway_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }).Parameter
def Instance.halfway_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.halfway_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }).space
def Instance.halfway (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }).model
def Instance.complete_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).Parameter
def Instance.complete_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.complete_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).space
def Instance.complete (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).model
def Instance.interim_test (i : Instance) :=
  i.test "interim" { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }
def Instance.interim_slack (i : Instance) : ℝ := i.slack "interim"
def Instance.final_test (i : Instance) :=
  i.test "final" { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }
def Instance.final_slack (i : Instance) : ℝ := i.slack "final"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.halfway.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.halfway.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.complete.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.complete.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_interim_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.halfway.law (null i)
    i.interim_test ((1 : ℚ) / 200) i.interim_slack
  cited_final_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.complete.law (null_1 i)
    i.final_test ((9 : ℚ) / 200) i.final_slack

def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.halfway_Parameter i.halfway_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.complete_Parameter i.complete_Outcome),
      v₀.Marginal σ i.halfway.law →
      v₁.Marginal σ i.complete.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.interim_test.reject,
        v₁.outcome ⁻¹' i.final_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.interim_slack, i.final_slack] k)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_interim_level, h.cited_final_level, trivial⟩

-- program: examples/tutorial/15_confirmatory_trial.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.interim_cohort_Parameter (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }).Parameter
def Instance.interim_cohort_Outcome (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.interim_cohort_Outcome i) :=
  (i.laws { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }).space
def Instance.interim_cohort (i : Instance) := (i.laws { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }).model
def Instance.full_cohort_Parameter (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter
def Instance.full_cohort_Outcome (i : Instance) : Type := (i.laws { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.full_cohort_Outcome i) :=
  (i.laws { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }).space
def Instance.full_cohort (i : Instance) := (i.laws { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }).model
def Instance.interim_test (i : Instance) :=
  i.test "interim" { outcome := .survival, sizes := ⟨150, 150, by decide, by decide⟩ }
def Instance.interim_slack (i : Instance) : ℝ := i.slack "interim"
def Instance.final_test (i : Instance) :=
  i.test "final" { outcome := .survival, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.final_slack (i : Instance) : ℝ := i.slack "final"
def Instance.scores_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter
def Instance.scores_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.scores_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).space
def Instance.scores (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.interim_cohort.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.interim_cohort.null StatClaim.Generated.NullKey.equal_survival.shape (0 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.full_cohort.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.full_cohort.null StatClaim.Generated.NullKey.equal_survival.shape (0 : ℚ)

noncomputable def design_2 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.scores.toModel

noncomputable def design_2_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_2 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_2 (i : Instance) :=
  i.scores.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨300, 300, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design_3 :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_3_compatible :
    StatClaim.Core.Compatibility design_3 :=
  StatClaim.Core.Compatibility.fixed _

def null_3 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis responders_sizes design_3 response_level

structure Premises (i : Instance) : Prop where
  cited_interim_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.log_rank.scope i.interim_cohort.law (null i)
    i.interim_test ((1 : ℚ) / 200) i.interim_slack
  cited_final_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.log_rank.scope i.full_cohort.law (null_1 i)
    i.final_test ((9 : ℚ) / 200) i.final_slack
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.scores.law (null_2 i)
    i.symptoms_test ((1 : ℚ) / 20) i.symptoms_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.interim_cohort_Parameter i.interim_cohort_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.full_cohort_Parameter i.full_cohort_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.scores_Parameter i.scores_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ i.interim_cohort.law →
      v₁.Marginal σ i.full_cohort.law →
      v₂.Marginal σ i.scores.law →
      v₃.Marginal σ responders.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∀ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null_1 i) (v₁.parameter θ)] k θ,
        fun θ => (null_2 i) (v₂.parameter θ),
        fun θ => response.hypothesis (v₃.parameter θ)]
        ![(⋃ k, ![v₀.outcome ⁻¹' i.interim_test.reject, v₁.outcome ⁻¹' i.final_test.reject] k),
        v₂.outcome ⁻¹' i.symptoms_test.reject,
        v₃.outcome ⁻¹' response.procedure.rejectionEvent]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![(∑ k, ![i.interim_slack, i.final_slack] k), i.symptoms_slack, 0] k)) ∧
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.interim_cohort_Parameter i.interim_cohort_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.full_cohort_Parameter i.full_cohort_Outcome),
      v₀.Marginal σ i.interim_cohort.law →
      v₁.Marginal σ i.full_cohort.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.interim_test.reject,
        v₁.outcome ⁻¹' i.final_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.interim_slack, i.final_slack] k)) ∧
  ((response.typeIClaim design_3_compatible
      (response_level.value : ℝ)).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_interim_level, h.cited_final_level, h.cited_symptoms_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_interim_level, h.cited_final_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/tutorial/16_recycling.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.per_protocol_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter
def Instance.per_protocol_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.per_protocol_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).space
def Instance.per_protocol (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).model
def Instance.everyone_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter
def Instance.everyone_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.everyone_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).space
def Instance.everyone (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).model
def Instance.trough_not_worse_test (i : Instance) :=
  i.test "trough_not_worse" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.trough_not_worse_slack (i : Instance) : ℝ := i.slack "trough_not_worse"
def Instance.peak_not_worse_test (i : Instance) :=
  i.test "peak_not_worse" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.peak_not_worse_slack (i : Instance) : ℝ := i.slack "peak_not_worse"
def Instance.peak_better_test (i : Instance) :=
  i.test "peak_better" { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }
def Instance.peak_better_slack (i : Instance) : ℝ := i.slack "peak_better"
def Instance.graph_procedure (i : Instance) (Θ Ω : Type) [MeasurableSpace Ω]
    (σ : StatClaim.Interface.JointStudy Θ Ω) (v0 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome) (v1 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome) (v2 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome) :
    Fin 3 → Set Ω :=
  i.graph "primary" [(StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ })] 3 Θ Ω σ (v0, v1, v2, PUnit.unit)
def Instance.graph_slack (i : Instance) : ℝ := i.slack "primary"
def Instance.capacity_test (i : Instance) :=
  i.test "capacity" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.capacity_slack (i : Instance) : ℝ := i.slack "capacity"
def Instance.onset_member_Parameter (i : Instance) : Type := (i.member "onset").law.Parameter
def Instance.onset_member_Outcome (i : Instance) : Type := (i.member "onset").law.Outcome
instance (i : Instance) : MeasurableSpace (Instance.onset_member_Outcome i) :=
  (i.member "onset").law.space
def Instance.onset_member (i : Instance) := (i.member "onset").law.model
def Instance.onset_member_hypothesis (i : Instance) := (i.member "onset").null
def Instance.onset_member_test (i : Instance) := (i.member "onset").procedure
def Instance.onset_member_slack (i : Instance) : ℝ := i.slack "onset"

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨500, 500, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.per_protocol.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-50 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.everyone.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.everyone.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

def onset_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def design_2 :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_2_compatible :
    StatClaim.Core.Compatibility design_2 :=
  StatClaim.Core.Compatibility.fixed _

def null_2 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

noncomputable def onset :=
  StatClaim.Modules.FisherOneSided.analysis responders_sizes onset_level

def onset_member_null (i : Instance) :=
  i.onset_member_hypothesis

structure Premises (i : Instance) : Prop where
  cited_trough_not_worse_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.trough_not_worse_test ((1 : ℚ) / 40) i.trough_not_worse_slack
  cited_peak_not_worse_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.peak_not_worse_test ((1 : ℚ) / 40) i.peak_not_worse_slack
  cited_peak_better_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.everyone.law (null_1 i)
    i.peak_better_test ((1 : ℚ) / 40) i.peak_better_slack
  cited_graph_rule : StatClaim.Interface.Scope.largeSample.permits i.graph_slack ∧
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)
  cited_capacity_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.capacity_test ((1 : ℚ) / 40) i.capacity_slack
  member_onset_member_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.finiteSample i.onset_member.law (onset_member_null i)
    i.onset_member_test ((1 : ℚ) / 40) i.onset_member_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)) ∧
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₄ : StatClaim.Interface.MemberView Θ Ω i.onset_member_Parameter i.onset_member_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      v₃.Marginal σ i.per_protocol.law →
      v₄.Marginal σ i.onset_member.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => (onset_member_null i) (v₄.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.capacity_test.reject,
        v₄.outcome ⁻¹' i.onset_member_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.capacity_slack, i.onset_member_slack] k))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_trough_not_worse_level, h.cited_peak_not_worse_level, h.cited_peak_better_level, h.cited_graph_rule, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_trough_not_worse_level, h.cited_peak_not_worse_level, h.cited_peak_better_level, h.cited_graph_rule, h.cited_capacity_level, h.member_onset_member_level, trivial⟩

-- program: examples/tutorial/17_declared_test.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).space
def Instance.study (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).model
def Instance.pain_test (i : Instance) :=
  i.test "pain" { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }
def Instance.pain_slack (i : Instance) : ℝ := i.slack "pain"
def Instance.function_test (i : Instance) :=
  i.test "function" { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }
def Instance.function_slack (i : Instance) : ℝ := i.slack "function"

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  declared_pain_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.study.law (null i)
    i.pain_test ((1 : ℚ) / 40) i.pain_slack
  cited_function_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.study.law (null i)
    i.function_test ((1 : ℚ) / 40) i.function_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome),
      v₀.Marginal σ i.study.law →
      v₁.Marginal σ i.study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.pain_test.reject,
        v₁.outcome ⁻¹' i.function_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.pain_slack, i.function_slack] k)) ∧
  (StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.pain_test ((↑((1 : ℚ) / 40) : ℝ) + i.pain_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.declared_pain_level, h.cited_function_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.declared_pain_level, trivial⟩

-- program: examples/tutorial/19_shared_assignment.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.scores_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower" }).Parameter
def Instance.scores_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.scores_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower" }).space
def Instance.scores (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower" }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, better := some "lower" }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨120, 120, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis responders_sizes design response_level

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.scores.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.scores.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.scores.law (null_1 i)
    i.symptoms_test ((1 : ℚ) / 40) i.symptoms_slack

def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω i.scores_Parameter i.scores_Outcome),
      v₀.Marginal σ responders.law →
      v₁.Marginal σ i.scores.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' i.symptoms_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, i.symptoms_slack] k)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_symptoms_level, trivial⟩

-- program: examples/tutorial/20_clusters_and_visits.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.visits_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, measurements := some 3 }).Parameter
def Instance.visits_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, measurements := some 3 }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.visits_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, measurements := some 3 }).space
def Instance.visits (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, measurements := some 3 }).model
def Instance.symptoms_test (i : Instance) :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨150, 150, by decide, by decide⟩, measurements := some 3 }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"
def Instance.practice_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12) }).Parameter
def Instance.practice_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12) }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.practice_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12) }).space
def Instance.practice (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12) }).model
def Instance.adherence_test (i : Instance) :=
  i.test "adherence" { outcome := .continuous, sizes := ⟨240, 240, by decide, by decide⟩, clusters := some (12, 12) }
def Instance.adherence_slack (i : Instance) : ℝ := i.slack "adherence"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.visits.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.visits.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.practice.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.practice.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test.scope i.visits.law (null i)
    i.symptoms_test ((1 : ℚ) / 20) i.symptoms_slack
  declared_adherence_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.practice.law (null_1 i)
    i.adherence_test ((1 : ℚ) / 20) i.adherence_slack

def Claims (i : Instance) : Prop :=
  (StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.symptoms_test ((↑((1 : ℚ) / 20) : ℝ) + i.symptoms_slack)) ∧
  (StatClaim.Interface.typeIClaim (design_1_compatible i) (null_1 i) i.adherence_test ((↑((1 : ℚ) / 20) : ℝ) + i.adherence_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_symptoms_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.declared_adherence_level, trivial⟩

-- program: examples/tutorial/21_randomisation_test.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.practice_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).Parameter
def Instance.practice_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.practice_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).space
def Instance.practice (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩, clusters := some (6, 6), randomisation := some "complete", better := some "higher" }).model

def adherence_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 12 → (Fin 12 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 12 Value)
      (sharp : StatClaim.Modules.Randomisation.SharpNull outcomes),
      (StatClaim.Modules.Randomisation.law 12 6).real
        (StatClaim.Modules.Randomisation.rejection 12 6 statistic outcomes adherence_level.value) ≤
      (adherence_level.value : ℝ)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/22_population_and_names.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def response_sizes : StatClaim.FixedSampleDesign :=
  ⟨40, 40, by decide, by decide⟩

noncomputable def response := StatClaim.Modules.TwoArmBinomial.model response_sizes

def primary_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

def adherent_sizes : StatClaim.FixedSampleDesign :=
  ⟨34, 35, by decide, by decide⟩

noncomputable def adherent := StatClaim.Modules.TwoArmBinomial.model adherent_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed adherent

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def supportive_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def supportive :=
  StatClaim.Modules.Fisher.analysis adherent_sizes design supportive_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 80 → (Fin 80 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 80 Value)
      (sharp : StatClaim.Modules.Randomisation.SharpNull outcomes),
      (MeasureTheory.Measure.pi (fun _ : Fin (9999 + 1) => StatClaim.Modules.Randomisation.law 80 40)).real
        (StatClaim.Modules.Randomisation.drawnRejection 9999 statistic outcomes primary_level.value) ≤
      (primary_level.value : ℝ)) ∧
  ((supportive.typeIClaim design_compatible
      (supportive_level.value : ℝ)).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial

-- program: examples/tutorial/23_observational_studies.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.followed_Parameter (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).Parameter
def Instance.followed_Outcome (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.followed_Outcome i) :=
  (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).space
def Instance.followed (i : Instance) := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).model
def Instance.sampled_Parameter (i : Instance) : Type := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).Parameter
def Instance.sampled_Outcome (i : Instance) : Type := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.sampled_Outcome i) :=
  (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).space
def Instance.sampled (i : Instance) := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).model
def Instance.surveyed_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 1200, exposure := "smoking", outcome := "wheeze" }).Parameter
def Instance.surveyed_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 1200, exposure := "smoking", outcome := "wheeze" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.surveyed_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 1200, exposure := "smoking", outcome := "wheeze" }).space
def Instance.surveyed (i : Instance) := (i.studies { design := .cross_sectional, n := some 1200, exposure := "smoking", outcome := "wheeze" }).model

def by_cohort_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def by_cohort_groups : StatClaim.FixedSampleDesign :=
  ⟨400, 200, by decide, by decide⟩

noncomputable def by_cohort_study := StatClaim.Modules.TwoArmBinomial.model by_cohort_groups

noncomputable def by_cohort_design :=
  StatClaim.Core.StudyDesign.fixed by_cohort_study

noncomputable def by_cohort_compatible :
    StatClaim.Core.Compatibility by_cohort_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def by_cohort :=
  StatClaim.Modules.Fisher.analysis by_cohort_groups by_cohort_design by_cohort_level

def by_cases_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def by_cases_groups : StatClaim.FixedSampleDesign :=
  ⟨300, 150, by decide, by decide⟩

noncomputable def by_cases_study := StatClaim.Modules.TwoArmBinomial.model by_cases_groups

noncomputable def by_cases_design :=
  StatClaim.Core.StudyDesign.fixed by_cases_study

noncomputable def by_cases_compatible :
    StatClaim.Core.Compatibility by_cases_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def by_cases :=
  StatClaim.Modules.Fisher.analysis by_cases_groups by_cases_design by_cases_level

def by_survey_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((by_cohort.typeIClaim by_cohort_compatible (by_cohort_level.value : ℝ)).statement) ∧
  ((by_cases.typeIClaim by_cases_compatible (by_cases_level.value : ℝ)).statement) ∧
  (∀ (q p : unitInterval),
      (StatClaim.Modules.Association.mixtureLaw 1200 q p).real
        (StatClaim.Modules.Association.mixtureRejection 1200 by_survey_level.value) ≤
      (by_survey_level.value : ℝ))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/tutorial/24_observed_tables.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.followed_Parameter (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).Parameter
def Instance.followed_Outcome (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.followed_Outcome i) :=
  (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).space
def Instance.followed (i : Instance) := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).model
def Instance.sampled_Parameter (i : Instance) : Type := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).Parameter
def Instance.sampled_Outcome (i : Instance) : Type := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.sampled_Outcome i) :=
  (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).space
def Instance.sampled (i : Instance) := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).model

def by_cohort_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def by_cohort_groups : StatClaim.FixedSampleDesign :=
  ⟨400, 200, by decide, by decide⟩

noncomputable def by_cohort_study := StatClaim.Modules.TwoArmBinomial.model by_cohort_groups

noncomputable def by_cohort_design :=
  StatClaim.Core.StudyDesign.fixed by_cohort_study

noncomputable def by_cohort_compatible :
    StatClaim.Core.Compatibility by_cohort_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def by_cohort :=
  StatClaim.Modules.Fisher.analysis by_cohort_groups by_cohort_design by_cohort_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((by_cohort_groups.nControl = 400 ∧ by_cohort_groups.nTreatment = 200 ∧ 0 < by_cohort_groups.nControl ∧
    0 < by_cohort_groups.nTreatment) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw by_cohort_groups.nControl by_cohort_groups.nTreatment p).real
        (StatClaim.fisherRejectionRegionAt by_cohort_groups.nControl by_cohort_groups.nTreatment by_cohort_level.value) ≤
      (by_cohort_level.value : ℝ)) ∧
    (StatClaim.hypergeometricPValue 400 200 55 25 =
    (190605870252878963571441524716493165335982561118267997 : ℚ) / 232891519498121670674152327158592534015281863472632122017) ∧
    (StatClaim.hypergeometricMass 400 200 55 25 =
    (837796902883397018295466104752922519839855879424 : ℚ) / 2333839596529894784737319014706957019463887437218853) ∧
    (((25, 30) ∈ StatClaim.fisherRejectionRegionAt 400 200 ((1 : ℚ) / 20)) ↔ True)) ∧
  ((∀ (pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 400 200 pc pt).real
      ({a | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 400 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
        {b | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 200 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 400 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 25)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 200 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 30)
      (positive : 0 < (pc : ℝ)),
      (((49 : ℕ) : ℝ) / ((500 : ℕ) : ℝ)) / (((119 : ℕ) : ℝ) / ((1250 : ℕ) : ℝ)) ≤ (pt : ℝ) / pc ∧
      (pt : ℝ) / pc ≤ (((431 : ℕ) : ℝ) / ((2000 : ℕ) : ℝ)) / (((383 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)))) ∧
  ((∀ (pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 400 200 pc pt).real
      ({a | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 400 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
        {b | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 200 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 400 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 25)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 200 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 30),
      (((49 : ℕ) : ℝ) / ((500 : ℕ) : ℝ)) - (((119 : ℕ) : ℝ) / ((1250 : ℕ) : ℝ)) ≤ (pt : ℝ) - (pc : ℝ) ∧
      (pt : ℝ) - (pc : ℝ) ≤ (((431 : ℕ) : ℝ) / ((2000 : ℕ) : ℝ)) - (((383 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)))) ∧
  ((∀ (pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 300 150 pc pt).real
      ({a | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 300 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
        {b | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 150 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 300 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 140)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 150 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 90)
      (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1),
      StatClaim.Modules.Association.odds (((316 : ℕ) : ℝ) / ((625 : ℕ) : ℝ)) / StatClaim.Modules.Association.odds (((5329 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds pt / StatClaim.Modules.Association.odds pc ∧
      StatClaim.Modules.Association.odds pt / StatClaim.Modules.Association.odds pc ≤ StatClaim.Modules.Association.odds (((3447 : ℕ) : ℝ) / ((5000 : ℕ) : ℝ)) / StatClaim.Modules.Association.odds (((4013 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ))))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i ∧ program.claimAt 3 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 3) := trivial

-- program: examples/tutorial/25_matched_pairs.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.paired_Parameter (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 150, exposure := "smoking", outcome := "lung cancer" }).Parameter
def Instance.paired_Outcome (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 150, exposure := "smoking", outcome := "lung cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.paired_Outcome i) :=
  (i.studies { design := .matched_case_control, pairs := some 150, exposure := "smoking", outcome := "lung cancer" }).space
def Instance.paired (i : Instance) := (i.studies { design := .matched_case_control, pairs := some 150, exposure := "smoking", outcome := "lung cancer" }).model

def by_pairs_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ (δ : unitInterval),
      (StatClaim.Modules.Matched.pairsLaw 150 δ StatClaim.Modules.Matched.half).real
        (StatClaim.Modules.Matched.pairsRejection 150 (by_pairs_level.value : ℝ)) ≤ (by_pairs_level.value : ℝ)) ∧
  ((150 = 150 ∧ 0 < 150) ∧
    (∀ (δ π : unitInterval),
      StatClaim.Modules.Matched.pairsLaw 150 δ π Set.univ = 1) ∧
    (∀ (δ : unitInterval),
      (StatClaim.Modules.Matched.pairsLaw 150 δ StatClaim.Modules.Matched.half).real
        (StatClaim.Modules.Matched.pairsRejection 150 (by_pairs_level.value : ℝ)) ≤ (by_pairs_level.value : ℝ)) ∧
    (StatClaim.Modules.OneSampleBinomial.tailNumerator 50 1 2 35 = 3715721875476 ∧
    StatClaim.Modules.BinomialInterval.lowerNumerator 50 1 2 35 = 1124435014542268) ∧
    (((50, 35) ∈ StatClaim.Modules.Matched.pairsRejection 150 (by_pairs_level.value : ℝ)) ↔ True)) ∧
  ((∀ (δ π : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.Modules.Matched.pairsLaw 150 δ π).real
      (StatClaim.Modules.Association.given 150
        (fun d => {x | π ∈ StatClaim.Modules.BinomialInterval.confidenceSet d (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) x}))) ∧
    (∀ (π : unitInterval)
      (member : π ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) 35) (below : (π : ℝ) < 1),
      StatClaim.Modules.Association.odds (((5539 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds π ∧
      StatClaim.Modules.Association.odds π ≤ StatClaim.Modules.Association.odds (((4107 : ℕ) : ℝ) / ((5000 : ℕ) : ℝ))))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial

-- program: examples/tutorial/26_prevalence_and_rates.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.survey_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 800, exposure := "night shifts", outcome := "insomnia" }).Parameter
def Instance.survey_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 800, exposure := "night shifts", outcome := "insomnia" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.survey_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 800, exposure := "night shifts", outcome := "insomnia" }).space
def Instance.survey (i : Instance) := (i.studies { design := .cross_sectional, n := some 800, exposure := "night shifts", outcome := "insomnia" }).model
def Instance.followed_Parameter (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).Parameter
def Instance.followed_Outcome (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.followed_Outcome i) :=
  (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).space
def Instance.followed (i : Instance) := (i.studies { design := .cohort, exposed := some 200, unexposed := some 400, exposure := "smoking", outcome := "asthma" }).model
def Instance.nurses_Parameter (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "night shifts", outcome := "breast cancer" }).Parameter
def Instance.nurses_Outcome (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "night shifts", outcome := "breast cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.nurses_Outcome i) :=
  (i.studies { design := .person_time_cohort, exposure := "night shifts", outcome := "breast cancer" }).space
def Instance.nurses (i : Instance) := (i.studies { design := .person_time_cohort, exposure := "night shifts", outcome := "breast cancer" }).model

def by_rates_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((∀ (p : unitInterval),
      1 - 2 * (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) ≤
      (ProbabilityTheory.binomial 800 p).real
        {count | p ∈ StatClaim.Modules.BinomialInterval.confidenceSet 800 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) count}) ∧
    (∀ (p : unitInterval)
      (member : p ∈ StatClaim.Modules.BinomialInterval.confidenceSet 800 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) 152),
      StatClaim.ratPoint 1633 10000 (by decide) (by decide) ≤ p ∧
      p ≤ StatClaim.ratPoint 219 1000 (by decide) (by decide))) ∧
  ((∀ (p : unitInterval),
      1 - 2 * (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) ≤
      (ProbabilityTheory.binomial 200 p).real
        {count | p ∈ StatClaim.Modules.BinomialInterval.confidenceSet 200 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) count}) ∧
    (∀ (p : unitInterval)
      (member : p ∈ StatClaim.Modules.BinomialInterval.confidenceSet 200 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) 30),
      StatClaim.ratPoint 207 2000 (by decide) (by decide) ≤ p ∧
      p ≤ StatClaim.ratPoint 259 1250 (by decide) (by decide))) ∧
  ((∀ (total : NNReal) (share : unitInterval),
      (StatClaim.Modules.Incidence.ratesLaw total share).real
        (StatClaim.Modules.Incidence.given (fun n => StatClaim.Modules.Incidence.rejectionAt share n (by_rates_level.value : ℝ))) ≤
      (by_rates_level.value : ℝ)) ∧
    (StatClaim.Modules.OneSampleBinomial.tailNumerator 109 25 87 48 = 12200444210616429138544017533138403621341339405392519081703896842113672737661435023982380653884107893304956918654027099345523546027044717028653256160507466787116937607070299431910598286776803433895111083984375 ∧
    StatClaim.Modules.BinomialInterval.lowerNumerator 109 25 87 48 = 25556285565252608419131244909862039805230253217217898579008876765089255946762186380526898356319890864162797842205601005320236523210865235019696161575171850099374936653556937825439110562427697890337066020767793152) ∧
    (((109, 48) ∈ StatClaim.Modules.Incidence.given (fun n => StatClaim.Modules.Incidence.rejectionAt (StatClaim.ratPoint 25 87 (by decide) (by decide)) n
      (by_rates_level.value : ℝ))) ↔ True)) ∧
  ((∀ (total : NNReal) (π : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.Modules.Incidence.ratesLaw total π).real
      (StatClaim.Modules.Incidence.given (fun n => {x | π ∈ StatClaim.Modules.BinomialInterval.confidenceSet n (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) x}))) ∧
    (∀ (π : unitInterval)
      (member : π ∈ StatClaim.Modules.BinomialInterval.confidenceSet 109 (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) 48) (below : (π : ℝ) < 1),
      StatClaim.Modules.Association.odds (((3453 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) * (((62 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds π * (((62 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) ∧
      StatClaim.Modules.Association.odds π * (((62 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds (((5387 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) * (((62 : ℕ) : ℝ) / ((25 : ℕ) : ℝ))))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i ∧ program.claimAt 3 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := trivial
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 3) := trivial

-- program: examples/tutorial/27_covariates_and_surveys.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.sampled_Parameter (i : Instance) : Type := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).Parameter
def Instance.sampled_Outcome (i : Instance) : Type := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.sampled_Outcome i) :=
  (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).space
def Instance.sampled (i : Instance) := (i.studies { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }).model
def Instance.adjusted_test (i : Instance) :=
  i.studyTest "adjusted" { design := .case_control, cases := some 150, controls := some 300, exposure := "smoking", outcome := "lung cancer" }
def Instance.adjusted_slack (i : Instance) : ℝ := i.slack "adjusted"
def Instance.clinic_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }).Parameter
def Instance.clinic_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.clinic_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }).space
def Instance.clinic (i : Instance) := (i.studies { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }).model
def Instance.slope_test (i : Instance) :=
  i.studyTest "slope" { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }
def Instance.slope_slack (i : Instance) : ℝ := i.slack "slope"
def Instance.rho_test (i : Instance) :=
  i.studyTest "rho" { design := .cross_sectional, n := some 250, exposure := "BMI", outcome := "systolic pressure", exposureScale := .continuous, outcomeScale := .continuous }
def Instance.rho_slack (i : Instance) : ℝ := i.slack "rho"
def Instance.national_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 12000, exposure := "smoking", outcome := "asthma", survey := .cluster, clusters := some 400 }).Parameter
def Instance.national_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 12000, exposure := "smoking", outcome := "asthma", survey := .cluster, clusters := some 400 }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.national_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 12000, exposure := "smoking", outcome := "asthma", survey := .cluster, clusters := some 400 }).space
def Instance.national (i : Instance) := (i.studies { design := .cross_sectional, n := some 12000, exposure := "smoking", outcome := "asthma", survey := .cluster, clusters := some 400 }).model
def Instance.weighted_test (i : Instance) :=
  i.studyTest "weighted" { design := .cross_sectional, n := some 12000, exposure := "smoking", outcome := "asthma", survey := .cluster, clusters := some 400 }
def Instance.weighted_slack (i : Instance) : ℝ := i.slack "weighted"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.sampled.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.sampled.noAssociation

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.clinic.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.clinic.noAssociation

noncomputable def design_2 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.national.toModel

noncomputable def design_2_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_2 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_2 (i : Instance) :=
  i.national.noAssociation

structure Premises (i : Instance) : Prop where
  cited_adjusted_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.logistic_association.scope i.sampled.law (null i)
    i.adjusted_test ((1 : ℚ) / 20) i.adjusted_slack
  cited_slope_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.linear_association.scope i.clinic.law (null_1 i)
    i.slope_test ((1 : ℚ) / 20) i.slope_slack
  cited_rho_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.pearson_correlation.scope i.clinic.law (null_1 i)
    i.rho_test ((1 : ℚ) / 20) i.rho_slack
  cited_weighted_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.survey_logistic.scope i.national.law (null_2 i)
    i.weighted_test ((1 : ℚ) / 20) i.weighted_slack

def Claims (i : Instance) : Prop :=
  (StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.adjusted_test ((↑((1 : ℚ) / 20) : ℝ) + i.adjusted_slack)) ∧
  (StatClaim.Interface.typeIClaim (design_1_compatible i) (null_1 i) i.slope_test (↑((1 : ℚ) / 20) : ℝ)) ∧
  (StatClaim.Interface.typeIClaim (design_1_compatible i) (null_1 i) i.rho_test (↑((1 : ℚ) / 20) : ℝ)) ∧
  (StatClaim.Interface.typeIClaim (design_2_compatible i) (null_2 i) i.weighted_test ((↑((1 : ℚ) / 20) : ℝ) + i.weighted_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i ∧ program.claimAt 3 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_adjusted_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_slope_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := ⟨h.cited_rho_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 3) := ⟨h.cited_weighted_level, trivial⟩

-- program: examples/tutorial/29_observational_power.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.studies { design := .case_control, cases := some 120, controls := some 240, exposure := "mobile phone use", outcome := "glioma" }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.studies { design := .case_control, cases := some 120, controls := some 240, exposure := "mobile phone use", outcome := "glioma" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.studies { design := .case_control, cases := some 120, controls := some 240, exposure := "mobile phone use", outcome := "glioma" }).space
def Instance.study (i : Instance) := (i.studies { design := .case_control, cases := some 120, controls := some 240, exposure := "mobile phone use", outcome := "glioma" }).model
def Instance.followed_Parameter (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 150, unexposed := some 300, exposure := "statin use", outcome := "dementia" }).Parameter
def Instance.followed_Outcome (i : Instance) : Type := (i.studies { design := .cohort, exposed := some 150, unexposed := some 300, exposure := "statin use", outcome := "dementia" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.followed_Outcome i) :=
  (i.studies { design := .cohort, exposed := some 150, unexposed := some 300, exposure := "statin use", outcome := "dementia" }).space
def Instance.followed (i : Instance) := (i.studies { design := .cohort, exposed := some 150, unexposed := some 300, exposure := "statin use", outcome := "dementia" }).model
def Instance.survey_Parameter (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 120, exposure := "night shifts", outcome := "insomnia" }).Parameter
def Instance.survey_Outcome (i : Instance) : Type := (i.studies { design := .cross_sectional, n := some 120, exposure := "night shifts", outcome := "insomnia" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.survey_Outcome i) :=
  (i.studies { design := .cross_sectional, n := some 120, exposure := "night shifts", outcome := "insomnia" }).space
def Instance.survey (i : Instance) := (i.studies { design := .cross_sectional, n := some 120, exposure := "night shifts", outcome := "insomnia" }).model

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def analysis_groups : StatClaim.FixedSampleDesign :=
  ⟨240, 120, by decide, by decide⟩

noncomputable def analysis_study := StatClaim.Modules.TwoArmBinomial.model analysis_groups

noncomputable def analysis_design :=
  StatClaim.Core.StudyDesign.fixed analysis_study

noncomputable def analysis_compatible :
    StatClaim.Core.Compatibility analysis_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis analysis_groups analysis_design analysis_level

def test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def test_groups : StatClaim.FixedSampleDesign :=
  ⟨300, 150, by decide, by decide⟩

noncomputable def test_study := StatClaim.Modules.TwoArmBinomial.model test_groups

noncomputable def test_design :=
  StatClaim.Core.StudyDesign.fixed test_study

noncomputable def test_compatible :
    StatClaim.Core.Compatibility test_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def test :=
  StatClaim.Modules.Fisher.analysis test_groups test_design test_level

def survey_test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

namespace checked_claim_plan

def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩

end checked_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (300 = 300 ∧ 150 = 150 ∧ 0 < 300 ∧
    0 < 150) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw 300 150 p).real
        (StatClaim.fisherRejectionRegionAt 300 150 checked_claim_plan.declaredLevel.value) ≤
      (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))) ∧
    ((((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) ≤
      (StatClaim.productBinomial 300 150 (StatClaim.ratPoint 1 10 (by decide) (by decide)) (StatClaim.ratPoint 1 5 (by decide) (by decide))).real
        (StatClaim.fisherRejectionRegionAt 300 150 checked_claim_plan.declaredLevel.value))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/tutorial/30_pairs_and_rates_power.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.paired_Parameter (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 150, exposure := "benzodiazepine use", outcome := "hip fracture" }).Parameter
def Instance.paired_Outcome (i : Instance) : Type := (i.studies { design := .matched_case_control, pairs := some 150, exposure := "benzodiazepine use", outcome := "hip fracture" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.paired_Outcome i) :=
  (i.studies { design := .matched_case_control, pairs := some 150, exposure := "benzodiazepine use", outcome := "hip fracture" }).space
def Instance.paired (i : Instance) := (i.studies { design := .matched_case_control, pairs := some 150, exposure := "benzodiazepine use", outcome := "hip fracture" }).model
def Instance.workers_Parameter (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).Parameter
def Instance.workers_Outcome (i : Instance) : Type := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.workers_Outcome i) :=
  (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).space
def Instance.workers (i : Instance) := (i.studies { design := .person_time_cohort, exposure := "solvent exposure", outcome := "kidney cancer" }).model

def pairs_test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

def rates_test_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

namespace events_needed_claim_plan

def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 40, by norm_num, by norm_num⟩

end events_needed_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (∀ (total : NNReal) (share : unitInterval),
      (StatClaim.Modules.Incidence.ratesLaw total share).real
        (StatClaim.Modules.Incidence.given (fun n => StatClaim.Modules.Incidence.rejectionAt share n (events_needed_claim_plan.declaredLevel.value : ℝ))) ≤
      (((1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ))) ∧
    ((((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) ≤ (ProbabilityTheory.binomial 94 (StatClaim.ratPoint 2 5 (by decide) (by decide))).real
        (StatClaim.Modules.Incidence.rejectionAt (StatClaim.ratPoint 1 4 (by decide) (by decide)) 94 (events_needed_claim_plan.declaredLevel.value : ℝ))) ∧
    (∀ (m : ℕ) (lower : 20 ≤ m) (upper : m < 94),
      (ProbabilityTheory.binomial m (StatClaim.ratPoint 2 5 (by decide) (by decide))).real
        (StatClaim.Modules.Incidence.rejectionAt (StatClaim.ratPoint 1 4 (by decide) (by decide)) m (events_needed_claim_plan.declaredLevel.value : ℝ)) <
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/two_outcomes.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨200, 100, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def primary_outcome_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def primary_outcome :=
  StatClaim.Modules.Fisher.analysis study_sizes plan primary_outcome_level

def secondary_outcome_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def secondary_outcome :=
  StatClaim.Modules.Fisher.analysis study_sizes plan secondary_outcome_level

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ study.law →
      v₁.Marginal σ study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => primary_outcome.hypothesis (v₀.parameter θ),
        fun θ => secondary_outcome.hypothesis (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' primary_outcome.procedure.rejectionEvent,
        v₁.outcome ⁻¹' secondary_outcome.procedure.rejectionEvent]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, 0] k)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/two_stage.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The participants in the first and the second stage. -/
def stages : ℕ × ℕ := (13, 30)

def analysis_design : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign stages.1 stages.2 3 12

noncomputable def analysis :=
  StatClaim.Modules.TwoStageBinomial.analysisAtMost analysis_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

namespace verification_claim_plan

def declaredDesign : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign 13 30 3 12
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 5 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.TwoStageBinomial.analysisAtMost declaredDesign nullRate

end verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (verification_claim_plan.declaredDesign.nFirst = 13 ∧ verification_claim_plan.declaredDesign.nSecond = 30) ∧
    ((verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((verification_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 2 5 (by decide) (by decide))
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/two_stage_posterior.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The participants in the first and the second stage. -/
def stages : ℕ × ℕ := (10, 20)

def analysis_design : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.posteriorDesign stages.1 stages.2 1 1 1 5 1 2 19 20

noncomputable def analysis :=
  StatClaim.Modules.TwoStageBinomial.analysisAtMost analysis_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

namespace verification_claim_plan

def declaredDesign : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.posteriorDesign 10 20 1 1 1 5 1 2 19 20
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 5 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.TwoStageBinomial.analysisAtMost declaredDesign nullRate

end verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (verification_claim_plan.declaredDesign.nFirst = 10 ∧ verification_claim_plan.declaredDesign.nSecond = 20) ∧
    ((verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement) ∧
    ((verification_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 2 5 (by decide) (by decide))
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/two_stage_result.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

/-- The participants in the first and the second stage. -/
def stages : ℕ × ℕ := (13, 30)

def analysis_design : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign stages.1 stages.2 3 12

noncomputable def analysis :=
  StatClaim.Modules.TwoStageBinomial.analysisAtMost analysis_design (StatClaim.ratPoint 1 5 (by decide) (by decide))

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  ((StatClaim.Modules.TwoStageBinomial.thresholdDesign 13 30 3 12).continues 5 = true) ∧
    ((StatClaim.Modules.TwoStageBinomial.thresholdDesign 13 30 3 12).rejects 5 9 = true) ∧
    (((StatClaim.Modules.TwoStageBinomial.analysisAtMost (StatClaim.Modules.TwoStageBinomial.thresholdDesign 13 30 3 12) (StatClaim.ratPoint 1 5 (by decide) (by decide))).typeIClaim
      (((31 : ℕ) : ℝ) / ((625 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/two_stage_search.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

namespace verification_claim_plan

def declaredDesign : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign 13 30 3 12
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 5 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.TwoStageBinomial.analysisAtMost declaredDesign nullRate

end verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (verification_claim_plan.declaredDesign.nFirst = 13 ∧ verification_claim_plan.declaredDesign.nSecond = 30) ∧
    ((verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((verification_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 2 5 (by decide) (by decide))
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: examples/unequal_allocation.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨20, 40, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

namespace verification_claim_plan

def declaredSizes : StatClaim.FixedSampleDesign := ⟨26, 52, by decide, by decide⟩
def declaredLevel : StatClaim.SignificanceLevel :=
  ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := StatClaim.Modules.FisherPower.analysis declaredSizes declaredLevel
noncomputable def planningPoint : StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.FisherPower.ratePoint 1 10 2 5 (by decide) (by decide) (by decide) (by decide)

end verification_claim_plan

structure Premises (i : Instance) : Prop where

def Claims (i : Instance) : Prop :=
  (verification_claim_plan.declaredSizes.nControl = 26 ∧ verification_claim_plan.declaredSizes.nTreatment = 52 ∧
    0 < verification_claim_plan.declaredSizes.nControl ∧ 0 < verification_claim_plan.declaredSizes.nTreatment) ∧
    ((verification_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))).statement) ∧
    ((verification_claim_plan.declaredAnalysis.powerClaim (fun parameter => parameter = verification_claim_plan.planningPoint)
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))).statement) ∧
    (∀ (n : ℕ) (positive : 0 < n) (lower : 10 ≤ n) (upper : n < 26),
      ((StatClaim.Core.Policy.fixed (StatClaim.Modules.TwoArmBinomial.model
        ⟨n, 2 * n, positive, Nat.mul_pos (by decide) positive⟩)).law verification_claim_plan.planningPoint).real
        (StatClaim.Modules.FisherPower.analysis ⟨n, 2 * n, positive, Nat.mul_pos (by decide) positive⟩
          verification_claim_plan.declaredLevel).rejection <
      (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := trivial

-- program: replication/comparison/graph.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).space
def Instance.study (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).model
def Instance.first_test (i : Instance) :=
  i.test "first" { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.first_slack (i : Instance) : ℝ := i.slack "first"
def Instance.second_test (i : Instance) :=
  i.test "second" { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.second_slack (i : Instance) : ℝ := i.slack "second"
def Instance.third_test (i : Instance) :=
  i.test "third" { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }
def Instance.third_slack (i : Instance) : ℝ := i.slack "third"
def Instance.graph_procedure (i : Instance) (Θ Ω : Type) [MeasurableSpace Ω]
    (σ : StatClaim.Interface.JointStudy Θ Ω) (v0 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome) (v1 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome) (v2 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }).Outcome) :
    Fin 3 → Set Ω :=
  i.graph "procedure" [(StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨300, 300, by decide, by decide⟩ })] 3 Θ Ω σ (v0, v1, v2, PUnit.unit)
def Instance.graph_slack (i : Instance) : ℝ := i.slack "procedure"

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-5 : ℚ)

def null_1 (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_first_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test_one_sided.scope i.study.law (null i)
    i.first_test ((1 : ℚ) / 40) i.first_slack
  cited_second_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test_one_sided.scope i.study.law (null i)
    i.second_test ((1 : ℚ) / 40) i.second_slack
  cited_third_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test_one_sided.scope i.study.law (null_1 i)
    i.third_test ((1 : ℚ) / 40) i.third_slack
  cited_graph_rule : StatClaim.Interface.Scope.finiteSample.permits i.graph_slack ∧
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome),
      v₀.Marginal σ i.study.law →
      v₁.Marginal σ i.study.law →
      v₂.Marginal σ i.study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)

def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome),
      v₀.Marginal σ i.study.law →
      v₁.Marginal σ i.study.law →
      v₂.Marginal σ i.study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_first_level, h.cited_second_level, h.cited_third_level, h.cited_graph_rule, trivial⟩

-- program: replication/comparison/sequential.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.halfway_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).Parameter
def Instance.halfway_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.halfway_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).space
def Instance.halfway (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).model
def Instance.complete_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).Parameter
def Instance.complete_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.complete_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).space
def Instance.complete (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }).model
def Instance.interim_test (i : Instance) :=
  i.test "interim" { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }
def Instance.interim_slack (i : Instance) : ℝ := i.slack "interim"
def Instance.final_test (i : Instance) :=
  i.test "final" { outcome := .continuous, sizes := ⟨200, 200, by decide, by decide⟩ }
def Instance.final_slack (i : Instance) : ℝ := i.slack "final"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.halfway.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.halfway.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.complete.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.complete.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_interim_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test_one_sided.scope i.halfway.law (null i)
    i.interim_test ((3 : ℚ) / 2000) i.interim_slack
  cited_final_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test_one_sided.scope i.complete.law (null_1 i)
    i.final_test ((47 : ℚ) / 2000) i.final_slack

def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.halfway_Parameter i.halfway_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.complete_Parameter i.complete_Outcome),
      v₀.Marginal σ i.halfway.law →
      v₁.Marginal σ i.complete.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.interim_test.reject,
        v₁.outcome ⁻¹' i.final_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.interim_slack, i.final_slack] k)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_interim_level, h.cited_final_level, trivial⟩

-- program: replication/comparison/two_arm_power.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.study_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).Parameter
def Instance.study_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.study_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).space
def Instance.study (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }).model
def Instance.analysis_test (i : Instance) :=
  i.test "analysis" { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }
def Instance.analysis_slack (i : Instance) : ℝ := i.slack "analysis"

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

structure Premises (i : Instance) : Prop where
  cited_analysis_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test.scope i.study.law (null i)
    i.analysis_test ((1 : ℚ) / 20) i.analysis_slack

def Claims (i : Instance) : Prop :=
  StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.analysis_test ((↑((1 : ℚ) / 20) : ℝ) + i.analysis_slack)

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_analysis_level, trivial⟩

-- program: replication/copd/design_cited.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.per_protocol_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter
def Instance.per_protocol_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.per_protocol_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).space
def Instance.per_protocol (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).model
def Instance.full_set_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter
def Instance.full_set_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.full_set_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).space
def Instance.full_set (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).model
def Instance.trough_fev1_ni_test (i : Instance) :=
  i.test "trough_fev1_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.trough_fev1_ni_slack (i : Instance) : ℝ := i.slack "trough_fev1_ni"
def Instance.peak_fev1_ni_test (i : Instance) :=
  i.test "peak_fev1_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.peak_fev1_ni_slack (i : Instance) : ℝ := i.slack "peak_fev1_ni"
def Instance.peak_fev1_sup_test (i : Instance) :=
  i.test "peak_fev1_sup" { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }
def Instance.peak_fev1_sup_slack (i : Instance) : ℝ := i.slack "peak_fev1_sup"
def Instance.graph_procedure (i : Instance) (Θ Ω : Type) [MeasurableSpace Ω]
    (σ : StatClaim.Interface.JointStudy Θ Ω) (v0 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome) (v1 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome) (v2 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome) :
    Fin 3 → Set Ω :=
  i.graph "co_primary" [(StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ })] 3 Θ Ω σ (v0, v1, v2, PUnit.unit)
def Instance.graph_slack (i : Instance) : ℝ := i.slack "co_primary"
def Instance.inspiratory_capacity_ni_test (i : Instance) :=
  i.test "inspiratory_capacity_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.inspiratory_capacity_ni_slack (i : Instance) : ℝ := i.slack "inspiratory_capacity_ni"
def Instance.onset_of_action_sup_test (i : Instance) :=
  i.test "onset_of_action_sup" { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }
def Instance.onset_of_action_sup_slack (i : Instance) : ℝ := i.slack "onset_of_action_sup"
def Instance.tdi_ni_test (i : Instance) :=
  i.test "tdi_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.tdi_ni_slack (i : Instance) : ℝ := i.slack "tdi_ni"
def Instance.emsci_ni_test (i : Instance) :=
  i.test "emsci_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.emsci_ni_slack (i : Instance) : ℝ := i.slack "emsci_ni"

def full_set_binary_sizes : StatClaim.FixedSampleDesign :=
  ⟨500, 500, by decide, by decide⟩

noncomputable def full_set_binary := StatClaim.Modules.TwoArmBinomial.model full_set_binary_sizes

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.per_protocol.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-50 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.full_set.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.full_set.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

noncomputable def design_2 :=
  StatClaim.Core.StudyDesign.fixed full_set_binary

noncomputable def design_2_compatible :
    StatClaim.Core.Compatibility design_2 :=
  StatClaim.Core.Compatibility.fixed _

def null_2 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

def null_3 (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-1 : ℚ)

def null_4 (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape ((-1 : ℚ) / 10)

structure Premises (i : Instance) : Prop where
  cited_trough_fev1_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null i)
    i.trough_fev1_ni_test ((1 : ℚ) / 40) i.trough_fev1_ni_slack
  cited_peak_fev1_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null i)
    i.peak_fev1_ni_test ((1 : ℚ) / 40) i.peak_fev1_ni_slack
  cited_peak_fev1_sup_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.full_set.law (null_1 i)
    i.peak_fev1_sup_test ((1 : ℚ) / 40) i.peak_fev1_sup_slack
  cited_graph_rule : StatClaim.Interface.Scope.largeSample.permits i.graph_slack ∧
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)
  cited_inspiratory_capacity_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null i)
    i.inspiratory_capacity_ni_test ((1 : ℚ) / 40) i.inspiratory_capacity_ni_slack
  cited_onset_of_action_sup_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.logistic_regression_one_sided.scope full_set_binary.law null_2
    i.onset_of_action_sup_test ((1 : ℚ) / 40) i.onset_of_action_sup_slack
  cited_tdi_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null_3 i)
    i.tdi_ni_test ((1 : ℚ) / 40) i.tdi_ni_slack
  cited_emsci_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null_4 i)
    i.emsci_ni_test ((1 : ℚ) / 40) i.emsci_ni_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)) ∧
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₄ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₅ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₆ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      v₃.Marginal σ i.per_protocol.law →
      v₄.Marginal σ full_set_binary.law →
      v₅.Marginal σ i.per_protocol.law →
      v₆.Marginal σ i.per_protocol.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => null_2 (v₄.parameter θ),
        fun θ => (null_3 i) (v₅.parameter θ),
        fun θ => (null_4 i) (v₆.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.inspiratory_capacity_ni_test.reject,
        v₄.outcome ⁻¹' i.onset_of_action_sup_test.reject,
        v₅.outcome ⁻¹' i.tdi_ni_test.reject,
        v₆.outcome ⁻¹' i.emsci_ni_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.inspiratory_capacity_ni_slack, i.onset_of_action_sup_slack, i.tdi_ni_slack, i.emsci_ni_slack] k)) ∧
  (StatClaim.Interface.typeIClaim design_2_compatible null_2 i.onset_of_action_sup_test ((↑((1 : ℚ) / 40) : ℝ) + i.onset_of_action_sup_slack))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.cited_trough_fev1_ni_level, h.cited_peak_fev1_ni_level, h.cited_peak_fev1_sup_level, h.cited_graph_rule, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.cited_trough_fev1_ni_level, h.cited_peak_fev1_ni_level, h.cited_peak_fev1_sup_level, h.cited_graph_rule, h.cited_inspiratory_capacity_ni_level, h.cited_onset_of_action_sup_level, h.cited_tdi_ni_level, h.cited_emsci_ni_level, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 2) := ⟨h.cited_onset_of_action_sup_level, trivial⟩

-- program: replication/copd/design_declared.stat
namespace Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.per_protocol_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter
def Instance.per_protocol_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.per_protocol_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).space
def Instance.per_protocol (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).model
def Instance.full_set_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter
def Instance.full_set_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace (Instance.full_set_Outcome i) :=
  (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).space
def Instance.full_set (i : Instance) := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).model
def Instance.trough_fev1_ni_test (i : Instance) :=
  i.test "trough_fev1_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.trough_fev1_ni_slack (i : Instance) : ℝ := i.slack "trough_fev1_ni"
def Instance.peak_fev1_ni_test (i : Instance) :=
  i.test "peak_fev1_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.peak_fev1_ni_slack (i : Instance) : ℝ := i.slack "peak_fev1_ni"
def Instance.peak_fev1_sup_test (i : Instance) :=
  i.test "peak_fev1_sup" { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }
def Instance.peak_fev1_sup_slack (i : Instance) : ℝ := i.slack "peak_fev1_sup"
def Instance.graph_procedure (i : Instance) (Θ Ω : Type) [MeasurableSpace Ω]
    (σ : StatClaim.Interface.JointStudy Θ Ω) (v0 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome) (v1 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome) (v2 : StatClaim.Interface.MemberView Θ Ω (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome) :
    Fin 3 → Set Ω :=
  i.graph "co_primary" [(StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }), (StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ })] 3 Θ Ω σ (v0, v1, v2, PUnit.unit)
def Instance.graph_slack (i : Instance) : ℝ := i.slack "co_primary"
def Instance.inspiratory_capacity_ni_test (i : Instance) :=
  i.test "inspiratory_capacity_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.inspiratory_capacity_ni_slack (i : Instance) : ℝ := i.slack "inspiratory_capacity_ni"
def Instance.onset_of_action_sup_test (i : Instance) :=
  i.test "onset_of_action_sup" { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }
def Instance.onset_of_action_sup_slack (i : Instance) : ℝ := i.slack "onset_of_action_sup"
def Instance.tdi_ni_test (i : Instance) :=
  i.test "tdi_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.tdi_ni_slack (i : Instance) : ℝ := i.slack "tdi_ni"
def Instance.emsci_ni_test (i : Instance) :=
  i.test "emsci_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.emsci_ni_slack (i : Instance) : ℝ := i.slack "emsci_ni"

def full_set_binary_sizes : StatClaim.FixedSampleDesign :=
  ⟨500, 500, by decide, by decide⟩

noncomputable def full_set_binary := StatClaim.Modules.TwoArmBinomial.model full_set_binary_sizes

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.per_protocol.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-50 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.full_set.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.full_set.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

noncomputable def design_2 :=
  StatClaim.Core.StudyDesign.fixed full_set_binary

noncomputable def design_2_compatible :
    StatClaim.Core.Compatibility design_2 :=
  StatClaim.Core.Compatibility.fixed _

def null_2 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

def null_3 (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-1 : ℚ)

def null_4 (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape ((-1 : ℚ) / 10)

structure Premises (i : Instance) : Prop where
  declared_trough_fev1_ni_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.per_protocol.law (null i)
    i.trough_fev1_ni_test ((1 : ℚ) / 40) i.trough_fev1_ni_slack
  declared_peak_fev1_ni_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.per_protocol.law (null i)
    i.peak_fev1_ni_test ((1 : ℚ) / 40) i.peak_fev1_ni_slack
  declared_peak_fev1_sup_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.full_set.law (null_1 i)
    i.peak_fev1_sup_test ((1 : ℚ) / 40) i.peak_fev1_sup_slack
  cited_graph_rule : StatClaim.Interface.Scope.largeSample.permits i.graph_slack ∧
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)
  declared_inspiratory_capacity_ni_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.per_protocol.law (null i)
    i.inspiratory_capacity_ni_test ((1 : ℚ) / 40) i.inspiratory_capacity_ni_slack
  declared_onset_of_action_sup_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample full_set_binary.law null_2
    i.onset_of_action_sup_test ((1 : ℚ) / 40) i.onset_of_action_sup_slack
  declared_tdi_ni_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.per_protocol.law (null_3 i)
    i.tdi_ni_test ((1 : ℚ) / 40) i.tdi_ni_slack
  declared_emsci_ni_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.per_protocol.law (null_4 i)
    i.emsci_ni_test ((1 : ℚ) / 40) i.emsci_ni_slack

def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)) ∧
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₄ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₅ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₆ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      v₃.Marginal σ i.per_protocol.law →
      v₄.Marginal σ full_set_binary.law →
      v₅.Marginal σ i.per_protocol.law →
      v₆.Marginal σ i.per_protocol.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => null_2 (v₄.parameter θ),
        fun θ => (null_3 i) (v₅.parameter θ),
        fun θ => (null_4 i) (v₆.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.inspiratory_capacity_ni_test.reject,
        v₄.outcome ⁻¹' i.onset_of_action_sup_test.reject,
        v₅.outcome ⁻¹' i.tdi_ni_test.reject,
        v₆.outcome ⁻¹' i.emsci_ni_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.inspiratory_capacity_ni_slack, i.onset_of_action_sup_slack, i.tdi_ni_slack, i.emsci_ni_slack] k))

end Old

example (i : StatClaim.Semantics.Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := by
  first
  | exact Iff.rfl
  | unfold Old.Claims
    repeat' apply and_congr
    all_goals first
      | rfl
      | simp only [StatClaim.Semantics.ProbabilityFraction.real,
          StatClaim.Semantics.Endpoints.odds, StatClaim.Semantics.EventCounts.scaleReal,
          StatClaim.Semantics.EventCounts.total, StatClaim.Semantics.EventCounts.scale]
        norm_num
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 0) := ⟨h.declared_trough_fev1_ni_level, h.declared_peak_fev1_ni_level, h.declared_peak_fev1_sup_level, h.cited_graph_rule, trivial⟩
example (i : StatClaim.Semantics.Instance) (h : Old.Premises i) :
    StatClaim.Semantics.Premise.AllHold i (program.premisesAt 1) := ⟨h.declared_trough_fev1_ni_level, h.declared_peak_fev1_ni_level, h.declared_peak_fev1_sup_level, h.cited_graph_rule, h.declared_inspiratory_capacity_ni_level, h.declared_onset_of_action_sup_level, h.declared_tdi_ni_level, h.declared_emsci_ni_level, trivial⟩
