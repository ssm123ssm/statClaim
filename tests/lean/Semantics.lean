import StatClaim

/-!
The semantics of `StatClaim.Semantics` on two programs, as data written by
`lean_translation/data.py`: `examples/mixed_endpoints.stat` and
`replication/copd/design_cited.stat`, the observational study of
`examples/complex_survey.stat` and the design with looks of `examples/interim_look.stat`. Their claims are proved by the soundness theorem alone. Changed copies of the first show what the contracts and the meaning refuse.
`scripts/check_lean_semantics.py` checks every program the semantics covers against
today's translation.
-/

open StatClaim.Semantics

namespace MixedEndpoints

def program : StatClaim.Semantics.Program where
  requests := [
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]
  declarations := [
  .fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none]

theorem contracts : program.Contracts := by decide +kernel

theorem claim_0 : program.Claim 0 :=
  StatClaim.Semantics.Program.sound program contracts 0 (by decide +kernel)
theorem claim_1 : program.Claim 1 :=
  StatClaim.Semantics.Program.sound program contracts 1 (by decide +kernel)

example : [program.grade 0, program.grade 1] = [.conditional, .proved] := by decide +kernel

/-- The premises can hold together: proved once, for every program. -/
example : Premise.AllHold Instance.trivial (program.premisesAt 0) := Program.satisfiable _ _

/-- The family's level below its members' sum: its declarations meet their contracts, but
the claim is not ready, as Python leaves it open, so soundness does not apply to it. -/
def overallocated : StatClaim.Semantics.Program where
  requests := [
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩ none),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]
  declarations := [
  .fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none]

example : overallocated.Contracts := by decide +kernel
example : overallocated.readyAt 0 = false := by decide +kernel

/-- A null the t-test does not support. -/
def unsupported : StatClaim.Semantics.Program where
  requests := [
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_least, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]
  declarations := [
  .fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none]

example : ¬ unsupported.Contracts := by decide +kernel

/-- Fewer participants than the t-test needs. -/
def tooFew : StatClaim.Semantics.Program where
  requests := [
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨1, 1, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨1, 1, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]
  declarations := [
  .fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none]

example : ¬ tooFew.Contracts := by decide +kernel

/-- A null about another model than the design's. -/
def otherModel : StatClaim.Semantics.Program where
  requests := [
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨121, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]
  declarations := [
  .fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none]

example : ¬ otherModel.Contracts := by decide +kernel

/-- A Type I claim about a combination. -/
def typeIOfFamily : StatClaim.Semantics.Program where
  requests := [
  .typeI (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]
  declarations := [
  .fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none]

example : ¬ typeIOfFamily.Contracts := by decide +kernel

/-- A design that stops by a rule depending on the data supplies no law: its claim is
`False`, and soundness does not apply to it. -/
def adaptive : StatClaim.Semantics.Program where
  requests := [
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .data_dependent }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]
  declarations := [
  .fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "symptoms" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ none]

example (i : Instance) : ¬ adaptive.claimAt 1 i := id
example : adaptive.readyAt 1 = false := by decide +kernel

end MixedEndpoints

namespace Copd

def program : StatClaim.Semantics.Program where
  requests := [
  .familywise (.graphical "co_primary"
    [.assumed "trough_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "peak_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "peak_fev1_sup" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    [((1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)] [[(0 : ℚ), (1 : ℚ), (0 : ℚ)], [(0 : ℚ), (0 : ℚ), (1 : ℚ)], [(1 : ℚ), (0 : ℚ), (0 : ℚ)]] ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩),
  .familywise (.sequence "trial"
    [.graphical "co_primary"
    [.assumed "trough_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "peak_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "peak_fev1_sup" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    [((1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)] [[(0 : ℚ), (1 : ℚ), (0 : ℚ)], [(0 : ℚ), (0 : ℚ), (1 : ℚ)], [(1 : ℚ), (0 : ℚ), (0 : ℚ)]] ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "inspiratory_capacity_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "onset_of_action_sup" (.cited StatClaim.Generated.Methods.logistic_regression_one_sided)
      { model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .proportion_difference_at_most, model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "tdi_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-1 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "emsci_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some ((-1 : ℚ) / 10) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩),
  .typeI (.assumed "onset_of_action_sup" (.cited StatClaim.Generated.Methods.logistic_regression_one_sided)
      { model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .proportion_difference_at_most, model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]
  declarations := [
  .assumed "trough_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "peak_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "peak_fev1_sup" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .graphical "co_primary"
    [.assumed "trough_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "peak_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "peak_fev1_sup" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    [((1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)] [[(0 : ℚ), (1 : ℚ), (0 : ℚ)], [(0 : ℚ), (0 : ℚ), (1 : ℚ)], [(1 : ℚ), (0 : ℚ), (0 : ℚ)]] ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "inspiratory_capacity_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "onset_of_action_sup" (.cited StatClaim.Generated.Methods.logistic_regression_one_sided)
      { model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .proportion_difference_at_most, model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "tdi_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-1 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .assumed "emsci_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some ((-1 : ℚ) / 10) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
  .sequence "trial"
    [.graphical "co_primary"
    [.assumed "trough_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "peak_fev1_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "peak_fev1_sup" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    [((1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)] [[(0 : ℚ), (1 : ℚ), (0 : ℚ)], [(0 : ℚ), (0 : ℚ), (1 : ℚ)], [(1 : ℚ), (0 : ℚ), (0 : ℚ)]] ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "inspiratory_capacity_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "onset_of_action_sup" (.cited StatClaim.Generated.Methods.logistic_regression_one_sided)
      { model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .proportion_difference_at_most, model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "tdi_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-1 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .assumed "emsci_ni" (.cited StatClaim.Generated.Methods.mmrm_test_one_sided)
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some ((-1 : ℚ) / 10) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]

theorem contracts : program.Contracts := by decide +kernel

theorem claim_0 : program.Claim 0 :=
  StatClaim.Semantics.Program.sound program contracts 0 (by decide +kernel)
theorem claim_1 : program.Claim 1 :=
  StatClaim.Semantics.Program.sound program contracts 1 (by decide +kernel)
theorem claim_2 : program.Claim 2 :=
  StatClaim.Semantics.Program.sound program contracts 2 (by decide +kernel)

example : [program.grade 0, program.grade 1, program.grade 2] = [.cited, .conditional, .cited] := by
  decide +kernel

end Copd

namespace Survey

def program : StatClaim.Semantics.Program where
  requests := [
  .typeI (.associated "weighted" StatClaim.Generated.Methods.survey_linear
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }, stopping := .fixed }
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted } }
      ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ ["age", "sex", "income"])]
  declarations := [
  .associated "weighted" StatClaim.Generated.Methods.survey_linear
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }, stopping := .fixed }
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted } }
      ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ ["age", "sex", "income"]]

theorem contracts : program.Contracts := by decide +kernel

theorem claim_0 : program.Claim 0 :=
  StatClaim.Semantics.Program.sound program contracts 0 (by decide +kernel)

example : [program.grade 0] = [.cited] := by decide +kernel

/-- A test of a continuous outcome applied to a binary one. -/
def binaryOutcome : StatClaim.Semantics.Program where
  requests := [
  .typeI (.associated "weighted" StatClaim.Generated.Methods.survey_linear
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", survey := .weighted }, stopping := .fixed }
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", survey := .weighted } }
      ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ ["age", "sex", "income"])]
  declarations := [
  .associated "weighted" StatClaim.Generated.Methods.survey_linear
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }, stopping := .fixed }
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted } }
      ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ ["age", "sex", "income"]]

example : ¬ binaryOutcome.Contracts := by decide +kernel

/-- A cluster survey with fewer clusters than the method needs. -/
def fewClusters : StatClaim.Semantics.Program where
  requests := [
  .typeI (.associated "weighted" StatClaim.Generated.Methods.survey_linear
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .cluster, clusters := some 12 }, stopping := .fixed }
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .cluster, clusters := some 12 } }
      ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ ["age", "sex", "income"])]
  declarations := [
  .associated "weighted" StatClaim.Generated.Methods.survey_linear
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }, stopping := .fixed }
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted } }
      ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ ["age", "sex", "income"]]

example : ¬ fewClusters.Contracts := by decide +kernel

/-- Covariates for a method that takes none. -/
def unadjustable : StatClaim.Semantics.Program where
  requests := [
  .typeI (.associated "weighted" StatClaim.Generated.Methods.pearson_correlation
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }, stopping := .fixed }
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted } }
      ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ ["age", "sex", "income"])]
  declarations := [
  .associated "weighted" StatClaim.Generated.Methods.survey_linear
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted }, stopping := .fixed }
      { model := { design := .cross_sectional, n := some 8000, exposure := "sugary drinks", outcome := "waist circumference", outcomeScale := .continuous, survey := .weighted } }
      ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩ ["age", "sex", "income"]]

example : ¬ unadjustable.Contracts := by decide +kernel

end Survey

namespace Looks

def program : StatClaim.Semantics.Program where
  requests := [
  .typeI (.looks "trial"
    [.assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
    .assumed "final" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩)]
  declarations := [
  .assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
  .assumed "final" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩,
  .looks "trial"
    [.assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
    .assumed "final" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

theorem contracts : program.Contracts := by decide +kernel

theorem claim_0 : program.Claim 0 :=
  StatClaim.Semantics.Program.sound program contracts 0 (by decide +kernel)

example : [program.grade 0] = [.conditional] := by decide +kernel

/-- A second look that asks another question: a different test. -/
def otherTest : StatClaim.Semantics.Program where
  requests := [
  .typeI (.looks "trial"
    [.assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
    .assumed "final" (.cited StatClaim.Generated.Methods.welch_test)
      { model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩)]
  declarations := [
  .assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
  .assumed "final" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩,
  .looks "trial"
    [.assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
    .assumed "final" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

example : ¬ otherTest.Contracts := by decide +kernel

/-- A second look taken at fewer participants than the first. -/
def shrinking : StatClaim.Semantics.Program where
  requests := [
  .typeI (.looks "trial"
    [.assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
    .assumed "final" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨40, 40, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨40, 40, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩)]
  declarations := [
  .assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
  .assumed "final" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩,
  .looks "trial"
    [.assumed "interim" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨50, 50, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 200), by norm_num, by norm_num⟩,
    .assumed "final" (.cited StatClaim.Generated.Methods.t_test)
      { model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨100, 100, by decide, by decide⟩ } }
      ⟨((9 : ℚ) / 200), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

example : ¬ shrinking.Contracts := by decide +kernel

end Looks
