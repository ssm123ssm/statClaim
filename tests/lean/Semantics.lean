import StatClaim

/-!
The semantics of `StatClaim.Semantics` on two programs, as data written by
`lean_translation/data.py`: `examples/mixed_endpoints.stat` and
`replication/copd/design_cited.stat`. Their claims are proved by the soundness theorem
alone. Changed copies of the first show what the contracts and the meaning refuse.
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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

theorem contracts : program.Contracts := by decide +kernel

theorem claim_0 : program.Claim 0 :=
  StatClaim.Semantics.Program.sound program contracts 0 (by decide +kernel)
theorem claim_1 : program.Claim 1 :=
  StatClaim.Semantics.Program.sound program contracts 1 (by decide +kernel)

example : [program.grade 0, program.grade 1] = [.conditional, .proved] := by decide +kernel

/-- The premises can hold together: proved once, for every program. -/
example : Premise.AllHold Instance.trivial (program.premisesAt 0) := Program.satisfiable _ _

/-- The family's level below its members' sum. -/
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
    ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩),
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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

example : ¬ overallocated.Contracts := by decide +kernel

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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
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
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩]

example (i : Instance) : ¬ adaptive.claimAt 1 i := id
example : adaptive.fixedAt 1 = false := by decide +kernel

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
