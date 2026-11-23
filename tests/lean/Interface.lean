import StatClaim

/-!
The translation interface read in known cases: scopes, null shapes, the
generated method entries, and level premises that hold and that fail.
-/

open MeasureTheory StatClaim.Interface StatClaim.Generated

-- A finite-sample guarantee permits no slack; a large-sample one any nonnegative slack.
example : Scope.finiteSample.permits 0 := Scope.permits_zero _
example : ¬ Scope.finiteSample.permits 1 := by norm_num [Scope.permits]
example : Scope.largeSample.permits (1 / 10) := by norm_num [Scope.permits]
example : ¬ Scope.largeSample.permits (-1) := by norm_num [Scope.permits]

-- Null shapes read as their names say.
example : NullShape.holds .atMost 0 (-1) := by norm_num [NullShape.holds]
example : ¬ NullShape.holds .atLeast 0 (-1) := by norm_num [NullShape.holds]
example : NullShape.holds .equal (1 / 2) (1 / 2) := by norm_num [NullShape.holds]

-- Generated null forms agree with their names and outcomes.
example : NullKey.mean_difference_at_most.shape = .atMost := rfl
example : NullKey.mean_difference_at_least.shape = .atLeast := rfl
example : NullKey.equal_means.shape = .equal ∧ NullKey.equal_means.outcome = .continuous :=
  ⟨rfl, rfl⟩
example : NullKey.proportion_difference.takesValue = true := rfl

-- Generated entries record the registry's scopes, nulls and units.
example : Methods.t_test.scope = .finiteSample := rfl
example : Methods.welch_test.scope = .largeSample := rfl
example : Methods.log_rank.nulls = [.equal_survival] := rfl
example : Methods.cluster_t_test.unit = .cluster ∧ Methods.cluster_t_test.minPerArm = 4 :=
  ⟨rfl, rfl⟩
example : Methods.rao_scott_test.minClusters = some 20 := rfl
example : trialMethods.length = 11 ∧ associationMethods.length = 10 := ⟨rfl, rfl⟩

-- A test that never rejects meets a level premise, so premises can be satisfied.
example : LevelPremise .largeSample (fun _ : Unit => Measure.dirac ()) (fun _ => True)
    (TestInterface.neverRejects Unit) (1 / 20) 0 :=
  neverRejects_meets_level _ _ _ _ (by norm_num)

-- A finite-sample premise allows no slack, whatever the test does.
example : ¬ LevelPremise .finiteSample (fun _ : Unit => Measure.dirac ()) (fun _ => True)
    (TestInterface.neverRejects Unit) (1 / 20) (1 / 10) := by
  intro premise
  exact absurd premise.1 (by norm_num [Scope.permits])

-- A test that always rejects breaks a level premise at 1/20: premises have content.
example : ¬ LevelPremise .finiteSample (fun _ : Unit => Measure.dirac ()) (fun _ => True)
    ⟨Set.univ, MeasurableSet.univ⟩ (1 / 20) 0 := by
  intro premise
  have bound := premise.2 () trivial
  simp at bound
  norm_num at bound
