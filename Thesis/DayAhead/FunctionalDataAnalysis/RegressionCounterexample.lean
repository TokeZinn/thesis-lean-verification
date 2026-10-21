import Mathlib.Tactic

/-! # DA-040: different information sets have different regression minima

For a fair two-point sample with X = (-1,1), constant predictors are exactly
the predictors measurable with respect to the trivial information set. A
predictor observing X itself has zero loss. These finite calculations certify
the historical counterexample in audit/ultravibe/FORMAL_FINDINGS.md, retained
as a regression guard after the UV001 information-set correction.
-/

noncomputable section

namespace Thesis.DayAhead.RegressionCounterexample

def risk (predictionMinus predictionPlus : ℝ) : ℝ :=
  ((-1 - predictionMinus) ^ 2 + (1 - predictionPlus) ^ 2) / 2

theorem constant_risk (c : ℝ) : risk c c = 1 + c ^ 2 := by
  unfold risk
  ring

theorem best_constant_risk (c : ℝ) : 1 ≤ risk c c := by
  rw [constant_risk]
  exact le_add_of_nonneg_right (sq_nonneg c)

theorem constant_minimum_attained : risk 0 0 = 1 := by norm_num [risk]

theorem fully_observed_risk : risk (-1) 1 = 0 := by norm_num [risk]

theorem information_sets_have_different_minima :
    risk (-1) 1 < risk 0 0 ∧ (∀ c : ℝ, risk 0 0 ≤ risk c c) := by
  rw [fully_observed_risk, constant_minimum_attained]
  exact ⟨by norm_num, best_constant_risk⟩

end Thesis.DayAhead.RegressionCounterexample
