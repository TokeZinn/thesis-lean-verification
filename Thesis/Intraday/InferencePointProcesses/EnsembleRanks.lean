import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Finite-ensemble midranks from the current intraday chapter

The displayed statistic is well-defined and bounded for a nonempty ensemble.
It does not have a continuous uniform null law merely because a model is
correct: the exact constant-model calculation below retains all ties.
-/

noncomputable section
namespace Thesis.Intraday.EnsembleRanks
open scoped BigOperators

/-- Original label: `defn:ensemble-mid-rank-coverage`. -/
def midrank {B : ℕ} (observed : ℝ) (sample : Fin B → ℝ) : ℝ :=
  (∑ i, ((if sample i < observed then 1 else 0) +
    (if sample i = observed then (1/2 : ℝ) else 0))) / B

theorem midrank_nonneg {B : ℕ} (observed : ℝ) (sample : Fin B → ℝ) :
    0 ≤ midrank observed sample := by
  unfold midrank
  positivity

theorem midrank_le_one {B : ℕ} (hB : 0 < B) (observed : ℝ) (sample : Fin B → ℝ) :
    midrank observed sample ≤ 1 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  unfold midrank
  apply (div_le_one hb).mpr
  calc
    _ ≤ ∑ _i : Fin B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hlt : sample i < observed
      · simp [hlt, ne_of_lt hlt]
      · simp [hlt]; split <;> norm_num
    _ = B := by simp

/-- Under a perfectly specified constant model every tie-adjusted
ensemble rank equals one half, for every positive ensemble size. -/
theorem midrank_constant {B : ℕ} (hB : 0 < B) (value : ℝ) :
    midrank value (fun _ : Fin B => value) = 1/2 := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  simp [midrank, hb]

/-- A central-rank coverage check accepts every constant-model observation
at any significance level between zero and one, not a fraction `1 - α`. -/
theorem constant_rank_in_central_band {B : ℕ} (hB : 0 < B) (value α : ℝ)
    (hα : α ≤ 1) :
    α/2 ≤ midrank value (fun _ : Fin B => value) ∧
      midrank value (fun _ : Fin B => value) ≤ 1-α/2 := by
  rw [midrank_constant hB]
  constructor <;> linarith

end Thesis.Intraday.EnsembleRanks
