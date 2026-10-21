import Mathlib.Tactic

/-! # Quantity-node projection need not contract the exact interpolant L² norm

On the final three equally spaced nodes take quantity values (0,2,1), with
all preceding nodes zero. The trapezoidal node fit pools the last two nodes
with weights 1 and 1/2, obtaining (0,5/3,5/3). The zero target is admissible.
Exact affine-cell integrals increase from 11/3 to 100/27, times cell width.
These proofs verify the pool's optimality and the exact norm discrepancy.
-/

namespace Thesis.Foundations.Research.NumericalNormCounterexample

noncomputable section

def pairLoss (a b : ℝ) : ℝ := (a - 2) ^ 2 + (1 / 2) * (b - 1) ^ 2

theorem pooled_pair_minimizes (a b : ℝ) (hab : a ≤ b) :
    pairLoss (5 / 3) (5 / 3) ≤ pairLoss a b := by
  have hsq : 0 ≤ (a - 5 / 3) ^ 2 := sq_nonneg _
  have hsq' : 0 ≤ (b - 5 / 3) ^ 2 := sq_nonneg _
  dsimp only [pairLoss]
  nlinarith

def interpolantNormSq (x y z : ℝ) : ℝ :=
  (x ^ 2 + x * y + y ^ 2) / 3 + (y ^ 2 + y * z + z ^ 2) / 3

theorem actual_l2_increases :
    interpolantNormSq 0 2 1 < interpolantNormSq 0 (5 / 3) (5 / 3) := by
  norm_num [interpolantNormSq]

theorem actual_l2_gap :
    interpolantNormSq 0 (5 / 3) (5 / 3) - interpolantNormSq 0 2 1 = 1 / 27 := by
  norm_num [interpolantNormSq]

end

end Thesis.Foundations.Research.NumericalNormCounterexample
