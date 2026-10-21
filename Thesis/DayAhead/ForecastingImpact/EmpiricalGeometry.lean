import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Finite empirical identities in the current day-ahead chapters

These results concern the displayed mathematical formulas, not reproduction of
the data or figures. Positive denominator assumptions are kept explicit.
-/

noncomputable section

namespace Thesis.DayAhead.EmpiricalGeometry

open scoped BigOperators

/-- The current tree interpolation claim assumes pairwise distinct inputs.
This lemma records why that qualification is needed. -/
theorem duplicate_input_prevents_interpolation {X Y : Type*} (f : X → Y)
    {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ = x₂) (hy : y₁ ≠ y₂) :
    ¬(f x₁ = y₁ ∧ f x₂ = y₂) := by
  rintro ⟨h₁, h₂⟩
  exact hy (h₁.symm.trans ((congrArg f hx).trans h₂))

/-- Even an unrestricted real-valued predictor has strictly positive loss on
two equal inputs with responses zero and one. -/
theorem conflicting_pair_loss_lower_bound (prediction : ℝ) :
    (1 / 2 : ℝ) ≤ (0 - prediction) ^ 2 + (1 - prediction) ^ 2 := by
  nlinarith [sq_nonneg (prediction - 1 / 2)]

def coordinateScale (a b : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (a * x.1, b * x.2)

/-- Original label: `eq:standardizing-operator`.
The claimed inverse is an inverse when both scales are nonzero. -/
theorem coordinateScale_inverse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (x : ℝ × ℝ) :
    coordinateScale a b (coordinateScale a⁻¹ b⁻¹ x) = x := by
  ext <;> simp [coordinateScale, ha, hb]

/-- Zero empirical scales cannot define inverse operators on the ambient space. -/
theorem zero_coordinateScale_not_injective (b : ℝ) :
    ¬Function.Injective (coordinateScale 0 b) := by
  intro h
  have heq := h (a₁ := (0, 0)) (a₂ := (1, 0)) (by simp [coordinateScale])
  have := congrArg Prod.fst heq
  norm_num at this

/-- The paired-lag normalization in Chapter 4 is bounded by one. The index
set is the actual common-observation set; no regular calendar is required. -/
theorem paired_autocorrelation_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : 0 < ∑ i ∈ s, x i ^ 2) (hy : 0 < ∑ i ∈ s, y i ^ 2) :
    |(∑ i ∈ s, x i * y i) /
      (Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2))| ≤ 1 := by
  have hden : 0 < Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2) :=
    mul_pos (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr hy)
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq s x y
  have hbound : |∑ i ∈ s, x i * y i| ≤
      Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2) := by
    have hdensq : (Real.sqrt (∑ i ∈ s, x i ^ 2) *
        Real.sqrt (∑ i ∈ s, y i ^ 2)) ^ 2 =
        (∑ i ∈ s, x i ^ 2) * ∑ i ∈ s, y i ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
    nlinarith [sq_abs (∑ i ∈ s, x i * y i), abs_nonneg (∑ i ∈ s, x i * y i)]
  rw [abs_div, abs_of_pos hden]
  exact (div_le_one hden).mpr hbound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The cell mean used by the current recursive regression-tree model. -/
def cellMean {ι : Type*} (s : Finset ι) (y : ι → H) : H :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, y i

theorem sum_sub_cellMean {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (y : ι → H) :
    ∑ i ∈ s, (y i - cellMean s y) = 0 := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [cellMean, smul_smul, mul_inv_cancel₀ hn, one_smul, sub_self]

/-- The sum-of-squares decomposition displayed in Chapter 5, lines 336–342. 

 Original label: `lem:cell-risk-minimiser`. -/
theorem cell_sum_squares {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (y : ι → H) (z : H) :
    ∑ i ∈ s, ‖y i - z‖ ^ 2 =
      (∑ i ∈ s, ‖y i - cellMean s y‖ ^ 2) + (s.card : ℝ) * ‖z - cellMean s y‖ ^ 2 := by
  have hinner : ∑ i ∈ s, inner ℝ (y i - cellMean s y) (cellMean s y - z) = 0 := by
    rw [← sum_inner, sum_sub_cellMean s hs y, inner_zero_left]
  have hterm (i : ι) : ‖y i - z‖ ^ 2 = ‖y i - cellMean s y‖ ^ 2 +
      2 * inner ℝ (y i - cellMean s y) (cellMean s y - z) + ‖cellMean s y - z‖ ^ 2 := by
    have heq : y i - z = (y i - cellMean s y) + (cellMean s y - z) := by abel
    rw [heq, norm_add_sq_real]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hinner]
  simp [norm_sub_rev, nsmul_eq_mul]

/-- The empirical mean is the unique minimizer; completeness is unnecessary. 

 Original label: `lem:cell-risk-minimiser`. -/
theorem cellMean_unique_minimizer {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (y : ι → H) (z : H) :
    (∑ i ∈ s, ‖y i - z‖ ^ 2) ≤ (∑ i ∈ s, ‖y i - cellMean s y‖ ^ 2) ↔
      z = cellMean s y := by
  rw [cell_sum_squares s hs y z]
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  constructor
  · intro h
    have hsq : ‖z - cellMean s y‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ hn).mp (show (s.card : ℝ) * ‖z - cellMean s y‖ ^ 2 ≤
        (s.card : ℝ) * 0 by linarith)
    have hzero : ‖z - cellMean s y‖ = 0 := by
      nlinarith [sq_nonneg ‖z - cellMean s y‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · rintro rfl
    simp

end Thesis.DayAhead.EmpiricalGeometry
