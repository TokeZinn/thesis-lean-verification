import Thesis.DayAhead.ForecastingImpact.Forecasting
import Thesis.DayAhead.ForecastingImpact.EmpiricalGeometry

/-! # Current squared Hilbert loss and boosting identities

Source: Chapter 5, lines 51–60, 231–279 and 302–342. The tree learner is an
algorithmic input; no global optimality is asserted for the greedy search.
-/

noncomputable section
namespace Thesis.DayAhead.BoostingLoss

open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def squaredLoss (y prediction : H) : ℝ := ‖y - prediction‖ ^ 2
def lossGradient (y prediction : H) : H := (2 : ℝ) • (prediction - y)
def lossDerivative (y prediction : H) : H →L[ℝ] ℝ := (2 : ℝ) • innerSL ℝ (prediction - y)

theorem squaredLoss_hasFDerivAt (y prediction : H) :
    HasFDerivAt (squaredLoss y) (lossDerivative y prediction) prediction := by
  have h := ((hasFDerivAt_id prediction).sub_const y).norm_sq
  simpa only [squaredLoss, lossDerivative, ContinuousLinearMap.comp_id, norm_sub_rev,
    id_eq, two_smul] using h

theorem lossDerivative_gradient (y prediction h : H) :
    lossDerivative y prediction h = inner ℝ (lossGradient y prediction) h := by
  simp [lossDerivative, lossGradient, inner_smul_left, inner_sub_left]

theorem loss_increment (y prediction h : H) :
    squaredLoss y (prediction + h) - squaredLoss y prediction =
      lossDerivative y prediction h + ‖h‖ ^ 2 := by
  have he : y - (prediction + h) = (y - prediction) - h := by abel
  rw [squaredLoss, he, norm_sub_sq_real, squaredLoss]
  simp only [lossDerivative, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hi : inner ℝ (prediction - y) h = -inner ℝ (y - prediction) h := by
    rw [← inner_neg_left, neg_sub]
  rw [hi]
  ring

/-- The source's quotient identity includes the zero increment under Lean's
totalized division convention; nonzero increments give the usual quotient. -/
theorem loss_remainder_quotient (y prediction h : H) :
    |squaredLoss y (prediction + h) - squaredLoss y prediction -
      lossDerivative y prediction h| / ‖h‖ = ‖h‖ := by
  rw [loss_increment]
  rw [add_sub_cancel_left, abs_of_nonneg (sq_nonneg ‖h‖)]
  by_cases hz : ‖h‖ = 0
  · simp [hz]
  · field_simp

def empiricalRisk {ι X : Type*} (s : Finset ι) (x : ι → X) (y : ι → H) (f : X → H) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ i ∈ s, squaredLoss (y i) (f (x i))

def pseudoResidual (y prediction : H) : H := -lossGradient y prediction

theorem pseudoResidual_eq (y prediction : H) :
    pseudoResidual y prediction = (2 : ℝ) • (y - prediction) := by
  simp [pseudoResidual, lossGradient, ← smul_neg, neg_sub]

/-- The pointwise boosting update, including the stated shrinkage factor. -/
def boosted {X : Type*} (initial : X → H) (shrinkage : ℝ)
    (step : ℕ → ℝ) (tree : ℕ → X → H) : ℕ → X → H
  | 0 => initial
  | n + 1 => fun x => boosted initial shrinkage step tree n x +
      (shrinkage * step n) • tree n x

/-- Original label: `eq:ensemble-tree`.
The recursively updated predictor equals the finite ensemble exactly. -/
theorem boosted_eq_sum {X : Type*} (initial : X → H) (shrinkage : ℝ)
    (step : ℕ → ℝ) (tree : ℕ → X → H) (n : ℕ) (x : X) :
    boosted initial shrinkage step tree n x =
      initial x + ∑ k ∈ Finset.range n, (shrinkage * step k) • tree k x := by
  induction n with
  | zero => simp [boosted]
  | succ n ih => simp only [boosted, ih, Finset.sum_range_succ, add_assoc]

def lineLoss {ι : Type*} (s : Finset ι) (residual direction : ι → H) (γ : ℝ) : ℝ :=
  ∑ i ∈ s, ‖residual i - γ • direction i‖ ^ 2

def lineSearchStep {ι : Type*} (s : Finset ι) (residual direction : ι → H) : ℝ :=
  (∑ i ∈ s, inner ℝ (residual i) (direction i)) / (∑ i ∈ s, ‖direction i‖ ^ 2)

theorem lineLoss_quadratic {ι : Type*} (s : Finset ι) (residual direction : ι → H) (γ : ℝ) :
    lineLoss s residual direction γ = (∑ i ∈ s, ‖residual i‖ ^ 2) -
      2 * γ * (∑ i ∈ s, inner ℝ (residual i) (direction i)) +
      γ ^ 2 * (∑ i ∈ s, ‖direction i‖ ^ 2) := by
  simp only [lineLoss, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- The squared-loss line search has an attained minimizer even when the
fitted direction vanishes on all training observations. In that case every
step is optimal and the displayed totalized formula selects zero. -/
theorem lineSearchStep_minimal {ι : Type*} (s : Finset ι) (residual direction : ι → H) (γ : ℝ) :
    lineLoss s residual direction (lineSearchStep s residual direction) ≤
      lineLoss s residual direction γ := by
  let a := ∑ i ∈ s, ‖direction i‖ ^ 2
  let b := ∑ i ∈ s, inner ℝ (residual i) (direction i)
  have ha : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hz : a = 0
  · have hd : ∀ i ∈ s, direction i = 0 := by
      intro i hi
      have hsq : ‖direction i‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖direction j‖)).mp hz i hi
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    simp only [lineLoss]
    apply Finset.sum_le_sum
    intro i hi
    simp only [hd i hi, smul_zero, sub_zero, le_refl]
  · rw [lineLoss_quadratic, lineLoss_quadratic]
    change _ - 2 * (b / a) * b + (b / a) ^ 2 * a ≤ _ - 2 * γ * b + γ ^ 2 * a
    have he : a * (γ - b / a) ^ 2 = γ ^ 2 * a - 2 * γ * b + (b / a) ^ 2 * a := by
      field_simp
      ring
    have hn := mul_nonneg ha (sq_nonneg (γ - b / a))
    rw [he] at hn
    have hcancel : (b / a) * b = (b / a)^2 * a := by field_simp
    nlinarith

end Thesis.DayAhead.BoostingLoss
