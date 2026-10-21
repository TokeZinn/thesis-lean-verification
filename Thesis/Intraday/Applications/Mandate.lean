import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Pathwise total-variation-normalised mandate

The deterministic formula and sign-symmetry parts of `defn:se-mandate` and
`prop:mandate-martingale`. `MandateGaussian` derives the Gaussian joint law,
nonzero denominator almost surely, and full natural-filtration martingale.
-/

noncomputable section
namespace Thesis.Intraday.Mandate
open scoped BigOperators
open MeasureTheory

def totalVariation {K : ℕ} (xi : Fin K → ℝ) : ℝ := ∑ j, |xi j|

def increment {K : ℕ} (TV : ℝ) (xi : Fin K → ℝ) (j : Fin K) : ℝ :=
  TV * xi j / totalVariation xi

/-- Original label: `defn:se-mandate`.
Deterministic formula; `MandateGaussian` supplies the law and filtration. -/
def walk {K : ℕ} (TV : ℝ) (xi : Fin K → ℝ) (k : ℕ) : ℝ :=
  TV * (∑ j ∈ Finset.univ.filter (fun j : Fin K => j.val < k), xi j) / totalVariation xi

theorem totalVariation_nonneg {K : ℕ} (xi : Fin K → ℝ) : 0 ≤ totalVariation xi :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem increment_abs {K : ℕ} (TV : ℝ) (hTV : 0 ≤ TV) (xi : Fin K → ℝ) (j : Fin K) :
    |increment TV xi j| = TV * |xi j| / totalVariation xi := by
  simp [increment, abs_div, abs_mul, abs_of_nonneg hTV,
    abs_of_nonneg (totalVariation_nonneg xi)]

/-- Original label: `prop:mandate-martingale`.
Pathwise variation lemma used in the complete theorem in `MandateGaussian`. -/
theorem total_variation_normalised {K : ℕ} (TV : ℝ) (hTV : 0 ≤ TV) (xi : Fin K → ℝ)
    (hS : totalVariation xi ≠ 0) : ∑ j, |increment TV xi j| = TV := by
  simp_rw [increment_abs TV hTV xi]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change TV * totalVariation xi / totalVariation xi = TV
  exact mul_div_cancel_right₀ TV hS

theorem walk_zero {K : ℕ} (TV : ℝ) (xi : Fin K → ℝ) : walk TV xi 0 = 0 := by
  simp [walk]

theorem walk_bound {K : ℕ} (TV : ℝ) (hTV : 0 ≤ TV) (xi : Fin K → ℝ)
    (hS : 0 < totalVariation xi) (k : ℕ) : |walk TV xi k| ≤ TV := by
  have hpart : |∑ j ∈ Finset.univ.filter (fun j : Fin K => j.val < k), xi j| ≤
      totalVariation xi := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin K => j.val < k), |xi j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |xi j| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)
  rw [walk, abs_div, abs_mul, abs_of_nonneg hTV, abs_of_nonneg hS.le]
  exact (div_le_iff₀ hS).mpr (mul_le_mul_of_nonneg_left hpart hTV)

def reflect {K : ℕ} (xi : Fin K → ℝ) (j : Fin K) (i : Fin K) : ℝ :=
  if i = j then -xi i else xi i

theorem reflection_totalVariation {K : ℕ} (xi : Fin K → ℝ) (j : Fin K) :
    totalVariation (reflect xi j) = totalVariation xi := by
  unfold totalVariation
  apply Finset.sum_congr rfl
  intro i _
  simp [reflect]; split <;> simp

theorem reflection_increment {K : ℕ} (TV : ℝ) (xi : Fin K → ℝ) (j : Fin K) :
    increment TV (reflect xi j) j = -increment TV xi j := by
  simp [increment, reflection_totalVariation, reflect, neg_div]

theorem reflection_preserves_past {K : ℕ} (TV : ℝ) (xi : Fin K → ℝ) (j : Fin K)
    (k : ℕ) (hk : k ≤ j.val) : walk TV (reflect xi j) k = walk TV xi k := by
  unfold walk
  rw [reflection_totalVariation]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have h : i ≠ j := by
    have := (Finset.mem_filter.mp hi).2
    intro he; subst i; omega
  simp [reflect, h]

/-- Measure-preserving reflection makes every integrable odd test product
have mean zero, the step used in the thesis's natural-filtration argument. -/
theorem reflection_mean_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ) (f : Ω → ℝ)
    (hf : ∀ x, f (T x) = -f x) : ∫ x, f x ∂μ = 0 := by
  have he := hT.integral_comp' f
  have hn : (fun x => f (T x)) = -f := funext hf
  rw [hn] at he
  change (∫ x, -f x ∂μ) = _ at he
  rw [integral_neg] at he
  linarith

end Thesis.Intraday.Mandate
