import Thesis.DayAhead.ForecastingImpact.LowRankGram
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # The renewable exercise's ridge forecast

Applications chapter, lines 164–205. The source uses a 365 by 156 training
design, 24 response columns, an entrywise pooled variance, and a positive-scale
domain guard. The displayed matrix inverse and the clipping rule are verified
here. These algebraic facts do not establish the availability or provenance of
the actual training rows, nor reproduce the plotted historical forecasts.
-/

noncomputable section
namespace Thesis.DayAhead.RidgeForecast

open scoped BigOperators Matrix

def pooledMean {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  (∑ i, ∑ j, X i j) / (m * p : ℕ)

def pooledVariance {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  (∑ i, ∑ j, (X i j - pooledMean X) ^ 2) / ((m * p : ℕ) - 1 : ℝ)

theorem pooledVariance_nonneg {m p : ℕ} (hsize : 1 ≤ m * p)
    (X : Matrix (Fin m) (Fin p) ℝ) : 0 ≤ pooledVariance X := by
  have hden : (0 : ℝ) ≤ (m * p : ℕ) - 1 := by
    have : (1 : ℝ) ≤ (m * p : ℕ) := by exact_mod_cast hsize
    linarith
  exact div_nonneg (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _) hden

theorem pooledVariance_eq_zero_iff {m p : ℕ} (hsize : 1 < m * p)
    (X : Matrix (Fin m) (Fin p) ℝ) :
    pooledVariance X = 0 ↔ ∀ i j, X i j = pooledMean X := by
  have hden : ((m * p : ℕ) - 1 : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (m * p : ℕ) := by exact_mod_cast hsize
    linarith
  rw [pooledVariance, div_eq_zero_iff, or_iff_left hden,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const]
  congr! 1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
  simp [sub_eq_zero]

variable {m p q : ℕ}

def normalMatrix (X : Matrix (Fin m) (Fin p) ℝ) (r : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  X.transpose * X + r • 1

theorem normalMatrix_posDef (X : Matrix (Fin m) (Fin p) ℝ) {r : ℝ} (hr : 0 < r) :
    (normalMatrix X r).PosDef := by
  have hgram : (X.transpose * X).PosSemidef := by
    simpa only [Matrix.conjTranspose, star_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  have hdiag : (r • (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef := by
    convert Matrix.PosDef.diagonal (n := Fin p) (fun _ => hr) using 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  exact Matrix.PosDef.posSemidef_add hgram hdiag

theorem normalMatrix_isUnit (X : Matrix (Fin m) (Fin p) ℝ) {r : ℝ} (hr : 0 < r) :
    IsUnit (normalMatrix X r) := (normalMatrix_posDef X hr).isUnit

def coefficients (X : Matrix (Fin m) (Fin p) ℝ) (Y : Matrix (Fin m) (Fin q) ℝ)
    (r : ℝ) : Matrix (Fin p) (Fin q) ℝ := (normalMatrix X r)⁻¹ * X.transpose * Y

theorem coefficients_normal_equation (X : Matrix (Fin m) (Fin p) ℝ)
    (Y : Matrix (Fin m) (Fin q) ℝ) {r : ℝ} (hr : 0 < r) :
    normalMatrix X r * coefficients X Y r = X.transpose * Y := by
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mp (normalMatrix_isUnit X hr)
  simp only [coefficients, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mul]

theorem coefficients_unique (X : Matrix (Fin m) (Fin p) ℝ)
    (Y : Matrix (Fin m) (Fin q) ℝ) {r : ℝ} (hr : 0 < r)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : normalMatrix X r * B = X.transpose * Y) :
    B = coefficients X Y r := by
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mp (normalMatrix_isUnit X hr)
  rw [coefficients, Matrix.mul_assoc, ← hB,
    Matrix.nonsing_inv_mul_cancel_left _ _ hunit]

/-- The source's dimensions and the pooled scale are used literally. -/
def fittedCoefficients (X : Matrix (Fin 365) (Fin 156) ℝ)
    (Y : Matrix (Fin 365) (Fin 24) ℝ) : Matrix (Fin 156) (Fin 24) ℝ :=
  coefficients X Y (pooledVariance X)

theorem fittedCoefficients_wellDefined (X : Matrix (Fin 365) (Fin 156) ℝ)
    (Y : Matrix (Fin 365) (Fin 24) ℝ) (hX : 0 < pooledVariance X) :
    (normalMatrix X (pooledVariance X)).PosDef ∧
      normalMatrix X (pooledVariance X) * fittedCoefficients X Y = X.transpose * Y :=
  ⟨normalMatrix_posDef X hX, coefficients_normal_equation X Y hX⟩

def clipProduction (capacity prediction : ℝ) : ℝ := min (max prediction 0) capacity

theorem clipProduction_bounds {capacity : ℝ} (hc : 0 ≤ capacity) (prediction : ℝ) :
    0 ≤ clipProduction capacity prediction ∧ clipProduction capacity prediction ≤ capacity :=
  ⟨le_min (le_max_right _ _) hc, min_le_right _ _⟩

theorem clipProduction_eq_self {capacity prediction : ℝ}
    (h0 : 0 ≤ prediction) (hc : prediction ≤ capacity) :
    clipProduction capacity prediction = prediction := by
  rw [clipProduction, max_eq_left h0, min_eq_left hc]

theorem clipProduction_idempotent {capacity : ℝ} (hc : 0 ≤ capacity) (prediction : ℝ) :
    clipProduction capacity (clipProduction capacity prediction) =
      clipProduction capacity prediction :=
  clipProduction_eq_self (clipProduction_bounds hc prediction).1
    (clipProduction_bounds hc prediction).2

def forecast (capacity : ℝ) (X : Matrix (Fin 365) (Fin 156) ℝ)
    (Y : Matrix (Fin 365) (Fin 24) ℝ) (target : Fin 156 → ℝ) (h : Fin 24) : ℝ :=
  clipProduction capacity (((fittedCoefficients X Y).transpose *ᵥ target) h)

theorem forecast_bounds {capacity : ℝ} (hc : 0 ≤ capacity)
    (X : Matrix (Fin 365) (Fin 156) ℝ) (Y : Matrix (Fin 365) (Fin 24) ℝ)
    (target : Fin 156 → ℝ) (h : Fin 24) :
    0 ≤ forecast capacity X Y target h ∧ forecast capacity X Y target h ≤ capacity :=
  clipProduction_bounds hc _

end Thesis.DayAhead.RidgeForecast
