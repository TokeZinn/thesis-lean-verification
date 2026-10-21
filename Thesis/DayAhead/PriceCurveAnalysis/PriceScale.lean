import Thesis.Appendices.DayAheadNumerical.NumericalRepresentation
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! # Current asinh price transform and finite-grid smearing

The scalar norm bound proves that the forward transform preserves every Lp
class. On the current finite numerical carrier the inverse and finite smearing
are everywhere defined. An inverse on arbitrary infinite-dimensional L² is
asserted only when the transformed inverse is square integrable.
-/

noncomputable section
namespace Thesis.DayAhead.PriceScale

open MeasureTheory
open scoped BigOperators ENNReal

/-- Original label: `defn:asinh-price-transform`. -/
def transform (c p : ℝ) : ℝ := Real.arsinh (p / c)

def inverse (c z : ℝ) : ℝ := c * Real.sinh z

theorem inverse_transform (c : ℝ) (hc : c ≠ 0) (p : ℝ) :
    inverse c (transform c p) = p := by
  rw [inverse, transform, Real.sinh_arsinh]
  field_simp

theorem transform_inverse (c : ℝ) (hc : c ≠ 0) (z : ℝ) :
    transform c (inverse c z) = z := by
  simp [transform, inverse, hc, Real.arsinh_sinh]

theorem transform_strictMono (c : ℝ) (hc : 0 < c) : StrictMono (transform c) := by
  intro x y hxy
  exact Real.arsinh_strictMono ((div_lt_div_iff_of_pos_right hc).mpr hxy)

theorem abs_arsinh_le (x : ℝ) : |Real.arsinh x| ≤ |x| := by
  have h := (Real.self_le_sinh_iff).mpr (abs_nonneg (Real.arsinh x))
  simpa only [← Real.abs_sinh, Real.sinh_arsinh] using h

theorem abs_transform_le (c : ℝ) (hc : 0 < c) (p : ℝ) :
    |transform c p| ≤ c⁻¹ * |p| := by
  have h := abs_arsinh_le (p / c)
  simpa [transform, abs_div, abs_of_pos hc, div_eq_mul_inv, mul_comm] using h

/-- The norm bound in `defn:lifted-price-scale-smearing` supplies the actual
Lp integrability obligation, including on non-finite measure spaces. -/
theorem transform_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (c : ℝ) (hc : 0 < c) (f : Ω → ℝ) (hf : MemLp f p μ) :
    MemLp (fun ω => transform c (f ω)) p μ := by
  apply hf.of_le_mul
    (((Real.continuous_arsinh.comp (continuous_id.div_const c))).comp_aestronglyMeasurable hf.1)
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using abs_transform_le c hc (f ω)

/-- Original label: `defn:lifted-price-scale-smearing`, finite numerical lift. -/
def lift {m : ℕ} (c : ℝ) (z : NumericalRepresentation.Values m) :
    NumericalRepresentation.Values m where
  quantity := z.quantity
  price i := transform c (z.price i)

def inverseLift {m : ℕ} (c : ℝ) (z : NumericalRepresentation.Values m) :
    NumericalRepresentation.Values m where
  quantity := z.quantity
  price i := inverse c (z.price i)

theorem inverseLift_lift {m : ℕ} (c : ℝ) (hc : c ≠ 0)
    (z : NumericalRepresentation.Values m) : inverseLift c (lift c z) = z := by
  cases z
  simp only [inverseLift, lift, inverse_transform c hc]

/-- At least one residual is required; quantity residuals are set to zero as
specified by the current numerical appendix. -/
def smear {m n : ℕ} (c : ℝ) (z : NumericalRepresentation.Values m)
    (residual : Fin (n + 1) → Fin (2 * m) → ℝ) : NumericalRepresentation.Values m where
  quantity := z.quantity
  price i := ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j, inverse c (z.price i + residual j i)

theorem smear_quantity {m n : ℕ} (c : ℝ) (z : NumericalRepresentation.Values m)
    (residual : Fin (n + 1) → Fin (2 * m) → ℝ) :
    (smear c z residual).quantity = z.quantity := rfl

theorem smear_zero_residual {m n : ℕ} (c : ℝ) (z : NumericalRepresentation.Values m) :
    smear (n := n) c z (fun _ _ => 0) = inverseLift c z := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  cases z
  simp [smear, inverseLift, hn]

end Thesis.DayAhead.PriceScale
