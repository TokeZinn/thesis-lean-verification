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

def inverse (c z : ℝ) : ℝ := c * Real.sinh z

theorem abs_arsinh_le (x : ℝ) : |Real.arsinh x| ≤ |x| := by
  have h := (Real.self_le_sinh_iff).mpr (abs_nonneg (Real.arsinh x))
  simpa only [← Real.abs_sinh, Real.sinh_arsinh] using h

def inverseLift {m : ℕ} (c : ℝ) (z : NumericalRepresentation.Values m) :
    NumericalRepresentation.Values m where
  quantity := z.quantity
  price i := inverse c (z.price i)

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
