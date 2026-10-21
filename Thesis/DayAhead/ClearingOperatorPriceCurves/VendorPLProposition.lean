import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLSourceTheorem
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLParameterMeasure

/-! # The literal Lebesgue-space form of prop:pl-encoding-measurable

All input restrictions and the source representative are supplied by the
concrete source carrier. Here the parameter measure is exactly Lebesgue
measure on [-1,1]; atomlessness and mass two are proved, not assumed.
-/

noncomputable section
namespace Thesis.DayAhead.VendorPLProposition

open Set MeasureTheory VendorPLSourceCarrier VendorPLSourceTheorem
open PriceCurveHilbert PLParameterMeasure

variable {lo hi : ℝ} (hlohi : lo ≤ hi)

abbrev Hilbert := PriceHilbertSpace lebesgue

def Z (m : Source hlohi) : Hilbert := encoding hlohi lebesgue m

/-- Original label: `prop:pl-encoding-measurable`.
Borel measurability of `m ↦ Z(m) ∈ L²([-1,1];ℝ²)` with the parameter measure equal to
Lebesgue measure on `[-1,1]`. -/
theorem measurable_Z : @Measurable (Source hlohi) Hilbert _ (borel Hilbert) (Z hlohi) :=
  measurable_encoding hlohi lebesgue

/-- Original label: `prop:pl-encoding-measurable`.
Borel measurability of the crossing price `m ↦ P_m(0)`. -/
theorem measurable_crossing : Measurable (crossingPrice hlohi) := measurable_crossingPrice hlohi

theorem norm_sq_bound (m : Source hlohi) :
    ‖Z hlohi m‖ ^ 2 ≤ 2 * depth hlohi m ^ 2 + 2 * (VendorPLMoment.priceBound lo hi) ^ 2 := by
  change ‖encoding hlohi lebesgue m‖ ^ 2 ≤ _
  rw [encoding_eq_raw]
  have h := VendorPLMoment.canonical_norm_sq_bound lebesgue (sourceBook hlohi m)
  rw [lebesgue_real_univ, mul_add] at h
  exact h

theorem square_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Ω → Source hlohi) (hM : Measurable M)
    (hdepth : Integrable (fun w => depth hlohi (M w) ^ 2) μ) :
    MemLp (fun w => Z hlohi (M w)) 2 μ :=
  encoding_memLp_of_depth_second_moment hlohi lebesgue lebesgue_real_univ M hM hdepth

/-- Original label: `prop:pl-encoding-measurable`.
Literal finite expected squared Hilbert norm conclusion of the source:
`E[D(M)²] < ∞` implies `E[‖Z(M)‖²_{L²([-1,1];ℝ²)}] < ∞`. -/
theorem integrable_squared_norm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Ω → Source hlohi) (hM : Measurable M)
    (hdepth : Integrable (fun w => depth hlohi (M w) ^ 2) μ) :
    Integrable (fun w => ‖Z hlohi (M w)‖ ^ 2) μ := by
  have hm := square_integrable hlohi M hM hdepth
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

end Thesis.DayAhead.VendorPLProposition
