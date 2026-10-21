import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLParser
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalEncoding

/-! # The actual interpolated vendor encoding's depth moment bound

The pointwise Euclidean-coordinate bound is proved for the actual full-affine
midpoint inverse and its intrinsic sided encoding. This is the source moment
argument; its measurability obligation remains explicitly separate.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLMoment

open Set MeasureTheory PriceCurves PriceCurveHilbert
open InterpolatedImpactCurve
open scoped ENNReal

def depth {lo hi : ℝ} (m : ExcessSupply.Book lo hi) : ℝ := max m.buyDepth m.sellDepth

def priceBound (lo hi : ℝ) : ℝ := max |lo| |hi|

theorem canonical_coordinate_bounds {lo hi : ℝ} (m : ExcessSupply.Book lo hi) (u : Parameter) :
    |(PLCanonicalEncoding.encoding (Book.impactCurve m) u).1| ≤ depth m ∧
      |(PLCanonicalEncoding.encoding (Book.impactCurve m) u).2| ≤ priceBound lo hi := by
  let f := Book.impactCurve m
  let a := PLCanonicalEncoding.admissible f
  have hq : (a u : ℝ) ∈ m.domain := (a u).property
  have hp := m.price_bounded _ hq
  constructor
  · apply abs_le.mpr
    exact ⟨(neg_le_neg (le_max_left _ _)).trans hq.1,
      hq.2.trans (le_max_right _ _)⟩
  · exact abs_le_max_abs_abs hp.1 hp.2

theorem canonical_pair_norm_sq {lo hi : ℝ} (m : ExcessSupply.Book lo hi) (u : Parameter) :
    ‖pairEquiv (PLCanonicalEncoding.encoding (Book.impactCurve m) u)‖^2 ≤
      depth m^2 + (priceBound lo hi)^2 := by
  have h := canonical_coordinate_bounds m u
  rw [pricePair_norm_sq]
  apply add_le_add
  · simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h.1)).mpr h.1
  · simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h.2)).mpr h.2

/-- Actual full-affine canonical encodings, with the source factor2 when the
parameter measure is Lebesgue measure on [-1,1]. -/
theorem canonical_norm_sq_bound (ν : Measure Parameter) [IsFiniteMeasure ν]
    {lo hi : ℝ} (m : ExcessSupply.Book lo hi) :
    ‖PLCanonicalEncoding.encodingLp ν (Book.impactCurve m)‖^2 ≤
      ν.real univ * (depth m^2 + (priceBound lo hi)^2) := by
  let Z := PLCanonicalEncoding.encodingLp ν (Book.impactCurve m)
  have hbound : ∀ᵐ u ∂ν, ‖Z u‖^2 ≤ depth m^2 + (priceBound lo hi)^2 := by
    filter_upwards [PLParametrisation.coeFn_encodingLp ν (Book.impactCurve m)
      (PLCanonicalEncoding.admissible _)] with u hu
    change Z u = _ at hu
    rw [hu]
    exact canonical_pair_norm_sq m u
  calc
    ‖Z‖^2 = ∫ u, ‖Z u‖^2 ∂ν := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    _ ≤ ∫ _ : Parameter, (depth m^2 + (priceBound lo hi)^2) ∂ν := by
      apply integral_mono_ae _ (integrable_const _) hbound
      simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) Z Z
    _ = ν.real univ * (depth m^2 + (priceBound lo hi)^2) := by
      simp

/-- Original label: `prop:pl-encoding-measurable`.
The source depth second-moment implication for the actual full-affine map,
conditional only on its still-separate Borel/strong-measurability obligation. -/
theorem canonical_memLp_of_depth_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ν : Measure Parameter) [IsFiniteMeasure ν] (hν : ν.real univ = 2)
    {lo hi : ℝ} (M : Ω → ExcessSupply.Book lo hi)
    (hmeas : AEStronglyMeasurable
      (fun ω => PLCanonicalEncoding.encodingLp ν (Book.impactCurve (M ω))) μ)
    (hdepth : Integrable (fun ω => depth (M ω) ^ 2) μ) :
    MemLp (fun ω => PLCanonicalEncoding.encodingLp ν (Book.impactCurve (M ω))) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  apply ((hdepth.const_mul 2).add (integrable_const (2*(priceBound lo hi)^2))).mono'
    (hmeas.norm.pow 2)
  exact Filter.Eventually.of_forall fun ω => by
    change ‖‖PLCanonicalEncoding.encodingLp ν (Book.impactCurve (M ω))‖^2‖ ≤
      2*depth (M ω) ^ 2 + 2*(priceBound lo hi)^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := canonical_norm_sq_bound ν (M ω)
    rw [hν, mul_add] at h
    exact h

end Thesis.DayAhead.VendorPLMoment
