import Thesis.DayAhead.ClearingOperatorPriceCurves.ImpactJoin
import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedLp

/-!
Scope note (2026-10-20): this module proves the finite-level step-order
submodel. The current thesis uses interpolated piecewise-affine orders;
these results are supporting simple-curve lemmas, not the current
`prop:pl-encoding-measurable` or full market reconstruction.
 # The actual market-derived price curve and its canonical Hilbert encoding

The curve fields are proved from the raw order book, rather than supplied as
assumptions. The resulting Hilbert-valued map's measurability is proved separately
in `MarketHilbertMeasurability.lean`.
-/

noncomputable section
namespace Thesis.DayAhead.MarketCurve

open Set MeasureTheory
open Foundations.MarketRepresentation Foundations.MarketClearing.Sorting
open MarketImpact ImpactJoin PriceCurves SidedCertificate SidedCurveLp CanonicalSidedLp
open PriceCurveHilbert

def impactCurve (upper : ℝ) (hupper : 0 ≤ upper) (m : MarketTuple)
    (hm : m ∈ positiveStates) (hp : priceBounded upper m) : PriceCurve where
  leftEndpoint := -buyDepth m
  rightEndpoint := sellDepth m
  leftEndpoint_nonpos := neg_nonpos.mpr (totalQuantity_nonneg _)
  rightEndpoint_nonneg := totalQuantity_nonneg _
  price := fun q => impactPrice upper (m, q.val)
  price_monotone := fun _ _ h => impactPrice_monotone upper hupper m hm hp h
  price_finite := (impactPrice_finite_range upper m).subset (by
    rintro _ ⟨q, rfl⟩
    exact mem_range_self q.val)

/-- Original label: `claim:pw-constant`.
The actual market map has a finite disjoint interval decomposition, including
any singleton boundary cells required by the stated midpoint convention. -/
theorem impactCurve_minimalRepresentation (upper : ℝ) (hupper : 0 ≤ upper) (m : MarketTuple)
    (hm : m ∈ positiveStates) (hp : priceBounded upper m) :
    Nonempty (MinimalRepresentation (impactCurve upper hupper m hm hp)) :=
  exists_minimalRepresentation _

/-- Original label: `claim:increasing`. -/
theorem impactCurve_monotone (upper : ℝ) (hupper : 0 ≤ upper) (m : MarketTuple)
    (hm : m ∈ positiveStates) (hp : priceBounded upper m) :
    Monotone (impactCurve upper hupper m hm hp).price :=
  (impactCurve upper hupper m hm hp).price_monotone

abbrev RegimeState (upper : ℝ) := {m : MarketTuple // m ∈ positiveStates ∧ priceBounded upper m}

/-- The exact canonical, essential-representative Hilbert curve in the source.
No measurable curve-valued input is assumed. -/
def marketHilbertCurve (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper) :
    PriceHilbertSpace sidedLebesgueMeasure :=
  canonicalSidedEncodingLpReal (impactCurve upper hupper m.val m.property.1 m.property.2)

theorem impactCurve_price_bounds (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper)
    (q : Icc (-buyDepth m.val) (sellDepth m.val)) :
    (impactCurve upper hupper m.val m.property.1 m.property.2).price q ∈ Icc (-500) upper :=
  impactPrice_mem_Icc upper hupper m.val m.property.2 q.val

theorem essential_impactCurve_price_bounds (upper : ℝ) (hupper : 0 ≤ upper)
    (m : RegimeState upper) (q : Icc (-buyDepth m.val) (sellDepth m.val)) :
    (impactCurve upper hupper m.val m.property.1 m.property.2).essential.price q ∈
      Icc (-500) upper := by
  obtain ⟨r, hr⟩ :=
    (impactCurve upper hupper m.val m.property.1 m.property.2).essentialPrice_mem_range q
  change (impactCurve upper hupper m.val m.property.1 m.property.2).essentialPrice q ∈
    Icc (-500) upper
  rw [← hr]
  exact impactCurve_price_bounds upper hupper m r

/-- The actual representative has the coordinate bounds used in the moment
argument of `prop:market-state-hilbert-curve`. -/
theorem canonical_coordinates_bounds (upper : ℝ) (hupper : 0 ≤ upper)
    (m : RegimeState upper) (u : Parameter) :
    let z := canonicalSidedEncoding (impactCurve upper hupper m.val m.property.1 m.property.2) u
    |z.1| ≤ depth m.val ∧ |z.2| ≤ max 500 upper := by
  let f := impactCurve upper hupper m.val m.property.1 m.property.2
  have hz : canonicalSidedEncoding f u ∈ f.essential.graph := by
    rw [← range_canonicalSidedEncoding]
    exact mem_range_self u
  obtain ⟨q, hq⟩ := hz
  change |(canonicalSidedEncoding f u).1| ≤ depth m.val ∧
    |(canonicalSidedEncoding f u).2| ≤ max 500 upper
  rw [← hq]
  refine ⟨abs_le_depth q.property, abs_le.mpr ?_⟩
  have hb := essential_impactCurve_price_bounds upper hupper m q
  exact ⟨(neg_le_neg (le_max_left 500 upper)).trans hb.1,
    hb.2.trans (le_max_right 500 upper)⟩

theorem canonical_norm_sq_bound (upper : ℝ) (hupper : 0 ≤ upper)
    (m : RegimeState upper) (u : Parameter) :
    ‖pairEquiv
      (canonicalSidedEncoding (impactCurve upper hupper m.val m.property.1 m.property.2) u)‖ ^ 2 ≤
      (depth m.val) ^ 2 + (max 500 upper) ^ 2 := by
  have hb := canonical_coordinates_bounds upper hupper m u
  rw [pricePair_norm_sq]
  apply add_le_add
  · simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hb.1)).mpr hb.1
  · simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hb.2)).mpr hb.2

/-- The norm estimate in the proof of `prop:market-state-hilbert-curve`, for
the actual state-derived Hilbert element. This is independent of the separate
measurability proof. -/
theorem marketHilbertCurve_norm_sq_bound (upper : ℝ) (hupper : 0 ≤ upper)
    (m : RegimeState upper) :
    ‖marketHilbertCurve upper hupper m‖ ^ 2 ≤
      2 * (depth m.val) ^ 2 + 2 * (max 500 upper) ^ 2 := by
  let Z := marketHilbertCurve upper hupper m
  have hae : ∀ᵐ x ∂sidedLebesgueMeasure,
      ‖Z x‖ ^ 2 ≤ (depth m.val) ^ 2 + (max 500 upper) ^ 2 := by
    filter_upwards [coeFn_canonicalSidedEncodingLpReal
      (impactCurve upper hupper m.val m.property.1 m.property.2)] with x hx
    change Z x = _ at hx
    rw [hx]
    exact canonical_norm_sq_bound upper hupper m _
  calc
    ‖Z‖ ^ 2 = ∫ x, ‖Z x‖ ^ 2 ∂sidedLebesgueMeasure := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    _ ≤ ∫ _ : ℝ, ((depth m.val) ^ 2 + (max 500 upper) ^ 2) ∂sidedLebesgueMeasure := by
      apply integral_mono_ae _ (integrable_const _) hae
      simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) Z Z
    _ = 2 * (depth m.val) ^ 2 + 2 * (max 500 upper) ^ 2 := by
      norm_num [sidedLebesgueMeasure, Measure.real, Real.volume_Icc, mul_add]

/-- The moment implication for the actual Hilbert curve, conditional only on
its separate strong-measurability obligation. The hypothesis is explicit so
this lemma cannot be mistaken for a proof of the proposition's Borel clause. -/
theorem marketHilbertCurve_memLp_of_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (upper : ℝ) (hupper : 0 ≤ upper) (M : Ω → RegimeState upper)
    (hZ : AEStronglyMeasurable (fun ω => marketHilbertCurve upper hupper (M ω)) μ)
    (hD : Integrable (fun ω => (depth (M ω).val) ^ 2) μ) :
    MemLp (fun ω => marketHilbertCurve upper hupper (M ω)) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hZ).mpr
  apply ((hD.const_mul 2).add (integrable_const (2 * (max 500 upper) ^ 2))).mono'
    (hZ.norm.pow 2)
  exact Filter.Eventually.of_forall fun ω => by
    change ‖‖marketHilbertCurve upper hupper (M ω)‖ ^ 2‖ ≤
      2 * (depth (M ω).val) ^ 2 + 2 * (max 500 upper) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact marketHilbertCurve_norm_sq_bound upper hupper (M ω)

end Thesis.DayAhead.MarketCurve
