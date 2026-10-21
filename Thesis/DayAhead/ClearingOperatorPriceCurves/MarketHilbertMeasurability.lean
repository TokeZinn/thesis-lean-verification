import Thesis.DayAhead.ClearingOperatorPriceCurves.MarketCurveEncoding
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Borel measurability and second moments of the actual market Hilbert map

The map starts from the original tagged order tuple. Its canonical
representative is jointly measurable by the preceding construction. Distances
to fixed L² elements are then measurable integrals, proving Borel measurability
in the norm topology. No measurable curve-valued input is assumed.
-/

noncomputable section
namespace Thesis.DayAhead.MarketCurve

open Set MeasureTheory TopologicalSpace
open Foundations.MarketClearing.Sorting
open MarketImpact PriceCurves SidedCertificate SidedCurveLp CanonicalSidedLp PriceCurveHilbert
open SidedParametrisation

local instance : MeasurableSpace MarketTuple := borel _
local instance : BorelSpace MarketTuple := ⟨rfl⟩
local instance : MeasurableSpace PricePair := borel _
local instance : BorelSpace PricePair := ⟨rfl⟩
local instance : MeasurableSpace (PriceHilbertSpace sidedLebesgueMeasure) := borel _
local instance : BorelSpace (PriceHilbertSpace sidedLebesgueMeasure) := ⟨rfl⟩
local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

theorem measurable_of_distances {Ω H : Type*} [MeasurableSpace Ω]
    [MetricSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (F : Ω → H) (hF : ∀ h, Measurable (fun ω => dist (F ω) h)) : Measurable F := by
  apply measurable_of_isOpen
  intro s hs
  let B := {p : H × ℝ // Metric.ball p.1 p.2 ⊆ s}
  have hcover : (⋃ p : B, Metric.ball p.val.1 p.val.2) = s := by
    apply Subset.antisymm
    · exact iUnion_subset fun p => p.property
    · intro x hx
      obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs x hx
      exact mem_iUnion.mpr ⟨⟨(x, r), hrs⟩, Metric.mem_ball_self hr⟩
  obtain ⟨T, hT, hU⟩ := isOpen_iUnion_countable
    (fun p : B => Metric.ball p.val.1 p.val.2) (fun _ => Metric.isOpen_ball)
  rw [← hcover, ← hU, preimage_iUnion₂]
  exact MeasurableSet.biUnion hT fun p _ => measurableSet_lt (hF p.val.1) measurable_const

theorem marketHilbertCurve_dist_sq (upper : ℝ) (hupper : 0 ≤ upper)
    (m : RegimeState upper) (g : PriceHilbertSpace sidedLebesgueMeasure) :
    dist (marketHilbertCurve upper hupper m) g ^ 2 =
      ∫ u : ℝ, ‖pairEquiv
        (canonicalSidedEncoding (impactCurve upper hupper m.val m.property.1 m.property.2)
          (clampParameter u)) - g u‖ ^ 2 ∂sidedLebesgueMeasure := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (marketHilbertCurve upper hupper m) g,
    coeFn_canonicalSidedEncodingLpReal
      (impactCurve upper hupper m.val m.property.1 m.property.2)] with u hu hz
  change marketHilbertCurve upper hupper m u = _ at hz
  rw [real_inner_self_eq_norm_sq, hu, Pi.sub_apply, hz]

/-- Original label: `prop:pl-encoding-measurable`.
Supporting step-order submodel only: the current interpolated piecewise-affine
market is not identified with this map. The proposition's carrier on the literal
vendor-list state space `𝓛` is `VendorPLSourceTheorem.measurable_encoding` /
`measurable_crossingPrice` / `encoding_memLp_of_depth_second_moment` (assembled with
Lebesgue parameter measure in `VendorPLProposition`); this declaration is the
step-order (tagged order tuple) sub-model of the same statement.
The actual canonical market-state map is Borel measurable in the Euclidean
L² norm topology on the fixed-regime, positive-volume state domain. -/
theorem measurable_marketHilbertCurve (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (marketHilbertCurve upper hupper) := by
  apply measurable_of_distances
  intro g
  have hrepr : Measurable (fun x : RegimeState upper × ℝ =>
      pairEquiv (canonicalSidedEncoding
        (impactCurve upper hupper x.1.val x.1.property.1 x.1.property.2)
        (clampParameter x.2))) :=
    pairEquiv.continuous.measurable.comp (measurable_canonicalMarketRepresentative upper hupper)
  have hg : Measurable (fun x : RegimeState upper × ℝ => g x.2) :=
    (Lp.stronglyMeasurable g).measurable.comp measurable_snd
  have hint : Measurable (fun m : RegimeState upper =>
      ∫ u : ℝ, ‖pairEquiv (canonicalSidedEncoding
        (impactCurve upper hupper m.val m.property.1 m.property.2)
        (clampParameter u)) - g u‖ ^ 2 ∂sidedLebesgueMeasure) :=
    ((hrepr.sub hg).norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have he (m : RegimeState upper) : dist (marketHilbertCurve upper hupper m) g =
      Real.sqrt (∫ u : ℝ, ‖pairEquiv (canonicalSidedEncoding
        (impactCurve upper hupper m.val m.property.1 m.property.2)
        (clampParameter u)) - g u‖ ^ 2 ∂sidedLebesgueMeasure) := by
    rw [← marketHilbertCurve_dist_sq, Real.sqrt_sq (dist_nonneg)]
  simp_rw [he]
  exact Real.continuous_sqrt.measurable.comp hint

/-- Original label: `prop:pl-encoding-measurable`.
Supporting step-order submodel only: the current interpolated piecewise-affine
market is not identified with this map. The proposition's carrier on the literal
vendor-list state space is `VendorPLSourceTheorem.encoding_memLp_of_depth_second_moment`
(and `VendorPLProposition.integrable_squared_norm`); this declaration is the
step-order (tagged order tuple) sub-model of the same moment clause.
For a measurable random original state, the stated depth second moment
implies square integrability of its actual canonical Hilbert curve. -/
theorem marketHilbertCurve_memLp_of_depth_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (upper : ℝ) (hupper : 0 ≤ upper) (M : Ω → RegimeState upper) (hM : Measurable M)
    (hD : Integrable (fun ω => (depth (M ω).val) ^ 2) μ) :
    MemLp (fun ω => marketHilbertCurve upper hupper (M ω)) 2 μ :=
  marketHilbertCurve_memLp_of_aestronglyMeasurable upper hupper M
    ((measurable_marketHilbertCurve upper hupper).comp hM).aestronglyMeasurable hD

end Thesis.DayAhead.MarketCurve
