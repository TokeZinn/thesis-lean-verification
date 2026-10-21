import Thesis.DayAhead.ClearingOperatorPriceCurves.MarketCurve
import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialPriceSampling
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveCuts
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveBlockCounts

/-! # Joint measurability of the actual essential market price

The scalar construction includes the thesis's selected one-sided convention,
even when the physical endpoints move with the state. The further passage to
the canonical equal-block parametrisation is proved in `MarketCurveEncoding.lean`.
-/

noncomputable section
namespace Thesis.DayAhead.MarketCurve

open Set Filter Topology MeasureTheory
open Foundations.MarketRepresentation MarketImpact PriceCurves
open Foundations.MarketClearing.Sorting
open SidedCertificate Foundations.Stochastic.MeasurableDistinctCounts

local instance : MeasurableSpace MarketTuple := borel _
local instance : BorelSpace MarketTuple := ⟨rfl⟩

def clampedQuantity {upper : ℝ} (m : RegimeState upper) (q : ℝ) :
    Icc (-buyDepth m.val) (sellDepth m.val) :=
  ⟨max (-buyDepth m.val) (min (sellDepth m.val) q), le_max_left _ _,
    max_le ((neg_nonpos.mpr (totalQuantity_nonneg _)).trans (totalQuantity_nonneg _))
      (min_le_left _ _)⟩

theorem measurable_clampedQuantity (upper : ℝ) :
    Measurable (fun x : RegimeState upper × ℝ => (clampedQuantity x.1 x.2 : ℝ)) := by
  exact ((continuous_buyDepth.measurable.comp
    (measurable_subtype_coe.comp measurable_fst)).neg).max
      ((continuous_sellDepth.measurable.comp
        (measurable_subtype_coe.comp measurable_fst)).min measurable_snd)

def essentialImpactPrice (upper : ℝ) (hupper : 0 ≤ upper) (x : RegimeState upper × ℝ) : ℝ :=
  (impactCurve upper hupper x.1.val x.1.property.1 x.1.property.2).essentialPrice
    (clampedQuantity x.1 x.2)

theorem measurable_marketSample (upper : ℝ) (n : ℕ) :
    Measurable (fun x : RegimeState upper × ℝ =>
      essentialSample (-buyDepth x.1.val) (sellDepth x.1.val) (clampedQuantity x.1 x.2) n) := by
  have ha : Measurable (fun x : RegimeState upper × ℝ => -buyDepth x.1.val) :=
    (continuous_buyDepth.measurable.comp (measurable_subtype_coe.comp measurable_fst)).neg
  have hb : Measurable (fun x : RegimeState upper × ℝ => sellDepth x.1.val) :=
    continuous_sellDepth.measurable.comp (measurable_subtype_coe.comp measurable_fst)
  have hq := measurable_clampedQuantity upper
  exact (hq.add ((hb.sub hq).div_const _)).ite (measurableSet_lt hq hb)
    (hq.sub ((hq.sub ha).div_const _))

/-- The selected price is jointly Borel in the original state and the physical
quantity, rather than postulated to be measurable as an input curve. -/
theorem measurable_essentialImpactPrice (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (essentialImpactPrice upper hupper) := by
  let g (n : ℕ) (x : RegimeState upper × ℝ) : ℝ :=
    impactPrice upper (x.1.val,
      essentialSample (-buyDepth x.1.val) (sellDepth x.1.val) (clampedQuantity x.1 x.2) n)
  apply measurable_of_tendsto_metrizable (f := g)
  · intro n
    exact (measurable_impactPrice upper).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_marketSample upper n))
  · apply tendsto_pi_nhds.mpr
    intro x
    exact (impactCurve upper hupper x.1.val x.1.property.1 x.1.property.2).tendsto_sample_price
      (clampedQuantity x.1 x.2)

def marketPriceCut (upper : ℝ) (hupper : 0 ≤ upper) (x : RegimeState upper × ℝ) : ℝ :=
  (impactCurve upper hupper x.1.val x.1.property.1 x.1.property.2).essential.rationalSublevelCut x.2

/-- A jointly measurable boundary at any specified price level. -/
theorem measurable_marketPriceCut (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (marketPriceCut upper hupper) := by
  change Measurable (fun x : RegimeState upper × ℝ => ⨆ r : ℚ,
    if essentialImpactPrice upper hupper (x.1, r) ≤ x.2 then
      (clampedQuantity x.1 r : ℝ) else -buyDepth x.1.val)
  apply Measurable.iSup
  intro r
  have he : Measurable (fun x : RegimeState upper × ℝ =>
      essentialImpactPrice upper hupper (x.1, r)) :=
    (measurable_essentialImpactPrice upper hupper).comp
      (measurable_fst.prodMk measurable_const)
  have hq : Measurable (fun x : RegimeState upper × ℝ => (clampedQuantity x.1 r : ℝ)) :=
    (measurable_clampedQuantity upper).comp (measurable_fst.prodMk measurable_const)
  have ha : Measurable (fun x : RegimeState upper × ℝ => -buyDepth x.1.val) :=
    (continuous_buyDepth.measurable.comp (measurable_subtype_coe.comp measurable_fst)).neg
  exact hq.ite (measurableSet_le he measurable_snd) ha

/-- The measurable formula is exactly the right endpoint of the current
minimal cell, not an unrelated candidate breakpoint. -/
theorem marketPriceCut_eq_cellSup (upper : ℝ) (hupper : 0 ≤ upper)
    (m : RegimeState upper)
    (R : MinimalRepresentation
      (impactCurve upper hupper m.val m.property.1 m.property.2).essential)
    (i : Fin R.blockCount) :
    marketPriceCut upper hupper (m, R.level i) = SidedCertificate.cellSup R i :=
  PriceCurve.rationalSublevelCut_eq_cellSup R i

def marketLeftCount (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper) : ℕ :=
  leftCount (chosenMinimalRepresentation
    (impactCurve upper hupper m.val m.property.1 m.property.2).essential)

def marketRightCount (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper) : ℕ :=
  rightCount (chosenMinimalRepresentation
    (impactCurve upper hupper m.val m.property.1 m.property.2).essential)

theorem measurable_marketLeftCount (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (marketLeftCount upper hupper) := by
  have he (m : RegimeState upper) : marketLeftCount upper hupper m =
      (impactCurve upper hupper m.val m.property.1 m.property.2).rationalLeftLevels.ncard :=
    ((impactCurve upper hupper m.val m.property.1 m.property.2).rationalLeftLevels_ncard _).symm
  change Measurable (fun m => marketLeftCount upper hupper m)
  simp_rw [he]
  apply measurable_ncard_image
  · apply measurable_set_iff.mpr
    intro r
    apply measurableSet_setOf.mp
    exact measurableSet_lt
      ((measurable_clampedQuantity upper).comp (measurable_id.prodMk measurable_const))
      measurable_const
  · intro r
    change Measurable (fun m : RegimeState upper => essentialImpactPrice upper hupper (m, r))
    exact (measurable_essentialImpactPrice upper hupper).comp
      (measurable_id.prodMk measurable_const)

theorem measurable_marketRightCount (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (marketRightCount upper hupper) := by
  have he (m : RegimeState upper) : marketRightCount upper hupper m =
      (impactCurve upper hupper m.val m.property.1 m.property.2).rationalRightLevels.ncard :=
    ((impactCurve upper hupper m.val m.property.1 m.property.2).rationalRightLevels_ncard _).symm
  change Measurable (fun m => marketRightCount upper hupper m)
  simp_rw [he]
  apply measurable_ncard_image
  · apply measurable_set_iff.mpr
    intro r
    apply measurableSet_setOf.mp
    exact measurableSet_lt measurable_const
      ((measurable_clampedQuantity upper).comp (measurable_id.prodMk measurable_const))
  · intro r
    change Measurable (fun m : RegimeState upper => essentialImpactPrice upper hupper (m, r))
    exact (measurable_essentialImpactPrice upper hupper).comp
      (measurable_id.prodMk measurable_const)

end Thesis.DayAhead.MarketCurve
