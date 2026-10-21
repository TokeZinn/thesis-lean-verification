import Thesis.DayAhead.ClearingOperatorPriceCurves.MarketCurveMeasurability
import Thesis.Foundations.Stochastic.MeasurableOrderedValues

/-! # Measurable actual essential price levels and sided quantity knots -/

noncomputable section
namespace Thesis.DayAhead.MarketCurve

open Set MeasureTheory
open Foundations.MarketClearing.Sorting
open Foundations.Stochastic.MeasurableDistinctCounts
open MarketImpact PriceCurves SidedCertificate

local instance : MeasurableSpace MarketTuple := borel _
local instance : BorelSpace MarketTuple := ⟨rfl⟩

def marketLeftLevel (upper : ℝ) (hupper : 0 ≤ upper) (j : ℕ) (m : RegimeState upper) : ℝ :=
  orderedValue upper {r : ℚ | (clampedQuantity m r : ℝ) < 0}
    (fun r => essentialImpactPrice upper hupper (m, r)) j

def marketRightLevel (upper : ℝ) (hupper : 0 ≤ upper) (j : ℕ) (m : RegimeState upper) : ℝ :=
  orderedValue upper {r : ℚ | 0 < (clampedQuantity m r : ℝ)}
    (fun r => essentialImpactPrice upper hupper (m, r)) j

theorem measurable_marketLeftLevel (upper : ℝ) (hupper : 0 ≤ upper) (j : ℕ) :
    Measurable (marketLeftLevel upper hupper j) := by
  apply measurable_orderedValue
  · apply measurable_set_iff.mpr
    intro r
    exact measurableSet_setOf.mp (measurableSet_lt
      ((measurable_clampedQuantity upper).comp (measurable_id.prodMk measurable_const))
      measurable_const)
  · intro r
    exact (measurable_essentialImpactPrice upper hupper).comp
      (measurable_id.prodMk measurable_const)

theorem measurable_marketRightLevel (upper : ℝ) (hupper : 0 ≤ upper) (j : ℕ) :
    Measurable (marketRightLevel upper hupper j) := by
  apply measurable_orderedValue
  · apply measurable_set_iff.mpr
    intro r
    exact measurableSet_setOf.mp (measurableSet_lt measurable_const
      ((measurable_clampedQuantity upper).comp (measurable_id.prodMk measurable_const)))
  · intro r
    exact (measurable_essentialImpactPrice upper hupper).comp
      (measurable_id.prodMk measurable_const)

theorem marketLeftLevel_eq (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper)
    (j : Fin (marketLeftCount upper hupper m)) :
    marketLeftLevel upper hupper j.val m =
      let R := chosenMinimalRepresentation
        (impactCurve upper hupper m.val m.property.1 m.property.2).essential
      R.level (leftCell R j) := by
  let f := impactCurve upper hupper m.val m.property.1 m.property.2
  let R := chosenMinimalRepresentation f.essential
  apply orderedValue_eq (fun j => R.level (leftCell R j))
    (R.level_strictMono.comp (leftCell R).strictMono)
  · exact f.rationalLeftLevels_range R
  · intro r _
    exact (essential_impactCurve_price_bounds upper hupper m (clampedQuantity m r)).2

theorem marketRightLevel_eq (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper)
    (j : Fin (marketRightCount upper hupper m)) :
    marketRightLevel upper hupper j.val m =
      let R := chosenMinimalRepresentation
        (impactCurve upper hupper m.val m.property.1 m.property.2).essential
      R.level (rightCell R j) := by
  let f := impactCurve upper hupper m.val m.property.1 m.property.2
  let R := chosenMinimalRepresentation f.essential
  apply orderedValue_eq (fun j => R.level (rightCell R j))
    (R.level_strictMono.comp (rightCell R).strictMono)
  · exact f.rationalRightLevels_range R
  · intro r _
    exact (essential_impactCurve_price_bounds upper hupper m (clampedQuantity m r)).2

def marketLeftKnot (upper : ℝ) (hupper : 0 ≤ upper) (j : ℕ) (m : RegimeState upper) : ℝ :=
  if j = 0 then -buyDepth m.val
    else min 0 (marketPriceCut upper hupper (m, marketLeftLevel upper hupper (j - 1) m))

def marketRightKnot (upper : ℝ) (hupper : 0 ≤ upper) (j : ℕ) (m : RegimeState upper) : ℝ :=
  if j = 0 then 0
    else max 0 (marketPriceCut upper hupper (m, marketRightLevel upper hupper (j - 1) m))

theorem measurable_marketLeftKnot (upper : ℝ) (hupper : 0 ≤ upper) (j : ℕ) :
    Measurable (marketLeftKnot upper hupper j) := by
  unfold marketLeftKnot
  split_ifs
  · exact (continuous_buyDepth.measurable.comp measurable_subtype_coe).neg
  · exact measurable_const.min ((measurable_marketPriceCut upper hupper).comp
      (measurable_id.prodMk (measurable_marketLeftLevel upper hupper (j - 1))))

theorem measurable_marketRightKnot (upper : ℝ) (hupper : 0 ≤ upper) (j : ℕ) :
    Measurable (marketRightKnot upper hupper j) := by
  unfold marketRightKnot
  split_ifs
  · exact measurable_const
  · exact measurable_const.max ((measurable_marketPriceCut upper hupper).comp
      (measurable_id.prodMk (measurable_marketRightLevel upper hupper (j - 1))))

theorem marketLeftKnot_eq (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper)
    (j : Fin (marketLeftCount upper hupper m + 1)) :
    marketLeftKnot upper hupper j.val m =
      canonicalLeftKnot (chosenMinimalRepresentation
        (impactCurve upper hupper m.val m.property.1 m.property.2).essential) j := by
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    simp only [marketLeftKnot, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      if_false, Nat.add_sub_cancel]
    rw [marketLeftLevel_eq upper hupper m j, marketPriceCut_eq_cellSup]
    rfl

theorem marketRightKnot_eq (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper)
    (j : Fin (marketRightCount upper hupper m + 1)) :
    marketRightKnot upper hupper j.val m =
      canonicalRightKnot (chosenMinimalRepresentation
        (impactCurve upper hupper m.val m.property.1 m.property.2).essential) j := by
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    simp only [marketRightKnot, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      if_false, Nat.add_sub_cancel]
    rw [marketRightLevel_eq upper hupper m j, marketPriceCut_eq_cellSup]
    rfl

end Thesis.DayAhead.MarketCurve
