import Thesis.DayAhead.ClearingOperatorPriceCurves.ImpactMonotonicity
import Thesis.Foundations.MarketClearing.ThresholdClearing

/-! # Baseline volume and positivity of the actual extreme-order market -/

noncomputable section
namespace Thesis.DayAhead.ImpactBaseline

open Foundations.MarketRepresentation TuplesBasic TuplesSorting TuplesMeasurableSorting
open Foundations.MarketClearing.Sorting Foundations.MarketClearing.Equilibrium
open Foundations.MarketClearing.ThresholdClearing Foundations.MarketClearing.Selection
open MarketImpact ImpactBooks ImpactClearing ImpactMonotonicity

def bookVolume (s b : Tuple LimitOrder) : Quantity :=
  thresholdVolume (fun i => orderPrice (s.2 i)) (fun i => orderQuantity (s.2 i))
    (fun i => orderPrice (b.2 i)) (fun i => orderQuantity (b.2 i))

theorem marketEquilibriumQuantity_eq_bookVolume (m : MarketTuple) :
    marketEquilibriumQuantity m = bookVolume (sellOrders m) (buyOrders m) := by
  have hs := realMinimalPermutationLE_sorts (sellPriceTuple m)
  have hb := realMinimalPermutationGE_sorts_dual (buyPriceTuple m)
  dsimp only [marketEquilibriumQuantity, cumulativeSellQuantityTuple, cumulativeBuyQuantityTuple,
    sortedSellQuantityTuple, sortedBuyQuantityTuple, sortedSellPriceTuple, sortedBuyPriceTuple,
    sellPriceTuple, buyPriceTuple, sellQuantityTuple, buyQuantityTuple] at hs hb ⊢
  generalize sellOrders m = s at hs ⊢
  generalize buyOrders m = b at hb ⊢
  rcases s with ⟨n, s⟩
  rcases b with ⟨k, b⟩
  dsimp only [priceTuple, quantityTuple, tupleProjection, Tuple.length, Tuple.entry,
    realMinimalPermutationLE, realMinimalPermutationGE, dualizeRealTuple] at hs hb ⊢
  simp only [permutationMap, Tuple.length, dite_true] at hs hb ⊢
  dsimp only [permute, Tuple.length, Tuple.entry] at hs hb ⊢
  rw [equilibrium_eq_thresholdVolume]
  · exact thresholdVolume_permutation (fun i => s i OrderField.price)
      (fun i => s i OrderField.quantity) (fun i => b i OrderField.price)
      (fun i => b i OrderField.quantity) _ _
  · exact (isSorted_iff_monotone _).mp hs
  · exact (isSorted_iff_monotone _).mp hb

theorem map_append {X Y : Type*} {n k : ℕ} (f : X → Y) (a : Fin n → X) (b : Fin k → X) :
    (fun i => f (Fin.append a b i)) = Fin.append (fun i => f (a i)) (fun i => f (b i)) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro i <;> simp only [Fin.append_left, Fin.append_right]

theorem bookVolume_le_prepend_buy (s b : Tuple LimitOrder) (p : ℝ) (q : Quantity) :
    bookVolume s b ≤ bookVolume s (prependOrder (mkLimitOrder p q) b) := by
  dsimp only [bookVolume, prependOrder, Foundations.MarketActions.Primitive.concat,
    Tuple.length, Tuple.entry]
  rw [map_append orderPrice, map_append orderQuantity]
  exact thresholdVolume_le_prepend_buy _ _ _ _ p q

theorem bookVolume_le_prepend_sell (s b : Tuple LimitOrder) (p : ℝ) (q : Quantity) :
    bookVolume s b ≤ bookVolume (prependOrder (mkLimitOrder p q) s) b := by
  dsimp only [bookVolume, prependOrder, Foundations.MarketActions.Primitive.concat,
    Tuple.length, Tuple.entry]
  rw [map_append orderPrice, map_append orderQuantity]
  exact thresholdVolume_le_prepend_sell _ _ _ _ p q

theorem bookVolume_prepend_zero_buy (s b : Tuple LimitOrder) (p : ℝ) :
    bookVolume s (prependOrder (mkLimitOrder p 0) b) = bookVolume s b := by
  dsimp only [bookVolume, prependOrder, Foundations.MarketActions.Primitive.concat,
    Tuple.length, Tuple.entry]
  rw [map_append orderPrice, map_append orderQuantity]
  exact thresholdVolume_prepend_zero_buy _ _ _ _ p

theorem bookVolume_prepend_zero_sell (s b : Tuple LimitOrder) (p : ℝ) :
    bookVolume (prependOrder (mkLimitOrder p 0) s) b = bookVolume s b := by
  dsimp only [bookVolume, prependOrder, Foundations.MarketActions.Primitive.concat,
    Tuple.length, Tuple.entry]
  rw [map_append orderPrice, map_append orderQuantity]
  exact thresholdVolume_prepend_zero_sell _ _ _ _ p

theorem market_volume_le_perturbed (upper : ℝ) (m : MarketTuple) (q : ℝ) :
    marketEquilibriumQuantity m ≤ marketEquilibriumQuantity (adjoinExtreme upper (m, q)) := by
  rw [marketEquilibriumQuantity_eq_bookVolume, marketEquilibriumQuantity_eq_bookVolume]
  by_cases hq : 0 ≤ q
  · rw [sellOrders_adjoin_nonneg _ _ hq, buyOrders_adjoin_nonneg _ _ hq]
    exact bookVolume_le_prepend_buy _ _ _ _
  · have hq' := lt_of_not_ge hq
    rw [sellOrders_adjoin_neg _ _ hq', buyOrders_adjoin_neg _ _ hq']
    exact bookVolume_le_prepend_sell _ _ _ _

theorem market_volume_zero_perturbation (upper : ℝ) (m : MarketTuple) :
    marketEquilibriumQuantity (adjoinExtreme upper (m, 0)) = marketEquilibriumQuantity m := by
  rw [marketEquilibriumQuantity_eq_bookVolume, marketEquilibriumQuantity_eq_bookVolume,
    sellOrders_adjoin_nonneg _ _ (le_refl 0), buyOrders_adjoin_nonneg _ _ (le_refl 0)]
  exact bookVolume_prepend_zero_buy _ _ _

theorem perturbation_positive (upper : ℝ) (m : MarketTuple) (hm : m ∈ positiveStates) (q : ℝ) :
    0 < marketEquilibriumQuantity (adjoinExtreme upper (m, q)) :=
  hm.trans_le (market_volume_le_perturbed upper m q)

theorem impactPrice_nonneg_mono_of_positive_state (upper : ℝ) (hupper : 0 ≤ upper)
    (m : MarketTuple) (hprice : priceBounded upper m) (hm : m ∈ positiveStates)
    {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) : impactPrice upper (m, q) ≤ impactPrice upper (m, r) :=
  impactPrice_nonneg_mono upper hupper m hprice (q := ⟨q, hq⟩) (r := ⟨r, hq.trans hqr⟩) hqr
    (perturbation_positive upper m hm q)

theorem impactPrice_neg_mono_of_positive_state (upper : ℝ) (hupper : 0 ≤ upper)
    (m : MarketTuple) (hprice : priceBounded upper m) (hm : m ∈ positiveStates)
    {q r : ℝ} (hqr : q ≤ r) (hr : r < 0) : impactPrice upper (m, q) ≤ impactPrice upper (m, r) := by
  have hq : q < 0 := hqr.trans_lt hr
  have hpos : (0 : Quantity) < ⟨-r, neg_nonneg.mpr hr.le⟩ :=
    show (0 : ℝ) < -r from neg_pos.mpr hr
  have hcomp : (⟨-r, neg_nonneg.mpr hr.le⟩ : Quantity) ≤ ⟨-q, neg_nonneg.mpr hq.le⟩ :=
    show -r ≤ -q from neg_le_neg hqr
  have hv : 0 < negativeVolume upper m ⟨-r, neg_nonneg.mpr hr.le⟩ := by
    change 0 < marketEquilibriumQuantity (adjoinExtreme upper (m, -(-r)))
    rw [neg_neg]
    exact perturbation_positive upper m hm r
  have h := impactPrice_neg_mono upper hupper m hprice
    (q := ⟨-r, neg_nonneg.mpr hr.le⟩) (r := ⟨-q, neg_nonneg.mpr hq.le⟩)
    hpos hcomp hv
  change impactPrice upper (m, -(-q)) ≤ impactPrice upper (m, -(-r)) at h
  simpa only [neg_neg] using h

end Thesis.DayAhead.ImpactBaseline
