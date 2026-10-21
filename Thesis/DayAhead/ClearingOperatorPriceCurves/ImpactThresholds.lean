import Thesis.DayAhead.ClearingOperatorPriceCurves.ImpactBaseline
import Thesis.Foundations.MarketClearing.ThresholdMarginals

/-! # The raw market's marginal prices and cumulative price cuts -/

noncomputable section
namespace Thesis.DayAhead.ImpactThresholds

open Foundations.MarketRepresentation TuplesBasic TuplesMeasurableSorting TuplesSorting
open Foundations.MarketClearing.Sorting Foundations.MarketClearing.Equilibrium
open Foundations.MarketClearing.MidpointPrice Foundations.MarketClearing.Selection
open Foundations.MarketClearing.ThresholdClearing Foundations.MarketClearing.ThresholdMarginals
open MarketImpact ImpactBooks ImpactBaseline

def sellMarginal (m : MarketTuple) : ℝ :=
  marginalPrice ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m),
    marketEquilibriumQuantity m)

def buyMarginal (m : MarketTuple) : ℝ :=
  marginalPrice ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m),
    marketEquilibriumQuantity m)

def sideBelow (s : Tuple LimitOrder) (r : ℝ) : Quantity :=
  below (fun i => orderPrice (s.2 i)) (fun i => orderQuantity (s.2 i)) r

def sideAbove (b : Tuple LimitOrder) (r : ℝ) : Quantity :=
  above (fun i => orderPrice (b.2 i)) (fun i => orderQuantity (b.2 i)) r

def sellCut (m : MarketTuple) (r : ℝ) : Quantity := sideBelow (sellOrders m) r
def buyCut (m : MarketTuple) (r : ℝ) : Quantity := sideAbove (buyOrders m) r

theorem sellMarginal_le_iff (m : MarketTuple) (hm : m ∈ positiveStates) (r : ℝ) :
    sellMarginal m ≤ r ↔ marketEquilibriumQuantity m ≤ sellCut m r := by
  obtain ⟨i, _, hi, _, _, _, _, _, _⟩ := marketMidpointPrice_positive_formula m hm
  have hs := realMinimalPermutationLE_sorts (sellPriceTuple m)
  dsimp only [sellMarginal, sellCut, sideBelow]
  generalize marketEquilibriumQuantity m = v at hi ⊢
  dsimp only [cumulativeSellQuantityTuple, sortedSellQuantityTuple, sortedSellPriceTuple,
    sellQuantityTuple, sellPriceTuple] at hi hs ⊢
  generalize sellOrders m = s at hi hs ⊢
  rcases s with ⟨n, s⟩
  dsimp only [priceTuple, quantityTuple, tupleProjection, Tuple.length, Tuple.entry,
    realMinimalPermutationLE] at hi hs ⊢
  simp only [permutationMap, Tuple.length, dite_true] at hi hs ⊢
  dsimp only [permute, Tuple.length, Tuple.entry] at hi hs ⊢
  have hmono : Monotone (β := ℝ) (fun i : Fin n =>
      (s (minimumSortPermutation (X := ℝ) ⟨n, fun i => s i OrderField.price⟩ i)
        OrderField.price : ℝ)) :=
    (isSorted_iff_monotone _).mp hs
  have h := marginal_le_iff_below _ _ hmono v hi r
  have he := below_permutation (fun i => s i OrderField.price) (fun i => s i OrderField.quantity)
    (minimumSortPermutation (X := ℝ) ⟨n, fun i => s i OrderField.price⟩) r
  exact he ▸ h

theorem le_buyMarginal_iff (m : MarketTuple) (hm : m ∈ positiveStates) (r : ℝ) :
    r ≤ buyMarginal m ↔ marketEquilibriumQuantity m ≤ buyCut m r := by
  obtain ⟨_, i, _, hi, _, _, _, _, _⟩ := marketMidpointPrice_positive_formula m hm
  have hb := realMinimalPermutationGE_sorts_dual (buyPriceTuple m)
  dsimp only [buyMarginal, buyCut, sideAbove]
  generalize marketEquilibriumQuantity m = v at hi ⊢
  dsimp only [cumulativeBuyQuantityTuple, sortedBuyQuantityTuple, sortedBuyPriceTuple,
    buyQuantityTuple, buyPriceTuple] at hi hb ⊢
  generalize buyOrders m = b at hi hb ⊢
  rcases b with ⟨n, b⟩
  dsimp only [priceTuple, quantityTuple, tupleProjection, Tuple.length, Tuple.entry,
    realMinimalPermutationGE, dualizeRealTuple] at hi hb ⊢
  simp only [permutationMap, Tuple.length, dite_true] at hi hb ⊢
  dsimp only [permute, Tuple.length, Tuple.entry] at hi hb ⊢
  have hanti : Antitone (β := ℝ) (fun i : Fin n => (b
      (minimumSortPermutation (X := OrderDual ℝ)
        ⟨n, fun i => OrderDual.toDual (b i OrderField.price)⟩ i)
      OrderField.price : ℝ)) := (isSorted_iff_monotone _).mp hb
  have h := le_marginal_iff_above _ _ hanti v hi r
  have he := above_permutation (fun i => b i OrderField.price) (fun i => b i OrderField.quantity)
    (minimumSortPermutation (X := OrderDual ℝ)
      ⟨n, fun i => OrderDual.toDual (b i OrderField.price)⟩) r
  exact he ▸ h

theorem sellCut_adjoin_nonneg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : 0 ≤ q) (r : ℝ) :
    sellCut (adjoinExtreme upper (m, q)) r = sellCut m r := by
  simp only [sellCut, sellOrders_adjoin_nonneg _ _ hq]

theorem buyCut_adjoin_nonneg (upper : ℝ) (m : MarketTuple) (q : Quantity) (r : ℝ) :
    buyCut (adjoinExtreme upper (m, (q : ℝ))) r =
      (if r ≤ upper then q else 0) + buyCut m r := by
  simp only [buyCut, buyOrders_adjoin_nonneg _ _ q.coe_nonneg]
  dsimp only [sideAbove, prependOrder, Foundations.MarketActions.Primitive.concat,
    Tuple.length, Tuple.entry]
  rw [map_append orderPrice, map_append orderQuantity]
  exact above_prepend _ _ upper r q

theorem buyCut_adjoin_neg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : q < 0) (r : ℝ) :
    buyCut (adjoinExtreme upper (m, q)) r = buyCut m r := by
  simp only [buyCut, buyOrders_adjoin_neg _ _ hq]

theorem sellCut_adjoin_neg (upper : ℝ) (m : MarketTuple) (q : Quantity) (hq : 0 < q) (r : ℝ) :
    sellCut (adjoinExtreme upper (m, -(q : ℝ))) r =
      (if -500 ≤ r then q else 0) + sellCut m r := by
  have hq' : -(q : ℝ) < 0 := neg_neg_of_pos hq
  simp only [sellCut, sellOrders_adjoin_neg _ _ hq']
  dsimp only [sideBelow, prependOrder, Foundations.MarketActions.Primitive.concat,
    Tuple.length, Tuple.entry]
  rw [map_append orderPrice, map_append orderQuantity]
  simp only [neg_neg]
  exact below_prepend _ _ (-500) r q

theorem sellMarginal_mem_bounds (upper : ℝ) (m : MarketTuple)
    (hm : m ∈ positiveStates) (hp : priceBounded upper m) :
    sellMarginal m ∈ Set.Icc (-500) upper := by
  obtain ⟨i, _, hi, _, _, _, hip, _, _⟩ := marketMidpointPrice_positive_formula m hm
  have h := (sortedPrice_all (fun p => p ∈ Set.Icc (-500) upper) m hp).1 ⟨i, hip⟩
  change i < (sortedSellPriceTuple m).1 at hip
  rw [sellMarginal, marginalPrice_eq hi, tuplePriceEval, dif_pos hip]
  exact h

theorem buyMarginal_mem_bounds (upper : ℝ) (m : MarketTuple)
    (hm : m ∈ positiveStates) (hp : priceBounded upper m) :
    buyMarginal m ∈ Set.Icc (-500) upper := by
  obtain ⟨_, i, _, hi, _, _, _, hip, _⟩ := marketMidpointPrice_positive_formula m hm
  have h := (sortedPrice_all (fun p => p ∈ Set.Icc (-500) upper) m hp).2 ⟨i, hip⟩
  change i < (sortedBuyPriceTuple m).1 at hip
  rw [buyMarginal, marginalPrice_eq hi, tuplePriceEval, dif_pos hip]
  exact h

theorem bookVolume_prepend_sell_le (s b : Tuple LimitOrder) (p : ℝ) (q : Quantity) :
    bookVolume (prependOrder (mkLimitOrder p q) s) b ≤ bookVolume s b + q := by
  dsimp only [bookVolume, prependOrder, Foundations.MarketActions.Primitive.concat,
    Tuple.length, Tuple.entry]
  rw [map_append orderPrice, map_append orderQuantity]
  exact thresholdVolume_prepend_sell_le _ _ _ _ p q

theorem negative_volume_le_baseline_add (upper : ℝ) (m : MarketTuple) (q : Quantity)
    (hq : 0 < q) : marketEquilibriumQuantity (adjoinExtreme upper (m, -(q : ℝ))) ≤
      marketEquilibriumQuantity m + q := by
  have hq' : -(q : ℝ) < 0 := neg_neg_of_pos hq
  rw [marketEquilibriumQuantity_eq_bookVolume, marketEquilibriumQuantity_eq_bookVolume,
    sellOrders_adjoin_neg _ _ hq', buyOrders_adjoin_neg _ _ hq']
  simp only [neg_neg]
  exact bookVolume_prepend_sell_le _ _ _ q

end Thesis.DayAhead.ImpactThresholds
