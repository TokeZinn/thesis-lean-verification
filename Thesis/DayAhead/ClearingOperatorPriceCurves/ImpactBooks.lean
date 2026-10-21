import Thesis.DayAhead.ClearingOperatorPriceCurves.MarketImpact
import Thesis.Foundations.MarketClearing.SeparationConcat
import Thesis.Foundations.MarketClearing.QuantityPerturbation

/-! # The actual side books after an extreme-price perturbation

These identities use the source's prepended order, separation, and fixed
minimal-price permutations. They retain zero quantities and price ties.
-/

noncomputable section
namespace Thesis.DayAhead.ImpactBooks

open Foundations.MarketRepresentation
open Foundations.MarketActions.Primitive
open Foundations.MarketClearing.Sorting Foundations.MarketClearing.Selection
open Foundations.MarketClearing.SeparationConcat
open Foundations.MarketClearing.QuantityPerturbation
open Foundations.MarketClearing.MidpointPrice
open TuplesBasic TuplesMeasurableSorting
open MarketImpact

def prependOrder (o : LimitOrder) (x : Tuple LimitOrder) : Tuple LimitOrder :=
  concat ⟨1, fun _ => o⟩ x

theorem buyOrders_adjoin_nonneg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : 0 ≤ q) :
    buyOrders (adjoinExtreme upper (m, q)) =
      prependOrder (mkLimitOrder upper ⟨q, hq⟩) (buyOrders m) := by
  change separationComponent OrderSide.buy (concat _ m) = _
  rw [separationComponent_concat]
  have he : extremeOrder upper q = Sigma.mk OrderSide.buy (mkLimitOrder upper ⟨q, hq⟩) := by
    simp [extremeOrder, hq, abs_of_nonneg hq]
  simp only [orderSingleton, he]
  rw [separationComponent_tagged (X := MarketOrderPayload) OrderSide.buy
    ⟨1, fun _ => mkLimitOrder upper ⟨q, hq⟩⟩]
  rfl

theorem sellOrders_adjoin_nonneg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : 0 ≤ q) :
    sellOrders (adjoinExtreme upper (m, q)) = sellOrders m := by
  change separationComponent OrderSide.sell (concat _ m) = _
  rw [separationComponent_concat]
  have he : extremeOrder upper q = Sigma.mk OrderSide.buy (mkLimitOrder upper ⟨q, hq⟩) := by
    simp [extremeOrder, hq, abs_of_nonneg hq]
  simp only [orderSingleton, he]
  rw [separationComponent_other (X := MarketOrderPayload) OrderSide.sell OrderSide.buy
    (by decide) ⟨1, fun _ => mkLimitOrder upper ⟨q, hq⟩⟩, concat_empty_left]
  rfl

theorem sellOrders_adjoin_neg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : q < 0) :
    sellOrders (adjoinExtreme upper (m, q)) =
      prependOrder (mkLimitOrder (-500) ⟨-q, by linarith⟩) (sellOrders m) := by
  change separationComponent OrderSide.sell (concat _ m) = _
  rw [separationComponent_concat]
  have he : extremeOrder upper q =
      Sigma.mk OrderSide.sell (mkLimitOrder (-500) ⟨-q, by linarith⟩) := by
    simp [extremeOrder, not_le.mpr hq, abs_of_neg hq]
  simp only [orderSingleton, he]
  rw [separationComponent_tagged (X := MarketOrderPayload) OrderSide.sell
    ⟨1, fun _ => mkLimitOrder (-500) ⟨-q, by linarith⟩⟩]
  rfl

theorem buyOrders_adjoin_neg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : q < 0) :
    buyOrders (adjoinExtreme upper (m, q)) = buyOrders m := by
  change separationComponent OrderSide.buy (concat _ m) = _
  rw [separationComponent_concat]
  have he : extremeOrder upper q =
      Sigma.mk OrderSide.sell (mkLimitOrder (-500) ⟨-q, by linarith⟩) := by
    simp [extremeOrder, not_le.mpr hq, abs_of_neg hq]
  simp only [orderSingleton, he]
  rw [separationComponent_other (X := MarketOrderPayload) OrderSide.buy OrderSide.sell
    (by decide) ⟨1, fun _ => mkLimitOrder (-500) ⟨-q, by linarith⟩⟩, concat_empty_left]
  rfl

theorem priceTuple_prepend (p : ℝ) (q : Quantity) (x : Tuple LimitOrder) :
    priceTuple (prependOrder (mkLimitOrder p q) x) = concat ⟨1, fun _ => p⟩ (priceTuple x) := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [priceTuple, tupleProjection, prependOrder, concat, Tuple.entry, Tuple.length]
    rfl
  · intro i
    simp [priceTuple, tupleProjection, prependOrder, concat, Tuple.entry, Tuple.length]

theorem quantityTuple_prepend (p : ℝ) (q : Quantity) (x : Tuple LimitOrder) :
    quantityTuple (prependOrder (mkLimitOrder p q) x) =
      concat ⟨1, fun _ => q⟩ (quantityTuple x) := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [quantityTuple, tupleProjection, prependOrder, concat, Tuple.entry, Tuple.length]
    rfl
  · intro i
    simp [quantityTuple, tupleProjection, prependOrder, concat, Tuple.entry, Tuple.length]

theorem buyPriceTuple_adjoin_nonneg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : 0 ≤ q) :
    buyPriceTuple (adjoinExtreme upper (m, q)) =
      concat ⟨1, fun _ => upper⟩ (buyPriceTuple m) := by
  rw [buyPriceTuple, buyOrders_adjoin_nonneg upper m hq, priceTuple_prepend]
  rfl

theorem sellPriceTuple_adjoin_nonneg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : 0 ≤ q) :
    sellPriceTuple (adjoinExtreme upper (m, q)) = sellPriceTuple m := by
  rw [sellPriceTuple, sellOrders_adjoin_nonneg upper m hq]
  rfl

theorem buyQuantityTuple_adjoin_nonneg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : 0 ≤ q) :
    buyQuantityTuple (adjoinExtreme upper (m, q)) =
      concat ⟨1, fun _ => ⟨q, hq⟩⟩ (buyQuantityTuple m) := by
  rw [buyQuantityTuple, buyOrders_adjoin_nonneg upper m hq, quantityTuple_prepend]
  rfl

theorem sellQuantityTuple_adjoin_nonneg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : 0 ≤ q) :
    sellQuantityTuple (adjoinExtreme upper (m, q)) = sellQuantityTuple m := by
  rw [sellQuantityTuple, sellOrders_adjoin_nonneg upper m hq]
  rfl

theorem sellPriceTuple_adjoin_neg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : q < 0) :
    sellPriceTuple (adjoinExtreme upper (m, q)) =
      concat ⟨1, fun _ => (-500)⟩ (sellPriceTuple m) := by
  rw [sellPriceTuple, sellOrders_adjoin_neg upper m hq, priceTuple_prepend]
  rfl

theorem buyPriceTuple_adjoin_neg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : q < 0) :
    buyPriceTuple (adjoinExtreme upper (m, q)) = buyPriceTuple m := by
  rw [buyPriceTuple, buyOrders_adjoin_neg upper m hq]
  rfl

theorem sellQuantityTuple_adjoin_neg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : q < 0) :
    sellQuantityTuple (adjoinExtreme upper (m, q)) =
      concat ⟨1, fun _ => ⟨-q, by linarith⟩⟩ (sellQuantityTuple m) := by
  rw [sellQuantityTuple, sellOrders_adjoin_neg upper m hq, quantityTuple_prepend]
  rfl

theorem buyQuantityTuple_adjoin_neg (upper : ℝ) (m : MarketTuple) {q : ℝ} (hq : q < 0) :
    buyQuantityTuple (adjoinExtreme upper (m, q)) = buyQuantityTuple m := by
  rw [buyQuantityTuple, buyOrders_adjoin_neg upper m hq]
  rfl

/-- Location of the added buy order after the actual common sorting permutation.
Its price remains the ceiling, even if other orders have the same price. -/
theorem positive_sorted_buy_increase (upper : ℝ) (m : MarketTuple) (q δ : Quantity) :
    ∃ (n : ℕ) (a : Fin n → Quantity) (p : Fin n → ℝ) (t : Fin n),
      sortedBuyQuantityTuple (adjoinExtreme upper (m, (q : ℝ))) = ⟨n, a⟩ ∧
      sortedBuyQuantityTuple (adjoinExtreme upper (m, ((q + δ : Quantity) : ℝ))) =
        addAt ⟨n, a⟩ t δ ∧
      sortedBuyPriceTuple (adjoinExtreme upper (m, (q : ℝ))) = ⟨n, p⟩ ∧ p t = upper := by
  simp only [sortedBuyQuantityTuple, sortedBuyPriceTuple,
    buyQuantityTuple_adjoin_nonneg _ _ q.coe_nonneg,
    buyQuantityTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg,
    buyPriceTuple_adjoin_nonneg _ _ q.coe_nonneg,
    buyPriceTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg]
  dsimp only [buyQuantityTuple, buyPriceTuple]
  generalize buyOrders m = x
  rcases x with ⟨n, x⟩
  let π : FinitePermutation (1 + n) :=
    (realMinimalPermutationGE (concat ⟨1, fun _ => upper⟩ (priceTuple ⟨n, x⟩))).2
  let t : Fin (1 + n) := π.symm (Fin.castAdd n (0 : Fin 1))
  have hπ : realMinimalPermutationGE (concat ⟨1, fun _ => upper⟩ (priceTuple ⟨n, x⟩)) =
      ⟨1 + n, π⟩ := rfl
  rw [hπ]
  dsimp only [concat, priceTuple, quantityTuple, tupleProjection, Tuple.length, Tuple.entry]
  simp only [permutationMap_same_length]
  refine ⟨1 + n, fun i => (Fin.append (fun _ : Fin 1 => q)
    (fun i => orderQuantity (x i))) (π i),
    fun i => (Fin.append (fun _ : Fin 1 => upper) (fun i => orderPrice (x i))) (π i),
    t, ?_, ?_, ?_, ?_⟩
  · rfl
  · have h := congrArg (fun y => permutationMap y ⟨1 + n, π⟩)
      (prepend_addAt (quantityTuple ⟨n, x⟩) q δ)
    dsimp only [concat, quantityTuple, tupleProjection, Tuple.length, Tuple.entry] at h
    rw [permutationMap_addAt] at h
    simpa only [permutationMap_same_length] using h
  · rfl
  · change (Fin.append (fun _ : Fin 1 => upper) (fun i : Fin n => orderPrice (x i)))
      (π (π.symm (Fin.castAdd n (0 : Fin 1)))) = upper
    rw [Equiv.apply_symm_apply, Fin.append_left]

theorem negative_sorted_sell_increase (upper : ℝ) (m : MarketTuple) (q δ : Quantity) (hq : 0 < q) :
    ∃ (n : ℕ) (a : Fin n → Quantity) (p : Fin n → ℝ) (t : Fin n),
      sortedSellQuantityTuple (adjoinExtreme upper (m, -(q : ℝ))) = ⟨n, a⟩ ∧
      sortedSellQuantityTuple (adjoinExtreme upper (m, -((q + δ : Quantity) : ℝ))) =
        addAt ⟨n, a⟩ t δ ∧
      sortedSellPriceTuple (adjoinExtreme upper (m, -(q : ℝ))) = ⟨n, p⟩ ∧ p t = -500 := by
  have hq' : -(q : ℝ) < 0 := neg_neg_of_pos hq
  have hqd : -((q + δ : Quantity) : ℝ) < 0 := neg_neg_of_pos (lt_of_lt_of_le hq
    (le_add_of_nonneg_right δ.coe_nonneg))
  simp only [sortedSellQuantityTuple, sortedSellPriceTuple,
    sellQuantityTuple_adjoin_neg _ _ hq', sellQuantityTuple_adjoin_neg _ _ hqd,
    sellPriceTuple_adjoin_neg _ _ hq', sellPriceTuple_adjoin_neg _ _ hqd, neg_neg]
  dsimp only [sellQuantityTuple, sellPriceTuple]
  generalize sellOrders m = x
  rcases x with ⟨n, x⟩
  let π : FinitePermutation (1 + n) :=
    (realMinimalPermutationLE (concat ⟨1, fun _ => (-500 : ℝ)⟩ (priceTuple ⟨n, x⟩))).2
  let t : Fin (1 + n) := π.symm (Fin.castAdd n (0 : Fin 1))
  have hπ : realMinimalPermutationLE (concat ⟨1, fun _ => (-500 : ℝ)⟩ (priceTuple ⟨n, x⟩)) =
      ⟨1 + n, π⟩ := rfl
  rw [hπ]
  dsimp only [concat, priceTuple, quantityTuple, tupleProjection, Tuple.length, Tuple.entry]
  simp only [permutationMap_same_length]
  refine ⟨1 + n, fun i => (Fin.append (fun _ : Fin 1 => q)
    (fun i => orderQuantity (x i))) (π i),
    fun i => (Fin.append (fun _ : Fin 1 => (-500 : ℝ)) (fun i => orderPrice (x i))) (π i),
    t, ?_, ?_, ?_, ?_⟩
  · rfl
  · have h := congrArg (fun y => permutationMap y ⟨1 + n, π⟩)
      (prepend_addAt (quantityTuple ⟨n, x⟩) q δ)
    dsimp only [concat, quantityTuple, tupleProjection, Tuple.length, Tuple.entry] at h
    rw [permutationMap_addAt] at h
    simpa only [permutationMap_same_length] using h
  · rfl
  · change (Fin.append (fun _ : Fin 1 => (-500 : ℝ)) (fun i : Fin n => orderPrice (x i)))
      (π (π.symm (Fin.castAdd n (0 : Fin 1)))) = -500
    rw [Equiv.apply_symm_apply, Fin.append_left]

end Thesis.DayAhead.ImpactBooks
