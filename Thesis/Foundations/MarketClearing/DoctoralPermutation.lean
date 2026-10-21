import Thesis.Foundations.MarketClearing.DoctoralResults
import Thesis.Foundations.MarketClearing.SeparationAlgebra

/-! # Raw-book price-cut invariants, including separation multiplicities -/

noncomputable section
namespace Thesis.Foundations.MarketClearing.DoctoralPermutation

open MarketRepresentation TuplesBasic TuplesSorting MarketActions.Primitive Selection Sorting
open FiniteSets ThresholdClearing ThresholdMarginals MidpointPrice Equilibrium DoctoralResults

def sideIndex (a : OrderSide) (m : MarketTuple)
    (i : Fin (separationComponent a m).1) : Fin m.1 :=
  ⟨(pairing (separationIndexSet a m)).2 i,
    ((mem_separationIndexSet a m).mp (pairing_entry_mem _ i)).1⟩

theorem sideIndex_tag (a : OrderSide) (m : MarketTuple) (i : Fin (separationComponent a m).1) :
    (m.2 (sideIndex a m i)).1 = a :=
  ((mem_separationIndexSet a m).mp (pairing_entry_mem _ i)).2

theorem sideIndex_injective (a : OrderSide) (m : MarketTuple) :
    Function.Injective (sideIndex a m) := by
  intro i j h
  have hval := congrArg Fin.val h
  exact (FiniteSubsets.toFinset (separationIndexSet a m)).orderEmbOfFin rfl |>.injective hval

theorem sideIndex_surjective (a : OrderSide) (m : MarketTuple) (k : Fin m.1)
    (hk : (m.2 k).1 = a) : ∃ i, sideIndex a m i = k := by
  obtain ⟨i, hi⟩ := exists_pairing_entry_eq_of_mem (separationIndexSet a m)
    ((mem_separationIndexSet a m).mpr ⟨k.isLt, hk⟩)
  exact ⟨i, Fin.ext hi⟩

theorem separation_entry (a : OrderSide) (m : MarketTuple)
    (i : Fin (separationComponent a m).1) :
    (separationComponent a m).2 i = (m.2 (sideIndex a m i)).2 := by
  change valueAtTag a (m.2 (sideIndex a m i)) _ = _
  have hval (z : MarketOrder) (h : z.1 = a) : valueAtTag a z h = z.2 := by
    rcases z with ⟨b, x⟩
    cases h
    rfl
  exact hval _ _

/-- Separation preserves every tag-filtered sum, with repeated entries counted
at their distinct original indices. -/
theorem sum_separation (a : OrderSide) (m : MarketTuple) (f : LimitOrder → Quantity) :
    (∑ i, f ((separationComponent a m).2 i)) =
      ∑ k, if (m.2 k).1 = a then f (m.2 k).2 else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ ↦ sideIndex a m i)
  · intro i _
    simp [sideIndex_tag]
  · intro i _ j _ hij
    exact sideIndex_injective a m hij
  · intro k hk
    obtain ⟨i, hi⟩ := sideIndex_surjective a m k (Finset.mem_filter.mp hk).2
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro i _
    rw [separation_entry]

def rawSupply (m : MarketTuple) (r : ℝ) : Quantity :=
  ∑ k, if (m.2 k).1 = OrderSide.sell ∧ orderPrice (m.2 k).2 ≤ r then
    orderQuantity (m.2 k).2 else 0

def rawDemand (m : MarketTuple) (r : ℝ) : Quantity :=
  ∑ k, if (m.2 k).1 = OrderSide.buy ∧ r ≤ orderPrice (m.2 k).2 then
    orderQuantity (m.2 k).2 else 0

theorem rawSupply_permute (m : MarketTuple) (π : FinitePermutation m.1) :
    rawSupply (permute m π) = rawSupply m := by
  funext r
  unfold rawSupply
  exact Equiv.sum_comp π (fun k ↦ if (m.2 k).1 = OrderSide.sell ∧
    orderPrice (m.2 k).2 ≤ r then orderQuantity (m.2 k).2 else 0)

theorem rawDemand_permute (m : MarketTuple) (π : FinitePermutation m.1) :
    rawDemand (permute m π) = rawDemand m := by
  funext r
  unfold rawDemand
  exact Equiv.sum_comp π (fun k ↦ if (m.2 k).1 = OrderSide.buy ∧
    r ≤ orderPrice (m.2 k).2 then orderQuantity (m.2 k).2 else 0)

theorem below_separated (m : MarketTuple) (r : ℝ) :
    below (fun i ↦ orderPrice ((sellOrders m).2 i))
      (fun i ↦ orderQuantity ((sellOrders m).2 i)) r = rawSupply m r := by
  classical
  change (∑ i, (fun o : LimitOrder ↦ if orderPrice o ≤ r then orderQuantity o else 0)
    ((separationComponent OrderSide.sell m).2 i)) = _
  rw [sum_separation OrderSide.sell m (fun o ↦ if orderPrice o ≤ r then orderQuantity o else 0)]
  unfold rawSupply
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

theorem above_separated (m : MarketTuple) (r : ℝ) :
    above (fun i ↦ orderPrice ((buyOrders m).2 i))
      (fun i ↦ orderQuantity ((buyOrders m).2 i)) r = rawDemand m r := by
  classical
  change (∑ i, (fun o : LimitOrder ↦ if r ≤ orderPrice o then orderQuantity o else 0)
    ((separationComponent OrderSide.buy m).2 i)) = _
  rw [sum_separation OrderSide.buy m (fun o ↦ if r ≤ orderPrice o then orderQuantity o else 0)]
  unfold rawDemand
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

def sellPermutation (m : MarketTuple) : FinitePermutation (sellOrders m).1 :=
  minimumSortPermutation (priceTuple (sellOrders m))

def buyPermutation (m : MarketTuple) : FinitePermutation (buyOrders m).1 :=
  minimumSortPermutation (X := OrderDual ℝ) (dualizeRealTuple (priceTuple (buyOrders m)))

def sellPrices (m : MarketTuple) : Fin (sellOrders m).1 → ℝ :=
  fun i ↦ orderPrice ((sellOrders m).2 (sellPermutation m i))

def sellQuantities (m : MarketTuple) : Fin (sellOrders m).1 → Quantity :=
  fun i ↦ orderQuantity ((sellOrders m).2 (sellPermutation m i))

def buyPrices (m : MarketTuple) : Fin (buyOrders m).1 → ℝ :=
  fun i ↦ orderPrice ((buyOrders m).2 (buyPermutation m i))

def buyQuantities (m : MarketTuple) : Fin (buyOrders m).1 → Quantity :=
  fun i ↦ orderQuantity ((buyOrders m).2 (buyPermutation m i))

def sellState (m : MarketTuple) : Tuple Quantity × Tuple ℝ :=
  (cumulativeQuantityTuple ⟨(sellOrders m).1, sellQuantities m⟩,
    ⟨(sellOrders m).1, sellPrices m⟩)

def buyState (m : MarketTuple) : Tuple Quantity × Tuple ℝ :=
  (cumulativeQuantityTuple ⟨(buyOrders m).1, buyQuantities m⟩,
    ⟨(buyOrders m).1, buyPrices m⟩)

theorem sellState_eq (m : MarketTuple) :
    sellState m = (cumulativeSellQuantityTuple m, sortedSellPriceTuple m) := by
  unfold sellState sellQuantities sellPrices sellPermutation
  simp only [cumulativeSellQuantityTuple,
    sortedSellQuantityTuple, sortedSellPriceTuple, sellQuantityTuple, sellPriceTuple,
    realMinimalPermutationLE, TuplesMeasurableSorting.permutationMap,
    priceTuple, quantityTuple, tupleProjection, permute, orderPrice, orderQuantity,
    Tuple.length, Tuple.entry]
  rfl

theorem buyState_eq (m : MarketTuple) :
    buyState m = (cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m) := by
  unfold buyState buyQuantities buyPrices buyPermutation
  simp only [cumulativeBuyQuantityTuple,
    sortedBuyQuantityTuple, sortedBuyPriceTuple, buyQuantityTuple, buyPriceTuple,
    realMinimalPermutationGE, TuplesMeasurableSorting.permutationMap,
    priceTuple, quantityTuple, tupleProjection, permute, orderPrice, orderQuantity,
    Tuple.length, Tuple.entry]
  rfl

theorem sellPrices_monotone (m : MarketTuple) : Monotone (sellPrices m) := by
  have h := minimumSort_isSorted (priceTuple (sellOrders m))
  rw [minimumSort_eq_permute_minimumSortPermutation] at h
  rw [isSorted_iff_monotone] at h
  exact h

theorem buyPrices_antitone (m : MarketTuple) : Antitone (buyPrices m) := by
  have h := minimumSort_isSorted (X := OrderDual ℝ)
    (dualizeRealTuple (priceTuple (buyOrders m)))
  rw [minimumSort_eq_permute_minimumSortPermutation] at h
  rw [isSorted_iff_monotone] at h
  exact h

theorem below_sorted (m : MarketTuple) (r : ℝ) :
    below (sellPrices m) (sellQuantities m) r = rawSupply m r := by
  unfold sellPrices sellQuantities
  rw [below_permutation (fun i ↦ orderPrice ((sellOrders m).2 i))
    (fun i ↦ orderQuantity ((sellOrders m).2 i)) (sellPermutation m)]
  exact below_separated m r

theorem above_sorted (m : MarketTuple) (r : ℝ) :
    above (buyPrices m) (buyQuantities m) r = rawDemand m r := by
  unfold buyPrices buyQuantities
  rw [above_permutation (fun i ↦ orderPrice ((buyOrders m).2 i))
    (fun i ↦ orderQuantity ((buyOrders m).2 i)) (buyPermutation m)]
  exact above_separated m r

/-- The literal raw-book pipeline has the price-cut characterization, after
the actual separation and common sorting permutations. -/
theorem marketVolume_greatest (m : MarketTuple) :
    IsGreatest (Set.range (fun r ↦ min (rawSupply m r) (rawDemand m r)))
      (marketEquilibriumQuantity m) := by
  have h := executableVolume_uniformPrice (sellPrices m) (sellQuantities m)
    (buyPrices m) (buyQuantities m) (sellPrices_monotone m) (buyPrices_antitone m)
  change IsGreatest _ (equilibriumQuantity (sellState m, buyState m)) at h
  simpa only [below_sorted, above_sorted, sellState_eq, buyState_eq,
    marketEquilibriumQuantity] using h

/-- Original label: `lem:state-functionals-permutation-invariant`.
Maximum executable volume of the actual tagged-book pipeline is invariant
under every full-book permutation, including repeated orders and zero size. -/
theorem marketVolume_permute (m : MarketTuple) (π : FinitePermutation m.1) :
    marketEquilibriumQuantity (permute m π) = marketEquilibriumQuantity m := by
  have h := marketVolume_greatest (permute m π)
  rw [rawSupply_permute, rawDemand_permute] at h
  exact h.unique (marketVolume_greatest m)

theorem stateVolume_eq (m : MarketTuple) :
    equilibriumQuantity (sellState m, buyState m) = marketEquilibriumQuantity m := by
  rw [sellState_eq, buyState_eq]
  rfl

theorem sellMarginal_iff (m : MarketTuple) (hq : 0 < marketEquilibriumQuantity m) (r : ℝ) :
    marginalPrice (sellState m, marketEquilibriumQuantity m) ≤ r ↔
      marketEquilibriumQuantity m ≤ rawSupply m r := by
  have hq' : 0 < equilibriumQuantity (sellState m, buyState m) := by rwa [stateVolume_eq]
  obtain ⟨i, hi⟩ := (positive_equilibrium_has_marginals _ hq').1
  rw [stateVolume_eq] at hi
  have h := marginal_le_iff_below (sellPrices m) (sellQuantities m)
    (sellPrices_monotone m) (marketEquilibriumQuantity m) hi r
  rwa [below_sorted] at h

theorem buyMarginal_iff (m : MarketTuple) (hq : 0 < marketEquilibriumQuantity m) (r : ℝ) :
    r ≤ marginalPrice (buyState m, marketEquilibriumQuantity m) ↔
      marketEquilibriumQuantity m ≤ rawDemand m r := by
  have hq' : 0 < equilibriumQuantity (sellState m, buyState m) := by rwa [stateVolume_eq]
  obtain ⟨i, hi⟩ := (positive_equilibrium_has_marginals _ hq').2
  rw [stateVolume_eq] at hi
  have h := le_marginal_iff_above (buyPrices m) (buyQuantities m)
    (buyPrices_antitone m) (marketEquilibriumQuantity m) hi r
  rwa [above_sorted] at h

set_option maxHeartbeats 1600000 in
-- Elaborating the dependent tuple casts across four cumulative-cut comparisons
-- needs a larger allowance; the resulting proof is still checked by the kernel.
/-- Original label: `lem:state-functionals-permutation-invariant`.
The actual selected midpoint, including the zero-volume fallback, is
independent of every permutation of the original side-tagged book. -/
theorem marketMidpoint_permute (m : MarketTuple) (π : FinitePermutation m.1) :
    marketMidpointPrice (permute m π) = marketMidpointPrice m := by
  have hQ := marketVolume_permute m π
  by_cases hz : marketEquilibriumQuantity m = 0
  · rw [marketMidpointPrice_zero (hQ.trans hz), marketMidpointPrice_zero hz]
  have hq : 0 < marketEquilibriumQuantity m := lt_of_le_of_ne (zero_le _) (Ne.symm hz)
  have hq' : 0 < marketEquilibriumQuantity (permute m π) := by rwa [hQ]
  have hs : marginalPrice (sellState (permute m π), marketEquilibriumQuantity (permute m π)) =
      marginalPrice (sellState m, marketEquilibriumQuantity m) := by
    apply le_antisymm
    · apply (sellMarginal_iff (permute m π) hq' _).mpr
      rw [hQ, rawSupply_permute]
      exact (sellMarginal_iff m hq _).mp le_rfl
    · apply (sellMarginal_iff m hq _).mpr
      have h := (sellMarginal_iff (permute m π) hq' _).mp le_rfl
      simpa only [hQ, rawSupply_permute] using h
  have hb : marginalPrice (buyState (permute m π), marketEquilibriumQuantity (permute m π)) =
      marginalPrice (buyState m, marketEquilibriumQuantity m) := by
    apply le_antisymm
    · apply (buyMarginal_iff m hq _).mpr
      have h := (buyMarginal_iff (permute m π) hq' _).mp le_rfl
      simpa only [hQ, rawDemand_permute] using h
    · apply (buyMarginal_iff (permute m π) hq' _).mpr
      rw [hQ, rawDemand_permute]
      exact (buyMarginal_iff m hq _).mp le_rfl
  simpa only [sellState_eq, buyState_eq] using
    congrArg₂ (fun x y : ℝ ↦ (x + y) / 2) hs hb

end Thesis.Foundations.MarketClearing.DoctoralPermutation
