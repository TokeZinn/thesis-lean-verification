import Thesis.Foundations.MarketClearing.Equilibrium
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! # The midpoint price of the actual sorted marginal orders

The selector uses the least cumulative index reaching the positive cleared
quantity. Empty and zero-volume cases return zero, as in the current thesis.
-/

noncomputable section
namespace Thesis.Foundations.MarketClearing.MidpointPrice

open Set MeasureTheory MarketRepresentation MarketRepresentation.TuplesMetricTopology
open Sorting Equilibrium

local instance : MeasurableSpace (Tuple Quantity) := tupleHausdorffBorel
local instance : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel

def tuplePriceEval (i : ℕ) (x : Tuple ℝ) : ℝ :=
  if h : i < x.1 then x.2 ⟨i, h⟩ else 0

theorem continuous_tuplePriceEval (i : ℕ) :
    @Continuous (Tuple ℝ) ℝ (tupleHausdorffMetricTopology (X := ℝ)) _ (tuplePriceEval i) := by
  rw [continuous_tupleHausdorff_iff_fixedLength]
  intro n
  by_cases hi : i < n
  · simpa [tuplePriceEval, hi] using (continuous_apply (A := fun _ : Fin n => ℝ) ⟨i, hi⟩)
  · simpa [tuplePriceEval, hi] using
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))

theorem measurable_tuplePriceEval (i : ℕ) : Measurable (tuplePriceEval i) := by
  letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology
  exact (continuous_tuplePriceEval i).borel_measurable

abbrev MarginalInput := (Tuple Quantity × Tuple ℝ) × Quantity

def ReachesFirst (s : MarginalInput) (i : ℕ) : Prop :=
  0 < s.2 ∧ s.2 ≤ tupleQuantityEval i s.1.1 ∧
    ∀ j < i, tupleQuantityEval j s.1.1 < s.2

theorem reachesFirst_unique {s : MarginalInput} {i j : ℕ}
    (hi : ReachesFirst s i) (hj : ReachesFirst s j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (not_lt_of_ge hi.2.1 (hj.2.2 i h)).elim
  · exact h
  · exact (not_lt_of_ge hj.2.1 (hi.2.2 j h)).elim

theorem reachesFirst_exists {s : MarginalInput} (hq : 0 < s.2)
    (hex : ∃ i, s.2 ≤ tupleQuantityEval i s.1.1) : ∃ i, ReachesFirst s i := by
  classical
  refine ⟨Nat.find hex, hq, Nat.find_spec hex, ?_⟩
  intro j hj
  exact lt_of_not_ge (Nat.find_min hex hj)

theorem reachesFirst_in_domain {s : MarginalInput} {i : ℕ} (hi : ReachesFirst s i) :
    i < s.1.1.1 := by
  by_contra hn
  have hz : tupleQuantityEval i s.1.1 = 0 := by
    simp [tupleQuantityEval, Tuple.length, hn]
  exact (not_le_of_gt hi.1) (hz ▸ hi.2.1)

/-- Positive compatible volume reaches an actual cumulative index on each side. -/
theorem positive_equilibrium_has_marginals
    (s : (Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ))
    (hq : 0 < equilibriumQuantity s) :
    (∃ i, ReachesFirst (s.1, equilibriumQuantity s) i) ∧
    (∃ j, ReachesFirst (s.2, equilibriumQuantity s) j) := by
  classical
  let η := FiniteSets.FiniteSubsets.toFinset (feasibleEquilibriumIndexSet s.1.2 s.2.2)
  have hn : η.Nonempty := by
    by_contra h
    have he : η = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    change 0 < η.sup (clearedQuantityAt s.1.1 s.2.1) at hq
    simp [he] at hq
  obtain ⟨ij, _, he⟩ := Finset.exists_mem_eq_sup η hn (clearedQuantityAt s.1.1 s.2.1)
  have he' : equilibriumQuantity s =
      min (tupleQuantityEval ij.1 s.1.1) (tupleQuantityEval ij.2 s.2.1) := he
  exact ⟨reachesFirst_exists hq ⟨ij.1, he'.le.trans (min_le_left _ _)⟩,
    reachesFirst_exists hq ⟨ij.2, he'.le.trans (min_le_right _ _)⟩⟩

theorem measurableSet_reachesFirst (i : ℕ) :
    MeasurableSet {s : MarginalInput | ReachesFirst s i} := by
  have hq : Measurable (fun s : MarginalInput => s.2) := measurable_snd
  have hQ (j : ℕ) : Measurable (fun s : MarginalInput => tupleQuantityEval j s.1.1) :=
    (measurable_tupleQuantityEval j).comp (measurable_fst.comp measurable_fst)
  have hall : MeasurableSet {s : MarginalInput | ∀ j < i, tupleQuantityEval j s.1.1 < s.2} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => measurableSet_lt (hQ j) hq
  exact (measurableSet_lt measurable_const hq).inter ((measurableSet_le hq (hQ i)).inter hall)

open Classical in
def marginalPrice (s : MarginalInput) : ℝ :=
  ∑' i : ℕ, if ReachesFirst s i then tuplePriceEval i s.1.2 else 0

theorem marginalPrice_zero (s : Tuple Quantity × Tuple ℝ) : marginalPrice (s, 0) = 0 := by
  classical
  simp [marginalPrice, ReachesFirst]

/-- On a positive-volume marginal cell, the formula selects exactly its price. -/
theorem marginalPrice_eq {s : MarginalInput} {i : ℕ} (hi : ReachesFirst s i) :
    marginalPrice s = tuplePriceEval i s.1.2 := by
  classical
  unfold marginalPrice
  rw [tsum_eq_single i]
  · simp [hi]
  · intro j hji
    have hj : ¬ReachesFirst s j := fun hj => hji (reachesFirst_unique hj hi)
    simp [hj]

theorem measurable_marginalPrice : Measurable marginalPrice := by
  classical
  have hm (i : ℕ) : Measurable (fun s : MarginalInput =>
      if ReachesFirst s i then tuplePriceEval i s.1.2 else 0) :=
    ((measurable_tuplePriceEval i).comp (measurable_snd.comp measurable_fst)).ite
      (measurableSet_reachesFirst i) measurable_const
  have hsum (s : MarginalInput) : Summable (fun i : ℕ =>
      if ReachesFirst s i then tuplePriceEval i s.1.2 else 0) := by
    by_cases hex : ∃ i, ReachesFirst s i
    · obtain ⟨i, hi⟩ := hex
      apply summable_of_ne_finset_zero (s := {i})
      intro j hj
      have hn : ¬ReachesFirst s j := fun h => hj (by simp [reachesFirst_unique h hi])
      simp [hn]
    · push Not at hex
      simpa only [if_neg (hex _)] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  exact measurable_of_tendsto_metrizable
    (fun n => Finset.measurable_sum (Finset.range n) (fun i _ => hm i))
    (tendsto_pi_nhds.mpr fun s => (hsum s).hasSum.tendsto_sum_nat)

/-- Original label: `cor:state-midpoint-price-measurable`. -/
def marketMidpointPrice (m : MarketTuple) : ℝ :=
  (marginalPrice ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m),
      marketEquilibriumQuantity m) +
    marginalPrice ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m),
      marketEquilibriumQuantity m)) / 2

theorem marketMidpointPrice_zero {m : MarketTuple} (h : marketEquilibriumQuantity m = 0) :
    marketMidpointPrice m = 0 := by
  simp [marketMidpointPrice, h, marginalPrice_zero]

/-- Original label: `cor:state-midpoint-price-measurable`.
The cumulative and price coordinates use the same permutation and have the
same length, so a reaching quantity index selects a genuine price. -/
theorem cumulativeSell_length_eq_price_length (m : MarketTuple) :
    (cumulativeSellQuantityTuple m).length = (sortedSellPriceTuple m).length := by
  simp [cumulativeSellQuantityTuple, cumulativeQuantityTuple, sortedSellQuantityTuple,
    sortedSellPriceTuple, MarketRepresentation.TuplesMeasurableSorting.permutationMap,
    realMinimalPermutationLE, ← sellPriceTuple_length_eq_sellQuantityTuple_length]

/-- Original label: `cor:state-midpoint-price-measurable`. -/
theorem cumulativeBuy_length_eq_price_length (m : MarketTuple) :
    (cumulativeBuyQuantityTuple m).length = (sortedBuyPriceTuple m).length := by
  simp [cumulativeBuyQuantityTuple, cumulativeQuantityTuple, sortedBuyQuantityTuple,
    sortedBuyPriceTuple, MarketRepresentation.TuplesMeasurableSorting.permutationMap,
    realMinimalPermutationGE, ← buyPriceTuple_length_eq_buyQuantityTuple_length]

/-- Original label: `cor:state-midpoint-price-measurable`.
For positive volume, both least reaching indices exist in the actual cumulative
tuples and the midpoint uses precisely their selected prices. -/
theorem marketMidpointPrice_positive_formula (m : MarketTuple)
    (hq : 0 < marketEquilibriumQuantity m) :
    ∃ i j : ℕ,
      ReachesFirst ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m),
        marketEquilibriumQuantity m) i ∧
      ReachesFirst ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m),
        marketEquilibriumQuantity m) j ∧
      i < (cumulativeSellQuantityTuple m).length ∧
      j < (cumulativeBuyQuantityTuple m).length ∧
      i < (sortedSellPriceTuple m).length ∧
      j < (sortedBuyPriceTuple m).length ∧
      marketMidpointPrice m =
        (tuplePriceEval i (sortedSellPriceTuple m) +
          tuplePriceEval j (sortedBuyPriceTuple m)) / 2 := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := positive_equilibrium_has_marginals
    ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m),
      (cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m)) hq
  change ReachesFirst ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m),
    marketEquilibriumQuantity m) i at hi
  change ReachesFirst ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m),
    marketEquilibriumQuantity m) j at hj
  refine ⟨i, j, hi, hj, reachesFirst_in_domain hi, reachesFirst_in_domain hj, ?_, ?_, ?_⟩
  · rw [← cumulativeSell_length_eq_price_length]
    exact reachesFirst_in_domain hi
  · rw [← cumulativeBuy_length_eq_price_length]
    exact reachesFirst_in_domain hj
  simp only [marketMidpointPrice, marginalPrice_eq hi, marginalPrice_eq hj]

/-- Original label: `cor:state-midpoint-price-measurable`.
This is the thesis proof by the measurable-partition theorem. The state space
is covered by the countable family of measurable cells
`A_0 = {\mathscr{Q}_{state} = 0}` and
`B^{i,j} = {\mathscr{Q}_{state} > 0, ι^s = i, ι^b = j}` (the cells
`B^{i,j}_{n_s,n_b}` of the thesis; the length indices `(n_s, n_b)` are absorbed
because the coordinate evaluations `ev_i = tuplePriceEval i` are defined on
all of tuple space and vanish out of range). On `A_0` the midpoint price is
`0`; on `B^{i,j}` it coincides with the fixed measurable combination
`(ev_i(\hat p^s) + ev_j(\hat p^b)) / 2`
(`marginalPrice_eq`). The cells are measurable because the state maps
(sorting, cumulative sums, compatible volume) are, and they cover the space by
`positive_equilibrium_has_marginals`;
`measurable_of_measurable_restrict_countable_cover` pastes the restrictions.
The marginal-index cells are described by `ReachesFirst`, i.e.
`ev_{i-1}(\hat Q) < \mathscr{Q}_{state} ≤ ev_i(\hat Q)` in the thesis'
notation. -/
theorem measurable_marketMidpointPrice :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace (X := MarketOrderPayload)
    @Measurable MarketTuple ℝ (tupleHausdorffBorel (X := MarketOrder)) _ marketMidpointPrice := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple := tupleHausdorffBorel (X := MarketOrder)
  let sellInput : MarketTuple → MarginalInput := fun m =>
    ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m), marketEquilibriumQuantity m)
  let buyInput : MarketTuple → MarginalInput := fun m =>
    ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m), marketEquilibriumQuantity m)
  have hsell : Measurable sellInput :=
    (measurable_cumulativeSellQuantityTuple.prodMk measurable_sortedSellPriceTuple).prodMk
      measurable_marketEquilibriumQuantity
  have hbuy : Measurable buyInput :=
    (measurable_cumulativeBuyQuantityTuple.prodMk measurable_sortedBuyPriceTuple).prodMk
      measurable_marketEquilibriumQuantity
  -- the thesis cells: `none` is `A_0`, `some (i, j)` is `B^{i,j}`
  let cell : Option (ℕ × ℕ) → Set MarketTuple := fun c =>
    c.elim {m | marketEquilibriumQuantity m = 0}
      (fun ij => {m | ReachesFirst (sellInput m) ij.1 ∧ ReachesFirst (buyInput m) ij.2})
  have hcell : ∀ c, MeasurableSet (cell c) := by
    intro c
    rcases c with _ | ⟨i, j⟩
    · exact measurable_marketEquilibriumQuantity (measurableSet_singleton 0)
    · exact ((measurableSet_reachesFirst i).preimage hsell).inter
        ((measurableSet_reachesFirst j).preimage hbuy)
  have hcover : ⋃ c, cell c = Set.univ := by
    apply Set.eq_univ_of_forall
    intro m
    rw [Set.mem_iUnion]
    by_cases hq : marketEquilibriumQuantity m = 0
    · exact ⟨none, hq⟩
    · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := positive_equilibrium_has_marginals
        ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m),
          (cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m)) (pos_iff_ne_zero.mpr hq)
      exact ⟨some (i, j), hi, hj⟩
  refine TuplesMeasurableSorting.measurable_of_measurable_restrict_countable_cover
    hcell hcover ?_
  intro c
  rcases c with _ | ⟨i, j⟩
  · have hz : (fun x : cell none => marketMidpointPrice x) = fun _ => 0 := by
      funext x
      have h0 : marketEquilibriumQuantity x.1 = 0 := x.2
      exact marketMidpointPrice_zero h0
    rw [hz]
    exact measurable_const
  · have hij : (fun x : cell (some (i, j)) => marketMidpointPrice x) =
        fun x : cell (some (i, j)) => (tuplePriceEval i (sortedSellPriceTuple x) +
          tuplePriceEval j (sortedBuyPriceTuple x)) / 2 := by
      funext x
      have h1 : ReachesFirst ((cumulativeSellQuantityTuple x.1, sortedSellPriceTuple x.1),
          marketEquilibriumQuantity x.1) i := x.2.1
      have h2 : ReachesFirst ((cumulativeBuyQuantityTuple x.1, sortedBuyPriceTuple x.1),
          marketEquilibriumQuantity x.1) j := x.2.2
      simp only [marketMidpointPrice, marginalPrice_eq h1, marginalPrice_eq h2]
    rw [hij]
    exact ((((measurable_tuplePriceEval i).comp measurable_sortedSellPriceTuple).add
      ((measurable_tuplePriceEval j).comp measurable_sortedBuyPriceTuple)).div_const 2).comp
      measurable_subtype_coe

/-- Original label: `cor:state-midpoint-price-measurable`. -/
def marketEquilibrium (m : MarketTuple) : ℝ × Quantity :=
  (marketMidpointPrice m, marketEquilibriumQuantity m)

/-- Original label: `cor:state-midpoint-price-measurable`.
The joint output has the product Borel sigma-algebra stated in the thesis. -/
theorem measurable_marketEquilibrium :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace (X := MarketOrderPayload)
    @Measurable MarketTuple (ℝ × Quantity) (tupleHausdorffBorel (X := MarketOrder)) _
      marketEquilibrium :=
  measurable_marketMidpointPrice.prodMk measurable_marketEquilibriumQuantity

end Thesis.Foundations.MarketClearing.MidpointPrice
