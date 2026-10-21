import Thesis.Intraday.LOBsAndTuples.Clearing
import Thesis.Foundations.MarketRepresentation.TuplesMeasurableSorting

/-! # Borel sorting for the intraday price-time order -/

noncomputable section
namespace Thesis.Intraday.MarketSorting

open Set Execution Clearing Foundations.MarketRepresentation
open DisjointUnionTopology TuplesMetricTopology TuplesSorting TuplesMeasurableSorting

attribute [local instance] Execution.sigmaBorel marketPriceTimeOrder
local instance : EMetricSpace TaggedOrder := disjointUnionEMetricSpace

def sideKey (x : TaggedOrder) : ℕ := if x.1 then 0 else 1
def priceKey (x : TaggedOrder) : ℝ := if x.1 then -price x.2 else price x.2
def timeKey (x : TaggedOrder) : ℝ := time x.2

theorem continuous_sideKey : Continuous sideKey := by
  apply continuous_sigma_iff.mpr
  intro buy
  change Continuous (fun _ : Order => (if buy then 0 else 1 : ℕ))
  exact continuous_const

theorem continuous_priceKey : Continuous priceKey := by
  apply continuous_sigma_iff.mpr
  intro buy
  cases buy
  · exact continuous_price
  · exact continuous_price.neg

theorem continuous_timeKey : Continuous timeKey := by
  apply continuous_sigma_iff.mpr
  intro buy
  exact continuous_time

theorem measurableSet_marketLE : MeasurableSet {p : TaggedOrder × TaggedOrder | p.1 ≤ p.2} := by
  have hf : Measurable (fun p : TaggedOrder × TaggedOrder => p.1) := measurable_fst
  have hs : Measurable (fun p : TaggedOrder × TaggedOrder => p.2) := measurable_snd
  have s1 := continuous_sideKey.measurable.comp hf
  have s2 := continuous_sideKey.measurable.comp hs
  have p1 := continuous_priceKey.measurable.comp hf
  have p2 := continuous_priceKey.measurable.comp hs
  have t1 := continuous_timeKey.measurable.comp hf
  have t2 := continuous_timeKey.measurable.comp hs
  have h := (measurableSet_eq_fun hf hs).union ((measurableSet_lt s1 s2).union
      ((measurableSet_eq_fun s1 s2).inter ((measurableSet_lt p1 p2).union
        ((measurableSet_eq_fun p1 p2).inter (measurableSet_lt t1 t2)))))
  change MeasurableSet {p : TaggedOrder × TaggedOrder |
    p.1 = p.2 ∨ marketKey p.1 < marketKey p.2}
  simpa only [marketKey, priorityKey, Prod.Lex.toLex_lt_toLex,
    Function.comp_def, sideKey, priceKey, timeKey, setOf_or, setOf_and] using h

def sortMarket : Market → Market := minimumSort

theorem sortMarket_sorted (m : Market) : SortedMarket (sortMarket m) :=
  (sortedMarket_iff_isSorted _).mpr (minimumSort_isSorted m)

/-- The exact minimal sorting rule has a Borel graph for the intraday order. -/
theorem measurable_sortMarket : Measurable sortMarket := by
  have hle : @MeasurableSet (TaggedOrder × TaggedOrder)
      (@borel (TaggedOrder × TaggedOrder)
        (@instTopologicalSpaceProd TaggedOrder TaggedOrder
          (disjointUnionMetricTopology (X := fun _ : Bool => Order))
          (disjointUnionMetricTopology (X := fun _ : Bool => Order)))) {p | p.1 ≤ p.2} := by
    rw [metricTopology_eq_sigma]
    rw [← @BorelSpace.measurable_eq (TaggedOrder × TaggedOrder) _ _ _]
    exact measurableSet_marketLE
  have h := measurable_minimumSort_of_borelOrder (X := TaggedOrder) hle
  rw [market_borel_eq] at h
  exact h

end Thesis.Intraday.MarketSorting
