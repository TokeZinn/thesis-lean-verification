import Thesis.Intraday.LOBsAndTuples.Execution
import Thesis.Foundations.MarketClearing.Selection
import Thesis.Foundations.MarketClearing.SeparationAlgebra

/-! # Clearing the actual tagged intraday market tuple -/

noncomputable section
namespace Thesis.Intraday.Clearing

open Set Execution Foundations.MarketRepresentation
open Foundations.MarketRepresentation.DisjointUnionTopology
open Foundations.MarketRepresentation.TuplesMetricTopology
open Foundations.MarketRepresentation.TuplesBasic
open Foundations.MarketRepresentation.FiniteSets
open Foundations.MarketActions.Primitive Foundations.MarketActions.Analytic
open Foundations.MarketClearing.Selection

attribute [local instance] Execution.sigmaBorel

/-- Original label: `defn:intraday-order-space`. -/
abbrev TaggedOrder := DisjointUnion (fun _ : Bool => Order)
abbrev Market := Tuple TaggedOrder

local instance : EMetricSpace TaggedOrder := disjointUnionEMetricSpace

/-- Both layers of disjoint-union topology agree with their native topology. -/
theorem market_topology_eq : tupleHausdorffMetricTopology (X := TaggedOrder) =
    (inferInstance : TopologicalSpace Market) := by
  rw [tupleHausdorffMetricTopology_eq_sigma]
  exact congrArg (fun t : TopologicalSpace TaggedOrder =>
    @instTopologicalSpaceSigma ℕ (fun n => Fin n → TaggedOrder)
      (fun n => @Pi.topologicalSpace (Fin n) (fun _ => TaggedOrder) (fun _ => t)))
    (metricTopology_eq_sigma (X := fun _ : Bool => Order))

def side (buy : Bool) (m : Market) : Book := separationComponent buy m
def splitMarket (m : Market) : State := (side true m, side false m)

def marketKey (x : TaggedOrder) : ℕ ×ₗ (ℝ ×ₗ ℝ) :=
  toLex (if x.1 then 0 else 1, priorityKey x.1 x.2)

def SortedMarket (m : Market) : Prop := Monotone (fun i => marketKey (m.2 i))

/-- Original label: `defn:price-time-priority-metric`.
The thesis's partial order: buys precede sells, then price and time decide;
distinct orders with the same side, price, and time remain incomparable. -/
@[implicit_reducible] def marketPriceTimeOrder : PartialOrder TaggedOrder where
  le x y := x = y ∨ marketKey x < marketKey y
  le_refl _ := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    exact Or.inr (lt_trans hxy hyz)
  le_antisymm x y hxy hyx := by
    rcases hxy with hxy | hxy
    · exact hxy
    rcases hyx with hyx | hyx
    · exact hyx.symm
    exact (lt_asymm hxy hyx).elim

theorem market_lt_iff (x y : TaggedOrder) :
    @LT.lt TaggedOrder marketPriceTimeOrder.toLT x y ↔ marketKey x < marketKey y := by
  change ((x = y ∨ marketKey x < marketKey y) ∧
    ¬(y = x ∨ marketKey y < marketKey x)) ↔ _
  constructor
  · rintro ⟨rfl | h, hn⟩
    · exact (hn (Or.inl rfl)).elim
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rintro (rfl | h')
    · exact (lt_irrefl _ h)
    · exact lt_asymm h h'

theorem sortedMarket_iff_isSorted (m : Market) :
    SortedMarket m ↔ @IsSorted TaggedOrder marketPriceTimeOrder.toPreorder m := by
  simp only [SortedMarket, Monotone, IsSorted, Tuple.entry, market_lt_iff, not_lt]
  constructor
  · intro h i j hij; exact h hij
  · intro h i j hij; exact h i j hij

theorem market_borel_eq : tupleHausdorffBorel (X := TaggedOrder) =
    (inferInstance : MeasurableSpace Market) := by
  rw [tupleHausdorffBorel, market_topology_eq]
  exact (@BorelSpace.measurable_eq Market _ _ _).symm

def sideIndex (buy : Bool) (m : Market) (i : Fin (side buy m).1) : Fin m.1 :=
  ⟨(pairing (separationIndexSet buy m)).2 i,
    ((mem_separationIndexSet buy m).mp
      (pairing_entry_mem (separationIndexSet buy m) i)).choose⟩

theorem sideIndex_monotone (buy : Bool) (m : Market) : Monotone (sideIndex buy m) := by
  intro i j hij
  exact ((isSorted_iff_monotone _).mp (pairing_isSorted (separationIndexSet buy m))) i j hij

theorem side_entry (buy : Bool) (m : Market) (i : Fin (side buy m).1) :
    Sigma.mk buy ((side buy m).2 i) = m.2 (sideIndex buy m i) := by
  have htag : (m.2 (sideIndex buy m i)).1 = buy :=
    ((mem_separationIndexSet buy m).mp
      (pairing_entry_mem (separationIndexSet buy m) i)).choose_spec
  change Sigma.mk buy (valueAtTag buy (m.2 (sideIndex buy m i)) htag) = _
  generalize m.2 (sideIndex buy m i) = z at htag ⊢
  rcases z with ⟨a, x⟩
  cases htag
  rfl

/-- Original label: `prop:separation-preserves-price-time`. -/
theorem side_sorted (buy : Bool) {m : Market} (h : SortedMarket m) : Sorted buy (side buy m) := by
  intro i j hij
  have hp := h (sideIndex_monotone buy m hij)
  change marketKey (m.2 (sideIndex buy m i)) ≤ marketKey (m.2 (sideIndex buy m j)) at hp
  rw [← side_entry buy m i, ← side_entry buy m j] at hp
  simpa [marketKey, Prod.Lex.toLex_le_toLex] using hp

theorem continuous_side (buy : Bool) : Continuous (side buy) := by
  have h := continuous_separationComponent_disjointTopology (X := fun _ : Bool => Order) buy
  rw [market_topology_eq,
    tupleHausdorffMetricTopology_eq_sigma (X := Order)] at h
  exact h

theorem measurable_splitMarket : Measurable splitMarket :=
  (continuous_side true).measurable.prodMk (continuous_side false).measurable

def joinMarket (x : State) : Market := concat (retag true x.1) (retag false x.2)

/-- Rejoining the separated sides preserves every buy entry and its index. -/
theorem side_join_true (x : State) : side true (joinMarket x) = x.1 := by
  exact Foundations.MarketClearing.SeparationAlgebra.separationComponent_taggedConcat_left
    (X := fun _ : Bool => Order) true false (by decide) x.1 x.2

/-- Rejoining the separated sides preserves every sell entry and its index. -/
theorem side_join_false (x : State) : side false (joinMarket x) = x.2 := by
  exact Foundations.MarketClearing.SeparationAlgebra.separationComponent_taggedConcat_right
    (X := fun _ : Bool => Order) true false (by decide) x.1 x.2

theorem split_joinMarket (x : State) : splitMarket (joinMarket x) = x :=
  Prod.ext (side_join_true x) (side_join_false x)

/-- Separation of the joined market can only return entries of that side. -/
theorem side_join_exists (buy : Bool) (x : State) (i : Fin (side buy (joinMarket x)).1) :
    ∃ j : Fin (if buy then x.1 else x.2).1,
      (side buy (joinMarket x)).2 i = (if buy then x.1 else x.2).2 j := by
  have he := side_entry buy (joinMarket x) i
  generalize sideIndex buy (joinMarket x) i = k at he
  change Fin (x.1.1 + x.2.1) at k
  revert he
  refine Fin.addCases ?_ ?_ k
  · intro j he
    have he' : (Sigma.mk buy ((side buy (joinMarket x)).2 i) : TaggedOrder) =
        Sigma.mk true (x.1.2 j) := by
      simpa [joinMarket, concat, retag, Tuple.map, Tuple.entry] using he
    have ht := congrArg Sigma.fst he'
    change buy = true at ht
    subst buy
    exact ⟨j, congrArg (fun z : TaggedOrder => z.2) he'⟩
  · intro j he
    have he' : (Sigma.mk buy ((side buy (joinMarket x)).2 i) : TaggedOrder) =
        Sigma.mk false (x.2.2 j) := by
      simpa [joinMarket, concat, retag, Tuple.map, Tuple.entry] using he
    have ht := congrArg Sigma.fst he'
    change buy = false at ht
    subst buy
    exact ⟨j, congrArg (fun z : TaggedOrder => z.2) he'⟩

/-- Original block id: `source:3 - intraday/2_lobs_and_tuples.tex:331:rem:13`. -/
theorem joinMarket_sorted {x : State} (h : SortedState x) : SortedMarket (joinMarket x) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      have hp := h.1 (show i ≤ j from hij)
      simpa [joinMarket, concat, retag, Tuple.map, marketKey, Tuple.entry,
        Prod.Lex.toLex_le_toLex] using hp
    · intro j _
      simp [joinMarket, concat, retag, Tuple.map, marketKey, Prod.Lex.toLex_le_toLex]
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      have hj : j.val < x.1.1 := j.isLt
      change x.1.1 + i.val ≤ j.val at hij
      omega
    · intro j hij
      have hij' : i ≤ j := by
        change x.1.1 + i.val ≤ x.1.1 + j.val at hij
        exact Nat.le_of_add_le_add_left hij
      have hp := h.2 hij'
      simpa [joinMarket, concat, retag, Tuple.map, marketKey, Tuple.entry,
        Prod.Lex.toLex_le_toLex] using hp

theorem splitMarket_count (m : Market) : orderCount (splitMarket m) = m.1 := by
  classical
  let b := FiniteSubsets.toFinset (separationIndexSet true m)
  let s := FiniteSubsets.toFinset (separationIndexSet false m)
  have hd : Disjoint b s := by
    apply Finset.disjoint_left.mpr
    intro n hb hs
    obtain ⟨hn, htag⟩ := (mem_separationIndexSet true m).mp
      ((FiniteSubsets.mem_toFinset _).mp hb)
    obtain ⟨hn', htag'⟩ := (mem_separationIndexSet false m).mp
      ((FiniteSubsets.mem_toFinset _).mp hs)
    exact Bool.noConfusion (htag.symm.trans htag')
  have hu : b ∪ s = Finset.range m.1 := by
    ext n
    simp only [Finset.mem_union, b, s, FiniteSubsets.mem_toFinset,
      mem_separationIndexSet, Finset.mem_range, Tuple.length]
    constructor
    · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
    · intro hn
      cases ht : (m.2 ⟨n, hn⟩).1 with
      | false => exact Or.inr ⟨hn, ht⟩
      | true => exact Or.inl ⟨hn, ht⟩
  change b.card + s.card = m.1
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_range]

theorem continuous_joinMarket : Continuous joinMarket := by
  have hc := continuous_concat_emetricTopology (X := TaggedOrder)
  have ht (buy : Bool) : Continuous (retag (X := fun _ : Bool => Order) buy) := by
    have h := retag_continuous (X := fun _ : Bool => Order) buy
    rw [tupleHausdorffMetricTopology_eq_sigma (X := Order),
      market_topology_eq] at h
    exact h
  have hc' : Continuous (fun p : Market × Market => concat p.1 p.2) := by
    change @Continuous (Market × Market) Market
      (@instTopologicalSpaceProd Market Market
        (tupleHausdorffMetricTopology (X := TaggedOrder))
        (tupleHausdorffMetricTopology (X := TaggedOrder)))
      (tupleHausdorffMetricTopology (X := TaggedOrder)) _ at hc
    rw [market_topology_eq] at hc
    exact hc
  exact hc'.comp ((ht true).comp continuous_fst |>.prodMk ((ht false).comp continuous_snd))

/-- Original label: `defn:clearing-operator`.
This formula uses the manuscript's market length as its exact iteration count. -/
def clearMarket (m : Market) : Market := joinMarket (step^[m.1 - 1] (splitMarket m))

/-- Original label: `thm:clearing-measurable`.
Measurability on all tuples implies measurability after restriction to the
sorted domain; the codomain closure is proved separately. -/
theorem measurable_clearMarket : Measurable clearMarket := by
  apply measurable_pasting_iff.mpr
  intro n
  exact continuous_joinMarket.measurable.comp
    ((measurable_step_iterate (n - 1)).comp
      (measurable_splitMarket.comp continuous_sigmaMk.measurable))

theorem clearMarket_sorted {m : Market} (h : SortedMarket m) : SortedMarket (clearMarket m) :=
  joinMarket_sorted (iterate_sorted _ ⟨side_sorted true h, side_sorted false h⟩)

theorem clearMarket_keySubset (buy : Bool) (m : Market) :
    KeySubset buy (side buy (clearMarket m)) (side buy m) := by
  intro i
  obtain ⟨j, hj⟩ := side_join_exists buy (step^[m.1 - 1] (splitMarket m)) i
  have hs := iterate_keySubset (m.1 - 1) (splitMarket m)
  cases buy with
  | false =>
    obtain ⟨k, hk⟩ := hs.2 j
    exact ⟨k, (congrArg (priorityKey false) hj).trans hk⟩
  | true =>
    obtain ⟨k, hk⟩ := hs.1 j
    exact ⟨k, (congrArg (priorityKey true) hj).trans hk⟩

theorem clearing_iteration_stops (m : Market) :
    ¬Crossing (step^[m.1 - 1] (splitMarket m)) := by
  rw [← splitMarket_count m]
  exact clearSides_not_crossing (splitMarket m)

/-- Original label: `defn:clearing-operator`. -/
def sortedClearMarket (m : {m : Market // SortedMarket m}) : {m : Market // SortedMarket m} :=
  ⟨clearMarket m, clearMarket_sorted m.property⟩

/-- Original label: `thm:clearing-measurable`.
The literal clearing formula with its sorted codomain. -/
theorem measurable_sortedClearMarket : Measurable sortedClearMarket :=
  (measurable_clearMarket.comp measurable_subtype_coe).subtype_mk

end Thesis.Intraday.Clearing
