import Thesis.Foundations.MarketClearing.Equilibrium

/-! Exact supremum topology and cumulative-state domain for the clearing chapter. -/

namespace Thesis.Foundations.MarketClearing.Alignment

open Thesis.Foundations.MarketRepresentation
open FiniteSets FiniteSets.FiniteSubsets TuplesBasic TuplesMetricTopology
open Selection Sorting Equilibrium

universe u v

/-! The Hausdorff estimate `tupleProjection_edist_le` (with its general form
`hausdorffEDist_image_le_of_edist_le`) and the sup-product-metric separation
continuity `continuous_separationOperator_supMetric` (with
`supProductEMetricSpace` and `separationComponent_edist_lt_of_near`) live in
`Selection`, where they are the mapped proofs of
`prop:tuple-projection-continuous` and `prop:separation-continuous`. They are
re-exported here only so that fully qualified `Alignment.…` references keep
working. -/
export Selection (hausdorffEDist_image_le_of_edist_le tupleProjection_edist_le
  supProductEMetricSpace separationComponent_edist_lt_of_near
  continuous_separationOperator_supMetric)

/-- Original label: `lem:cumulative-summation-continuous`.
Nonnegative cumulative quantities really lie in the sorted quantity space used next. -/
theorem cumulativeQuantityTuple_isSorted (x : Tuple Quantity) :
    IsSorted (cumulativeQuantityTuple x) := by
  apply (isSorted_iff_monotone _).mpr
  intro i j hij
  change (∑ k : Fin x.length, if k ≤ i then Tuple.entry x k else 0) ≤
    ∑ k : Fin x.length, if k ≤ j then Tuple.entry x k else 0
  apply Finset.sum_le_sum
  intro k _
  by_cases hki : k ≤ i
  · simp [hki, hki.trans hij]
  · simp only [if_neg hki]
    exact bot_le

/-- Exact thesis `C(R)`: both quantity and price tuples are sorted, with equal lengths. -/
abbrev CumulativeClearingStates (priceSorted : Tuple ℝ → Prop) :=
  {state : Tuple Quantity × Tuple ℝ //
    IsSorted state.1 ∧ priceSorted state.2 ∧ state.1.length = state.2.length}

/-- Original label: `thm:equilibrium-quantity-measurable`.
This is the literal manuscript domain, including the sorted cumulative quantities,
with the Borel structure induced by the specified product and subspace metrics. -/
theorem measurable_equilibriumQuantity_cumulativeDomain :
    letI : TopologicalSpace (Tuple Quantity) := tupleHausdorffMetricTopology (X := Quantity)
    letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology (X := ℝ)
    @Measurable
      (CumulativeClearingStates IsIncreasingRealTuple ×
        CumulativeClearingStates IsDecreasingRealTuple)
      Quantity (borel _) inferInstance
      (fun s => equilibriumQuantity (s.1.val, s.2.val)) := by
  letI : TopologicalSpace (Tuple Quantity) := tupleHausdorffMetricTopology (X := Quantity)
  letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology (X := ℝ)
  letI : MeasurableSpace (Tuple Quantity) := tupleHausdorffBorel (X := Quantity)
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  letI : BorelSpace (Tuple Quantity) := ⟨rfl⟩
  letI : BorelSpace (Tuple ℝ) := ⟨rfl⟩
  haveI : TopologicalSpace.SeparableSpace (Tuple Quantity) :=
    TuplesMetricTopology.separableSpace (X := Quantity)
  haveI : TopologicalSpace.SeparableSpace (Tuple ℝ) :=
    TuplesMetricTopology.separableSpace (X := ℝ)
  have h := measurable_equilibriumQuantity.comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd) :
      Measurable (fun s : CumulativeClearingStates IsIncreasingRealTuple ×
        CumulativeClearingStates IsDecreasingRealTuple => (s.1.val, s.2.val)))
  have hb : (inferInstance : MeasurableSpace
      (CumulativeClearingStates IsIncreasingRealTuple ×
        CumulativeClearingStates IsDecreasingRealTuple)) = borel _ :=
    BorelSpace.measurable_eq
  rw [← hb]
  exact h

/-- Original label: `thm:equilibrium-quantity-measurable`.
The empty-cell branch of the displayed formula is exactly zero. -/
theorem maxClearedQuantityForIndexSet_empty (Qs Qb : Tuple Quantity) :
    maxClearedQuantityForIndexSet ⟨∅, Set.finite_empty⟩ Qs Qb = 0 := by
  simp [maxClearedQuantityForIndexSet, FiniteSubsets.toFinset]

/-- Original label: `thm:equilibrium-quantity-measurable`.
The nonempty-cell branch is an attained maximum of precisely the candidate volumes. -/
theorem maxClearedQuantityForIndexSet_isGreatest
    (η : FiniteSubsets (ℕ × ℕ)) (hη : (η : Set (ℕ × ℕ)).Nonempty)
    (Qs Qb : Tuple Quantity) :
    IsGreatest (clearedQuantityAt Qs Qb '' (η : Set (ℕ × ℕ)))
      (maxClearedQuantityForIndexSet η Qs Qb) := by
  classical
  have hn : (FiniteSubsets.toFinset η).Nonempty := by
    simpa [FiniteSubsets.toFinset] using hη
  obtain ⟨ij, hij, heq⟩ := Finset.exists_mem_eq_sup (FiniteSubsets.toFinset η)
    hn (clearedQuantityAt Qs Qb)
  refine ⟨⟨ij, by simpa [FiniteSubsets.toFinset] using hij, heq.symm⟩, ?_⟩
  rintro q ⟨ij, hij, rfl⟩
  exact Finset.le_sup (f := clearedQuantityAt Qs Qb)
    (by simpa [FiniteSubsets.toFinset] using hij)

end Thesis.Foundations.MarketClearing.Alignment
