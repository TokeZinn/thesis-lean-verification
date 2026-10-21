import Thesis.Context.ThesisContext

/-! # Exact clauses of the current market-actions chapter

Thesis source: `1 - theoretical foundations/3_market_actions.tex`.
-/

namespace Thesis.Foundations.MarketActions.Alignment

open MarketRepresentation MarketRepresentation.TuplesBasic
open MarketRepresentation.TuplesSorting MarketRepresentation.TuplesMetricTopology
open MarketRepresentation.FiniteSets MarketRepresentation.FiniteSets.FiniteSubsets
open Primitive Analytic

universe u v

/-- Original label: `defn:identifier-cancel`.
Resolve stable identifiers against the input state before deleting anything.
Lean indices are zero-based; no uniqueness assumption on the identifier field
is needed, since the source cancels every matching index. -/
def identifierIndices {X : Type u} {I : Type v} (id : X → I)
    (J : Set I) (x : Tuple X) : FiniteSubsets ℕ :=
  ⟨{n | ∃ h : n < x.length, id (x.entry ⟨n, h⟩) ∈ J},
    (tupleDomain x).2.subset (by
      rintro n ⟨h, _⟩
      exact (mem_tupleDomain x).mpr h)⟩

/-- Original label: `defn:identifier-cancel`.
The resolved index set is exactly the set specified in the thesis. -/
theorem mem_identifierIndices {X : Type u} {I : Type v} (id : X → I)
    (J : Set I) (x : Tuple X) (i : Fin x.length) :
    i.val ∈ (identifierIndices id J x : Set ℕ) ↔ id (x.entry i) ∈ J := by
  change (∃ h : i.val < x.length, id (x.entry ⟨i.val, h⟩) ∈ J) ↔ _
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.isLt, h⟩⟩

/-- Original label: `defn:identifier-cancel`.
The structural cancellation after resolving the requested identifier set.
Any venue authorization restriction determines which requests are admissible. -/
noncomputable def cancelIdentifiers {X : Type u} {I : Type v}
    (id : X → I) (J : Set I) (x : Tuple X) : Tuple X :=
  cancel x (identifierIndices id J x)

/-- Original label: `defn:identifier-cancel`.
The indices kept by this operation are exactly the input orders whose
identifiers are outside the requested set, preserving their original order. -/
theorem identifierCancellation_surviving_indices {X : Type u} {I : Type v}
    (id : X → I) (J : Set I) (x : Tuple X) (i : Fin x.length) :
    i.val ∈ (finiteSubsetDiff (tupleDomain x) (identifierIndices id J x) : Set ℕ) ↔
      id (x.entry i) ∉ J := by
  change (i.val ∈ (tupleDomain x : Set ℕ) ∧
    i.val ∉ (identifierIndices id J x : Set ℕ)) ↔ _
  rw [mem_identifierIndices]
  exact and_iff_right ((mem_tupleDomain x).mpr i.isLt)

/-- Original label: `defn:pairing`.
The increasing enumeration satisfies the literal repeated-minimum formula:
its next entry is the least element not among earlier entries. -/
theorem pairing_entry_isLeast_remaining {X : Type u} [LinearOrder X]
    (ξ : FiniteSubsets X) (i : Fin (pairing ξ).length) :
    IsLeast {a : X | a ∈ (ξ : Set X) ∧
      ¬ ∃ j : Fin (pairing ξ).length, j < i ∧ (pairing ξ).entry j = a}
      ((pairing ξ).entry i) := by
  have hstrict : StrictMono (fun j : Fin (pairing ξ).length => (pairing ξ).entry j) :=
    (FiniteSubsets.toFinset ξ).orderEmbOfFin rfl |>.strictMono
  constructor
  · refine ⟨pairing_entry_mem ξ i, ?_⟩
    rintro ⟨j, hji, heq⟩
    exact (ne_of_lt (hstrict hji)) heq
  · rintro a ⟨ha, hnot⟩
    obtain ⟨j, rfl⟩ := exists_pairing_entry_eq_of_mem ξ ha
    exact hstrict.monotone (le_of_not_gt (fun hji => hnot ⟨j, hji, rfl⟩))

/-- Original label: `rem:void-modification`.
Every modification whose indices miss the input domain is void, including
nonempty modification payloads. -/
theorem modify_eq_self_of_disjoint_indices {X : Type u} (x : Tuple X)
    (ξ : DistinctFiniteSubsets X)
    (h : Disjoint (DistinctFiniteSubsets.indexSet ξ : Set ℕ)
      (tupleDomain x : Set ℕ)) : modify x ξ = x := by
  cases x with
  | mk n f =>
      apply congrArg (fun g => (⟨n, g⟩ : Tuple X))
      funext i
      apply modificationValue_eq_default_of_not_exists
      intro hi
      exact Set.disjoint_left.mp h
        ((DistinctFiniteSubsets.mem_indexSet ξ).mpr hi)
        ((mem_tupleDomain _).mpr i.isLt)

/-- Original label: `rem:void-modification`.
The valid sorted-output clause for every void payload. Equality with the
input itself additionally requires that the sorting rule fix that input. -/
theorem sortedModify_void_eq_sort {X : Type u} [Preorder X]
    (σ : SortingRule X) (x : Tuple X) (ξ : DistinctFiniteSubsets X)
    (h : Disjoint (DistinctFiniteSubsets.indexSet ξ : Set ℕ)
      (tupleDomain x : Set ℕ)) :
    (sortedModify σ x ξ).val = σ.sort x := by
  change σ.sort (modify x ξ) = σ.sort x
  rw [modify_eq_self_of_disjoint_indices x ξ h]

/-- Original label: `rem:void-modification`.
The corrected final clause: a void sorted modification fixes any input
already fixed by the selected sorting rule. -/
theorem sortedModify_void_eq_self_of_fixed {X : Type u} [Preorder X]
    (σ : SortingRule X) (x : Tuple X) (ξ : DistinctFiniteSubsets X)
    (h : Disjoint (DistinctFiniteSubsets.indexSet ξ : Set ℕ)
      (tupleDomain x : Set ℕ)) (hfix : σ.sort x = x) :
    (sortedModify σ x ξ).val = x := (sortedModify_void_eq_sort σ x ξ h).trans hfix

/-- Original label: `rem:void-modification`.
Idempotence suffices when the input lies in the sorting rule's image. -/
theorem sortedModify_void_eq_self_of_mem_range {X : Type u} [Preorder X]
    (σ : SortingRule X) (x : Tuple X) (ξ : DistinctFiniteSubsets X)
    (h : Disjoint (DistinctFiniteSubsets.indexSet ξ : Set ℕ)
      (tupleDomain x : Set ℕ))
    (hid : ∀ y, σ.sort (σ.sort y) = σ.sort y) (hx : x ∈ Set.range σ.sort) :
    (sortedModify σ x ξ).val = x := by
  obtain ⟨y, rfl⟩ := hx
  exact sortedModify_void_eq_self_of_fixed σ _ ξ h (hid y)

/-- Original label: `defn:composite-actions`.
Appending scripts means finishing the first before starting the second. -/
theorem applyCompositeAction_concat {X : Type u} (x : Tuple X)
    (c d : Composite.CompositeAction X) :
    Composite.applyCompositeAction x (concat c d) =
      Composite.applyCompositeAction (Composite.applyCompositeAction x c) d := by
  change (tupleList (concat c d)).foldl Composite.applyAction x =
    (tupleList d).foldl Composite.applyAction ((tupleList c).foldl Composite.applyAction x)
  rw [tupleList_concat, List.foldl_append]

/-- Original label: `defn:composite-actions`.
The chapter's two-instruction example cancels input-state indices first and
then appends the submitted tuple. -/
theorem applyCompositeAction_cancel_then_add {X : Type u} (x y : Tuple X)
    (η : FiniteSubsets ℕ) :
    Composite.applyCompositeAction x
      ⟨2, ![Composite.MarketAction.cancel η, Composite.MarketAction.add y]⟩ =
      concat (cancel x η) y := by
  simp [Composite.applyCompositeAction, Composite.compositeActionList, List.ofFn_succ,
    Composite.applyAction]

/-- The product Borel sigma-algebra agrees with the Borel sigma-algebra of
the product topology when one metric factor is separable. -/
theorem emetricBorel_prod_of_separable_left {A : Type u} {B : Type v}
    [EMetricSpace A] [EMetricSpace B] [TopologicalSpace.SeparableSpace A] :
    emetricBorel (A × B) =
      @Prod.instMeasurableSpace A B (emetricBorel A) (emetricBorel B) := by
  letI : MeasurableSpace A := emetricBorel A
  letI : MeasurableSpace B := emetricBorel B
  letI : BorelSpace A := ⟨rfl⟩
  letI : BorelSpace B := ⟨rfl⟩
  exact BorelSpace.measurable_eq.symm

/-- Original label: `cor:sorted-operations-measurable`.
Sorted addition is measurable for the product of the factor Borel
sigma-algebras required by the source. -/
theorem measurable_sortedAdd_productBorel {X : Type u}
    [EMetricSpace X] [TopologicalSpace.SeparableSpace X] [Preorder X]
    (σ : SortingRule X) (hσ : IsMeasurableSortingRule σ) :
    @Measurable (Tuple X × Tuple X) (SortedTuple X)
      (@Prod.instMeasurableSpace (Tuple X) (Tuple X)
        (emetricBorel (Tuple X)) (emetricBorel (Tuple X)))
      (emetricBorel (SortedTuple X)) (fun p => sortedAdd σ p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) := emetricTopology (Tuple X)
  haveI : TopologicalSpace.SeparableSpace (Tuple X) :=
    TuplesMetricTopology.separableSpace
  rw [← emetricBorel_prod_of_separable_left]
  exact measurable_sortedAdd_emetricBorel σ hσ

/-- Original label: `cor:sorted-operations-measurable`.
The sorted cancellation clause with the actual product sigma-algebra. -/
theorem measurable_sortedCancel_productBorel {X : Type u}
    [EMetricSpace X] [TopologicalSpace.SeparableSpace X] [Preorder X]
    (σ : SortingRule X) (hσ : IsMeasurableSortingRule σ) :
    @Measurable (Tuple X × FiniteSubsets ℕ) (SortedTuple X)
      (@Prod.instMeasurableSpace (Tuple X) (FiniteSubsets ℕ)
        (emetricBorel (Tuple X)) (emetricBorel (FiniteSubsets ℕ)))
      (emetricBorel (SortedTuple X)) (fun p => sortedCancel σ p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) := emetricTopology (Tuple X)
  haveI : TopologicalSpace.SeparableSpace (Tuple X) :=
    TuplesMetricTopology.separableSpace
  rw [← emetricBorel_prod_of_separable_left]
  exact measurable_sortedCancel_emetricBorel σ hσ

/-- Original label: `cor:sorted-operations-measurable`.
The sorted modification clause with the actual product sigma-algebra. -/
theorem measurable_sortedModify_productBorel {X : Type u}
    [EMetricSpace X] [TopologicalSpace.SeparableSpace X] [Preorder X]
    (σ : SortingRule X) (hσ : IsMeasurableSortingRule σ) :
    @Measurable (Tuple X × DistinctFiniteSubsets X) (SortedTuple X)
      (@Prod.instMeasurableSpace (Tuple X) (DistinctFiniteSubsets X)
        (emetricBorel (Tuple X)) (emetricBorel (DistinctFiniteSubsets X)))
      (emetricBorel (SortedTuple X)) (fun p => sortedModify σ p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) := emetricTopology (Tuple X)
  haveI : TopologicalSpace.SeparableSpace (Tuple X) :=
    TuplesMetricTopology.separableSpace
  rw [← emetricBorel_prod_of_separable_left]
  exact measurable_sortedModify_emetricBorel σ hσ

end Thesis.Foundations.MarketActions.Alignment
