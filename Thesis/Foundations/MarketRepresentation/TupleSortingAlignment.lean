import Thesis.Foundations.MarketActions.Primitive
import Thesis.Foundations.MarketRepresentation.FiniteRelationClosure

/-! # Statement-level bridges for tuple sorting

Thesis source: `1 - theoretical foundations/2_chapter_market_representations.tex`.
-/

namespace Thesis.Foundations.MarketRepresentation.TupleSortingAlignment

open TuplesBasic TuplesSorting
open Thesis.Foundations.MarketActions.Primitive

universe u
variable {X : Type u}

/--
Original block id:
`source:1 - theoretical foundations/2_chapter_market_representations.tex:985:rem:50`.
The literal positive-natural-valued tuple associated to a finite permutation.
Adding one translates the internal `Fin n` indices to the source's 1,...,n. -/
def positiveFinitePermutationTuple (π : FinitePermutations) : Tuple ℕ+ :=
  ⟨π.1, fun i => ⟨(π.2 i).val + 1, by omega⟩⟩

/--
Original block id:
`source:1 - theoretical foundations/2_chapter_market_representations.tex:985:rem:50`.
-/
theorem positiveFinitePermutationTuple_injective :
    Function.Injective positiveFinitePermutationTuple := by
  rintro ⟨m, π⟩ ⟨n, ρ⟩ h
  have hlen : m = n := congrArg Tuple.length h
  subst n
  have hfun : (fun i : Fin m => (⟨(π i).val + 1, by omega⟩ : ℕ+)) =
      (fun i : Fin m => (⟨(ρ i).val + 1, by omega⟩ : ℕ+)) := by
    injection h with hfun
  congr
  ext i
  have hi := congrArg PNat.val (congrFun hfun i)
  simpa using hi

/--
Original block id:
`source:1 - theoretical foundations/2_chapter_market_representations.tex:985:rem:50`.
The permutation tuples form a proper subset: the length-one tuple (2) is not
a permutation of {1}. -/
theorem positiveFinitePermutationTuple_range_proper :
    Set.range positiveFinitePermutationTuple ⊂ (Set.univ : Set (Tuple ℕ+)) := by
  refine Set.ssubset_univ_iff.mpr ?_
  intro hfull
  have hmem : (⟨1, fun _ => 2⟩ : Tuple ℕ+) ∈ Set.range positiveFinitePermutationTuple :=
    hfull.symm ▸ Set.mem_univ _
  obtain ⟨⟨n, π⟩, hπ⟩ := hmem
  have hn : n = 1 := congrArg Tuple.length hπ
  subst n
  have hfun : (fun i : Fin 1 => (⟨(π i).val + 1, by omega⟩ : ℕ+)) =
      (fun _ : Fin 1 => (⟨2, by decide⟩ : ℕ+)) := by
    injection hπ with hfun
  have hi := congrArg PNat.val (congrFun hfun 0)
  have hzero : π 0 = 0 := Subsingleton.elim _ _
  simp [hzero] at hi

/-! `sortingRule_fixes_sorted` (the "sorting fixes sorted tuples" form of
`cor:unique-sorting-map-total-order`) now lives in `TuplesSorting`, so that
`MarketActions.Primitive.sortedCancel_eq_cancel` can cite it as the thesis
proof of `cor:cancel-closure-sorted` does. It is re-exported here so the
qualified name `TupleSortingAlignment.sortingRule_fixes_sorted` keeps
resolving. -/
export Thesis.Foundations.MarketRepresentation.TuplesSorting (sortingRule_fixes_sorted)

/-- Original label: `cor:components-totally-ordered-by-arrival-index`.
All order axioms for the exact arrival-index relation. -/
theorem segmentArrivalLE_isLinearOrder [Preorder X] (x : Tuple X) :
    IsLinearOrder (ConnectedSegment x) (SegmentArrivalLE x) where
  refl _ := le_rfl
  trans _ _ _ := le_trans
  antisymm _ _ := segmentArrivalLE_antisymm x
  total := segmentArrivalLE_total x

/-- Original label: `defn:comparability-components`.
The number of connected components cannot exceed the number of indices. -/
theorem segment_count_le_length [Preorder X] (x : Tuple X) :
    (segmentListByArrival x).length ≤ x.length := by
  have hnodup : ((segmentListByArrival x).map (segmentArrivalIndex x)).Nodup :=
    (nodup_segmentListByArrival x).map (segmentArrivalIndex_injective x)
  simpa using hnodup.length_le_card

/--
Original block id:
`source:1 - theoretical foundations/2_chapter_market_representations.tex:1550:rem:77`.
Concatenation need not commute, as witnessed by the singleton tuples (0)
and (1). -/
theorem tuple_concat_not_commutative :
    concat (⟨1, fun _ => 0⟩ : Tuple ℕ) ⟨1, fun _ => 1⟩ ≠
      concat (⟨1, fun _ => 1⟩ : Tuple ℕ) ⟨1, fun _ => 0⟩ := by
  intro h
  have hfun : Fin.append (fun _ : Fin 1 => (0 : ℕ)) (fun _ : Fin 1 => 1) =
      Fin.append (fun _ : Fin 1 => (1 : ℕ)) (fun _ : Fin 1 => 0) := by
    injection h with hfun
  have hi := congrFun hfun 0
  change (0 : ℕ) = 1 at hi
  exact Nat.zero_ne_one hi

end Thesis.Foundations.MarketRepresentation.TupleSortingAlignment
