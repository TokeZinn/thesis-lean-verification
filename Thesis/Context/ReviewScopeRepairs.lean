import Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
import Thesis.Foundations.Stochastic.KernelHilbert
import Thesis.Foundations.MarketActions.Primitive

/-! # Scope repairs identified by the independent doctoral-source review

Two of the three repairs recorded here have since been absorbed by the primary
modules: `TuplesMetricTopology.sortedTuple_separableSpace` is stated for an
arbitrary partial order, and
`KernelHilbert.bijective_weakLinear_transport_hilbert_structure` assumes only
surjectivity. Those two names are kept below as aliases of the primary
declarations (the labels live on the primaries). The remaining repair,
`sortingRule_permutation_invariant`, is still proved here.
-/

noncomputable section
namespace Thesis.Foundations.ReviewScopeRepairs

open MarketRepresentation TuplesBasic TuplesSorting
open Stochastic.KernelHilbert
open MarketActions.Primitive

/-- Original label: `cor:unique-sorting-map-total-order`.
Both outputs are sorted and have the same multiplicities. Uniqueness of a
sorted representative therefore makes any sorting rule permutation invariant,
as in the source proof. -/
theorem sortingRule_permutation_invariant {X : Type*} [LinearOrder X]
    (σ : SortingRule X) (x : Tuple X) (π : FinitePermutation x.length) :
    σ.sort (permute x π) = σ.sort x := by
  apply sortedTuple_eq_of_tupleMultiset_eq (σ.sorted_sort _) (σ.sorted_sort _)
  rw [tupleMultiset_sort, tupleMultiset_sort, tupleMultiset_permute]

/-- Alias of `TuplesMetricTopology.sortedTuple_separableSpace` (the mapped
statement, item (v) of `thm:tuple-space-properties`), which is now stated for
any partial order; kept under its former name for interface stability. -/
alias sortedTuple_separableSpace_partial := TuplesMetricTopology.sortedTuple_separableSpace

/-- Alias of `KernelHilbert.bijective_weakLinear_transport_hilbert_structure`
(the mapped statement of `cor:bijective-weak-linear-transport-hilbert-structure`),
which now assumes surjectivity only; kept under its former name for interface
stability. -/
alias surjective_weakLinear_transport_hilbert_structure :=
  bijective_weakLinear_transport_hilbert_structure

end Thesis.Foundations.ReviewScopeRepairs
