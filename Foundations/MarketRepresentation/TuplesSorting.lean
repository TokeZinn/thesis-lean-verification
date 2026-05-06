import Foundations.MarketRepresentation.TuplesBasic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Extension.Linear

/-!
# Market Representation: Sorting Tuples

Blueprint module for
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Planned formal content:

* sorting permutations;
* existence of a sorting permutation;
* sorting rules;
* uniqueness/idempotency where applicable;
* index comparability relation;
* reflexive-transitive closure on finite index sets;
* connectivity relation, connected segments, segment arrival indices;
* minimum sorting rule.

Lean note: for total orders, mathlib's finite sorting APIs may prove many
existence statements. For partial orders, the thesis construction via connected
segments should be followed closely.
-/

namespace Thesis
namespace Foundations
namespace MarketRepresentation
namespace TuplesSorting

open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets

universe u v

variable {X : Type u}

/-! ## Sorting Permutations -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:sorting-permutations`.

Informal statement: a finite permutation sorts a tuple when the permuted tuple
is sorted.
-/
def IsSortingPermutation [Preorder X] (x : Tuple X)
    (π : FinitePermutation x.length) : Prop :=
  IsSorted (permute x π)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: set `\mathscr{P}_{\bm{x}}` in
`defn:sorting-permutations`.

Informal statement: the type of sorting permutations for a fixed tuple.
-/
abbrev SortingPermutations [Preorder X] (x : Tuple X) : Type :=
  {π : FinitePermutation x.length // IsSortingPermutation x π}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: direct consequence of `defn:sorting-permutations`.

Informal statement: applying a sorting permutation gives a sorted tuple.
-/
theorem sortingPermutation_isSorted [Preorder X] (x : Tuple X)
    (π : SortingPermutations x) : IsSorted (permute x π.1) :=
  π.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: identity case for `defn:sorting-permutations`.

Informal statement: if a tuple is already sorted, then the identity
permutation is a sorting permutation for it.
-/
def identitySortingPermutation [Preorder X] (x : Tuple X) (hx : IsSorted x) :
    SortingPermutations x :=
  ⟨Equiv.refl (Fin x.length), by
    simpa [IsSortingPermutation, permute_refl x] using hx⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: construction inside `thm:permutation-exists`.

Informal statement: choose a sorting permutation by extending the partial
order to a linear order, then sorting the finite tuple with respect to that
linear extension.

Lean strategy / thesis relation note: this is the thesis proof with two mathlib implementations
plugged in: `LinearExtension X` is Szpilrajn's extension theorem, and
`Tuple.sort` is mathlib's recursive finite sorting permutation.
-/
noncomputable def extensionSortingPermutation [PartialOrder X] (x : Tuple X) :
    FinitePermutation x.length :=
  _root_.Tuple.sort (fun i : Fin x.length =>
    (Tuple.entry x i : LinearExtension X))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `thm:permutation-exists`.

Informal statement: every tuple over a partially ordered set has a sorting
permutation.

Lean strategy / thesis relation note: the proof mirrors the thesis. Sorting by the Szpilrajn linear
extension gives a tuple monotone in the extension. If a later entry were
strictly smaller in the original partial order, the extension property would
force both extension inequalities, contradicting antisymmetry.
-/
theorem extensionSortingPermutation_isSorting [PartialOrder X] (x : Tuple X) :
    IsSortingPermutation x (extensionSortingPermutation x) := by
  let f : Fin x.length → LinearExtension X := fun i =>
    (Tuple.entry x i : LinearExtension X)
  have hmono : Monotone (f ∘ _root_.Tuple.sort f) :=
    _root_.Tuple.monotone_sort f
  change ∀ i j : Fin x.length, i ≤ j →
    ¬ Tuple.entry x (extensionSortingPermutation x j) <
      Tuple.entry x (extensionSortingPermutation x i)
  intro i j hij hlt
  have hle_forward :
      (Tuple.entry x (extensionSortingPermutation x i) : LinearExtension X) ≤
        (Tuple.entry x (extensionSortingPermutation x j) : LinearExtension X) := by
    simpa [f, extensionSortingPermutation, Function.comp_def] using hmono hij
  have hle_original :
      Tuple.entry x (extensionSortingPermutation x j) ≤
        Tuple.entry x (extensionSortingPermutation x i) :=
    le_of_lt hlt
  have hle_backward :
      (Tuple.entry x (extensionSortingPermutation x j) : LinearExtension X) ≤
        (Tuple.entry x (extensionSortingPermutation x i) : LinearExtension X) :=
    (toLinearExtension (α := X)).monotone hle_original
  have heq_ext :
      (Tuple.entry x (extensionSortingPermutation x i) : LinearExtension X) =
        (Tuple.entry x (extensionSortingPermutation x j) : LinearExtension X) :=
    le_antisymm hle_forward hle_backward
  have heq :
      Tuple.entry x (extensionSortingPermutation x i) =
        Tuple.entry x (extensionSortingPermutation x j) := heq_ext
  rw [heq] at hlt
  exact lt_irrefl (Tuple.entry x (extensionSortingPermutation x j)) hlt

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `thm:permutation-exists`.

Informal statement: the type of sorting permutations for a tuple is nonempty.
-/
theorem sortingPermutation_exists [PartialOrder X] (x : Tuple X) :
    Nonempty (SortingPermutations x) :=
  ⟨⟨extensionSortingPermutation x,
    extensionSortingPermutation_isSorting x⟩⟩

/-! ## Sorting Rules -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:sorting-map`.

Informal statement: a sorting rule sends every tuple to a sorted tuple and
does so by applying a finite permutation of that tuple's domain.

Lean strategy / thesis relation note: the thesis gives the codomain as the subtype
`\mathscr{S}(X,\preceq)`. The Lean structure stores a plain tuple-valued
function plus proofs of sortedness and permutation preservation; the associated
subtype-valued map is `SortingRule.toSortedTuple`.
-/
structure SortingRule (X : Type u) [Preorder X] where
  sort : Tuple X → Tuple X
  sorted_sort : ∀ x, IsSorted (sort x)
  exists_perm : ∀ x, ∃ π : FinitePermutation x.length, sort x = permute x π

namespace SortingRule

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: codomain form of `defn:sorting-map`.

Informal statement: a sorting rule may be viewed as a function into the type
of sorted tuples.
-/
def toSortedTuple [Preorder X] (σ : SortingRule X) (x : Tuple X) : SortedTuple X :=
  ⟨σ.sort x, σ.sorted_sort x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: permutation condition in equation `eq:sort-permute`.

Informal statement: the output of a sorting rule is a permuted copy of the
input tuple.
-/
theorem exists_sortingPermutation [Preorder X] (σ : SortingRule X) (x : Tuple X) :
    ∃ π : SortingPermutations x, σ.sort x = permute x π.1 := by
  rcases σ.exists_perm x with ⟨π, hπ⟩
  refine ⟨⟨π, ?_⟩, hπ⟩
  change IsSorted (permute x π)
  rw [← hπ]
  exact σ.sorted_sort x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: sortedness consequence of `defn:sorting-map`.

Informal statement: every output of a sorting rule is sorted.
-/
theorem isSorted_sort [Preorder X] (σ : SortingRule X) (x : Tuple X) :
    IsSorted (σ.sort x) :=
  σ.sorted_sort x

end SortingRule

/-! ## Existence of Sorting Rules -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: choice function in the proof of `thm:sorting-exists`.

Informal statement: choose one sorting permutation for each tuple.

Lean strategy / thesis relation note: this is the formal counterpart of the thesis' use of the
axiom of choice after proving `\mathscr{P}_{\bm{x}}` is nonempty.

Lean strategy / thesis strategy note: this declaration should be archived together with
`choiceSortingRule` and `sortingRule_exists`; it is the selected-permutation
piece of the thesis proof, not a standalone thesis result.
-/
noncomputable def chosenSortingPermutation [PartialOrder X] (x : Tuple X) :
    SortingPermutations x :=
  Classical.choice (sortingPermutation_exists x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: construction in `thm:sorting-exists`.

Informal statement: the choice of one sorting permutation per tuple defines a
sorting rule.

Lean strategy / thesis strategy note: this is the construction used by the theorem
`sortingRule_exists`. The source prose about choice above is inside a Lean doc
comment; if it appears as raw code in a trace bundle, that is an extraction
artifact rather than a Lean source issue.
-/
noncomputable def choiceSortingRule (X : Type u) [PartialOrder X] :
    SortingRule X where
  sort x := permute x (chosenSortingPermutation x).1
  sorted_sort x := (chosenSortingPermutation x).2
  exists_perm x := ⟨(chosenSortingPermutation x).1, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `thm:sorting-exists`.

Informal statement: every partially ordered space has at least one sorting
rule.
-/
theorem sortingRule_exists (X : Type u) [PartialOrder X] :
    Nonempty (SortingRule X) :=
  ⟨choiceSortingRule X⟩

/-! ## Uniqueness and Idempotency in Total Orders -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary step in `cor:unique-and-idempotent-sort`.

Informal statement: applying a finite permutation to `Fin n` only permutes
the canonical list of indices.
-/
theorem list_finRange_perm_equiv {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (List.map π (List.finRange n)).Perm (List.finRange n) := by
  rw [List.perm_iff_count]
  intro a
  have hnodup_map : (List.map π (List.finRange n)).Nodup :=
    (List.nodup_finRange n).map π.injective
  have hmem_map : a ∈ List.map π (List.finRange n) := by
    simp only [List.mem_map, List.mem_finRange, true_and]
    exact ⟨π.symm a, by simp⟩
  have hleft : List.count a (List.map π (List.finRange n)) = 1 :=
    List.count_eq_one_of_mem hnodup_map hmem_map
  have hright : List.count a (List.finRange n) = 1 :=
    List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a)
  rw [hleft, hright]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary step in `cor:unique-and-idempotent-sort`.

Informal statement: applying a finite permutation to a fixed-length tuple
preserves its list of entries up to list permutation.

Lean strategy / thesis relation note: this is the multiplicity-preservation line in the thesis
proof, expressed through `List.Perm`.
-/
theorem list_ofFn_perm_comp_equiv {n : ℕ} (f : Fin n → X)
    (π : Equiv.Perm (Fin n)) :
    (List.ofFn (fun i => f (π i))).Perm (List.ofFn f) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  simpa [List.map_map, Function.comp_def] using
    (list_finRange_perm_equiv π).map f

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary step in `cor:unique-and-idempotent-sort`.

Informal statement: a sorted tuple over a total order gives a pairwise
increasing list of entries.
-/
theorem isSorted_pairwise_ofFn [LinearOrder X] (x : Tuple X)
    (hx : IsSorted x) :
    List.Pairwise (fun a b : X => a ≤ b)
      (List.ofFn fun i => Tuple.entry x i) := by
  cases x with
  | mk n f =>
      change List.Pairwise (fun a b : X => a ≤ b) (List.ofFn f)
      rw [List.pairwise_iff_get]
      intro i j hij
      let i' : Fin n := ⟨i.1, by simpa using i.2⟩
      let j' : Fin n := ⟨j.1, by simpa using j.2⟩
      have hle : i' ≤ j' := hij.le
      have hnlt := hx i' j' hle
      have hget_i : (List.ofFn f).get i = f i' := by
        simp [i']
      have hget_j : (List.ofFn f).get j = f j' := by
        simp [j']
      rw [hget_i, hget_j]
      exact le_of_not_gt hnlt

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: uniqueness part of `cor:unique-and-idempotent-sort`.

Informal statement: over a total order, any two sorting permutations of the
same tuple produce the same sorted tuple.

Lean strategy / thesis relation note: the thesis argues by the first index at which two sorted
permuted tuples differ. Lean uses the equivalent finite-list theorem:
pairwise sorted lists with the same multiset of entries are equal.
-/
theorem sortedPermutations_eq_of_linearOrder [LinearOrder X]
    (x : Tuple X) (π ρ : SortingPermutations x) :
    permute x π.1 = permute x ρ.1 := by
  cases x with
  | mk n f =>
      have hsπ : List.Pairwise (fun a b : X => a ≤ b)
          (List.ofFn (fun i => f (π.1 i))) := by
        simpa [IsSortingPermutation, permute, Tuple.entry] using
          isSorted_pairwise_ofFn (X := X)
            (permute (Sigma.mk n f : Tuple X) π.1) π.2
      have hsρ : List.Pairwise (fun a b : X => a ≤ b)
          (List.ofFn (fun i => f (ρ.1 i))) := by
        simpa [IsSortingPermutation, permute, Tuple.entry] using
          isSorted_pairwise_ofFn (X := X)
            (permute (Sigma.mk n f : Tuple X) ρ.1) ρ.2
      have hperm : (List.ofFn (fun i => f (π.1 i))).Perm
          (List.ofFn (fun i => f (ρ.1 i))) :=
        (list_ofFn_perm_comp_equiv f π.1).trans
          (list_ofFn_perm_comp_equiv f ρ.1).symm
      have hlist : List.ofFn (fun i => f (π.1 i)) =
          List.ofFn (fun i => f (ρ.1 i)) :=
        List.Perm.eq_of_pairwise
          (by intro a b _ _ hab hba; exact le_antisymm hab hba)
          hsπ hsρ hperm
      have hfun : (fun i => f (π.1 i)) = (fun i => f (ρ.1 i)) :=
        List.ofFn_inj.mp hlist
      change (Sigma.mk n (fun i => f (π.1 i)) : Tuple X) =
        Sigma.mk n (fun i => f (ρ.1 i))
      exact congrArg (fun g => (Sigma.mk n g : Tuple X)) hfun

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: uniqueness part of `cor:unique-and-idempotent-sort`.

Informal statement: over a total order, all sorting rules have the same
underlying tuple-valued function.

Lean strategy / thesis relation note: Lean states uniqueness extensionally for the `sort` field,
since two structures with proposition-valued proof fields need not be
definitionally identical as records.
-/
theorem sortingRule_sort_unique_of_linearOrder [LinearOrder X]
    (σ τ : SortingRule X) :
    σ.sort = τ.sort := by
  funext x
  rcases σ.exists_sortingPermutation x with ⟨π, hπ⟩
  rcases τ.exists_sortingPermutation x with ⟨ρ, hρ⟩
  rw [hπ, hρ]
  exact sortedPermutations_eq_of_linearOrder x π ρ

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: idempotency part of `cor:unique-and-idempotent-sort`.

Informal statement: over a total order, sorting an already sorted output does
nothing.
-/
theorem sortingRule_idempotent_of_linearOrder [LinearOrder X]
    (σ : SortingRule X) (x : Tuple X) :
    σ.sort (σ.sort x) = σ.sort x := by
  let y := σ.sort x
  rcases σ.exists_sortingPermutation y with ⟨π, hπ⟩
  let ι : SortingPermutations y := identitySortingPermutation y (σ.sorted_sort x)
  have hunique : permute y π.1 = permute y ι.1 :=
    sortedPermutations_eq_of_linearOrder y π ι
  rw [hπ]
  simpa [ι, identitySortingPermutation, permute_refl] using hunique

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: auxiliary consequence of
`cor:unique-and-idempotent-sort`, used in `exmp:sort-discont`.

Informal statement: over a total order, any sorting rule fixes a tuple that is
already sorted.

Lean strategy / thesis relation note: the thesis says the sorting map is unique in a total order.
Lean proves the fixed-point statement by comparing the sorting permutation
chosen by `σ` with the identity sorting permutation.

Lean strategy / thesis strategy note: this is only the fixed-point helper used in the
discontinuity example. The full formalization of `exmp:sort-discont` is in
`TuplesMeasurableSorting.lean`, including the lexicographic real-plane
sequence, its convergence, the unsorted limit, and the discontinuity theorem.
-/
theorem sortingRule_sort_eq_self_of_isSorted [LinearOrder X]
    (σ : SortingRule X) {x : Tuple X} (hx : IsSorted x) :
    σ.sort x = x := by
  rcases σ.exists_sortingPermutation x with ⟨π, hπ⟩
  let ι : SortingPermutations x := identitySortingPermutation x hx
  have hunique : permute x π.1 = permute x ι.1 :=
    sortedPermutations_eq_of_linearOrder x π ι
  rw [hπ]
  simpa [ι, identitySortingPermutation, permute_refl] using hunique

/-! ## Connected Segments -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:index-comparable`.

Informal statement: two tuple indices are immediately comparable when their
entries are comparable in the ambient preorder.

Lean strategy / thesis relation note: the thesis writes the tuple domain as a finite subset of
`\mathbb{N}`. Here the domain is `Fin x.length`; the relation is otherwise
the same disjunction `x i ≤ x j ∨ x j ≤ x i`.
-/
def IndexComparable [Preorder X] (x : Tuple X)
    (i j : Fin x.length) : Prop :=
  Tuple.entry x i ≤ Tuple.entry x j ∨ Tuple.entry x j ≤ Tuple.entry x i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: basic property of `defn:index-comparable`.

Informal statement: immediate comparability is reflexive.
-/
theorem indexComparable_refl [Preorder X] (x : Tuple X)
    (i : Fin x.length) : IndexComparable x i i :=
  Or.inl le_rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: basic property of `defn:index-comparable`.

Informal statement: immediate comparability is symmetric.
-/
theorem indexComparable_symm [Preorder X] (x : Tuple X)
    {i j : Fin x.length} :
    IndexComparable x i j → IndexComparable x j i := by
  rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:reflexive-transitive-closure`.

Informal statement: the reflexive-transitive closure of a relation collects
all pairs connected by a finite path of relation steps.

Lean strategy / thesis relation note: mathlib's `Relation.ReflTransGen` is the inductive version of
the thesis formula `Δ ∪ ⋃ₙ Rⁿ`. This is definitionally path-based rather than
set-union-based, but it proves the same reflexive and transitive closure
principle and is the standard Lean representation.
-/
abbrev ReflexiveTransitiveClosure {α : Type u} (R : α → α → Prop) :
    α → α → Prop :=
  Relation.ReflTransGen R

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:connectivity-relation`.

Informal statement: two indices of a tuple are connected when one can move
from one to the other through a finite chain of immediately comparable
indices.
-/
def IndexConnected [Preorder X] (x : Tuple X) :
    Fin x.length → Fin x.length → Prop :=
  ReflexiveTransitiveClosure (IndexComparable x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: reflexive part of `prop:sim-equivalence`.
-/
theorem indexConnected_refl [Preorder X] (x : Tuple X)
    (i : Fin x.length) : IndexConnected x i i :=
  Relation.ReflTransGen.refl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: one-step chain used in `prop:sim-equivalence`.
-/
theorem indexConnected_of_indexComparable [Preorder X] (x : Tuple X)
    {i j : Fin x.length} (hij : IndexComparable x i j) :
    IndexConnected x i j :=
  Relation.ReflTransGen.single hij

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: transitive part of `prop:sim-equivalence`.
-/
theorem indexConnected_trans [Preorder X] (x : Tuple X)
    {i j k : Fin x.length} :
    IndexConnected x i j → IndexConnected x j k → IndexConnected x i k :=
  Relation.ReflTransGen.trans

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: symmetric part of `prop:sim-equivalence`.

Informal statement: because immediate comparability is symmetric, reversing a
finite comparability chain gives a chain in the opposite direction.
-/
theorem indexConnected_symm [Preorder X] (x : Tuple X)
    {i j : Fin x.length} :
    IndexConnected x i j → IndexConnected x j i := by
  intro h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hconn hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (indexComparable_symm x hstep)) ih

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `prop:sim-equivalence`.

Informal statement: the connectivity relation on tuple indices is an
equivalence relation.
-/
def connectivitySetoid [Preorder X] (x : Tuple X) :
    Setoid (Fin x.length) where
  r := IndexConnected x
  iseqv := ⟨indexConnected_refl x, indexConnected_symm x,
    indexConnected_trans x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:segments`.

Informal statement: the connected segments of a tuple are the equivalence
classes of the connectivity relation on its domain.

Lean strategy / thesis relation note: the thesis represents segments as finite subsets of the tuple
graph. Lean first represents the indexing classes as a quotient type; below,
`segmentGraph` recovers the graph-subset formulation.
-/
abbrev ConnectedSegment [Preorder X] (x : Tuple X) :=
  Quotient (connectivitySetoid x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: class membership implicit in `defn:segments`.

Informal statement: the connected segment containing index `i`.
-/
def indexSegment [Preorder X] (x : Tuple X) (i : Fin x.length) :
    ConnectedSegment x :=
  Quotient.mk (connectivitySetoid x) i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: index part of `defn:segments`.

Informal statement: the set of indices belonging to a connected segment.
-/
def segmentIndices [Preorder X] (x : Tuple X) (K : ConnectedSegment x) :
    Set (Fin x.length) :=
  {i | indexSegment x i = K}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: quotient-class interpretation of `defn:segments`.

Informal statement: two tuple indices are connected exactly when they lie in
the same connected segment.

Lean strategy / thesis relation note: the thesis treats this as the defining property of equivalence
classes. Lean's connected segments are quotient classes, so the proof is the
standard `Quotient.sound`/`Quotient.exact` bridge.
-/
theorem indexConnected_iff_same_segment [Preorder X] (x : Tuple X)
    (i j : Fin x.length) :
    IndexConnected x i j ↔ indexSegment x i = indexSegment x j := by
  constructor
  · intro hij
    exact Quotient.sound hij
  · intro hseg
    exact Quotient.exact hseg

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: membership interpretation of `defn:segments`.

Informal statement: if two indices belong to the same connected segment, then
they are connected by a finite chain of immediately comparable indices.
-/
theorem indexConnected_of_mem_same_segment [Preorder X] (x : Tuple X)
    {K : ConnectedSegment x} {i j : Fin x.length}
    (hi : i ∈ segmentIndices x K) (hj : j ∈ segmentIndices x K) :
    IndexConnected x i j := by
  exact (indexConnected_iff_same_segment x i j).mpr (hi.trans hj.symm)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: membership interpretation of `defn:segments`.

Informal statement: membership in a connected segment can be read as equality
with the quotient class of that index.
-/
@[simp] theorem mem_segmentIndices_iff [Preorder X] (x : Tuple X)
    (K : ConnectedSegment x) (i : Fin x.length) :
    i ∈ segmentIndices x K ↔ indexSegment x i = K :=
  Iff.rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: tuple graph used in `defn:segments`.

Informal statement: the graph of a tuple, written with Lean's finite index
domain.
-/
def tupleGraph (x : Tuple X) : Set (Fin x.length × X) :=
  {p | p.2 = Tuple.entry x p.1}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:segments`.

Informal statement: the graph subset corresponding to one connected segment.
-/
def segmentGraph [Preorder X] (x : Tuple X) (K : ConnectedSegment x) :
    Set (Fin x.length × X) :=
  {p | indexSegment x p.1 = K ∧ p.2 = Tuple.entry x p.1}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: bridge from `defn:segments` to
`defn:sorting-finite-sets`.

Informal statement: a connected segment of a tuple may be viewed as a
distinct finite subset of `ℕ × X`, so the distinct-finite-set sorting map can
be applied to it.

Lean strategy / thesis relation note: the thesis writes segment graph points as `(i, x(i))`.
Lean first indexes the tuple by `Fin x.length`; the segment distinct finite
set stores the underlying natural index `i.1`.
-/
noncomputable def segmentDistinctFiniteSet [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) : DistinctFiniteSubsets X := by
  classical
  let point : {i : Fin x.length // i ∈ segmentIndices x K} → IndexAugmented X :=
    fun i => IndexAugmented.mk i.1.1 (Tuple.entry x i.1)
  let s : FiniteSets.FiniteSubsets (IndexAugmented X) :=
    ⟨Set.range point, Set.finite_range point⟩
  have hdistinct : HasDistinctIndices s := by
    intro n a b ha hb
    rcases ha with ⟨i, hi⟩
    rcases hb with ⟨j, hj⟩
    have hiidx : i.1.1 = n := by
      simpa [point] using congrArg IndexAugmented.index hi
    have hjidx : j.1.1 = n := by
      simpa [point] using congrArg IndexAugmented.index hj
    have hij : i.1 = j.1 := Fin.ext (hiidx.trans hjidx.symm)
    have hia : Tuple.entry x i.1 = a := by
      simpa [point] using congrArg IndexAugmented.value hi
    have hjb : Tuple.entry x j.1 = b := by
      simpa [point] using congrArg IndexAugmented.value hj
    calc
      a = Tuple.entry x i.1 := hia.symm
      _ = Tuple.entry x j.1 := by rw [hij]
      _ = b := hjb
  exact ⟨s, hdistinct⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: membership form of the bridge from `defn:segments` to
`defn:sorting-finite-sets`.

Informal statement: the points of the distinct finite set associated to a
segment are exactly the tuple graph points whose indices lie in that segment.
-/
theorem mem_segmentDistinctFiniteSet [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) {p : IndexAugmented X} :
    p ∈ ((segmentDistinctFiniteSet (X := X) x K).1 : Set (IndexAugmented X)) ↔
      ∃ i : Fin x.length, i ∈ segmentIndices x K ∧
        p = IndexAugmented.mk i.1 (Tuple.entry x i) := by
  constructor
  · intro hp
    change p ∈ Set.range
      (fun i : {i : Fin x.length // i ∈ segmentIndices x K} =>
        IndexAugmented.mk i.1.1 (Tuple.entry x i.1)) at hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i.1, i.2, hi.symm⟩
  · rintro ⟨i, hiK, rfl⟩
    change IndexAugmented.mk i.1 (Tuple.entry x i) ∈ Set.range
      (fun i : {i : Fin x.length // i ∈ segmentIndices x K} =>
        IndexAugmented.mk i.1.1 (Tuple.entry x i.1))
    exact ⟨⟨i, hiK⟩, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: same-segment part of `prop:segments-partition-incomp`.

Informal statement: two graph points in the same connected segment come from
indices that are connected in the original tuple.

Lean strategy / thesis relation note: the thesis moves freely between a segment as an equivalence
class and as a subset of the tuple graph. Lean records the two underlying
indices explicitly.

Lean strategy / thesis strategy note: this is a bridge lemma for
`prop:segments-partition-incomp`. The source prose above is inside this doc
comment; if an audit copy shows it as raw text, the issue is in archive
extraction, not in the Lean module.
-/
theorem indexConnected_of_mem_segmentDistinctFiniteSet [Preorder X]
    (x : Tuple X) {K : ConnectedSegment x} {p q : IndexAugmented X}
    (hp : p ∈ ((segmentDistinctFiniteSet (X := X) x K).1 :
      Set (IndexAugmented X)))
    (hq : q ∈ ((segmentDistinctFiniteSet (X := X) x K).1 :
      Set (IndexAugmented X))) :
    ∃ i j : Fin x.length,
      p = IndexAugmented.mk i.1 (Tuple.entry x i) ∧
      q = IndexAugmented.mk j.1 (Tuple.entry x j) ∧
      IndexConnected x i j := by
  rcases (mem_segmentDistinctFiniteSet (X := X) x K).mp hp with
    ⟨i, hiK, hp_eq⟩
  rcases (mem_segmentDistinctFiniteSet (X := X) x K).mp hq with
    ⟨j, hjK, hq_eq⟩
  refine ⟨i, j, hp_eq, hq_eq, ?_⟩
  exact indexConnected_of_mem_same_segment (X := X) x hiK hjK

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: incomparability part of `prop:segments-partition-incomp`.

Informal statement: graph points in two distinct connected segments have
incomparable values.

Lean strategy / thesis relation note: this is the value-level form needed when the minimum-sort
construction concatenates segment blocks. The earlier quotient statement is
about indices; this theorem projects it to the stored tuple values.
-/
theorem not_comparable_of_mem_distinct_segmentDistinctFiniteSet [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} (hKL : K ≠ L)
    {p q : IndexAugmented X}
    (hp : p ∈ ((segmentDistinctFiniteSet (X := X) x K).1 :
      Set (IndexAugmented X)))
    (hq : q ∈ ((segmentDistinctFiniteSet (X := X) x L).1 :
      Set (IndexAugmented X))) :
    ¬ (IndexAugmented.value p ≤ IndexAugmented.value q ∨
      IndexAugmented.value q ≤ IndexAugmented.value p) := by
  intro hcomp
  rcases (mem_segmentDistinctFiniteSet (X := X) x K).mp hp with
    ⟨i, hiK, hp_eq⟩
  rcases (mem_segmentDistinctFiniteSet (X := X) x L).mp hq with
    ⟨j, hjL, hq_eq⟩
  have hij : IndexComparable x i j := by
    rcases hcomp with hle | hle
    · exact Or.inl (by simpa [hp_eq, hq_eq] using hle)
    · exact Or.inr (by simpa [hp_eq, hq_eq] using hle)
  have hseg : indexSegment x i = indexSegment x j :=
    Quotient.sound (indexConnected_of_indexComparable x hij)
  exact hKL (hiK.symm.trans (hseg.trans hjL))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cover part of `prop:segments-partition-incomp`.

Informal statement: every tuple-graph point belongs to the segment determined
by its index.
-/
theorem tupleGraph_subset_segmentUnion [Preorder X] (x : Tuple X) :
    tupleGraph x ⊆ ⋃ K : ConnectedSegment x, segmentGraph x K := by
  intro p hp
  exact Set.mem_iUnion.mpr
    ⟨indexSegment x p.1, by exact ⟨rfl, hp⟩⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cover part of `prop:segments-partition-incomp`.

Informal statement: the union of the connected segments is exactly the tuple
graph.
-/
theorem segmentUnion_eq_tupleGraph [Preorder X] (x : Tuple X) :
    (⋃ K : ConnectedSegment x, segmentGraph x K) = tupleGraph x := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨K, hK⟩
    exact hK.2
  · exact tupleGraph_subset_segmentUnion x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: disjointness part of `prop:segments-partition-incomp`.

Informal statement: distinct connected segments have disjoint index sets.
-/
theorem segmentIndices_disjoint_of_ne [Preorder X] (x : Tuple X)
    {K L : ConnectedSegment x} (hKL : K ≠ L) :
    Disjoint (segmentIndices x K) (segmentIndices x L) := by
  rw [Set.disjoint_left]
  intro i hi hL
  exact hKL (hi.symm.trans hL)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: disjointness part of `prop:segments-partition-incomp`.

Informal statement: distinct connected segments have disjoint graph subsets.
-/
theorem segmentGraph_disjoint_of_ne [Preorder X] (x : Tuple X)
    {K L : ConnectedSegment x} (hKL : K ≠ L) :
    Disjoint (segmentGraph x K) (segmentGraph x L) := by
  rw [Set.disjoint_left]
  intro p hp hL
  exact hKL (hp.1.symm.trans hL.1)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: incomparability part of `prop:segments-partition-incomp`.

Informal statement: indices in distinct connected segments are not
immediately comparable.
-/
theorem not_indexComparable_of_distinct_segments [Preorder X] (x : Tuple X)
    {K L : ConnectedSegment x} (hKL : K ≠ L)
    {i j : Fin x.length}
    (hi : i ∈ segmentIndices x K) (hj : j ∈ segmentIndices x L) :
    ¬ IndexComparable x i j := by
  intro hij
  have hseg : indexSegment x i = indexSegment x j :=
    Quotient.sound (indexConnected_of_indexComparable x hij)
  exact hKL (hi.symm.trans (hseg.trans hj))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: incomparability part of `prop:segments-partition-incomp`.

Informal statement: points in distinct connected graph segments have
incomparable tuple entries.
-/
theorem segmentGraph_incomparable_of_ne [Preorder X] (x : Tuple X)
    {K L : ConnectedSegment x} (hKL : K ≠ L)
    {p q : Fin x.length × X}
    (hp : p ∈ segmentGraph x K) (hq : q ∈ segmentGraph x L) :
    ¬ (p.2 ≤ q.2 ∨ q.2 ≤ p.2) := by
  intro hcomp
  have hij : IndexComparable x p.1 q.1 := by
    rcases hcomp with h | h
    · exact Or.inl (by simpa [hp.2, hq.2] using h)
    · exact Or.inr (by simpa [hp.2, hq.2] using h)
  exact not_indexComparable_of_distinct_segments x hKL hp.1 hq.1 hij

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite set used in `defn:tau`.

Informal statement: the finite set of indices belonging to a connected
segment.
-/
noncomputable def segmentIndexFinset [Preorder X] (x : Tuple X)
    (K : ConnectedSegment x) : Finset (Fin x.length) := by
  classical
  exact Finset.univ.filter (fun i => indexSegment x i = K)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: nonemptiness used in `defn:tau`.

Informal statement: each connected segment contains at least one index.
-/
theorem segmentIndexFinset_nonempty [Preorder X] (x : Tuple X)
    (K : ConnectedSegment x) :
    (segmentIndexFinset x K).Nonempty := by
  classical
  refine Quotient.inductionOn K ?_
  intro i
  exact ⟨i, by simp [segmentIndexFinset, indexSegment]⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:tau`.

Informal statement: the first appearance map sends a connected segment to the
least tuple index appearing in that segment.
-/
noncomputable def segmentArrivalIndex [Preorder X] (x : Tuple X)
    (K : ConnectedSegment x) : Fin x.length :=
  (segmentIndexFinset x K).min' (segmentIndexFinset_nonempty x K)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: membership property of `defn:tau`.

Informal statement: the first appearance index of a segment belongs to that
segment.
-/
theorem segmentArrivalIndex_mem [Preorder X] (x : Tuple X)
    (K : ConnectedSegment x) :
    segmentArrivalIndex x K ∈ segmentIndices x K := by
  classical
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (segmentIndexFinset x K)
      (segmentIndexFinset_nonempty x K))).2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `prop:tau-injective`.

Informal statement: two connected segments with the same first appearance are
the same segment.
-/
theorem segmentArrivalIndex_injective [Preorder X] (x : Tuple X) :
    Function.Injective (segmentArrivalIndex x) := by
  intro K L hKL
  have hK : indexSegment x (segmentArrivalIndex x K) = K :=
    segmentArrivalIndex_mem x K
  have hL : indexSegment x (segmentArrivalIndex x L) = L :=
    segmentArrivalIndex_mem x L
  rw [← hK, ← hL, hKL]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: corollary after `prop:tau-injective`.

Informal statement: connected segments inherit a total order by first
appearance.
-/
def SegmentArrivalLE [Preorder X] (x : Tuple X)
    (K L : ConnectedSegment x) : Prop :=
  segmentArrivalIndex x K ≤ segmentArrivalIndex x L

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: corollary after `prop:tau-injective`.

Informal statement: the first-appearance order on connected segments is
total.
-/
theorem segmentArrivalLE_total [Preorder X] (x : Tuple X)
    (K L : ConnectedSegment x) :
    SegmentArrivalLE x K L ∨ SegmentArrivalLE x L K :=
  le_total (segmentArrivalIndex x K) (segmentArrivalIndex x L)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: corollary after `prop:tau-injective`.

Informal statement: the first-appearance order on connected segments is
antisymmetric.
-/
theorem segmentArrivalLE_antisymm [Preorder X] (x : Tuple X)
    {K L : ConnectedSegment x} :
    SegmentArrivalLE x K L → SegmentArrivalLE x L K → K = L := by
  intro hKL hLK
  exact segmentArrivalIndex_injective x (le_antisymm hKL hLK)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for
`defn:segments`.

Informal statement: remove duplicates from a list while keeping the first
occurrence of each element.

Lean strategy / thesis relation note: mathlib's `List.dedup` keeps the last occurrence. The thesis
requires first-appearance order, so Lean implements first-occurrence deletion
as `reverse.dedup.reverse`.
-/
noncomputable def firstOccurrenceList {α : Type u} (l : List α) : List α := by
  classical
  exact l.reverse.dedup.reverse

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for
`defn:segments`.

Informal statement: first-occurrence deletion preserves list membership.
-/
@[simp]
theorem mem_firstOccurrenceList {α : Type u} {l : List α} {a : α} :
    a ∈ firstOccurrenceList l ↔ a ∈ l := by
  classical
  simp [firstOccurrenceList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for
`defn:segments`.

Informal statement: first-occurrence deletion produces a duplicate-free list.
-/
theorem nodup_firstOccurrenceList {α : Type u} (l : List α) :
    (firstOccurrenceList l).Nodup := by
  classical
  simpa [firstOccurrenceList, List.Nodup, eq_comm] using
    (List.nodup_dedup l.reverse).reverse

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for
`defn:segments`.

Informal statement: the first-occurrence list of the empty list is empty.
-/
@[simp]
theorem firstOccurrenceList_nil {α : Type u} :
    firstOccurrenceList ([] : List α) = [] := by
  classical
  simp [firstOccurrenceList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for
`defn:segments`.

Informal statement: first-occurrence deletion commutes with an injective
change of labels.

Lean strategy / thesis relation note: this is bookkeeping for transporting the thesis' first-arrival
enumeration across the source-to-output segment bijection.
-/
theorem firstOccurrenceList_map_of_injective {α β : Type u}
    {f : α → β} (hf : Function.Injective f) (l : List α) :
    firstOccurrenceList (l.map f) = (firstOccurrenceList l).map f := by
  classical
  unfold firstOccurrenceList
  rw [← List.map_reverse]
  rw [List.dedup_map_of_injective hf]
  rw [← List.map_reverse]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for
`defn:segments`.

Informal statement: first-occurrence deletion fixes a duplicate-free list.
-/
theorem firstOccurrenceList_eq_self_of_nodup {α : Type u}
    {l : List α} (hl : l.Nodup) :
    firstOccurrenceList l = l := by
  classical
  have hrev : l.reverse.Nodup := by
    simpa [List.Nodup, eq_comm] using hl.reverse
  simpa [firstOccurrenceList] using
    congrArg List.reverse (List.dedup_eq_self.mpr hrev)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for the corollary
after `defn:minimum-sorting-rule`.

Informal statement: if `a` does not occur in `l`, adjoining `a` as the final
possible new element of a list-union is the same as deduplicating `l` and
then appending `a`.

Lean strategy / thesis relation note: this is list bookkeeping only. It supports the thesis'
argument that, in a concatenation of nonempty blocks ordered by first
appearance, the first occurrence of each block label is the first element of
that block.
-/
theorem list_union_singleton_eq_dedup_append_of_notMem {α : Type u}
    [DecidableEq α] {a : α} {l : List α} (ha : a ∉ l) :
    l ∪ [a] = l.dedup ++ [a] := by
  induction l with
  | nil =>
      simp
  | cons b t ih =>
      have hat : a ∉ t := by
        intro hat
        exact ha (List.mem_cons_of_mem b hat)
      by_cases hbt : b ∈ t
      · have hb_union : b ∈ t ∪ [a] :=
          List.mem_union_left hbt [a]
        rw [List.cons_union]
        rw [List.insert_of_mem hb_union]
        rw [List.dedup_cons_of_mem hbt]
        exact ih hat
      · have hbne : b ≠ a := by
          intro hba
          exact ha (by simp [hba])
        have hb_union : b ∉ t ∪ [a] := by
          intro hbmem
          rw [List.mem_union_iff] at hbmem
          rcases hbmem with hbmem | hbmem
          · exact hbt hbmem
          · have hba : b = a := by
              simpa using hbmem
            exact hbne hba
        rw [List.cons_union]
        rw [List.insert_of_not_mem hb_union]
        rw [List.dedup_cons_of_notMem hbt]
        rw [ih hat]
        rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for the corollary
after `defn:minimum-sorting-rule`.

Informal statement: if a positive-length constant block labelled `a` is
concatenated before a tail that contains no `a`, first-occurrence deletion
keeps exactly one leading `a` and then processes the tail.
-/
theorem firstOccurrenceList_replicate_append_of_pos {α : Type u}
    {a : α} {l : List α} {n : ℕ} (hn : n ≠ 0) (ha : a ∉ l) :
    firstOccurrenceList (List.replicate n a ++ l) =
      a :: firstOccurrenceList l := by
  classical
  unfold firstOccurrenceList
  rw [List.reverse_append]
  rw [List.reverse_replicate]
  rw [List.dedup_append]
  rw [List.replicate_dedup hn]
  rw [list_union_singleton_eq_dedup_append_of_notMem]
  · simp
  · simpa using ha

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for the corollary
after `defn:minimum-sorting-rule`.

Informal statement: if `a` is not one of the labels in `Ks`, then `a` does
not occur in the flattened list obtained by replacing each `K` by a constant
block labelled `K`.
-/
theorem not_mem_flatten_replicates_of_notMem {α : Type u}
    {a : α} {Ks : List α} {n : α → ℕ}
    (ha : a ∉ Ks) :
    a ∉ ((Ks.map fun K => List.replicate (n K) K).flatten) := by
  intro hmem
  rw [List.mem_flatten] at hmem
  rcases hmem with ⟨block, hblock, hamem⟩
  rw [List.mem_map] at hblock
  rcases hblock with ⟨K, hK, rfl⟩
  have hrep : n K ≠ 0 ∧ a = K := by
    simpa using hamem
  exact ha (by simpa [hrep.2] using hK)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite first-occurrence enumeration helper for the corollary
after `defn:minimum-sorting-rule`.

Informal statement: replacing each entry of a duplicate-free label list by a
nonempty constant block and then taking first occurrences recovers the
original label list.

Lean strategy / thesis relation note: this is the exact list-level form of the thesis' block-order
argument: the first element of each nonempty connected-segment block is the
first occurrence of that segment after concatenation.
-/
theorem firstOccurrenceList_flatten_replicates_of_nodup {α : Type u}
    {Ks : List α} {n : α → ℕ}
    (hKs : Ks.Nodup) (hpos : ∀ K ∈ Ks, n K ≠ 0) :
    firstOccurrenceList ((Ks.map fun K => List.replicate (n K) K).flatten) =
      Ks := by
  classical
  induction Ks with
  | nil =>
      simp
  | cons K Ks ih =>
      rw [List.nodup_cons] at hKs
      simp only [List.map_cons, List.flatten_cons]
      rw [firstOccurrenceList_replicate_append_of_pos]
      · have ih' := ih hKs.2
          (fun L hL => hpos L (List.mem_cons_of_mem K hL))
        rw [ih']
      · exact hpos K (by simp)
      · exact not_mem_flatten_replicates_of_notMem
          (a := K) (Ks := Ks) (n := n) hKs.1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite block bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: in a flattened list of blocks, the parallel flattened
source-label list identifies a block that contains the graph point at the
same position.

Lean strategy / thesis relation note: this is list bookkeeping for the thesis' concatenation
notation. It lets us pass from an abstract source-label shadow back to the
actual sorted graph point occupying the same concatenated position.
-/
theorem exists_label_of_getElem_flatten_blocks
    {α : Type u} {β : Type v} (Ks : List α) (block : α → List β) {i : ℕ}
    (hg : i < ((Ks.map block).flatten).length)
    (hs : i < ((Ks.map fun K => List.replicate (block K).length K).flatten).length) :
    ∃ K : α,
      ((Ks.map fun K => List.replicate (block K).length K).flatten)[i] = K ∧
      ((Ks.map block).flatten)[i] ∈ block K := by
  induction Ks generalizing i with
  | nil =>
      simp at hg
  | cons K Ks ih =>
      simp only [List.map_cons, List.flatten_cons] at hg hs ⊢
      by_cases hi : i < (block K).length
      · refine ⟨K, ?_, ?_⟩
        · rw [List.getElem_append_left
            (as := List.replicate (block K).length K)
            (bs := (Ks.map fun K => List.replicate (block K).length K).flatten)
            (by simpa [List.length_replicate] using hi)]
          exact List.getElem_replicate
            (by simpa [List.length_replicate] using hi)
        · rw [List.getElem_append_left
            (as := block K) (bs := (Ks.map block).flatten) hi]
          exact List.getElem_mem hi
      · have hge : (block K).length ≤ i := Nat.le_of_not_gt hi
        have hg_tail : i - (block K).length < ((Ks.map block).flatten).length := by
          have hi_total : i < (block K).length + ((Ks.map block).flatten).length := by
            simpa [List.length_append] using hg
          exact (Nat.sub_lt_iff_lt_add hge).mpr
            (by simpa [Nat.add_comm] using hi_total)
        have hs_tail : i - (block K).length <
            ((Ks.map fun K => List.replicate (block K).length K).flatten).length := by
          have hi_total : i < (block K).length +
              ((Ks.map fun K => List.replicate (block K).length K).flatten).length := by
            simpa [List.length_append, List.length_replicate] using hs
          exact (Nat.sub_lt_iff_lt_add hge).mpr
            (by simpa [Nat.add_comm] using hi_total)
        rcases ih hg_tail hs_tail with ⟨L, hsource, hgraph⟩
        refine ⟨L, ?_, ?_⟩
        · rw [List.getElem_append_right
            (as := List.replicate (block K).length K)
            (bs := (Ks.map fun K => List.replicate (block K).length K).flatten)
            (i := i) (by simpa [List.length_replicate] using hge)]
          simpa [List.length_replicate] using hsource
        · rw [List.getElem_append_right
            (as := block K) (bs := (Ks.map block).flatten) (i := i) hge]
          exact hgraph

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite block bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: if a label does not occur in a source-label list, then
filtering a parallel zipped source/value list by that label returns no
values.
-/
theorem map_snd_filter_zip_eq_nil_of_notMem
    {α : Type u} {β : Type v} [DecidableEq α]
    {K : α} {src : List α} {values : List β}
    (hK : K ∉ src) :
    (((src.zip values).filter (fun z : α × β => z.1 = K)).map Prod.snd) = [] := by
  induction src generalizing values with
  | nil =>
      simp
  | cons a src ih =>
      cases values with
      | nil =>
          simp
      | cons b values =>
          have hane : a ≠ K := by
            intro ha
            exact hK (by simp [ha])
          have htail : K ∉ src := by
            intro ht
            exact hK (List.mem_cons_of_mem a ht)
          simp [hane, ih htail]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite block bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: zipping a constant source-label block with a value block,
filtering by that same label, and projecting values recovers the value block.
-/
theorem map_snd_filter_zip_replicate_eq
    {α : Type u} {β : Type v} [DecidableEq α]
    (K : α) (l : List β) :
    (((List.replicate l.length K).zip l).filter
      (fun z : α × β => z.1 = K)).map Prod.snd = l := by
  induction l with
  | nil =>
      simp
  | cons b t ih =>
      change (((List.replicate (t.length + 1) K).zip (b :: t)).filter
        (fun z : α × β => z.1 = K)).map Prod.snd = b :: t
      rw [List.replicate_succ]
      simp [ih]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite block bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: if a duplicate-free list of labels is expanded into
constant source-label blocks, then filtering a parallel source/value zip by
each label and flattening those filtered value blocks recovers the original
value list.

Lean strategy / thesis relation note: this is the generic list form of the thesis' final
contiguous-block argument. It is independent of markets: the only hypotheses
are duplicate-free block labels and matching source/value lengths.
-/
theorem flatten_filter_zip_replicateLabels_eq_values
    {α : Type u} {β : Type v} [DecidableEq α]
    {Ks : List α} {n : α → ℕ} {values : List β}
    (hKs : Ks.Nodup)
    (hlen : values.length =
      ((Ks.map fun K => List.replicate (n K) K).flatten).length) :
    ((Ks.map fun K =>
      ((((Ks.map fun L => List.replicate (n L) L).flatten).zip values).filter
        (fun z : α × β => z.1 = K)).map Prod.snd).flatten) = values := by
  induction Ks generalizing values with
  | nil =>
      have hlen0 : values.length = 0 := by simpa using hlen
      have hval : values = [] := List.eq_nil_of_length_eq_zero hlen0
      simp [hval]
  | cons K Ks ih =>
      rw [List.nodup_cons] at hKs
      let srcTail : List α := (Ks.map fun L => List.replicate (n L) L).flatten
      let srcHead : List α := List.replicate (n K) K
      let valuesHead : List β := values.take (n K)
      let valuesTail : List β := values.drop (n K)
      have hsource_len : values.length = n K + srcTail.length := by
        simpa [srcTail] using hlen
      have hnle : n K ≤ values.length := by
        rw [hsource_len]
        exact Nat.le_add_right (n K) srcTail.length
      have htake_len : srcHead.length = valuesHead.length := by
        simp [valuesHead, srcHead, List.length_take_of_le hnle]
      have htake_len' : valuesHead.length = n K := by
        simp [valuesHead, List.length_take_of_le hnle]
      have htail_len : valuesTail.length = srcTail.length := by
        simp [valuesTail, hsource_len]
      have hvalues_split : values = valuesHead ++ valuesTail := by
        simp [valuesHead, valuesTail]
      have hzip : ((srcHead ++ srcTail).zip values) =
          srcHead.zip valuesHead ++ srcTail.zip valuesTail := by
        rw [hvalues_split]
        exact List.zip_append htake_len
      have hhead :
          (((srcHead.zip valuesHead).filter
            (fun z : α × β => z.1 = K)).map Prod.snd) = valuesHead := by
        simpa [srcHead, htake_len'] using
          map_snd_filter_zip_replicate_eq (α := α) (β := β) K valuesHead
      have htail_not_K : K ∉ srcTail := by
        simpa [srcTail] using
          not_mem_flatten_replicates_of_notMem (a := K) (Ks := Ks) (n := n) hKs.1
      have hhead_tail_nil :
          (((srcTail.zip valuesTail).filter
            (fun z : α × β => z.1 = K)).map Prod.snd) = [] :=
        map_snd_filter_zip_eq_nil_of_notMem (β := β) htail_not_K
      have hblockK :
          ((((srcHead ++ srcTail).zip values).filter
            (fun z : α × β => z.1 = K)).map Prod.snd) = valuesHead := by
        rw [hzip]
        rw [List.filter_append, List.map_append]
        simp [hhead, hhead_tail_nil]
      have htail_blocks :
          ((Ks.map fun L =>
            ((((srcHead ++ srcTail).zip values).filter
              (fun z : α × β => z.1 = L)).map Prod.snd)).flatten) =
          ((Ks.map fun L =>
            (((srcTail.zip valuesTail).filter
              (fun z : α × β => z.1 = L)).map Prod.snd)).flatten) := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro L hL
        have hLK : L ≠ K := by
          intro h
          exact hKs.1 (by simpa [h] using hL)
        have hL_not_head : L ∉ srcHead := by
          intro hmem
          have hrep := (List.mem_replicate).mp hmem
          exact hLK hrep.2
        have hhead_nil :
            (((srcHead.zip valuesHead).filter
              (fun z : α × β => z.1 = L)).map Prod.snd) = [] :=
          map_snd_filter_zip_eq_nil_of_notMem (β := β) hL_not_head
        rw [hzip]
        rw [List.filter_append, List.map_append]
        simp [hhead_nil]
      have ih_tail := ih hKs.2 (by simpa [srcTail] using htail_len)
      simp only [List.map_cons, List.flatten_cons]
      change
        ((((srcHead ++ srcTail).zip values).filter
          (fun z : α × β => z.1 = K)).map Prod.snd) ++
          (Ks.map (fun L =>
            ((((srcHead ++ srcTail).zip values).filter
              (fun z : α × β => z.1 = L)).map Prod.snd))).flatten = values
      rw [hblockK, htail_blocks]
      rw [ih_tail]
      exact hvalues_split.symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite block bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: filtering finite positions by a label and then reading
their values is the same as zipping the source-label and value lists,
filtering by that label, and projecting values.
-/
theorem map_filter_finRange_eq_map_snd_filter_zip_ofFn
    {α : Type u} {β : Type v} [DecidableEq α]
    {n : ℕ} (s : Fin n → α) (f : Fin n → β) (K : α) :
    ((List.finRange n).filter (fun i => s i = K)).map f =
      (((List.ofFn s).zip (List.ofFn f)).filter
        (fun z : α × β => z.1 = K)).map Prod.snd := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.finRange_succ]
      rw [List.ofFn_succ (f := s)]
      rw [List.ofFn_succ (f := f)]
      by_cases h0 : s 0 = K
      · simp only [List.zip_cons_cons]
        rw [List.filter_cons_of_pos (by simp [h0])]
        rw [List.filter_cons_of_pos]
        · rw [List.map_cons, List.map_cons]
          rw [List.filter_map]
          simpa [List.map_map, Function.comp_def] using
            ih (fun i => s i.succ) (fun i => f i.succ)
        · simpa using h0
      · simp only [List.zip_cons_cons]
        rw [List.filter_cons_of_neg (by simp [h0])]
        rw [List.filter_cons_of_neg]
        · rw [List.filter_map]
          simpa [List.map_map, Function.comp_def] using
            ih (fun i => s i.succ) (fun i => f i.succ)
        · simpa using h0

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: ordered enumeration in `defn:segments`.

Informal statement: enumerate the connected segments in order of first
appearance by scanning the tuple domain and deleting repeated segment classes.

Lean strategy / thesis relation note: the thesis writes `(C_k)` ordered by the minimum index in each
class. The Lean definition is the equivalent finite-domain construction:
`finRange` scans indices increasingly, and `firstOccurrenceList` keeps the
first occurrence of each connected segment.
-/
noncomputable def segmentListByArrival [Preorder X]
    (x : Tuple X) : List (ConnectedSegment x) := by
  classical
  exact firstOccurrenceList ((List.finRange x.length).map (indexSegment x))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: membership property of the ordered segment enumeration.

Informal statement: a connected segment appears in the first-arrival list
exactly when it is represented by some tuple index.
-/
theorem mem_segmentListByArrival_iff [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    K ∈ segmentListByArrival (X := X) x ↔
      ∃ i : Fin x.length, indexSegment x i = K := by
  classical
  simp [segmentListByArrival]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cover property of the ordered segment enumeration.

Informal statement: every connected segment appears in the first-arrival
list.
-/
theorem mem_segmentListByArrival [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    K ∈ segmentListByArrival (X := X) x := by
  refine Quotient.inductionOn K ?_
  intro i
  rw [mem_segmentListByArrival_iff]
  exact ⟨i, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: no-duplicate property of the ordered segment enumeration.

Informal statement: the first-arrival list contains each connected segment
only once.
-/
theorem nodup_segmentListByArrival [Preorder X]
    (x : Tuple X) :
    (segmentListByArrival (X := X) x).Nodup := by
  classical
  simpa [segmentListByArrival] using
    nodup_firstOccurrenceList ((List.finRange x.length).map (indexSegment x))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:segments` / `defn:tau` bookkeeping.

Informal statement: a connected segment is determined by its set of member
indices.
-/
theorem segmentIndices_injective [Preorder X] (x : Tuple X) :
    Function.Injective (segmentIndices x) := by
  intro K L hKL
  have hKmem : segmentArrivalIndex x K ∈ segmentIndices x K :=
    segmentArrivalIndex_mem x K
  have hLmem : segmentArrivalIndex x K ∈ segmentIndices x L := by
    simpa [hKL] using hKmem
  exact hKmem.symm.trans hLmem

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: first-arrival form of `defn:segments`.

Informal statement: listing connected segments by first arrival and then
forgetting to their index sets is the same as scanning the tuple indices and
keeping the first occurrence of each connected-index set.

Lean strategy / thesis relation note: this avoids comparing quotient segment objects belonging to
different tuples; their index sets live in the common finite domain.
-/
theorem map_segmentIndices_segmentListByArrival_eq_firstOccurrenceList
    [Preorder X] (x : Tuple X) :
    (segmentListByArrival (X := X) x).map (segmentIndices x) =
      firstOccurrenceList
        ((List.finRange x.length).map fun i =>
          segmentIndices x (indexSegment x i)) := by
  classical
  simpa [segmentListByArrival, List.map_map, Function.comp_def] using
    (firstOccurrenceList_map_of_injective
      (f := segmentIndices x) (segmentIndices_injective (X := X) x)
      ((List.finRange x.length).map (indexSegment x))).symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: connected-component form of `defn:segments`.

Informal statement: the member set of the segment containing `i` is exactly
the set of indices connected to `i`.
-/
theorem segmentIndices_indexSegment_eq_connectedSet [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    segmentIndices x (indexSegment x i) =
      {j : Fin x.length | IndexConnected x i j} := by
  ext j
  constructor
  · intro hj
    exact (indexConnected_iff_same_segment x i j).mpr hj.symm
  · intro hij
    exact ((indexConnected_iff_same_segment x i j).mp hij).symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: first-arrival form of `defn:segments`.

Informal statement: the first-arrival list of connected-segment index sets
depends only on the connected-index relation.
-/
theorem map_segmentIndices_segmentListByArrival_eq_firstOccurrenceList_connectedSets
    [Preorder X] (x : Tuple X) :
    (segmentListByArrival (X := X) x).map (segmentIndices x) =
      firstOccurrenceList
        ((List.finRange x.length).map fun i =>
          {j : Fin x.length | IndexConnected x i j}) := by
  rw [map_segmentIndices_segmentListByArrival_eq_firstOccurrenceList
    (X := X) x]
  apply congrArg firstOccurrenceList
  apply List.map_congr_left
  intro i _hi
  exact segmentIndices_indexSegment_eq_connectedSet (X := X) x i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: empty case in `defn:minimum-sorting-rule`.

Informal statement: the empty tuple has no connected segments.
-/
@[simp]
theorem segmentListByArrival_empty [Preorder X] :
    segmentListByArrival (X := X) (Tuple.empty X) = [] := by
  classical
  simp [segmentListByArrival, Tuple.empty]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: lemma after `prop:tau-injective`.

Informal statement: on a distinct finite graph, the projection onto the
index coordinate is injective.

Lean strategy / thesis relation note: the thesis states this for
`\xi ∈ \mathscr{D}(X)` and the coordinate projection
`\Pi_{\mathbb{N}} : \mathbb{N} × X → \mathbb{N}`. The Lean carrier for
distinct finite graphs is `DistinctFiniteSubsets X`, whose points are
`IndexAugmented X`; the projection is `IndexAugmented.index`.
-/
theorem distinctFiniteSet_indexProjection_injOn (ξ : DistinctFiniteSubsets X) :
    Set.InjOn IndexAugmented.index (ξ.1 : Set (IndexAugmented X)) :=
  DistinctFiniteSubsets.index_injOn ξ

/-! ## Sorting Distinct Finite Sets -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: tuple/list bridge for `defn:sorting-finite-sets`.

Informal statement: a finite list determines a Lean tuple whose domain is
the list length.
-/
def tupleOfList (l : List X) : Tuple X :=
  ⟨l.length, fun i => l.get i⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: tuple/list bridge for `defn:sorting-finite-sets`.

Informal statement: the tuple associated to a list has length equal to the
list length.
-/
@[simp]
theorem tupleOfList_length (l : List X) :
    (tupleOfList l).length = l.length :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: tuple/list bridge for `defn:sorting-finite-sets`.

Informal statement: the entry of the tuple associated to a list is the
corresponding list entry.
-/
@[simp]
theorem tupleOfList_entry (l : List X) (i : Fin (tupleOfList l).length) :
    Tuple.entry (tupleOfList l) i =
      l.get (Fin.cast (tupleOfList_length (X := X) l) i) := by
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: empty tuple case for list-based tuple constructions.

Informal statement: the tuple associated to the empty list is the empty
tuple.
-/
@[simp]
theorem tupleOfList_nil :
    tupleOfList ([] : List X) = Tuple.empty X := by
  simp only [tupleOfList, Tuple.empty, List.length_nil]
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (by
      funext i
      exact Fin.elim0 i)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: set `M^{(n)}` in `defn:sorting-finite-sets`.

Informal statement: among the remaining graph points, keep exactly those for
which no remaining point has a strictly smaller value.

Lean strategy / thesis relation note: the thesis works with finite subsets. Lean performs the
recursive selection on the associated `Finset`.
-/
noncomputable def valueMinimalElements [Preorder X]
    (s : Finset (IndexAugmented X)) : Finset (IndexAugmented X) := by
  classical
  exact s.filter fun p =>
    ∀ q ∈ s, ¬ IndexAugmented.value q < IndexAugmented.value p

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: nonemptiness of `M^{(n)}` in `defn:sorting-finite-sets`.

Informal statement: every nonempty finite remainder has at least one
value-minimal point.
-/
theorem valueMinimalElements_nonempty [Preorder X]
    {s : Finset (IndexAugmented X)} (hs : s.Nonempty) :
    (valueMinimalElements (X := X) s).Nonempty := by
  classical
  letI : LE (IndexAugmented X) := ⟨fun p q =>
    IndexAugmented.value p ≤ IndexAugmented.value q⟩
  haveI : IsTrans (IndexAugmented X) (· ≤ ·) :=
    ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
  rcases Finset.exists_minimal (s := s) hs with ⟨p, hpmin⟩
  refine ⟨p, ?_⟩
  rw [valueMinimalElements, Finset.mem_filter]
  refine ⟨hpmin.1, ?_⟩
  intro q hq hlt
  have hp_le_q : IndexAugmented.value p ≤ IndexAugmented.value q :=
    hpmin.2 hq (le_of_lt hlt)
  exact (not_lt_of_ge hp_le_q) hlt

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `argmin` choice in `defn:sorting-finite-sets`.

Informal statement: choose, among current value-minimal points, the one with
least original index.
-/
noncomputable def leastIndexValueMinimal [Preorder X]
    (s : Finset (IndexAugmented X)) (hs : s.Nonempty) :
    IndexAugmented X :=
  Classical.choose
    (Finset.exists_min_image (valueMinimalElements (X := X) s)
      IndexAugmented.index (valueMinimalElements_nonempty (X := X) hs))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: selection property in `defn:sorting-finite-sets`.

Informal statement: the selected point really belongs to the current
remainder.
-/
theorem leastIndexValueMinimal_mem [Preorder X]
    (s : Finset (IndexAugmented X)) (hs : s.Nonempty) :
    leastIndexValueMinimal (X := X) s hs ∈ s := by
  classical
  have hmem_min : leastIndexValueMinimal (X := X) s hs ∈
      valueMinimalElements (X := X) s :=
    (Classical.choose_spec
      (Finset.exists_min_image (valueMinimalElements (X := X) s)
        IndexAugmented.index (valueMinimalElements_nonempty (X := X) hs))).1
  exact (Finset.mem_filter.mp hmem_min).1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: selection property in `defn:sorting-finite-sets`.

Informal statement: the selected point is one of the current value-minimal
points.
-/
theorem leastIndexValueMinimal_mem_valueMinimal [Preorder X]
    (s : Finset (IndexAugmented X)) (hs : s.Nonempty) :
    leastIndexValueMinimal (X := X) s hs ∈
      valueMinimalElements (X := X) s := by
  classical
  exact
    (Classical.choose_spec
      (Finset.exists_min_image (valueMinimalElements (X := X) s)
        IndexAugmented.index (valueMinimalElements_nonempty (X := X) hs))).1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: selection property in `defn:sorting-finite-sets`.

Informal statement: no remaining point has strictly smaller value than the
selected point.
-/
theorem leastIndexValueMinimal_value_minimal [Preorder X]
    (s : Finset (IndexAugmented X)) (hs : s.Nonempty) :
    ∀ q ∈ s,
      ¬ IndexAugmented.value q <
        IndexAugmented.value (leastIndexValueMinimal (X := X) s hs) := by
  classical
  exact (Finset.mem_filter.mp
    (leastIndexValueMinimal_mem_valueMinimal (X := X) s hs)).2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `argmin` property in `defn:sorting-finite-sets`.

Informal statement: among current value-minimal points, the selected point
has least original index.
-/
theorem leastIndexValueMinimal_index_le [Preorder X]
    (s : Finset (IndexAugmented X)) (hs : s.Nonempty)
    {p : IndexAugmented X} (hp : p ∈ valueMinimalElements (X := X) s) :
    IndexAugmented.index (leastIndexValueMinimal (X := X) s hs) ≤
      IndexAugmented.index p := by
  classical
  exact
    (Classical.choose_spec
      (Finset.exists_min_image (valueMinimalElements (X := X) s)
        IndexAugmented.index (valueMinimalElements_nonempty (X := X) hs))).2 p hp

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: Lean bookkeeping for recursive finite remainders.

Informal statement: the least-index value-minimal selector is invariant under
equality of finite remainders.

Lean strategy / thesis relation note: this has no mathematical content in the thesis; it only
handles the proof object witnessing nonemptiness in Lean.
-/
theorem leastIndexValueMinimal_congr [Preorder X]
    {s t : Finset (IndexAugmented X)}
    (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    leastIndexValueMinimal (X := X) s hs =
      leastIndexValueMinimal (X := X) t ht := by
  subst t
  exact congrArg (leastIndexValueMinimal (X := X) s)
    (Subsingleton.elim hs ht)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary minimum-selection step used in
`thm:minimal-sorting-measurable`.

Informal statement: if a point in a finite remainder has lower index than the
least-index value-minimal point, then that point is not value-minimal; hence
some point in the same remainder has strictly smaller value.

Lean strategy / thesis relation note: the thesis uses this as an informal consequence of the
definition of value-minimality. Lean records the witness explicitly.

Lean strategy / thesis strategy note: this is supporting machinery for the finite recursive
selector. The theorem-level measurable minimum sorting result is
`measurable_minimumSort_of_borelOrder` in `TuplesMeasurableSorting.lean`.
-/
theorem exists_lower_value_of_index_lt_leastIndexValueMinimal [Preorder X]
    {s : Finset (IndexAugmented X)} (hs : s.Nonempty)
    {p : IndexAugmented X} (hp : p ∈ s)
    (hidx :
      IndexAugmented.index p <
        IndexAugmented.index (leastIndexValueMinimal (X := X) s hs)) :
    ∃ q : IndexAugmented X, q ∈ s ∧
      IndexAugmented.value q < IndexAugmented.value p := by
  classical
  by_contra hnone
  have hpmin : p ∈ valueMinimalElements (X := X) s := by
    rw [valueMinimalElements, Finset.mem_filter]
    refine ⟨hp, ?_⟩
    intro q hq hlt
    exact hnone ⟨q, hq, hlt⟩
  have hle :
      IndexAugmented.index (leastIndexValueMinimal (X := X) s hs) ≤
        IndexAugmented.index p :=
    leastIndexValueMinimal_index_le (X := X) s hs hpmin
  exact (not_lt_of_ge hle) hidx

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary normal-form step after `defn:minimum-sorting-rule`.

Informal statement: convert a list of graph points into the finite-set object
used by the recursive least-index value-minimal sorter.

Lean strategy / thesis relation note: this wrapper fixes the classical decidable-equality choice for
the finite-set representation. The thesis treats the finite set extensionally;
Lean needs a concrete `Finset` term while proving the recursive selector is
fixed on already canonical lists.
-/
noncomputable def graphPointListToFinset
    (l : List (IndexAugmented X)) : Finset (IndexAugmented X) := by
  classical
  exact l.toFinset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary normal-form step after `defn:minimum-sorting-rule`.

Informal statement: the concrete finite-set wrapper above has exactly the same
members as the original list.
-/
@[simp] theorem mem_graphPointListToFinset
    {l : List (IndexAugmented X)} {p : IndexAugmented X} :
    p ∈ graphPointListToFinset (X := X) l ↔ p ∈ l := by
  classical
  simp [graphPointListToFinset]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary `argmin` uniqueness step after
`defn:minimum-sorting-rule`.

Informal statement: if a value-minimal point has index no larger than every
other value-minimal point, and the set has no duplicate at that index, then it
is the least-index value-minimal selection.

Lean strategy / thesis relation note: the thesis uses uniqueness of the least original index
implicitly. Lean states the two ingredients explicitly: index minimality among
value-minimal points and uniqueness of a graph point at that index.
-/
theorem leastIndexValueMinimal_eq_of_index_min [Preorder X]
    (s : Finset (IndexAugmented X)) (hs : s.Nonempty) {p : IndexAugmented X}
    (hpmin : p ∈ valueMinimalElements (X := X) s)
    (hle : ∀ q ∈ valueMinimalElements (X := X) s,
      IndexAugmented.index p ≤ IndexAugmented.index q)
    (huniq : ∀ q ∈ s, IndexAugmented.index q = IndexAugmented.index p → q = p) :
    leastIndexValueMinimal (X := X) s hs = p := by
  classical
  let c := leastIndexValueMinimal (X := X) s hs
  have hcmin : c ∈ valueMinimalElements (X := X) s :=
    leastIndexValueMinimal_mem_valueMinimal (X := X) s hs
  have hc_le_p : IndexAugmented.index c ≤ IndexAugmented.index p :=
    leastIndexValueMinimal_index_le (X := X) s hs hpmin
  have hp_le_c : IndexAugmented.index p ≤ IndexAugmented.index c := hle c hcmin
  have hidx : IndexAugmented.index c = IndexAugmented.index p :=
    le_antisymm hc_le_p hp_le_c
  have hc_s : c ∈ s := (Finset.mem_filter.mp hcmin).1
  exact huniq c hc_s hidx

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary normal-form step after `defn:minimum-sorting-rule`.

Informal statement: for a nonempty canonical graph-point list, the recursive
least-index value-minimal selector chooses the head.

Lean strategy / thesis relation note: "canonical" is expressed as two list
hypotheses: no later value is strictly below an earlier value, and the head has
smaller original index than every tail element. This is the Lean-local form of
the thesis' ordered connected-segment block argument.
-/
theorem leastIndexValueMinimal_eq_head_of_sorted_indexed_cons [Preorder X]
    {p : IndexAugmented X} {l : List (IndexAugmented X)}
    (hs : (graphPointListToFinset (X := X) (p :: l)).Nonempty)
    (hpair : List.Pairwise (fun a b : IndexAugmented X =>
      ¬ IndexAugmented.value b < IndexAugmented.value a) (p :: l))
    (hidx : ∀ q ∈ l, IndexAugmented.index p < IndexAugmented.index q) :
    leastIndexValueMinimal (X := X)
      (graphPointListToFinset (X := X) (p :: l)) hs = p := by
  classical
  refine leastIndexValueMinimal_eq_of_index_min (X := X)
    (graphPointListToFinset (X := X) (p :: l)) hs ?_ ?_ ?_
  · rw [valueMinimalElements, Finset.mem_filter]
    refine ⟨by simp [graphPointListToFinset], ?_⟩
    intro q hq hlt
    have hq_list : q ∈ p :: l := (mem_graphPointListToFinset (X := X)).mp hq
    simp only [List.mem_cons] at hq_list
    rcases hq_list with hq_eq | hq_tail
    · rw [hq_eq] at hlt
      exact (lt_irrefl (IndexAugmented.value p)) hlt
    · exact (List.pairwise_cons.mp hpair).1 q hq_tail hlt
  · intro q hq_min
    have hq_set : q ∈ graphPointListToFinset (X := X) (p :: l) :=
      (Finset.mem_filter.mp hq_min).1
    have hq_list : q ∈ p :: l := (mem_graphPointListToFinset (X := X)).mp hq_set
    simp only [List.mem_cons] at hq_list
    rcases hq_list with hq_eq | hq_tail
    · rw [hq_eq]
    · exact (hidx q hq_tail).le
  · intro q hq_set hqidx
    have hq_list : q ∈ p :: l := (mem_graphPointListToFinset (X := X)).mp hq_set
    simp only [List.mem_cons] at hq_list
    rcases hq_list with hq_eq | hq_tail
    · exact hq_eq
    · exfalso
      have hlt : IndexAugmented.index p < IndexAugmented.index p := by
        simpa [hqidx] using hidx q hq_tail
      exact (Nat.lt_irrefl (IndexAugmented.index p)) hlt

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: recursive construction of `\varsigma^\ast` in
`defn:sorting-finite-sets`.

Informal statement: repeatedly select the least-index value-minimal remaining
graph point and remove it from the remainder.
-/
noncomputable def distinctFiniteSetSortListAux [Preorder X] :
    Finset (IndexAugmented X) → List (IndexAugmented X)
  | s => by
      classical
      exact if hs : s.Nonempty then
        let p := leastIndexValueMinimal (X := X) s hs
        p :: distinctFiniteSetSortListAux (s.erase p)
      else []
termination_by s => s.card
decreasing_by
  classical
  exact Finset.card_erase_lt_of_mem
    (leastIndexValueMinimal_mem (X := X) s hs)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary normal-form step after `defn:minimum-sorting-rule`.

Informal statement: when a graph-point list is already sorted by value and its
stored original indices strictly increase along the list, the recursive
least-index value-minimal finite-set sorter returns that same list.

Lean strategy / thesis relation note: this is a formal version of the thesis' "sorting a canonical
block does not change it" step. The proof follows the recursive definition:
the head is the selected value-minimal point of least original index, and the
tail satisfies the same hypotheses after erasing that head.
-/
theorem distinctFiniteSetSortListAux_eq_self_of_pairwise_indexed [Preorder X]
    (l : List (IndexAugmented X))
    (hpair : List.Pairwise (fun a b : IndexAugmented X =>
      ¬ IndexAugmented.value b < IndexAugmented.value a) l)
    (hidx : ∀ i j : Fin l.length, i < j →
      IndexAugmented.index (l.get i) < IndexAugmented.index (l.get j)) :
    distinctFiniteSetSortListAux (X := X) (graphPointListToFinset (X := X) l) = l := by
  classical
  induction l with
  | nil =>
      rw [distinctFiniteSetSortListAux.eq_1]
      simp [graphPointListToFinset]
  | cons p l ih =>
      have hs : (graphPointListToFinset (X := X) (p :: l)).Nonempty := by
        simp [graphPointListToFinset]
      have hidx_head : ∀ q ∈ l, IndexAugmented.index p < IndexAugmented.index q := by
        intro q hq
        rcases List.mem_iff_get.mp hq with ⟨k, hk⟩
        have hlt_fin : (0 : Fin (p :: l).length) < (Fin.succ k : Fin (p :: l).length) := by
          simp
        have h := hidx 0 (Fin.succ k) hlt_fin
        have h' : IndexAugmented.index p < IndexAugmented.index (l.get k) := by
          simpa [List.get_cons_zero, List.get_cons_succ] using h
        rw [hk] at h'
        exact h'
      have hsel : leastIndexValueMinimal (X := X)
          (graphPointListToFinset (X := X) (p :: l)) hs = p :=
        leastIndexValueMinimal_eq_head_of_sorted_indexed_cons (X := X) hs hpair hidx_head
      have hp_not_tail : p ∉ l := by
        intro hp
        have hlt := hidx_head p hp
        exact (Nat.lt_irrefl (IndexAugmented.index p)) hlt
      have hp_not_finset : p ∉ l.toFinset := by
        simpa [List.mem_toFinset] using hp_not_tail
      have hpair_tail : List.Pairwise (fun a b : IndexAugmented X =>
          ¬ IndexAugmented.value b < IndexAugmented.value a) l :=
        (List.pairwise_cons.mp hpair).2
      have hidx_tail : ∀ i j : Fin l.length, i < j →
          IndexAugmented.index (l.get i) < IndexAugmented.index (l.get j) := by
        intro i j hij
        have hlt_succ : (Fin.succ i : Fin (p :: l).length) <
            (Fin.succ j : Fin (p :: l).length) := by
          simpa using hij
        have h := hidx (Fin.succ i) (Fin.succ j) hlt_succ
        simpa [List.get_cons_succ] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_pos hs]
      simp only [hsel]
      change p :: distinctFiniteSetSortListAux (X := X)
          ((p :: l).toFinset.erase p) = p :: l
      rw [List.toFinset_cons]
      have herase : ((insert p l.toFinset).erase p) = l.toFinset := by
        exact Finset.erase_insert hp_not_finset
      have hsort : distinctFiniteSetSortListAux (X := X) ((insert p l.toFinset).erase p) =
          distinctFiniteSetSortListAux (X := X) l.toFinset :=
        congrArg (distinctFiniteSetSortListAux (X := X)) herase
      exact congrArg (List.cons p) (hsort.trans (ih hpair_tail hidx_tail))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: list form of `\varsigma^\ast` in
`defn:sorting-finite-sets`.

Informal statement: sort a distinct finite set by applying the recursive
selection to its finite-set representation.
-/
noncomputable def distinctFiniteSetSortList [Preorder X]
    (ξ : DistinctFiniteSubsets X) : List (IndexAugmented X) :=
  distinctFiniteSetSortListAux (X := X) (toFinset ξ.1)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary normal-form step after `defn:minimum-sorting-rule`.

Informal statement: if a distinct finite set is represented by an already
canonical graph-point list, then the distinct finite-set sorter returns that
list.

Lean strategy / thesis relation note: this transports the raw finite-set normal-form lemma from the
concrete `Finset` used by recursion to the thesis carrier
`\mathscr{D}(X)` represented as `DistinctFiniteSubsets X`.
-/
theorem distinctFiniteSetSortList_eq_self_of_pairwise_indexed [Preorder X]
    (ξ : DistinctFiniteSubsets X) (l : List (IndexAugmented X))
    (hmem : ∀ p : IndexAugmented X,
      p ∈ l ↔ p ∈ (ξ.1 : Set (IndexAugmented X)))
    (hpair : List.Pairwise (fun a b : IndexAugmented X =>
      ¬ IndexAugmented.value b < IndexAugmented.value a) l)
    (hidx : ∀ i j : Fin l.length, i < j →
      IndexAugmented.index (l.get i) < IndexAugmented.index (l.get j)) :
    distinctFiniteSetSortList (X := X) ξ = l := by
  classical
  unfold distinctFiniteSetSortList
  have hfin : toFinset ξ.1 = graphPointListToFinset (X := X) l := by
    ext p
    rw [mem_toFinset]
    rw [mem_graphPointListToFinset]
    exact (hmem p).symm
  rw [hfin]
  exact distinctFiniteSetSortListAux_eq_self_of_pairwise_indexed (X := X) l hpair hidx

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary segment list after `defn:minimum-sorting-rule`.

Informal statement: list the graph points of a connected segment in increasing
tuple-index order.

Lean strategy / thesis relation note: the thesis often writes a segment as a finite graph subset and
then orders it by its natural index coordinate. Lean makes that ordered
representative explicit using `Finset.sort` on the segment's finite index set.
-/
noncomputable def segmentPointListByIndex [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) : List (IndexAugmented X) := by
  classical
  exact ((segmentIndexFinset x K).sort (fun i j : Fin x.length => i ≤ j)).map
    fun i => IndexAugmented.mk i.1 (Tuple.entry x i)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary segment list after `defn:minimum-sorting-rule`.

Informal statement: the ordered segment list has exactly the graph points of
the corresponding segment finite set.
-/
theorem mem_segmentPointListByIndex_iff [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) {p : IndexAugmented X} :
    p ∈ segmentPointListByIndex (X := X) x K ↔
      p ∈ ((segmentDistinctFiniteSet (X := X) x K).1 : Set (IndexAugmented X)) := by
  classical
  constructor
  · intro hp
    rw [segmentPointListByIndex, List.mem_map] at hp
    rcases hp with ⟨i, hi, rfl⟩
    have hiK : i ∈ segmentIndices x K := by
      have hi_finset : i ∈ segmentIndexFinset x K := by
        exact (Finset.mem_sort (fun i j : Fin x.length => i ≤ j)).mp hi
      exact (Finset.mem_filter.mp hi_finset).2
    exact (mem_segmentDistinctFiniteSet (X := X) x K).mpr ⟨i, hiK, rfl⟩
  · intro hp
    rcases (mem_segmentDistinctFiniteSet (X := X) x K).mp hp with
      ⟨i, hiK, rfl⟩
    rw [segmentPointListByIndex, List.mem_map]
    refine ⟨i, ?_, rfl⟩
    have hi_finset : i ∈ segmentIndexFinset x K := by
      rw [segmentIndexFinset]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hiK⟩
    exact (Finset.mem_sort (fun i j : Fin x.length => i ≤ j)).mpr hi_finset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary segment normal-form step after
`defn:minimum-sorting-rule`.

Informal statement: if the ambient tuple is already sorted, then a segment
listed in increasing tuple-index order is sorted by value.
-/
theorem pairwise_segmentPointListByIndex_of_isSorted [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) (hx : IsSorted x) :
    List.Pairwise (fun a b : IndexAugmented X =>
      ¬ IndexAugmented.value b < IndexAugmented.value a)
      (segmentPointListByIndex (X := X) x K) := by
  classical
  unfold segmentPointListByIndex
  refine List.Pairwise.map
    (fun i : Fin x.length => IndexAugmented.mk i.1 (Tuple.entry x i)) ?_
    (Finset.pairwise_sort (segmentIndexFinset x K)
      (fun i j : Fin x.length => i ≤ j))
  intro i j hij
  simpa using hx i j hij

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary segment normal-form step after
`defn:minimum-sorting-rule`.

Informal statement: along the increasing-index segment list, the stored
natural indices strictly increase.
-/
theorem index_strict_segmentPointListByIndex [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    ∀ i j : Fin (segmentPointListByIndex (X := X) x K).length, i < j →
      IndexAugmented.index ((segmentPointListByIndex (X := X) x K).get i) <
        IndexAugmented.index ((segmentPointListByIndex (X := X) x K).get j) := by
  classical
  intro i j hij
  let idxs := (segmentIndexFinset x K).sort (fun i j : Fin x.length => i ≤ j)
  let f : Fin x.length → IndexAugmented X :=
    fun i => IndexAugmented.mk i.1 (Tuple.entry x i)
  have hsorted : List.Pairwise (fun i j : Fin x.length => i < j) idxs := by
    simpa [idxs] using
      (Finset.sortedLT_sort (segmentIndexFinset x K)).pairwise
  have hlen : (segmentPointListByIndex (X := X) x K).length = idxs.length := by
    simp [segmentPointListByIndex, idxs]
  let i' : Fin idxs.length := Fin.cast hlen i
  let j' : Fin idxs.length := Fin.cast hlen j
  have hij' : i' < j' := by
    simpa [i', j'] using hij
  have hidx := hsorted.rel_get_of_lt hij'
  calc
    IndexAugmented.index ((segmentPointListByIndex (X := X) x K).get i)
        = (idxs.get i').1 := by
          simp [segmentPointListByIndex, idxs, i']
    _ < (idxs.get j').1 := by
          simpa using hidx
    _ = IndexAugmented.index ((segmentPointListByIndex (X := X) x K).get j) := by
          simp [segmentPointListByIndex, idxs, j']

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary segment normal-form step after
`defn:minimum-sorting-rule`.

Informal statement: for an already sorted tuple, sorting a connected segment
finite set returns the segment graph points in increasing tuple-index order.

Lean strategy / thesis relation note: this is one of the main local bridges toward the idempotence
corollary for the minimum sorting rule. It is exactly the thesis' recursive
least-index selection argument, but isolated at the level of a single
connected segment.
-/
theorem distinctFiniteSetSortList_segment_eq_segmentPointListByIndex_of_isSorted
    [Preorder X] (x : Tuple X) (K : ConnectedSegment x) (hx : IsSorted x) :
    distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) =
      segmentPointListByIndex (X := X) x K := by
  apply distinctFiniteSetSortList_eq_self_of_pairwise_indexed
  · intro p
    exact mem_segmentPointListByIndex_iff (X := X) x K
  · exact pairwise_segmentPointListByIndex_of_isSorted (X := X) x K hx
  · exact index_strict_segmentPointListByIndex (X := X) x K

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `\varsigma^\ast` in `defn:sorting-finite-sets`.

Informal statement: the recursive graph-point sorting map as a tuple of
indexed graph points.
-/
noncomputable def distinctFiniteSetSortStar [Preorder X]
    (ξ : DistinctFiniteSubsets X) : Tuple (IndexAugmented X) :=
  tupleOfList (distinctFiniteSetSortList (X := X) ξ)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `\varsigma` in `defn:sorting-finite-sets`.

Informal statement: project the recursively sorted graph-point tuple to its
values.
-/
noncomputable def distinctFiniteSetSort [Preorder X]
    (ξ : DistinctFiniteSubsets X) : Tuple X :=
  tupleOfList ((distinctFiniteSetSortList (X := X) ξ).map IndexAugmented.value)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `\pi` in `defn:sorting-finite-sets`.

Informal statement: project the recursively sorted graph-point tuple to its
original indices.
-/
noncomputable def distinctFiniteSetSortIndices [Preorder X]
    (ξ : DistinctFiniteSubsets X) : Tuple ℕ :=
  tupleOfList ((distinctFiniteSetSortList (X := X) ξ).map IndexAugmented.index)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: bookkeeping fact for `defn:sorting-finite-sets`.

Informal statement: every point output by the recursive selection was present
in the original finite remainder.
-/
theorem mem_distinctFiniteSetSortListAux_subset [Preorder X]
    (s : Finset (IndexAugmented X)) {p : IndexAugmented X}
    (hp : p ∈ distinctFiniteSetSortListAux (X := X) s) : p ∈ s := by
  classical
  induction s using distinctFiniteSetSortListAux.induct with
  | case1 x s h p0 ih =>
      have hx : x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1] at hp
      rw [dif_pos hx] at hp
      simp only [List.mem_cons] at hp
      rcases hp with hp_eq | hp_tail
      · rw [hp_eq]
        exact leastIndexValueMinimal_mem (X := X) x hx
      · have hperase :
            p ∈ x.erase (leastIndexValueMinimal (X := X) x hx) :=
          ih hp_tail
        exact (Finset.mem_erase.mp hperase).2
  | case2 x s h =>
      have hx : ¬ x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1] at hp
      rw [dif_neg hx] at hp
      exact False.elim (List.not_mem_nil hp)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: bookkeeping fact for `defn:sorting-finite-sets`.

Informal statement: every point output by the distinct finite-set sorting map
belongs to the original distinct finite set.
-/
theorem mem_distinctFiniteSetSortList_subset [Preorder X]
    (ξ : DistinctFiniteSubsets X) {p : IndexAugmented X}
    (hp : p ∈ distinctFiniteSetSortList (X := X) ξ) :
    p ∈ (ξ.1 : Set (IndexAugmented X)) := by
  have hp_finset : p ∈ toFinset ξ.1 :=
    mem_distinctFiniteSetSortListAux_subset (X := X) (toFinset ξ.1) hp
  exact (mem_toFinset ξ.1).mp hp_finset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: bookkeeping fact for `defn:sorting-finite-sets`.

Informal statement: the recursive selection list has length equal to the
cardinality of the current finite remainder.
-/
theorem length_distinctFiniteSetSortListAux [Preorder X]
    (s : Finset (IndexAugmented X)) :
    (distinctFiniteSetSortListAux (X := X) s).length = s.card := by
  classical
  induction s using distinctFiniteSetSortListAux.induct with
  | case1 x s h p0 ih =>
      have hx : x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_pos hx]
      simp only [List.length_cons]
      rw [ih]
      exact Finset.card_erase_add_one (leastIndexValueMinimal_mem (X := X) x hx)
  | case2 x s h =>
      have hx : ¬ x.Nonempty := by simpa [s] using h
      have hempty : x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hx
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_neg hx]
      simp [hempty]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: bookkeeping fact for `defn:sorting-finite-sets`.

Informal statement: every point in the current finite remainder appears in
the recursive selection output.
-/
theorem mem_distinctFiniteSetSortListAux_of_mem [Preorder X]
    (s : Finset (IndexAugmented X)) {p : IndexAugmented X}
    (hp : p ∈ s) : p ∈ distinctFiniteSetSortListAux (X := X) s := by
  classical
  induction s using distinctFiniteSetSortListAux.induct with
  | case1 x s h p0 ih =>
      have hx : x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_pos hx]
      simp only [List.mem_cons]
      by_cases hpeq : p = leastIndexValueMinimal (X := X) x hx
      · exact Or.inl hpeq
      · exact Or.inr (ih ((Finset.mem_erase).mpr ⟨hpeq, hp⟩))
  | case2 x s h =>
      have hx : ¬ x.Nonempty := by simpa [s] using h
      exact False.elim (hx ⟨p, hp⟩)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: bookkeeping fact for `defn:sorting-finite-sets`.

Informal statement: membership in the recursive selection output is exactly
membership in the current finite remainder.
-/
theorem mem_distinctFiniteSetSortListAux_iff [Preorder X]
    (s : Finset (IndexAugmented X)) {p : IndexAugmented X} :
    p ∈ distinctFiniteSetSortListAux (X := X) s ↔ p ∈ s :=
  ⟨mem_distinctFiniteSetSortListAux_subset (X := X) s,
    mem_distinctFiniteSetSortListAux_of_mem (X := X) s⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite-remainder bookkeeping in `defn:sorting-finite-sets`.

Informal statement: recursively sorting a finite graph set lists exactly the
points of that finite set.
-/
theorem graphPointListToFinset_distinctFiniteSetSortListAux [Preorder X]
    (s : Finset (IndexAugmented X)) :
    graphPointListToFinset (X := X)
      (distinctFiniteSetSortListAux (X := X) s) = s := by
  classical
  ext p
  rw [mem_graphPointListToFinset, mem_distinctFiniteSetSortListAux_iff]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: recursive tail selector in `defn:sorting-finite-sets`, used
in `thm:minimal-sorting-measurable`.

Informal statement: at every position of the recursively sorted list, the
point at that position is the least-index value-minimal point of the
remaining tail.

Lean strategy / thesis relation note: this is the fully explicit Lean form of the thesis recursive
argument: after deleting the earlier selected points, the next head is chosen
by the same least-index value-minimal rule.

Lean strategy / thesis strategy note: this is a recursive-selection helper, not the final
`thm:minimal-sorting-measurable` statement. The final measurability theorem is
proved in `TuplesMeasurableSorting.lean` by finite branch-cell pasting.
-/
theorem leastIndexValueMinimal_graphPointListToFinset_drop_distinctFiniteSetSortListAux
    [Preorder X] (s : Finset (IndexAugmented X)) :
    ∀ (r : Fin (distinctFiniteSetSortListAux (X := X) s).length)
      (hsdrop :
        (graphPointListToFinset (X := X)
          ((distinctFiniteSetSortListAux (X := X) s).drop r.1)).Nonempty),
      leastIndexValueMinimal (X := X)
          (graphPointListToFinset (X := X)
            ((distinctFiniteSetSortListAux (X := X) s).drop r.1))
          hsdrop =
        (distinctFiniteSetSortListAux (X := X) s).get r := by
  classical
  induction s using distinctFiniteSetSortListAux.induct with
  | case1 x s h p0 ih =>
      have hx : x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_pos hx]
      intro r hsdrop
      cases r using Fin.cases with
      | zero =>
          change
            leastIndexValueMinimal (X := X)
                (graphPointListToFinset (X := X)
                  (leastIndexValueMinimal (X := X) x hx ::
                    distinctFiniteSetSortListAux (X := X)
                      (x.erase (leastIndexValueMinimal (X := X) x hx))))
                hsdrop =
              leastIndexValueMinimal (X := X) x hx
          have hfin :
              graphPointListToFinset (X := X)
                  (leastIndexValueMinimal (X := X) x hx ::
                    distinctFiniteSetSortListAux (X := X)
                      (x.erase (leastIndexValueMinimal (X := X) x hx))) =
                x := by
            have hsort :
                distinctFiniteSetSortListAux (X := X) x =
                  leastIndexValueMinimal (X := X) x hx ::
                    distinctFiniteSetSortListAux (X := X)
                      (x.erase (leastIndexValueMinimal (X := X) x hx)) := by
              rw [distinctFiniteSetSortListAux.eq_1, dif_pos hx]
            rw [← hsort]
            exact graphPointListToFinset_distinctFiniteSetSortListAux
              (X := X) x
          exact leastIndexValueMinimal_congr (X := X) hfin hsdrop hx
      | succ r =>
          simpa [List.drop, List.get_cons_succ] using ih r hsdrop
  | case2 x s h =>
      have hx : ¬ x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_neg hx]
      intro r _hsdrop
      exact Fin.elim0 r

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: bookkeeping fact for `defn:sorting-finite-sets`.

Informal statement: the recursive selection output contains no duplicate
graph points.
-/
theorem nodup_distinctFiniteSetSortListAux [Preorder X]
    (s : Finset (IndexAugmented X)) :
    (distinctFiniteSetSortListAux (X := X) s).Nodup := by
  classical
  induction s using distinctFiniteSetSortListAux.induct with
  | case1 x s h p0 ih =>
      have hx : x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_pos hx]
      simp only [List.nodup_cons]
      constructor
      · intro hp_tail
        have hp_erase : leastIndexValueMinimal (X := X) x hx ∈
            x.erase (leastIndexValueMinimal (X := X) x hx) :=
          mem_distinctFiniteSetSortListAux_subset (X := X)
            (x.erase (leastIndexValueMinimal (X := X) x hx)) hp_tail
        exact (Finset.mem_erase.mp hp_erase).1 rfl
      · exact ih
  | case2 x s h =>
      have hx : ¬ x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_neg hx]
      exact List.nodup_nil

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: bookkeeping fact for `defn:sorting-finite-sets`.

Informal statement: the recursive selection output is a permutation of the
current finite remainder. This is the Lean-native expression of the thesis
claim that `\varsigma^\ast` is an enumeration of the original graph.
-/
theorem perm_distinctFiniteSetSortListAux_toList [Preorder X]
    (s : Finset (IndexAugmented X)) :
    (distinctFiniteSetSortListAux (X := X) s).Perm s.toList := by
  classical
  rw [List.perm_ext_iff_of_nodup
    (nodup_distinctFiniteSetSortListAux (X := X) s) (Finset.nodup_toList s)]
  intro p
  rw [mem_distinctFiniteSetSortListAux_iff, Finset.mem_toList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cardinality bookkeeping for `defn:sorting-finite-sets`.

Informal statement: sorting a distinct finite set produces a graph-point list
whose length is the cardinality of the original finite set.
-/
theorem length_distinctFiniteSetSortList [Preorder X]
    (ξ : DistinctFiniteSubsets X) :
    (distinctFiniteSetSortList (X := X) ξ).length = (toFinset ξ.1).card :=
  length_distinctFiniteSetSortListAux (X := X) (toFinset ξ.1)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cardinality bookkeeping for `\varsigma^\ast` in
`defn:sorting-finite-sets`.

Informal statement: the graph-point tuple `\varsigma^\ast(ξ)` has length
equal to the cardinality of `ξ`.
-/
theorem length_distinctFiniteSetSortStar [Preorder X]
    (ξ : DistinctFiniteSubsets X) :
    (distinctFiniteSetSortStar (X := X) ξ).length = (toFinset ξ.1).card := by
  simp [distinctFiniteSetSortStar, tupleOfList, length_distinctFiniteSetSortList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cardinality bookkeeping for `\varsigma` in
`defn:sorting-finite-sets`.

Informal statement: the projected value tuple has length equal to the
cardinality of the original distinct finite set.
-/
theorem length_distinctFiniteSetSort [Preorder X]
    (ξ : DistinctFiniteSubsets X) :
    (distinctFiniteSetSort (X := X) ξ).length = (toFinset ξ.1).card := by
  simp [distinctFiniteSetSort, tupleOfList, length_distinctFiniteSetSortList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cardinality bookkeeping for `\pi` in
`defn:sorting-finite-sets`.

Informal statement: the projected index tuple has length equal to the
cardinality of the original distinct finite set.
-/
theorem length_distinctFiniteSetSortIndices [Preorder X]
    (ξ : DistinctFiniteSubsets X) :
    (distinctFiniteSetSortIndices (X := X) ξ).length = (toFinset ξ.1).card := by
  simp [distinctFiniteSetSortIndices, tupleOfList, length_distinctFiniteSetSortList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: permutation bookkeeping for `defn:sorting-finite-sets`.

Informal statement: the graph-point list produced by sorting a distinct
finite set has no duplicate graph points.
-/
theorem nodup_distinctFiniteSetSortList [Preorder X]
    (ξ : DistinctFiniteSubsets X) :
    (distinctFiniteSetSortList (X := X) ξ).Nodup :=
  nodup_distinctFiniteSetSortListAux (X := X) (toFinset ξ.1)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: index-permutation bookkeeping for `\pi` in
`defn:sorting-finite-sets`.

Informal statement: because distinct finite sets have at most one value at
each index, the index list underlying `\pi(ξ)` has no duplicates.
-/
theorem nodup_distinctFiniteSetSortIndexList [Preorder X]
    (ξ : DistinctFiniteSubsets X) :
    ((distinctFiniteSetSortList (X := X) ξ).map IndexAugmented.index).Nodup := by
  classical
  apply List.Nodup.map_on
  · intro p hp q hq hindex
    exact DistinctFiniteSubsets.index_injOn ξ
      (mem_distinctFiniteSetSortList_subset (X := X) ξ hp)
      (mem_distinctFiniteSetSortList_subset (X := X) ξ hq)
      hindex
  · exact nodup_distinctFiniteSetSortList (X := X) ξ

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: sortedness construction in `defn:sorting-finite-sets`.

Informal statement: in the recursive graph-point output, no later selected
point has value strictly below an earlier selected point.

Lean strategy / thesis relation note: Lean packages the recursive argument as `List.Pairwise`.
This is exactly the thesis induction: the head is value-minimal in the
current remainder, and the tail is sorted after erasing the head.
-/
theorem pairwise_no_later_lt_distinctFiniteSetSortListAux [Preorder X]
    (s : Finset (IndexAugmented X)) :
    List.Pairwise (fun p q : IndexAugmented X =>
      ¬ IndexAugmented.value q < IndexAugmented.value p)
      (distinctFiniteSetSortListAux (X := X) s) := by
  classical
  induction s using distinctFiniteSetSortListAux.induct with
  | case1 x s h p0 ih =>
      have hx : x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_pos hx]
      apply List.Pairwise.cons
      · intro q hq_tail
        have hq_erase : q ∈ x.erase (leastIndexValueMinimal (X := X) x hx) :=
          mem_distinctFiniteSetSortListAux_subset (X := X)
            (x.erase (leastIndexValueMinimal (X := X) x hx)) hq_tail
        have hq_x : q ∈ x := (Finset.mem_erase.mp hq_erase).2
        exact leastIndexValueMinimal_value_minimal (X := X) x hx q hq_x
      · exact ih
  | case2 x s h =>
      have hx : ¬ x.Nonempty := by simpa [s] using h
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_neg hx]
      exact List.Pairwise.nil

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: Lean bridge for `defn:sorted-tuples`.

Informal statement: a list whose later entries are pairwise never strictly
smaller than earlier entries yields a sorted tuple.

Lean strategy / thesis strategy note: this is not the primary definition of sorted tuples. The
actual formal counterparts of `defn:sorted-tuples` are `IsSorted` and
`SortedTuple` in `TuplesBasic.lean`; this lemma only transports list-level
sortedness into that predicate.
-/
theorem isSorted_tupleOfList_of_pairwise [Preorder X] {l : List X}
    (hpair : List.Pairwise (fun a b : X => ¬ b < a) l) :
    IsSorted (tupleOfList l) := by
  intro i j hij hbad
  by_cases h_eq : i = j
  · subst j
    exact (lt_irrefl (Tuple.entry (tupleOfList l) i)) hbad
  · have hltij : i < j := lt_of_le_of_ne hij h_eq
    have hno := (List.pairwise_iff_get.mp hpair) i j hltij
    exact hno hbad

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: codomain statement in `defn:sorting-finite-sets`.

Informal statement: projecting the recursive graph-point sorting map to
values produces a sorted tuple.
-/
theorem distinctFiniteSetSort_isSorted [Preorder X]
    (ξ : DistinctFiniteSubsets X) :
    IsSorted (distinctFiniteSetSort (X := X) ξ) := by
  apply isSorted_tupleOfList_of_pairwise
  exact List.Pairwise.map IndexAugmented.value
    (fun _ _ h => h)
    (pairwise_no_later_lt_distinctFiniteSetSortListAux (X := X) (toFinset ξ.1))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block used in `defn:minimum-sorting-rule`.

Informal statement: sort one connected segment by first viewing it as a
distinct finite set, then applying the distinct-finite-set sorting map.
-/
noncomputable def sortedSegment [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) : Tuple X :=
  distinctFiniteSetSort (X := X) (segmentDistinctFiniteSet x K)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: sorted block property in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: each connected segment block is sorted before the
minimum sorting rule concatenates the blocks.
-/
theorem sortedSegment_isSorted [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    IsSorted (sortedSegment (X := X) x K) :=
  distinctFiniteSetSort_isSorted (X := X) (segmentDistinctFiniteSet x K)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-point blocks underlying `defn:minimum-sorting-rule`.

Informal statement: for each connected segment, list the sorted graph points
selected by `defn:sorting-finite-sets`.
-/
noncomputable def minimumSortGraphBlocks [Preorder X]
    (x : Tuple X) : List (List (IndexAugmented X)) :=
  (segmentListByArrival (X := X) x).map fun K =>
    distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary block normal form after `defn:minimum-sorting-rule`.

Informal statement: if the tuple is already sorted, each graph block used by
the minimum sorting construction is just that segment listed by increasing
tuple index.

Lean strategy / thesis relation note: this lifts the single-segment normal-form lemma to the block
list in the minimum sorting rule. It keeps the proof close to the thesis:
first normalize each segment, then concatenate the normalized blocks.
-/
theorem minimumSortGraphBlocks_eq_segmentPointLists_of_isSorted [Preorder X]
    (x : Tuple X) (hx : IsSorted x) :
    minimumSortGraphBlocks (X := X) x =
      (segmentListByArrival (X := X) x).map
        fun K => segmentPointListByIndex (X := X) x K := by
  simp [minimumSortGraphBlocks,
    distinctFiniteSetSortList_segment_eq_segmentPointListByIndex_of_isSorted
      (X := X) x, hx]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: concatenated graph-point list for the proof after
`defn:minimum-sorting-rule`.

Informal statement: concatenate the sorted graph-point blocks in first-arrival
order.
-/
noncomputable def minimumSortGraphList [Preorder X]
    (x : Tuple X) : List (IndexAugmented X) :=
  (minimumSortGraphBlocks (X := X) x).flatten

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: auxiliary concatenated normal form after
`defn:minimum-sorting-rule`.

Informal statement: for an already sorted tuple, the graph list used by the
minimum sorting construction is the concatenation of its connected segments
listed by increasing tuple index.
-/
theorem minimumSortGraphList_eq_flatten_segmentPointLists_of_isSorted [Preorder X]
    (x : Tuple X) (hx : IsSorted x) :
    minimumSortGraphList (X := X) x =
      ((segmentListByArrival (X := X) x).map
        fun K => segmentPointListByIndex (X := X) x K).flatten := by
  rw [minimumSortGraphList]
  rw [minimumSortGraphBlocks_eq_segmentPointLists_of_isSorted (X := X) x hx]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: concatenated projected index tuple `π` in the proof after
`defn:minimum-sorting-rule`.

Informal statement: project the concatenated graph-point list to its original
tuple indices.
-/
noncomputable def minimumSortIndexList [Preorder X]
    (x : Tuple X) : List ℕ :=
  (minimumSortGraphList (X := X) x).map IndexAugmented.index

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block list in `defn:minimum-sorting-rule`.

Informal statement: for each connected segment, take the sorted list of its
values. The outer list is ordered by first appearance of the segments.
-/
noncomputable def minimumSortBlocks [Preorder X]
    (x : Tuple X) : List (List X) :=
  (segmentListByArrival (X := X) x).map fun K =>
    (distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)).map
      IndexAugmented.value

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: concatenation in `defn:minimum-sorting-rule`.

Informal statement: concatenate the sorted connected-segment blocks, in
first-arrival order.

Lean strategy / thesis relation note: the thesis writes this as
`⊕ᵢ varsigma(K_i)`. Since Chapter 3's tuple concatenation module depends on
this chapter, Lean performs the same finite concatenation as list flattening
here; Chapter 3 can later relate this list-level concatenation to its tuple
`concat`.
-/
noncomputable def minimumSortList [Preorder X]
    (x : Tuple X) : List X :=
  (minimumSortBlocks (X := X) x).flatten

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: projection identity in `defn:minimum-sorting-rule`.

Informal statement: the concatenated value list is the value projection of the
concatenated graph-point list.
-/
theorem minimumSortList_eq_map_value [Preorder X]
    (x : Tuple X) :
    minimumSortList (X := X) x =
      (minimumSortGraphList (X := X) x).map IndexAugmented.value := by
  rw [minimumSortGraphList, minimumSortGraphBlocks,
    minimumSortList, minimumSortBlocks]
  rw [List.map_flatten]
  simp only [List.map_map]
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: projection identity in `defn:minimum-sorting-rule`.

Informal statement: at every graph-list position, the minimum-sort value list
contains the value projection of the same graph point.
-/
theorem minimumSortList_get_cast_graphList_eq_value [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    (minimumSortList (X := X) x).get
        (Fin.cast (by
          rw [minimumSortList_eq_map_value (X := X) x]
          simp) k) =
      IndexAugmented.value ((minimumSortGraphList (X := X) x).get k) := by
  let hlen : (minimumSortGraphList (X := X) x).length =
      (minimumSortList (X := X) x).length := by
    rw [minimumSortList_eq_map_value (X := X) x]
    simp
  have hleft := List.get_of_eq (minimumSortList_eq_map_value (X := X) x)
    (Fin.cast hlen k)
  simpa [List.get_eq_getElem, hlen] using hleft

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: tuple-valued form of `defn:minimum-sorting-rule`.

Informal statement: the minimum sorting construction as a tuple: sort each
connected segment separately and concatenate the resulting blocks by first
arrival.

Lean strategy / thesis relation note: this is intentionally a tuple-valued construction. The
subsequent proposition is the theorem that upgrades it to a sorting rule by
proving sortedness and the permutation property.
-/
noncomputable def minimumSort [Preorder X]
    (x : Tuple X) : Tuple X :=
  tupleOfList (minimumSortList (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: empty case in `defn:minimum-sorting-rule`.

Informal statement: the minimum sorting construction sends the empty tuple
to the empty tuple.
-/
@[simp]
theorem minimumSort_empty [Preorder X] :
    minimumSort (X := X) (Tuple.empty X) = Tuple.empty X := by
  change tupleOfList (minimumSortList (X := X) (Tuple.empty X)) = Tuple.empty X
  rw [show minimumSortList (X := X) (Tuple.empty X) = [] by
    simp [minimumSortList, minimumSortBlocks]]
  exact tupleOfList_nil

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: sorted block property in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the list representation of each connected-segment block
is internally sorted.
-/
theorem pairwise_minimumSortBlock [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    List.Pairwise (fun a b : X => ¬ b < a)
      ((distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)).map
        IndexAugmented.value) :=
  List.Pairwise.map IndexAugmented.value
    (fun _ _ h => h)
    (pairwise_no_later_lt_distinctFiniteSetSortListAux (X := X)
      (toFinset (segmentDistinctFiniteSet x K).1))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: enumeration property for `defn:sorting-finite-sets`.

Informal statement: the sorted graph-point list for a distinct finite set has
exactly the same points as the original distinct finite set.
-/
theorem mem_distinctFiniteSetSortList_iff [Preorder X]
    (ξ : DistinctFiniteSubsets X) {p : IndexAugmented X} :
    p ∈ distinctFiniteSetSortList (X := X) ξ ↔
      p ∈ (ξ.1 : Set (IndexAugmented X)) := by
  constructor
  · exact mem_distinctFiniteSetSortList_subset (X := X) ξ
  · intro hp
    have hp_finset : p ∈ toFinset ξ.1 := (mem_toFinset ξ.1).mpr hp
    exact mem_distinctFiniteSetSortListAux_of_mem (X := X) (toFinset ξ.1) hp_finset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: nonempty block fact implicit in
`defn:minimum-sorting-rule`.

Informal statement: the sorted graph-point list associated to a connected
segment is nonempty.

Lean strategy / thesis relation note: quotient classes are nonempty by construction; Lean witnesses
that nonemptiness with the segment's first-arrival index.
-/
theorem distinctFiniteSetSortList_segment_nonempty [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    ∃ p : IndexAugmented X,
      p ∈ distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet x K) := by
  let p : IndexAugmented X :=
    IndexAugmented.mk (segmentArrivalIndex (X := X) x K).1
      (Tuple.entry x (segmentArrivalIndex (X := X) x K))
  refine ⟨p, ?_⟩
  apply (mem_distinctFiniteSetSortList_iff (X := X)
    (segmentDistinctFiniteSet x K)).mpr
  exact (mem_segmentDistinctFiniteSet (X := X) x K).mpr
    ⟨segmentArrivalIndex (X := X) x K,
      segmentArrivalIndex_mem (X := X) x K, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: nonempty block fact implicit in
`defn:minimum-sorting-rule`.

Informal statement: every sorted connected-segment graph block has positive
length.
-/
theorem length_distinctFiniteSetSortList_segment_pos [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    0 < (distinctFiniteSetSortList (X := X)
      (segmentDistinctFiniteSet x K)).length := by
  rcases distinctFiniteSetSortList_segment_nonempty (X := X) x K with ⟨p, hp⟩
  exact List.length_pos_of_mem hp

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the ideal source-label block list underlying one
minimum-sort pass: each original connected segment contributes a constant
source label repeated once for each graph point in its sorted block.

Lean strategy / thesis relation note: the thesis keeps this implicit in the notation
`\bigoplus_r \varsigma(K_r)`. Lean names the source-label shadow of that
concatenation so the first-arrival order can be proved at list level.
-/
noncomputable def minimumSortSourceBlocks [Preorder X]
    (x : Tuple X) : List (List (ConnectedSegment x)) :=
  (segmentListByArrival (X := X) x).map fun K =>
    List.replicate
      (distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet x K)).length K

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: first-occurrence deletion of the ideal source-label
shadow of one minimum-sort pass recovers the original first-arrival segment
list.

Lean strategy / thesis relation note: this is the formal version of the thesis' order argument:
connected segments are concatenated in first-arrival order, and every sorted
segment block is nonempty, so the first appearances after concatenation are
exactly the original segment order.
-/
theorem firstOccurrenceList_minimumSortSourceBlocks_flatten [Preorder X]
    (x : Tuple X) :
    firstOccurrenceList (minimumSortSourceBlocks (X := X) x).flatten =
      segmentListByArrival (X := X) x := by
  rw [minimumSortSourceBlocks]
  apply firstOccurrenceList_flatten_replicates_of_nodup
  · exact nodup_segmentListByArrival (X := X) x
  · intro K _hK
    exact Nat.ne_of_gt
      (length_distinctFiniteSetSortList_segment_pos (X := X) x K)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the source-label shadow of the concatenated minimum-sort
graph list has exactly one label for each graph point.
-/
theorem length_minimumSortSourceBlocks_flatten [Preorder X]
    (x : Tuple X) :
    (minimumSortSourceBlocks (X := X) x).flatten.length =
      (minimumSortGraphList (X := X) x).length := by
  rw [minimumSortSourceBlocks, minimumSortGraphList, minimumSortGraphBlocks]
  rw [List.length_flatten, List.length_flatten]
  simp only [List.map_map, List.length_replicate, Function.comp_def]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: same-block connectivity used after
`defn:minimum-sorting-rule`.

Informal statement: two sorted graph points from the same connected-segment
block still come from connected indices of the original tuple.

Lean strategy / thesis relation note: sorting the finite segment changes only the order of graph
points, not which segment they belong to.
-/
theorem indexConnected_of_mem_same_sortedSegmentGraphBlock [Preorder X]
    (x : Tuple X) {K : ConnectedSegment x} {p q : IndexAugmented X}
    (hp : p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hq : q ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)) :
    ∃ i j : Fin x.length,
      p = IndexAugmented.mk i.1 (Tuple.entry x i) ∧
      q = IndexAugmented.mk j.1 (Tuple.entry x j) ∧
      IndexConnected x i j := by
  have hp_set : p ∈ ((segmentDistinctFiniteSet x K).1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X)
      (segmentDistinctFiniteSet x K)).mp hp
  have hq_set : q ∈ ((segmentDistinctFiniteSet x K).1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X)
      (segmentDistinctFiniteSet x K)).mp hq
  exact indexConnected_of_mem_segmentDistinctFiniteSet (X := X) x hp_set hq_set

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cross-block incomparability used after
`defn:minimum-sorting-rule`.

Informal statement: graph points chosen from two distinct sorted
connected-segment blocks have incomparable values.

Lean strategy / thesis relation note: this is the stronger value-level form of the thesis' statement
that distinct segments are mutually incomparable. It is stronger than the
`¬ b < a` fact used for sortedness and is aimed at the idempotence corollary.
-/
theorem not_comparable_of_mem_distinct_sortedSegmentGraphBlocks [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} (hKL : K ≠ L)
    {p q : IndexAugmented X}
    (hp : p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hq : q ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L)) :
    ¬ (IndexAugmented.value p ≤ IndexAugmented.value q ∨
      IndexAugmented.value q ≤ IndexAugmented.value p) := by
  have hp_set : p ∈ ((segmentDistinctFiniteSet x K).1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X)
      (segmentDistinctFiniteSet x K)).mp hp
  have hq_set : q ∈ ((segmentDistinctFiniteSet x L).1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X)
      (segmentDistinctFiniteSet x L)).mp hq
  exact not_comparable_of_mem_distinct_segmentDistinctFiniteSet
    (X := X) x hKL hp_set hq_set

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block source bookkeeping after
`defn:minimum-sorting-rule`.

Informal statement: every graph point in the concatenated minimum-sort graph
list comes from one of the sorted connected-segment blocks, and we can recover
that source segment.
-/
theorem exists_segment_of_mem_minimumSortGraphList [Preorder X]
    (x : Tuple X) {p : IndexAugmented X}
    (hp : p ∈ minimumSortGraphList (X := X) x) :
    ∃ K : ConnectedSegment x,
      K ∈ segmentListByArrival (X := X) x ∧
      p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) := by
  rw [minimumSortGraphList, List.mem_flatten] at hp
  rcases hp with ⟨block, hblock, hpblock⟩
  rw [minimumSortGraphBlocks, List.mem_map] at hblock
  rcases hblock with ⟨K, hK, hblock_eq⟩
  subst block
  exact ⟨K, hK, hpblock⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: same-block connectivity after
`defn:minimum-sorting-rule`.

Informal statement: if two graph points in the minimum-sort graph list are
known to come from the same connected-segment block, their original tuple
indices are connected.
-/
theorem indexConnected_of_mem_minimumSortGraphList_same_source [Preorder X]
    (x : Tuple X) {K : ConnectedSegment x} {p q : IndexAugmented X}
    (hp : p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hq : q ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)) :
    ∃ i j : Fin x.length,
      p = IndexAugmented.mk i.1 (Tuple.entry x i) ∧
      q = IndexAugmented.mk j.1 (Tuple.entry x j) ∧
      IndexConnected x i j := by
  exact indexConnected_of_mem_same_sortedSegmentGraphBlock (X := X) x hp hq

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cross-block separation after
`defn:minimum-sorting-rule`.

Informal statement: if two graph points in the minimum-sort graph list are
known to come from distinct connected-segment blocks, then their values are
incomparable.
-/
theorem not_comparable_of_mem_minimumSortGraphList_distinct_sources [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} (hKL : K ≠ L)
    {p q : IndexAugmented X}
    (hp : p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hq : q ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L)) :
    ¬ (IndexAugmented.value p ≤ IndexAugmented.value q ∨
      IndexAugmented.value q ≤ IndexAugmented.value p) :=
  not_comparable_of_mem_distinct_sortedSegmentGraphBlocks (X := X) x hKL hp hq

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: positional same-block connectivity after
`defn:minimum-sorting-rule`.

Informal statement: graph-list entries at two positions belonging to the same
source segment come from connected original tuple indices.
-/
theorem indexConnected_of_get_minimumSortGraphList_same_source [Preorder X]
    (x : Tuple X) {K : ConnectedSegment x}
    (i j : Fin (minimumSortGraphList (X := X) x).length)
    (hi : (minimumSortGraphList (X := X) x).get i ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hj : (minimumSortGraphList (X := X) x).get j ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)) :
    ∃ a b : Fin x.length,
      (minimumSortGraphList (X := X) x).get i =
        IndexAugmented.mk a.1 (Tuple.entry x a) ∧
      (minimumSortGraphList (X := X) x).get j =
        IndexAugmented.mk b.1 (Tuple.entry x b) ∧
      IndexConnected x a b :=
  indexConnected_of_mem_minimumSortGraphList_same_source (X := X) x hi hj

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: positional cross-block separation after
`defn:minimum-sorting-rule`.

Informal statement: graph-list entries at positions belonging to distinct
source segments have incomparable value projections.
-/
theorem not_comparable_get_minimumSortGraphList_distinct_sources [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} (hKL : K ≠ L)
    (i j : Fin (minimumSortGraphList (X := X) x).length)
    (hi : (minimumSortGraphList (X := X) x).get i ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hj : (minimumSortGraphList (X := X) x).get j ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L)) :
    ¬ (IndexAugmented.value ((minimumSortGraphList (X := X) x).get i) ≤
        IndexAugmented.value ((minimumSortGraphList (X := X) x).get j) ∨
      IndexAugmented.value ((minimumSortGraphList (X := X) x).get j) ≤
        IndexAugmented.value ((minimumSortGraphList (X := X) x).get i)) :=
  not_comparable_of_mem_minimumSortGraphList_distinct_sources
    (X := X) x hKL hi hj

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: partition/enumeration claim in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the concatenated sorted segment graph list contains
exactly the graph points of the original tuple.
-/
theorem mem_minimumSortGraphList_iff [Preorder X]
    (x : Tuple X) {p : IndexAugmented X} :
    p ∈ minimumSortGraphList (X := X) x ↔
      p ∈ ((TuplesBasic.graph x).1 : Set (IndexAugmented X)) := by
  constructor
  · intro hp
    rw [minimumSortGraphList, List.mem_flatten] at hp
    rcases hp with ⟨block, hblock, hpblock⟩
    rw [minimumSortGraphBlocks, List.mem_map] at hblock
    rcases hblock with ⟨K, _hK, hblock_eq⟩
    subst block
    have hpseg : p ∈ ((segmentDistinctFiniteSet x K).1 : Set (IndexAugmented X)) :=
      (mem_distinctFiniteSetSortList_iff (X := X) (segmentDistinctFiniteSet x K)).mp
        hpblock
    rcases (mem_segmentDistinctFiniteSet (X := X) x K).mp hpseg with
      ⟨i, _hiK, hp_eq⟩
    rw [TuplesBasic.mem_graph]
    exact ⟨i, hp_eq⟩
  · intro hp
    rcases (TuplesBasic.mem_graph x).mp hp with ⟨i, hp_eq⟩
    let K : ConnectedSegment x := indexSegment x i
    have hK : K ∈ segmentListByArrival (X := X) x :=
      mem_segmentListByArrival (X := X) x K
    have hiK : i ∈ segmentIndices x K := rfl
    have hpseg : p ∈ ((segmentDistinctFiniteSet x K).1 : Set (IndexAugmented X)) :=
      (mem_segmentDistinctFiniteSet (X := X) x K).mpr ⟨i, hiK, hp_eq⟩
    have hplist : p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) :=
      (mem_distinctFiniteSetSortList_iff (X := X) (segmentDistinctFiniteSet x K)).mpr
        hpseg
    rw [minimumSortGraphList, List.mem_flatten]
    refine ⟨distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K), ?_,
      hplist⟩
    rw [minimumSortGraphBlocks, List.mem_map]
    exact ⟨K, hK, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: every original tuple index has a unique position in the
concatenated minimum-sort graph list.

Lean strategy / thesis relation note: the thesis describes the concatenated projected index map
`\pi`. Lean packages the inverse lookup as a finite index into the graph list,
chosen from the already proved membership statement.
-/
noncomputable def minimumSortGraphPositionOfIndex [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    Fin (minimumSortGraphList (X := X) x).length := by
  classical
  let p : IndexAugmented X := IndexAugmented.mk i.1 (Tuple.entry x i)
  have hpgraph : p ∈ ((TuplesBasic.graph x).1 : Set (IndexAugmented X)) := by
    rw [TuplesBasic.mem_graph]
    exact ⟨i, rfl⟩
  have hplist : p ∈ minimumSortGraphList (X := X) x :=
    (mem_minimumSortGraphList_iff (X := X) x).mpr hpgraph
  exact Classical.choose (List.mem_iff_get.mp hplist)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: the graph-list position associated to an original index
indeed contains that original graph point.
-/
theorem minimumSortGraphList_get_graphPositionOfIndex [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    (minimumSortGraphList (X := X) x).get
        (minimumSortGraphPositionOfIndex (X := X) x i) =
      IndexAugmented.mk i.1 (Tuple.entry x i) := by
  classical
  unfold minimumSortGraphPositionOfIndex
  let p : IndexAugmented X := IndexAugmented.mk i.1 (Tuple.entry x i)
  have hpgraph : p ∈ ((TuplesBasic.graph x).1 : Set (IndexAugmented X)) := by
    rw [TuplesBasic.mem_graph]
    exact ⟨i, rfl⟩
  have hplist : p ∈ minimumSortGraphList (X := X) x :=
    (mem_minimumSortGraphList_iff (X := X) x).mpr hpgraph
  simpa [p] using Classical.choose_spec (List.mem_iff_get.mp hplist)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: domain coverage of projected `π` in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the concatenated projected index list contains exactly
the natural numbers below the original tuple length.
-/
theorem mem_minimumSortIndexList_iff [Preorder X]
    (x : Tuple X) {n : ℕ} :
    n ∈ minimumSortIndexList (X := X) x ↔ n < x.length := by
  constructor
  · intro hn
    rw [minimumSortIndexList, List.mem_map] at hn
    rcases hn with ⟨p, hp, hpidx⟩
    have hpgraph : p ∈ ((TuplesBasic.graph x).1 : Set (IndexAugmented X)) :=
      (mem_minimumSortGraphList_iff (X := X) x).mp hp
    rcases (TuplesBasic.mem_graph x).mp hpgraph with ⟨i, hp_eq⟩
    have hn_eq : n = i.1 := by
      calc
        n = p.index := hpidx.symm
        _ = (IndexAugmented.mk i.1 (Tuple.entry x i)).index := by rw [hp_eq]
        _ = i.1 := IndexAugmented.index_mk i.1 (Tuple.entry x i)
    rw [hn_eq]
    exact i.2
  · intro hn
    let i : Fin x.length := ⟨n, hn⟩
    let p : IndexAugmented X := IndexAugmented.mk n (Tuple.entry x i)
    have hpgraph : p ∈ ((TuplesBasic.graph x).1 : Set (IndexAugmented X)) := by
      rw [TuplesBasic.mem_graph]
      exact ⟨i, rfl⟩
    have hplist : p ∈ minimumSortGraphList (X := X) x :=
      (mem_minimumSortGraphList_iff (X := X) x).mpr hpgraph
    rw [minimumSortIndexList, List.mem_map]
    exact ⟨p, hplist, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: disjoint block argument in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: graph points selected from two distinct connected
segments are never equal.
-/
theorem ne_of_mem_distinct_sortedSegmentGraphBlocks [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} (hKL : K ≠ L)
    {p q : IndexAugmented X}
    (hp : p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hq : q ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L)) :
    p ≠ q := by
  intro hpq
  have hpseg : p ∈ ((segmentDistinctFiniteSet x K).1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X) (segmentDistinctFiniteSet x K)).mp hp
  have hqseg : q ∈ ((segmentDistinctFiniteSet x L).1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X) (segmentDistinctFiniteSet x L)).mp hq
  rcases (mem_segmentDistinctFiniteSet (X := X) x K).mp hpseg with ⟨i, hiK, hp_eq⟩
  rcases (mem_segmentDistinctFiniteSet (X := X) x L).mp hqseg with ⟨j, hjL, hq_eq⟩
  have hidx : i.1 = j.1 := by
    calc
      i.1 = p.index := by simp [hp_eq]
      _ = q.index := by rw [hpq]
      _ = j.1 := by simp [hq_eq]
  have hij : i = j := Fin.ext hidx
  have hseg : K = L := by
    rw [← hiK, ← hjL, hij]
  exact hKL hseg

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: duplicate-free graph-block concatenation in the proposition
after `defn:minimum-sorting-rule`.

Informal statement: if the segment list has no duplicate segments, then the
concatenated sorted graph-point blocks have no duplicate graph points.
-/
theorem nodup_flatten_sortedSegmentGraphBlocks [Preorder X]
    (x : Tuple X) (Ks : List (ConnectedSegment x)) (hKs : Ks.Nodup) :
    ((Ks.map fun K => distinctFiniteSetSortList (X := X)
      (segmentDistinctFiniteSet x K)).flatten).Nodup := by
  classical
  induction Ks with
  | nil =>
      simp
  | cons K Ks ih =>
      rw [List.nodup_cons] at hKs
      rw [List.map_cons, List.flatten_cons, List.nodup_append]
      refine ⟨nodup_distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K),
        ih hKs.2, ?_⟩
      intro p hp q hq
      rw [List.mem_flatten] at hq
      rcases hq with ⟨block, hblock_mem, hq_block⟩
      rw [List.mem_map] at hblock_mem
      rcases hblock_mem with ⟨L, hLmem, hblock_eq⟩
      subst block
      have hKL : K ≠ L := by
        intro hEq
        exact hKs.1 (by simpa [hEq] using hLmem)
      exact ne_of_mem_distinct_sortedSegmentGraphBlocks (X := X) x hKL hp hq_block

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: duplicate-free graph list in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the concatenated graph-point list used by the minimum
sorting construction has no duplicate graph points.
-/
theorem nodup_minimumSortGraphList [Preorder X]
    (x : Tuple X) :
    (minimumSortGraphList (X := X) x).Nodup := by
  simpa [minimumSortGraphList, minimumSortGraphBlocks] using
    nodup_flatten_sortedSegmentGraphBlocks (X := X) x
      (segmentListByArrival (X := X) x) (nodup_segmentListByArrival (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: duplicate-free projected `π` in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the concatenated projected index list contains no
duplicate original indices.
-/
theorem nodup_minimumSortIndexList [Preorder X]
    (x : Tuple X) :
    (minimumSortIndexList (X := X) x).Nodup := by
  classical
  unfold minimumSortIndexList
  apply List.Nodup.map_on
  · intro p hp q hq hidx
    exact DistinctFiniteSubsets.index_injOn (TuplesBasic.graph x)
      ((mem_minimumSortGraphList_iff (X := X) x).mp hp)
      ((mem_minimumSortGraphList_iff (X := X) x).mp hq)
      hidx
  · exact nodup_minimumSortGraphList (X := X) x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: image/domain equality of projected `π` in the proposition
after `defn:minimum-sorting-rule`.

Informal statement: the concatenated projected index list is a permutation of
the canonical original domain list `0, ..., length - 1`.
-/
theorem perm_minimumSortIndexList_range [Preorder X]
    (x : Tuple X) :
    (minimumSortIndexList (X := X) x).Perm (List.range x.length) := by
  rw [List.perm_ext_iff_of_nodup
    (nodup_minimumSortIndexList (X := X) x) List.nodup_range]
  intro n
  rw [mem_minimumSortIndexList_iff, List.mem_range]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: length of projected `π` in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the concatenated projected index list has length equal to
the original tuple length.
-/
theorem length_minimumSortIndexList [Preorder X]
    (x : Tuple X) :
    (minimumSortIndexList (X := X) x).length = x.length := by
  have hperm := perm_minimumSortIndexList_range (X := X) x
  exact hperm.length_eq.trans List.length_range

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-list length in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the concatenated graph-point list has one point for each
original tuple index.
-/
theorem length_minimumSortGraphList [Preorder X]
    (x : Tuple X) :
    (minimumSortGraphList (X := X) x).length = x.length := by
  have h := length_minimumSortIndexList (X := X) x
  simpa [minimumSortIndexList] using h

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: length preservation in `defn:minimum-sorting-rule`.

Informal statement: the value list underlying the minimum sorting
construction has the original tuple length.
-/
theorem length_minimumSortList [Preorder X]
    (x : Tuple X) :
    (minimumSortList (X := X) x).length = x.length := by
  rw [minimumSortList_eq_map_value]
  rw [← length_minimumSortIndexList (X := X) x]
  simp [minimumSortIndexList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: length preservation in `defn:minimum-sorting-rule`.

Informal statement: the tuple produced by the minimum sorting construction
has the original tuple length.
-/
theorem length_minimumSort [Preorder X]
    (x : Tuple X) :
    (minimumSort (X := X) x).length = x.length := by
  simp [minimumSort, tupleOfList, length_minimumSortList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: view the graph-list position of an original index as a
position in the tuple produced by the minimum sort.
-/
noncomputable def minimumSortOutputPositionOfIndex [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    Fin (minimumSort (X := X) x).length :=
  Fin.cast (by
    simp [minimumSort, tupleOfList, minimumSortList_eq_map_value (X := X) x])
    (minimumSortGraphPositionOfIndex (X := X) x i)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: a position in the minimum-sort graph list is also a
position in the tuple produced by projecting that graph list to values.
-/
noncomputable def minimumSortOutputPositionOfGraphPosition [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    Fin (minimumSort (X := X) x).length :=
  Fin.cast (by
    simp [minimumSort, tupleOfList, minimumSortList_eq_map_value (X := X) x])
    k

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: every output position in the once-sorted tuple determines
the corresponding position in the projected graph list.
-/
noncomputable def minimumSortGraphPositionOfOutputPosition [Preorder X]
    (x : Tuple X) (k : Fin (minimumSort (X := X) x).length) :
    Fin (minimumSortGraphList (X := X) x).length :=
  Fin.cast (by
    simp [minimumSort, tupleOfList, minimumSortList_eq_map_value (X := X) x])
    k

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: converting a graph-list position to an output-tuple
position and back recovers the original graph-list position.
-/
@[simp]
theorem minimumSort_graphPosition_outputPosition [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    minimumSortGraphPositionOfOutputPosition (X := X) x
      (minimumSortOutputPositionOfGraphPosition (X := X) x k) = k := by
  apply Fin.ext
  simp [minimumSortGraphPositionOfOutputPosition,
    minimumSortOutputPositionOfGraphPosition]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: converting an output-tuple position to a graph-list
position and back recovers the original output position.
-/
@[simp]
theorem minimumSort_outputPosition_graphPosition [Preorder X]
    (x : Tuple X) (k : Fin (minimumSort (X := X) x).length) :
    minimumSortOutputPositionOfGraphPosition (X := X) x
      (minimumSortGraphPositionOfOutputPosition (X := X) x k) = k := by
  apply Fin.ext
  simp [minimumSortGraphPositionOfOutputPosition,
    minimumSortOutputPositionOfGraphPosition]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: at the output position corresponding to graph-list
position `k`, the once-sorted tuple has the value of the graph point at `k`.
-/
theorem minimumSort_entry_outputPositionOfGraphPosition [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    Tuple.entry (minimumSort (X := X) x)
      (minimumSortOutputPositionOfGraphPosition (X := X) x k) =
      IndexAugmented.value ((minimumSortGraphList (X := X) x).get k) := by
  classical
  unfold minimumSortOutputPositionOfGraphPosition
  change Tuple.entry (tupleOfList (minimumSortList (X := X) x))
    (Fin.cast (by
      simp [tupleOfList, minimumSortList_eq_map_value (X := X) x]) k) =
      IndexAugmented.value ((minimumSortGraphList (X := X) x).get k)
  have hval := minimumSortList_get_cast_graphList_eq_value (X := X) x k
  simpa [tupleOfList, Tuple.entry] using hval

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: at the output position assigned to original index `i`,
the once-sorted tuple has the original value `x i`.
-/
theorem minimumSort_entry_outputPositionOfIndex [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    Tuple.entry (minimumSort (X := X) x)
      (minimumSortOutputPositionOfIndex (X := X) x i) =
      Tuple.entry x i := by
  classical
  unfold minimumSortOutputPositionOfIndex
  change Tuple.entry (tupleOfList (minimumSortList (X := X) x))
    (Fin.cast (by
      simp [tupleOfList, minimumSortList_eq_map_value (X := X) x])
      (minimumSortGraphPositionOfIndex (X := X) x i)) =
      Tuple.entry x i
  have hval := minimumSortList_get_cast_graphList_eq_value (X := X) x
    (minimumSortGraphPositionOfIndex (X := X) x i)
  have hgraph := minimumSortGraphList_get_graphPositionOfIndex (X := X) x i
  have hgraph_value :
      IndexAugmented.value ((minimumSortGraphList (X := X) x).get
        (minimumSortGraphPositionOfIndex (X := X) x i)) = Tuple.entry x i := by
    simpa [hgraph] using congrArg IndexAugmented.value hgraph
  simpa [tupleOfList, Tuple.entry] using hval.trans hgraph_value

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: comparability transport for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: an immediate comparability step between original indices
is preserved between their output positions in the once-minimum-sorted tuple.
-/
theorem minimumSort_indexComparable_outputPosition_of_indexComparable [Preorder X]
    (x : Tuple X) {i j : Fin x.length}
    (hij : IndexComparable x i j) :
    IndexComparable (minimumSort (X := X) x)
      (minimumSortOutputPositionOfIndex (X := X) x i)
      (minimumSortOutputPositionOfIndex (X := X) x j) := by
  unfold IndexComparable at hij ⊢
  rw [minimumSort_entry_outputPositionOfIndex (X := X) x i,
    minimumSort_entry_outputPositionOfIndex (X := X) x j]
  exact hij

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: connected-path transport for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: if two original indices are connected, then their output
positions in the once-minimum-sorted tuple are connected.

Lean strategy / thesis relation note: this is the formal counterpart of transporting the finite
comparability chain through the permutation/list construction.
-/
theorem minimumSort_indexConnected_outputPosition_of_indexConnected [Preorder X]
    (x : Tuple X) {i j : Fin x.length}
    (hij : IndexConnected x i j) :
    IndexConnected (minimumSort (X := X) x)
      (minimumSortOutputPositionOfIndex (X := X) x i)
      (minimumSortOutputPositionOfIndex (X := X) x j) := by
  induction hij with
  | refl =>
      exact indexConnected_refl (X := X) (minimumSort (X := X) x)
        (minimumSortOutputPositionOfIndex (X := X) x i)
  | tail hconn hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (minimumSort_indexComparable_outputPosition_of_indexComparable
          (X := X) x hstep)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: uniqueness of graph-list positions after
`defn:minimum-sorting-rule`.

Informal statement: if a graph-list position contains the graph point for an
original index, then it is the distinguished position chosen for that index.
-/
theorem minimumSortGraphPosition_eq_of_get_eq [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length)
    (i : Fin x.length)
    (hget : (minimumSortGraphList (X := X) x).get k =
      IndexAugmented.mk i.1 (Tuple.entry x i)) :
    k = minimumSortGraphPositionOfIndex (X := X) x i := by
  have hinj : Function.Injective
      (fun k : Fin (minimumSortGraphList (X := X) x).length =>
        (minimumSortGraphList (X := X) x).get k) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpair := List.nodup_iff_pairwise_ne.mp
        (nodup_minimumSortGraphList (X := X) x)
      have hneq := (List.pairwise_iff_get.mp hpair) a b hlt
      exact hneq hab
    · have hpair := List.nodup_iff_pairwise_ne.mp
        (nodup_minimumSortGraphList (X := X) x)
      have hneq := (List.pairwise_iff_get.mp hpair) b a hgt
      exact hneq hab.symm
  apply hinj
  change (minimumSortGraphList (X := X) x).get k =
    (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfIndex (X := X) x i)
  rw [hget, minimumSortGraphList_get_graphPositionOfIndex (X := X) x i]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: same-block connectivity for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: two positions in the once-sorted tuple whose graph-list
points came from the same original connected-segment block are connected in
the once-sorted tuple.
-/
theorem minimumSort_indexConnected_of_get_same_source [Preorder X]
    (x : Tuple X) {K : ConnectedSegment x}
    (k l : Fin (minimumSortGraphList (X := X) x).length)
    (hk : (minimumSortGraphList (X := X) x).get k ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hl : (minimumSortGraphList (X := X) x).get l ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)) :
    IndexConnected (minimumSort (X := X) x)
      (minimumSortOutputPositionOfGraphPosition (X := X) x k)
      (minimumSortOutputPositionOfGraphPosition (X := X) x l) := by
  rcases indexConnected_of_get_minimumSortGraphList_same_source
      (X := X) x k l hk hl with
    ⟨i, j, hk_eq, hl_eq, hij⟩
  have hk_pos : k = minimumSortGraphPositionOfIndex (X := X) x i :=
    minimumSortGraphPosition_eq_of_get_eq (X := X) x k i hk_eq
  have hl_pos : l = minimumSortGraphPositionOfIndex (X := X) x j :=
    minimumSortGraphPosition_eq_of_get_eq (X := X) x l j hl_eq
  rw [hk_pos, hl_pos]
  simpa [minimumSortOutputPositionOfGraphPosition,
    minimumSortOutputPositionOfIndex] using
    minimumSort_indexConnected_outputPosition_of_indexConnected (X := X) x hij

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cross-block separation for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: two positions in the once-sorted tuple whose graph-list
points came from distinct original connected-segment blocks are not
immediately comparable.
-/
theorem minimumSort_not_indexComparable_of_get_distinct_sources [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} (hKL : K ≠ L)
    (k l : Fin (minimumSortGraphList (X := X) x).length)
    (hk : (minimumSortGraphList (X := X) x).get k ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hl : (minimumSortGraphList (X := X) x).get l ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L)) :
    ¬ IndexComparable (minimumSort (X := X) x)
      (minimumSortOutputPositionOfGraphPosition (X := X) x k)
      (minimumSortOutputPositionOfGraphPosition (X := X) x l) := by
  unfold IndexComparable
  rw [minimumSort_entry_outputPositionOfGraphPosition (X := X) x k,
    minimumSort_entry_outputPositionOfGraphPosition (X := X) x l]
  exact not_comparable_get_minimumSortGraphList_distinct_sources
    (X := X) x hKL k l hk hl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: one-step source invariance for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: an immediate comparability step in the once-sorted tuple
cannot move from one source segment block to a distinct source segment block.
-/
theorem minimumSort_source_eq_of_indexComparable [Preorder X]
    (x : Tuple X) {r s : Fin (minimumSort (X := X) x).length}
    {K L : ConnectedSegment x}
    (hr : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfOutputPosition (X := X) x r) ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hs : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfOutputPosition (X := X) x s) ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L))
    (hrs : IndexComparable (minimumSort (X := X) x) r s) :
    K = L := by
  by_contra hne
  have hbad := minimumSort_not_indexComparable_of_get_distinct_sources
    (X := X) x hne
    (minimumSortGraphPositionOfOutputPosition (X := X) x r)
    (minimumSortGraphPositionOfOutputPosition (X := X) x s) hr hs
  exact hbad (by simpa using hrs)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: uniqueness of source blocks for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the same sorted graph point cannot belong to two
different source segment blocks.
-/
theorem source_eq_of_mem_same_sortedSegmentGraphPoint [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} {p : IndexAugmented X}
    (hpK : p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hpL : p ∈ distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L)) :
    K = L := by
  by_contra hne
  exact ne_of_mem_distinct_sortedSegmentGraphBlocks (X := X) x hne hpK hpL rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: path source invariance for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: a finite connectivity path in the once-sorted tuple stays
inside a single source segment block.

Lean strategy / thesis relation note: this is the precise Lean form of the thesis intuition that,
after the first minimum sort, distinct connected segments are separated by
incomparability and therefore cannot be connected by a path.
-/
theorem minimumSort_source_eq_of_indexConnected [Preorder X]
    (x : Tuple X) {r s : Fin (minimumSort (X := X) x).length}
    {K L : ConnectedSegment x}
    (hr : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfOutputPosition (X := X) x r) ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hs : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfOutputPosition (X := X) x s) ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L))
    (hconn : IndexConnected (minimumSort (X := X) x) r s) :
    K = L := by
  induction hconn generalizing L with
  | refl =>
      exact source_eq_of_mem_same_sortedSegmentGraphPoint (X := X) x hr hs
  | @tail b c hconn hstep ih =>
      let m : Fin (minimumSortGraphList (X := X) x).length :=
        minimumSortGraphPositionOfOutputPosition (X := X) x b
      have hm_list : (minimumSortGraphList (X := X) x).get m ∈
          minimumSortGraphList (X := X) x := by
        exact List.get_mem (minimumSortGraphList (X := X) x) m
      rcases exists_segment_of_mem_minimumSortGraphList (X := X) x hm_list with
        ⟨M, _hM, hmM⟩
      have hKM : K = M := ih hmM
      have hML : M = L :=
        minimumSort_source_eq_of_indexComparable (X := X) x hmM hs hstep
      exact hKM.trans hML

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cross-block connectivity separation for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: positions in the once-sorted tuple coming from distinct
source segment blocks are not connected.
-/
theorem minimumSort_not_indexConnected_of_get_distinct_sources [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} (hKL : K ≠ L)
    (k l : Fin (minimumSortGraphList (X := X) x).length)
    (hk : (minimumSortGraphList (X := X) x).get k ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hl : (minimumSortGraphList (X := X) x).get l ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L)) :
    ¬ IndexConnected (minimumSort (X := X) x)
      (minimumSortOutputPositionOfGraphPosition (X := X) x k)
      (minimumSortOutputPositionOfGraphPosition (X := X) x l) := by
  intro hconn
  have hk' : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfOutputPosition (X := X) x
        (minimumSortOutputPositionOfGraphPosition (X := X) x k)) ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) := by
    simpa using hk
  have hl' : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfOutputPosition (X := X) x
        (minimumSortOutputPositionOfGraphPosition (X := X) x l)) ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L) := by
    simpa using hl
  exact hKL (minimumSort_source_eq_of_indexConnected (X := X) x hk' hl' hconn)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block characterization for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: for graph-list positions with known source blocks,
connectivity in the once-sorted tuple is equivalent to equality of the source
blocks.
-/
theorem minimumSort_indexConnected_get_iff_source_eq [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x}
    (k l : Fin (minimumSortGraphList (X := X) x).length)
    (hk : (minimumSortGraphList (X := X) x).get k ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K))
    (hl : (minimumSortGraphList (X := X) x).get l ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L)) :
    IndexConnected (minimumSort (X := X) x)
      (minimumSortOutputPositionOfGraphPosition (X := X) x k)
      (minimumSortOutputPositionOfGraphPosition (X := X) x l) ↔ K = L := by
  constructor
  · intro hconn
    have hk' : (minimumSortGraphList (X := X) x).get
        (minimumSortGraphPositionOfOutputPosition (X := X) x
          (minimumSortOutputPositionOfGraphPosition (X := X) x k)) ∈
          distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) := by
      simpa using hk
    have hl' : (minimumSortGraphList (X := X) x).get
        (minimumSortGraphPositionOfOutputPosition (X := X) x
          (minimumSortOutputPositionOfGraphPosition (X := X) x l)) ∈
          distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L) := by
      simpa using hl
    exact minimumSort_source_eq_of_indexConnected (X := X) x hk' hl' hconn
  · intro hKL
    subst L
    exact minimumSort_indexConnected_of_get_same_source (X := X) x k l hk hl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the source segment `K` of the original tuple determines
the connected segment of the once-minimum-sorted tuple that contains the
output position of `K`'s first original index.

Lean strategy / thesis relation note: the thesis treats this correspondence implicitly when saying
that minimum sorting sorts each connected segment separately. Lean names the
map so later lemmas can compare the segment enumeration before and after one
minimum-sort pass.
-/
noncomputable def minimumSortSegmentOfSource [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    ConnectedSegment (minimumSort (X := X) x) :=
  indexSegment (minimumSort (X := X) x)
    (minimumSortOutputPositionOfIndex (X := X) x
      (segmentArrivalIndex (X := X) x K))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the distinguished graph-list position of the first
original index of a source segment belongs to that source block.
-/
theorem minimumSort_graphPosition_arrival_mem_source [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    (minimumSortGraphList (X := X) x).get
        (minimumSortGraphPositionOfIndex (X := X) x
          (segmentArrivalIndex (X := X) x K)) ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) := by
  rw [minimumSortGraphList_get_graphPositionOfIndex (X := X) x
    (segmentArrivalIndex (X := X) x K)]
  apply (mem_distinctFiniteSetSortList_iff (X := X)
    (segmentDistinctFiniteSet x K)).mpr
  exact (mem_segmentDistinctFiniteSet (X := X) x K).mpr
    ⟨segmentArrivalIndex (X := X) x K,
      segmentArrivalIndex_mem (X := X) x K, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: output-position bookkeeping for
`defn:minimum-sorting-rule`.

Informal statement: viewing the output position of an original index as a
graph-list position recovers the graph-list position chosen for that index.
-/
@[simp]
theorem minimumSort_graphPosition_outputPositionOfIndex [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    minimumSortGraphPositionOfOutputPosition (X := X) x
      (minimumSortOutputPositionOfIndex (X := X) x i) =
      minimumSortGraphPositionOfIndex (X := X) x i := by
  apply Fin.ext
  simp [minimumSortGraphPositionOfOutputPosition,
    minimumSortOutputPositionOfIndex]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: every output position whose graph point comes from source
segment `K` belongs to the once-sorted segment associated to `K`.
-/
theorem minimumSort_indexSegment_outputPositionOfGraphPosition [Preorder X]
    (x : Tuple X) {K : ConnectedSegment x}
    (k : Fin (minimumSortGraphList (X := X) x).length)
    (hk : (minimumSortGraphList (X := X) x).get k ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)) :
    indexSegment (minimumSort (X := X) x)
      (minimumSortOutputPositionOfGraphPosition (X := X) x k) =
      minimumSortSegmentOfSource (X := X) x K := by
  let a : Fin (minimumSortGraphList (X := X) x).length :=
    minimumSortGraphPositionOfIndex (X := X) x
      (segmentArrivalIndex (X := X) x K)
  have ha : (minimumSortGraphList (X := X) x).get a ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) := by
    simpa [a] using minimumSort_graphPosition_arrival_mem_source (X := X) x K
  have hconn := minimumSort_indexConnected_of_get_same_source
    (X := X) x k a hk ha
  have hseg := (indexConnected_iff_same_segment (X := X)
    (minimumSort (X := X) x)
    (minimumSortOutputPositionOfGraphPosition (X := X) x k)
    (minimumSortOutputPositionOfGraphPosition (X := X) x a)).mp hconn
  simpa [minimumSortSegmentOfSource, minimumSortOutputPositionOfIndex, a]
    using hseg

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: source bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the original source segment of a graph-list position in
the minimum-sort construction.

Lean strategy / thesis relation note: this is a named choice from the already proved fact that every
graph-list point belongs to exactly one sorted source block.
-/
noncomputable def minimumSortSourceAtGraphPosition [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    ConnectedSegment x :=
  Classical.choose
    (exists_segment_of_mem_minimumSortGraphList (X := X) x
      (List.get_mem (minimumSortGraphList (X := X) x) k))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: source bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the graph-list point at position `k` belongs to the
source block selected by `minimumSortSourceAtGraphPosition`.
-/
theorem minimumSortSourceAtGraphPosition_mem [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    (minimumSortGraphList (X := X) x).get k ∈
      distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet x
          (minimumSortSourceAtGraphPosition (X := X) x k)) :=
  (Classical.choose_spec
    (exists_segment_of_mem_minimumSortGraphList (X := X) x
      (List.get_mem (minimumSortGraphList (X := X) x) k))).2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: source uniqueness for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: if the graph-list point at position `k` lies in the
source block `K`, then the selected source at `k` is `K`.
-/
theorem minimumSortSourceAtGraphPosition_eq_of_mem [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length)
    {K : ConnectedSegment x}
    (hk : (minimumSortGraphList (X := X) x).get k ∈
      distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)) :
    minimumSortSourceAtGraphPosition (X := X) x k = K :=
  source_eq_of_mem_same_sortedSegmentGraphPoint (X := X) x
    (minimumSortSourceAtGraphPosition_mem (X := X) x k) hk

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: at each position of the concatenated minimum-sort graph
list, the source-label shadow names a connected segment whose sorted block
contains the graph point at that same position.

Lean strategy / thesis relation note: this is the tuple-specific specialization of the generic
parallel-flatten lemma. It makes precise the thesis' implicit alignment
between the concatenated graph blocks and their source segments.
-/
theorem exists_minimumSortSourceBlock_of_graphPosition [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    ∃ K : ConnectedSegment x,
      (minimumSortSourceBlocks (X := X) x).flatten.get
          (Fin.cast (length_minimumSortSourceBlocks_flatten (X := X) x).symm k) = K ∧
      (minimumSortGraphList (X := X) x).get k ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) := by
  let block : ConnectedSegment x → List (IndexAugmented X) := fun K =>
    distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)
  have hg : k.1 < (((segmentListByArrival (X := X) x).map block).flatten).length := by
    simpa [block, minimumSortGraphList, minimumSortGraphBlocks] using k.2
  have hs : k.1 < (((segmentListByArrival (X := X) x).map fun K =>
        List.replicate (block K).length K).flatten).length := by
    simpa [block, minimumSortSourceBlocks] using
      (show k.1 < (minimumSortSourceBlocks (X := X) x).flatten.length by
        simp [length_minimumSortSourceBlocks_flatten (X := X) x, k.2])
  rcases exists_label_of_getElem_flatten_blocks
      (Ks := segmentListByArrival (X := X) x) (block := block) hg hs with
    ⟨K, hsource, hgraph⟩
  refine ⟨K, ?_, ?_⟩
  · simpa [block, minimumSortSourceBlocks, List.get_eq_getElem] using hsource
  · simpa [block, minimumSortGraphList, minimumSortGraphBlocks, List.get_eq_getElem]
      using hgraph

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the actual source chosen for a graph-list position agrees
with the source-label shadow at that position.

Lean strategy / thesis relation note: this is the alignment theorem needed to convert the abstract
first-arrival block-order argument into a statement about
`segmentListByArrival (minimumSort x)`.
-/
theorem minimumSortSourceAtGraphPosition_eq_sourceBlocks_get [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    minimumSortSourceAtGraphPosition (X := X) x k =
      (minimumSortSourceBlocks (X := X) x).flatten.get
        (Fin.cast (length_minimumSortSourceBlocks_flatten (X := X) x).symm k) := by
  rcases exists_minimumSortSourceBlock_of_graphPosition (X := X) x k with
    ⟨K, hsource, hmem⟩
  calc
    minimumSortSourceAtGraphPosition (X := X) x k = K :=
      minimumSortSourceAtGraphPosition_eq_of_mem (X := X) x k hmem
    _ = (minimumSortSourceBlocks (X := X) x).flatten.get
        (Fin.cast (length_minimumSortSourceBlocks_flatten (X := X) x).symm k) :=
      hsource.symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: list the original source segment of each graph-list
position in the minimum-sort construction.
-/
noncomputable def minimumSortSourceList [Preorder X]
    (x : Tuple X) : List (ConnectedSegment x) :=
  List.ofFn (minimumSortSourceAtGraphPosition (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the concrete list of selected sources at graph-list
positions agrees with the source-label shadow of the block concatenation.
-/
theorem minimumSortSourceList_eq_sourceBlocks_flatten [Preorder X]
    (x : Tuple X) :
    minimumSortSourceList (X := X) x =
      (minimumSortSourceBlocks (X := X) x).flatten := by
  apply List.ext_get
  · simp [minimumSortSourceList, length_minimumSortSourceBlocks_flatten (X := X) x]
  · intro n hleft hright
    let k : Fin (minimumSortGraphList (X := X) x).length := by
      refine ⟨n, ?_⟩
      simpa [minimumSortSourceList] using hleft
    have halign :=
      minimumSortSourceAtGraphPosition_eq_sourceBlocks_get (X := X) x k
    simpa [minimumSortSourceList, List.get_eq_getElem, k] using halign

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: first-occurrence deletion of the concrete source list
for graph positions recovers the original first-arrival segment list.
-/
theorem firstOccurrenceList_minimumSortSourceList [Preorder X]
    (x : Tuple X) :
    firstOccurrenceList (minimumSortSourceList (X := X) x) =
      segmentListByArrival (X := X) x := by
  rw [minimumSortSourceList_eq_sourceBlocks_flatten (X := X) x,
    firstOccurrenceList_minimumSortSourceBlocks_flatten (X := X) x]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-order bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: scanning the once-sorted tuple by output index gives the
same connected-segment list as mapping each graph-position source to its
once-sorted connected segment.

Lean strategy / thesis relation note: this is the cast-heavy Lean version of the thesis' statement
that the concatenated output tuple is scanned in the same order as the
concatenated graph blocks.
-/
theorem ofFn_indexSegment_minimumSort_eq_map_sourceList [Preorder X]
    (x : Tuple X) :
    List.ofFn (fun i : Fin (minimumSort (X := X) x).length =>
      indexSegment (minimumSort (X := X) x) i) =
      (minimumSortSourceList (X := X) x).map
        (minimumSortSegmentOfSource (X := X) x) := by
  apply List.ext_get
  · simp [minimumSortSourceList, minimumSort, tupleOfList,
      minimumSortList_eq_map_value (X := X) x]
  · intro n hleft hright
    let k : Fin (minimumSortGraphList (X := X) x).length := by
      refine ⟨n, ?_⟩
      simpa [minimumSortSourceList] using hright
    have hseg :=
      minimumSort_indexSegment_outputPositionOfGraphPosition (X := X) x k
        (minimumSortSourceAtGraphPosition_mem (X := X) x k)
    simpa [minimumSortSourceList, List.get_eq_getElem, k,
      minimumSortOutputPositionOfGraphPosition] using hseg

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: source bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the once-sorted connected segment at graph-list position
`k` is the image of the source selected at `k`.
-/
theorem minimumSort_indexSegment_outputPositionOfGraphPosition_eq_sourceAt
    [Preorder X] (x : Tuple X)
    (k : Fin (minimumSortGraphList (X := X) x).length) :
    indexSegment (minimumSort (X := X) x)
      (minimumSortOutputPositionOfGraphPosition (X := X) x k) =
      minimumSortSegmentOfSource (X := X) x
        (minimumSortSourceAtGraphPosition (X := X) x k) :=
  minimumSort_indexSegment_outputPositionOfGraphPosition (X := X) x k
    (minimumSortSourceAtGraphPosition_mem (X := X) x k)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: source bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the graph-list position of an original index has source
equal to that index's original connected segment.
-/
theorem minimumSortSourceAtGraphPosition_graphPositionOfIndex [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    minimumSortSourceAtGraphPosition (X := X) x
      (minimumSortGraphPositionOfIndex (X := X) x i) =
      indexSegment x i := by
  apply minimumSortSourceAtGraphPosition_eq_of_mem (X := X) x
  rw [minimumSortGraphList_get_graphPositionOfIndex (X := X) x i]
  apply (mem_distinctFiniteSetSortList_iff (X := X)
    (segmentDistinctFiniteSet x (indexSegment x i))).mpr
  exact (mem_segmentDistinctFiniteSet (X := X) x (indexSegment x i)).mpr
    ⟨i, rfl, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block characterization for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: two graph-list positions of the once-minimum-sorted tuple
are connected exactly when their original source segments agree.
-/
theorem minimumSort_indexConnected_outputPositionOfGraphPosition_iff_sourceAt_eq
    [Preorder X] (x : Tuple X)
    (k l : Fin (minimumSortGraphList (X := X) x).length) :
    IndexConnected (minimumSort (X := X) x)
      (minimumSortOutputPositionOfGraphPosition (X := X) x k)
      (minimumSortOutputPositionOfGraphPosition (X := X) x l) ↔
      minimumSortSourceAtGraphPosition (X := X) x k =
        minimumSortSourceAtGraphPosition (X := X) x l := by
  exact minimumSort_indexConnected_get_iff_source_eq (X := X) x k l
    (minimumSortSourceAtGraphPosition_mem (X := X) x k)
    (minimumSortSourceAtGraphPosition_mem (X := X) x l)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: distinct original source segments determine distinct
connected segments after one minimum-sort pass.
-/
theorem minimumSortSegmentOfSource_injective [Preorder X]
    (x : Tuple X) :
    Function.Injective (minimumSortSegmentOfSource (X := X) x) := by
  intro K L hKL
  let rK : Fin (minimumSort (X := X) x).length :=
    minimumSortOutputPositionOfIndex (X := X) x
      (segmentArrivalIndex (X := X) x K)
  let rL : Fin (minimumSort (X := X) x).length :=
    minimumSortOutputPositionOfIndex (X := X) x
      (segmentArrivalIndex (X := X) x L)
  have hconn : IndexConnected (minimumSort (X := X) x) rK rL := by
    apply (indexConnected_iff_same_segment (X := X)
      (minimumSort (X := X) x) rK rL).mpr
    simpa [minimumSortSegmentOfSource, rK, rL] using hKL
  have hKmem : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfOutputPosition (X := X) x rK) ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K) := by
    simpa [rK] using minimumSort_graphPosition_arrival_mem_source (X := X) x K
  have hLmem : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfOutputPosition (X := X) x rL) ∈
        distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x L) := by
    simpa [rL] using minimumSort_graphPosition_arrival_mem_source (X := X) x L
  exact minimumSort_source_eq_of_indexConnected (X := X) x hKmem hLmem hconn

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: ordered segment-list equality for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the connected segments of the once-minimum-sorted tuple,
listed by first arrival, are exactly the original connected segments listed
by first arrival and transported through `minimumSortSegmentOfSource`.

Lean strategy / thesis relation note: this is the order refinement of the earlier permutation
statement. It formalizes the thesis' claim that sorting each connected block
and concatenating the blocks in first-arrival order preserves the block
order for the second pass.
-/
theorem segmentListByArrival_minimumSort_eq_map_source [Preorder X]
    (x : Tuple X) :
    segmentListByArrival (X := X) (minimumSort (X := X) x) =
      (segmentListByArrival (X := X) x).map
        (minimumSortSegmentOfSource (X := X) x) := by
  rw [segmentListByArrival]
  rw [← List.ofFn_eq_map]
  rw [ofFn_indexSegment_minimumSort_eq_map_sourceList (X := X) x]
  rw [firstOccurrenceList_map_of_injective
    (minimumSortSegmentOfSource_injective (X := X) x)]
  rw [firstOccurrenceList_minimumSortSourceList (X := X) x]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: every connected segment of the once-minimum-sorted tuple
comes from an original connected segment.
-/
theorem exists_source_of_minimumSortSegment [Preorder X]
    (x : Tuple X) (S : ConnectedSegment (minimumSort (X := X) x)) :
    ∃ K : ConnectedSegment x, S = minimumSortSegmentOfSource (X := X) x K := by
  refine Quotient.inductionOn S ?_
  intro r
  let k : Fin (minimumSortGraphList (X := X) x).length :=
    minimumSortGraphPositionOfOutputPosition (X := X) x r
  have hk_list : (minimumSortGraphList (X := X) x).get k ∈
      minimumSortGraphList (X := X) x :=
    List.get_mem (minimumSortGraphList (X := X) x) k
  rcases exists_segment_of_mem_minimumSortGraphList (X := X) x hk_list with
    ⟨K, _hK, hkK⟩
  refine ⟨K, ?_⟩
  have hseg :=
    minimumSort_indexSegment_outputPositionOfGraphPosition (X := X) x k hkK
  simpa [k] using hseg

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: source segments and once-sorted connected segments are in
bijection via `minimumSortSegmentOfSource`.
-/
theorem minimumSortSegmentOfSource_surjective [Preorder X]
    (x : Tuple X) :
    Function.Surjective (minimumSortSegmentOfSource (X := X) x) := by
  intro S
  rcases exists_source_of_minimumSortSegment (X := X) x S with ⟨K, hK⟩
  exact ⟨K, hK.symm⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: source segments and once-sorted connected segments are in
bijection.

Lean strategy / thesis relation note: the thesis uses this implicitly when arguing that applying the
minimum sorting rule again cannot merge or split the already sorted blocks.
Lean records the bijection as a `Function.Bijective` statement.
-/
theorem minimumSortSegmentOfSource_bijective [Preorder X]
    (x : Tuple X) :
    Function.Bijective (minimumSortSegmentOfSource (X := X) x) :=
  ⟨minimumSortSegmentOfSource_injective (X := X) x,
    minimumSortSegmentOfSource_surjective (X := X) x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: two source segments have the same once-sorted image
exactly when they are equal.
-/
theorem minimumSortSegmentOfSource_eq_iff [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} :
    minimumSortSegmentOfSource (X := X) x K =
      minimumSortSegmentOfSource (X := X) x L ↔ K = L := by
  constructor
  · intro hKL
    exact minimumSortSegmentOfSource_injective (X := X) x hKL
  · intro hKL
    rw [hKL]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: source bookkeeping for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the source selected at a graph-list position is one of
the original first-arrival segment list entries.
-/
theorem minimumSortSourceAtGraphPosition_mem_segmentListByArrival [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    minimumSortSourceAtGraphPosition (X := X) x k ∈
      segmentListByArrival (X := X) x :=
  (Classical.choose_spec
    (exists_segment_of_mem_minimumSortGraphList (X := X) x
      (List.get_mem (minimumSortGraphList (X := X) x) k))).1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the output position assigned to an original index lies
in the once-sorted segment corresponding to that index's original source
segment.
-/
theorem minimumSort_indexSegment_outputPositionOfIndex [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    indexSegment (minimumSort (X := X) x)
      (minimumSortOutputPositionOfIndex (X := X) x i) =
      minimumSortSegmentOfSource (X := X) x (indexSegment x i) := by
  have hmem : (minimumSortGraphList (X := X) x).get
      (minimumSortGraphPositionOfIndex (X := X) x i) ∈
        distinctFiniteSetSortList (X := X)
          (segmentDistinctFiniteSet x (indexSegment x i)) := by
    rw [minimumSortGraphList_get_graphPositionOfIndex (X := X) x i]
    apply (mem_distinctFiniteSetSortList_iff (X := X)
      (segmentDistinctFiniteSet x (indexSegment x i))).mpr
    exact (mem_segmentDistinctFiniteSet (X := X) x
      (indexSegment x i)).mpr ⟨i, rfl, rfl⟩
  simpa [minimumSortOutputPositionOfIndex,
    minimumSortOutputPositionOfGraphPosition] using
    minimumSort_indexSegment_outputPositionOfGraphPosition
      (X := X) x (minimumSortGraphPositionOfIndex (X := X) x i) hmem

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: every once-sorted connected segment appears in the
minimum-sort image of the original segment list, and conversely.

Lean strategy / thesis relation note: this is the set-level version of the thesis' claim that the
same connected blocks are present after one pass. The ordering statement is
handled separately because Lean's `segmentListByArrival` is a concrete list.
-/
theorem mem_map_minimumSortSegmentOfSource_segmentListByArrival_iff
    [Preorder X] (x : Tuple X)
    (S : ConnectedSegment (minimumSort (X := X) x)) :
    S ∈ (segmentListByArrival (X := X) x).map
        (minimumSortSegmentOfSource (X := X) x) ↔
      S ∈ segmentListByArrival (X := X) (minimumSort (X := X) x) := by
  constructor
  · intro hS
    exact mem_segmentListByArrival (X := X) (minimumSort (X := X) x) S
  · intro _hS
    rcases exists_source_of_minimumSortSegment (X := X) x S with ⟨K, hK⟩
    rw [hK]
    exact List.mem_map.mpr
      ⟨K, mem_segmentListByArrival (X := X) x K, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: mapping the original first-arrival segment list through
the once-sort segment correspondence produces no duplicates.
-/
theorem nodup_map_minimumSortSegmentOfSource_segmentListByArrival
    [Preorder X] (x : Tuple X) :
    ((segmentListByArrival (X := X) x).map
      (minimumSortSegmentOfSource (X := X) x)).Nodup :=
  (nodup_segmentListByArrival (X := X) x).map
    (minimumSortSegmentOfSource_injective (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: after one minimum-sort pass, the list of connected
segments is a permutation of the original connected segment list transported
through the source-to-output segment bijection.

Lean strategy / thesis relation note: this proves the block-set preservation part of the thesis
idempotence argument. The next refinement is the order-preservation theorem:
the permutation is in fact the identity because both lists are ordered by
first arrival.
-/
theorem segmentListByArrival_minimumSort_perm_map_source [Preorder X]
    (x : Tuple X) :
    (segmentListByArrival (X := X) (minimumSort (X := X) x)).Perm
      ((segmentListByArrival (X := X) x).map
        (minimumSortSegmentOfSource (X := X) x)) := by
  rw [List.perm_ext_iff_of_nodup
    (nodup_segmentListByArrival (X := X) (minimumSort (X := X) x))
    (nodup_map_minimumSortSegmentOfSource_segmentListByArrival (X := X) x)]
  intro S
  rw [← mem_map_minimumSortSegmentOfSource_segmentListByArrival_iff
    (X := X) x S]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: segment correspondence for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: one minimum-sort pass preserves the number of connected
segments.
-/
theorem length_segmentListByArrival_minimumSort [Preorder X]
    (x : Tuple X) :
    (segmentListByArrival (X := X) (minimumSort (X := X) x)).length =
      (segmentListByArrival (X := X) x).length := by
  have hperm := segmentListByArrival_minimumSort_perm_map_source (X := X) x
  simpa using hperm.length_eq

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-list normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the canonical graph list of the once-minimum-sorted tuple
has output indices `0, ..., n - 1` and the values appearing in the first
minimum-sort graph list.

Lean strategy / thesis relation note: the thesis suppresses the distinction between an original
graph index and the output tuple index after sorting. Lean keeps them
separate: `minimumSortGraphList x` stores original indices, while this list
stores the corresponding output-position indices. The values are unchanged.
-/
noncomputable def minimumSortOutputGraphList [Preorder X]
    (x : Tuple X) : List (IndexAugmented X) :=
  List.ofFn fun k : Fin (minimumSortGraphList (X := X) x).length =>
    IndexAugmented.mk k.1
      (IndexAugmented.value ((minimumSortGraphList (X := X) x).get k))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-list normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: reading the output graph list at graph position `k`
returns the output-indexed version of the graph point at `k`.
-/
theorem minimumSortOutputGraphList_get [Preorder X]
    (x : Tuple X) (k : Fin (minimumSortGraphList (X := X) x).length) :
    (minimumSortOutputGraphList (X := X) x).get
        (Fin.cast (by simp [minimumSortOutputGraphList]) k) =
      IndexAugmented.mk k.1
        (IndexAugmented.value ((minimumSortGraphList (X := X) x).get k)) := by
  simp [minimumSortOutputGraphList, List.get_eq_getElem]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-list normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: forgetting output indices from the once-sorted output
graph list recovers the value list produced by the first minimum-sort pass.
-/
theorem minimumSortOutputGraphList_map_value [Preorder X]
    (x : Tuple X) :
    (minimumSortOutputGraphList (X := X) x).map IndexAugmented.value =
      minimumSortList (X := X) x := by
  rw [minimumSortList_eq_map_value (X := X) x]
  apply List.ext_get
  · simp [minimumSortOutputGraphList]
  · intro n hleft hright
    let k : Fin (minimumSortGraphList (X := X) x).length := by
      refine ⟨n, ?_⟩
      simpa [minimumSortOutputGraphList] using hleft
    simp [minimumSortOutputGraphList, List.get_eq_getElem]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-list normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the output graph list enumerates exactly the graph of the
once-minimum-sorted tuple.

Lean strategy / thesis relation note: in the thesis this is hidden by identifying a tuple with its
ordered graph. Lean states it as a membership equivalence between the list
normal form and the finite graph set.
-/
theorem mem_minimumSortOutputGraphList_iff [Preorder X]
    (x : Tuple X) {p : IndexAugmented X} :
    p ∈ minimumSortOutputGraphList (X := X) x ↔
      p ∈ ((TuplesBasic.graph (minimumSort (X := X) x)).1 :
        Set (IndexAugmented X)) := by
  constructor
  · intro hp
    rw [minimumSortOutputGraphList, List.mem_ofFn] at hp
    rcases hp with ⟨k, rfl⟩
    rw [TuplesBasic.mem_graph]
    refine ⟨minimumSortOutputPositionOfGraphPosition (X := X) x k, ?_⟩
    apply IndexAugmented.ext
    · simp [minimumSortOutputPositionOfGraphPosition]
    · rw [minimumSort_entry_outputPositionOfGraphPosition (X := X) x k]
      simp
  · intro hp
    rcases (TuplesBasic.mem_graph (minimumSort (X := X) x)).mp hp with
      ⟨r, rfl⟩
    rw [minimumSortOutputGraphList, List.mem_ofFn]
    refine ⟨minimumSortGraphPositionOfOutputPosition (X := X) x r, ?_⟩
    apply IndexAugmented.ext
    · simp [minimumSortGraphPositionOfOutputPosition]
    · rw [← minimumSort_entry_outputPositionOfGraphPosition (X := X) x
        (minimumSortGraphPositionOfOutputPosition (X := X) x r)]
      simp

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-list normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the output graph list has no duplicate graph points.
-/
theorem nodup_minimumSortOutputGraphList [Preorder X]
    (x : Tuple X) :
    (minimumSortOutputGraphList (X := X) x).Nodup := by
  rw [minimumSortOutputGraphList]
  rw [List.nodup_ofFn]
  intro k l hkl
  apply Fin.ext
  exact congrArg IndexAugmented.index hkl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-list normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the graph list built by applying the minimum sorting rule
a second time is a permutation of the output-index graph list of the first
pass.

Lean strategy / thesis relation note: this is the set/enumeration part of the thesis' idempotence
claim. The theorem does not yet assert that the orders agree; that is the
remaining contiguous-block argument.
-/
theorem minimumSortGraphList_minimumSort_perm_outputGraphList [Preorder X]
    (x : Tuple X) :
    (minimumSortGraphList (X := X) (minimumSort (X := X) x)).Perm
      (minimumSortOutputGraphList (X := X) x) := by
  rw [List.perm_ext_iff_of_nodup
    (nodup_minimumSortGraphList (X := X) (minimumSort (X := X) x))
    (nodup_minimumSortOutputGraphList (X := X) x)]
  intro p
  rw [mem_minimumSortGraphList_iff (X := X) (minimumSort (X := X) x)]
  rw [mem_minimumSortOutputGraphList_iff (X := X) x]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-membership normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the output-indexed graph point at position `k` lies in
the once-sorted connected segment obtained by transporting the original
source segment attached to graph-list position `k`.

Lean strategy / thesis relation note: this is the formal version of the thesis' statement that a
point remains inside the same connected block after the first minimum-sort
permutation; only its graph index has changed from the original index to the
output position.
-/
theorem minimumSortOutputGraphList_get_mem_segmentPointListByIndex_source
    [Preorder X] (x : Tuple X)
    (k : Fin (minimumSortGraphList (X := X) x).length) :
    (minimumSortOutputGraphList (X := X) x).get
        (Fin.cast (by simp [minimumSortOutputGraphList]) k) ∈
      segmentPointListByIndex (X := X) (minimumSort (X := X) x)
        (minimumSortSegmentOfSource (X := X) x
          (minimumSortSourceAtGraphPosition (X := X) x k)) := by
  rw [mem_segmentPointListByIndex_iff]
  apply (mem_segmentDistinctFiniteSet (X := X)
    (minimumSort (X := X) x)
    (minimumSortSegmentOfSource (X := X) x
      (minimumSortSourceAtGraphPosition (X := X) x k))).mpr
  refine ⟨minimumSortOutputPositionOfGraphPosition (X := X) x k, ?_, ?_⟩
  · exact minimumSort_indexSegment_outputPositionOfGraphPosition_eq_sourceAt
      (X := X) x k
  · rw [minimumSortOutputGraphList_get (X := X) x k]
    apply IndexAugmented.ext
    · simp [minimumSortOutputPositionOfGraphPosition]
    · rw [minimumSort_entry_outputPositionOfGraphPosition (X := X) x k]
      simp

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block-membership normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: a graph point belongs to the transported once-sorted
segment associated to an original segment `K` exactly when it is the
output-indexed graph point at a graph-list position whose source label is
`K`.

Lean strategy / thesis relation note: this is the set-level form of the thesis' block-preservation
claim. It does not yet identify the order of the points inside the block,
but it proves that no point can enter or leave the transported block.
-/
theorem mem_segmentPointListByIndex_minimumSort_segmentOfSource_iff
    [Preorder X] (x : Tuple X) (K : ConnectedSegment x)
    {p : IndexAugmented X} :
    p ∈ segmentPointListByIndex (X := X) (minimumSort (X := X) x)
        (minimumSortSegmentOfSource (X := X) x K) ↔
      ∃ k : Fin (minimumSortGraphList (X := X) x).length,
        minimumSortSourceAtGraphPosition (X := X) x k = K ∧
        p = (minimumSortOutputGraphList (X := X) x).get
          (Fin.cast (by simp [minimumSortOutputGraphList]) k) := by
  constructor
  · intro hp
    have hp_set : p ∈
        ((segmentDistinctFiniteSet (X := X) (minimumSort (X := X) x)
          (minimumSortSegmentOfSource (X := X) x K)).1 :
          Set (IndexAugmented X)) := by
      exact (mem_segmentPointListByIndex_iff (X := X)
        (minimumSort (X := X) x)
        (minimumSortSegmentOfSource (X := X) x K)).mp hp
    rcases (mem_segmentDistinctFiniteSet (X := X)
        (minimumSort (X := X) x)
        (minimumSortSegmentOfSource (X := X) x K)).mp hp_set with
      ⟨r, hr, hp_eq⟩
    let k : Fin (minimumSortGraphList (X := X) x).length :=
      minimumSortGraphPositionOfOutputPosition (X := X) x r
    refine ⟨k, ?_, ?_⟩
    · have hseg_source :
          indexSegment (minimumSort (X := X) x) r =
            minimumSortSegmentOfSource (X := X) x
              (minimumSortSourceAtGraphPosition (X := X) x k) := by
        have h :=
          minimumSort_indexSegment_outputPositionOfGraphPosition_eq_sourceAt
            (X := X) x k
        simpa [k] using h
      have hseg_K :
          indexSegment (minimumSort (X := X) x) r =
            minimumSortSegmentOfSource (X := X) x K := hr
      apply minimumSortSegmentOfSource_injective (X := X) x
      exact hseg_source.symm.trans hseg_K
    · rw [hp_eq, minimumSortOutputGraphList_get (X := X) x k]
      apply IndexAugmented.ext
      · simp [k, minimumSortGraphPositionOfOutputPosition]
      · rw [← minimumSort_entry_outputPositionOfGraphPosition (X := X) x k]
        simp [k]
  · rintro ⟨k, hsource, rfl⟩
    have hmem :=
      minimumSortOutputGraphList_get_mem_segmentPointListByIndex_source
        (X := X) x k
    simpa [hsource] using hmem

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the output-indexed graph block associated to a source
segment `K`, obtained by filtering graph-list positions by their source label.

Lean strategy / thesis relation note: the thesis treats the block as a contiguous summand of
`\bigoplus_r \varsigma(K_r)`. Lean first defines it as a source-filtered
sublist; the later order theorem identifies this filtered list with the
contiguous summand.
-/
noncomputable def minimumSortOutputGraphBlockOfSource [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) : List (IndexAugmented X) := by
  classical
  exact ((List.finRange (minimumSortGraphList (X := X) x).length).filter
    (fun k => minimumSortSourceAtGraphPosition (X := X) x k = K)).map
      fun k => (minimumSortOutputGraphList (X := X) x).get
        (Fin.cast (by simp [minimumSortOutputGraphList]) k)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the source-filtered output block has exactly the graph
points of the transported once-sorted connected segment.
-/
theorem mem_minimumSortOutputGraphBlockOfSource_iff [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) {p : IndexAugmented X} :
    p ∈ minimumSortOutputGraphBlockOfSource (X := X) x K ↔
      p ∈ segmentPointListByIndex (X := X) (minimumSort (X := X) x)
        (minimumSortSegmentOfSource (X := X) x K) := by
  classical
  constructor
  · intro hp
    rw [minimumSortOutputGraphBlockOfSource, List.mem_map] at hp
    rcases hp with ⟨k, hk, rfl⟩
    have hsource : minimumSortSourceAtGraphPosition (X := X) x k = K := by
      exact of_decide_eq_true (List.mem_filter.mp hk).2
    exact
      (mem_segmentPointListByIndex_minimumSort_segmentOfSource_iff
        (X := X) x K).mpr ⟨k, hsource, rfl⟩
  · intro hp
    rcases
        (mem_segmentPointListByIndex_minimumSort_segmentOfSource_iff
          (X := X) x K).mp hp with
      ⟨k, hsource, hp_eq⟩
    rw [minimumSortOutputGraphBlockOfSource, List.mem_map]
    refine ⟨k, ?_, hp_eq.symm⟩
    rw [List.mem_filter]
    exact ⟨List.mem_finRange k, decide_eq_true hsource⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block order normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: inside a source-filtered output graph block, output
indices strictly increase.
-/
theorem pairwise_index_minimumSortOutputGraphBlockOfSource [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    List.Pairwise (fun p q : IndexAugmented X =>
      IndexAugmented.index p < IndexAugmented.index q)
      (minimumSortOutputGraphBlockOfSource (X := X) x K) := by
  classical
  let n := (minimumSortGraphList (X := X) x).length
  let pred : Fin n → Bool := fun k =>
    decide (minimumSortSourceAtGraphPosition (X := X) x k = K)
  let f : Fin n → IndexAugmented X := fun k =>
    (minimumSortOutputGraphList (X := X) x).get
      (Fin.cast (by simp [minimumSortOutputGraphList, n]) k)
  have hfin : List.Pairwise (fun k l : Fin n => k < l) (List.finRange n) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simpa using hij
  have hfiltered : List.Pairwise (fun k l : Fin n => k < l)
      ((List.finRange n).filter pred) :=
    List.Pairwise.filter pred hfin
  have hmap : List.Pairwise (fun p q : IndexAugmented X =>
        IndexAugmented.index p < IndexAugmented.index q)
      (((List.finRange n).filter pred).map f) := by
    refine List.Pairwise.map f ?_ hfiltered
    intro k l hkl
    simpa [f, minimumSortOutputGraphList_get (X := X) x,
      minimumSortOutputGraphList] using hkl
  simpa [minimumSortOutputGraphBlockOfSource, n, pred, f] using hmap

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block order normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the stored output indices in the source-filtered output
block strictly increase with list position.
-/
theorem index_strict_minimumSortOutputGraphBlockOfSource [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    ∀ i j : Fin (minimumSortOutputGraphBlockOfSource (X := X) x K).length,
      i < j →
        IndexAugmented.index
          ((minimumSortOutputGraphBlockOfSource (X := X) x K).get i) <
        IndexAugmented.index
          ((minimumSortOutputGraphBlockOfSource (X := X) x K).get j) := by
  intro i j hij
  exact (pairwise_index_minimumSortOutputGraphBlockOfSource
    (X := X) x K).rel_get_of_lt hij

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: idempotence bridge for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: if the second minimum-sort graph list is exactly the
once-sorted output graph list, then the second pass has the same value list as
the first pass.

Lean strategy / thesis relation note: this isolates the remaining thesis argument. What remains is
to prove that the connected-segment blocks of `minimumSort x` are exactly the
contiguous output blocks created during the first pass.
-/
theorem minimumSortList_minimumSort_eq_of_graphList_eq_outputGraphList
    [Preorder X] (x : Tuple X)
    (hgraph : minimumSortGraphList (X := X) (minimumSort (X := X) x) =
      minimumSortOutputGraphList (X := X) x) :
    minimumSortList (X := X) (minimumSort (X := X) x) =
      minimumSortList (X := X) x := by
  rw [minimumSortList_eq_map_value (X := X) (minimumSort (X := X) x)]
  rw [hgraph]
  exact minimumSortOutputGraphList_map_value (X := X) x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: idempotence bridge for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the graph-list normal form above is sufficient to prove
idempotence of the tuple-valued minimum sorting construction.
-/
theorem minimumSort_idempotent_of_graphList_eq_outputGraphList [Preorder X]
    (x : Tuple X)
    (hgraph : minimumSortGraphList (X := X) (minimumSort (X := X) x) =
      minimumSortOutputGraphList (X := X) x) :
    minimumSort (X := X) (minimumSort (X := X) x) =
      minimumSort (X := X) x := by
  have hlist :=
    minimumSortList_minimumSort_eq_of_graphList_eq_outputGraphList
      (X := X) x hgraph
  simpa [minimumSort] using congrArg (tupleOfList (X := X)) hlist

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: Lean transport helper for the proposition after
`defn:minimum-sorting-rule`.

Informal statement: casting a finite index along an equality transported
through `Fin` preserves the underlying natural-number index.

Lean strategy / thesis relation note: this is not mathematical content in the thesis. It is a
type-theoretic bookkeeping lemma needed when comparing tuples whose lengths
are propositionally, rather than definitionally, equal.
-/
theorem fin_cast_congrArg_val {n m : ℕ} (h : n = m) (i : Fin n) :
    ((cast (congrArg Fin h) i : Fin m).1 = i.1) := by
  cases h
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite-list helper for the permutation property after
`defn:minimum-sorting-rule`.

Informal statement: in a duplicate-free list, `List.get` is injective on
finite positions.
-/
theorem list_get_injective_of_nodup {α : Type u} {l : List α}
    (h : l.Nodup) : Function.Injective (fun i : Fin l.length => l.get i) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpair := List.nodup_iff_pairwise_ne.mp h
    have hneq := (List.pairwise_iff_get.mp hpair) i j hlt
    exact hneq hij
  · have hpair := List.nodup_iff_pairwise_ne.mp h
    have hneq := (List.pairwise_iff_get.mp hpair) j i hgt
    exact hneq hij.symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: finite-list helper for the permutation property after
`defn:minimum-sorting-rule`.

Informal statement: a duplicate-free natural-number list whose members are
exactly `0, ..., n - 1` induces a finite permutation of `Fin n`.

Lean strategy / thesis relation note: this packages the thesis' statement that the concatenated
projected index blocks form a bijection of the tuple domain.
-/
noncomputable def finPermutationOfNatList (l : List ℕ) (n : ℕ)
    (hlen : l.length = n)
    (hmem : ∀ k : ℕ, k ∈ l ↔ k < n)
    (hnodup : l.Nodup) : FinitePermutation n :=
  Equiv.ofBijective
    (fun i : Fin n =>
      let k : Fin l.length := Fin.cast hlen.symm i
      ⟨l.get k, (hmem (l.get k)).mp (List.get_mem l k)⟩)
    (by
      constructor
      · intro i j hij
        have hget : l.get (Fin.cast hlen.symm i) =
            l.get (Fin.cast hlen.symm j) := by
          exact congrArg Fin.val hij
        have hcast : Fin.cast hlen.symm i = Fin.cast hlen.symm j :=
          list_get_injective_of_nodup hnodup hget
        apply Fin.ext
        simpa using congrArg Fin.val hcast
      · intro y
        have hy_mem : y.1 ∈ l := (hmem y.1).mpr y.2
        rcases List.mem_iff_get.mp hy_mem with ⟨k, hk⟩
        refine ⟨Fin.cast hlen k, ?_⟩
        apply Fin.ext
        change l.get (Fin.cast hlen.symm (Fin.cast hlen k)) = y.1
        simpa using hk)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: concatenated permutation `π` in the proof after
`defn:minimum-sorting-rule`.

Informal statement: the projected index list of the minimum sorting
construction induces a finite permutation of the original tuple domain.
-/
noncomputable def minimumSortPermutation [Preorder X]
    (x : Tuple X) : FinitePermutation x.length :=
  finPermutationOfNatList (minimumSortIndexList (X := X) x) x.length
    (length_minimumSortIndexList (X := X) x)
    (fun _ => mem_minimumSortIndexList_iff (X := X) x)
    (nodup_minimumSortIndexList (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph/value compatibility in the proof after
`defn:minimum-sorting-rule`.

Informal statement: every graph point appearing in the concatenated
minimum-sort graph list has value equal to the original tuple entry at its
projected index.
-/
theorem minimumSortGraphList_get_value_eq_entry_index [Preorder X]
    (x : Tuple X) (i : Fin (minimumSortGraphList (X := X) x).length)
    (hidx : IndexAugmented.index ((minimumSortGraphList (X := X) x).get i) <
      x.length) :
    IndexAugmented.value ((minimumSortGraphList (X := X) x).get i) =
      Tuple.entry x
        ⟨IndexAugmented.index ((minimumSortGraphList (X := X) x).get i), hidx⟩ := by
  let p : IndexAugmented X := (minimumSortGraphList (X := X) x).get i
  have hp_list : p ∈ minimumSortGraphList (X := X) x := by
    simp [p]
  have hp_graph : p ∈ ((TuplesBasic.graph x).1 : Set (IndexAugmented X)) :=
    (mem_minimumSortGraphList_iff (X := X) x).mp hp_list
  rcases (TuplesBasic.mem_graph x).mp hp_graph with ⟨j, hj⟩
  have hidx_eq : IndexAugmented.index p = j.1 := by
    simpa [p] using congrArg IndexAugmented.index hj
  have hfin : (⟨IndexAugmented.index p, hidx⟩ : Fin x.length) = j :=
    Fin.ext hidx_eq
  have hvalue : IndexAugmented.value p = Tuple.entry x j := by
    simpa [p] using congrArg IndexAugmented.value hj
  rw [hfin]
  exact hvalue

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: value-list projection in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: at each position, the minimum-sort value list is the value
projection of the graph point at the same concatenated position.
-/
theorem minimumSortList_get_eq_graphList_get_value [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    let iL : Fin (minimumSortList (X := X) x).length :=
      Fin.cast (length_minimumSortList (X := X) x).symm i
    let iMap : Fin ((minimumSortGraphList (X := X) x).map IndexAugmented.value).length :=
      Fin.cast (by rw [minimumSortList_eq_map_value (X := X) x]) iL
    let iG : Fin (minimumSortGraphList (X := X) x).length :=
      ⟨iMap.1, by simpa using iMap.2⟩
    (minimumSortList (X := X) x).get iL =
      IndexAugmented.value ((minimumSortGraphList (X := X) x).get iG) := by
  intro iL iMap iG
  have hleft := List.get_of_eq (minimumSortList_eq_map_value (X := X) x) iL
  trans (List.map IndexAugmented.value (minimumSortGraphList (X := X) x)).get iMap
  · simpa [iMap] using hleft
  · simp [List.get_eq_getElem, iG]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: tuple-level projection in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the entry of the minimum-sorted tuple at a given output
position is the value projection of the graph point at the same concatenated
position.

Lean strategy / thesis relation note: the thesis silently identifies the tuple produced by a graph
list with its value projection. Lean states the required casts explicitly.
-/
theorem minimumSort_entry_eq_graphList_get_value [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    let iT : Fin (minimumSort (X := X) x).length :=
      Fin.cast (length_minimumSort (X := X) x).symm i
    let iL : Fin (minimumSortList (X := X) x).length :=
      Fin.cast (length_minimumSortList (X := X) x).symm i
    let iMap : Fin ((minimumSortGraphList (X := X) x).map IndexAugmented.value).length :=
      Fin.cast (by rw [minimumSortList_eq_map_value (X := X) x]) iL
    let iG : Fin (minimumSortGraphList (X := X) x).length :=
      ⟨iMap.1, by simpa using iMap.2⟩
    Tuple.entry (minimumSort (X := X) x) iT =
      IndexAugmented.value ((minimumSortGraphList (X := X) x).get iG) := by
  intro iT iL iMap iG
  simpa [minimumSort, tupleOfList, Tuple.entry, iT, iL, iMap, iG] using
    minimumSortList_get_eq_graphList_get_value (X := X) x i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: projected permutation compatibility in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the permutation induced by the projected index list sends
each output position to the original index of the graph point at the same
concatenated position.
-/
theorem minimumSortPermutation_val_eq_graphList_get_index [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    let iL : Fin (minimumSortList (X := X) x).length :=
      Fin.cast (length_minimumSortList (X := X) x).symm i
    let iMap : Fin ((minimumSortGraphList (X := X) x).map IndexAugmented.value).length :=
      Fin.cast (by rw [minimumSortList_eq_map_value (X := X) x]) iL
    let iG : Fin (minimumSortGraphList (X := X) x).length :=
      ⟨iMap.1, by simpa using iMap.2⟩
    (minimumSortPermutation (X := X) x i).1 =
      IndexAugmented.index ((minimumSortGraphList (X := X) x).get iG) := by
  intro iL iMap iG
  unfold minimumSortPermutation finPermutationOfNatList
  simp [minimumSortIndexList, List.get_eq_getElem, iG, iMap, iL]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: pointwise permutation property in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the value at output position `i` of the minimum-sort list
is the original tuple entry at the index selected by the minimum-sort
permutation.
-/
theorem minimumSortList_get_eq_entry_minimumSortPermutation [Preorder X]
    (x : Tuple X) (i : Fin x.length) :
    (minimumSortList (X := X) x).get
        (Fin.cast (length_minimumSortList (X := X) x).symm i) =
      Tuple.entry x (minimumSortPermutation (X := X) x i) := by
  let iL : Fin (minimumSortList (X := X) x).length :=
    Fin.cast (length_minimumSortList (X := X) x).symm i
  let iMap : Fin ((minimumSortGraphList (X := X) x).map IndexAugmented.value).length :=
    Fin.cast (by rw [minimumSortList_eq_map_value (X := X) x]) iL
  let iG : Fin (minimumSortGraphList (X := X) x).length :=
    ⟨iMap.1, by simpa using iMap.2⟩
  have hleft : (minimumSortList (X := X) x).get iL =
      IndexAugmented.value ((minimumSortGraphList (X := X) x).get iG) := by
    simpa [iL, iMap, iG] using
      minimumSortList_get_eq_graphList_get_value (X := X) x i
  have hperm_val : (minimumSortPermutation (X := X) x i).1 =
      IndexAugmented.index ((minimumSortGraphList (X := X) x).get iG) := by
    simpa [iL, iMap, iG] using
      minimumSortPermutation_val_eq_graphList_get_index (X := X) x i
  have hidx : IndexAugmented.index ((minimumSortGraphList (X := X) x).get iG) <
      x.length := by
    rw [← hperm_val]
    exact (minimumSortPermutation (X := X) x i).2
  have hvalue :=
    minimumSortGraphList_get_value_eq_entry_index (X := X) x iG hidx
  have hfin :
      (⟨IndexAugmented.index ((minimumSortGraphList (X := X) x).get iG),
        hidx⟩ : Fin x.length) = minimumSortPermutation (X := X) x i :=
    Fin.ext hperm_val.symm
  calc
    (minimumSortList (X := X) x).get
        (Fin.cast (length_minimumSortList (X := X) x).symm i)
        = IndexAugmented.value ((minimumSortGraphList (X := X) x).get iG) := by
          simpa [iL] using hleft
    _ = Tuple.entry x
        ⟨IndexAugmented.index ((minimumSortGraphList (X := X) x).get iG),
          hidx⟩ := hvalue
    _ = Tuple.entry x (minimumSortPermutation (X := X) x i) := by
          rw [hfin]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: permutation half of the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the minimum-sort tuple is obtained by permuting the
original tuple by the concatenated projected index permutation.

Lean strategy / thesis relation note: the thesis identifies tuples with equal finite domains
silently. Lean stores the length in a sigma type, so the proof uses
heterogeneous function extensionality to transport along the verified length
equality.
-/
theorem minimumSort_eq_permute_minimumSortPermutation [Preorder X]
    (x : Tuple X) :
    minimumSort (X := X) x =
      permute x (minimumSortPermutation (X := X) x) := by
  unfold minimumSort tupleOfList permute
  apply Sigma.ext
  · exact length_minimumSortList (X := X) x
  · let f : Fin (minimumSortList (X := X) x).length → X :=
      fun i => (minimumSortList (X := X) x).get i
    let g : Fin x.length → X :=
      fun i => Tuple.entry x (minimumSortPermutation (X := X) x i)
    let hLen : (minimumSortList (X := X) x).length = x.length :=
      length_minimumSortList (X := X) x
    have hα : Fin (minimumSortList (X := X) x).length = Fin x.length :=
      congrArg Fin hLen
    change f ≍ g
    refine Function.hfunext hα ?_
    intro a a' haa
    have hcast : cast hα a = a' := (cast_eq_iff_heq).mpr haa
    rw [← hcast]
    apply heq_of_eq
    have hfin : Fin.cast hLen.symm (cast hα a) = a := by
      apply Fin.ext
      calc
        (Fin.cast hLen.symm (cast hα a)).1 = (cast hα a).1 := by
          simp
        _ = a.1 := fin_cast_congrArg_val hLen a
    simpa [f, g, hfin, hLen] using
      minimumSortList_get_eq_entry_minimumSortPermutation (X := X) x (cast hα a)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: cross-block argument in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: if two sorted blocks come from distinct connected
segments, then no element of the later block can be strictly smaller than an
element of the earlier block.

Lean strategy / thesis relation note: the thesis cites incomparability of distinct segments. Lean
spells out the projection through `segmentDistinctFiniteSet` and then applies
`not_indexComparable_of_distinct_segments`.
-/
theorem not_lt_of_mem_distinct_sortedSegmentBlocks [Preorder X]
    (x : Tuple X) {K L : ConnectedSegment x} (hKL : K ≠ L)
    {a b : X}
    (ha : a ∈ ((distinctFiniteSetSortList (X := X)
      (segmentDistinctFiniteSet x K)).map IndexAugmented.value))
    (hb : b ∈ ((distinctFiniteSetSortList (X := X)
      (segmentDistinctFiniteSet x L)).map IndexAugmented.value)) :
    ¬ b < a := by
  intro hlt
  rcases (List.mem_map.mp ha) with ⟨p, hp, hpa⟩
  rcases (List.mem_map.mp hb) with ⟨q, hq, hqb⟩
  have hp_set : p ∈ ((segmentDistinctFiniteSet x K).1 : Set (IndexAugmented X)) :=
    mem_distinctFiniteSetSortList_subset (X := X) (segmentDistinctFiniteSet x K) hp
  have hq_set : q ∈ ((segmentDistinctFiniteSet x L).1 : Set (IndexAugmented X)) :=
    mem_distinctFiniteSetSortList_subset (X := X) (segmentDistinctFiniteSet x L) hq
  rcases (mem_segmentDistinctFiniteSet (X := X) x K).mp hp_set with ⟨i, hiK, hp_eq⟩
  rcases (mem_segmentDistinctFiniteSet (X := X) x L).mp hq_set with ⟨j, hjL, hq_eq⟩
  have ha_entry : a = Tuple.entry x i := by
    simpa [hp_eq] using hpa.symm
  have hb_entry : b = Tuple.entry x j := by
    simpa [hq_eq] using hqb.symm
  have hle : Tuple.entry x j ≤ Tuple.entry x i := by
    rw [← ha_entry, ← hb_entry]
    exact le_of_lt hlt
  exact not_indexComparable_of_distinct_segments x hKL hiK hjL (Or.inr hle)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: sortedness induction in the proposition after
`defn:minimum-sorting-rule`.

Informal statement: concatenating sorted blocks indexed by a duplicate-free
list of connected segments is sorted. Inside each block sortedness comes from
`defn:sorting-finite-sets`; across blocks it comes from incomparability of
distinct connected segments.
-/
theorem pairwise_flatten_sortedSegmentBlocks [Preorder X]
    (x : Tuple X) (Ks : List (ConnectedSegment x)) (hKs : Ks.Nodup) :
    List.Pairwise (fun a b : X => ¬ b < a)
      ((Ks.map fun K =>
        (distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)).map
          IndexAugmented.value).flatten) := by
  classical
  induction Ks with
  | nil =>
      simp
  | cons K Ks ih =>
      rw [List.nodup_cons] at hKs
      rw [List.map_cons, List.flatten_cons, List.pairwise_append]
      refine ⟨pairwise_minimumSortBlock (X := X) x K, ih hKs.2, ?_⟩
      intro a ha b hb
      rw [List.mem_flatten] at hb
      rcases hb with ⟨block, hblock_mem, hb_block⟩
      rw [List.mem_map] at hblock_mem
      rcases hblock_mem with ⟨L, hLmem, hblock_eq⟩
      subst block
      have hKL : K ≠ L := by
        intro hEq
        exact hKs.1 (by simpa [hEq] using hLmem)
      exact not_lt_of_mem_distinct_sortedSegmentBlocks (X := X) x hKL ha hb_block

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: sortedness part of the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the concatenated list underlying the minimum sorting
construction is sorted.
-/
theorem pairwise_minimumSortList [Preorder X]
    (x : Tuple X) :
    List.Pairwise (fun a b : X => ¬ b < a)
      (minimumSortList (X := X) x) := by
  simpa [minimumSortList, minimumSortBlocks] using
    pairwise_flatten_sortedSegmentBlocks (X := X) x
      (segmentListByArrival (X := X) x) (nodup_segmentListByArrival (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: sortedness half of the proposition after
`defn:minimum-sorting-rule`.

Informal statement: the minimum sorting construction produces a sorted tuple.

Lean strategy / thesis relation note: the permutation/bijection half of the proposition is still a
separate proof obligation; this theorem verifies the codomain
`\mathscr{S}(X,\preceq)` part.
-/
theorem minimumSort_isSorted [Preorder X]
    (x : Tuple X) :
    IsSorted (minimumSort (X := X) x) := by
  apply isSorted_tupleOfList_of_pairwise
  exact pairwise_minimumSortList (X := X) x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: proposition after `defn:minimum-sorting-rule`.

Informal statement: the minimum sorting construction is a sorting rule: it
produces a sorted tuple and is obtained by a finite permutation of the input.
-/
noncomputable def minimumSortingRule [Preorder X] : SortingRule X where
  sort := minimumSort (X := X)
  sorted_sort := minimumSort_isSorted (X := X)
  exists_perm := fun x =>
    ⟨minimumSortPermutation (X := X) x,
      minimumSort_eq_permute_minimumSortPermutation (X := X) x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the graph list used by the second minimum-sort pass is
the flattening of the connected segments of `minimumSort x`, but those
segments are exactly the original first-arrival segments transported through
`minimumSortSegmentOfSource`.

Lean strategy / thesis relation note: this is the formal version of the thesis' "apply the same
minimum rule again to the already formed blocks" step. The theorem uses the
previous ordered segment-list equality, not merely the weaker permutation
statement.
-/
theorem minimumSortGraphList_minimumSort_eq_flatten_segmentPointLists_source
    [Preorder X] (x : Tuple X) :
    minimumSortGraphList (X := X) (minimumSort (X := X) x) =
      ((segmentListByArrival (X := X) x).map fun K =>
        segmentPointListByIndex (X := X) (minimumSort (X := X) x)
          (minimumSortSegmentOfSource (X := X) x K)).flatten := by
  rw [minimumSortGraphList_eq_flatten_segmentPointLists_of_isSorted
    (X := X) (minimumSort (X := X) x) (minimumSort_isSorted (X := X) x)]
  rw [segmentListByArrival_minimumSort_eq_map_source (X := X) x]
  simp only [List.map_map, Function.comp_def]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: value-list normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the value list produced by a second minimum-sort pass is
the flattening of the value projections of the transported once-sorted
connected segments.
-/
theorem minimumSortList_minimumSort_eq_flatten_segmentPointValues_source
    [Preorder X] (x : Tuple X) :
    minimumSortList (X := X) (minimumSort (X := X) x) =
      ((segmentListByArrival (X := X) x).map fun K =>
        (segmentPointListByIndex (X := X) (minimumSort (X := X) x)
          (minimumSortSegmentOfSource (X := X) x K)).map
            IndexAugmented.value).flatten := by
  rw [minimumSortList_eq_map_value (X := X) (minimumSort (X := X) x)]
  rw [minimumSortGraphList_minimumSort_eq_flatten_segmentPointLists_source
    (X := X) x]
  rw [List.map_flatten]
  simp only [List.map_map, Function.comp_def]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block order normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: inside a source-filtered output graph block, later values
are never strictly smaller than earlier values.

Lean strategy / thesis relation note: this is where the first pass's sortedness is used. Since the
source-filtered block is listed by increasing output index, `minimumSort x`
being sorted gives the finite-set sorter's value-order condition.
-/
theorem pairwise_value_minimumSortOutputGraphBlockOfSource [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    List.Pairwise (fun p q : IndexAugmented X =>
      ¬ IndexAugmented.value q < IndexAugmented.value p)
      (minimumSortOutputGraphBlockOfSource (X := X) x K) := by
  classical
  let n := (minimumSortGraphList (X := X) x).length
  let pred : Fin n → Bool := fun k =>
    decide (minimumSortSourceAtGraphPosition (X := X) x k = K)
  let f : Fin n → IndexAugmented X := fun k =>
    (minimumSortOutputGraphList (X := X) x).get
      (Fin.cast (by simp [minimumSortOutputGraphList, n]) k)
  have hfin : List.Pairwise (fun k l : Fin n => k < l) (List.finRange n) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simpa using hij
  have hfiltered : List.Pairwise (fun k l : Fin n => k < l)
      ((List.finRange n).filter pred) :=
    List.Pairwise.filter pred hfin
  have hmap : List.Pairwise (fun p q : IndexAugmented X =>
        ¬ IndexAugmented.value q < IndexAugmented.value p)
      (((List.finRange n).filter pred).map f) := by
    refine List.Pairwise.map f ?_ hfiltered
    intro k l hkl
    have hle :
        minimumSortOutputPositionOfGraphPosition (X := X) x k ≤
          minimumSortOutputPositionOfGraphPosition (X := X) x l := by
      exact le_of_lt (by
        simpa [minimumSortOutputPositionOfGraphPosition, n] using hkl)
    have hsorted := minimumSort_isSorted (X := X) x
      (minimumSortOutputPositionOfGraphPosition (X := X) x k)
      (minimumSortOutputPositionOfGraphPosition (X := X) x l) hle
    simpa [f, minimumSortOutputGraphList_get (X := X) x,
      minimumSort_entry_outputPositionOfGraphPosition (X := X) x,
      minimumSortOutputGraphList] using hsorted
  simpa [minimumSortOutputGraphBlockOfSource, n, pred, f] using hmap

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the transported once-sorted segment block is exactly the
source-filtered output graph block.

Lean strategy / thesis relation note: the proof follows the thesis strategy: the block has the same
finite graph set, its values are already sorted, and its output indices
strictly increase, so the recursive least-index finite-set sorter leaves it
unchanged.
-/
theorem minimumSortOutputGraphBlockOfSource_eq_segmentPointListByIndex
    [Preorder X] (x : Tuple X) (K : ConnectedSegment x) :
    minimumSortOutputGraphBlockOfSource (X := X) x K =
      segmentPointListByIndex (X := X) (minimumSort (X := X) x)
        (minimumSortSegmentOfSource (X := X) x K) := by
  let y : Tuple X := minimumSort (X := X) x
  let S : ConnectedSegment y := minimumSortSegmentOfSource (X := X) x K
  have hsort_output :
      distinctFiniteSetSortList (X := X)
          (segmentDistinctFiniteSet (X := X) y S) =
        minimumSortOutputGraphBlockOfSource (X := X) x K := by
    apply distinctFiniteSetSortList_eq_self_of_pairwise_indexed
    · intro p
      rw [mem_minimumSortOutputGraphBlockOfSource_iff (X := X) x K]
      rw [mem_segmentPointListByIndex_iff (X := X) y S]
    · exact pairwise_value_minimumSortOutputGraphBlockOfSource (X := X) x K
    · exact index_strict_minimumSortOutputGraphBlockOfSource (X := X) x K
  have hsort_segment :
      distinctFiniteSetSortList (X := X)
          (segmentDistinctFiniteSet (X := X) y S) =
        segmentPointListByIndex (X := X) y S :=
    distinctFiniteSetSortList_segment_eq_segmentPointListByIndex_of_isSorted
      (X := X) y S (by simpa [y] using minimumSort_isSorted (X := X) x)
  exact hsort_output.symm.trans hsort_segment

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the output graph block obtained by zipping
graph-position source labels with output graph points and filtering by a
source segment.
-/
noncomputable def minimumSortOutputGraphBlockOfSourceZip [Preorder X]
    (x : Tuple X) (K : ConnectedSegment x) : List (IndexAugmented X) := by
  classical
  exact (((minimumSortSourceList (X := X) x).zip
    (minimumSortOutputGraphList (X := X) x)).filter
      (fun z : ConnectedSegment x × IndexAugmented X => z.1 = K)).map
        Prod.snd

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: block normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the source-filtered output graph block can equivalently
be obtained by zipping the graph-position source labels with the output graph
list, filtering by the source label, and projecting graph points.

Lean strategy / thesis relation note: this is a purely finite-list bridge between Lean's positional
definition of `minimumSortOutputGraphBlockOfSource` and the thesis'
source-labelled block notation.
-/
theorem minimumSortOutputGraphBlockOfSource_eq_zip_filter
    [Preorder X] (x : Tuple X) (K : ConnectedSegment x) :
    minimumSortOutputGraphBlockOfSource (X := X) x K =
      minimumSortOutputGraphBlockOfSourceZip (X := X) x K := by
  classical
  let n := (minimumSortGraphList (X := X) x).length
  let s : Fin n → ConnectedSegment x :=
    minimumSortSourceAtGraphPosition (X := X) x
  let f : Fin n → IndexAugmented X := fun k =>
    IndexAugmented.mk k.1
      (IndexAugmented.value ((minimumSortGraphList (X := X) x).get k))
  have hdirect :
      ((List.finRange n).filter (fun i => decide (s i = K))).map f =
        minimumSortOutputGraphBlockOfSourceZip (X := X) x K := by
    simpa [minimumSortSourceList, minimumSortOutputGraphList, n, s, f] using
      map_filter_finRange_eq_map_snd_filter_zip_ofFn
        (s := s) (f := f) K
  have hblock_direct :
      minimumSortOutputGraphBlockOfSource (X := X) x K =
        ((List.finRange n).filter (fun i => decide (s i = K))).map f := by
    rw [minimumSortOutputGraphBlockOfSource]
    change (((List.finRange n).filter
      (fun k => decide (minimumSortSourceAtGraphPosition (X := X) x k = K))).map
        (fun k => (minimumSortOutputGraphList (X := X) x).get
          (Fin.cast (by simp [minimumSortOutputGraphList]) k))) =
            ((List.finRange n).filter (fun i => decide (s i = K))).map f
    simp only [s]
    apply List.map_congr_left
    intro k _hk
    have hget := minimumSortOutputGraphList_get (X := X) x k
    simpa [n, f, List.get_eq_getElem] using hget
  exact hblock_direct.trans hdirect

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: final contiguous-block normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: flattening the source-filtered output graph blocks in
the original first-arrival segment order reconstructs the output graph list
of the first minimum-sort pass.

Lean strategy / thesis relation note: this is the formal version of the thesis' final block-order
argument. The source-label shadow is a concatenation of nonempty constant
blocks in first-arrival order, so filtering by those labels and flattening in
that same order leaves the output graph list unchanged.
-/
theorem flatten_minimumSortOutputGraphBlocks_eq_outputGraphList
    [Preorder X] (x : Tuple X) :
    ((segmentListByArrival (X := X) x).map fun K =>
      minimumSortOutputGraphBlockOfSource (X := X) x K).flatten =
      minimumSortOutputGraphList (X := X) x := by
  classical
  let Ks : List (ConnectedSegment x) := segmentListByArrival (X := X) x
  let n : ConnectedSegment x → ℕ := fun K =>
    (distinctFiniteSetSortList (X := X) (segmentDistinctFiniteSet x K)).length
  have hblocks :
      ((Ks.map fun K => minimumSortOutputGraphBlockOfSource (X := X) x K).flatten) =
        ((Ks.map fun K =>
          minimumSortOutputGraphBlockOfSourceZip (X := X) x K).flatten) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro K _hK
    exact minimumSortOutputGraphBlockOfSource_eq_zip_filter (X := X) x K
  have hsource :
      minimumSortSourceList (X := X) x =
        ((Ks.map fun K => List.replicate (n K) K).flatten) := by
    simpa [Ks, n, minimumSortSourceBlocks] using
      minimumSortSourceList_eq_sourceBlocks_flatten (X := X) x
  have hlen :
      (minimumSortOutputGraphList (X := X) x).length =
        ((Ks.map fun K => List.replicate (n K) K).flatten).length := by
    rw [← hsource]
    simp [minimumSortOutputGraphList, minimumSortSourceList]
  rw [hblocks]
  simp only [minimumSortOutputGraphBlockOfSourceZip]
  rw [hsource]
  exact flatten_filter_zip_replicateLabels_eq_values
    (Ks := Ks) (n := n) (values := minimumSortOutputGraphList (X := X) x)
    (nodup_segmentListByArrival (X := X) x) hlen

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: global block normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: the graph list used by the second minimum-sort pass is
the flattening of the source-filtered output graph blocks, in the original
first-arrival order.
-/
theorem minimumSortGraphList_minimumSort_eq_flatten_outputGraphBlocks
    [Preorder X] (x : Tuple X) :
    minimumSortGraphList (X := X) (minimumSort (X := X) x) =
      ((segmentListByArrival (X := X) x).map fun K =>
        minimumSortOutputGraphBlockOfSource (X := X) x K).flatten := by
  rw [minimumSortGraphList_minimumSort_eq_flatten_segmentPointLists_source
    (X := X) x]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro K _hK
  exact (minimumSortOutputGraphBlockOfSource_eq_segmentPointListByIndex
    (X := X) x K).symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: graph-list normal form for the corollary after
`defn:minimum-sorting-rule`.

Informal statement: applying the minimum sorting construction a second time
uses exactly the output graph list of the first minimum-sort pass.
-/
theorem minimumSortGraphList_minimumSort_eq_outputGraphList
    [Preorder X] (x : Tuple X) :
    minimumSortGraphList (X := X) (minimumSort (X := X) x) =
      minimumSortOutputGraphList (X := X) x := by
  rw [minimumSortGraphList_minimumSort_eq_flatten_outputGraphBlocks
    (X := X) x]
  rw [flatten_minimumSortOutputGraphBlocks_eq_outputGraphList (X := X) x]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: corollary after `defn:minimum-sorting-rule`.

Informal statement: the minimum sorting rule is idempotent.

Lean strategy / thesis relation note: the proof now follows the thesis block proof: one pass
creates sorted connected blocks in first-arrival order; the second pass sees
the same output-indexed graph blocks in the same order and therefore returns
the same tuple.
-/
theorem minimumSort_idempotent [Preorder X] (x : Tuple X) :
    minimumSort (X := X) (minimumSort (X := X) x) =
      minimumSort (X := X) x :=
  minimumSort_idempotent_of_graphList_eq_outputGraphList
    (X := X) x (minimumSortGraphList_minimumSort_eq_outputGraphList (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: corollary after `defn:minimum-sorting-rule`.

Informal statement: as a sorting rule, the minimum sorting rule is
idempotent.
-/
theorem minimumSortingRule_idempotent [Preorder X] (x : Tuple X) :
    (minimumSortingRule (X := X)).sort
        ((minimumSortingRule (X := X)).sort x) =
      (minimumSortingRule (X := X)).sort x :=
  minimumSort_idempotent (X := X) x

end TuplesSorting
end MarketRepresentation
end Foundations
end Thesis
