import Foundations.MarketRepresentation.FiniteSets

/-!
# Market Representation: Tuples, Graphs, and Sorted Tuples

Blueprint module for
`1 - theoretical foundations/2_chapter_market_representations.tex`,
sections "Tuples and Markets" and the first part of "Sorted Tuples".

Planned formal content:

* `defn:tuple` / `defn:tuple-space`;
* tuple length;
* sorted tuples;
* finite permutations;
* graph map from tuples to distinct finite subsets;
* `prop:graph-injects`.

Lean note: fixed-length tuples should be represented by `Fin n → X`; the
variable-length tuple space should be a sigma type `Σ n : ℕ, Fin n → X`.
-/

universe u

namespace Thesis
namespace Foundations
namespace MarketRepresentation

/-- Thesis `defn:tuple` / `defn:tuple-space`.

Lean-native variable-length tuples over `X`. The first coordinate is the length
and the second coordinate is a function from `Fin n`.
-/
abbrev Tuple (X : Type u) : Type u :=
  Σ n : ℕ, Fin n → X

namespace Tuple

variable {X : Type u}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Tuples and Markets".

Original label: length map after `defn:tuple`.

Informal statement: the length of a Lean-native tuple is the finite domain
size carried by the sigma type.
-/
def length (x : Tuple X) : ℕ :=
  x.1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Tuples and Markets".

Original label: empty tuple remark after `defn:tuple`.

Informal statement: the empty tuple has domain `Fin 0`.
-/
def empty (X : Type u) : Tuple X :=
  ⟨0, Fin.elim0⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Tuples and Markets".

Original label: coordinate evaluation for `defn:tuple`.

Informal statement: the `i`th entry of a tuple.
-/
def entry (x : Tuple X) (i : Fin x.length) : X :=
  x.2 i

@[simp]
theorem length_mk (n : ℕ) (x : Fin n → X) :
    length (Sigma.mk n x : Tuple X) = n :=
  rfl

@[simp]
theorem entry_mk (n : ℕ) (x : Fin n → X) (i : Fin n) :
    entry (Sigma.mk n x : Tuple X) i = x i :=
  rfl

@[simp]
theorem empty_length : length (empty X) = 0 :=
  rfl

end Tuple

namespace TuplesBasic

open FiniteSets
open FiniteSets.FiniteSubsets

variable {X : Type u}

/-! ## Sorted Tuples -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:sorted-tuples`.

Informal statement: a tuple is sorted when later entries are never strictly
smaller than earlier entries.

Lean strategy / thesis relation note: the thesis indexes the domain by `{1, ..., n}`. Lean uses
`Fin n`, so indices are zero-based; the order on `Fin n` is the inherited
natural-number order.
-/
def IsSorted [Preorder X] (x : Tuple X) : Prop :=
  ∀ i j : Fin x.length, i ≤ j → ¬ Tuple.entry x j < Tuple.entry x i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: set `\mathscr{S}(X,\preceq)` in `defn:sorted-tuples`.

Informal statement: the type of tuples together with a proof that they are
sorted.
-/
abbrev SortedTuple (X : Type u) [Preorder X] : Type u :=
  {x : Tuple X // IsSorted x}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: empty tuple case following `defn:sorted-tuples`.

Informal statement: the empty tuple is sorted.
-/
theorem empty_isSorted [Preorder X] : IsSorted (Tuple.empty X) := by
  intro i
  exact Fin.elim0 i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: proposition after `defn:sorted-tuples`.

Informal statement: over a total order, the thesis sortedness condition is
equivalent to the usual monotonicity condition `i ≤ j → xᵢ ≤ xⱼ`.
-/
theorem isSorted_iff_monotone [LinearOrder X] (x : Tuple X) :
    IsSorted x ↔ ∀ i j : Fin x.length, i ≤ j → Tuple.entry x i ≤ Tuple.entry x j := by
  constructor
  · intro hx i j hij
    exact le_of_not_gt (hx i j hij)
  · intro hx i j hij
    exact not_lt_of_ge (hx i j hij)

/-! ## Finite Permutations -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:finite-permutations`.

Informal statement: an `n`-permutation is a bijection of the finite index
type `Fin n`.
-/
abbrev FinitePermutation (n : ℕ) : Type :=
  Equiv.Perm (Fin n)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: union `\mathscr{P}` in `defn:finite-permutations`.

Informal statement: the type of finite permutations with their length.
-/
abbrev FinitePermutations : Type :=
  Σ n : ℕ, FinitePermutation n

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: permutation action used in `defn:sorting-permutations`.

Informal statement: permuting a tuple reindexes its entries by a bijection of
its finite domain.
-/
def permute (x : Tuple X) (π : FinitePermutation x.length) : Tuple X :=
  ⟨x.length, fun i => Tuple.entry x (π i)⟩

@[simp]
theorem permute_length (x : Tuple X) (π : FinitePermutation x.length) :
    (permute x π).length = x.length :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `defn:sorting-permutations`.

Informal statement: a finite permutation of a tuple's domain is a sorting
permutation when the permuted tuple is sorted.
-/
def IsTupleSortingPermutation [Preorder X] (x : Tuple X)
    (π : FinitePermutation x.length) : Prop :=
  IsSorted (permute x π)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: set `\mathscr{P}_{\bm{x}}` in
`defn:sorting-permutations`.

Informal statement: the type of sorting permutations for a fixed tuple.

Lean strategy / thesis relation note: the thesis writes this as a subset of all finite permutations
of `domain(x)`. Lean represents the subset as a subtype whose first component
is a finite permutation and whose second component is the proof that applying
it produces a sorted tuple.
-/
abbrev TupleSortingPermutations [Preorder X] (x : Tuple X) : Type :=
  {π : FinitePermutation x.length // IsTupleSortingPermutation x π}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: direct consequence of `defn:sorting-permutations`.

Informal statement: applying a sorting permutation gives a sorted tuple.
-/
theorem tupleSortingPermutation_isSorted [Preorder X] (x : Tuple X)
    (π : TupleSortingPermutations x) : IsSorted (permute x π.1) :=
  π.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: identity permutation observation for finite permutations.

Informal statement: applying the identity permutation leaves a tuple
unchanged.
-/
theorem permute_refl (x : Tuple X) :
    permute x (Equiv.refl (Fin x.length)) = x := by
  cases x with
  | mk n f =>
      rfl

/-! ## Tuple Graphs -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: graph map `\Gamma` before `prop:graph-injects`.

Informal statement: the graph of a tuple is the distinct finite set of its
indexed entries.

Lean strategy / thesis relation note: the thesis writes graph points as `(i,x(i))`; Lean uses the
index-augmented carrier introduced for distinct finite sets.
-/
noncomputable def graph (x : Tuple X) : DistinctFiniteSubsets X := by
  let point : Fin x.length → IndexAugmented X := fun i =>
    IndexAugmented.mk i.1 (Tuple.entry x i)
  let s : FiniteSubsets (IndexAugmented X) :=
    ⟨Set.range point, Set.finite_range point⟩
  have hdistinct : HasDistinctIndices s := by
    intro n a b ha hb
    rcases ha with ⟨i, hi⟩
    rcases hb with ⟨j, hj⟩
    have hiidx : i.1 = n := by
      simpa [point] using congrArg IndexAugmented.index hi
    have hjidx : j.1 = n := by
      simpa [point] using congrArg IndexAugmented.index hj
    have hij : i = j := Fin.ext (hiidx.trans hjidx.symm)
    have hia : Tuple.entry x i = a := by
      simpa [point] using congrArg IndexAugmented.value hi
    have hjb : Tuple.entry x j = b := by
      simpa [point] using congrArg IndexAugmented.value hj
    calc
      a = Tuple.entry x i := hia.symm
      _ = Tuple.entry x j := by rw [hij]
      _ = b := hjb
  exact ⟨s, hdistinct⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: membership characterization for graph map `\Gamma`.

Informal statement: a point belongs to the graph iff it is one of the indexed
tuple entries.
-/
theorem mem_graph (x : Tuple X) {p : IndexAugmented X} :
    p ∈ ((graph x).1 : Set (IndexAugmented X)) ↔
      ∃ i : Fin x.length, p = IndexAugmented.mk i.1 (Tuple.entry x i) := by
  constructor
  · intro hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: index set of the graph map.

Informal statement: the indices appearing in the tuple graph are exactly the
indices below the tuple length.
-/
theorem mem_indexSet_graph (x : Tuple X) {n : ℕ} :
    n ∈ (DistinctFiniteSubsets.indexSet (graph x) : Set ℕ) ↔ n < x.length := by
  constructor
  · intro hn
    rcases (DistinctFiniteSubsets.mem_indexSet (graph x)).mp hn with ⟨a, ha⟩
    rcases (mem_graph x).mp ha with ⟨i, hi⟩
    have hiidx : i.1 = n := by
      simpa using (congrArg IndexAugmented.index hi).symm
    simpa [hiidx] using i.2
  · intro hn
    let i : Fin x.length := ⟨n, hn⟩
    exact (DistinctFiniteSubsets.mem_indexSet (graph x)).mpr
      ⟨Tuple.entry x i, by
        rw [mem_graph]
        exact ⟨i, rfl⟩⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: natural-number helper for `prop:graph-injects`.

Informal statement: equal initial finite segments of natural numbers have the
same endpoint.
-/
theorem length_eq_of_initialSegment_eq {n m : ℕ}
    (h : ({k : ℕ | k < n} : Set ℕ) = {k : ℕ | k < m}) : n = m := by
  apply le_antisymm
  · by_contra hnm
    have hmn : m < n := Nat.lt_of_not_ge hnm
    have hm : m ∈ ({k : ℕ | k < n} : Set ℕ) := hmn
    rw [h] at hm
    exact (Nat.lt_irrefl m) hm
  · by_contra hmn
    have hnm : n < m := Nat.lt_of_not_ge hmn
    have hn : n ∈ ({k : ℕ | k < m} : Set ℕ) := hnm
    rw [← h] at hn
    exact (Nat.lt_irrefl n) hn

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: `prop:graph-injects`.

Informal statement: the tuple graph map into distinct finite sets is
injective.
-/
theorem graph_injective : Function.Injective (graph (X := X)) := by
  intro x y hxy
  cases x with
  | mk n f =>
      cases y with
      | mk m g =>
          have hidx :
              ({k : ℕ | k < n} : Set ℕ) = {k : ℕ | k < m} := by
            ext k
            constructor
            · intro hk
              have hk' :
                  k ∈ (DistinctFiniteSubsets.indexSet
                    (graph (Sigma.mk n f : Tuple X)) : Set ℕ) :=
                (mem_indexSet_graph (Sigma.mk n f : Tuple X)).mpr hk
              rw [hxy] at hk'
              exact (mem_indexSet_graph (Sigma.mk m g : Tuple X)).mp hk'
            · intro hk
              have hk' :
                  k ∈ (DistinctFiniteSubsets.indexSet
                    (graph (Sigma.mk m g : Tuple X)) : Set ℕ) :=
                (mem_indexSet_graph (Sigma.mk m g : Tuple X)).mpr hk
              rw [← hxy] at hk'
              exact (mem_indexSet_graph (Sigma.mk n f : Tuple X)).mp hk'
          have hlen : n = m := length_eq_of_initialSegment_eq hidx
          subst m
          congr
          funext i
          have hmem_f :
              IndexAugmented.mk i.1 (f i) ∈
                ((graph (Sigma.mk n f : Tuple X)).1 : Set (IndexAugmented X)) := by
            rw [mem_graph]
            exact ⟨i, rfl⟩
          have hmem_g :
              IndexAugmented.mk i.1 (f i) ∈
                ((graph (Sigma.mk n g : Tuple X)).1 : Set (IndexAugmented X)) := by
            simpa [hxy] using hmem_f
          rcases (mem_graph (Sigma.mk n g : Tuple X)).mp hmem_g with ⟨j, hj⟩
          have hij : j = i := by
            apply Fin.ext
            simpa using (congrArg IndexAugmented.index hj).symm
          have hvalue : f i = g j := by
            simpa using congrArg IndexAugmented.value hj
          rw [hij] at hvalue
          exact hvalue

end TuplesBasic
end MarketRepresentation
end Foundations
end Thesis
