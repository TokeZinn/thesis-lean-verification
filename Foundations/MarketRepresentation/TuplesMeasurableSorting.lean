import Foundations.MarketRepresentation.TuplesMetricTopology
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Order.PiLex

/-!
# Market Representation: Measurable Sorting

Blueprint module for
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Planned formal content:

* `exmp:sort-discont`;
* `thm:measurable-partition`;
* `defn:permutation-map`;
* `prop:permuting-continuous`;
* `prop:permutations-countable`;
* valid sorting sets `V_π`;
* induced sorting maps;
* measurable partition for sorting;
* `thm:measurable-sorting-exists`;
* `cor:many-measurable-sorting-exists`;
* `thm:minimal-sorting-measurable`.
-/

namespace Thesis
namespace Foundations
namespace MarketRepresentation
namespace TuplesMeasurableSorting

open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
open Thesis.Foundations.MarketRepresentation.TuplesSorting
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets

universe u v w

variable {X : Type u}

/-! ## Sorting Discontinuity Example -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: the point space in the example is `ℝ²` with
lexicographic order.

Lean strategy / thesis relation note: Lean represents `ℝ²` as `Fin 2 → ℝ` and wraps it in `Lex` to
use mathlib's lexicographic order. The metric is the ordinary product
extended metric transported across the `Lex` wrapper; the order and topology
are intentionally independent, exactly as in the thesis example.
-/
abbrev SortDiscontPoint : Type :=
  Lex (Fin 2 → ℝ)

noncomputable instance sortDiscontPointEMetricSpace :
    EMetricSpace SortDiscontPoint :=
  EMetricSpace.induced (fun z : SortDiscontPoint => ofLex z)
    (by
      intro a b h
      exact ofLex.injective h)
    inferInstance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: the Lean encoding of a point `(x,y) ∈ ℝ²`.
-/
noncomputable def sortDiscontPair (x y : ℝ) : SortDiscontPoint :=
  toLex (fun i : Fin 2 => if i = 0 then x else y)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: lexicographic comparison by first coordinate.
-/
theorem sortDiscontPair_lt_of_first_lt {a b c d : ℝ} (h : a < c) :
    sortDiscontPair a b < sortDiscontPair c d := by
  change Pi.Lex (· < ·) (fun {i : Fin 2} => (· < ·))
    (fun i : Fin 2 => if i = 0 then a else b)
    (fun i : Fin 2 => if i = 0 then c else d)
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    exact False.elim ((not_lt_of_ge (Fin.zero_le j)) hj)
  · simpa using h

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: when first coordinates agree, lexicographic comparison is
comparison by second coordinate.
-/
theorem sortDiscontPair_lt_of_second_lt {a b d : ℝ} (h : b < d) :
    sortDiscontPair a b < sortDiscontPair a d := by
  change Pi.Lex (· < ·) (fun {i : Fin 2} => (· < ·))
    (fun i : Fin 2 => if i = 0 then a else b)
    (fun i : Fin 2 => if i = 0 then a else d)
  refine ⟨1, ?_, ?_⟩
  · intro j hj
    fin_cases j <;> simp at hj ⊢
  · simpa using h

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: the `n`th fixed-length coordinate function
`((0,1), (1/(n+1),0))`. The thesis writes `1/n`; Lean indexes sequences from
`0`, so the same convergent tail is written as `1/(n+1)`.
-/
noncomputable def sortDiscontSequenceCoord (n : ℕ) :
    Fin 2 → SortDiscontPoint :=
  fun i =>
    if i = 0 then
      sortDiscontPair 0 1
    else
      sortDiscontPair ((1 : ℝ) / (n + 1)) 0

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: the limiting fixed-length coordinate function
`((0,1), (0,0))`.
-/
noncomputable def sortDiscontLimitCoord : Fin 2 → SortDiscontPoint :=
  fun i =>
    if i = 0 then
      sortDiscontPair 0 1
    else
      sortDiscontPair 0 0

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: the sequence of sorted length-two tuples from the thesis.
-/
noncomputable def sortDiscontSequence (n : ℕ) :
    Tuple SortDiscontPoint :=
  Sigma.mk 2 (sortDiscontSequenceCoord n)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: the tuple limit of `sortDiscontSequence`.
-/
noncomputable def sortDiscontLimit : Tuple SortDiscontPoint :=
  Sigma.mk 2 sortDiscontLimitCoord

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: every tuple in the example sequence is sorted.
-/
theorem sortDiscontSequence_isSorted (n : ℕ) :
    IsSorted (sortDiscontSequence n) := by
  rw [Thesis.Foundations.MarketRepresentation.TuplesBasic.isSorted_iff_monotone
    (X := SortDiscontPoint) (sortDiscontSequence n)]
  change ∀ i j : Fin 2, i ≤ j →
    sortDiscontSequenceCoord n i ≤ sortDiscontSequenceCoord n j
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · exact le_of_lt (sortDiscontPair_lt_of_first_lt
      (by positivity : (0 : ℝ) < (1 : ℝ) / (n + 1)))
  · simp at hij
  · exact le_rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: the limit tuple is not sorted, since `(0,0)` is
lexicographically smaller than `(0,1)` but appears second.
-/
theorem sortDiscontLimit_not_isSorted :
    ¬ IsSorted sortDiscontLimit := by
  change ¬ IsSorted (Sigma.mk 2 sortDiscontLimitCoord : Tuple SortDiscontPoint)
  intro hsorted
  let i0 : Fin (Tuple.length
      (Sigma.mk 2 sortDiscontLimitCoord : Tuple SortDiscontPoint)) :=
    ⟨0, by simp [Tuple.length]⟩
  let i1 : Fin (Tuple.length
      (Sigma.mk 2 sortDiscontLimitCoord : Tuple SortDiscontPoint)) :=
    ⟨1, by simp [Tuple.length]⟩
  have hle : i0 ≤ i1 := by
    simp [i0, i1]
  have hnot := hsorted i0 i1 hle
  have hbad :
      Tuple.entry
          (Sigma.mk 2 sortDiscontLimitCoord : Tuple SortDiscontPoint) i1 <
        Tuple.entry
          (Sigma.mk 2 sortDiscontLimitCoord : Tuple SortDiscontPoint) i0 := by
    simpa [i0, i1, sortDiscontLimitCoord, Tuple.entry, Tuple.length] using
      (sortDiscontPair_lt_of_second_lt
        (a := (0 : ℝ)) (b := (0 : ℝ)) (d := (1 : ℝ)) zero_lt_one)
  exact hnot hbad

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: for points of the form `(a,0)` and `(c,0)`, the product
metric on `ℝ²` reduces to the metric between first coordinates.
-/
theorem sortDiscontPair_edist_first (a c : ℝ) :
    edist (sortDiscontPair a 0) (sortDiscontPair c 0) = edist a c := by
  change edist (fun i : Fin 2 => if i = 0 then a else 0)
      (fun i : Fin 2 => if i = 0 then c else 0) = edist a c
  rw [edist_pi_def]
  simp [Finset.sup, Finset.fold]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: the sorted sequence converges in the tuple Hausdorff
topology to `sortDiscontLimit`.

Lean strategy / thesis relation note: the proof is the thesis argument in metric form. The tuple
length is fixed at `2`, so the tuple Hausdorff distance is bounded by the
coordinate supremum, and only the first coordinate of the second point moves,
with `1/(n+1) → 0`.
-/
theorem sortDiscontSequence_tendsto :
    letI : TopologicalSpace (Tuple SortDiscontPoint) :=
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
    Filter.Tendsto sortDiscontSequence Filter.atTop (nhds sortDiscontLimit) := by
  letI : TopologicalSpace (Tuple SortDiscontPoint) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  rw [EMetric.tendsto_nhds]
  intro ε hε
  have hreal :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
        Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent := (EMetric.tendsto_nhds.mp hreal) ε hε
  exact hevent.mono (fun n hn => by
    have hle :
        edist (sortDiscontSequence n) sortDiscontLimit ≤
          coordinateEDistSup (sortDiscontSequenceCoord n)
            sortDiscontLimitCoord := by
      simpa [sortDiscontSequence, sortDiscontLimit] using
        fixedLength_edist_le_coordinateEDistSup
          (X := SortDiscontPoint)
          (sortDiscontSequenceCoord n) sortDiscontLimitCoord
    have hsup :
        coordinateEDistSup (sortDiscontSequenceCoord n)
            sortDiscontLimitCoord =
          edist (sortDiscontPair ((1 : ℝ) / (n + 1)) 0)
            (sortDiscontPair 0 0) := by
      simp [coordinateEDistSup, sortDiscontSequenceCoord,
        sortDiscontLimitCoord, Finset.sup, Finset.fold]
    have hdist :
        edist (sortDiscontPair ((1 : ℝ) / (n + 1)) 0)
            (sortDiscontPair 0 0) < ε := by
      simpa [sortDiscontPair_edist_first] using hn
    exact lt_of_le_of_lt (by simpa [hsup] using hle) hdist)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `exmp:sort-discont`.

Informal statement: because the lexicographic order is total, any sorting
rule agrees on this example. If it were continuous at the limit tuple, its
values on the sorted sequence would converge both to the unsorted limit and to
the sorted value of that limit, forcing the limit to be sorted. This
contradicts `sortDiscontLimit_not_isSorted`.
-/
theorem sortDiscont_sortingRule_not_continuousAt
    (σ : SortingRule SortDiscontPoint) :
    letI : TopologicalSpace (Tuple SortDiscontPoint) :=
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
    ¬ ContinuousAt σ.sort sortDiscontLimit := by
  letI : TopologicalSpace (Tuple SortDiscontPoint) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  intro hcont
  have hsort_tendsto :
      Filter.Tendsto
        (fun n : ℕ => σ.sort (sortDiscontSequence n)) Filter.atTop
        (nhds (σ.sort sortDiscontLimit)) :=
    Filter.Tendsto.comp hcont sortDiscontSequence_tendsto
  have hsort_eq :
      (fun n : ℕ => σ.sort (sortDiscontSequence n)) =
        sortDiscontSequence := by
    funext n
    exact sortingRule_sort_eq_self_of_isSorted
      (X := SortDiscontPoint) σ (sortDiscontSequence_isSorted n)
  have hseq_to_sort :
      Filter.Tendsto sortDiscontSequence Filter.atTop
        (nhds (σ.sort sortDiscontLimit)) := by
    simpa [hsort_eq] using hsort_tendsto
  have hlim_eq : sortDiscontLimit = σ.sort sortDiscontLimit :=
    tendsto_nhds_unique sortDiscontSequence_tendsto hseq_to_sort
  have hsorted_lim : IsSorted sortDiscontLimit := by
    rw [hlim_eq]
    exact σ.sorted_sort sortDiscontLimit
  exact sortDiscontLimit_not_isSorted hsorted_lim

/-! ## Measurable Partitions -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-list bookkeeping for remaining tails.

Informal statement: an element belongs to the dropped tail `l.drop r`
exactly when it occurs in the original list at some position `s ≥ r`.

Lean strategy / thesis relation note: this is the list-index version of the thesis notation
`C^{(r)}` for a finite remainder after earlier selections have been removed.
-/
theorem list_mem_drop_iff_exists_get_ge {α : Type u}
    (l : List α) (r : ℕ) (a : α) :
    a ∈ l.drop r ↔
      ∃ s : Fin l.length, r ≤ s.1 ∧ l.get s = a := by
  constructor
  · intro ha
    rcases List.mem_iff_get.mp ha with ⟨k, hk⟩
    have hk_lt : k.1 + r < l.length := by
      apply Nat.add_lt_of_lt_sub
      simpa [List.length_drop] using k.2
    let s : Fin l.length := ⟨r + k.1, by simpa [Nat.add_comm] using hk_lt⟩
    refine ⟨s, ?_, ?_⟩
    · exact Nat.le_add_right r k.1
    · have hk_getElem : (l.drop r)[k.1] = a := by
        simpa [List.get_eq_getElem] using hk
      have hdrop : (l.drop r)[k.1] = l[r + k.1] := by
        exact List.getElem_drop
      simpa [s, List.get_eq_getElem, hk_getElem] using hdrop.symm
  · rintro ⟨s, hrs, hs⟩
    have hk_lt : s.1 - r < (l.drop r).length := by
      simpa [List.length_drop] using Nat.sub_lt_sub_right hrs s.2
    let k : Fin (l.drop r).length := ⟨s.1 - r, hk_lt⟩
    apply List.mem_iff_get.mpr
    refine ⟨k, ?_⟩
    have hdrop : (l.drop r)[k.1] = l[r + k.1] := by
      exact List.getElem_drop
    have hidx : r + k.1 = s.1 := by
      simpa [k] using Nat.add_sub_of_le hrs
    let s' : Fin l.length := ⟨r + k.1, by
      rw [hidx]
      exact s.2⟩
    have hs' : s' = s := Fin.ext hidx
    have hdrop_get : (l.drop r).get k = l.get s' := by
      simp [k, s', List.get_eq_getElem, hdrop]
    rw [hdrop_get, hs']
    exact hs

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `thm:measurable-partition`.

Informal statement: if `(S n)` is a countable measurable partition of `α`,
then a function `f : α → β` is measurable iff every restriction
`f|_{S n}` is measurable for the trace sigma-algebra.

Lean strategy / thesis relation note: Lean represents the trace sigma-algebra on `S n` by the
subtype measurable space. The proof follows the thesis proof: reconstruct
`f ⁻¹' B` as a countable union of the measurable images of the restricted
preimages on each partition cell. The disjointness assumption is included to
match the thesis statement, although the measurability argument only needs a
countable measurable cover.
-/
theorem measurable_iff_measurable_restrict_partition
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n))
    (_hdisjoint : Pairwise fun n m => Disjoint (S n) (S m))
    (hcover : ⋃ n, S n = Set.univ) {f : α → β} :
    Measurable f ↔ ∀ n : ℕ, Measurable (fun x : S n => f x) := by
  constructor
  · intro hf n
    exact hf.comp measurable_subtype_coe
  · intro hrestr t ht
    have himage : ∀ n : ℕ,
        MeasurableSet (Subtype.val '' {x : S n | f x ∈ t}) := by
      intro n
      have ht_sub : MeasurableSet {x : S n | f x ∈ t} :=
        ht.preimage (hrestr n)
      exact MeasurableSet.subtype_image (hS n) ht_sub
    have hpre : f ⁻¹' t = ⋃ n : ℕ, Subtype.val '' {x : S n | f x ∈ t} := by
      ext x
      constructor
      · intro hx
        have hxcover : x ∈ ⋃ n : ℕ, S n := by
          rw [hcover]
          trivial
        rcases Set.mem_iUnion.mp hxcover with ⟨n, hn⟩
        exact Set.mem_iUnion.2 ⟨n, ⟨⟨x, hn⟩, hx, rfl⟩⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨n, y, hy, hyx⟩
        simpa [hyx] using hy
    rw [hpre]
    exact MeasurableSet.iUnion himage

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurable-pasting lemma used in
`thm:minimal-sorting-measurable`.

Informal statement: a function is measurable if it is measurable on each set
of a countable measurable cover.

Lean strategy / thesis relation note: the thesis states this for partitions. The proof only needs a
cover; disjointness is relevant for uniqueness of the branch description, not
for measurability of the pasted map.
-/
theorem measurable_of_measurable_restrict_countable_cover
    {α : Type u} {β : Type v} {ι : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    {S : ι → Set α} (hS : ∀ i, MeasurableSet (S i))
    (hcover : ⋃ i, S i = Set.univ) {f : α → β}
    (hrestr : ∀ i : ι, Measurable (fun x : S i => f x)) :
    Measurable f := by
  intro t ht
  have himage : ∀ i : ι,
      MeasurableSet (Subtype.val '' {x : S i | f x ∈ t}) := by
    intro i
    have ht_sub : MeasurableSet {x : S i | f x ∈ t} :=
      ht.preimage (hrestr i)
    exact MeasurableSet.subtype_image (hS i) ht_sub
  have hpre : f ⁻¹' t = ⋃ i : ι, Subtype.val '' {x : S i | f x ∈ t} := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ ⋃ i : ι, S i := by
        rw [hcover]
        trivial
      rcases Set.mem_iUnion.mp hxcover with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, ⟨⟨x, hi⟩, hx, rfl⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, y, hy, hyx⟩
      simpa [hyx] using hy
  rw [hpre]
  exact MeasurableSet.iUnion himage

/-! ## Permutation Maps -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `defn:permutation-map`.

Informal statement: the permutation map sends `(x, π)` to `x ∘ π` when the
tuple and permutation have the same length, and to the empty tuple otherwise.

Lean strategy / thesis relation note: `FinitePermutations` is the Sigma type
`Σ n, Equiv.Perm (Fin n)`, so the length check is a dependent type cast in
the same-length branch.
-/
def permutationMap (x : Tuple X) (π : FinitePermutations) : Tuple X :=
  if h : x.length = π.1 then permute x (h.symm ▸ π.2) else Tuple.empty X

@[simp]
theorem permutationMap_same_length {n : ℕ} (x : Fin n → X)
    (π : FinitePermutation n) :
    permutationMap (Sigma.mk n x : Tuple X) (Sigma.mk n π) =
      permute (Sigma.mk n x : Tuple X) π := by
  simp [permutationMap]

@[simp]
theorem permutationMap_ne_length {m n : ℕ} (h : m ≠ n)
    (x : Fin m → X) (π : FinitePermutation n) :
    permutationMap (Sigma.mk m x : Tuple X) (Sigma.mk n π) =
      Tuple.empty X := by
  simp [permutationMap, h]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed-length step in `prop:permuting-continuous`.

Informal statement: inserting a fixed-length tuple into the global tuple
space is continuous for the tuple Hausdorff topology.
-/
theorem continuous_sigmaMk_tupleHausdorff {X : Type u} [EMetricSpace X]
    (n : ℕ) :
    @Continuous (Fin n → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun x => (Sigma.mk n x : Tuple X)) := by
  rw [tupleHausdorffMetricTopology_eq_sigma]
  exact @continuous_sigmaMk ℕ (fun n : ℕ => Fin n → X)
    (fun n => inferInstance) n

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed-length step in `prop:permuting-continuous`.

Informal statement: on a fixed-length layer, reindexing coordinates by a
finite permutation is continuous.
-/
theorem continuous_fixedLength_permute {X : Type u} [EMetricSpace X]
    {n : ℕ} (π : FinitePermutation n) :
    @Continuous (Fin n → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun x => permute (Sigma.mk n x : Tuple X) π) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  change Continuous (fun x : Fin n → X => permute (Sigma.mk n x : Tuple X) π)
  have hmk : Continuous (fun x : Fin n → X => (Sigma.mk n x : Tuple X)) := by
    change @Continuous (Fin n → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun x => (Sigma.mk n x : Tuple X))
    exact continuous_sigmaMk_tupleHausdorff n
  have hp : Continuous (fun x : Fin n → X => fun i : Fin n => x (π i)) := by
    exact continuous_pi (A := fun _ : Fin n => X) fun i =>
      continuous_apply (A := fun _ : Fin n => X) (π i)
  exact hmk.comp' hp

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed-permutation component of `prop:permuting-continuous`.

Informal statement: for a fixed finite permutation `π`, the map
`x ↦ x[π]` is continuous on tuple space.

Lean strategy / thesis relation note: this is the fixed-`π` branch used in the thesis proof of the
full two-variable continuity statement.
-/
theorem continuous_fixedPermutationMap {X : Type u} [EMetricSpace X]
    (π : FinitePermutations) :
    @Continuous (Tuple X) (Tuple X)
      (tupleHausdorffMetricTopology (X := X))
      (tupleHausdorffMetricTopology (X := X))
      (fun x => permutationMap x π) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  change Continuous (fun x : Tuple X => permutationMap x π)
  rw [continuous_tupleHausdorff_iff_fixedLength]
  intro k
  rcases π with ⟨n, π⟩
  by_cases hkn : k = n
  · subst n
    simpa only [permutationMap_same_length] using
      (continuous_fixedLength_permute π)
  · simpa only [permutationMap_ne_length hkn] using
      (continuous_const :
        Continuous fun _ : Fin k → X => (Tuple.empty X : Tuple X))

/-! ## Metric Structure on Finite Permutations -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: metric model for `\mathscr{P}` in
`prop:permuting-continuous`.

Informal statement: view a finite permutation as the tuple of its natural
index-values.

Lean strategy / thesis relation note: the thesis treats `\mathscr{P}` as a subset of
`\mathscr{T}(\mathbb{N})`. Lean's `FinitePermutations` is already a Sigma
type over lengths, so this embedding is the formal subset map.
-/
noncomputable def finitePermutationTuple (π : FinitePermutations) : Tuple ℕ :=
  Sigma.mk π.1 (fun i => (π.2 i).1)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: injectivity of the metric model for `\mathscr{P}`.

Informal statement: the tuple representation of finite permutations is
injective.
-/
theorem finitePermutationTuple_injective :
    Function.Injective finitePermutationTuple := by
  rintro ⟨m, π⟩ ⟨n, ρ⟩ h
  have hlen : m = n := by
    simpa [finitePermutationTuple] using congrArg Tuple.length h
  subst n
  have hfun : (fun i : Fin m => (π i).1) = (fun i : Fin m => (ρ i).1) := by
    injection h with hfun
  congr
  ext i
  exact congrFun hfun i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: metric model for `\mathscr{P}` in
`prop:permuting-continuous`.

Informal statement: the distance between two finite permutations is the tuple
Hausdorff distance between their tuple representations in
`\mathscr{T}(\mathbb{N})`.
-/
noncomputable def finitePermutationEDistance
    (π ρ : FinitePermutations) : ENNReal :=
  edist (finitePermutationTuple π) (finitePermutationTuple ρ)

/-- Thesis metric-space structure on `\mathscr{P}` induced from tuples over `ℕ`. -/
noncomputable instance instEDistFinitePermutations :
    EDist FinitePermutations where
  edist := finitePermutationEDistance

/-- Thesis pseudometric laws for the induced permutation distance. -/
noncomputable instance instPseudoEMetricSpaceFinitePermutations :
    PseudoEMetricSpace FinitePermutations where
  edist_self := by
    intro π
    change edist (finitePermutationTuple π) (finitePermutationTuple π) = 0
    simp
  edist_comm := by
    intro π ρ
    change edist (finitePermutationTuple π) (finitePermutationTuple ρ) =
      edist (finitePermutationTuple ρ) (finitePermutationTuple π)
    exact edist_comm _ _
  edist_triangle := by
    intro π ρ τ
    change edist (finitePermutationTuple π) (finitePermutationTuple τ) ≤
      edist (finitePermutationTuple π) (finitePermutationTuple ρ) +
        edist (finitePermutationTuple ρ) (finitePermutationTuple τ)
    exact edist_triangle _ _ _

/-- Thesis extended metric structure on `\mathscr{P}` induced from tuples over `ℕ`. -/
noncomputable instance instEMetricSpaceFinitePermutations :
    EMetricSpace FinitePermutations :=
  EMetricSpace.mk (by
    intro π ρ h
    apply finitePermutationTuple_injective
    change edist (finitePermutationTuple π) (finitePermutationTuple ρ) = 0 at h
    exact edist_eq_zero.mp h)

/-- The topology induced by the thesis extended metric on finite permutations. -/
@[reducible]
noncomputable def finitePermutationMetricTopology :
    TopologicalSpace FinitePermutations :=
  PseudoEMetricSpace.toUniformSpace.toTopologicalSpace

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: isolative step inside `prop:permuting-continuous`.

Informal statement: if two finite permutations are within Hausdorff distance
`< 1`, then they are equal.

Lean strategy / thesis relation note: this is the concrete version of the thesis statement that
`\mathscr{P}` is isolative under the tuple Hausdorff metric inherited from
`\mathscr{T}(\mathbb{N})`.
-/
theorem finitePermutation_eq_of_edist_lt_one
    {π ρ : FinitePermutations} (h : edist π ρ < (1 : ENNReal)) :
    π = ρ := by
  rcases π with ⟨m, π⟩
  rcases ρ with ⟨n, ρ⟩
  change edist (finitePermutationTuple (Sigma.mk m π))
      (finitePermutationTuple (Sigma.mk n ρ)) < (1 : ENNReal) at h
  have hlen : m = n := by
    simpa [finitePermutationTuple] using
      (length_eq_of_edist_lt_one
        (x := finitePermutationTuple (Sigma.mk m π))
        (y := finitePermutationTuple (Sigma.mk n ρ)) h)
  subst n
  congr
  ext i
  have hcoord : edist ((π i).1) ((ρ i).1) < (1 : ENNReal) := by
    simpa [finitePermutationTuple] using
      (coordinate_edist_lt_one_of_fixedLength_edist_lt_one
        (x := fun i : Fin m => (π i).1)
        (y := fun i : Fin m => (ρ i).1) h i)
  exact IndexAugmented.nat_eq_of_edist_lt_one hcoord

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: local constancy step inside `prop:permuting-continuous`.

Informal statement: singleton permutation sets are open in the induced
permutation metric topology.
-/
theorem isOpen_singleton_finitePermutation (π : FinitePermutations) :
    @IsOpen FinitePermutations finitePermutationMetricTopology {π} := by
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  rw [isOpen_iff_mem_nhds]
  intro ρ hρ
  simp only [Set.mem_singleton_iff] at hρ
  subst ρ
  rw [EMetric.mem_nhds_iff]
  refine ⟨1, zero_lt_one, ?_⟩
  intro σ hσ
  exact finitePermutation_eq_of_edist_lt_one hσ

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: product-topology convention in `prop:permuting-continuous`.

Informal statement: the product topology on tuple space and permutation
space, using their thesis metric topologies.
-/
@[reducible]
noncomputable def permutationProductTopology {X : Type u} [EMetricSpace X] :
    TopologicalSpace (Tuple X × FinitePermutations) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  exact inferInstance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `prop:permuting-continuous`.

Informal statement: the two-variable permutation map
`(x, π) ↦ x[π]` is continuous for the product topology on
`\mathscr{T}(X) × \mathscr{P}`.

Lean strategy / thesis relation note: the proof follows the thesis proof. Around any point
`(x₀, π₀)`, the permutation coordinate is locally constant because
`\mathscr{P}` is isolated at radius `1`; on that neighborhood the map agrees
with the already-proved fixed-permutation branch `x ↦ x[π₀]`.
-/
theorem continuous_permutationMap {X : Type u} [EMetricSpace X] :
    @Continuous (Tuple X × FinitePermutations) (Tuple X)
      (permutationProductTopology (X := X))
      (tupleHausdorffMetricTopology (X := X))
      (fun z => permutationMap z.1 z.2) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  change Continuous (fun z : Tuple X × FinitePermutations =>
    permutationMap z.1 z.2)
  rw [continuous_iff_continuousAt]
  intro z0
  have hfixed : @ContinuousAt (Tuple X) (Tuple X)
      (tupleHausdorffMetricTopology (X := X))
      (tupleHausdorffMetricTopology (X := X))
      (fun x : Tuple X => permutationMap x z0.2) z0.1 :=
    @Continuous.continuousAt (Tuple X) (Tuple X)
      (tupleHausdorffMetricTopology (X := X))
      (tupleHausdorffMetricTopology (X := X))
      (fun x : Tuple X => permutationMap x z0.2) z0.1
      (continuous_fixedPermutationMap (X := X) z0.2)
  have hbranch : ContinuousAt
      (fun z : Tuple X × FinitePermutations => permutationMap z.1 z0.2) z0 :=
    hfixed.comp continuousAt_fst
  have hsingleton : ({z0.2} : Set FinitePermutations) ∈ nhds z0.2 :=
    (isOpen_singleton_finitePermutation z0.2).mem_nhds rfl
  have hsnd : Filter.Tendsto Prod.snd (nhds z0) (nhds z0.2) :=
    continuousAt_snd
  have heq :
      (fun z : Tuple X × FinitePermutations => permutationMap z.1 z.2) =ᶠ[nhds z0]
        (fun z : Tuple X × FinitePermutations => permutationMap z.1 z0.2) := by
    filter_upwards [hsnd hsingleton] with z hz
    rw [Set.mem_singleton_iff.mp hz]
  exact hbranch.congr_of_eventuallyEq heq

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties"; used again in
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: measurable consequence of `prop:permuting-continuous`.

Informal statement: if a tuple-valued map and a finite-permutation-valued map
are Borel measurable, then applying the permutation to the tuple is Borel
measurable.

Lean strategy / thesis relation note: this is the formal composition step behind the thesis phrase
"done in a measurable way": the continuous two-variable map
`(x,\pi) \mapsto x[\pi]` is composed with the measurable graph
`a \mapsto (x(a),\pi(a))`.
-/
theorem measurable_permutationMap_comp
    {α X : Type u} [MeasurableSpace α] [EMetricSpace X]
    {f : α → Tuple X} {π : α → FinitePermutations}
    (hf :
      @Measurable α (Tuple X) inferInstance (tupleHausdorffBorel (X := X)) f)
    (hπ :
      @Measurable α FinitePermutations inferInstance
        (@borel FinitePermutations finitePermutationMetricTopology) π) :
    @Measurable α (Tuple X) inferInstance (tupleHausdorffBorel (X := X))
      (fun a => permutationMap (f a) (π a)) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  letI : OpensMeasurableSpace FinitePermutations := ⟨le_rfl⟩
  letI : BorelSpace FinitePermutations := ⟨rfl⟩
  have hpair : Measurable fun a => (f a, π a) := Measurable.prod hf hπ
  exact continuous_permutationMap.measurable.comp hpair

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `prop:permutations-countable`.

Informal statement: the set of all finite permutations is countable.

Lean strategy / thesis relation note: Lean proves this directly from
`FinitePermutations = Σ n, Equiv.Perm (Fin n)`: the index set is countable and
each finite permutation group is finite, hence countable.
-/
theorem finitePermutations_countable : Countable FinitePermutations := by
  infer_instance

/-! ## Sorting-Valid Sets -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: definition of `\mathscr{V}_\pi`.

Informal statement: `sortingValidSet π` consists of the tuples whose length
matches `π` and whose permutation by `π` is sorted.
-/
def sortingValidSet [Preorder X] (π : FinitePermutations) : Set (Tuple X) :=
  {x | x.length = π.1 ∧ IsSorted (permutationMap x π)}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: domain topology in `cor:local-continuity-sorting`.

Informal statement: `\mathscr{V}_\pi` carries the subspace topology inherited
from the tuple Hausdorff topology.
-/
@[reducible]
noncomputable def sortingValidTopology {X : Type u} [EMetricSpace X]
    [Preorder X] (π : FinitePermutations) :
    TopologicalSpace (sortingValidSet (X := X) π) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  exact inferInstance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: codomain topology in `cor:local-continuity-sorting`.

Informal statement: the sorted tuple space carries the subspace topology
inherited from the tuple Hausdorff topology.
-/
@[reducible]
noncomputable def sortedTupleTopology {X : Type u} [EMetricSpace X]
    [Preorder X] :
    TopologicalSpace (SortedTuple X) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  exact inferInstance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: map `\varsigma_\pi` in `cor:local-continuity-sorting`.

Informal statement: on the sorting-valid set `\mathscr{V}_\pi`, send a tuple
to its permuted sorted tuple.
-/
def sortingValidMap [Preorder X] (π : FinitePermutations)
    (x : sortingValidSet (X := X) π) : SortedTuple X :=
  ⟨permutationMap x.1 π, x.2.2⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `cor:local-continuity-sorting`.

Informal statement: for each finite permutation `π`, the map
`\varsigma_\pi : \mathscr{V}_\pi → \mathscr{S}(X,\preceq)`,
`x ↦ x[π]`, is continuous.

Lean strategy / thesis relation note: Lean expresses both domain and codomain as subtypes. The proof
is exactly the thesis reduction to `prop:permuting-continuous`, restricted to
the fixed permutation `π`.
-/
theorem continuous_sortingValidMap {X : Type u} [EMetricSpace X]
    [Preorder X] (π : FinitePermutations) :
    @Continuous (sortingValidSet (X := X) π) (SortedTuple X)
      (sortingValidTopology (X := X) π)
      (sortedTupleTopology (X := X))
      (sortingValidMap (X := X) π) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  change Continuous (fun x : sortingValidSet (X := X) π =>
    (⟨permutationMap x.1 π, x.2.2⟩ : SortedTuple X))
  have hbase :
      Continuous (fun x : sortingValidSet (X := X) π =>
        permutationMap x.1 π) := by
    exact (continuous_fixedPermutationMap (X := X) π).comp continuous_subtype_val
  exact hbase.subtype_mk (fun x => x.2.2)

/-! ## Non-Unique Sorting Permutations -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: example after the cover by `\mathscr{V}_\pi`.

Informal statement: the constant tuple of length `n`.
-/
abbrev constantTuple (n : ℕ) (x : X) : Tuple X :=
  Sigma.mk n (fun _ => x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: example after the cover by `\mathscr{V}_\pi`.

Informal statement: every constant tuple is sorted.
-/
theorem constantTuple_isSorted [Preorder X] (n : ℕ) (x : X) :
    IsSorted (constantTuple n x) := by
  intro i j hij
  simp [constantTuple]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: example after the cover by `\mathscr{V}_\pi`.

Informal statement: the transposition of the two entries of a length-two
constant tuple.

Lean strategy / thesis relation note: the proofs that `0` and `1` are in the
tuple domain are written with explicit `change ... < 2` terms because the tuple
length is carried through the dependent type `Fin (constantTuple 2 x).length`.
-/
def constantTwoSwap (x : X) : FinitePermutation (constantTuple 2 x).length :=
  Equiv.swap
    (⟨0, by change 0 < 2; decide⟩ : Fin (constantTuple 2 x).length)
    (⟨1, by change 1 < 2; decide⟩ : Fin (constantTuple 2 x).length)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: example after the cover by `\mathscr{V}_\pi`.

Informal statement: the identity permutation sorts a length-two constant
tuple.
-/
theorem constantTwo_identity_isSortingPermutation [Preorder X] (x : X) :
    IsSortingPermutation (constantTuple 2 x)
      (Equiv.refl (Fin (constantTuple 2 x).length)) := by
  simpa [IsSortingPermutation, permute_refl] using constantTuple_isSorted 2 x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: example after the cover by `\mathscr{V}_\pi`.

Informal statement: swapping the two entries also sorts a length-two constant
tuple.
-/
theorem constantTwo_swap_isSortingPermutation [Preorder X] (x : X) :
    IsSortingPermutation (constantTuple 2 x) (constantTwoSwap x) := by
  change IsSorted (permute (constantTuple 2 x) (constantTwoSwap x))
  intro i j hij
  simp [permute, constantTwoSwap, Tuple.entry]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: example after the cover by `\mathscr{V}_\pi`.

Informal statement: the identity and swap sorting permutations above are
distinct.
-/
theorem constantTwo_identity_ne_swap (x : X) :
    (Equiv.refl (Fin (constantTuple 2 x).length) :
      FinitePermutation (constantTuple 2 x).length) ≠ constantTwoSwap x := by
  intro h
  have h0 := congrFun (congrArg Equiv.toFun h)
    (⟨0, by change 0 < 2; decide⟩ : Fin (constantTuple 2 x).length)
  simp [constantTwoSwap] at h0

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: corollary following the definition of `\mathscr{V}_\pi`.

Informal statement: any sorting rule chooses, for each tuple, a finite
permutation whose sorting-valid set contains that tuple.

Lean strategy / thesis relation note: this theorem records the conditional form supplied by an
arbitrary `SortingRule`; the non-conditional wrappers below now use the
minimum sorting rule constructed in `TuplesSorting`.

Lean strategy / thesis strategy note: this is not itself `thm:sorting-exists`. The global
existence theorem is `TuplesSorting.sortingRule_exists`, and the concrete
minimum-rule witness is `TuplesSorting.minimumSortingRule`; the present lemma
is the downstream cover fact for sorting-valid sets `\mathscr{V}_π`.
-/
theorem exists_mem_sortingValidSet_of_sortingRule [Preorder X]
    (σ : TuplesSorting.SortingRule X) (x : Tuple X) :
    ∃ π : FinitePermutations, x ∈ sortingValidSet (X := X) π := by
  rcases σ.exists_sortingPermutation x with ⟨π, _hπ⟩
  refine ⟨Sigma.mk x.length π.1, ?_⟩
  exact ⟨rfl, by simpa [TuplesSorting.IsSortingPermutation, permutationMap] using π.2⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: corollary following `thm:sorting-exists`.

Informal statement: every tuple lies in at least one sorting-valid set
`\mathscr{V}_π`.

Lean strategy / thesis relation note: this is the non-conditional form obtained from the verified
minimum sorting rule. It is slightly more general than the thesis statement:
the construction only needs a preorder.

Lean strategy / thesis strategy note: the thesis theorem `thm:sorting-exists` is formalized in
`TuplesSorting.lean` as `sortingRule_exists`. This corollary records the
consequence needed in the measurable-sorting partition proof.
-/
theorem exists_mem_sortingValidSet [Preorder X] (x : Tuple X) :
    ∃ π : FinitePermutations, x ∈ sortingValidSet (X := X) π :=
  exists_mem_sortingValidSet_of_sortingRule
    (X := X)
    (_root_.Thesis.Foundations.MarketRepresentation.TuplesSorting.minimumSortingRule
      (X := X)) x

/-! ## Enumerating Valid Sorting Sets -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `lem:permutations-inherit-order`.

Informal statement: a bijection `φ : \mathscr{P} → ℕ` pulls the usual order
on `ℕ` back to an order on finite permutations.
-/
def permutationInheritedLE (φ : FinitePermutations ≃ ℕ)
    (π ρ : FinitePermutations) : Prop :=
  φ π ≤ φ ρ

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `lem:permutations-inherit-order`.

Informal statement: the pullback order along a bijection
`φ : \mathscr{P} → ℕ` is total.

Lean strategy / thesis relation note: rather than registering a global `LinearOrder` instance
depending on `φ`, Lean records the four order laws needed downstream.
-/
theorem permutationInheritedLE_total_order (φ : FinitePermutations ≃ ℕ) :
    (∀ π, permutationInheritedLE φ π π) ∧
      (∀ π ρ τ, permutationInheritedLE φ π ρ →
        permutationInheritedLE φ ρ τ → permutationInheritedLE φ π τ) ∧
      (∀ π ρ, permutationInheritedLE φ π ρ →
        permutationInheritedLE φ ρ π → π = ρ) ∧
      (∀ π ρ, permutationInheritedLE φ π ρ ∨
        permutationInheritedLE φ ρ π) := by
  constructor
  · intro π
    exact le_rfl
  constructor
  · intro π ρ τ hπρ hρτ
    exact le_trans hπρ hρτ
  constructor
  · intro π ρ hπρ hρπ
    exact φ.injective (le_antisymm hπρ hρπ)
  · intro π ρ
    exact le_total (φ π) (φ ρ)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ranked permutations `\pi_{(k)}` after
`lem:permutations-inherit-order`.

Informal statement: the `n`th ranked permutation is `φ⁻¹(n)`.

Lean strategy / thesis relation note: the thesis writes the ranking one-based. Lean's natural
numbers are zero-based, so this is the same construction indexed by `ℕ`
starting at `0`.
-/
def rankedPermutation (φ : FinitePermutations ≃ ℕ) (n : ℕ) :
    FinitePermutations :=
  φ.symm n

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: sets `\mathscr{U}_n`.

Informal statement: `sortingCell φ n` is the part of
`\mathscr{V}_{π_(n)}` not already covered by earlier valid-permutation sets.
-/
def sortingCell [Preorder X] (φ : FinitePermutations ≃ ℕ)
    (n : ℕ) : Set (Tuple X) :=
  {x | x ∈ sortingValidSet (X := X) (rankedPermutation φ n) ∧
    ∀ m < n, x ∉ sortingValidSet (X := X) (rankedPermutation φ m)}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: helper for the lemma that the `\mathscr{U}_n` cover tuple
space.

Informal statement: if a sorting rule exists, every tuple has at least one
valid ranked permutation.
-/
theorem exists_rank_mem_sortingValidSet_of_sortingRule [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (x : Tuple X) :
    ∃ n : ℕ, x ∈ sortingValidSet (X := X) (rankedPermutation φ n) := by
  rcases exists_mem_sortingValidSet_of_sortingRule (X := X) σ x with ⟨π, hπ⟩
  refine ⟨φ π, ?_⟩
  simpa [rankedPermutation] using hπ

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: lemma following `lem:permutations-inherit-order`.

Informal statement: if a sorting rule exists, the cells `\mathscr{U}_n`
cover tuple space.

Lean strategy / thesis relation note: the thesis says this follows directly from the cover by
`\mathscr{V}_π`. Lean makes explicit the hidden minimal-rank argument using
`Nat.find`.
-/
theorem sortingCell_cover_of_sortingRule [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ) :
    (⋃ n : ℕ, sortingCell (X := X) φ n) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro x
  let P : ℕ → Prop := fun n =>
    x ∈ sortingValidSet (X := X) (rankedPermutation φ n)
  have hex : ∃ n, P n :=
    exists_rank_mem_sortingValidSet_of_sortingRule (X := X) σ φ x
  let n₀ := Nat.find hex
  have hn₀ : P n₀ := Nat.find_spec hex
  have hmin : ∀ m < n₀, ¬ P m := fun m hm => Nat.find_min hex hm
  exact Set.mem_iUnion.2 ⟨n₀, ⟨hn₀, hmin⟩⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: lemma following `lem:permutations-inherit-order`.

Informal statement: the cells `\mathscr{U}_n` cover tuple space.

Lean strategy / thesis relation note: this is the thesis-level statement, with the sorting rule
chosen by the minimum sorting construction.
-/
theorem sortingCell_cover [Preorder X]
    (φ : FinitePermutations ≃ ℕ) :
    (⋃ n : ℕ, sortingCell (X := X) φ n) = Set.univ :=
  sortingCell_cover_of_sortingRule
    (X := X)
    (_root_.Thesis.Foundations.MarketRepresentation.TuplesSorting.minimumSortingRule
      (X := X)) φ

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: disjointness component of
`prop:measurable-partition-sorting`.

Informal statement: the cells `\mathscr{U}_n` are pairwise disjoint by
construction.
-/
theorem sortingCell_pairwiseDisjoint [Preorder X]
    (φ : FinitePermutations ≃ ℕ) :
    Pairwise fun m n : ℕ =>
      Disjoint (sortingCell (X := X) φ m) (sortingCell (X := X) φ n) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro x hxm hxn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact hxn.2 m hlt hxm.1
  · exact hxm.2 n hgt hxn.1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: same-length branch in the definition of `\mathscr{V}_\pi`.

Informal statement: if `π` has the same length as `x`, then `x[π]` is the
ordinary permuted tuple.
-/
@[simp]
theorem permutationMap_mk_length (x : Tuple X)
    (π : FinitePermutation x.length) :
    permutationMap x (Sigma.mk x.length π) = permute x π := by
  simp [permutationMap]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: cover statement following the definition of
`\mathscr{V}_\pi`.

Informal statement: if a sorting rule exists, then the sorting-valid sets
cover tuple space.
-/
theorem sortingValidSet_cover_of_sortingRule [Preorder X]
    (σ : TuplesSorting.SortingRule X) :
    (⋃ π : FinitePermutations, sortingValidSet (X := X) π) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  rcases exists_mem_sortingValidSet_of_sortingRule (X := X) σ x with ⟨π, hπ⟩
  exact Set.mem_iUnion.2 ⟨π, hπ⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: cover statement following the definition of
`\mathscr{V}_\pi`.

Informal statement: the sorting-valid sets cover tuple space.

Lean strategy / thesis relation note: this is the non-conditional form supplied by the minimum
sorting rule.
-/
theorem sortingValidSet_cover [Preorder X] :
    (⋃ π : FinitePermutations, sortingValidSet (X := X) π) = Set.univ :=
  sortingValidSet_cover_of_sortingRule
    (X := X)
    (_root_.Thesis.Foundations.MarketRepresentation.TuplesSorting.minimumSortingRule
      (X := X))

/-! ## Induced Sorting Rules -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: construction in `prop:induced-sorting`.

Informal statement: given an enumeration of finite permutations, the least
valid rank of a tuple is the first ranked permutation whose valid set contains
the tuple.

Lean strategy / thesis relation note: the thesis writes this using the first `\mathscr{U}_n`
containing the tuple. Lean implements the same minimum with `Nat.find`, using
an arbitrary existing sorting rule only to supply the nonempty witness.
-/
noncomputable def leastValidRank [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (x : Tuple X) : ℕ := by
  classical
  exact Nat.find (exists_rank_mem_sortingValidSet_of_sortingRule (X := X) σ φ x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: construction in `prop:induced-sorting`.

Informal statement: the least valid rank is genuinely valid for the tuple.
-/
theorem leastValidRank_spec [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (x : Tuple X) :
    x ∈ sortingValidSet (X := X) (rankedPermutation φ (leastValidRank σ φ x)) := by
  classical
  dsimp [leastValidRank]
  exact Nat.find_spec (exists_rank_mem_sortingValidSet_of_sortingRule (X := X) σ φ x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: minimality part of `prop:induced-sorting`.

Informal statement: no earlier ranked permutation is valid for the tuple.
-/
theorem leastValidRank_min [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (x : Tuple X) {m : ℕ} (hm : m < leastValidRank σ φ x) :
    x ∉ sortingValidSet (X := X) (rankedPermutation φ m) := by
  classical
  dsimp [leastValidRank] at hm
  exact Nat.find_min
    (exists_rank_mem_sortingValidSet_of_sortingRule (X := X) σ φ x) hm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: connection between the sets `\mathscr{U}_n` and
`prop:induced-sorting`.

Informal statement: membership in the cell `\mathscr{U}_n` identifies the
least valid rank as `n`.
-/
theorem leastValidRank_eq_of_mem_sortingCell [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    {x : Tuple X} {n : ℕ} (hx : x ∈ sortingCell (X := X) φ n) :
    leastValidRank σ φ x = n := by
  classical
  refine le_antisymm ?hle ?hge
  · exact not_lt.mp (by
      intro hn
      exact leastValidRank_min (X := X) σ φ x hn hx.1)
  · exact not_lt.mp (by
      intro hn
      exact hx.2 (leastValidRank σ φ x) hn
        (leastValidRank_spec (X := X) σ φ x))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: selected permutation in `prop:induced-sorting`.

Informal statement: the induced sorting rule chooses the least valid
permutation in the inherited order.
-/
noncomputable def inducedSortingPermutation [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (x : Tuple X) : FinitePermutations :=
  rankedPermutation φ (leastValidRank σ φ x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `prop:induced-sorting`.

Informal statement: choosing the least valid permutation and applying it to
each tuple gives a sorting map.

Lean strategy / thesis relation note: the thesis starts from the countable partition
`\{\mathscr{U}_n\}`. Lean packages the result as a `SortingRule`; the seed
sorting rule `σ` witnesses that every tuple has at least one valid
permutation, and the induced rule itself is the least-valid choice.
-/
noncomputable def inducedSortingRule [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ) :
    TuplesSorting.SortingRule X where
  sort x := permutationMap x (inducedSortingPermutation σ φ x)
  sorted_sort x := (leastValidRank_spec (X := X) σ φ x).2
  exists_perm x := by
    let piSigma := inducedSortingPermutation σ φ x
    have hvalid : x ∈ sortingValidSet (X := X) piSigma := by
      simpa [piSigma, inducedSortingPermutation] using
        leastValidRank_spec (X := X) σ φ x
    refine ⟨hvalid.1.symm ▸ piSigma.2, ?_⟩
    simp [piSigma, permutationMap, hvalid.1]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: cellwise description in `prop:induced-sorting`.

Informal statement: on `\mathscr{U}_n`, the induced sorting rule agrees with
the fixed permutation map for the `n`th ranked permutation.
-/
theorem inducedSortingRule_sort_eq_of_mem_sortingCell [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    {x : Tuple X} {n : ℕ} (hx : x ∈ sortingCell (X := X) φ n) :
    (inducedSortingRule (X := X) σ φ).sort x =
      permutationMap x (rankedPermutation φ n) := by
  simp [inducedSortingRule, inducedSortingPermutation,
    leastValidRank_eq_of_mem_sortingCell (X := X) σ φ hx]

/-! ## Measurable Sorting Partitions -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `thm:the-standard-machinery`, set-valued form used inside
`prop:measurable-partition-sorting`.

Informal statement: a subset of tuple space is Borel for the tuple Hausdorff
topology iff all of its fixed-length restrictions are Borel.

Lean strategy / thesis relation note: the thesis invokes this as the product-layer reduction
`\mathscr{T}(X)=\bigsqcup_n X^n`. Lean derives the set statement by applying
the existing function-valued bridge to the characteristic predicate
`x ↦ x ∈ s`.

Lean strategy / thesis strategy note: this lemma is only the set-level fixed-layer bridge used
inside measurable sorting. The full five-part `thm:the-standard-machinery`
is formalized in `TuplesMetricTopology.lean` through the identity
homeomorphism, continuity equivalences, and measurability equivalences.
-/
theorem measurableSet_tupleHausdorff_iff_fixedLength {X : Type u}
    [EMetricSpace X] {s : Set (Tuple X)} :
    @MeasurableSet (Tuple X) (tupleHausdorffBorel (X := X)) s ↔
      ∀ n : ℕ,
        @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
          {x | (Sigma.mk n x : Tuple X) ∈ s} := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  have hiff := measurable_tupleHausdorff_iff_fixedLength
    (X := X) (Y := Prop) (f := fun x : Tuple X => x ∈ s)
  constructor
  · intro hs n
    letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
    exact measurableSet_setOf.mpr (hiff.mp (measurableSet_setOf.mp hs) n)
  · intro hs
    exact measurableSet_setOf.mpr
      (hiff.mpr fun n => by
        letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
        exact measurableSet_setOf.mp (hs n))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed-product step in
`prop:measurable-partition-sorting`.

Informal statement: on a fixed product layer `X^n`, the set of tuples sorted
by a fixed permutation is Borel when the strict order relation is Borel.

Lean strategy / thesis relation note: this is exactly the thesis' finite-intersection argument. For
each pair `i ≤ j`, the forbidden set
`{x | x (π j) < x (π i)}` is the preimage of the Borel strict-order relation
under a continuous coordinate-pair map, and sortedness is the finite
intersection of its complements.
-/
theorem measurableSet_fixed_sortingValid_of_strictOrder {X : Type u}
    [EMetricSpace X] [Preorder X]
    (hstrict :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 < p.2})
    (n : ℕ) (π : FinitePermutation n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      {x | IsSorted (permutationMap (Sigma.mk n x : Tuple X) (Sigma.mk n π))} := by
  classical
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  letI : MeasurableSpace (X × X) := @borel (X × X) inferInstance
  letI : OpensMeasurableSpace (X × X) := ⟨le_rfl⟩
  letI : BorelSpace (X × X) := ⟨rfl⟩
  have hforbidden : ∀ i j : Fin n,
      @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
        {x | x (π j) < x (π i)} := by
    intro i j
    have hpair_cont :
        Continuous (fun x : Fin n → X => (x (π j), x (π i))) :=
      (continuous_apply (π j)).prodMk (continuous_apply (π i))
    exact hstrict.preimage hpair_cont.measurable
  have hallowed : ∀ i j : Fin n,
      @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
        {x | i ≤ j → ¬ x (π j) < x (π i)} := by
    intro i j
    by_cases hij : i ≤ j
    · have hnot :
          @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
            {x | ¬ x (π j) < x (π i)} := by
        simpa [Set.compl_setOf] using (hforbidden i j).compl
      simpa [hij] using hnot
    · have hset :
          {x : Fin n → X | i ≤ j → ¬ x (π j) < x (π i)} = Set.univ := by
        ext x
        simp [hij]
      rw [hset]
      exact MeasurableSet.univ
  have hfinite :
      @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
        (⋂ i : Fin n, ⋂ j : Fin n,
          {x | i ≤ j → ¬ x (π j) < x (π i)}) := by
    exact MeasurableSet.iInter fun i =>
      MeasurableSet.iInter fun j => hallowed i j
  convert hfinite using 1
  ext x
  change IsSorted (permutationMap (Sigma.mk n x : Tuple X) (Sigma.mk n π)) ↔
    x ∈ ⋂ i : Fin n, ⋂ j : Fin n,
      {x | i ≤ j → ¬ x (π j) < x (π i)}
  rw [permutationMap_same_length]
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  change (∀ i j : Fin n, i ≤ j → ¬ x (π j) < x (π i)) ↔
    ∀ i j : Fin n, i ≤ j → ¬ x (π j) < x (π i)
  exact Iff.rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: Borel-valid-set step in
`prop:measurable-partition-sorting`.

Informal statement: every sorting-valid set `\mathscr{V}_π` is Borel when
the strict order relation is Borel.

Lean strategy / thesis relation note: the thesis first fixes `N = \ell(π)` and proves measurability
inside `X^N`; Lean then pastes the fixed-length restrictions back into the
Sigma tuple space using `measurableSet_tupleHausdorff_iff_fixedLength`.
-/
theorem measurableSet_sortingValidSet_of_strictOrder {X : Type u}
    [EMetricSpace X] [Preorder X]
    (hstrict :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 < p.2}) :
    ∀ π : FinitePermutations,
      @MeasurableSet (Tuple X) (tupleHausdorffBorel (X := X))
        (sortingValidSet (X := X) π) := by
  intro π
  rw [measurableSet_tupleHausdorff_iff_fixedLength]
  intro n
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  rcases π with ⟨N, π⟩
  by_cases h : n = N
  · subst N
    simpa [sortingValidSet] using
      measurableSet_fixed_sortingValid_of_strictOrder (X := X) hstrict n π
  · have hempty :
        {x : Fin n → X |
          (Sigma.mk n x : Tuple X) ∈ sortingValidSet (X := X) (Sigma.mk N π)} =
          ∅ := by
      ext x
      simp [sortingValidSet, h]
    rw [hempty]
    exact @MeasurableSet.empty (Fin n → X) (@borel (Fin n → X) inferInstance)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: Borel strict-order step in
`thm:minimal-sorting-measurable`.

Informal statement: if the partial-order relation `≤` is Borel, then the
strict-order relation `<` is Borel.

Lean strategy / thesis relation note: the thesis writes `\prec = \preceq \setminus \Delta`. Lean's
strict order on a partial order is definitionally `a ≤ b ∧ ¬ b ≤ a`, so the
proof uses the Borel order relation and its pullback along the continuous
coordinate swap.
-/
theorem measurableSet_strictOrder_of_measurableSet_le {X : Type u}
    [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2}) :
    @MeasurableSet (X × X) (@borel (X × X) inferInstance)
      {p | p.1 < p.2} := by
  letI : MeasurableSpace (X × X) := @borel (X × X) inferInstance
  letI : OpensMeasurableSpace (X × X) := ⟨le_rfl⟩
  letI : BorelSpace (X × X) := ⟨rfl⟩
  have hswap :
      @Measurable (X × X) (X × X)
        (@borel (X × X) inferInstance)
        (@borel (X × X) inferInstance) Prod.swap :=
    continuous_swap.measurable
  have hrev :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p : X × X | p.2 ≤ p.1} := by
    simpa [Prod.swap] using hle.preimage hswap
  have hstrict_eq :
      ({p : X × X | p.1 < p.2} : Set (X × X)) =
        {p : X × X | p.1 ≤ p.2} ∩
          ({p : X × X | p.2 ≤ p.1})ᶜ := by
    ext p
    simp [lt_iff_le_not_ge]
  rw [hstrict_eq]
  exact hle.inter hrev.compl

/-! ## Fixed-Length Minimal-Sorting Cells -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: first fixed-length component of
`thm:minimal-sorting-measurable`.

Informal statement: on a fixed layer `X^n`, `C_{i,j}` is the set of tuples
for which indices `i` and `j` are immediately comparable.

Lean strategy / thesis relation note: the thesis writes indices as elements of `{1,\dots,n}`.
Lean uses `Fin n`; the set is otherwise the same
`x i ≤ x j ∨ x j ≤ x i`.
-/
def fixedIndexComparableSet [Preorder X] (n : ℕ)
    (i j : Fin n) : Set (Fin n → X) :=
  {x | IndexComparable (Sigma.mk n x : Tuple X) i j}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of the sets `C_{i,j}` in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: if the ambient order relation is Borel, then each
fixed-length immediate-comparability set `C_{i,j}` is Borel.

Lean strategy / thesis relation note: this is the thesis coordinate-pullback argument: coordinate
evaluation maps on `X^n` are continuous, and `C_{i,j}` is the union of the
order relation pulled back by `(x i, x j)` and by `(x j, x i)`.
-/
theorem measurableSet_fixedIndexComparableSet_of_borelOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    (n : ℕ) (i j : Fin n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedIndexComparableSet (X := X) n i j) := by
  letI : MeasurableSpace (X × X) := @borel (X × X) inferInstance
  letI : OpensMeasurableSpace (X × X) := ⟨le_rfl⟩
  letI : BorelSpace (X × X) := ⟨rfl⟩
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  have hpair_ij :
      Measurable (fun x : Fin n → X => (x i, x j)) :=
    ((continuous_apply i).prodMk (continuous_apply j)).measurable
  have hpair_ji :
      Measurable (fun x : Fin n → X => (x j, x i)) :=
    ((continuous_apply j).prodMk (continuous_apply i)).measurable
  have hij : MeasurableSet {x : Fin n → X | x i ≤ x j} := by
    simpa using hle.preimage hpair_ij
  have hji : MeasurableSet {x : Fin n → X | x j ≤ x i} := by
    simpa using hle.preimage hpair_ji
  have hset :
      fixedIndexComparableSet (X := X) n i j =
        {x : Fin n → X | x i ≤ x j} ∪
          {x : Fin n → X | x j ≤ x i} := by
    ext x
    simp [fixedIndexComparableSet, IndexComparable, Tuple.entry]
  rw [hset]
  exact hij.union hji

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: strict-order set `A_{i,j}` in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: on a fixed layer `X^n`, `A_{i,j}` is the set of tuples
for which coordinate `j` is strictly smaller than coordinate `i`.
-/
def fixedStrictLowerSet [LT X] (n : ℕ) (i j : Fin n) :
    Set (Fin n → X) :=
  {x | x j < x i}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of `A_{i,j}` in
`thm:minimal-sorting-measurable`.

Informal statement: if the partial order is Borel, then every fixed-length
strict-lower set `A_{i,j}` is Borel.

Lean strategy / thesis relation note: the thesis writes `≺ = \preceq \setminus Δ`. Lean uses the
previous theorem `measurableSet_strictOrder_of_measurableSet_le` and pulls it
back along the continuous coordinate map `(x j, x i)`.
-/
theorem measurableSet_fixedStrictLowerSet_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    (n : ℕ) (i j : Fin n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedStrictLowerSet (X := X) n i j) := by
  letI : MeasurableSpace (X × X) := @borel (X × X) inferInstance
  letI : OpensMeasurableSpace (X × X) := ⟨le_rfl⟩
  letI : BorelSpace (X × X) := ⟨rfl⟩
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  have hstrict :=
    measurableSet_strictOrder_of_measurableSet_le (X := X) hle
  have hpair :
      Measurable (fun x : Fin n → X => (x j, x i)) :=
    ((continuous_apply j).prodMk (continuous_apply i)).measurable
  simpa [fixedStrictLowerSet] using hstrict.preimage hpair

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite path expansion in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: a fixed finite path of indices is comparable along every
successive edge.

Lean strategy / thesis relation note: the thesis indexes paths as `(i_0,\dots,i_k)`. Lean represents
such a path by a function `Fin (k+1) → Fin n`; the edge from `r` to `r+1` is
expressed using `Fin.castSucc r` and `Fin.succ r`.
-/
def fixedPathComparable [Preorder X] {n : ℕ} (x : Fin n → X)
    {k : ℕ} (p : Fin (k + 1) → Fin n) : Prop :=
  ∀ r : Fin k,
    IndexComparable (Sigma.mk n x : Tuple X)
      (p (Fin.castSucc r)) (p (Fin.succ r))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite path expansion in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: the set of fixed-length tuples for which a specified
index path is comparable along each edge is Borel.

Lean strategy / thesis relation note: this is the finite-intersection step in the thesis proof.
-/
theorem measurableSet_fixedPathComparable_of_borelOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n k : ℕ} (p : Fin (k + 1) → Fin n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      {x | fixedPathComparable (X := X) x p} := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  have h :
      MeasurableSet
        (⋂ r : Fin k,
          fixedIndexComparableSet (X := X) n
            (p (Fin.castSucc r)) (p (Fin.succ r))) := by
    exact MeasurableSet.iInter fun r =>
      measurableSet_fixedIndexComparableSet_of_borelOrder
        (X := X) hle n (p (Fin.castSucc r)) (p (Fin.succ r))
  have hset :
      {x : Fin n → X | fixedPathComparable (X := X) x p} =
        ⋂ r : Fin k,
          fixedIndexComparableSet (X := X) n
            (p (Fin.castSucc r)) (p (Fin.succ r)) := by
    ext x
    simp [fixedPathComparable, fixedIndexComparableSet]
  rw [hset]
  exact h

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: path interpretation of connectivity in
`thm:minimal-sorting-measurable`.

Informal statement: a concrete comparable path induces membership in the
reflexive-transitive connectivity relation.

Lean strategy / thesis relation note: this is the forward direction of the thesis' path expansion of
the transitive closure.
-/
theorem fixedPathComparable_indexConnected [Preorder X]
    {n k : ℕ} (x : Fin n → X) (p : Fin (k + 1) → Fin n)
    (hpath : fixedPathComparable (X := X) x p) :
    IndexConnected (Sigma.mk n x : Tuple X) (p 0) (p (Fin.last k)) := by
  induction k with
  | zero =>
      simpa using
        indexConnected_refl (X := X) (Sigma.mk n x : Tuple X) (p 0)
  | succ k ih =>
      let q : Fin (k + 1) → Fin n := fun r => p (Fin.castSucc r)
      have hq : fixedPathComparable (X := X) x q := by
        intro r
        have hr := hpath (Fin.castSucc r)
        simpa [fixedPathComparable, q] using hr
      have hprev :
          IndexConnected (Sigma.mk n x : Tuple X) (q 0) (q (Fin.last k)) :=
        ih q hq
      have hlast :
          IndexComparable (Sigma.mk n x : Tuple X)
            (q (Fin.last k)) (p (Fin.last (k + 1))) := by
        have hr := hpath (Fin.last k)
        simpa [fixedPathComparable, q, Fin.succ_last] using hr
      have hconn :
          IndexConnected (Sigma.mk n x : Tuple X)
            (q 0) (p (Fin.last (k + 1))) :=
        Relation.ReflTransGen.tail hprev hlast
      simpa [q] using hconn

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: path interpretation of connectivity in
`thm:minimal-sorting-measurable`.

Informal statement: every connected pair of fixed-length indices is witnessed
by some finite comparable path.

Lean strategy / thesis relation note: mathlib's `Relation.ReflTransGen` is inductive, so the proof
constructs the thesis path by induction on the closure proof.
-/
theorem indexConnected_exists_fixedPathComparable [Preorder X]
    {n : ℕ} (x : Fin n → X) {i j : Fin n}
    (hconn : IndexConnected (Sigma.mk n x : Tuple X) i j) :
    ∃ k : ℕ, ∃ p : Fin (k + 1) → Fin n,
      p 0 = i ∧ p (Fin.last k) = j ∧
        fixedPathComparable (X := X) x p := by
  exact Relation.ReflTransGen.head_induction_on
    (motive := fun a _ =>
      ∃ k : ℕ, ∃ p : Fin (k + 1) → Fin n,
        p 0 = a ∧ p (Fin.last k) = j ∧
          fixedPathComparable (X := X) x p)
    hconn
    (by
      refine ⟨0, (fun _ => j), rfl, ?_, ?_⟩
      · simp
      · intro r
        exact Fin.elim0 r)
    (by
      intro a c hstep _htail ih
      rcases ih with ⟨k, p, hp0, hplast, hpath⟩
      refine ⟨k + 1, Fin.cons a p, ?_, ?_, ?_⟩
      · simp
      · simpa [Fin.succ_last] using hplast
      · intro r
        cases r using Fin.cases with
        | zero =>
            simpa [fixedPathComparable, hp0] using hstep
        | succ s =>
            have hs := hpath s
            simpa [fixedPathComparable] using hs)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `prop:transitive-closure-finite`.

Informal statement: for a fixed tuple of length `n`, connectivity of two
indices is witnessed by a comparable index path of length at most `n-1`.

Lean strategy / thesis relation note: the thesis states this for an arbitrary finite relation and
argues by deleting cycles from a long path. The downstream use is for the
symmetric immediate-comparability relation. Lean packages that cycle-deletion
argument in `SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty`;
we apply it to the simple graph generated by immediate comparability.
-/
noncomputable def indexComparableSimpleGraph [Preorder X] {n : ℕ}
    (x : Fin n → X) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet <|
    Sym2.fromRel
      (r := fun i j : Fin n => IndexComparable (Sigma.mk n x : Tuple X) i j)
      (fun _ _ h =>
        indexComparable_symm (X := X) (Sigma.mk n x : Tuple X) h)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `prop:transitive-closure-finite`.

Informal statement: reachability in the finite simple graph generated by
immediate comparability is exactly the tuple connectivity relation.
-/
theorem indexComparableSimpleGraph_reachable_iff_indexConnected [Preorder X]
    {n : ℕ} (x : Fin n → X) (i j : Fin n) :
    (indexComparableSimpleGraph (X := X) x).Reachable i j ↔
      IndexConnected (Sigma.mk n x : Tuple X) i j := by
  change (indexComparableSimpleGraph (X := X) x).Reachable i j ↔
    Relation.ReflTransGen (IndexComparable (Sigma.mk n x : Tuple X)) i j
  have hrel :=
    SimpleGraph.reachable_fromEdgeSet_fromRel_eq_reflTransGen
      (V := Fin n) (r := IndexComparable (Sigma.mk n x : Tuple X))
      (fun _ _ h =>
        indexComparable_symm (X := X) (Sigma.mk n x : Tuple X) h)
  simpa [indexComparableSimpleGraph] using congrFun (congrFun hrel i) j

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: `prop:transitive-closure-finite`.

Informal statement: if `i` and `j` are connected in a tuple of length `n`,
then some comparable path from `i` to `j` has edge count `k < n`.

Lean strategy / thesis relation note: `k : Fin n` is Lean's zero-based version of the thesis bound
`k ≤ n-1`. The path itself is still represented as
`Fin (k+1) → Fin n`, matching the thesis sequence
`(i_0,\dots,i_k)`.

Lean strategy / thesis strategy note: the manuscript states `prop:transitive-closure-finite` for
an arbitrary finite relation using powers `R^k`. Downstream, the proof only
uses this symmetric finite-index instance for tuple comparability, and this
is the form verified here.
-/
theorem indexConnected_exists_bounded_fixedPathComparable [Preorder X]
    {n : ℕ} (x : Fin n → X) {i j : Fin n}
    (hconn : IndexConnected (Sigma.mk n x : Tuple X) i j) :
    ∃ k : Fin n, ∃ p : Fin (k.1 + 1) → Fin n,
      p 0 = i ∧ p (Fin.last k.1) = j ∧
        fixedPathComparable (X := X) x p := by
  classical
  let G := indexComparableSimpleGraph (X := X) x
  have hreach : G.Reachable i j :=
    (indexComparableSimpleGraph_reachable_iff_indexConnected
      (X := X) x i j).2 hconn
  rcases (SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty
      G i j).1 hreach with
    ⟨k, hk_nonempty⟩
  rcases hk_nonempty with ⟨w, hw_mem⟩
  have hwlen : w.length = k.1 :=
    SimpleGraph.mem_finsetWalkLength_iff.mp hw_mem
  refine ⟨⟨k.1, by simpa using k.2⟩,
    (fun r : Fin (k.1 + 1) => w.getVert r.1), ?_, ?_, ?_⟩
  · simp
  · rw [← hwlen]
    exact w.getVert_length
  · intro r
    have hrlt : r.1 < w.length := by
      rw [hwlen]
      exact r.2
    have hadj : G.Adj (w.getVert r.1) (w.getVert (r.1 + 1)) :=
      w.adj_getVert_succ hrlt
    have hrel : IndexComparable (Sigma.mk n x : Tuple X)
        (w.getVert r.1) (w.getVert (r.1 + 1)) := by
      have hs : s(w.getVert r.1, w.getVert (r.1 + 1)) ∈
          Sym2.fromRel
            (r := fun i j : Fin n =>
              IndexComparable (Sigma.mk n x : Tuple X) i j)
            (fun _ _ h =>
              indexComparable_symm (X := X) (Sigma.mk n x : Tuple X) h) := by
        simpa [G, indexComparableSimpleGraph, SimpleGraph.fromEdgeSet_adj]
          using hadj.1
      exact (Sym2.fromRel_prop
        (sym := fun _ _ h =>
          indexComparable_symm (X := X) (Sigma.mk n x : Tuple X) h)).1 hs
    simpa [fixedPathComparable, Fin.val_castSucc, Fin.val_succ] using hrel

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: path sets in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: a fixed path witness starts at `i`, ends at `j`, and has
comparable adjacent entries.

Lean strategy / thesis relation note: endpoint constraints are independent of the tuple. Writing
them into the witness set lets the later union over all finite paths mirror
the thesis union over `\mathsf{path}(i,j)`.
-/
def fixedPathWitnessSet [Preorder X] (n : ℕ) (i j : Fin n)
    (k : ℕ) (p : Fin (k + 1) → Fin n) : Set (Fin n → X) :=
  if p 0 = i ∧ p (Fin.last k) = j then
    {x | fixedPathComparable (X := X) x p}
  else
    ∅

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of path components in
`thm:minimal-sorting-measurable`.

Informal statement: each fixed path-witness set is Borel.
-/
theorem measurableSet_fixedPathWitnessSet_of_borelOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    (n : ℕ) (i j : Fin n) (k : ℕ)
    (p : Fin (k + 1) → Fin n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedPathWitnessSet (X := X) n i j k p) := by
  by_cases hend : p 0 = i ∧ p (Fin.last k) = j
  · simpa [fixedPathWitnessSet, hend] using
      measurableSet_fixedPathComparable_of_borelOrder (X := X) hle p
  · simp [fixedPathWitnessSet, hend]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: connected-index set `\mathbf{C}_{i,j}` in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: fixed-length tuples for which `i` and `j` are connected
by a finite chain of immediately comparable indices.

Lean strategy / thesis relation note: the thesis reduces to paths of length at most `n-1`. Lean
records this directly by indexing the outer union by `k : Fin n`, so
`k.1 < n` is the bounded path length.
-/
def fixedIndexConnectedPathSet [Preorder X] (n : ℕ)
    (i j : Fin n) : Set (Fin n → X) :=
  ⋃ k : Fin n, ⋃ p : Fin (k.1 + 1) → Fin n,
    fixedPathWitnessSet (X := X) n i j k.1 p

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of `\mathbf{C}_{i,j}` in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: the path-expanded connected-index set is Borel.

Lean strategy / thesis relation note: this is now the same finite union used in the thesis proof:
there are only finitely many path lengths `k < n`, and for each such `k`
only finitely many maps `Fin (k+1) → Fin n`.
-/
theorem measurableSet_fixedIndexConnectedPathSet_of_borelOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    (n : ℕ) (i j : Fin n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedIndexConnectedPathSet (X := X) n i j) := by
  exact MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun p =>
      measurableSet_fixedPathWitnessSet_of_borelOrder
        (X := X) hle n i j k.1 p

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: path expansion of `\mathbf{C}_{i,j}` in
`thm:minimal-sorting-measurable`.

Informal statement: the path-expanded connected-index set is exactly the set
of tuples for which `i` and `j` are connected in Lean's existing
`IndexConnected` relation.
-/
theorem mem_fixedIndexConnectedPathSet_iff_indexConnected [Preorder X]
    {n : ℕ} (i j : Fin n) (x : Fin n → X) :
    x ∈ fixedIndexConnectedPathSet (X := X) n i j ↔
      IndexConnected (Sigma.mk n x : Tuple X) i j := by
  constructor
  · intro hx
    rw [fixedIndexConnectedPathSet] at hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨p, hp⟩
    rw [fixedPathWitnessSet] at hp
    by_cases hend : p 0 = i ∧ p (Fin.last k.1) = j
    · rw [if_pos hend] at hp
      rcases hend with ⟨hstart, hend'⟩
      have hconn :=
        fixedPathComparable_indexConnected (X := X) x p hp
      simpa [hstart, hend'] using hconn
    · rw [if_neg hend] at hp
      exact False.elim hp
  · intro hconn
    rcases indexConnected_exists_bounded_fixedPathComparable (X := X) x hconn with
      ⟨k, p, hstart, hend, hpath⟩
    rw [fixedIndexConnectedPathSet]
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨p, ?_⟩⟩
    rw [fixedPathWitnessSet]
    simp [hstart, hend, hpath]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of `\mathbf{C}_{i,j}` in
`thm:minimal-sorting-measurable`.

Informal statement: the actual connected-index set
`{x ∈ X^n | i ∼_x j}` is Borel.

Lean strategy / thesis relation note: this follows the thesis proof: use
`prop:transitive-closure-finite` to replace the reflexive-transitive closure
by a finite union over paths of length at most `n-1`.
-/
theorem measurableSet_fixedIndexConnected_of_borelOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    (n : ℕ) (i j : Fin n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      {x | IndexConnected (Sigma.mk n x : Tuple X) i j} := by
  have hset :
      {x : Fin n → X | IndexConnected (Sigma.mk n x : Tuple X) i j} =
        fixedIndexConnectedPathSet (X := X) n i j := by
    ext x
    exact (mem_fixedIndexConnectedPathSet_iff_indexConnected
      (X := X) i j x).symm
  rw [hset]
  exact measurableSet_fixedIndexConnectedPathSet_of_borelOrder
    (X := X) hle n i j

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: connectivity-partition cell `\mathscr{E}(P)` in
`thm:minimal-sorting-measurable`.

Informal statement: on `X^n`, a connectivity-pattern cell consists of the
tuples whose connected-index relation is exactly the prescribed relation
`R`.

Lean strategy / thesis relation note: the thesis parametrizes these cells by finite partitions
`P = {C_1,\dots,C_m}` and defines `same(P)` and `diff(P)`. Lean records the
same data as a binary relation `R`; when `R` is the same-block relation of a
partition, this is exactly `\mathscr{E}(P)`.
-/
def fixedConnectivityPatternCell [Preorder X] (n : ℕ)
    (R : Fin n → Fin n → Prop) : Set (Fin n → X) :=
  {x | ∀ i j : Fin n,
    IndexConnected (Sigma.mk n x : Tuple X) i j ↔ R i j}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of the cells `\mathscr{E}(P)` in
`thm:minimal-sorting-measurable`.

Informal statement: every fixed connectivity-pattern cell is Borel.

Lean strategy / thesis relation note: this is the thesis finite-intersection proof:
for each pair `(i,j)`, require either membership in `\mathbf{C}_{i,j}` or in
its complement, according to the prescribed same/different block relation.
-/
theorem measurableSet_fixedConnectivityPatternCell_of_borelOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    (n : ℕ) (R : Fin n → Fin n → Prop) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedConnectivityPatternCell (X := X) n R) := by
  classical
  let C : Fin n → Fin n → Set (Fin n → X) := fun i j =>
    {x | IndexConnected (Sigma.mk n x : Tuple X) i j}
  have hC : ∀ i j : Fin n,
      @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
        (C i j) := by
    intro i j
    exact measurableSet_fixedIndexConnected_of_borelOrder (X := X) hle n i j
  have hpieces :
      ∀ i j : Fin n,
        @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
          (if R i j then C i j else (C i j)ᶜ) := by
    intro i j
    by_cases hij : R i j
    · simpa [hij] using hC i j
    · simpa [hij] using (hC i j).compl
  have hset :
      fixedConnectivityPatternCell (X := X) n R =
        ⋂ i : Fin n, ⋂ j : Fin n,
          if R i j then C i j else (C i j)ᶜ := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter]
      intro i j
      by_cases hij : R i j
      · simpa [C, hij] using (hx i j).2 hij
      · have hnot : ¬ IndexConnected (Sigma.mk n x : Tuple X) i j := by
          intro hconn
          exact hij ((hx i j).1 hconn)
        simpa [C, hij] using hnot
    · intro hx i j
      have hxij := (Set.mem_iInter.mp (Set.mem_iInter.mp hx i) j)
      by_cases hij : R i j
      · simpa [C, hij] using hxij
      · constructor
        · intro hconn
          have hnot : ¬ IndexConnected (Sigma.mk n x : Tuple X) i j := by
            simpa [C, hij] using hxij
          exact False.elim (hnot hconn)
        · intro hR
          exact False.elim (hij hR)
  rw [hset]
  exact MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun j => hpieces i j

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: remaining block `C^{(r)}` in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: after the first `r` selected indices of a candidate
block enumeration `π`, the remaining set is
`C \ {π(0), ..., π(r-1)}`.

Lean strategy / thesis relation note: thesis indices run from `1` to `|C|`; Lean uses zero-based
`Fin m`, so the previous selected positions are those `s < r`.
-/
noncomputable def fixedBlockRemaining {n m : ℕ}
    (C : Finset (Fin n)) (π : Fin m → Fin n) (r : Fin m) :
    Finset (Fin n) := by
  classical
  exact C.filter fun i => ∀ s : Fin m, s < r → π s ≠ i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: zero-stage form of `C^{(r)}` in
`thm:minimal-sorting-measurable`.

Informal statement: before the first block-selection step, the remaining set
is the whole block.

Lean strategy / thesis relation note: the thesis uses one-based stages; Lean's first stage is
`r = 0`, so the set of previously selected positions is empty.
-/
@[simp]
theorem fixedBlockRemaining_zero {n m : ℕ}
    (C : Finset (Fin n)) (π : Fin m → Fin n) (hpos : 0 < m) :
    fixedBlockRemaining C π ⟨0, hpos⟩ = C := by
  ext i
  rw [fixedBlockRemaining, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hi
    refine ⟨hi, ?_⟩
    intro s hs
    have hsNat : s.1 < 0 := by
      exact hs
    exact False.elim ((Nat.not_lt_zero s.1) hsNat)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `M_{C,\pi,r}` in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: at stage `r`, `π r` is the least-index value-minimal
remaining element of the block `C`.

Lean strategy / thesis relation note: this is the thesis formula
`⋂_{j∈C^(r)} A_{π(r),j}^C ∩
 ⋂_{i∈C^(r), i<π(r)} ⋃_{j∈C^(r)} A_{i,j}`.
The predicate is written directly, and measurability below rewrites it into
those finite intersections/unions.
-/
def fixedBlockStepCell [LT X] {n m : ℕ}
    (C : Finset (Fin n)) (π : Fin m → Fin n) (r : Fin m) :
    Set (Fin n → X) :=
  {x |
    (∀ j : Fin n, j ∈ fixedBlockRemaining C π r →
      ¬ x j < x (π r)) ∧
    (∀ i : Fin n, i ∈ fixedBlockRemaining C π r → i < π r →
      ∃ j : Fin n, j ∈ fixedBlockRemaining C π r ∧ x j < x i)}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of `M_{C,\pi,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: each step cell saying that `π r` is the least-index
value-minimal remaining point is Borel.

Lean strategy / thesis relation note: this follows the thesis proof literally: the first half is a
finite intersection of complements of `A_{π(r),j}`, and the second half is a
finite intersection of finite unions of `A_{i,j}`.
-/
theorem measurableSet_fixedBlockStepCell_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n m : ℕ} (C : Finset (Fin n)) (π : Fin m → Fin n) (r : Fin m) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedBlockStepCell (X := X) C π r) := by
  classical
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  let R : Finset (Fin n) := fixedBlockRemaining C π r
  let first : Set (Fin n → X) :=
    {x | ∀ j : Fin n, j ∈ R → ¬ x j < x (π r)}
  let second : Set (Fin n → X) :=
    {x | ∀ i : Fin n, i ∈ R → i < π r →
      ∃ j : Fin n, j ∈ R ∧ x j < x i}
  have hstrict : ∀ i j : Fin n,
      @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
        (fixedStrictLowerSet (X := X) n i j) := by
    intro i j
    exact measurableSet_fixedStrictLowerSet_of_borelOrder
      (X := X) hle n i j
  have hfirst_set :
      first =
        ⋂ j : Fin n,
          if j ∈ R then
            (fixedStrictLowerSet (X := X) n (π r) j)ᶜ
          else
            Set.univ := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter]
      intro j
      by_cases hj : j ∈ R
      · simpa [fixedStrictLowerSet, hj] using hx j hj
      · simp [hj]
    · intro hx j hj
      have hxj := Set.mem_iInter.mp hx j
      simpa [fixedStrictLowerSet, hj] using hxj
  have hfirst : MeasurableSet first := by
    rw [hfirst_set]
    exact MeasurableSet.iInter fun j => by
      by_cases hj : j ∈ R
      · simpa [hj] using (hstrict (π r) j).compl
      · simp [hj]
  have hsecond_set :
      second =
        ⋂ i : Fin n,
          if i ∈ R ∧ i < π r then
            ⋃ j : Fin n,
              if j ∈ R then
                fixedStrictLowerSet (X := X) n i j
              else
                ∅
          else
            Set.univ := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter]
      intro i
      by_cases hi : i ∈ R ∧ i < π r
      · rw [if_pos hi]
        rcases hi with ⟨hiR, hir⟩
        rcases hx i hiR hir with ⟨j, hjR, hlt⟩
        refine Set.mem_iUnion.2 ⟨j, ?_⟩
        simpa [fixedStrictLowerSet, hjR] using hlt
      · simp [hi]
    · intro hx i hiR hir
      have hxi := Set.mem_iInter.mp hx i
      have hi : i ∈ R ∧ i < π r := ⟨hiR, hir⟩
      rw [if_pos hi] at hxi
      rcases Set.mem_iUnion.mp hxi with ⟨j, hxj⟩
      by_cases hjR : j ∈ R
      · exact ⟨j, hjR, by simpa [fixedStrictLowerSet, hjR] using hxj⟩
      · simp [hjR] at hxj
  have hsecond : MeasurableSet second := by
    rw [hsecond_set]
    exact MeasurableSet.iInter fun i => by
      by_cases hi : i ∈ R ∧ i < π r
      · rw [if_pos hi]
        exact MeasurableSet.iUnion fun j => by
          by_cases hj : j ∈ R
          · simpa [hj] using hstrict i j
          · simp [hj]
      · simp [hi]
  have hcell :
      fixedBlockStepCell (X := X) C π r = first ∩ second := by
    ext x
    simp [fixedBlockStepCell, first, second, R]
  rw [hcell]
  exact hfirst.inter hsecond

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `B_{C,\pi}` in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: the candidate enumeration `π` is the minimum sorting
enumeration of the block `C` exactly when all step cells `M_{C,\pi,r}` hold.
-/
def fixedBlockPermutationCell [LT X] {n m : ℕ}
    (C : Finset (Fin n)) (π : Fin m → Fin n) : Set (Fin n → X) :=
  ⋂ r : Fin m, fixedBlockStepCell (X := X) C π r

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of `B_{C,\pi}` in
`thm:minimal-sorting-measurable`.

Informal statement: the block-permutation cell is Borel.

Lean strategy / thesis relation note: this is the thesis line
`B_{C,\pi} = ⋂_r M_{C,\pi,r}`.
-/
theorem measurableSet_fixedBlockPermutationCell_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n m : ℕ} (C : Finset (Fin n)) (π : Fin m → Fin n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedBlockPermutationCell (X := X) C π) := by
  rw [fixedBlockPermutationCell]
  exact MeasurableSet.iInter fun r =>
    measurableSet_fixedBlockStepCell_of_borelOrder (X := X) hle C π r

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: data `(C_k,\pi_k)` in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: one block of a fixed partition together with a candidate
enumeration/permutation of that block.

Lean strategy / thesis relation note: the thesis writes `π_k ∈ Π(C_k)`, a bijection from
`{1,\dots,|C_k|}` onto `C_k`. This structure intentionally stores the finite
domain length, the block, and the candidate enumeration separately; later
lemmas can add the bijection and cardinality hypotheses when proving that the
cell is one of the genuine partition atoms.
-/
structure FixedBlockEnumeration (n : ℕ) where
  length : ℕ
  block : Finset (Fin n)
  enum : Fin length → Fin n

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: one `B_{C_k,\pi_k}` factor in
`\mathscr{E}(P,\pi_1,\dots,\pi_m)`.

Informal statement: the Borel cell where the stored enumeration is the
minimum block sorting enumeration.
-/
def fixedBlockEnumerationCell [LT X] {n : ℕ}
    (B : FixedBlockEnumeration n) : Set (Fin n → X) :=
  fixedBlockPermutationCell (X := X) B.block B.enum

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block-permutation cell
`B_{C,\pi}` in `thm:minimal-sorting-measurable`.

Informal statement: membership in `B_{C,\pi}` gives membership in every
stage cell `M_{C,\pi,r}`.
-/
theorem mem_fixedBlockPermutationCell_step [LT X]
    {n m : ℕ} {C : Finset (Fin n)} {π : Fin m → Fin n}
    {x : Fin n → X}
    (hx : x ∈ fixedBlockPermutationCell (X := X) C π)
    (r : Fin m) :
    x ∈ fixedBlockStepCell (X := X) C π r := by
  rw [fixedBlockPermutationCell] at hx
  exact Set.mem_iInter.mp hx r

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: first half of `M_{C,\pi,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: on a block-permutation cell, the stage-selected point is
value-minimal among the remaining indices.
-/
theorem fixedBlockEnumerationCell_no_strict_lower [LT X]
    {n : ℕ} {B : FixedBlockEnumeration n} {x : Fin n → X}
    (hx : x ∈ fixedBlockEnumerationCell (X := X) B)
    (r : Fin B.length) :
    ∀ j : Fin n, j ∈ fixedBlockRemaining B.block B.enum r →
      ¬ x j < x (B.enum r) := by
  exact
    (mem_fixedBlockPermutationCell_step
      (X := X) (C := B.block) (π := B.enum) hx r).1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: second half of `M_{C,\pi,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: on a block-permutation cell, any remaining lower-index
candidate is not value-minimal, so the selected point is the least-index
value-minimal remaining point.
-/
theorem fixedBlockEnumerationCell_least_index_witness [LT X]
    {n : ℕ} {B : FixedBlockEnumeration n} {x : Fin n → X}
    (hx : x ∈ fixedBlockEnumerationCell (X := X) B)
    (r : Fin B.length) :
    ∀ i : Fin n, i ∈ fixedBlockRemaining B.block B.enum r →
      i < B.enum r →
        ∃ j : Fin n, j ∈ fixedBlockRemaining B.block B.enum r ∧
          x j < x i := by
  exact
    (mem_fixedBlockPermutationCell_step
      (X := X) (C := B.block) (π := B.enum) hx r).2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block-intersection component of
`\mathscr{E}(P,\pi_1,\dots,\pi_m)`.

Informal statement: all candidate block enumerations are the minimum
enumerations on their respective blocks.

Lean strategy / thesis relation note: a finite list of block data replaces the thesis' indexed
family `k=1,\dots,m`.
-/
def fixedBlockEnumerationCells [LT X] {n : ℕ}
    (blocks : List (FixedBlockEnumeration n)) : Set (Fin n → X) :=
  match blocks with
  | [] => Set.univ
  | B :: Bs =>
      fixedBlockEnumerationCell (X := X) B ∩
        fixedBlockEnumerationCells Bs

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block-intersection component of
`\mathscr{E}(P,\pi_1,\dots,\pi_m)`.

Informal statement: membership in the finite block intersection is exactly
membership in every listed block-permutation cell.
-/
theorem mem_fixedBlockEnumerationCells_iff_forall [LT X]
    {n : ℕ} {blocks : List (FixedBlockEnumeration n)}
    {x : Fin n → X} :
    x ∈ fixedBlockEnumerationCells (X := X) blocks ↔
      ∀ B ∈ blocks, x ∈ fixedBlockEnumerationCell (X := X) B := by
  induction blocks with
  | nil =>
      simp [fixedBlockEnumerationCells]
  | cons B Bs ih =>
      constructor
      · intro hx C hC
        rw [fixedBlockEnumerationCells] at hx
        rcases hx with ⟨hB, hBs⟩
        rw [List.mem_cons] at hC
        rcases hC with rfl | hC
        · exact hB
        · exact ih.mp hBs C hC
      · intro hx
        rw [fixedBlockEnumerationCells]
        refine ⟨hx B (by simp), ?_⟩
        exact ih.mpr fun C hC => hx C (by simp [hC])

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of the block-intersection component of
`\mathscr{E}(P,\pi_1,\dots,\pi_m)`.

Informal statement: a finite intersection of block-permutation cells is
Borel.
-/
theorem measurableSet_fixedBlockEnumerationCells_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n : ℕ} (blocks : List (FixedBlockEnumeration n)) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedBlockEnumerationCells (X := X) blocks) := by
  induction blocks with
  | nil =>
      rw [fixedBlockEnumerationCells]
      exact MeasurableSet.univ
  | cons B Bs ih =>
      rw [fixedBlockEnumerationCells, fixedBlockEnumerationCell]
      exact (measurableSet_fixedBlockPermutationCell_of_borelOrder
        (X := X) hle B.block B.enum).inter ih

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: refined cell
`\mathscr{E}(P,\pi_1,\dots,\pi_m)` in
`thm:minimal-sorting-measurable`.

Informal statement: a fixed connectivity pattern holds, and within each
block the specified enumeration is the minimum sorting enumeration.

Lean strategy / thesis relation note: the connectivity pattern relation `R` represents the thesis
partition `P`; the list `blocks` represents the ordered block/enumeration
data `(C_k,\pi_k)`.
-/
def fixedMinimalSortingRefinedCell [Preorder X] {n : ℕ}
    (R : Fin n → Fin n → Prop)
    (blocks : List (FixedBlockEnumeration n)) : Set (Fin n → X) :=
  fixedConnectivityPatternCell (X := X) n R ∩
    fixedBlockEnumerationCells (X := X) blocks

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of
`\mathscr{E}(P,\pi_1,\dots,\pi_m)` in
`thm:minimal-sorting-measurable`.

Informal statement: each refined fixed-length minimum-sorting cell is Borel.

Lean strategy / thesis relation note: this is the thesis proof line
`\mathscr{E}(P,\pi_1,\dots,\pi_m)
= \mathscr{E}(P) ∩ ⋂_k B_{C_k,\pi_k}`.
-/
theorem measurableSet_fixedMinimalSortingRefinedCell_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n : ℕ} (R : Fin n → Fin n → Prop)
    (blocks : List (FixedBlockEnumeration n)) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (fixedMinimalSortingRefinedCell (X := X) R blocks) := by
  rw [fixedMinimalSortingRefinedCell]
  exact (measurableSet_fixedConnectivityPatternCell_of_borelOrder
    (X := X) hle n R).inter
      (measurableSet_fixedBlockEnumerationCells_of_borelOrder
        (X := X) hle blocks)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed map
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]` in
`thm:minimal-sorting-measurable`.

Informal statement: given a fixed finite list of source indices, read a
fixed-length tuple in that order.

Lean strategy / thesis relation note: before proving that the concatenated list is a genuine
permutation of all indices, Lean uses this slightly more general list-indexed
map. On genuine refined cells the list will be exactly the thesis'
concatenated permutation.
-/
def fixedIndexListMap {X : Type u} {n : ℕ}
    (idx : List (Fin n)) (x : Fin n → X) : Tuple X :=
  ⟨idx.length, fun i => x (idx.get i)⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: list/tuple compatibility for fixed permutation maps.

Informal statement: applying a fixed index list to a tuple is the same as
forming the tuple from the corresponding list of values.
-/
theorem fixedIndexListMap_eq_tupleOfList
    {X : Type u} {n : ℕ} (idx : List (Fin n)) (x : Fin n → X) :
    fixedIndexListMap (X := X) idx x =
      tupleOfList (X := X) (idx.map fun i => x i) := by
  have hLen : idx.length = (idx.map fun i => x i).length := by
    simp
  unfold fixedIndexListMap tupleOfList
  apply Sigma.ext
  · exact hLen
  · let f : Fin idx.length → X := fun i => x (idx.get i)
    let g : Fin (idx.map fun i => x i).length → X := fun i =>
      (idx.map fun i => x i).get i
    have hα : Fin idx.length = Fin (idx.map fun i => x i).length :=
      congrArg Fin hLen
    change f ≍ g
    refine Function.hfunext hα ?_
    intro a a' haa
    have hcast : cast hα a = a' := (cast_eq_iff_heq).mpr haa
    rw [← hcast]
    apply heq_of_eq
    change x (idx.get a) =
      (idx.map fun i => x i).get (cast hα a)
    have hval : (cast hα a).1 = a.1 := fin_cast_congrArg_val hLen a
    simp [List.get_eq_getElem, hval]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: graph-list reading of the fixed map
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]`.

Informal statement: read a fixed tuple through a fixed source-index list and
remember each source index as an index-augmented graph point.
-/
def fixedIndexGraphList {X : Type u} {n : ℕ}
    (idx : List (Fin n)) (x : Fin n → X) :
    List (IndexAugmented X) :=
  idx.map fun i => IndexAugmented.mk i.1 (x i)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: value projection of the fixed map in
`thm:minimal-sorting-measurable`.

Informal statement: projecting the fixed graph list to values gives the
ordinary value list read by the fixed index list.
-/
@[simp]
theorem fixedIndexGraphList_map_value {X : Type u} {n : ℕ}
    (idx : List (Fin n)) (x : Fin n → X) :
    (fixedIndexGraphList (X := X) idx x).map IndexAugmented.value =
      idx.map fun i => x i := by
  simp [fixedIndexGraphList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: continuity of the fixed map
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]` in
`thm:minimal-sorting-measurable`, by `prop:permuting-continuous`.

Informal statement: any fixed finite index-list reindexing is continuous from
`X^n` into tuple space.

Lean strategy / thesis relation note: this proves the same continuity ingredient as the thesis'
fixed-permutation map, but for the list representation used before the
permutation-cover proof is attached.
-/
theorem continuous_fixedIndexListMap {X : Type u} [EMetricSpace X]
    {n : ℕ} (idx : List (Fin n)) :
    @Continuous (Fin n → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun x => fixedIndexListMap (X := X) idx x) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  change Continuous
    (fun x : Fin n → X =>
      (Sigma.mk idx.length (fun i : Fin idx.length => x (idx.get i)) :
        Tuple X))
  have hmk :
      Continuous
        (fun y : Fin idx.length → X =>
          (Sigma.mk idx.length y : Tuple X)) := by
    change @Continuous (Fin idx.length → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun y => (Sigma.mk idx.length y : Tuple X))
    exact continuous_sigmaMk_tupleHausdorff idx.length
  have hcoords :
      Continuous (fun x : Fin n → X =>
        fun i : Fin idx.length => x (idx.get i)) := by
    exact continuous_pi (A := fun _ : Fin idx.length => X) fun i =>
      continuous_apply (A := fun _ : Fin n => X) (idx.get i)
  exact hmk.comp' hcoords

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: one block enumeration `\pi_k` in
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: turn one stored block enumeration into its list of source
indices.
-/
def FixedBlockEnumeration.indexList {n : ℕ}
    (B : FixedBlockEnumeration n) : List (Fin n) :=
  (List.finRange B.length).map B.enum

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: hypothesis `\pi_k \in \Pi(C_k)` in
`thm:minimal-sorting-measurable`.

Informal statement: the stored enumeration hits exactly the indices in its
block.

Lean strategy / thesis relation note: this is the surjectivity/onto-block half of the thesis'
statement that `\pi_k` is a bijection from `{1,\dots,|C_k|}` onto `C_k`.
-/
def FixedBlockEnumeration.CoversBlock {n : ℕ}
    (B : FixedBlockEnumeration n) : Prop :=
  ∀ i : Fin n, i ∈ B.block ↔ ∃ r : Fin B.length, B.enum r = i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: hypothesis `\pi_k \in \Pi(C_k)` in
`thm:minimal-sorting-measurable`.

Informal statement: the stored enumeration has no repeated indices.
-/
def FixedBlockEnumeration.InjectiveEnumeration {n : ℕ}
    (B : FixedBlockEnumeration n) : Prop :=
  Function.Injective B.enum

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `\pi_k \in \Pi(C_k)` in
`thm:minimal-sorting-measurable`.

Informal statement: if the stored enumeration covers its block, every
enumerated index belongs to the block.
-/
theorem FixedBlockEnumeration.enum_mem_block_of_coversBlock
    {n : ℕ} {B : FixedBlockEnumeration n}
    (hB : B.CoversBlock) (r : Fin B.length) :
    B.enum r ∈ B.block := by
  exact (hB (B.enum r)).mpr ⟨r, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: remaining block `C^{(r)}` in
`thm:minimal-sorting-measurable`.

Informal statement: for a genuine block enumeration, the current selected
index `π(r)` is still in the remaining set `C^{(r)}`.

Lean strategy / thesis relation note: this is the zero-based Lean form of the thesis fact that a
bijection `π : {1,\dots,|C|} → C` has not selected `π(r)` before stage `r`.
-/
theorem FixedBlockEnumeration.enum_mem_remaining_of_coversBlock_injective
    {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    (r : Fin B.length) :
    B.enum r ∈ fixedBlockRemaining B.block B.enum r := by
  classical
  rw [fixedBlockRemaining, Finset.mem_filter]
  refine ⟨FixedBlockEnumeration.enum_mem_block_of_coversBlock
    (B := B) hcov r, ?_⟩
  intro s hsr hEq
  have hs_eq : s = r := hinj hEq
  subst s
  exact (lt_irrefl r) hsr

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: remaining block `C^{(r)}` in
`thm:minimal-sorting-measurable`.

Informal statement: under a bijective block enumeration, the remaining set at
stage `r` is exactly the tail of the enumeration from `r` onward.

Lean strategy / thesis relation note: this makes explicit the finite-domain bookkeeping that the
thesis writes as `C^{(r)} = C \setminus \{\pi(1),\dots,\pi(r-1)\}`.
-/
theorem FixedBlockEnumeration.mem_remaining_iff_exists_enum_ge
    {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    (r : Fin B.length) (i : Fin n) :
    i ∈ fixedBlockRemaining B.block B.enum r ↔
      ∃ s : Fin B.length, r ≤ s ∧ B.enum s = i := by
  classical
  constructor
  · intro hi
    rw [fixedBlockRemaining, Finset.mem_filter] at hi
    rcases (hcov i).mp hi.1 with ⟨s, hs⟩
    refine ⟨s, ?_, hs⟩
    exact le_of_not_gt fun hsr => hi.2 s hsr hs
  · rintro ⟨s, hrs, hs⟩
    rw [fixedBlockRemaining, Finset.mem_filter]
    refine ⟨(hcov i).mpr ⟨s, hs⟩, ?_⟩
    intro t htr ht
    have hts : t = s := hinj (ht.trans hs.symm)
    subst t
    exact (not_lt_of_ge hrs) htr

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-domain bookkeeping for
`\pi_k \in \Pi(C_k)`.

Informal statement: the list representation of a block enumeration has the
stored block length.
-/
@[simp]
theorem FixedBlockEnumeration.length_indexList {n : ℕ}
    (B : FixedBlockEnumeration n) :
    B.indexList.length = B.length := by
  simp [FixedBlockEnumeration.indexList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-domain bookkeeping for
`\pi_k \in \Pi(C_k)`.

Informal statement: if the enumeration covers its block, then its index list
has exactly the block members.
-/
theorem FixedBlockEnumeration.mem_indexList_iff_of_coversBlock
    {n : ℕ} {B : FixedBlockEnumeration n}
    (hB : B.CoversBlock) (i : Fin n) :
    i ∈ B.indexList ↔ i ∈ B.block := by
  constructor
  · intro hi
    rw [FixedBlockEnumeration.indexList, List.mem_map] at hi
    rcases hi with ⟨r, _hr, hri⟩
    exact (hB i).mpr ⟨r, hri⟩
  · intro hi
    rcases (hB i).mp hi with ⟨r, hri⟩
    rw [FixedBlockEnumeration.indexList, List.mem_map]
    exact ⟨r, by simp, hri⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-domain bookkeeping for
`\pi_k \in \Pi(C_k)`.

Informal statement: an injective stored enumeration gives a duplicate-free
index list.
-/
theorem FixedBlockEnumeration.nodup_indexList_of_injective
    {n : ℕ} {B : FixedBlockEnumeration n}
    (hB : B.InjectiveEnumeration) :
    B.indexList.Nodup := by
  simpa [FixedBlockEnumeration.indexList,
    FixedBlockEnumeration.InjectiveEnumeration] using
      (List.nodup_finRange B.length).map hB

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `\pi_k \in \Pi(C_k)` cardinality bookkeeping in
`thm:minimal-sorting-measurable`.

Informal statement: a block enumeration that covers its block injectively
has domain length exactly equal to the block cardinality.

Lean strategy / thesis relation note: the thesis writes the domain of `π_k` as
`{1,\dots,|C_k|}`. Lean stores the domain length separately, so this theorem
recovers the thesis cardinality constraint from cover and injectivity.
-/
theorem FixedBlockEnumeration.length_eq_card_block_of_coversBlock_injective
    {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration) :
    B.length = B.block.card := by
  have hnodup : B.indexList.Nodup :=
    FixedBlockEnumeration.nodup_indexList_of_injective (B := B) hinj
  have htoFinset : B.indexList.toFinset = B.block := by
    ext i
    simpa using
      FixedBlockEnumeration.mem_indexList_iff_of_coversBlock
        (B := B) hcov i
  calc
    B.length = B.indexList.length := by
      rw [FixedBlockEnumeration.length_indexList]
    _ = B.indexList.toFinset.card := by
      exact (List.toFinset_card_of_nodup hnodup).symm
    _ = B.block.card := by
      rw [htoFinset]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finiteness of the block-permutation choices in
`thm:minimal-sorting-measurable`.

Informal statement: a genuine block enumeration in a fixed `n`-tuple has
length at most `n`.
-/
theorem FixedBlockEnumeration.length_le_of_coversBlock_injective
    {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration) :
    B.length ≤ n := by
  calc
    B.length = B.block.card :=
      FixedBlockEnumeration.length_eq_card_block_of_coversBlock_injective
        (B := B) hcov hinj
    _ ≤ n := by
      simpa using (Finset.card_le_univ B.block)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: nonempty block domains for
`\pi_k \in \Pi(C_k)` in `thm:minimal-sorting-measurable`.

Informal statement: if a genuine block is nonempty, then its stored
enumeration list has positive length.

Lean strategy / thesis relation note: in the thesis this is implicit because `π_k` has domain
`{1,\dots,|C_k|}`. Lean stores the length separately, so we recover the
positive-length fact from cover.
-/
theorem FixedBlockEnumeration.length_indexList_pos_of_block_nonempty
    {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hne : B.block.Nonempty) :
    0 < B.indexList.length := by
  rcases hne with ⟨i, hiB⟩
  have hiList : i ∈ B.indexList :=
    (FixedBlockEnumeration.mem_indexList_iff_of_coversBlock
      (B := B) hcov i).mpr hiB
  rcases List.mem_iff_get.mp hiList with ⟨r, _hr⟩
  exact lt_of_le_of_lt (Nat.zero_le r.1) r.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: concatenated permutation
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: concatenate the fixed enumerations of the blocks, in the
chosen block order.

Lean strategy / thesis relation note: the thesis assumes each `\pi_k` is a bijection from its block
domain onto `C_k` and the blocks partition `{1,\dots,n}`. Those hypotheses
will later upgrade this list to a `FinitePermutation n`.
-/
def fixedBlockEnumerationsIndexList {n : ℕ}
    (blocks : List (FixedBlockEnumeration n)) : List (Fin n) :=
  (blocks.map FixedBlockEnumeration.indexList).flatten

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finiteness of possible partition lengths in
`thm:minimal-sorting-measurable`.

Informal statement: if every block enumeration contributes at least one
index, then the number of listed blocks is at most the length of the
concatenated block-enumeration list.

Lean strategy / thesis relation note: this is the finite-list form of the thesis observation that a
partition of `{1,\dots,n}` into nonempty blocks has at most `n` blocks.
-/
theorem blocks_length_le_fixedBlockEnumerationsIndexList_length_of_nonempty
    {n : ℕ} {blocks : List (FixedBlockEnumeration n)}
    (hpos : ∀ B ∈ blocks, 0 < B.indexList.length) :
    blocks.length ≤ (fixedBlockEnumerationsIndexList blocks).length := by
  induction blocks with
  | nil =>
      simp [fixedBlockEnumerationsIndexList]
  | cons B Bs ih =>
      have hB : 0 < B.indexList.length := hpos B (by simp)
      have hBs : ∀ C ∈ Bs, 0 < C.indexList.length := by
        intro C hC
        exact hpos C (by simp [hC])
      have ihBs : Bs.length ≤
          (fixedBlockEnumerationsIndexList Bs).length := ih hBs
      have hOne : 1 ≤ B.indexList.length := Nat.succ_le_of_lt hB
      have hsum :
          1 + Bs.length ≤
            B.indexList.length +
              (fixedBlockEnumerationsIndexList Bs).length :=
        Nat.add_le_add hOne ihBs
      simpa [fixedBlockEnumerationsIndexList, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hsum

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: distinct nonempty partition blocks in
`thm:minimal-sorting-measurable`.

Informal statement: a list of pairwise-disjoint nonempty block enumerations
has no repeated block sets.

Lean strategy / thesis relation note: this is implicit in the thesis' use of a partition
`P=\{C_1,\dots,C_m\}`. In Lean it is stated for the block-list
representation that drives the fixed branch cells.
-/
theorem nodup_blockList_of_pairwiseDisjoint_noEmpty
    {n : ℕ} {blocks : List (FixedBlockEnumeration n)}
    (hdisj :
      List.Pairwise
        (fun B C : FixedBlockEnumeration n =>
          Disjoint (B.block : Set (Fin n)) (C.block : Set (Fin n)))
        blocks)
    (hne : ∀ B ∈ blocks, B.block.Nonempty) :
    (blocks.map fun B => B.block).Nodup := by
  classical
  induction blocks with
  | nil =>
      simp
  | cons B Bs ih =>
      cases hdisj with
      | cons hrel hpw =>
          rw [List.map_cons, List.nodup_cons]
          constructor
          · intro hmem
            rcases List.mem_map.mp hmem with ⟨C, hC, hCB⟩
            have hBC : Disjoint
                (B.block : Set (Fin n)) (C.block : Set (Fin n)) :=
              hrel C hC
            rcases hne B (by simp) with ⟨i, hiB⟩
            have hiBset : i ∈ (B.block : Set (Fin n)) := by
              simpa using hiB
            have hiCset : i ∈ (C.block : Set (Fin n)) := by
              simpa [hCB.symm] using hiBset
            rw [Set.disjoint_left] at hBC
            exact hBC hiBset hiCset
          · exact ih hpw (by
              intro C hC
              exact hne C (by simp [hC]))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block-cover bookkeeping for
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: if every block enumeration covers its block, then the
concatenated index list contains exactly the indices lying in one of the
listed blocks.
-/
theorem mem_fixedBlockEnumerationsIndexList_iff_of_coversBlock
    {n : ℕ} {blocks : List (FixedBlockEnumeration n)}
    (hblocks : ∀ B ∈ blocks, B.CoversBlock) (i : Fin n) :
    i ∈ fixedBlockEnumerationsIndexList blocks ↔
      ∃ B ∈ blocks, i ∈ B.block := by
  constructor
  · intro hi
    rw [fixedBlockEnumerationsIndexList, List.mem_flatten] at hi
    rcases hi with ⟨l, hl, hil⟩
    rw [List.mem_map] at hl
    rcases hl with ⟨B, hBmem, hBlist⟩
    subst l
    exact ⟨B, hBmem,
      (FixedBlockEnumeration.mem_indexList_iff_of_coversBlock
        (hblocks B hBmem) i).mp hil⟩
  · intro hi
    rcases hi with ⟨B, hBmem, hiB⟩
    rw [fixedBlockEnumerationsIndexList, List.mem_flatten]
    exact ⟨B.indexList,
      by
        rw [List.mem_map]
        exact ⟨B, hBmem, rfl⟩,
      (FixedBlockEnumeration.mem_indexList_iff_of_coversBlock
        (hblocks B hBmem) i).mpr hiB⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block-partition bookkeeping for
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: if the block enumerations are internally injective and
their blocks are pairwise disjoint, then the concatenated index list has no
duplicates.

Lean strategy / thesis relation note: this is one half of upgrading Lean's list representation of
`\pi_1 \oplus \dots \oplus \pi_m` into the thesis' genuine finite
permutation.
-/
theorem nodup_fixedBlockEnumerationsIndexList_of_pairwiseDisjoint
    {n : ℕ} {blocks : List (FixedBlockEnumeration n)}
    (hcov : ∀ B ∈ blocks, B.CoversBlock)
    (hinj : ∀ B ∈ blocks, B.InjectiveEnumeration)
    (hdisjoint :
      List.Pairwise
        (fun B C : FixedBlockEnumeration n =>
          Disjoint (B.block : Set (Fin n)) (C.block : Set (Fin n)))
        blocks) :
    (fixedBlockEnumerationsIndexList blocks).Nodup := by
  induction blocks with
  | nil =>
      simp [fixedBlockEnumerationsIndexList]
  | cons B Bs ih =>
      rw [fixedBlockEnumerationsIndexList, List.map_cons, List.flatten_cons,
        List.nodup_append]
      have hpair_tail := (List.pairwise_cons.mp hdisjoint).2
      refine ⟨
        FixedBlockEnumeration.nodup_indexList_of_injective
          (B := B) (hinj B (by simp)),
        ?_,
        ?_⟩
      · apply ih
        · intro C hC
          exact hcov C (by simp [hC])
        · intro C hC
          exact hinj C (by simp [hC])
        · exact hpair_tail
      · intro i hi j hj hij
        have hiB : i ∈ B.block :=
          (FixedBlockEnumeration.mem_indexList_iff_of_coversBlock
            (hcov B (by simp)) i).mp hi
        have hj_blocks :
            ∃ C ∈ Bs, j ∈ C.block :=
          (mem_fixedBlockEnumerationsIndexList_iff_of_coversBlock
            (blocks := Bs)
            (fun C hC => hcov C (by simp [hC])) j).mp hj
        rcases hj_blocks with ⟨C, hCmem, hjC⟩
        have hBC :
            Disjoint (B.block : Set (Fin n)) (C.block : Set (Fin n)) :=
          (List.pairwise_cons.mp hdisjoint).1 C hCmem
        have hiC : i ∈ (C.block : Set (Fin n)) := by
          simpa [hij] using hjC
        exact (Set.disjoint_left.mp hBC) (by simpa using hiB) hiC

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-list helper for
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: a duplicate-free list of `Fin n` indices that contains
every index induces a finite permutation of `Fin n`.

Lean strategy / thesis relation note: this is the Fin-index analogue of
`finPermutationOfNatList` used in `TuplesSorting.lean` for the minimum sorter.
-/
noncomputable def finPermutationOfFinList {n : ℕ} (idx : List (Fin n))
    (hlen : idx.length = n)
    (hmem : ∀ i : Fin n, i ∈ idx)
    (hnodup : idx.Nodup) : FinitePermutation n :=
  Equiv.ofBijective
    (fun i : Fin n => idx.get (Fin.cast hlen.symm i))
    (by
      constructor
      · intro i j hij
        have hcast :
            Fin.cast hlen.symm i = Fin.cast hlen.symm j :=
          list_get_injective_of_nodup hnodup hij
        apply Fin.ext
        simpa using congrArg Fin.val hcast
      · intro y
        rcases List.mem_iff_get.mp (hmem y) with ⟨k, hk⟩
        refine ⟨Fin.cast hlen k, ?_⟩
        simpa using hk)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: branch data `(P,\pi_1,\dots,\pi_m)` in
`thm:minimal-sorting-measurable`.

Informal statement: a fixed connectivity pattern, together with an ordered
list of block enumerations that genuinely partitions `Fin n`.

Lean strategy / thesis relation note: the thesis quantifies over finite partitions `P` of
`{1,\dots,n}` and bijections `\pi_k \in \Pi(C_k)`. Lean stores this as a list
of block-enumeration records plus explicit cover, injectivity, disjointness,
and universe-cover hypotheses.
-/
structure FixedMinimalSortingBranch (n : ℕ) where
  relation : Fin n → Fin n → Prop
  blocks : List (FixedBlockEnumeration n)
  blockRelation :
    ∀ i j : Fin n,
      relation i j ↔ ∃ B ∈ blocks, i ∈ B.block ∧ j ∈ B.block
  coversBlock : ∀ B ∈ blocks, B.CoversBlock
  injectiveEnumeration : ∀ B ∈ blocks, B.InjectiveEnumeration
  pairwiseDisjointBlocks :
    List.Pairwise
      (fun B C : FixedBlockEnumeration n =>
        Disjoint (B.block : Set (Fin n)) (C.block : Set (Fin n)))
      blocks
  coversAllIndices : ∀ i : Fin n, ∃ B ∈ blocks, i ∈ B.block

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: nonempty partition blocks in
`thm:minimal-sorting-measurable`.

Informal statement: every listed block in a fixed branch is nonempty.

Lean strategy / thesis relation note: the thesis works with actual partition blocks
`C_1,\dots,C_m`, hence empty blocks are not part of the combinatorial data.
Lean's broader `FixedMinimalSortingBranch` stores enough data for local
cell arguments before this normalization predicate is attached.
-/
def FixedMinimalSortingBranch.NoEmptyBlocks {n : ℕ}
    (branch : FixedMinimalSortingBranch n) : Prop :=
  ∀ B ∈ branch.blocks, B.block.Nonempty

/-! ## Finite Branch Codes -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite choices for one `\pi_k \in \Pi(C_k)` in
`thm:minimal-sorting-measurable`.

Informal statement: a finite code for one block and one candidate block
enumeration. The enumeration length is stored as an element of
`{0,\dots,n}`, so the code type is finite for fixed `n`.

Lean strategy / thesis relation note: this is the explicit finite-combinatorial object behind the
thesis sentence that, for fixed `n`, there are finitely many block
permutation choices.
-/
structure FixedBlockCode (n : ℕ) where
  length : Fin (n + 1)
  block : Finset (Fin n)
  enum : Fin length.1 → Fin n
  deriving Fintype

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: converting finite block codes back to `(C_k,\pi_k)` data.

Informal statement: forget the bounded-code wrapper and recover the block
enumeration used by the refined cells.
-/
def FixedBlockCode.toEnumeration {n : ℕ}
    (code : FixedBlockCode n) : FixedBlockEnumeration n :=
  { length := code.length.1
    block := code.block
    enum := code.enum }

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: coding genuine `\pi_k \in \Pi(C_k)` data.

Informal statement: any block enumeration whose length is at most `n` has a
finite code.
-/
def FixedBlockCode.ofEnumeration {n : ℕ}
    (B : FixedBlockEnumeration n) (hlen : B.length ≤ n) :
    FixedBlockCode n :=
  { length := ⟨B.length, Nat.lt_succ_of_le hlen⟩
    block := B.block
    enum := B.enum }

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: coding genuine `\pi_k \in \Pi(C_k)` data.

Informal statement: encoding and then forgetting a bounded block
enumeration recovers the original enumeration.
-/
@[simp]
theorem FixedBlockCode.toEnumeration_ofEnumeration {n : ℕ}
    (B : FixedBlockEnumeration n) (hlen : B.length ≤ n) :
    (FixedBlockCode.ofEnumeration B hlen).toEnumeration = B := by
  rfl

/-- The cover predicate transported to finite block codes. -/
def FixedBlockCode.CoversBlock {n : ℕ} (code : FixedBlockCode n) : Prop :=
  code.toEnumeration.CoversBlock

/-- The injectivity predicate transported to finite block codes. -/
def FixedBlockCode.InjectiveEnumeration {n : ℕ}
    (code : FixedBlockCode n) : Prop :=
  code.toEnumeration.InjectiveEnumeration

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite branch skeletons `(P,\pi_1,\dots,\pi_m)`.

Informal statement: a finite raw code for an ordered list of block
enumeration codes. The number of blocks is stored in `{0,\dots,n}`, making
the raw branch-code type finite for fixed `n`.

Lean strategy / thesis relation note: validity of the code as a partition is deliberately separated
from this raw finite code. This mirrors the thesis proof: first enumerate the
finite possible data, then restrict to those satisfying the partition and
bijection hypotheses.
-/
structure FixedBranchRawCode (n : ℕ) where
  blockCount : Fin (n + 1)
  block : Fin blockCount.1 → FixedBlockCode n
  deriving Fintype

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: reading the finite code as a branch block list.

Informal statement: convert a raw branch code into the list
`(C_1,\pi_1),\dots,(C_m,\pi_m)` used in the refined cell.
-/
def FixedBranchRawCode.toBlocks {n : ℕ}
    (code : FixedBranchRawCode n) : List (FixedBlockEnumeration n) :=
  List.ofFn fun k : Fin code.blockCount.1 =>
    (code.block k).toEnumeration

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: the partition relation `P` induced by a finite branch code.

Informal statement: two indices are related when they lie in the same listed
block.
-/
def FixedBranchRawCode.relation {n : ℕ}
    (code : FixedBranchRawCode n) : Fin n → Fin n → Prop :=
  fun i j => ∃ B ∈ code.toBlocks, i ∈ B.block ∧ j ∈ B.block

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: validity hypotheses for
`(P,\pi_1,\dots,\pi_m)`.

Informal statement: a raw code is valid when its blocks cover `Fin n`, are
pairwise disjoint, and each stored enumeration is a bijection onto its block.
-/
structure FixedBranchRawCode.Valid {n : ℕ}
    (code : FixedBranchRawCode n) : Prop where
  coversBlock : ∀ B ∈ code.toBlocks, B.CoversBlock
  injectiveEnumeration : ∀ B ∈ code.toBlocks, B.InjectiveEnumeration
  pairwiseDisjointBlocks :
    List.Pairwise
      (fun B C : FixedBlockEnumeration n =>
        Disjoint (B.block : Set (Fin n)) (C.block : Set (Fin n)))
      code.toBlocks
  coversAllIndices : ∀ i : Fin n, ∃ B ∈ code.toBlocks, i ∈ B.block

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite valid branch codes.

Informal statement: a valid branch code is a raw finite branch code together
with the thesis partition and block-bijection hypotheses.
-/
abbrev FixedBranchCode (n : ℕ) :=
  { code : FixedBranchRawCode n // code.Valid }

noncomputable instance FixedBranchCode.instFintype (n : ℕ) :
    Fintype (FixedBranchCode n) := by
  classical
  infer_instance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: turning valid finite codes into refined branch data.

Informal statement: a valid finite code determines a genuine fixed branch.
-/
def FixedBranchRawCode.toBranch {n : ℕ}
    (code : FixedBranchRawCode n) (hvalid : code.Valid) :
    FixedMinimalSortingBranch n :=
  { relation := code.relation
    blocks := code.toBlocks
    blockRelation := by
      intro i j
      rfl
    coversBlock := hvalid.coversBlock
    injectiveEnumeration := hvalid.injectiveEnumeration
    pairwiseDisjointBlocks := hvalid.pairwiseDisjointBlocks
    coversAllIndices := hvalid.coversAllIndices }

/-- A valid finite branch code determines a genuine fixed branch. -/
def FixedBranchCode.toBranch {n : ℕ}
    (code : FixedBranchCode n) : FixedMinimalSortingBranch n :=
  code.1.toBranch code.2

/-- The branch produced from a raw code has exactly the code's block list. -/
@[simp]
theorem FixedBranchRawCode.toBranch_blocks {n : ℕ}
    (code : FixedBranchRawCode n) (hvalid : code.Valid) :
    (code.toBranch hvalid).blocks = code.toBlocks := by
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: branch cell
`\mathscr{E}(P,\pi_1,\dots,\pi_m)`.
-/
def FixedMinimalSortingBranch.cell [Preorder X] {n : ℕ}
    (branch : FixedMinimalSortingBranch n) : Set (Fin n → X) :=
  fixedMinimalSortingRefinedCell (X := X) branch.relation branch.blocks

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: branch map
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]`.
-/
def FixedMinimalSortingBranch.map {X : Type u} {n : ℕ}
    (branch : FixedMinimalSortingBranch n) (x : Fin n → X) : Tuple X :=
  fixedIndexListMap (X := X)
    (fixedBlockEnumerationsIndexList branch.blocks) x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ordered branch data in `thm:minimal-sorting-measurable`.

Informal statement: the listed branch blocks appear in the same order as the
connected segments of the tuple, namely the thesis' first-arrival order.

Lean strategy / thesis relation note: the thesis writes an ordered partition
`P = (C_1,\dots,C_m)` when pasting the fixed maps. Lean's branch record stores
a list of blocks, so this predicate records the missing order assertion for a
particular tuple `x`.
-/
def FixedMinimalSortingBranch.blocksMatchSegmentArrival [Preorder X] {n : ℕ}
    (branch : FixedMinimalSortingBranch n) (x : Fin n → X) : Prop :=
  ((segmentListByArrival (X := X) (Sigma.mk n x : Tuple X)).map fun K =>
      segmentIndices (Sigma.mk n x : Tuple X) K) =
    branch.blocks.map fun B => (B.block : Set (Fin n))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ordered refined cell in
`thm:minimal-sorting-measurable`.

Informal statement: a branch cell together with the thesis' first-arrival
ordering convention for its listed partition blocks.

Lean strategy / thesis relation note: the LaTeX proof orders the partition blocks before applying
the pasted fixed permutation `\pi_1 \oplus \dots \oplus \pi_m`. Lean keeps
that ordering as an explicit predicate, so the local fixed-map theorem has
exactly the needed hypothesis.
-/
def FixedMinimalSortingBranch.arrivalRefinedCell [Preorder X] {n : ℕ}
    (branch : FixedMinimalSortingBranch n) : Set (Fin n → X) :=
  branch.cell (X := X) ∩
    {x | branch.blocksMatchSegmentArrival (X := X) x}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: graph-list form of one branch block `\pi_k`.

Informal statement: the graph points read from one stored block enumeration.
-/
def FixedBlockEnumeration.graphList {X : Type u} {n : ℕ}
    (B : FixedBlockEnumeration n) (x : Fin n → X) :
    List (IndexAugmented X) :=
  fixedIndexGraphList (X := X) B.indexList x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite graph subset associated with a block `C_k` in
`thm:minimal-sorting-measurable`.

Informal statement: the block `C_k` determines the distinct finite graph
subset `{(i,x_i) : i ∈ C_k}`.

Lean strategy / thesis relation note: the thesis treats `C_k` as a finite
subset of the tuple domain. Lean packages the corresponding graph subset as a
`DistinctFiniteSubsets X`, matching the existing finite-set sorter interface.
-/
noncomputable def FixedBlockEnumeration.distinctFiniteSet
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) : DistinctFiniteSubsets X := by
  classical
  let point : {i : Fin n // i ∈ B.block} → IndexAugmented X := fun i =>
    IndexAugmented.mk i.1.1 (x i.1)
  let s : FiniteSets.FiniteSubsets (IndexAugmented X) :=
    ⟨Set.range point, Set.finite_range point⟩
  have hdistinct : HasDistinctIndices s := by
    intro k a b ha hb
    rcases ha with ⟨i, hi⟩
    rcases hb with ⟨j, hj⟩
    have hiidx : i.1.1 = k := by
      simpa [point] using congrArg IndexAugmented.index hi
    have hjidx : j.1.1 = k := by
      simpa [point] using congrArg IndexAugmented.index hj
    have hij : i.1 = j.1 := Fin.ext (hiidx.trans hjidx.symm)
    have hia : x i.1 = a := by
      simpa [point] using congrArg IndexAugmented.value hi
    have hjb : x j.1 = b := by
      simpa [point] using congrArg IndexAugmented.value hj
    calc
      a = x i.1 := hia.symm
      _ = x j.1 := by rw [hij]
      _ = b := hjb
  exact ⟨s, hdistinct⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: membership in the block graph subset `{(i,x_i): i∈C_k}`.

Informal statement: a point belongs to the block's distinct finite set exactly
when it is the graph point of an index in the block.
-/
theorem FixedBlockEnumeration.mem_distinctFiniteSet_iff
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) {p : IndexAugmented X} :
    p ∈ ((B.distinctFiniteSet (X := X) x).1 : Set (IndexAugmented X)) ↔
      ∃ i : Fin n, i ∈ B.block ∧ p = IndexAugmented.mk i.1 (x i) := by
  rw [FixedBlockEnumeration.distinctFiniteSet]
  constructor
  · intro hp
    change p ∈ Set.range
      (fun i : {i : Fin n // i ∈ B.block} =>
        IndexAugmented.mk i.1.1 (x i.1)) at hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i.1, i.2, hi.symm⟩
  · rintro ⟨i, hiB, rfl⟩
    change IndexAugmented.mk i.1 (x i) ∈ Set.range
      (fun i : {i : Fin n // i ∈ B.block} =>
        IndexAugmented.mk i.1.1 (x i.1))
    exact ⟨⟨i, hiB⟩, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: segment/block identification inside
`thm:minimal-sorting-measurable`.

Informal statement: if a connected segment has the same index set as a stored
block `C_k`, then its finite graph subset is exactly the stored block graph
subset `{(i,x_i): i ∈ C_k}`.

Lean strategy / thesis relation note: this is extensional equality of the finite subsets. The thesis
uses ordinary finite-set equality; Lean proves equality of the subtype package
by proving equality of membership in the underlying sets.
-/
theorem FixedBlockEnumeration.segmentDistinctFiniteSet_eq_distinctFiniteSet
    [Preorder X] {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) (K : ConnectedSegment (Sigma.mk n x : Tuple X))
    (hK :
      segmentIndices (Sigma.mk n x : Tuple X) K =
        (B.block : Set (Fin n))) :
    segmentDistinctFiniteSet (X := X) (Sigma.mk n x : Tuple X) K =
      B.distinctFiniteSet (X := X) x := by
  apply Subtype.ext
  apply Subtype.ext
  ext p
  rw [mem_segmentDistinctFiniteSet,
    FixedBlockEnumeration.mem_distinctFiniteSet_iff]
  constructor
  · rintro ⟨i, hiK, hp⟩
    exact ⟨i, by simpa [hK] using hiK, by simpa using hp⟩
  · rintro ⟨i, hiB, hp⟩
    exact ⟨i, by simpa [hK] using hiB, by simpa using hp⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: construction of the branch-local permutation `π_k` in
`thm:minimal-sorting-measurable`.

Informal statement: for one connected segment of a tuple, store the finite
block of indices together with the exact enumeration chosen by the thesis'
recursive least-index value-minimal finite-set sorter.

Lean strategy / thesis relation note: the thesis writes this as a permutation
`π_k ∈ Π(C_k)`. Lean stores the same data as a `FixedBlockEnumeration`: the
block is the finite set of indices in the connected segment, and the
enumeration reads the index coordinate of the sorted graph-point list.
-/
noncomputable def FixedBlockEnumeration.ofSegmentSort
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X)) :
    FixedBlockEnumeration n := by
  classical
  let y : Tuple X := Sigma.mk n x
  let ξ : DistinctFiniteSubsets X :=
    segmentDistinctFiniteSet (X := X) y K
  let l : List (IndexAugmented X) :=
    distinctFiniteSetSortList (X := X) ξ
  refine
    { length := l.length
      block := segmentIndexFinset (X := X) y K
      enum := fun r =>
        ⟨IndexAugmented.index (l.get r), ?_⟩ }
  have hmem : l.get r ∈ l := List.get_mem l r
  have hset : l.get r ∈ (ξ.1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X) ξ).mp hmem
  rcases (mem_segmentDistinctFiniteSet (X := X) y K).mp hset with
    ⟨i, _hiK, hp⟩
  have hidx : IndexAugmented.index (l.get r) = i.1 := by
    simpa using congrArg IndexAugmented.index hp
  exact hidx.trans_lt i.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: nonempty blocks `C_k` in
`thm:minimal-sorting-measurable`.

Informal statement: the block obtained from a connected segment is nonempty.

Lean strategy / thesis relation note: the thesis treats connected components as nonempty partition
blocks. Lean proves this from the quotient representation of connected
segments and the `segmentIndexFinset_nonempty` lemma.
-/
theorem FixedBlockEnumeration.ofSegmentSort_block_nonempty
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X)) :
    (FixedBlockEnumeration.ofSegmentSort (X := X) x K).block.Nonempty := by
  classical
  let y : Tuple X := Sigma.mk n x
  simpa [FixedBlockEnumeration.ofSegmentSort, y] using
    (segmentIndexFinset_nonempty (X := X) y K)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block component of the constructed `π_k`.

Informal statement: the block stored by the segment-derived enumeration is
exactly the connected segment's finite index set.
-/
@[simp]
theorem FixedBlockEnumeration.ofSegmentSort_block
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X)) :
    (FixedBlockEnumeration.ofSegmentSort (X := X) x K).block =
      segmentIndexFinset (X := X) (Sigma.mk n x : Tuple X) K := by
  simp [FixedBlockEnumeration.ofSegmentSort]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: domain length of the constructed `π_k`.

Informal statement: the segment-derived enumeration has the same length as
the sorted graph-point list for that connected segment.
-/
@[simp]
theorem FixedBlockEnumeration.ofSegmentSort_length
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X)) :
    (FixedBlockEnumeration.ofSegmentSort (X := X) x K).length =
      (distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet (X := X)
          (Sigma.mk n x : Tuple X) K)).length := by
  simp [FixedBlockEnumeration.ofSegmentSort]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: graph-point reading of the constructed `π_k`.

Informal statement: reading the tuple graph along the segment-derived
enumeration recovers the corresponding entry of the sorted graph-point list.
-/
theorem FixedBlockEnumeration.ofSegmentSort_graphPoint_eq_get
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X))
    (r : Fin
      (distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet (X := X)
          (Sigma.mk n x : Tuple X) K)).length) :
    IndexAugmented.mk
        ((FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r).1
        (x ((FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r)) =
      (distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet (X := X)
          (Sigma.mk n x : Tuple X) K)).get r := by
  classical
  let y : Tuple X := Sigma.mk n x
  let ξ : DistinctFiniteSubsets X :=
    segmentDistinctFiniteSet (X := X) y K
  let l : List (IndexAugmented X) :=
    distinctFiniteSetSortList (X := X) ξ
  have hmem : l.get r ∈ l := List.get_mem l r
  have hset : l.get r ∈ (ξ.1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X) ξ).mp hmem
  rcases (mem_segmentDistinctFiniteSet (X := X) y K).mp hset with
    ⟨i, _hiK, hp⟩
  have henum : (FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r = i := by
    apply Fin.ext
    have hidx : IndexAugmented.index (l.get r) = i.1 := by
      simpa using congrArg IndexAugmented.index hp
    simpa [FixedBlockEnumeration.ofSegmentSort, y, ξ, l, hidx]
  rw [henum]
  simpa [y] using hp.symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: membership of the constructed `π_k`.

Informal statement: the segment-derived enumeration maps into the connected
segment block.
-/
theorem FixedBlockEnumeration.ofSegmentSort_enum_mem_segmentIndices
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X))
    (r : Fin
      (distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet (X := X)
          (Sigma.mk n x : Tuple X) K)).length) :
    (FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r ∈
      segmentIndices (Sigma.mk n x : Tuple X) K := by
  classical
  let y : Tuple X := Sigma.mk n x
  let ξ : DistinctFiniteSubsets X :=
    segmentDistinctFiniteSet (X := X) y K
  let l : List (IndexAugmented X) :=
    distinctFiniteSetSortList (X := X) ξ
  have hmem : l.get r ∈ l := List.get_mem l r
  have hset : l.get r ∈ (ξ.1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X) ξ).mp hmem
  rcases (mem_segmentDistinctFiniteSet (X := X) y K).mp hset with
    ⟨i, hiK, hp⟩
  have henum : (FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r = i := by
    apply Fin.ext
    have hidx : IndexAugmented.index (l.get r) = i.1 := by
      simpa using congrArg IndexAugmented.index hp
    simpa [FixedBlockEnumeration.ofSegmentSort, y, ξ, l, hidx]
  simpa [henum, y] using hiK

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `π_k ∈ Π(C_k)` for the constructed branch-local
permutation.

Informal statement: the segment-derived enumeration hits exactly the indices
of its connected segment block.
-/
theorem FixedBlockEnumeration.ofSegmentSort_coversBlock
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X)) :
    (FixedBlockEnumeration.ofSegmentSort (X := X) x K).CoversBlock := by
  classical
  let y : Tuple X := Sigma.mk n x
  let ξ : DistinctFiniteSubsets X :=
    segmentDistinctFiniteSet (X := X) y K
  let l : List (IndexAugmented X) :=
    distinctFiniteSetSortList (X := X) ξ
  intro i
  constructor
  · intro hi
    have hiK : i ∈ segmentIndices y K := by
      simpa [FixedBlockEnumeration.ofSegmentSort, y, segmentIndexFinset,
        segmentIndices] using hi
    let p : IndexAugmented X := IndexAugmented.mk i.1 (x i)
    have hpSet : p ∈ (ξ.1 : Set (IndexAugmented X)) := by
      apply (mem_segmentDistinctFiniteSet (X := X) y K).mpr
      exact ⟨i, hiK, by simp [p, y]⟩
    have hpList : p ∈ l :=
      (mem_distinctFiniteSetSortList_iff (X := X) ξ).mpr hpSet
    rcases List.mem_iff_get.mp hpList with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    apply Fin.ext
    have hidx : IndexAugmented.index (l.get r) = i.1 := by
      simpa [p] using congrArg IndexAugmented.index hr
    simpa [FixedBlockEnumeration.ofSegmentSort, y, ξ, l, hidx]
  · rintro ⟨r, hri⟩
    have hmem : l.get r ∈ l := List.get_mem l r
    have hset : l.get r ∈ (ξ.1 : Set (IndexAugmented X)) :=
      (mem_distinctFiniteSetSortList_iff (X := X) ξ).mp hmem
    rcases (mem_segmentDistinctFiniteSet (X := X) y K).mp hset with
      ⟨j, hjK, hp⟩
    have henum : (FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r = j := by
      apply Fin.ext
      have hidx : IndexAugmented.index (l.get r) = j.1 := by
        simpa using congrArg IndexAugmented.index hp
      simpa [FixedBlockEnumeration.ofSegmentSort, y, ξ, l, hidx]
    have hiK : i ∈ segmentIndices y K := by
      rw [← hri, henum]
      exact hjK
    simpa [FixedBlockEnumeration.ofSegmentSort, y, segmentIndexFinset,
      segmentIndices] using hiK

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: injectivity of the constructed `π_k ∈ Π(C_k)`.

Informal statement: the segment-derived enumeration has no duplicate source
indices.
-/
theorem FixedBlockEnumeration.ofSegmentSort_injectiveEnumeration
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X)) :
    (FixedBlockEnumeration.ofSegmentSort (X := X) x K).InjectiveEnumeration := by
  classical
  let y : Tuple X := Sigma.mk n x
  let ξ : DistinctFiniteSubsets X :=
    segmentDistinctFiniteSet (X := X) y K
  let l : List (IndexAugmented X) :=
    distinctFiniteSetSortList (X := X) ξ
  intro r s hrs
  have hrmem : l.get r ∈ l := List.get_mem l r
  have hsmem : l.get s ∈ l := List.get_mem l s
  have hrset : l.get r ∈ (ξ.1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X) ξ).mp hrmem
  have hsset : l.get s ∈ (ξ.1 : Set (IndexAugmented X)) :=
    (mem_distinctFiniteSetSortList_iff (X := X) ξ).mp hsmem
  have hidx :
      IndexAugmented.index (l.get r) =
        IndexAugmented.index (l.get s) := by
    simpa [FixedBlockEnumeration.ofSegmentSort, y, ξ, l] using
      congrArg Fin.val hrs
  have hpoint : l.get r = l.get s :=
    DistinctFiniteSubsets.index_injOn ξ hrset hsset hidx
  exact list_get_injective_of_nodup
    (nodup_distinctFiniteSetSortList (X := X) ξ) hpoint

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized refined-cell data
`(P,\pi_1,\dots,\pi_m)` in `thm:minimal-sorting-measurable`.

Informal statement: from one fixed-length tuple, list its connected segments
by first arrival and attach to each segment the enumeration chosen by the
minimum finite-set sorter.

Lean strategy / thesis relation note: this is the tuple-dependent data that witnesses membership in
some refined cell. The later finite-cover theorem will quotient out the
tuple-dependence by observing that only finitely many such combinatorial
patterns can occur for fixed `n`.
-/
noncomputable def FixedMinimalSortingBranch.blocksOfTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    List (FixedBlockEnumeration n) :=
  (segmentListByArrival (X := X) (Sigma.mk n x : Tuple X)).map
    fun K => FixedBlockEnumeration.ofSegmentSort (X := X) x K

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized refined branch
`(P,\pi_1,\dots,\pi_m)` in `thm:minimal-sorting-measurable`.

Informal statement: the connectivity relation and the segment-local minimum
sorting enumerations associated with one tuple form genuine fixed branch
data: the blocks partition the domain, each `π_k` is a bijection onto its
block, and distinct blocks are disjoint.

Lean strategy / thesis relation note: the thesis chooses `P` as the connected-index partition of
the tuple and `π_k` as the finite-set sorting permutation on each block.
Lean records `P` as the relation `IndexConnected`.
-/
noncomputable def FixedMinimalSortingBranch.ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    FixedMinimalSortingBranch n := by
  classical
  let y : Tuple X := Sigma.mk n x
  refine
    { relation := fun i j : Fin n => IndexConnected y i j
      blocks := FixedMinimalSortingBranch.blocksOfTuple (X := X) x
      blockRelation := ?_
      coversBlock := ?_
      injectiveEnumeration := ?_
      pairwiseDisjointBlocks := ?_
      coversAllIndices := ?_ }
  · intro i j
    constructor
    · intro hij
      let K : ConnectedSegment y := indexSegment y i
      let B : FixedBlockEnumeration n :=
        FixedBlockEnumeration.ofSegmentSort (X := X) x K
      have hseg : indexSegment y i = indexSegment y j :=
        (indexConnected_iff_same_segment (X := X) y i j).mp hij
      refine ⟨B, ?_, ?_, ?_⟩
      · rw [FixedMinimalSortingBranch.blocksOfTuple, List.mem_map]
        exact ⟨K, mem_segmentListByArrival (X := X) y K, rfl⟩
      · simp [B, K, FixedBlockEnumeration.ofSegmentSort,
          segmentIndexFinset, y]
      · have hjK : j ∈ segmentIndices y K := by
          simpa [K] using hseg.symm
        simpa [B, FixedBlockEnumeration.ofSegmentSort,
          segmentIndexFinset, segmentIndices, y] using hjK
    · rintro ⟨B, hBmem, hiB, hjB⟩
      rw [FixedMinimalSortingBranch.blocksOfTuple, List.mem_map] at hBmem
      rcases hBmem with ⟨K, _hKmem, rfl⟩
      have hiK : i ∈ segmentIndices y K := by
        simpa [FixedBlockEnumeration.ofSegmentSort,
          segmentIndexFinset, segmentIndices, y] using hiB
      have hjK : j ∈ segmentIndices y K := by
        simpa [FixedBlockEnumeration.ofSegmentSort,
          segmentIndexFinset, segmentIndices, y] using hjB
      exact indexConnected_of_mem_same_segment (X := X) y hiK hjK
  · intro B hBmem
    rw [FixedMinimalSortingBranch.blocksOfTuple, List.mem_map] at hBmem
    rcases hBmem with ⟨K, _hKmem, rfl⟩
    exact FixedBlockEnumeration.ofSegmentSort_coversBlock (X := X) x K
  · intro B hBmem
    rw [FixedMinimalSortingBranch.blocksOfTuple, List.mem_map] at hBmem
    rcases hBmem with ⟨K, _hKmem, rfl⟩
    exact
      FixedBlockEnumeration.ofSegmentSort_injectiveEnumeration
        (X := X) x K
  · rw [FixedMinimalSortingBranch.blocksOfTuple]
    refine
      List.Pairwise.map
        (fun K : ConnectedSegment y =>
          FixedBlockEnumeration.ofSegmentSort (X := X) x K)
        ?_
        (List.nodup_iff_pairwise_ne.mp
          (nodup_segmentListByArrival (X := X) y))
    intro K L hKL
    have hdisj :
        Disjoint (segmentIndices y K) (segmentIndices y L) :=
      segmentIndices_disjoint_of_ne (X := X) y hKL
    simpa [FixedBlockEnumeration.ofSegmentSort,
      segmentIndexFinset, segmentIndices, y] using hdisj
  · intro i
    let K : ConnectedSegment y := indexSegment y i
    let B : FixedBlockEnumeration n :=
      FixedBlockEnumeration.ofSegmentSort (X := X) x K
    refine ⟨B, ?_, ?_⟩
    · rw [FixedMinimalSortingBranch.blocksOfTuple, List.mem_map]
      exact ⟨K, mem_segmentListByArrival (X := X) y K, rfl⟩
    · simp [B, K, FixedBlockEnumeration.ofSegmentSort,
        segmentIndexFinset, y]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: first-arrival ordering of realized refined-cell data in
`thm:minimal-sorting-measurable`.

Informal statement: the branch constructed from a tuple lists its blocks in
the tuple's first-arrival segment order.
-/
theorem FixedMinimalSortingBranch.ofTuple_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    (FixedMinimalSortingBranch.ofTuple (X := X) x).blocksMatchSegmentArrival
      (X := X) x := by
  rw [FixedMinimalSortingBranch.blocksMatchSegmentArrival]
  simp only [FixedMinimalSortingBranch.ofTuple,
    FixedMinimalSortingBranch.blocksOfTuple, List.map_map]
  apply List.map_congr_left
  intro K _hK
  ext i
  simp [FixedBlockEnumeration.ofSegmentSort, segmentIndexFinset,
    segmentIndices]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: connectivity-pattern membership for the realized refined
cell.

Informal statement: the tuple that realizes a branch satisfies the branch's
fixed connectivity pattern by construction.
-/
theorem FixedMinimalSortingBranch.mem_connectivityPatternCell_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    x ∈ fixedConnectivityPatternCell (X := X) n
      (FixedMinimalSortingBranch.ofTuple (X := X) x).relation := by
  intro i j
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: list representation of `\pi_k ∈ \Pi(C_k)`.

Informal statement: if the stored enumeration covers its block, then the
block graph list has exactly the points of the block's distinct finite set.
-/
theorem FixedBlockEnumeration.mem_graphList_iff_of_coversBlock
    {X : Type u} {n : ℕ} {B : FixedBlockEnumeration n}
    (hB : B.CoversBlock) (x : Fin n → X) {p : IndexAugmented X} :
    p ∈ B.graphList (X := X) x ↔
      p ∈ ((B.distinctFiniteSet (X := X) x).1 :
        Set (IndexAugmented X)) := by
  constructor
  · intro hp
    rw [FixedBlockEnumeration.graphList, fixedIndexGraphList,
      List.mem_map] at hp
    rcases hp with ⟨i, hi, rfl⟩
    exact (FixedBlockEnumeration.mem_distinctFiniteSet_iff
      (X := X) B x).mpr
        ⟨i, (FixedBlockEnumeration.mem_indexList_iff_of_coversBlock
          (B := B) hB i).mp hi, rfl⟩
  · intro hp
    rcases (FixedBlockEnumeration.mem_distinctFiniteSet_iff
        (X := X) B x).mp hp with
      ⟨i, hiB, rfl⟩
    rw [FixedBlockEnumeration.graphList, fixedIndexGraphList,
      List.mem_map]
    exact ⟨i,
      (FixedBlockEnumeration.mem_indexList_iff_of_coversBlock
        (B := B) hB i).mpr hiB, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-set form of one block graph enumeration.

Informal statement: converting a genuine block graph list to a finite set
recovers exactly the block's distinct finite graph set.
-/
theorem FixedBlockEnumeration.graphPointListToFinset_graphList_eq
    {X : Type u} {n : ℕ} {B : FixedBlockEnumeration n}
    (hB : B.CoversBlock) (x : Fin n → X) :
    graphPointListToFinset (X := X) (B.graphList (X := X) x) =
      toFinset (B.distinctFiniteSet (X := X) x).1 := by
  ext p
  rw [mem_graphPointListToFinset, mem_toFinset]
  exact FixedBlockEnumeration.mem_graphList_iff_of_coversBlock
    (B := B) hB x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-domain bookkeeping for one block graph list.

Informal statement: the block graph list has the stored block length.
-/
@[simp]
theorem FixedBlockEnumeration.length_graphList
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) :
    (B.graphList (X := X) x).length = B.length := by
  simp [FixedBlockEnumeration.graphList, fixedIndexGraphList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: pointwise reading of `\pi_k`.

Informal statement: the `r`th graph point of a block graph list is
`(π_k(r), x_{π_k(r)})`.
-/
theorem FixedBlockEnumeration.graphList_get
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) (r : Fin B.length) :
    (B.graphList (X := X) x).get
        (Fin.cast (FixedBlockEnumeration.length_graphList
          (X := X) B x).symm r) =
      IndexAugmented.mk (B.enum r).1 (x (B.enum r)) := by
  simp [FixedBlockEnumeration.graphList, fixedIndexGraphList,
    FixedBlockEnumeration.indexList, List.get_eq_getElem]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: first half of the stage condition `M_{C,\pi,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: if the block graph list is sorted in the thesis sense
(no later graph point has strictly smaller value than an earlier one), then
the stage-selected index `π(r)` has no strictly lower-valued competitor in
the remaining block.

Lean strategy / thesis relation note: the proof expands `C^{(r)}` using
`mem_remaining_iff_exists_enum_ge`, the explicit Lean form of the thesis
tail identity for `C^{(r)}`.
-/
theorem FixedBlockEnumeration.no_strict_lower_of_pairwise_graphList
    [Preorder X] {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    (x : Fin n → X)
    (hpair :
      List.Pairwise (fun p q : IndexAugmented X =>
        ¬ IndexAugmented.value q < IndexAugmented.value p)
        (B.graphList (X := X) x))
    (r : Fin B.length) :
    ∀ j : Fin n, j ∈ fixedBlockRemaining B.block B.enum r →
      ¬ x j < x (B.enum r) := by
  intro j hj hlt
  rcases (FixedBlockEnumeration.mem_remaining_iff_exists_enum_ge
      (B := B) hcov hinj r j).mp hj with
    ⟨s, hrs, hs⟩
  by_cases hsr : r = s
  · subst s
    rw [← hs] at hlt
    exact (lt_irrefl (x (B.enum r))) hlt
  · have hlt_rs : r < s := lt_of_le_of_ne hrs hsr
    let rG : Fin (B.graphList (X := X) x).length :=
      Fin.cast (FixedBlockEnumeration.length_graphList (X := X) B x).symm r
    let sG : Fin (B.graphList (X := X) x).length :=
      Fin.cast (FixedBlockEnumeration.length_graphList (X := X) B x).symm s
    have hltG : rG < sG := by
      simpa [rG, sG] using hlt_rs
    have hno := (List.pairwise_iff_get.mp hpair) rG sG hltG
    have hgetr := FixedBlockEnumeration.graphList_get (X := X) B x r
    have hgets := FixedBlockEnumeration.graphList_get (X := X) B x s
    have hgetr' :
        (B.graphList (X := X) x).get rG =
          IndexAugmented.mk (B.enum r).1 (x (B.enum r)) := by
      simpa [rG] using hgetr
    have hgets' :
        (B.graphList (X := X) x).get sG =
          IndexAugmented.mk (B.enum s).1 (x (B.enum s)) := by
      simpa [sG] using hgets
    exact hno (by
      rw [hgets', hgetr']
      simpa [hs] using hlt)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: branch-local agreement for the constructed `π_k`.

Informal statement: the fixed graph list induced by the segment-derived
enumeration is exactly the recursive finite-set sort list for that segment.

Lean strategy / thesis relation note: this is the constructed-branch counterpart of the earlier
cell-local theorem. Here the agreement is by construction of `π_k` from the
sorter's own output.
-/
theorem FixedBlockEnumeration.ofSegmentSort_graphList_eq_sortList
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X)) :
    (FixedBlockEnumeration.ofSegmentSort (X := X) x K).graphList (X := X) x =
      distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet (X := X)
          (Sigma.mk n x : Tuple X) K) := by
  classical
  let B : FixedBlockEnumeration n :=
    FixedBlockEnumeration.ofSegmentSort (X := X) x K
  let l : List (IndexAugmented X) :=
    distinctFiniteSetSortList (X := X)
      (segmentDistinctFiniteSet (X := X) (Sigma.mk n x : Tuple X) K)
  apply List.ext_get
  · rw [FixedBlockEnumeration.length_graphList]
    simp
  · intro k hleft hright
    let r : Fin l.length := ⟨k, by simpa [l] using hright⟩
    have hgraph :
        (B.graphList (X := X) x).get ⟨k, hleft⟩ =
          IndexAugmented.mk (B.enum r).1 (x (B.enum r)) := by
      simpa [B, l, r] using
        FixedBlockEnumeration.graphList_get (X := X) B x r
    have hsort :
        IndexAugmented.mk (B.enum r).1 (x (B.enum r)) =
          l.get r := by
      simpa [B, l, r] using
        FixedBlockEnumeration.ofSegmentSort_graphPoint_eq_get
          (X := X) x K r
    exact hgraph.trans hsort

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: first half of the stage condition `M_{C_k,\pi_k,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: for the block enumeration constructed from a connected
segment, the selected index has no strictly lower-valued remaining competitor.

Lean strategy / thesis relation note: this is the thesis proof's recursive-minimum argument after
the constructed enumeration has been identified with the recursive
finite-set sort list.
-/
theorem FixedBlockEnumeration.ofSegmentSort_no_strict_lower
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X))
    (r : Fin (FixedBlockEnumeration.ofSegmentSort (X := X) x K).length) :
    ∀ j : Fin n,
      j ∈ fixedBlockRemaining
        (FixedBlockEnumeration.ofSegmentSort (X := X) x K).block
        (FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r →
      ¬ x j < x
        ((FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r) := by
  classical
  let B : FixedBlockEnumeration n :=
    FixedBlockEnumeration.ofSegmentSort (X := X) x K
  have hpairSort :
      List.Pairwise (fun p q : IndexAugmented X =>
        ¬ IndexAugmented.value q < IndexAugmented.value p)
        (distinctFiniteSetSortList (X := X)
          (segmentDistinctFiniteSet (X := X)
            (Sigma.mk n x : Tuple X) K)) := by
    simpa [distinctFiniteSetSortList] using
      pairwise_no_later_lt_distinctFiniteSetSortListAux
        (X := X)
        (toFinset
          (segmentDistinctFiniteSet (X := X)
            (Sigma.mk n x : Tuple X) K).1)
  have hpair :
      List.Pairwise (fun p q : IndexAugmented X =>
        ¬ IndexAugmented.value q < IndexAugmented.value p)
        (B.graphList (X := X) x) := by
    simpa [B, FixedBlockEnumeration.ofSegmentSort_graphList_eq_sortList
      (X := X) x K] using hpairSort
  simpa [B] using
    FixedBlockEnumeration.no_strict_lower_of_pairwise_graphList
      (B := B)
      (FixedBlockEnumeration.ofSegmentSort_coversBlock (X := X) x K)
      (FixedBlockEnumeration.ofSegmentSort_injectiveEnumeration (X := X) x K)
      x hpair r

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-list bookkeeping for one block enumeration.

Informal statement: dropping a block graph list to stage `r` exposes
`(π(r),x_{π(r)})` as the next head, followed by the stage `r+1` suffix.
-/
theorem FixedBlockEnumeration.graphList_drop_eq_cons
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) {r : Fin B.length}
    (_hr : r.1 + 1 < B.length) :
    (B.graphList (X := X) x).drop r.1 =
      IndexAugmented.mk (B.enum r).1 (x (B.enum r)) ::
        (B.graphList (X := X) x).drop (r.1 + 1) := by
  have hdrop := List.drop_eq_getElem_cons
    (l := B.graphList (X := X) x) (i := r.1)
    (by simp [FixedBlockEnumeration.length_graphList])
  have hhead :
      (B.graphList (X := X) x)[r.1] =
        IndexAugmented.mk (B.enum r).1 (x (B.enum r)) := by
    simpa [List.get_eq_getElem] using
      FixedBlockEnumeration.graphList_get (X := X) B x r
  simpa [hhead] using hdrop

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: terminal finite-list bookkeeping for one block enumeration.

Informal statement: at the final stage, the graph-list suffix contains only
the final selected graph point.
-/
theorem FixedBlockEnumeration.graphList_drop_eq_singleton_of_last
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) {r : Fin B.length}
    (hlast : ¬ r.1 + 1 < B.length) :
    (B.graphList (X := X) x).drop r.1 =
      [IndexAugmented.mk (B.enum r).1 (x (B.enum r))] := by
  have hdrop := List.drop_eq_getElem_cons
    (l := B.graphList (X := X) x) (i := r.1)
    (by simp [FixedBlockEnumeration.length_graphList])
  have hhead :
      (B.graphList (X := X) x)[r.1] =
        IndexAugmented.mk (B.enum r).1 (x (B.enum r)) := by
    simpa [List.get_eq_getElem] using
      FixedBlockEnumeration.graphList_get (X := X) B x r
  have htail :
      (B.graphList (X := X) x).drop (r.1 + 1) = [] := by
    exact List.drop_eq_nil_of_le (by
      simpa [FixedBlockEnumeration.length_graphList] using
        Nat.le_of_not_gt hlast)
  simpa [hhead, htail] using hdrop

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: duplicate-free block graph list for `\pi_k ∈ \Pi(C_k)`.

Informal statement: an injective stored block enumeration gives a
duplicate-free block graph list.
-/
theorem FixedBlockEnumeration.nodup_graphList_of_injective
    {X : Type u} {n : ℕ} {B : FixedBlockEnumeration n}
    (hB : B.InjectiveEnumeration) (x : Fin n → X) :
    (B.graphList (X := X) x).Nodup := by
  rw [FixedBlockEnumeration.graphList, fixedIndexGraphList]
  exact (FixedBlockEnumeration.nodup_indexList_of_injective
    (B := B) hB).map (by
      intro i j hij
      apply Fin.ext
      simpa using congrArg IndexAugmented.index hij)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: remaining graph set `C^{(r)}` in
`thm:minimal-sorting-measurable`.

Informal statement: turn the remaining index set at stage `r` into the
corresponding finite graph-point set.
-/
noncomputable def FixedBlockEnumeration.remainingGraphFinset
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) (r : Fin B.length) : Finset (IndexAugmented X) := by
  classical
  exact (fixedBlockRemaining B.block B.enum r).image
    (fun i : Fin n => IndexAugmented.mk i.1 (x i))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: membership in the remaining graph set `C^{(r)}`.

Informal statement: a graph point belongs to the remaining graph finset
exactly when it is `(i,x_i)` for a remaining index `i`.
-/
theorem FixedBlockEnumeration.mem_remainingGraphFinset_iff
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) (r : Fin B.length) {p : IndexAugmented X} :
    p ∈ B.remainingGraphFinset (X := X) x r ↔
      ∃ i : Fin n, i ∈ fixedBlockRemaining B.block B.enum r ∧
        p = IndexAugmented.mk i.1 (x i) := by
  classical
  constructor
  · intro hp
    rw [FixedBlockEnumeration.remainingGraphFinset] at hp
    rcases Finset.mem_image.mp hp with ⟨i, hiR, hip⟩
    exact ⟨i, hiR, hip.symm⟩
  · rintro ⟨i, hiR, rfl⟩
    rw [FixedBlockEnumeration.remainingGraphFinset]
    exact Finset.mem_image.mpr ⟨i, hiR, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: remaining graph set `C^{(r)}` in
`thm:minimal-sorting-measurable`.

Informal statement: for a genuine block enumeration, the graph-point
remainder at stage `r` is exactly the finite set attached to the dropped tail
of the block graph list.

Lean strategy / thesis relation note: the thesis writes this as an obvious identification between
`C^{(r)}` and the unprocessed tail of the permutation; Lean needs the finite
index conversion explicitly.
-/
theorem FixedBlockEnumeration.remainingGraphFinset_eq_graphPointListToFinset_drop
    {X : Type u} {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    (x : Fin n → X) (r : Fin B.length) :
    B.remainingGraphFinset (X := X) x r =
      graphPointListToFinset (X := X)
        ((B.graphList (X := X) x).drop r.1) := by
  classical
  ext p
  rw [FixedBlockEnumeration.mem_remainingGraphFinset_iff,
    mem_graphPointListToFinset]
  constructor
  · rintro ⟨i, hiR, hp⟩
    rcases (FixedBlockEnumeration.mem_remaining_iff_exists_enum_ge
        (B := B) hcov hinj r i).mp hiR with
      ⟨s, hrs, hs⟩
    rw [list_mem_drop_iff_exists_get_ge]
    let sG : Fin (B.graphList (X := X) x).length :=
      Fin.cast (FixedBlockEnumeration.length_graphList (X := X) B x).symm s
    refine ⟨sG, ?_, ?_⟩
    · simpa [sG] using hrs
    · have hget :=
        FixedBlockEnumeration.graphList_get (X := X) B x s
      have hget' :
          (B.graphList (X := X) x).get sG =
            IndexAugmented.mk (B.enum s).1 (x (B.enum s)) := by
        simpa [sG] using hget
      rw [hget', hs]
      exact hp.symm
  · intro hp
    rw [list_mem_drop_iff_exists_get_ge] at hp
    rcases hp with ⟨sG, hrs, hget⟩
    let s : Fin B.length :=
      Fin.cast (FixedBlockEnumeration.length_graphList (X := X) B x) sG
    have hrs' : r ≤ s := by
      simpa [s] using hrs
    have hget_graph :=
      FixedBlockEnumeration.graphList_get (X := X) B x s
    have hget_graph' :
        (B.graphList (X := X) x).get sG =
          IndexAugmented.mk (B.enum s).1 (x (B.enum s)) := by
      simpa [s] using hget_graph
    have hp_eq :
        p = IndexAugmented.mk (B.enum s).1 (x (B.enum s)) :=
      hget.symm.trans hget_graph'
    have hiR : B.enum s ∈ fixedBlockRemaining B.block B.enum r :=
      (FixedBlockEnumeration.mem_remaining_iff_exists_enum_ge
        (B := B) hcov hinj r (B.enum s)).mpr ⟨s, hrs', rfl⟩
    exact ⟨B.enum s, hiR, hp_eq⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: zero-stage graph form of `C^{(r)}` in
`thm:minimal-sorting-measurable`.

Informal statement: the stage-zero remaining graph finset is exactly the
finite graph subset `{(i,x_i): i ∈ C}` attached to the block.
-/
theorem FixedBlockEnumeration.remainingGraphFinset_zero_eq_toFinset
    {X : Type u} {n : ℕ} {B : FixedBlockEnumeration n}
    (x : Fin n → X) (hpos : 0 < B.length) :
    B.remainingGraphFinset (X := X) x ⟨0, hpos⟩ =
      toFinset (B.distinctFiniteSet (X := X) x).1 := by
  ext p
  rw [FixedBlockEnumeration.mem_remainingGraphFinset_iff, mem_toFinset,
    FixedBlockEnumeration.mem_distinctFiniteSet_iff]
  constructor
  · rintro ⟨i, hiR, hp⟩
    have hiB : i ∈ B.block := by
      simpa [fixedBlockRemaining_zero B.block B.enum hpos] using hiR
    exact ⟨i, hiB, hp⟩
  · rintro ⟨i, hiB, hp⟩
    have hiR : i ∈ fixedBlockRemaining B.block B.enum ⟨0, hpos⟩ := by
      simpa [fixedBlockRemaining_zero B.block B.enum hpos] using hiB
    exact ⟨i, hiR, hp⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: nonempty remaining set `C^{(r)}`.

Informal statement: for a genuine block enumeration, the remaining graph
finset at stage `r` is nonempty because it contains `(π(r),x_{π(r)})`.
-/
theorem FixedBlockEnumeration.remainingGraphFinset_nonempty
    {X : Type u} {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    (x : Fin n → X) (r : Fin B.length) :
    (B.remainingGraphFinset (X := X) x r).Nonempty := by
  refine ⟨IndexAugmented.mk (B.enum r).1 (x (B.enum r)), ?_⟩
  rw [FixedBlockEnumeration.mem_remainingGraphFinset_iff]
  exact ⟨B.enum r,
    FixedBlockEnumeration.enum_mem_remaining_of_coversBlock_injective
      (B := B) hcov hinj r, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: recursive selector equality inside
`thm:minimal-sorting-measurable`.

Informal statement: for the block enumeration constructed from a connected
segment, the current graph point `(π_k(r),x_{π_k(r)})` is the least-index
value-minimal point of the current remaining graph set.

Lean strategy / thesis relation note: this is the thesis recursive sorting rule, with the finite
tail `C^{(r)}` made explicit through
`remainingGraphFinset_eq_graphPointListToFinset_drop`.
-/
theorem FixedBlockEnumeration.ofSegmentSort_leastIndexValueMinimal_remainingGraphFinset_eq
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X))
    (r : Fin (FixedBlockEnumeration.ofSegmentSort (X := X) x K).length) :
    leastIndexValueMinimal (X := X)
        (FixedBlockEnumeration.remainingGraphFinset (X := X)
          (FixedBlockEnumeration.ofSegmentSort (X := X) x K) x r)
        (FixedBlockEnumeration.remainingGraphFinset_nonempty
          (B := FixedBlockEnumeration.ofSegmentSort (X := X) x K)
          (FixedBlockEnumeration.ofSegmentSort_coversBlock (X := X) x K)
          (FixedBlockEnumeration.ofSegmentSort_injectiveEnumeration
            (X := X) x K)
          x r) =
      IndexAugmented.mk
        ((FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r).1
        (x ((FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r)) := by
  classical
  let B : FixedBlockEnumeration n :=
    FixedBlockEnumeration.ofSegmentSort (X := X) x K
  let ξ : DistinctFiniteSubsets X :=
    segmentDistinctFiniteSet (X := X) (Sigma.mk n x : Tuple X) K
  let S : Finset (IndexAugmented X) := toFinset ξ.1
  have hcov : B.CoversBlock := by
    simpa [B] using FixedBlockEnumeration.ofSegmentSort_coversBlock
      (X := X) x K
  have hinj : B.InjectiveEnumeration := by
    simpa [B] using FixedBlockEnumeration.ofSegmentSort_injectiveEnumeration
      (X := X) x K
  have hlen :
      B.length = (distinctFiniteSetSortListAux (X := X) S).length := by
    simp [B, ξ, S, distinctFiniteSetSortList]
  let rS : Fin (distinctFiniteSetSortListAux (X := X) S).length :=
    Fin.cast hlen r
  have hsdrop :
      (graphPointListToFinset (X := X)
        ((distinctFiniteSetSortListAux (X := X) S).drop rS.1)).Nonempty := by
    refine ⟨(distinctFiniteSetSortListAux (X := X) S).get rS, ?_⟩
    rw [mem_graphPointListToFinset]
    rw [list_mem_drop_iff_exists_get_ge]
    exact ⟨rS, le_rfl, rfl⟩
  have hrem :
      B.remainingGraphFinset (X := X) x r =
        graphPointListToFinset (X := X)
          ((distinctFiniteSetSortListAux (X := X) S).drop rS.1) := by
    calc
      B.remainingGraphFinset (X := X) x r =
          graphPointListToFinset (X := X)
            ((B.graphList (X := X) x).drop r.1) := by
            exact FixedBlockEnumeration.remainingGraphFinset_eq_graphPointListToFinset_drop
              (B := B) hcov hinj x r
      _ = graphPointListToFinset (X := X)
          ((distinctFiniteSetSortListAux (X := X) S).drop rS.1) := by
            simp [B, ξ, S, rS, distinctFiniteSetSortList,
              FixedBlockEnumeration.ofSegmentSort_graphList_eq_sortList
                (X := X) x K]
  have hleast_congr :
      leastIndexValueMinimal (X := X)
          (B.remainingGraphFinset (X := X) x r)
          (FixedBlockEnumeration.remainingGraphFinset_nonempty
            (B := B) hcov hinj x r) =
        leastIndexValueMinimal (X := X)
          (graphPointListToFinset (X := X)
            ((distinctFiniteSetSortListAux (X := X) S).drop rS.1))
          hsdrop :=
    leastIndexValueMinimal_congr (X := X) hrem
      (FixedBlockEnumeration.remainingGraphFinset_nonempty
        (B := B) hcov hinj x r)
      hsdrop
  have hleast_tail :=
    leastIndexValueMinimal_graphPointListToFinset_drop_distinctFiniteSetSortListAux
      (X := X) S rS hsdrop
  have hpoint :
      (distinctFiniteSetSortListAux (X := X) S).get rS =
        IndexAugmented.mk (B.enum r).1 (x (B.enum r)) := by
    symm
    simpa [B, ξ, S, rS, distinctFiniteSetSortList] using
      FixedBlockEnumeration.ofSegmentSort_graphPoint_eq_get
        (X := X) x K rS
  simpa [B] using hleast_congr.trans (hleast_tail.trans hpoint)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: second half of `M_{C,\pi,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: once the selected graph point is identified as the
least-index value-minimal point of the current remainder, every remaining
lower-index candidate has a strictly lower-valued witness in the same
remainder.

Lean strategy / thesis relation note: this packages the thesis's value-minimal/tie-breaking
argument for later use with constructed segment sorters.
-/
theorem FixedBlockEnumeration.least_index_witness_of_leastIndexValueMinimal
    [Preorder X] {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    (x : Fin n → X) (r : Fin B.length)
    (hsel :
      leastIndexValueMinimal (X := X)
          (B.remainingGraphFinset (X := X) x r)
          (FixedBlockEnumeration.remainingGraphFinset_nonempty
            (B := B) hcov hinj x r) =
        IndexAugmented.mk (B.enum r).1 (x (B.enum r))) :
    ∀ i : Fin n, i ∈ fixedBlockRemaining B.block B.enum r →
      i < B.enum r →
        ∃ j : Fin n, j ∈ fixedBlockRemaining B.block B.enum r ∧
          x j < x i := by
  classical
  intro i hiR hi_lt
  let R : Finset (IndexAugmented X) :=
    B.remainingGraphFinset (X := X) x r
  let p : IndexAugmented X := IndexAugmented.mk i.1 (x i)
  have hpR : p ∈ R := by
    change p ∈ B.remainingGraphFinset (X := X) x r
    rw [FixedBlockEnumeration.mem_remainingGraphFinset_iff]
    exact ⟨i, hiR, rfl⟩
  have hidx :
      IndexAugmented.index p <
        IndexAugmented.index
          (leastIndexValueMinimal (X := X) R
            (FixedBlockEnumeration.remainingGraphFinset_nonempty
              (B := B) hcov hinj x r)) := by
    simpa [R, p, hsel] using hi_lt
  rcases exists_lower_value_of_index_lt_leastIndexValueMinimal
      (X := X)
      (FixedBlockEnumeration.remainingGraphFinset_nonempty
        (B := B) hcov hinj x r)
      hpR hidx with
    ⟨q, hqR, hq_lt⟩
  rcases (FixedBlockEnumeration.mem_remainingGraphFinset_iff
      (X := X) B x r).mp (by simpa [R] using hqR) with
    ⟨j, hjR, hq⟩
  refine ⟨j, hjR, ?_⟩
  simpa [p, hq] using hq_lt

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: stage cell `M_{C,\pi,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: a block enumeration satisfies the stage cell whenever
its graph list is value-sorted through stage `r` and its selected graph point
is the least-index value-minimal point of the current remainder.

Lean strategy / thesis relation note: this combines the two defining clauses of `M_{C,\pi,r}` that
the thesis proves from recursive minimal selection.
-/
theorem FixedBlockEnumeration.mem_fixedBlockStepCell_of_pairwise_graphList_leastIndexValueMinimal
    [Preorder X] {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    {x : Fin n → X}
    (hpair :
      List.Pairwise (fun p q : IndexAugmented X =>
        ¬ IndexAugmented.value q < IndexAugmented.value p)
        (B.graphList (X := X) x))
    (r : Fin B.length)
    (hsel :
      leastIndexValueMinimal (X := X)
          (B.remainingGraphFinset (X := X) x r)
          (FixedBlockEnumeration.remainingGraphFinset_nonempty
            (B := B) hcov hinj x r) =
        IndexAugmented.mk (B.enum r).1 (x (B.enum r))) :
    x ∈ fixedBlockStepCell (X := X) B.block B.enum r := by
  constructor
  · exact FixedBlockEnumeration.no_strict_lower_of_pairwise_graphList
      (B := B) hcov hinj x hpair r
  · exact FixedBlockEnumeration.least_index_witness_of_leastIndexValueMinimal
      (B := B) hcov hinj x r hsel

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: stage cell `M_{C_k,\pi_k,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: the block enumeration constructed from a connected
segment satisfies the `r`th stage cell condition.

Lean strategy / thesis relation note: this combines the recursive selector equality with the
pairwise no-later-smaller property of the recursive finite-set sort list.
-/
theorem FixedBlockEnumeration.ofSegmentSort_mem_fixedBlockStepCell
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X))
    (r : Fin (FixedBlockEnumeration.ofSegmentSort (X := X) x K).length) :
    x ∈ fixedBlockStepCell (X := X)
      (FixedBlockEnumeration.ofSegmentSort (X := X) x K).block
      (FixedBlockEnumeration.ofSegmentSort (X := X) x K).enum r := by
  classical
  let B : FixedBlockEnumeration n :=
    FixedBlockEnumeration.ofSegmentSort (X := X) x K
  have hcov : B.CoversBlock := by
    simpa [B] using FixedBlockEnumeration.ofSegmentSort_coversBlock
      (X := X) x K
  have hinj : B.InjectiveEnumeration := by
    simpa [B] using FixedBlockEnumeration.ofSegmentSort_injectiveEnumeration
      (X := X) x K
  have hpairSort :
      List.Pairwise (fun p q : IndexAugmented X =>
        ¬ IndexAugmented.value q < IndexAugmented.value p)
        (distinctFiniteSetSortList (X := X)
          (segmentDistinctFiniteSet (X := X)
            (Sigma.mk n x : Tuple X) K)) := by
    simpa [distinctFiniteSetSortList] using
      pairwise_no_later_lt_distinctFiniteSetSortListAux
        (X := X)
        (toFinset
          (segmentDistinctFiniteSet (X := X)
            (Sigma.mk n x : Tuple X) K).1)
  have hpair :
      List.Pairwise (fun p q : IndexAugmented X =>
        ¬ IndexAugmented.value q < IndexAugmented.value p)
        (B.graphList (X := X) x) := by
    simpa [B, FixedBlockEnumeration.ofSegmentSort_graphList_eq_sortList
      (X := X) x K] using hpairSort
  have hsel :
      leastIndexValueMinimal (X := X)
          (B.remainingGraphFinset (X := X) x r)
          (FixedBlockEnumeration.remainingGraphFinset_nonempty
            (B := B) hcov hinj x r) =
        IndexAugmented.mk (B.enum r).1 (x (B.enum r)) := by
    simpa [B] using
      FixedBlockEnumeration.ofSegmentSort_leastIndexValueMinimal_remainingGraphFinset_eq
        (X := X) x K r
  simpa [B] using
    FixedBlockEnumeration.mem_fixedBlockStepCell_of_pairwise_graphList_leastIndexValueMinimal
      (B := B) hcov hinj hpair r hsel

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block-permutation cell `B_{C_k,\pi_k}` in
`thm:minimal-sorting-measurable`.

Informal statement: the original tuple lies in the block-permutation cell
attached to the connected-segment enumeration constructed from that tuple.

Lean strategy / thesis relation note: Lean expands `B_{C,\pi}` as an indexed intersection over all
finite stages `r`.
-/
theorem FixedBlockEnumeration.ofSegmentSort_mem_cell
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (K : ConnectedSegment (Sigma.mk n x : Tuple X)) :
    x ∈ fixedBlockEnumerationCell (X := X)
      (FixedBlockEnumeration.ofSegmentSort (X := X) x K) := by
  rw [fixedBlockEnumerationCell, fixedBlockPermutationCell]
  exact Set.mem_iInter.mpr fun r =>
    FixedBlockEnumeration.ofSegmentSort_mem_fixedBlockStepCell
      (X := X) x K r

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized refined cell
`\mathscr{E}(P,\pi_1,\dots,\pi_m)` in
`thm:minimal-sorting-measurable`.

Informal statement: the tuple that determines a refined branch belongs to
that branch's refined cell: it has the chosen connectivity pattern and each
connected-segment enumeration satisfies the corresponding block-permutation
cell.

Lean strategy / thesis relation note: this is the reverse direction of the earlier cell-local
recursion theorem. The thesis phrases it as choosing the partition `P` and
permutations `π_k` associated with the tuple; Lean materializes that choice
as `FixedMinimalSortingBranch.ofTuple`.
-/
theorem FixedMinimalSortingBranch.mem_cell_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    x ∈ (FixedMinimalSortingBranch.ofTuple (X := X) x).cell (X := X) := by
  classical
  rw [FixedMinimalSortingBranch.cell, fixedMinimalSortingRefinedCell]
  refine ⟨?_, ?_⟩
  · exact FixedMinimalSortingBranch.mem_connectivityPatternCell_ofTuple
      (X := X) x
  · rw [mem_fixedBlockEnumerationCells_iff_forall]
    intro B hB
    change B ∈ FixedMinimalSortingBranch.blocksOfTuple (X := X) x at hB
    rw [FixedMinimalSortingBranch.blocksOfTuple, List.mem_map] at hB
    rcases hB with ⟨K, _hK, rfl⟩
    exact FixedBlockEnumeration.ofSegmentSort_mem_cell (X := X) x K

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: recursive-removal step for `C^{(r)}` in
`thm:minimal-sorting-measurable`.

Informal statement: deleting the current graph point from the stage-`r`
remaining graph finset gives the stage-`r+1` remaining graph finset.

Lean strategy / thesis relation note: this is the formal version of the thesis update
`C^{(r+1)} = C^{(r)} \ {π(r)}`. Lean has to split the finite-index case
`s < r+1` into `s < r` or `s = r`.
-/
theorem FixedBlockEnumeration.remainingGraphFinset_erase_eq_next
    {X : Type u} [DecidableEq X] {n : ℕ} {B : FixedBlockEnumeration n}
    (x : Fin n → X) {r : Fin B.length} (hr : r.1 + 1 < B.length) :
    (B.remainingGraphFinset (X := X) x r).erase
        (IndexAugmented.mk (B.enum r).1 (x (B.enum r))) =
      B.remainingGraphFinset (X := X) x ⟨r.1 + 1, hr⟩ := by
  classical
  ext p
  rw [Finset.mem_erase, FixedBlockEnumeration.mem_remainingGraphFinset_iff,
    FixedBlockEnumeration.mem_remainingGraphFinset_iff]
  constructor
  · rintro ⟨hpne, i, hiR, hp⟩
    refine ⟨i, ?_, hp⟩
    rw [fixedBlockRemaining, Finset.mem_filter] at hiR ⊢
    rcases hiR with ⟨hiB, hiPrev⟩
    refine ⟨hiB, ?_⟩
    intro s hs
    by_cases hsr : s < r
    · exact hiPrev s hsr
    · have hs_le : s.1 ≤ r.1 := by
        have hsNat : s.1 < r.1 + 1 := by
          exact hs
        exact Nat.lt_succ_iff.mp hsNat
      have hnot_nat : ¬ s.1 < r.1 := by
        intro hlt
        exact hsr (by simpa using hlt)
      have hval : s.1 = r.1 :=
        le_antisymm hs_le (Nat.le_of_not_gt hnot_nat)
      have hs_eq : s = r := Fin.ext hval
      subst s
      intro hEq
      subst i
      exact hpne hp
  · rintro ⟨i, hiNext, hp⟩
    refine ⟨?_, i, ?_, hp⟩
    · intro hpEq
      have hidx : i = B.enum r := by
        apply Fin.ext
        have hcong :
            IndexAugmented.index (IndexAugmented.mk i.1 (x i)) =
              IndexAugmented.index
                (IndexAugmented.mk (B.enum r).1 (x (B.enum r))) := by
          simpa using congrArg IndexAugmented.index (hp.symm.trans hpEq)
        simpa using hcong
      rw [fixedBlockRemaining, Finset.mem_filter] at hiNext
      have hrnext : r < (⟨r.1 + 1, hr⟩ : Fin B.length) := by
        exact Nat.lt_succ_self r.1
      exact hiNext.2 r hrnext hidx.symm
    · rw [fixedBlockRemaining, Finset.mem_filter] at hiNext ⊢
      rcases hiNext with ⟨hiB, hiNextPrev⟩
      refine ⟨hiB, ?_⟩
      intro s hs
      have hrnext : r < (⟨r.1 + 1, hr⟩ : Fin B.length) := by
        exact Nat.lt_succ_self r.1
      exact hiNextPrev s (lt_trans hs hrnext)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: terminal recursive-removal step for `C^{(r)}` in
`thm:minimal-sorting-measurable`.

Informal statement: at the last stage of a genuine block enumeration, deleting
the selected graph point leaves no remaining graph points.
-/
theorem FixedBlockEnumeration.remainingGraphFinset_erase_eq_empty_of_last
    {X : Type u} [DecidableEq X] {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (x : Fin n → X)
    {r : Fin B.length} (hlast : ¬ r.1 + 1 < B.length) :
    (B.remainingGraphFinset (X := X) x r).erase
        (IndexAugmented.mk (B.enum r).1 (x (B.enum r))) =
      ∅ := by
  ext p
  constructor
  · intro hpErase
    rw [Finset.mem_erase] at hpErase
    rcases hpErase with ⟨hpne, hpR⟩
    rcases (FixedBlockEnumeration.mem_remainingGraphFinset_iff
        (X := X) B x r).mp hpR with
      ⟨i, hiR, hp⟩
    have hiB : i ∈ B.block := by
      rw [fixedBlockRemaining, Finset.mem_filter] at hiR
      exact hiR.1
    rcases (hcov i).mp hiB with ⟨s, hs_i⟩
    have hs_not_lt : ¬ s < r := by
      intro hslt
      have hprev : B.enum s ≠ i := by
        rw [fixedBlockRemaining, Finset.mem_filter] at hiR
        exact hiR.2 s hslt
      exact hprev hs_i
    have hlen_le : B.length ≤ r.1 + 1 := Nat.le_of_not_gt hlast
    have hs_le_r : s.1 ≤ r.1 := by
      exact Nat.lt_succ_iff.mp (lt_of_lt_of_le s.2 hlen_le)
    have hr_le_s : r.1 ≤ s.1 := by
      apply Nat.le_of_not_gt
      intro hlt
      exact hs_not_lt (by exact hlt)
    have hs_eq : s = r := Fin.ext (le_antisymm hs_le_r hr_le_s)
    subst s
    subst i
    exact False.elim (hpne hp)
  · intro hpEmpty
    simp at hpEmpty

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: selection interpretation of `M_{C,\pi,r}` in
`thm:minimal-sorting-measurable`.

Informal statement: on a block-permutation cell, `(π(r),x_{π(r)})` is the
least-index value-minimal point of the remaining graph finset.

Lean strategy / thesis relation note: this is the recursive-selector form of the thesis explanation
following the definition of `M_{C,\pi,r}`: first no remaining point is
strictly smaller in value, then every lower-index remaining candidate fails
to be value-minimal.
-/
theorem FixedBlockEnumeration.leastIndexValueMinimal_remainingGraphFinset_eq
    [Preorder X] {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    {x : Fin n → X}
    (hx : x ∈ fixedBlockEnumerationCell (X := X) B)
    (r : Fin B.length) :
    leastIndexValueMinimal (X := X)
        (B.remainingGraphFinset (X := X) x r)
        (FixedBlockEnumeration.remainingGraphFinset_nonempty
          (B := B) hcov hinj x r) =
      IndexAugmented.mk (B.enum r).1 (x (B.enum r)) := by
  classical
  let R : Finset (IndexAugmented X) :=
    B.remainingGraphFinset (X := X) x r
  let p : IndexAugmented X := IndexAugmented.mk (B.enum r).1 (x (B.enum r))
  have hpR : p ∈ R := by
    change p ∈ B.remainingGraphFinset (X := X) x r
    rw [FixedBlockEnumeration.mem_remainingGraphFinset_iff]
    exact ⟨B.enum r,
      FixedBlockEnumeration.enum_mem_remaining_of_coversBlock_injective
        (B := B) hcov hinj r, rfl⟩
  refine leastIndexValueMinimal_eq_of_index_min
    (X := X) R
    (FixedBlockEnumeration.remainingGraphFinset_nonempty
      (B := B) hcov hinj x r)
    (p := p) ?_ ?_ ?_
  · rw [valueMinimalElements, Finset.mem_filter]
    refine ⟨hpR, ?_⟩
    intro q hq hlt
    rcases (FixedBlockEnumeration.mem_remainingGraphFinset_iff
        (X := X) B x r).mp (by simpa [R] using hq) with
      ⟨j, hjR, hq⟩
    have hno :=
      fixedBlockEnumerationCell_no_strict_lower
        (X := X) hx r j hjR
    exact hno (by simpa [p, hq] using hlt)
  · intro q hqmin
    have hqR : q ∈ R := (Finset.mem_filter.mp hqmin).1
    rcases (FixedBlockEnumeration.mem_remainingGraphFinset_iff
        (X := X) B x r).mp (by simpa [R] using hqR) with
      ⟨i, hiR, hq⟩
    by_contra hle
    have hi_lt : i < B.enum r := by
      simpa [p, hq] using Nat.lt_of_not_ge hle
    rcases fixedBlockEnumerationCell_least_index_witness
        (X := X) hx r i hiR hi_lt with
      ⟨j, hjR, hji⟩
    have hj_mem : IndexAugmented.mk j.1 (x j) ∈ R := by
      change IndexAugmented.mk j.1 (x j) ∈
        B.remainingGraphFinset (X := X) x r
      rw [FixedBlockEnumeration.mem_remainingGraphFinset_iff]
      exact ⟨j, hjR, rfl⟩
    have hq_min :=
      (Finset.mem_filter.mp hqmin).2
        (IndexAugmented.mk j.1 (x j)) hj_mem
    exact hq_min (by simpa [hq] using hji)
  · intro q hqR hqidx
    rcases (FixedBlockEnumeration.mem_remainingGraphFinset_iff
        (X := X) B x r).mp (by simpa [R] using hqR) with
      ⟨i, _hiR, hq⟩
    have hi_eq : i = B.enum r := by
      apply Fin.ext
      simpa [p, hq] using hqidx
    subst i
    simpa [p] using hq

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: one recursive step in the proof of
`thm:minimal-sorting-measurable`.

Informal statement: on a block cell `B_{C,\pi}`, unfolding the recursive
finite-set sorter at stage `r` puts `(π(r),x_{π(r)})` at the head.

Lean strategy / thesis relation note: this is the direct Lean counterpart of the thesis claim that
the block cell conditions force the minimum finite-set sorting algorithm to
choose the stored enumeration at each stage.
-/
theorem FixedBlockEnumeration.distinctFiniteSetSortListAux_remainingGraphFinset_eq_cons
    [Preorder X] [DecidableEq X] {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    {x : Fin n → X}
    (hx : x ∈ fixedBlockEnumerationCell (X := X) B)
    (r : Fin B.length) :
    distinctFiniteSetSortListAux (X := X)
        (B.remainingGraphFinset (X := X) x r) =
      IndexAugmented.mk (B.enum r).1 (x (B.enum r)) ::
        distinctFiniteSetSortListAux (X := X)
          ((B.remainingGraphFinset (X := X) x r).erase
            (IndexAugmented.mk (B.enum r).1 (x (B.enum r)))) := by
  rw [distinctFiniteSetSortListAux.eq_1]
  rw [dif_pos
    (FixedBlockEnumeration.remainingGraphFinset_nonempty
      (B := B) hcov hinj x r)]
  simp only [
    FixedBlockEnumeration.leastIndexValueMinimal_remainingGraphFinset_eq
      (B := B) hcov hinj hx r]
  apply congrArg (List.cons (IndexAugmented.mk (B.enum r).1 (x (B.enum r))))
  apply congrArg (distinctFiniteSetSortListAux (X := X))
  ext q
  simp [Finset.mem_erase]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block-level recursive agreement in
`thm:minimal-sorting-measurable`.

Informal statement: on a block cell `B_{C,\pi}`, the recursive finite-set
sorter applied to the stage-`r` remaining graph set returns exactly the suffix
of the fixed block graph list beginning at `r`.

Lean strategy / thesis relation note: this is the detailed Lean induction behind the thesis sentence
that, on the refined cell, the minimum sorting rule is represented by the
fixed block permutation `π_k`.
-/
theorem FixedBlockEnumeration.distinctFiniteSetSortListAux_remainingGraphFinset_eq_graphList_drop
    [Preorder X] {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    {x : Fin n → X}
    (hx : x ∈ fixedBlockEnumerationCell (X := X) B)
    (r : Fin B.length) :
    distinctFiniteSetSortListAux (X := X)
        (B.remainingGraphFinset (X := X) x r) =
      (B.graphList (X := X) x).drop r.1 := by
  classical
  rw [
    FixedBlockEnumeration.distinctFiniteSetSortListAux_remainingGraphFinset_eq_cons
      (B := B) hcov hinj hx r]
  by_cases hnext : r.1 + 1 < B.length
  · rw [FixedBlockEnumeration.remainingGraphFinset_erase_eq_next
      (B := B) x hnext]
    rw [
      FixedBlockEnumeration.distinctFiniteSetSortListAux_remainingGraphFinset_eq_graphList_drop
        (B := B) hcov hinj hx ⟨r.1 + 1, hnext⟩]
    rw [FixedBlockEnumeration.graphList_drop_eq_cons
      (X := X) B x (r := r) hnext]
  · rw [FixedBlockEnumeration.remainingGraphFinset_erase_eq_empty_of_last
      (B := B) hcov x hnext]
    rw [distinctFiniteSetSortListAux.eq_1]
    rw [dif_neg (by simp : ¬ (∅ : Finset (IndexAugmented X)).Nonempty)]
    rw [FixedBlockEnumeration.graphList_drop_eq_singleton_of_last
      (X := X) B x (r := r) hnext]
termination_by B.length - r.1
decreasing_by
  exact Nat.sub_succ_lt_self B.length r.1 r.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block-level fixed-map agreement in
`thm:minimal-sorting-measurable`.

Informal statement: on a block cell `B_{C,\pi}`, applying the recursive
distinct finite-set sorter to the block graph `{(i,x_i): i ∈ C}` returns
exactly the fixed graph list determined by the stored enumeration `π`.

Lean strategy / thesis relation note: this is the block-local version of the thesis statement that
the minimum sorting rule agrees with the fixed permutation
`\pi_k ∈ \Pi(C_k)` on the refined cell. The empty-block case is handled
separately because Lean has no first `Fin 0` stage.
-/
theorem FixedBlockEnumeration.distinctFiniteSetSortList_eq_graphList_of_mem_cell
    [Preorder X] {n : ℕ} {B : FixedBlockEnumeration n}
    (hcov : B.CoversBlock) (hinj : B.InjectiveEnumeration)
    {x : Fin n → X}
    (hx : x ∈ fixedBlockEnumerationCell (X := X) B) :
    distinctFiniteSetSortList (X := X)
        (B.distinctFiniteSet (X := X) x) =
      B.graphList (X := X) x := by
  classical
  by_cases hpos : 0 < B.length
  · unfold distinctFiniteSetSortList
    rw [← FixedBlockEnumeration.remainingGraphFinset_zero_eq_toFinset
      (B := B) x hpos]
    simpa using
      FixedBlockEnumeration.distinctFiniteSetSortListAux_remainingGraphFinset_eq_graphList_drop
        (B := B) hcov hinj hx ⟨0, hpos⟩
  · have hlen0 : B.length = 0 := Nat.eq_zero_of_not_pos hpos
    have hfinempty :
        toFinset (B.distinctFiniteSet (X := X) x).1 = ∅ := by
      ext p
      rw [mem_toFinset, FixedBlockEnumeration.mem_distinctFiniteSet_iff]
      constructor
      · rintro ⟨i, hiB, _hp⟩
        rcases (hcov i).mp hiB with ⟨r, _hr⟩
        exact False.elim (Fin.elim0 (Fin.cast hlen0 r))
      · intro hp
        simp at hp
    have hsort_empty :
        distinctFiniteSetSortListAux (X := X)
            (toFinset (B.distinctFiniteSet (X := X) x).1) = [] := by
      rw [hfinempty]
      rw [distinctFiniteSetSortListAux.eq_1]
      rw [dif_neg (by simp : ¬ (∅ : Finset (IndexAugmented X)).Nonempty)]
    have hgraph_empty : B.graphList (X := X) x = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [FixedBlockEnumeration.length_graphList, hlen0]
    rw [distinctFiniteSetSortList, hsort_empty, hgraph_empty]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: value projection of one fixed block.

Informal statement: the values of the fixed block graph list are exactly the
tuple values read along the block enumeration.
-/
@[simp]
theorem FixedBlockEnumeration.graphList_map_value
    {X : Type u} {n : ℕ} (B : FixedBlockEnumeration n)
    (x : Fin n → X) :
    (B.graphList (X := X) x).map IndexAugmented.value =
      B.indexList.map fun i => x i := by
  simp [FixedBlockEnumeration.graphList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: branch-level fixed-map agreement in
`thm:minimal-sorting-measurable`.

Informal statement: if a list of connected segments and a list of stored
block enumerations have the same index blocks in the same order, then sorting
each segment's finite graph set gives the stored block graph list.

Lean strategy / thesis relation note: this is the finite-list induction hidden in the thesis'
notation `\pi_1 \oplus \dots \oplus \pi_m`: each block is handled by the
block-local recursion theorem, and the list induction concatenates those
agreements without changing the thesis order.
-/
theorem minimumSortGraphBlocks_eq_fixedGraphBlocks_of_segmentBlocks_eq
    [Preorder X] {n : ℕ} (x : Fin n → X)
    (segments : List (ConnectedSegment (Sigma.mk n x : Tuple X)))
    (blocks : List (FixedBlockEnumeration n))
    (hmatch :
      (segments.map fun K =>
        segmentIndices (Sigma.mk n x : Tuple X) K) =
        blocks.map fun B => (B.block : Set (Fin n)))
    (hcell : ∀ B ∈ blocks, x ∈ fixedBlockEnumerationCell (X := X) B)
    (hcov : ∀ B ∈ blocks, B.CoversBlock)
    (hinj : ∀ B ∈ blocks, B.InjectiveEnumeration) :
    (segments.map fun K =>
      distinctFiniteSetSortList (X := X)
        (segmentDistinctFiniteSet (X := X)
          (Sigma.mk n x : Tuple X) K)) =
      blocks.map fun B => B.graphList (X := X) x := by
  induction segments generalizing blocks with
  | nil =>
      cases blocks with
      | nil =>
          simp
      | cons B Bs =>
          simp at hmatch
  | cons K Ks ih =>
      cases blocks with
      | nil =>
          simp at hmatch
      | cons B Bs =>
          simp only [List.map_cons] at hmatch ⊢
          injection hmatch with hhead htail
          have hset :
              segmentDistinctFiniteSet (X := X)
                  (Sigma.mk n x : Tuple X) K =
                B.distinctFiniteSet (X := X) x :=
            FixedBlockEnumeration.segmentDistinctFiniteSet_eq_distinctFiniteSet
              (X := X) B x K hhead
          have hhead_sort :
              distinctFiniteSetSortList (X := X)
                  (segmentDistinctFiniteSet (X := X)
                    (Sigma.mk n x : Tuple X) K) =
                B.graphList (X := X) x := by
            rw [hset]
            exact
              FixedBlockEnumeration.distinctFiniteSetSortList_eq_graphList_of_mem_cell
                (X := X) (B := B) (hcov B (by simp))
                (hinj B (by simp)) (hcell B (by simp))
          rw [hhead_sort]
          exact congrArg (List.cons (B.graphList (X := X) x))
            (ih Bs htail
              (by
                intro C hC
                exact hcell C (by simp [hC]))
              (by
                intro C hC
                exact hcov C (by simp [hC]))
              (by
                intro C hC
                exact hinj C (by simp [hC])))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: graph-list form of
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: concatenate the fixed graph lists of all branch blocks.
-/
def fixedBlockEnumerationsGraphList {X : Type u} {n : ℕ}
    (blocks : List (FixedBlockEnumeration n)) (x : Fin n → X) :
    List (IndexAugmented X) :=
  (blocks.map fun B => B.graphList (X := X) x).flatten

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: graph-list compatibility for
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: concatenating the block graph lists is the same as
reading the concatenated branch index list.
-/
theorem fixedBlockEnumerationsGraphList_eq_fixedIndexGraphList
    {X : Type u} {n : ℕ} (blocks : List (FixedBlockEnumeration n))
    (x : Fin n → X) :
    fixedBlockEnumerationsGraphList (X := X) blocks x =
      fixedIndexGraphList (X := X)
        (fixedBlockEnumerationsIndexList blocks) x := by
  induction blocks with
  | nil =>
      simp [fixedBlockEnumerationsGraphList, fixedBlockEnumerationsIndexList,
        fixedIndexGraphList]
  | cons B Bs ih =>
      simp [fixedBlockEnumerationsGraphList, fixedBlockEnumerationsIndexList,
        FixedBlockEnumeration.graphList, fixedIndexGraphList, Function.comp_def]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: value-list compatibility for the fixed branch map.

Informal statement: the value projection of the concatenated branch graph
list is the same value list read by the fixed branch index list.
-/
theorem fixedBlockEnumerationsGraphList_map_value
    {X : Type u} {n : ℕ} (blocks : List (FixedBlockEnumeration n))
    (x : Fin n → X) :
    (fixedBlockEnumerationsGraphList (X := X) blocks x).map
        IndexAugmented.value =
      (fixedBlockEnumerationsIndexList blocks).map fun i => x i := by
  rw [fixedBlockEnumerationsGraphList_eq_fixedIndexGraphList]
  simp

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized branch agreement in
`thm:minimal-sorting-measurable`.

Informal statement: for the branch constructed from a tuple, the minimum-sort
graph blocks are exactly the fixed graph lists attached to the constructed
block enumerations.

Lean strategy / thesis relation note: this is the tuple-realized version of the thesis statement
that, on a refined cell, the sorting map is represented by
`\pi_1 \oplus \dots \oplus \pi_m`. It uses the constructed `π_k` directly,
before proving the whole cell membership/cover theorem.
-/
theorem FixedMinimalSortingBranch.minimumSortGraphBlocks_eq_graphLists_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    minimumSortGraphBlocks (X := X) (Sigma.mk n x : Tuple X) =
      (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks.map
        fun B => B.graphList (X := X) x := by
  simp [minimumSortGraphBlocks,
    FixedMinimalSortingBranch.ofTuple,
    FixedMinimalSortingBranch.blocksOfTuple,
    FixedBlockEnumeration.ofSegmentSort_graphList_eq_sortList]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized branch agreement in
`thm:minimal-sorting-measurable`.

Informal statement: for the branch constructed from a tuple, the full
minimum-sort graph list is the concatenated fixed branch graph list.
-/
theorem FixedMinimalSortingBranch.minimumSortGraphList_eq_graphList_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    minimumSortGraphList (X := X) (Sigma.mk n x : Tuple X) =
      fixedBlockEnumerationsGraphList (X := X)
        (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks x := by
  unfold minimumSortGraphList fixedBlockEnumerationsGraphList
  rw [
    FixedMinimalSortingBranch.minimumSortGraphBlocks_eq_graphLists_ofTuple
      (X := X) x]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized branch agreement in
`thm:minimal-sorting-measurable`.

Informal statement: for the branch constructed from a tuple, the minimum-sort
value list is exactly the value list read along the branch's concatenated
index enumeration.
-/
theorem FixedMinimalSortingBranch.minimumSortList_eq_indexList_map_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    minimumSortList (X := X) (Sigma.mk n x : Tuple X) =
      (fixedBlockEnumerationsIndexList
        (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks).map
          fun i => x i := by
  calc
    minimumSortList (X := X) (Sigma.mk n x : Tuple X) =
        (minimumSortGraphList (X := X)
          (Sigma.mk n x : Tuple X)).map IndexAugmented.value :=
      minimumSortList_eq_map_value (X := X) (Sigma.mk n x : Tuple X)
    _ =
        (fixedBlockEnumerationsGraphList (X := X)
          (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks x).map
          IndexAugmented.value := by
      rw [
        FixedMinimalSortingBranch.minimumSortGraphList_eq_graphList_ofTuple
          (X := X) x]
    _ =
        (fixedBlockEnumerationsIndexList
          (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks).map
          fun i => x i :=
      fixedBlockEnumerationsGraphList_map_value
        (X := X) (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized branch agreement in
`thm:minimal-sorting-measurable`.

Informal statement: for the branch constructed from a tuple, `minimumSort`
agrees with the fixed map induced by that branch's concatenated enumeration.
-/
theorem FixedMinimalSortingBranch.minimumSort_eq_map_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    minimumSort (X := X) (Sigma.mk n x : Tuple X) =
      (FixedMinimalSortingBranch.ofTuple (X := X) x).map (X := X) x := by
  have hlist :
      minimumSortList (X := X) (Sigma.mk n x : Tuple X) =
        (fixedBlockEnumerationsIndexList
          (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks).map
          fun i => x i :=
    FixedMinimalSortingBranch.minimumSortList_eq_indexList_map_ofTuple
      (X := X) x
  calc
    minimumSort (X := X) (Sigma.mk n x : Tuple X) =
        tupleOfList (X := X)
          ((fixedBlockEnumerationsIndexList
            (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks).map
            fun i => x i) := by
      simpa [minimumSort] using congrArg (tupleOfList (X := X)) hlist
    _ = (FixedMinimalSortingBranch.ofTuple (X := X) x).map (X := X) x := by
      simpa [FixedMinimalSortingBranch.map] using
        (fixedIndexListMap_eq_tupleOfList
          (X := X)
          (fixedBlockEnumerationsIndexList
            (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks) x).symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: covering step in `thm:minimal-sorting-measurable`.

Informal statement: every fixed-length tuple determines a refined branch
cell containing it, that branch has the thesis' first-arrival block order for
the tuple, and `minimumSort` agrees there with the fixed branch map.

Lean strategy / thesis relation note: the thesis says to take the tuple's connected-index
partition `P` and the blockwise minimum permutations `π_k`. Lean expresses
that choice by the canonical constructor `FixedMinimalSortingBranch.ofTuple`.
-/
theorem FixedMinimalSortingBranch.exists_mem_cell_blocksMatch_minimumSort_eq_map
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    ∃ branch : FixedMinimalSortingBranch n,
      x ∈ branch.cell (X := X) ∧
        branch.blocksMatchSegmentArrival (X := X) x ∧
          minimumSort (X := X) (Sigma.mk n x : Tuple X) =
            branch.map (X := X) x := by
  refine ⟨FixedMinimalSortingBranch.ofTuple (X := X) x, ?_, ?_, ?_⟩
  · exact FixedMinimalSortingBranch.mem_cell_ofTuple (X := X) x
  · exact FixedMinimalSortingBranch.ofTuple_blocksMatchSegmentArrival
      (X := X) x
  · exact FixedMinimalSortingBranch.minimumSort_eq_map_ofTuple (X := X) x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: covering step in `thm:minimal-sorting-measurable`.

Informal statement: the refined branch cells cover the fixed-length tuple
space.

Lean strategy / thesis relation note: this is the non-finitary cover obtained from the canonical
tuple-dependent branch. The thesis next uses the fact that, for fixed `n`,
only finitely many combinatorial branch data can occur; that finite
enumeration is tracked separately.
-/
theorem FixedMinimalSortingBranch.iUnion_cell_eq_univ
    [Preorder X] {n : ℕ} :
    (⋃ branch : FixedMinimalSortingBranch n, branch.cell (X := X)) =
      Set.univ := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    exact Set.mem_iUnion.2
      ⟨FixedMinimalSortingBranch.ofTuple (X := X) x,
        FixedMinimalSortingBranch.mem_cell_ofTuple (X := X) x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ordered covering step in
`thm:minimal-sorting-measurable`.

Informal statement: the tuple that realizes a branch belongs to the
arrival-ordered refinement of that branch cell.
-/
theorem FixedMinimalSortingBranch.mem_arrivalRefinedCell_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    x ∈ (FixedMinimalSortingBranch.ofTuple (X := X) x).arrivalRefinedCell
      (X := X) := by
  exact ⟨FixedMinimalSortingBranch.mem_cell_ofTuple (X := X) x,
    FixedMinimalSortingBranch.ofTuple_blocksMatchSegmentArrival (X := X) x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: nonempty partition blocks in
`thm:minimal-sorting-measurable`.

Informal statement: if a branch's listed blocks agree with the connected
segments of some tuple in first-arrival order, then all branch blocks are
nonempty.

Lean strategy / thesis relation note: this is the type-theoretic bookkeeping behind the thesis'
phrase "partition blocks": equality of the branch block list with the list
of connected-segment index sets transfers nonemptiness from connected
segments to the branch data.
-/
theorem FixedMinimalSortingBranch.noEmptyBlocks_of_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X}
    (hmatch : branch.blocksMatchSegmentArrival (X := X) x) :
    branch.NoEmptyBlocks := by
  classical
  let y : Tuple X := Sigma.mk n x
  intro B hB
  have hBmem :
      (B.block : Set (Fin n)) ∈
        branch.blocks.map fun B => (B.block : Set (Fin n)) :=
    List.mem_map.mpr ⟨B, hB, rfl⟩
  have hSegMem :
      (B.block : Set (Fin n)) ∈
        (segmentListByArrival (X := X) y).map
          (fun K => segmentIndices y K) := by
    simpa [FixedMinimalSortingBranch.blocksMatchSegmentArrival, y] using
      show
        (B.block : Set (Fin n)) ∈
          (segmentListByArrival (X := X) (Sigma.mk n x : Tuple X)).map
            (fun K => segmentIndices (Sigma.mk n x : Tuple X) K)
        from by
          rw [hmatch]
          exact hBmem
  rcases List.mem_map.mp hSegMem with ⟨K, _hKmem, hKset⟩
  rcases segmentIndexFinset_nonempty (X := X) y K with ⟨i, hiKfin⟩
  refine ⟨i, ?_⟩
  have hiKset : i ∈ segmentIndices y K := by
    simpa [segmentIndexFinset, segmentIndices] using hiKfin
  have hiBset : i ∈ (B.block : Set (Fin n)) := by
    simpa [hKset] using hiKset
  simpa using hiBset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized branch normalization in
`thm:minimal-sorting-measurable`.

Informal statement: every branch with a witness in its arrival-refined cell
has nonempty blocks.
-/
theorem FixedMinimalSortingBranch.noEmptyBlocks_of_mem_arrivalRefinedCell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X}
    (hx : x ∈ branch.arrivalRefinedCell (X := X)) :
    branch.NoEmptyBlocks :=
  FixedMinimalSortingBranch.noEmptyBlocks_of_blocksMatchSegmentArrival
    (X := X) branch hx.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized branch normalization in
`thm:minimal-sorting-measurable`.

Informal statement: the branch constructed from a tuple has no empty blocks.
-/
theorem FixedMinimalSortingBranch.ofTuple_noEmptyBlocks
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    (FixedMinimalSortingBranch.ofTuple (X := X) x).NoEmptyBlocks :=
  FixedMinimalSortingBranch.noEmptyBlocks_of_mem_arrivalRefinedCell
    (X := X) (FixedMinimalSortingBranch.ofTuple (X := X) x)
    (FixedMinimalSortingBranch.mem_arrivalRefinedCell_ofTuple (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ordered covering step in
`thm:minimal-sorting-measurable`.

Informal statement: the arrival-ordered refined branch cells cover the
fixed-length tuple space.

Lean strategy / thesis relation note: this cover now includes the ordering condition needed for the
thesis pasted-map equality. Proving the finite enumeration of these ordered
combinatorial cells is the remaining fixed-length cover task.
-/
theorem FixedMinimalSortingBranch.iUnion_arrivalRefinedCell_eq_univ
    [Preorder X] {n : ℕ} :
    (⋃ branch : FixedMinimalSortingBranch n,
        branch.arrivalRefinedCell (X := X)) = Set.univ := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    exact Set.mem_iUnion.2
      ⟨FixedMinimalSortingBranch.ofTuple (X := X) x,
        FixedMinimalSortingBranch.mem_arrivalRefinedCell_ofTuple
          (X := X) x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ordered-partition invariance in
`thm:minimal-sorting-measurable`.

Informal statement: if two fixed-length tuples have the same connected-index
relation, then their connected-segment index sets, listed by first arrival,
are the same list.

Lean strategy / thesis relation note: the segment quotient types for the two tuples are not the
same Lean type. Mapping each segment to its concrete index set gives a
common `Set (Fin n)` codomain, which is the thesis' partition data.
-/
theorem segmentSetListByArrival_eq_of_same_connectedRelation
    [Preorder X] {n : ℕ} {x y : Fin n → X}
    (hxy : ∀ i j : Fin n,
      IndexConnected (Sigma.mk n x : Tuple X) i j ↔
        IndexConnected (Sigma.mk n y : Tuple X) i j) :
    ((segmentListByArrival (X := X) (Sigma.mk n x : Tuple X)).map fun K =>
        segmentIndices (Sigma.mk n x : Tuple X) K) =
      ((segmentListByArrival (X := X) (Sigma.mk n y : Tuple X)).map fun K =>
        segmentIndices (Sigma.mk n y : Tuple X) K) := by
  rw [
    map_segmentIndices_segmentListByArrival_eq_firstOccurrenceList_connectedSets
      (X := X) (Sigma.mk n x : Tuple X),
    map_segmentIndices_segmentListByArrival_eq_firstOccurrenceList_connectedSets
      (X := X) (Sigma.mk n y : Tuple X)]
  apply congrArg firstOccurrenceList
  apply List.map_congr_left
  intro i _hi
  ext j
  exact hxy i j

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ordered refined cells in
`thm:minimal-sorting-measurable`.

Informal statement: first-arrival block order is constant on a fixed branch
cell once it holds for one tuple in that cell.

Lean strategy / thesis relation note: this is the formal version of the thesis convention that the
ordered partition `(C_1,\dots,C_m)` is combinatorial data, not a numerical
feature of the particular tuple values inside the same connectivity-pattern
cell.
-/
theorem FixedMinimalSortingBranch.blocksMatchSegmentArrival_of_mem_cell_of_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x y : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (hy : y ∈ branch.cell (X := X))
    (harrival : branch.blocksMatchSegmentArrival (X := X) x) :
    branch.blocksMatchSegmentArrival (X := X) y := by
  have hxy : ∀ i j : Fin n,
      IndexConnected (Sigma.mk n x : Tuple X) i j ↔
        IndexConnected (Sigma.mk n y : Tuple X) i j := by
    intro i j
    exact (hx.1 i j).trans (hy.1 i j).symm
  rw [FixedMinimalSortingBranch.blocksMatchSegmentArrival] at harrival ⊢
  exact
    (segmentSetListByArrival_eq_of_same_connectedRelation
      (X := X) (x := y) (y := x) fun i j => (hxy i j).symm).trans
      harrival

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ordered refined cells in
`thm:minimal-sorting-measurable`.

Informal statement: if one point of a branch cell verifies the first-arrival
ordering convention, then every point of that branch cell verifies it.
-/
theorem FixedMinimalSortingBranch.arrivalRefinedCell_eq_cell_of_mem
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.arrivalRefinedCell (X := X)) :
    branch.arrivalRefinedCell (X := X) = branch.cell (X := X) := by
  ext y
  constructor
  · intro hy
    exact hy.1
  · intro hy
    exact ⟨hy,
      FixedMinimalSortingBranch.blocksMatchSegmentArrival_of_mem_cell_of_blocksMatchSegmentArrival
        (X := X) branch hx.1 hy hx.2⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: tuple-realized ordered refined cell in
`thm:minimal-sorting-measurable`.

Informal statement: for the branch constructed from a tuple, the
arrival-refined cell and the underlying refined branch cell coincide.
-/
theorem FixedMinimalSortingBranch.ofTuple_arrivalRefinedCell_eq_cell
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    (FixedMinimalSortingBranch.ofTuple (X := X) x).arrivalRefinedCell
        (X := X) =
      (FixedMinimalSortingBranch.ofTuple (X := X) x).cell (X := X) := by
  exact
    FixedMinimalSortingBranch.arrivalRefinedCell_eq_cell_of_mem
      (X := X) (FixedMinimalSortingBranch.ofTuple (X := X) x)
      (FixedMinimalSortingBranch.mem_arrivalRefinedCell_ofTuple
        (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: tuple-realized ordered refined cell in
`thm:minimal-sorting-measurable`.

Informal statement: every tuple in the cell of a tuple-realized branch sees
the branch blocks in first-arrival order.
-/
theorem FixedMinimalSortingBranch.ofTuple_blocksMatchSegmentArrival_of_mem_cell
    [Preorder X] {n : ℕ} (x : Fin n → X)
    {y : Fin n → X}
    (hy : y ∈ (FixedMinimalSortingBranch.ofTuple (X := X) x).cell
      (X := X)) :
    (FixedMinimalSortingBranch.ofTuple (X := X) x).blocksMatchSegmentArrival
      (X := X) y := by
  have hcell :
      y ∈ (FixedMinimalSortingBranch.ofTuple (X := X) x).arrivalRefinedCell
        (X := X) := by
    rwa [FixedMinimalSortingBranch.ofTuple_arrivalRefinedCell_eq_cell
      (X := X) x]
  exact hcell.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: connectivity-pattern component `\mathscr{E}(P)` in
`thm:minimal-sorting-measurable`.

Informal statement: on a fixed branch cell, Lean's connectivity relation is
exactly the branch relation representing the partition `P`.
-/
theorem FixedMinimalSortingBranch.indexConnected_iff_relation_of_mem_cell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (i j : Fin n) :
    IndexConnected (Sigma.mk n x : Tuple X) i j ↔
      branch.relation i j := by
  have hxPattern :
      x ∈ fixedConnectivityPatternCell (X := X) n branch.relation := by
    exact hx.1
  exact hxPattern i j

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: "the connected segments are fixed" in
`thm:minimal-sorting-measurable`.

Informal statement: on a fixed branch cell, two indices are connected
exactly when they lie in the same listed block.
-/
theorem FixedMinimalSortingBranch.indexConnected_iff_same_block_of_mem_cell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (i j : Fin n) :
    IndexConnected (Sigma.mk n x : Tuple X) i j ↔
      ∃ B ∈ branch.blocks, i ∈ B.block ∧ j ∈ B.block := by
  exact
    (FixedMinimalSortingBranch.indexConnected_iff_relation_of_mem_cell
      (X := X) branch hx i j).trans (branch.blockRelation i j)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: block component of
`\mathscr{E}(P,\pi_1,\dots,\pi_m)`.

Informal statement: on a fixed branch cell, every listed block enumeration is
in its block-permutation cell.
-/
theorem FixedMinimalSortingBranch.mem_blockEnumerationCell_of_mem_cell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    {B : FixedBlockEnumeration n} (hB : B ∈ branch.blocks) :
    x ∈ fixedBlockEnumerationCell (X := X) B := by
  have hxBlocks :
      x ∈ fixedBlockEnumerationCells (X := X) branch.blocks := by
    exact hx.2
  exact (mem_fixedBlockEnumerationCells_iff_forall
    (X := X) (blocks := branch.blocks)).mp hxBlocks B hB

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: "within each segment, the minimal sorting permutation is
fixed" in `thm:minimal-sorting-measurable`.

Informal statement: on a fixed branch cell, every stage of every listed block
enumeration satisfies the corresponding minimum-selection step cell.
-/
theorem FixedMinimalSortingBranch.mem_blockStepCell_of_mem_cell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    {B : FixedBlockEnumeration n} (hB : B ∈ branch.blocks)
    (r : Fin B.length) :
    x ∈ fixedBlockStepCell (X := X) B.block B.enum r := by
  exact mem_fixedBlockPermutationCell_step
    (X := X)
    (FixedMinimalSortingBranch.mem_blockEnumerationCell_of_mem_cell
      (X := X) branch hx hB) r

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: branch-level fixed-map agreement in
`thm:minimal-sorting-measurable`.

Informal statement: on a refined branch cell whose blocks are listed in the
same first-arrival order as the tuple's connected segments, the graph blocks
used by Lean's `minimumSort` are exactly the stored fixed block graph lists.

Lean strategy / thesis relation note: this is the first place where Lean makes explicit a thesis
convention: the partition blocks used for pasting fixed maps must be ordered
by first arrival of their connected segments.
-/
theorem FixedMinimalSortingBranch.minimumSortGraphBlocks_eq_graphLists_of_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (harrival : branch.blocksMatchSegmentArrival (X := X) x) :
    minimumSortGraphBlocks (X := X) (Sigma.mk n x : Tuple X) =
      branch.blocks.map fun B => B.graphList (X := X) x := by
  unfold minimumSortGraphBlocks
  exact
    minimumSortGraphBlocks_eq_fixedGraphBlocks_of_segmentBlocks_eq
      (X := X) x (segmentListByArrival (X := X)
        (Sigma.mk n x : Tuple X)) branch.blocks
      (by
        simpa [FixedMinimalSortingBranch.blocksMatchSegmentArrival]
          using harrival)
      (by
        intro B hB
        exact FixedMinimalSortingBranch.mem_blockEnumerationCell_of_mem_cell
          (X := X) branch hx hB)
      branch.coversBlock branch.injectiveEnumeration

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: graph-list fixed-map agreement in
`thm:minimal-sorting-measurable`.

Informal statement: under the same branch-order hypothesis, the full
minimum-sort graph list is the concatenated graph list
`\pi_1 \oplus \dots \oplus \pi_m`.
-/
theorem FixedMinimalSortingBranch.minimumSortGraphList_eq_graphList_of_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (harrival : branch.blocksMatchSegmentArrival (X := X) x) :
    minimumSortGraphList (X := X) (Sigma.mk n x : Tuple X) =
      fixedBlockEnumerationsGraphList (X := X) branch.blocks x := by
  unfold minimumSortGraphList fixedBlockEnumerationsGraphList
  rw [
    FixedMinimalSortingBranch.minimumSortGraphBlocks_eq_graphLists_of_blocksMatchSegmentArrival
      (X := X) branch hx harrival]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: value-list fixed-map agreement in
`thm:minimal-sorting-measurable`.

Informal statement: after projecting away original indices, the minimum-sort
value list is the value list read by the concatenated branch enumeration.
-/
theorem FixedMinimalSortingBranch.minimumSortList_eq_indexList_map_of_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (harrival : branch.blocksMatchSegmentArrival (X := X) x) :
    minimumSortList (X := X) (Sigma.mk n x : Tuple X) =
      (fixedBlockEnumerationsIndexList branch.blocks).map fun i => x i := by
  calc
    minimumSortList (X := X) (Sigma.mk n x : Tuple X) =
        (minimumSortGraphList (X := X)
          (Sigma.mk n x : Tuple X)).map IndexAugmented.value :=
      minimumSortList_eq_map_value (X := X) (Sigma.mk n x : Tuple X)
    _ =
        (fixedBlockEnumerationsGraphList (X := X) branch.blocks x).map
          IndexAugmented.value := by
      rw [
        FixedMinimalSortingBranch.minimumSortGraphList_eq_graphList_of_blocksMatchSegmentArrival
          (X := X) branch hx harrival]
    _ = (fixedBlockEnumerationsIndexList branch.blocks).map fun i => x i :=
      fixedBlockEnumerationsGraphList_map_value (X := X) branch.blocks x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed-map agreement in `thm:minimal-sorting-measurable`.

Informal statement: on an ordered refined branch cell, the minimum sorting map
agrees with the continuous fixed branch map
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]`.

Lean strategy / thesis relation note: the thesis states this as the key local equality before
pasting. Lean obtains the tuple equality from the graph-list equality above,
then translates the value list into the fixed-index-list tuple map.
-/
theorem FixedMinimalSortingBranch.minimumSort_eq_map_of_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (harrival : branch.blocksMatchSegmentArrival (X := X) x) :
    minimumSort (X := X) (Sigma.mk n x : Tuple X) =
      branch.map (X := X) x := by
  have hlist :
      minimumSortList (X := X) (Sigma.mk n x : Tuple X) =
        (fixedBlockEnumerationsIndexList branch.blocks).map fun i => x i :=
    FixedMinimalSortingBranch.minimumSortList_eq_indexList_map_of_blocksMatchSegmentArrival
      (X := X) branch hx harrival
  calc
    minimumSort (X := X) (Sigma.mk n x : Tuple X) =
        tupleOfList (X := X)
          ((fixedBlockEnumerationsIndexList branch.blocks).map fun i => x i) := by
      simpa [minimumSort] using congrArg (tupleOfList (X := X)) hlist
    _ = branch.map (X := X) x := by
      simpa [FixedMinimalSortingBranch.map] using
        (fixedIndexListMap_eq_tupleOfList
          (X := X) (fixedBlockEnumerationsIndexList branch.blocks) x).symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: local equality on ordered refined cells in
`thm:minimal-sorting-measurable`.

Informal statement: on the arrival-refined branch cell, `minimumSort` agrees
with the branch's fixed permutation map.

Lean strategy / thesis relation note: this is just the preceding thesis local-equality theorem with
the two cell hypotheses bundled into the explicit Lean cell
`arrivalRefinedCell`.
-/
theorem FixedMinimalSortingBranch.minimumSort_eq_map_of_mem_arrivalRefinedCell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.arrivalRefinedCell (X := X)) :
    minimumSort (X := X) (Sigma.mk n x : Tuple X) =
      branch.map (X := X) x := by
  exact
    FixedMinimalSortingBranch.minimumSort_eq_map_of_blocksMatchSegmentArrival
      (X := X) branch hx.1 hx.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: local equality on ordered refined cells in
`thm:minimal-sorting-measurable`.

Informal statement: if a branch cell has one witness showing that the listed
blocks are in first-arrival order, then `minimumSort` agrees with the fixed
branch map on the whole branch cell.

Lean strategy / thesis relation note: this packages the order-invariance result above with the
thesis local fixed-map equality.
-/
theorem FixedMinimalSortingBranch.minimumSort_eq_map_of_mem_cell_of_mem_arrivalRefinedCell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x y : Fin n → X} (hx : x ∈ branch.arrivalRefinedCell (X := X))
    (hy : y ∈ branch.cell (X := X)) :
    minimumSort (X := X) (Sigma.mk n y : Tuple X) =
      branch.map (X := X) y := by
  exact
    FixedMinimalSortingBranch.minimumSort_eq_map_of_blocksMatchSegmentArrival
      (X := X) branch hy
      (FixedMinimalSortingBranch.blocksMatchSegmentArrival_of_mem_cell_of_blocksMatchSegmentArrival
        (X := X) branch hx.1 hy hx.2)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: local equality on tuple-realized refined cells in
`thm:minimal-sorting-measurable`.

Informal statement: on the entire refined cell of the branch constructed
from a tuple, `minimumSort` agrees with that branch's fixed map.
-/
theorem FixedMinimalSortingBranch.minimumSort_eq_map_of_mem_cell_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X)
    {y : Fin n → X}
    (hy : y ∈ (FixedMinimalSortingBranch.ofTuple (X := X) x).cell
      (X := X)) :
    minimumSort (X := X) (Sigma.mk n y : Tuple X) =
      (FixedMinimalSortingBranch.ofTuple (X := X) x).map (X := X) y := by
  exact
    FixedMinimalSortingBranch.minimumSort_eq_map_of_mem_cell_of_mem_arrivalRefinedCell
      (X := X) (FixedMinimalSortingBranch.ofTuple (X := X) x)
      (FixedMinimalSortingBranch.mem_arrivalRefinedCell_ofTuple (X := X) x)
      hy

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-branch bookkeeping in
`thm:minimal-sorting-measurable`.

Informal statement: the branch index list has no repeated indices.
-/
theorem FixedMinimalSortingBranch.nodup_indexList {n : ℕ}
    (branch : FixedMinimalSortingBranch n) :
    (fixedBlockEnumerationsIndexList branch.blocks).Nodup :=
  nodup_fixedBlockEnumerationsIndexList_of_pairwiseDisjoint
    branch.coversBlock branch.injectiveEnumeration
    branch.pairwiseDisjointBlocks

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-branch bookkeeping in
`thm:minimal-sorting-measurable`.

Informal statement: the branch index list contains every source index.
-/
theorem FixedMinimalSortingBranch.mem_indexList
    {n : ℕ} (branch : FixedMinimalSortingBranch n) (i : Fin n) :
    i ∈ fixedBlockEnumerationsIndexList branch.blocks := by
  exact
    (mem_fixedBlockEnumerationsIndexList_iff_of_coversBlock
      branch.coversBlock i).mpr (branch.coversAllIndices i)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-permutation fact for
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: the concatenated branch index list is a permutation of
the canonical domain list.
-/
theorem FixedMinimalSortingBranch.indexList_perm_finRange {n : ℕ}
    (branch : FixedMinimalSortingBranch n) :
    (fixedBlockEnumerationsIndexList branch.blocks).Perm
      (List.finRange n) := by
  rw [List.perm_ext_iff_of_nodup
    (FixedMinimalSortingBranch.nodup_indexList branch)
    (List.nodup_finRange n)]
  intro i
  constructor
  · intro _hi
    exact List.mem_finRange i
  · intro _hi
    exact FixedMinimalSortingBranch.mem_indexList branch i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: length of
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: the concatenated branch index list has length `n`.
-/
theorem FixedMinimalSortingBranch.length_indexList {n : ℕ}
    (branch : FixedMinimalSortingBranch n) :
    (fixedBlockEnumerationsIndexList branch.blocks).length = n := by
  exact (FixedMinimalSortingBranch.indexList_perm_finRange branch).length_eq.trans
    (by simp)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite partition cardinality in
`thm:minimal-sorting-measurable`.

Informal statement: the cardinalities of the branch blocks sum to the tuple
length `n`.

Lean strategy / thesis relation note: the thesis uses this as ordinary finite-partition
bookkeeping. Lean obtains it from the fact that the concatenated
block-enumeration index list is a permutation of `Fin n`, together with the
proved equality `length(π_k)=|C_k|`.
-/
theorem FixedMinimalSortingBranch.sum_block_card_eq {n : ℕ}
    (branch : FixedMinimalSortingBranch n) :
    (branch.blocks.map fun B => B.block.card).sum = n := by
  have hsumLen :
      (List.map (List.length ∘ FixedBlockEnumeration.indexList)
        branch.blocks).sum = n := by
    simpa [fixedBlockEnumerationsIndexList] using
      FixedMinimalSortingBranch.length_indexList branch
  have hmap :
      List.map (List.length ∘ FixedBlockEnumeration.indexList)
          branch.blocks =
        branch.blocks.map fun B => B.block.card := by
    apply List.map_congr_left
    intro B hB
    calc
      (List.length ∘ FixedBlockEnumeration.indexList) B = B.length := by
        exact FixedBlockEnumeration.length_indexList B
      _ = B.block.card :=
        FixedBlockEnumeration.length_eq_card_block_of_coversBlock_injective
          (B := B) (branch.coversBlock B hB)
          (branch.injectiveEnumeration B hB)
  simpa [hmap] using hsumLen

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finiteness of partition choices in
`thm:minimal-sorting-measurable`.

Informal statement: a normalized fixed branch over `Fin n` has at most `n`
blocks.

Lean strategy / thesis relation note: this is the formal version of the thesis' finite-partition
bookkeeping: the branch index list is a permutation of `{1,\dots,n}`, and
each nonempty block contributes at least one index to that concatenation.
-/
theorem FixedMinimalSortingBranch.blocks_length_le_of_noEmptyBlocks
    {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (hne : branch.NoEmptyBlocks) :
    branch.blocks.length ≤ n := by
  calc
    branch.blocks.length ≤
        (fixedBlockEnumerationsIndexList branch.blocks).length :=
      blocks_length_le_fixedBlockEnumerationsIndexList_length_of_nonempty
        (blocks := branch.blocks) (by
          intro B hB
          exact
            FixedBlockEnumeration.length_indexList_pos_of_block_nonempty
              (B := B) (branch.coversBlock B hB) (hne B hB))
    _ = n := FixedMinimalSortingBranch.length_indexList branch

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: distinct nonempty partition blocks in
`thm:minimal-sorting-measurable`.

Informal statement: the block sets of a normalized fixed branch have no
duplicates.

Lean strategy / thesis relation note: the theorem recovers the ordinary set-theoretic convention
that the blocks of a partition are distinct sets.
-/
theorem FixedMinimalSortingBranch.nodup_blockList_of_noEmptyBlocks
    {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (hne : branch.NoEmptyBlocks) :
    (branch.blocks.map fun B => B.block).Nodup :=
  nodup_blockList_of_pairwiseDisjoint_noEmpty
    branch.pairwiseDisjointBlocks hne

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: coding a fixed branch
`(P,\pi_1,\dots,\pi_m)`.

Informal statement: any genuine fixed branch whose number of blocks is at
most `n` can be encoded as a finite raw branch code.

Lean strategy / thesis relation note: the length bound is the formal version of the thesis'
nonempty finite-partition observation; for realized/normalized branches this
is supplied by `blocks_length_le_of_noEmptyBlocks`.
-/
noncomputable def FixedBranchRawCode.ofBranch {n : ℕ}
    (branch : FixedMinimalSortingBranch n)
    (hlen : branch.blocks.length ≤ n) : FixedBranchRawCode n :=
  { blockCount := ⟨branch.blocks.length, Nat.lt_succ_of_le hlen⟩
    block := fun k =>
      FixedBlockCode.ofEnumeration (branch.blocks.get k)
        (FixedBlockEnumeration.length_le_of_coversBlock_injective
          (B := branch.blocks.get k)
          (branch.coversBlock (branch.blocks.get k)
            (List.get_mem branch.blocks k))
          (branch.injectiveEnumeration (branch.blocks.get k)
            (List.get_mem branch.blocks k))) }

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: coding a fixed branch
`(P,\pi_1,\dots,\pi_m)`.

Informal statement: encoding a fixed branch and reading out its block list
recovers the original branch block list.
-/
@[simp]
theorem FixedBranchRawCode.toBlocks_ofBranch {n : ℕ}
    (branch : FixedMinimalSortingBranch n)
    (hlen : branch.blocks.length ≤ n) :
    (FixedBranchRawCode.ofBranch branch hlen).toBlocks = branch.blocks := by
  simp [FixedBranchRawCode.ofBranch, FixedBranchRawCode.toBlocks]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: valid finite code for a genuine branch.

Informal statement: the finite raw code obtained from a genuine fixed branch
is valid: it has the same cover, injectivity, disjointness, and universe-cover
hypotheses as the original branch.
-/
theorem FixedBranchRawCode.valid_ofBranch {n : ℕ}
    (branch : FixedMinimalSortingBranch n)
    (hlen : branch.blocks.length ≤ n) :
    (FixedBranchRawCode.ofBranch branch hlen).Valid := by
  have hblocks :
      (FixedBranchRawCode.ofBranch branch hlen).toBlocks = branch.blocks :=
    FixedBranchRawCode.toBlocks_ofBranch branch hlen
  refine
    { coversBlock := ?_
      injectiveEnumeration := ?_
      pairwiseDisjointBlocks := ?_
      coversAllIndices := ?_ }
  · intro B hB
    exact branch.coversBlock B (by simpa [hblocks] using hB)
  · intro B hB
    exact branch.injectiveEnumeration B (by simpa [hblocks] using hB)
  · simpa [hblocks] using branch.pairwiseDisjointBlocks
  · intro i
    simpa [hblocks] using branch.coversAllIndices i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: valid finite branch code for
`(P,\pi_1,\dots,\pi_m)`.

Informal statement: a genuine branch with at most `n` blocks determines a
valid finite branch code.
-/
noncomputable def FixedBranchCode.ofBranch {n : ℕ}
    (branch : FixedMinimalSortingBranch n)
    (hlen : branch.blocks.length ≤ n) : FixedBranchCode n :=
  ⟨FixedBranchRawCode.ofBranch branch hlen,
    FixedBranchRawCode.valid_ofBranch branch hlen⟩

/-- The branch-code encoding preserves the underlying block list. -/
@[simp]
theorem FixedBranchCode.toBranch_ofBranch_blocks {n : ℕ}
    (branch : FixedMinimalSortingBranch n)
    (hlen : branch.blocks.length ≤ n) :
    ((FixedBranchCode.ofBranch branch hlen).toBranch).blocks =
      branch.blocks := by
  simp [FixedBranchCode.ofBranch, FixedBranchCode.toBranch]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite coding preserves the partition relation `P`.

Informal statement: the branch reconstructed from the finite code has the
same same-block relation as the original branch.
-/
theorem FixedBranchCode.toBranch_ofBranch_relation_iff {n : ℕ}
    (branch : FixedMinimalSortingBranch n)
    (hlen : branch.blocks.length ≤ n) (i j : Fin n) :
    ((FixedBranchCode.ofBranch branch hlen).toBranch).relation i j ↔
      branch.relation i j := by
  change
    (FixedBranchRawCode.ofBranch branch hlen).relation i j ↔
      branch.relation i j
  rw [FixedBranchRawCode.relation,
    FixedBranchRawCode.toBlocks_ofBranch]
  exact (branch.blockRelation i j).symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite coding preserves
`\mathscr{E}(P,\pi_1,\dots,\pi_m)`.

Informal statement: encoding a genuine branch as a finite code and
reconstructing it does not change its refined cell.
-/
theorem FixedBranchCode.toBranch_ofBranch_cell_eq
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (hlen : branch.blocks.length ≤ n) :
    ((FixedBranchCode.ofBranch branch hlen).toBranch).cell (X := X) =
      branch.cell (X := X) := by
  ext x
  constructor
  · intro hx
    rw [FixedMinimalSortingBranch.cell, fixedMinimalSortingRefinedCell] at hx ⊢
    refine ⟨?_, ?_⟩
    · intro i j
      exact (hx.1 i j).trans
        (FixedBranchCode.toBranch_ofBranch_relation_iff branch hlen i j)
    · have hblocks :
          ((FixedBranchCode.ofBranch branch hlen).toBranch).blocks =
            branch.blocks :=
        FixedBranchCode.toBranch_ofBranch_blocks branch hlen
      simpa [hblocks] using hx.2
  · intro hx
    rw [FixedMinimalSortingBranch.cell, fixedMinimalSortingRefinedCell] at hx ⊢
    refine ⟨?_, ?_⟩
    · intro i j
      exact (hx.1 i j).trans
        (FixedBranchCode.toBranch_ofBranch_relation_iff branch hlen i j).symm
    · have hblocks :
          ((FixedBranchCode.ofBranch branch hlen).toBranch).blocks =
            branch.blocks :=
        FixedBranchCode.toBranch_ofBranch_blocks branch hlen
      simpa [hblocks] using hx.2

/-- Membership in a branch cell survives finite-code reconstruction. -/
theorem FixedBranchCode.mem_toBranch_cell_ofBranch
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (hlen : branch.blocks.length ≤ n) {x : Fin n → X}
    (hx : x ∈ branch.cell (X := X)) :
    x ∈ ((FixedBranchCode.ofBranch branch hlen).toBranch).cell (X := X) := by
  rwa [FixedBranchCode.toBranch_ofBranch_cell_eq (X := X) branch hlen]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finiteness of realized partition choices in
`thm:minimal-sorting-measurable`.

Informal statement: any branch that is realized by a tuple in its
arrival-refined cell has at most `n` blocks.
-/
theorem FixedMinimalSortingBranch.blocks_length_le_of_mem_arrivalRefinedCell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X}
    (hx : x ∈ branch.arrivalRefinedCell (X := X)) :
    branch.blocks.length ≤ n :=
  FixedMinimalSortingBranch.blocks_length_le_of_noEmptyBlocks branch
    (FixedMinimalSortingBranch.noEmptyBlocks_of_mem_arrivalRefinedCell
      (X := X) branch hx)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: distinct realized partition blocks in
`thm:minimal-sorting-measurable`.

Informal statement: any branch realized by a tuple in its arrival-refined
cell has a duplicate-free block-set list.
-/
theorem FixedMinimalSortingBranch.nodup_blockList_of_mem_arrivalRefinedCell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X}
    (hx : x ∈ branch.arrivalRefinedCell (X := X)) :
    (branch.blocks.map fun B => B.block).Nodup :=
  FixedMinimalSortingBranch.nodup_blockList_of_noEmptyBlocks branch
    (FixedMinimalSortingBranch.noEmptyBlocks_of_mem_arrivalRefinedCell
      (X := X) branch hx)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finiteness of realized partition choices in
`thm:minimal-sorting-measurable`.

Informal statement: the tuple-realized branch has at most `n` connected
blocks.
-/
theorem FixedMinimalSortingBranch.ofTuple_blocks_length_le
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks.length ≤ n :=
  FixedMinimalSortingBranch.blocks_length_le_of_noEmptyBlocks
    (FixedMinimalSortingBranch.ofTuple (X := X) x)
    (FixedMinimalSortingBranch.ofTuple_noEmptyBlocks (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: distinct realized partition blocks in
`thm:minimal-sorting-measurable`.

Informal statement: the tuple-realized branch has a duplicate-free list of
connected block sets.
-/
theorem FixedMinimalSortingBranch.ofTuple_nodup_blockList
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    ((FixedMinimalSortingBranch.ofTuple (X := X) x).blocks.map
      fun B => B.block).Nodup :=
  FixedMinimalSortingBranch.nodup_blockList_of_noEmptyBlocks
    (FixedMinimalSortingBranch.ofTuple (X := X) x)
    (FixedMinimalSortingBranch.ofTuple_noEmptyBlocks (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite code of the tuple-realized branch in
`thm:minimal-sorting-measurable`.

Informal statement: every fixed-length tuple determines a valid finite
branch code.

Lean strategy / thesis relation note: this is the first half of the finite-cover argument: the
tuple-dependent branch constructed earlier can now be viewed as an element of
the finite code type for fixed `n`.
-/
noncomputable def FixedBranchCode.ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) : FixedBranchCode n :=
  FixedBranchCode.ofBranch
    (FixedMinimalSortingBranch.ofTuple (X := X) x)
    (FixedMinimalSortingBranch.ofTuple_blocks_length_le (X := X) x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite code of the tuple-realized branch in
`thm:minimal-sorting-measurable`.

Informal statement: the finite code attached to a tuple has the same block
list as the tuple-realized branch.
-/
@[simp]
theorem FixedBranchCode.toBranch_ofTuple_blocks
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    ((FixedBranchCode.ofTuple (X := X) x).toBranch).blocks =
      (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks := by
  simp [FixedBranchCode.ofTuple]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-code cover witness in
`thm:minimal-sorting-measurable`.

Informal statement: a tuple lies in the arrival-refined cell of the finite
branch code it determines.

Lean strategy / thesis relation note: this is the cover step in finite-code form: the previously
tuple-dependent branch is now represented by an element of the finite code
type.
-/
theorem FixedBranchCode.mem_toBranch_arrivalRefinedCell_ofTuple
    [Preorder X] {n : ℕ} (x : Fin n → X) :
    x ∈ ((FixedBranchCode.ofTuple (X := X) x).toBranch).arrivalRefinedCell
      (X := X) := by
  refine ⟨?_, ?_⟩
  · simpa [FixedBranchCode.ofTuple] using
      FixedBranchCode.mem_toBranch_cell_ofBranch
        (X := X) (FixedMinimalSortingBranch.ofTuple (X := X) x)
        (FixedMinimalSortingBranch.ofTuple_blocks_length_le (X := X) x)
        (FixedMinimalSortingBranch.mem_cell_ofTuple (X := X) x)
  · have hmatch :
        (FixedMinimalSortingBranch.ofTuple (X := X) x).blocksMatchSegmentArrival
          (X := X) x :=
      FixedMinimalSortingBranch.ofTuple_blocksMatchSegmentArrival
        (X := X) x
    have hblocks :
        ((FixedBranchCode.ofTuple (X := X) x).toBranch).blocks =
          (FixedMinimalSortingBranch.ofTuple (X := X) x).blocks :=
      FixedBranchCode.toBranch_ofTuple_blocks (X := X) x
    simpa [FixedMinimalSortingBranch.blocksMatchSegmentArrival, hblocks]
      using hmatch

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: realized finite branch codes in
`thm:minimal-sorting-measurable`.

Informal statement: realized branch codes are valid finite branch codes whose
arrival-refined cells contain at least one tuple.

Lean strategy / thesis relation note: the thesis pastes only over partition/permutation cells that
are actually realized. This subtype removes empty or incorrectly ordered
codes while remaining finite because it is a subtype of the finite code type.
-/
abbrev RealizedFixedBranchCode (X : Type u) [Preorder X] (n : ℕ) :=
  { code : FixedBranchCode n //
    ∃ x : Fin n → X, x ∈ code.toBranch.arrivalRefinedCell (X := X) }

noncomputable instance RealizedFixedBranchCode.instFintype
    (X : Type u) [Preorder X] (n : ℕ) :
    Fintype (RealizedFixedBranchCode X n) := by
  classical
  infer_instance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite realized-code cover in
`thm:minimal-sorting-measurable`.

Informal statement: the cells of realized finite branch codes cover the
fixed-length tuple space `X^n`.
-/
theorem RealizedFixedBranchCode.iUnion_cell_eq_univ
    [Preorder X] {n : ℕ} :
    (⋃ code : RealizedFixedBranchCode X n,
        code.1.toBranch.cell (X := X)) = Set.univ := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    let code : FixedBranchCode n := FixedBranchCode.ofTuple (X := X) x
    have hxcode :
        x ∈ code.toBranch.arrivalRefinedCell (X := X) := by
      simpa [code] using
        FixedBranchCode.mem_toBranch_arrivalRefinedCell_ofTuple
          (X := X) x
    let realized : RealizedFixedBranchCode X n :=
      ⟨code, ⟨x, hxcode⟩⟩
    exact Set.mem_iUnion.mpr ⟨realized, hxcode.1⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: concatenated permutation
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: the genuine finite permutation induced by the branch
index list.
-/
noncomputable def FixedMinimalSortingBranch.permutation {n : ℕ}
    (branch : FixedMinimalSortingBranch n) : FinitePermutation n :=
  finPermutationOfFinList
    (fixedBlockEnumerationsIndexList branch.blocks)
    (FixedMinimalSortingBranch.length_indexList branch)
    (FixedMinimalSortingBranch.mem_indexList branch)
    (FixedMinimalSortingBranch.nodup_indexList branch)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: pointwise reading of
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: applying the branch permutation reads the corresponding
entry of the concatenated branch index list.
-/
@[simp]
theorem FixedMinimalSortingBranch.permutation_apply {n : ℕ}
    (branch : FixedMinimalSortingBranch n) (i : Fin n) :
    FixedMinimalSortingBranch.permutation branch i =
      (fixedBlockEnumerationsIndexList branch.blocks).get
        (Fin.cast
          (FixedMinimalSortingBranch.length_indexList branch).symm i) := by
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: permutation-valued strengthening used in
`thm:minimal-sorting-measurable`.

Informal statement: on a realized fixed sorting cell, the list of indices
chosen by the minimum sorting rule is exactly the concatenation
`\pi_1 \oplus \dots \oplus \pi_m` of the branch permutations.

Lean strategy / thesis relation note: this is the index-list form of the thesis local equality.
It preserves the actual sorting rule, which matters later when duplicate
values could make two different permutations yield the same sorted tuple.
-/
theorem FixedMinimalSortingBranch.minimumSortIndexList_eq_indexList_of_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (harrival : branch.blocksMatchSegmentArrival (X := X) x) :
    minimumSortIndexList (X := X) (Sigma.mk n x : Tuple X) =
      (fixedBlockEnumerationsIndexList branch.blocks).map
        (fun i : Fin n => i.1) := by
  unfold minimumSortIndexList
  rw [
    FixedMinimalSortingBranch.minimumSortGraphList_eq_graphList_of_blocksMatchSegmentArrival
      (X := X) branch hx harrival]
  rw [fixedBlockEnumerationsGraphList_eq_fixedIndexGraphList]
  simp [fixedIndexGraphList, List.map_map]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: permutation-valued strengthening used in
`thm:minimal-sorting-measurable`.

Informal statement: on a realized fixed sorting cell, the minimum sorting
permutation is the branch permutation
`\pi_1 \oplus \dots \oplus \pi_m`.

Lean strategy / thesis relation note: the thesis phrases the local map as
`\bm{x}[\pi_1 \oplus \dots \oplus \pi_m]`. Lean also records equality of
the permutations themselves, not only equality of the permuted tuple.
-/
theorem FixedMinimalSortingBranch.minimumSortPermutation_eq_permutation_of_blocksMatchSegmentArrival
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x : Fin n → X} (hx : x ∈ branch.cell (X := X))
    (harrival : branch.blocksMatchSegmentArrival (X := X) x) :
    minimumSortPermutation (X := X) (Sigma.mk n x : Tuple X) =
      FixedMinimalSortingBranch.permutation branch := by
  have hidx :
      minimumSortIndexList (X := X) (Sigma.mk n x : Tuple X) =
        (fixedBlockEnumerationsIndexList branch.blocks).map
          (fun i : Fin n => i.1) :=
    FixedMinimalSortingBranch.minimumSortIndexList_eq_indexList_of_blocksMatchSegmentArrival
      (X := X) branch hx harrival
  apply Equiv.ext
  intro i
  apply Fin.ext
  unfold minimumSortPermutation FixedMinimalSortingBranch.permutation
  unfold finPermutationOfNatList finPermutationOfFinList
  simp [hidx, List.get_eq_getElem, List.getElem_map]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: permutation-valued strengthening used in
`thm:minimal-sorting-measurable`.

Informal statement: one ordered witness in an arrival-refined cell makes the
minimum sorting permutation constant on the whole fixed branch cell.

Lean strategy / thesis relation note: this is the finite-cell constancy assertion needed for the
thesis pasting proof of the permutation-valued minimal sorting map.
-/
theorem FixedMinimalSortingBranch.minimumSortPermutation_eq_permutation_of_witnessedCell
    [Preorder X] {n : ℕ} (branch : FixedMinimalSortingBranch n)
    {x y : Fin n → X} (hx : x ∈ branch.arrivalRefinedCell (X := X))
    (hy : y ∈ branch.cell (X := X)) :
    minimumSortPermutation (X := X) (Sigma.mk n y : Tuple X) =
      FixedMinimalSortingBranch.permutation branch :=
  FixedMinimalSortingBranch.minimumSortPermutation_eq_permutation_of_blocksMatchSegmentArrival
    (X := X) branch hy
    (FixedMinimalSortingBranch.blocksMatchSegmentArrival_of_mem_cell_of_blocksMatchSegmentArrival
      (X := X) branch hx.1 hy hx.2)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: graph coverage by
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: a genuine branch graph list contains exactly the graph
points of the original tuple.

Lean strategy / thesis relation note: this is the Lean version of the thesis fact that the blocks
`C_1,\dots,C_m` form a partition of `{1,\dots,n}` and each `π_k` is onto
`C_k`.
-/
theorem FixedMinimalSortingBranch.mem_graphList_iff_graph
    {X : Type u} {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (x : Fin n → X) {p : IndexAugmented X} :
    p ∈ fixedBlockEnumerationsGraphList (X := X) branch.blocks x ↔
      p ∈ ((TuplesBasic.graph (Sigma.mk n x : Tuple X)).1 :
        Set (IndexAugmented X)) := by
  rw [fixedBlockEnumerationsGraphList_eq_fixedIndexGraphList]
  constructor
  · intro hp
    rw [fixedIndexGraphList, List.mem_map] at hp
    rcases hp with ⟨i, _hi, rfl⟩
    rw [TuplesBasic.mem_graph]
    exact ⟨i, rfl⟩
  · intro hp
    rcases (TuplesBasic.mem_graph (Sigma.mk n x : Tuple X)).mp hp with
      ⟨i, rfl⟩
    rw [fixedIndexGraphList, List.mem_map]
    exact ⟨i, FixedMinimalSortingBranch.mem_indexList branch i, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite-set form of
`\pi_1 \oplus \dots \oplus \pi_m`.

Informal statement: converting the genuine branch graph list to a finite set
recovers the whole tuple graph.
-/
theorem FixedMinimalSortingBranch.graphPointListToFinset_graphList_eq
    {X : Type u} {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (x : Fin n → X) :
    graphPointListToFinset (X := X)
        (fixedBlockEnumerationsGraphList (X := X) branch.blocks x) =
      toFinset (TuplesBasic.graph (Sigma.mk n x : Tuple X)).1 := by
  ext p
  rw [mem_graphPointListToFinset, mem_toFinset]
  exact FixedMinimalSortingBranch.mem_graphList_iff_graph
    (X := X) branch x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: duplicate-free concatenated graph list.

Informal statement: a genuine branch graph list has no repeated graph points.
-/
theorem FixedMinimalSortingBranch.nodup_graphList
    {X : Type u} {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (x : Fin n → X) :
    (fixedBlockEnumerationsGraphList (X := X) branch.blocks x).Nodup := by
  rw [fixedBlockEnumerationsGraphList_eq_fixedIndexGraphList]
  rw [fixedIndexGraphList]
  exact (FixedMinimalSortingBranch.nodup_indexList branch).map (by
    intro i j hij
    apply Fin.ext
    simpa using congrArg IndexAugmented.index hij)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: length of the concatenated branch graph list.

Informal statement: the branch graph list has one graph point for each input
tuple coordinate.
-/
theorem FixedMinimalSortingBranch.length_graphList
    {X : Type u} {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (x : Fin n → X) :
    (fixedBlockEnumerationsGraphList (X := X) branch.blocks x).length = n := by
  rw [fixedBlockEnumerationsGraphList_eq_fixedIndexGraphList]
  simp [fixedIndexGraphList, FixedMinimalSortingBranch.length_indexList branch]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of branch cells
`\mathscr{E}(P,\pi_1,\dots,\pi_m)`.
-/
theorem FixedMinimalSortingBranch.measurableSet_cell_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n : ℕ} (branch : FixedMinimalSortingBranch n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (branch.cell (X := X)) :=
  measurableSet_fixedMinimalSortingRefinedCell_of_borelOrder
    (X := X) hle branch.relation branch.blocks

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: continuity of branch maps
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]`.
-/
theorem FixedMinimalSortingBranch.continuous_map
    {X : Type u} [EMetricSpace X] {n : ℕ}
    (branch : FixedMinimalSortingBranch n) :
    @Continuous (Fin n → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun x => branch.map (X := X) x) := by
  simpa [FixedMinimalSortingBranch.map] using
    continuous_fixedIndexListMap
      (X := X) (fixedBlockEnumerationsIndexList branch.blocks)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: local measurable restriction in
`thm:minimal-sorting-measurable`.

Informal statement: if a fixed branch has one tuple witnessing that its
blocks are listed in first-arrival order, then the restriction of
`minimumSort` to the whole branch cell is measurable.

Lean strategy / thesis relation note: the previous order-invariance theorem turns one ordered
witness into order throughout the cell. The rest is the thesis argument:
on the cell, `minimumSort` is the continuous fixed map
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]`.
-/
theorem FixedMinimalSortingBranch.measurable_minimumSort_restrict_of_mem_arrivalRefinedCell
    {X : Type u} [EMetricSpace X] [Preorder X] {n : ℕ}
    (branch : FixedMinimalSortingBranch n)
    {x₀ : Fin n → X} (hx₀ : x₀ ∈ branch.arrivalRefinedCell (X := X)) :
    letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    Measurable
      (fun x : branch.cell (X := X) =>
        minimumSort (X := X) (Sigma.mk n x.1 : Tuple X)) := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  have hbranch_cont :
      Continuous
        (fun x : branch.cell (X := X) => branch.map (X := X) x.1) :=
    (FixedMinimalSortingBranch.continuous_map
      (X := X) branch).comp continuous_subtype_val
  have hbranch_meas :
      Measurable
        (fun x : branch.cell (X := X) => branch.map (X := X) x.1) :=
    hbranch_cont.measurable
  have hfun :
      (fun x : branch.cell (X := X) =>
        minimumSort (X := X) (Sigma.mk n x.1 : Tuple X)) =
        (fun x : branch.cell (X := X) => branch.map (X := X) x.1) := by
    funext x
    exact
      FixedMinimalSortingBranch.minimumSort_eq_map_of_mem_cell_of_mem_arrivalRefinedCell
        (X := X) branch hx₀ x.2
  simpa [hfun] using hbranch_meas

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite pasting step in `thm:minimal-sorting-measurable`.

Informal statement: if finitely many fixed branch cells cover `X^n`, and
each branch has one ordered witness, then the fixed-length minimum sorting
map is Borel measurable.

Lean strategy / thesis relation note: this is the version of the thesis pasting argument that the
finite combinatorial enumeration of branch data should instantiate. It avoids
requiring the stronger universe-polymorphic `OrderedFixedMinimalSortingBranch`
wrapper; one realized point per branch is enough because first-arrival order
is invariant on the cell.
-/
theorem measurable_minimumSort_fixedLength_of_realizedBranchFiniteCover
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {m n : ℕ} (branches : Fin m → FixedMinimalSortingBranch n)
    (hwitness : ∀ k : Fin m,
      ∃ x : Fin n → X, x ∈ (branches k).arrivalRefinedCell (X := X))
    (hcover : (⋃ k : Fin m, (branches k).cell (X := X)) = Set.univ) :
    letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    @Measurable (Fin n → X) (Tuple X) (@borel (Fin n → X) inferInstance)
      (tupleHausdorffBorel (X := X))
      (fun x => minimumSort (X := X) (Sigma.mk n x : Tuple X)) := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  exact
    measurable_of_measurable_restrict_countable_cover
      (S := fun k : Fin m => (branches k).cell (X := X))
      (fun k =>
        FixedMinimalSortingBranch.measurableSet_cell_of_borelOrder
          (X := X) hle (branches k))
      hcover
      (fun k => by
        rcases hwitness k with ⟨x₀, hx₀⟩
        exact
          FixedMinimalSortingBranch.measurable_minimumSort_restrict_of_mem_arrivalRefinedCell
            (X := X) (branches k) hx₀)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed-length finite-code proof of
`thm:minimal-sorting-measurable`.

Informal statement: on each fixed-length layer `X^n`, the minimum sorting
map is Borel measurable.

Lean strategy / thesis relation note: this instantiates the thesis finite-pasting argument using
the finite subtype of realized branch codes. The cover is finite because
there are finitely many bounded branch codes, and every tuple belongs to the
arrival-refined cell of its own code.
-/
theorem measurable_minimumSort_fixedLength_of_realizedBranchCodes
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n : ℕ} :
    letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    @Measurable (Fin n → X) (Tuple X) (@borel (Fin n → X) inferInstance)
      (tupleHausdorffBorel (X := X))
      (fun x => minimumSort (X := X) (Sigma.mk n x : Tuple X)) := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  exact
    measurable_of_measurable_restrict_countable_cover
      (S := fun code : RealizedFixedBranchCode X n =>
        code.1.toBranch.cell (X := X))
      (fun code =>
        FixedMinimalSortingBranch.measurableSet_cell_of_borelOrder
          (X := X) hle code.1.toBranch)
      (RealizedFixedBranchCode.iUnion_cell_eq_univ (X := X) (n := n))
      (fun code => by
        rcases code.2 with ⟨x₀, hx₀⟩
        exact
          FixedMinimalSortingBranch.measurable_minimumSort_restrict_of_mem_arrivalRefinedCell
            (X := X) code.1.toBranch hx₀)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `thm:minimal-sorting-measurable`.

Informal statement: if the order relation is Borel, then the minimum sorting
map on tuple space is Borel measurable.

Lean strategy / thesis relation note: this is the thesis proof's final pasting step over
`\mathscr{T}(X)=\bigsqcup_n X^n`. The fixed-length measurability has already
been proved by finite realized branch codes; the global result follows from
the standard fixed-length/Sigma measurable bridge.
-/
theorem measurable_minimumSort_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2}) :
    @Measurable (Tuple X) (Tuple X) (tupleHausdorffBorel (X := X))
      (tupleHausdorffBorel (X := X)) (minimumSort (X := X)) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  exact
    (measurable_tupleHausdorff_iff_fixedLength
      (X := X) (Y := Tuple X) (f := minimumSort (X := X))).mpr
      (fun n =>
        measurable_minimumSort_fixedLength_of_realizedBranchCodes
          (X := X) hle (n := n))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed-length permutation-valued step in
`thm:minimal-sorting-measurable`.

Informal statement: on a fixed-length layer `X^n`, the map sending a tuple to
its minimum sorting permutation is Borel measurable.

Lean strategy / thesis relation note: this is the same finite-pasting argument as the tuple-valued
theorem above, but the local equality is now equality of the chosen
permutation. This keeps the formal statement faithful when repeated values
make different permutations act identically on the tuple.
-/
theorem measurable_minimumSortPermutation_fixedLength_of_realizedBranchCodes
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n : ℕ} :
    letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
    letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
    letI : MeasurableSpace FinitePermutations :=
      @borel FinitePermutations finitePermutationMetricTopology
    @Measurable (Fin n → X) FinitePermutations
      (@borel (Fin n → X) inferInstance)
      (@borel FinitePermutations finitePermutationMetricTopology)
      (fun x =>
        Sigma.mk n (minimumSortPermutation (X := X)
          (Sigma.mk n x : Tuple X))) := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  letI : OpensMeasurableSpace FinitePermutations := ⟨le_rfl⟩
  letI : BorelSpace FinitePermutations := ⟨rfl⟩
  exact
    measurable_of_measurable_restrict_countable_cover
      (S := fun code : RealizedFixedBranchCode X n =>
        code.1.toBranch.cell (X := X))
      (fun code =>
        FixedMinimalSortingBranch.measurableSet_cell_of_borelOrder
          (X := X) hle code.1.toBranch)
      (RealizedFixedBranchCode.iUnion_cell_eq_univ (X := X) (n := n))
      (fun code => by
        rcases code.2 with ⟨x₀, hx₀⟩
        have hfun :
            (fun x : code.1.toBranch.cell (X := X) =>
              Sigma.mk n (minimumSortPermutation (X := X)
                (Sigma.mk n x.1 : Tuple X))) =
              (fun _x : code.1.toBranch.cell (X := X) =>
                Sigma.mk n
                  (FixedMinimalSortingBranch.permutation code.1.toBranch)) := by
          funext x
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            exact
              FixedMinimalSortingBranch.minimumSortPermutation_eq_permutation_of_witnessedCell
                (X := X) code.1.toBranch hx₀ x.2
        rw [hfun]
        exact measurable_const)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: permutation-valued form of
`thm:minimal-sorting-measurable`.

Informal statement: if the order relation is Borel, then the minimum sorting
permutation map on tuple space is Borel measurable.

Lean strategy / thesis relation note: the thesis' map is permutation-valued. The codomain here is
the disjoint union `Σ n, Equiv.Perm (Fin n)` of finite permutation groups,
matching the thesis' varying tuple lengths.
-/
theorem measurable_minimumSortPermutation_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2}) :
    letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
    letI : MeasurableSpace FinitePermutations :=
      @borel FinitePermutations finitePermutationMetricTopology
    @Measurable (Tuple X) FinitePermutations
      (tupleHausdorffBorel (X := X))
      (@borel FinitePermutations finitePermutationMetricTopology)
      (fun x => Sigma.mk x.length (minimumSortPermutation (X := X) x)) := by
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  exact
    (measurable_tupleHausdorff_iff_fixedLength
      (X := X) (Y := FinitePermutations)
      (f := fun x => Sigma.mk x.length
        (minimumSortPermutation (X := X) x))).mpr
      (fun n =>
        measurable_minimumSortPermutation_fixedLength_of_realizedBranchCodes
          (X := X) hle (n := n))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed map
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]`.

Informal statement: the branch list-index map is exactly permutation by the
finite permutation induced from the concatenated branch list.

Lean strategy / thesis relation note: this removes the temporary Lean-only list representation and
recovers the thesis' fixed-permutation formulation.
-/
theorem FixedMinimalSortingBranch.map_eq_permute
    {X : Type u} {n : ℕ} (branch : FixedMinimalSortingBranch n)
    (x : Fin n → X) :
    branch.map (X := X) x =
      permute (Sigma.mk n x : Tuple X)
        (FixedMinimalSortingBranch.permutation branch) := by
  let idx : List (Fin n) := fixedBlockEnumerationsIndexList branch.blocks
  have hLen : idx.length = n :=
    FixedMinimalSortingBranch.length_indexList branch
  unfold FixedMinimalSortingBranch.map fixedIndexListMap permute
  apply Sigma.ext
  · exact hLen
  · let f : Fin idx.length → X := fun i => x (idx.get i)
    let g : Fin n → X := fun i =>
      Tuple.entry (Sigma.mk n x : Tuple X)
        (FixedMinimalSortingBranch.permutation branch i)
    have hα : Fin idx.length = Fin n := congrArg Fin hLen
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
    have hget :
        idx.get a = idx.get (Fin.cast hLen.symm (cast hα a)) := by
      rw [hfin]
    change x (idx.get a) =
      Tuple.entry (Sigma.mk n x : Tuple X)
        (FixedMinimalSortingBranch.permutation branch (cast hα a))
    simpa [FixedMinimalSortingBranch.permutation, finPermutationOfFinList, idx] using
      congrArg x hget

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: ordered refined branches in
`thm:minimal-sorting-measurable`.

Informal statement: an ordered fixed branch is fixed branch data
`(P,\pi_1,\dots,\pi_m)` whose listed blocks agree, on its cell, with the
first-arrival order of the tuple's connected segments.

Lean strategy / thesis relation note: the thesis silently orders the partition blocks before pasting
the fixed maps. Lean keeps this as an explicit field so the local equality
`minimumSort = x[\pi_1 \oplus \dots \oplus \pi_m]` cannot be applied to a
branch whose blocks are listed in the wrong order.
-/
structure OrderedFixedMinimalSortingBranch (n : ℕ) : Type (u + 1) where
  branch : FixedMinimalSortingBranch n
  blocksMatchSegmentArrival :
    ∀ {X : Type u} [Preorder X] {x : Fin n → X},
      x ∈ branch.cell (X := X) →
        branch.blocksMatchSegmentArrival (X := X) x

/-- The underlying cell of an ordered fixed branch. -/
def OrderedFixedMinimalSortingBranch.cell [Preorder X] {n : ℕ}
    (ordered : OrderedFixedMinimalSortingBranch.{u} n) : Set (Fin n → X) :=
  ordered.branch.cell (X := X)

/-- The fixed map attached to an ordered fixed branch. -/
def OrderedFixedMinimalSortingBranch.map {X : Type u} {n : ℕ}
    (ordered : OrderedFixedMinimalSortingBranch.{u} n)
    (x : Fin n → X) : Tuple X :=
  ordered.branch.map (X := X) x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: local equality in `thm:minimal-sorting-measurable`.

Informal statement: on an ordered refined branch cell, `minimumSort` agrees
with the branch's fixed permutation map.
-/
theorem OrderedFixedMinimalSortingBranch.minimumSort_eq_map_of_mem_cell
    [Preorder X] {n : ℕ}
    (ordered : OrderedFixedMinimalSortingBranch.{u} n)
    {x : Fin n → X} (hx : x ∈ ordered.cell (X := X)) :
    minimumSort (X := X) (Sigma.mk n x : Tuple X) =
      ordered.map (X := X) x := by
  exact
    FixedMinimalSortingBranch.minimumSort_eq_map_of_blocksMatchSegmentArrival
      (X := X) ordered.branch
      (by simpa [OrderedFixedMinimalSortingBranch.cell] using hx)
      (ordered.blocksMatchSegmentArrival
        (by simpa [OrderedFixedMinimalSortingBranch.cell] using hx))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurability of ordered branch cells in
`thm:minimal-sorting-measurable`.
-/
theorem OrderedFixedMinimalSortingBranch.measurableSet_cell_of_borelOrder
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n : ℕ} (ordered : OrderedFixedMinimalSortingBranch.{u} n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (ordered.cell (X := X)) := by
  simpa [OrderedFixedMinimalSortingBranch.cell] using
    FixedMinimalSortingBranch.measurableSet_cell_of_borelOrder
      (X := X) hle ordered.branch

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: continuity of fixed ordered-branch maps in
`thm:minimal-sorting-measurable`.
-/
theorem OrderedFixedMinimalSortingBranch.continuous_map
    {X : Type u} [EMetricSpace X] {n : ℕ}
    (ordered : OrderedFixedMinimalSortingBranch.{u} n) :
    @Continuous (Fin n → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun x => ordered.map (X := X) x) := by
  simpa [OrderedFixedMinimalSortingBranch.map] using
    FixedMinimalSortingBranch.continuous_map (X := X) ordered.branch

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: local measurable restriction in
`thm:minimal-sorting-measurable`.

Informal statement: the restriction of the minimum sorting map to one ordered
refined branch cell is measurable, because there it is equal to a continuous
fixed branch map.
-/
theorem OrderedFixedMinimalSortingBranch.measurable_minimumSort_restrict
    {X : Type u} [EMetricSpace X] [Preorder X] {n : ℕ}
    (ordered : OrderedFixedMinimalSortingBranch.{u} n) :
    letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    Measurable
      (fun x : ordered.cell (X := X) =>
        minimumSort (X := X) (Sigma.mk n x.1 : Tuple X)) := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  have hbranch_cont :
      Continuous
        (fun x : ordered.cell (X := X) => ordered.map (X := X) x.1) :=
    (OrderedFixedMinimalSortingBranch.continuous_map
      (X := X) ordered).comp continuous_subtype_val
  have hbranch_meas :
      Measurable
        (fun x : ordered.cell (X := X) => ordered.map (X := X) x.1) :=
    hbranch_cont.measurable
  have hfun :
      (fun x : ordered.cell (X := X) =>
        minimumSort (X := X) (Sigma.mk n x.1 : Tuple X)) =
        (fun x : ordered.cell (X := X) => ordered.map (X := X) x.1) := by
    funext x
    exact OrderedFixedMinimalSortingBranch.minimumSort_eq_map_of_mem_cell
      (X := X) ordered x.2
  simpa [hfun] using hbranch_meas

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: pasting step in `thm:minimal-sorting-measurable`.

Informal statement: if the fixed-length space `X^n` is partitioned by
ordered refined branch cells, then the fixed-length minimum sorting map is
Borel measurable.

Lean strategy / thesis relation note: this is the thesis measurable-pasting argument. The theorem is
conditional on the ordered branch partition; constructing that finite
partition is the next formalization task.
-/
theorem measurable_minimumSort_fixedLength_of_orderedBranchPartition
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {n : ℕ} (branches : ℕ → OrderedFixedMinimalSortingBranch.{u} n)
    (hdisjoint : Pairwise fun m k =>
      Disjoint ((branches m).cell (X := X)) ((branches k).cell (X := X)))
    (hcover : (⋃ k : ℕ, (branches k).cell (X := X)) = Set.univ) :
    letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    @Measurable (Fin n → X) (Tuple X) (@borel (Fin n → X) inferInstance)
      (tupleHausdorffBorel (X := X))
      (fun x => minimumSort (X := X) (Sigma.mk n x : Tuple X)) := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  exact
    (measurable_iff_measurable_restrict_partition
      (S := fun k : ℕ => (branches k).cell (X := X))
      (fun k =>
        OrderedFixedMinimalSortingBranch.measurableSet_cell_of_borelOrder
          (X := X) hle (branches k))
      hdisjoint hcover).2
      (fun k =>
        OrderedFixedMinimalSortingBranch.measurable_minimumSort_restrict
          (X := X) (branches k))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: finite pasting step in `thm:minimal-sorting-measurable`.

Informal statement: if the fixed-length space `X^n` is covered by finitely
many ordered refined branch cells, then the fixed-length minimum sorting map
is Borel measurable.

Lean strategy / thesis relation note: this is the closer fixed-length version of the thesis proof:
for fixed `n`, there are finitely many partitions and finitely many block
permutations. The theorem still assumes the finite cover has already been
constructed.
-/
theorem measurable_minimumSort_fixedLength_of_orderedBranchFiniteCover
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2})
    {m n : ℕ} (branches : Fin m → OrderedFixedMinimalSortingBranch.{u} n)
    (hcover : (⋃ k : Fin m, (branches k).cell (X := X)) = Set.univ) :
    letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    @Measurable (Fin n → X) (Tuple X) (@borel (Fin n → X) inferInstance)
      (tupleHausdorffBorel (X := X))
      (fun x => minimumSort (X := X) (Sigma.mk n x : Tuple X)) := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  exact
    measurable_of_measurable_restrict_countable_cover
      (S := fun k : Fin m => (branches k).cell (X := X))
      (fun k =>
        OrderedFixedMinimalSortingBranch.measurableSet_cell_of_borelOrder
          (X := X) hle (branches k))
      hcover
      (fun k =>
        OrderedFixedMinimalSortingBranch.measurable_minimumSort_restrict
          (X := X) (branches k))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: fixed map
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]`.

Informal statement: apply the concatenated block enumeration list to a
fixed-length tuple.
-/
def fixedBlockEnumerationsMap {X : Type u} {n : ℕ}
    (blocks : List (FixedBlockEnumeration n)) (x : Fin n → X) : Tuple X :=
  fixedIndexListMap (X := X) (fixedBlockEnumerationsIndexList blocks) x

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: continuity of
`\bm{x} \mapsto \bm{x}[\pi_1 \oplus \dots \oplus \pi_m]` in
`thm:minimal-sorting-measurable`.

Informal statement: the fixed block-concatenation map attached to one refined
cell is continuous.
-/
theorem continuous_fixedBlockEnumerationsMap
    {X : Type u} [EMetricSpace X] {n : ℕ}
    (blocks : List (FixedBlockEnumeration n)) :
    @Continuous (Fin n → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun x => fixedBlockEnumerationsMap (X := X) blocks x) := by
  simpa [fixedBlockEnumerationsMap] using
    continuous_fixedIndexListMap
      (X := X) (fixedBlockEnumerationsIndexList blocks)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: measurable-set component of
`prop:measurable-partition-sorting`.

Informal statement: if all sorting-valid sets `\mathscr{V}_π` are
measurable, then every cell `\mathscr{U}_n` is measurable.

Lean strategy / thesis relation note: this is the thesis proof verbatim: each `\mathscr{U}_n` is
`\mathscr{V}_{π_(n)}` minus the finite union of earlier
`\mathscr{V}_{π_(m)}` sets. Lean indexes that finite union by the subtype
`{m // m < n}`.
-/
theorem measurableSet_sortingCell_of_measurable_sortingValidSet
    [Preorder X] [MeasurableSpace (Tuple X)]
    (φ : FinitePermutations ≃ ℕ)
    (hV : ∀ π : FinitePermutations,
      MeasurableSet (sortingValidSet (X := X) π)) :
    ∀ n : ℕ, MeasurableSet (sortingCell (X := X) φ n) := by
  intro n
  have hcell :
      sortingCell (X := X) φ n =
        sortingValidSet (X := X) (rankedPermutation φ n) ∩
          (⋃ m : {m : ℕ // m < n},
            sortingValidSet (X := X) (rankedPermutation φ m.1))ᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxEarlier
      rcases Set.mem_iUnion.mp hxEarlier with ⟨m, hm⟩
      exact hx.2 m.1 m.2 hm
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro m hm hmem
      exact hx.2 (Set.mem_iUnion.2 ⟨⟨m, hm⟩, hmem⟩)
  rw [hcell]
  exact (hV (rankedPermutation φ n)).inter
    ((MeasurableSet.iUnion fun m : {m : ℕ // m < n} =>
      hV (rankedPermutation φ m.1)).compl)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `prop:measurable-partition-sorting`.

Informal statement: the cells `\mathscr{U}_n` form a countable measurable
partition of tuple space.

Lean strategy / thesis relation note: the theorem is conditional on an existing sorting rule and on
measurability of the valid sets `\mathscr{V}_π`. The remaining Borel proof of
that hypothesis belongs to the later measurable-sorting existence theorem.
-/
theorem sortingCell_measurablePartition_of_sortingRule
    [Preorder X] [MeasurableSpace (Tuple X)]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (hV : ∀ π : FinitePermutations,
      MeasurableSet (sortingValidSet (X := X) π)) :
    (∀ n : ℕ, MeasurableSet (sortingCell (X := X) φ n)) ∧
      Pairwise (fun m n : ℕ =>
        Disjoint (sortingCell (X := X) φ m) (sortingCell (X := X) φ n)) ∧
      (⋃ n : ℕ, sortingCell (X := X) φ n) = Set.univ := by
  exact ⟨measurableSet_sortingCell_of_measurable_sortingValidSet
      (X := X) φ hV,
    sortingCell_pairwiseDisjoint (X := X) φ,
    sortingCell_cover_of_sortingRule (X := X) σ φ⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `prop:measurable-partition-sorting`.

Informal statement: under the Borel strict-order assumption, the cells
`\mathscr{U}_n` form a countable measurable partition of tuple space.

Lean strategy / thesis relation note: this discharges the thesis proof's missing Borel-valid-set
step by invoking `measurableSet_sortingValidSet_of_strictOrder`.
-/
theorem sortingCell_measurablePartition_of_strictOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (hstrict :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 < p.2}) :
    (∀ n : ℕ,
        @MeasurableSet (Tuple X) (tupleHausdorffBorel (X := X))
          (sortingCell (X := X) φ n)) ∧
      Pairwise (fun m n : ℕ =>
        Disjoint (sortingCell (X := X) φ m) (sortingCell (X := X) φ n)) ∧
      (⋃ n : ℕ, sortingCell (X := X) φ n) = Set.univ := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  exact sortingCell_measurablePartition_of_sortingRule
    (X := X) σ φ (measurableSet_sortingValidSet_of_strictOrder (X := X) hstrict)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `prop:measurable-partition-sorting`.

Informal statement: the sets `\mathscr{U}_n` form a measurable partition for
any ranking of finite permutations, assuming the strict order is Borel.

Lean strategy / thesis relation note: this wrapper now uses the verified minimum sorting rule to
supply the cover, rather than the earlier choice-based sorting rule.
-/
theorem sortingCell_measurablePartition_of_strictOrder_exists
    {X : Type u} [EMetricSpace X] [Preorder X]
    (φ : FinitePermutations ≃ ℕ)
    (hstrict :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 < p.2}) :
    (∀ n : ℕ,
        @MeasurableSet (Tuple X) (tupleHausdorffBorel (X := X))
          (sortingCell (X := X) φ n)) ∧
      Pairwise (fun m n : ℕ =>
        Disjoint (sortingCell (X := X) φ m) (sortingCell (X := X) φ n)) ∧
      (⋃ n : ℕ, sortingCell (X := X) φ n) = Set.univ :=
  sortingCell_measurablePartition_of_strictOrder
    (X := X)
    (_root_.Thesis.Foundations.MarketRepresentation.TuplesSorting.minimumSortingRule
      (X := X)) φ hstrict

/-! ## Measurable Induced Sorting -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: local restriction step in `thm:measurable-sorting-exists`.

Informal statement: on a cell `\mathscr{U}_n`, the induced sorting rule is
Borel measurable because it agrees there with the fixed continuous local
sorting map `\varsigma_{\pi_(n)}`.

Lean strategy / thesis relation note: the proof is the thesis proof with the subtypes made explicit:
`\mathscr{U}_n` includes into `\mathscr{V}_{\pi_(n)}`, and
`cor:local-continuity-sorting` supplies continuity on that larger valid set.
-/
theorem measurable_inducedSortingRule_restrict_sortingCell
    {X : Type u} [EMetricSpace X] [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (n : ℕ) :
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    letI : TopologicalSpace (SortedTuple X) := sortedTupleTopology (X := X)
    letI : MeasurableSpace (SortedTuple X) :=
      @borel (SortedTuple X) (sortedTupleTopology (X := X))
    Measurable
      (fun x : sortingCell (X := X) φ n =>
        (inducedSortingRule (X := X) σ φ).toSortedTuple x.1) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  letI : TopologicalSpace (SortedTuple X) := sortedTupleTopology (X := X)
  letI : MeasurableSpace (SortedTuple X) :=
    @borel (SortedTuple X) (sortedTupleTopology (X := X))
  letI : OpensMeasurableSpace (SortedTuple X) := ⟨le_rfl⟩
  letI : BorelSpace (SortedTuple X) := ⟨rfl⟩
  let πn := rankedPermutation φ n
  have hinc :
      Continuous (fun x : sortingCell (X := X) φ n =>
        (⟨x.1, x.2.1⟩ : sortingValidSet (X := X) πn)) :=
    continuous_subtype_val.subtype_mk (fun x => x.2.1)
  have hbranch_cont :
      Continuous (fun x : sortingCell (X := X) φ n =>
        sortingValidMap (X := X) πn (⟨x.1, x.2.1⟩)) :=
    (continuous_sortingValidMap (X := X) πn).comp hinc
  have hbranch_meas :
      Measurable (fun x : sortingCell (X := X) φ n =>
        sortingValidMap (X := X) πn (⟨x.1, x.2.1⟩)) :=
    hbranch_cont.measurable
  have hfun :
      (fun x : sortingCell (X := X) φ n =>
        (inducedSortingRule (X := X) σ φ).toSortedTuple x.1) =
        (fun x : sortingCell (X := X) φ n =>
          sortingValidMap (X := X) πn (⟨x.1, x.2.1⟩)) := by
    funext x
    apply Subtype.ext
    change (inducedSortingRule (X := X) σ φ).sort x.1 =
      permutationMap x.1 πn
    exact inducedSortingRule_sort_eq_of_mem_sortingCell (X := X) σ φ x.2
  simpa [hfun] using hbranch_meas

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `thm:measurable-sorting-exists`, measurable-pasting step.

Informal statement: for any enumeration of finite permutations, the induced
sorting rule is Borel measurable when the strict order relation is Borel.

Lean strategy / thesis relation note: this theorem keeps explicit the current Lean prerequisite
`σ : SortingRule X`, which supplies the earlier thesis result that every tuple
has at least one sorting permutation. The non-conditional theorem below uses
the verified minimum sorting rule as that witness.
-/
theorem measurable_inducedSortingRule_of_strictOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (σ : TuplesSorting.SortingRule X) (φ : FinitePermutations ≃ ℕ)
    (hstrict :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 < p.2}) :
    @Measurable (Tuple X) (SortedTuple X)
      (tupleHausdorffBorel (X := X))
      (@borel (SortedTuple X) (sortedTupleTopology (X := X)))
      (inducedSortingRule (X := X) σ φ).toSortedTuple := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : TopologicalSpace (SortedTuple X) := sortedTupleTopology (X := X)
  letI : MeasurableSpace (SortedTuple X) :=
    @borel (SortedTuple X) (sortedTupleTopology (X := X))
  have hpartition :=
    sortingCell_measurablePartition_of_strictOrder (X := X) σ φ hstrict
  exact (measurable_iff_measurable_restrict_partition
    (S := fun n : ℕ => sortingCell (X := X) φ n)
    hpartition.1 hpartition.2.1 hpartition.2.2).2
      (fun n => measurable_inducedSortingRule_restrict_sortingCell
        (X := X) σ φ n)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: conditional form of `thm:measurable-sorting-exists`.

Informal statement: given the earlier sorting-existence result as an input,
there exists a Borel measurable sorting rule.

Lean strategy / thesis relation note: the thesis also chooses a bijection
`\varphi : \mathscr{P} → \mathbb{N}`. Lean obtains such a bijection from the
countability and infinitude of `FinitePermutations` via mathlib's
`Nonempty (FinitePermutations ≃ ℕ)` instance.
-/
theorem exists_measurableSortingRule_of_sortingRule_strictOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (σ : TuplesSorting.SortingRule X)
    (hstrict :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 < p.2}) :
    ∃ τ : TuplesSorting.SortingRule X,
      @Measurable (Tuple X) (SortedTuple X)
        (tupleHausdorffBorel (X := X))
        (@borel (SortedTuple X) (sortedTupleTopology (X := X)))
        τ.toSortedTuple := by
  classical
  let φ : FinitePermutations ≃ ℕ :=
    Classical.choice (inferInstance :
      Nonempty (FinitePermutations ≃ ℕ))
  exact ⟨inducedSortingRule (X := X) σ φ,
    measurable_inducedSortingRule_of_strictOrder (X := X) σ φ hstrict⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: strict-order form of `thm:measurable-sorting-exists`.

Informal statement: if the strict order is Borel, then a Borel measurable
sorting rule exists.

Lean strategy / thesis relation note: the witness supplied here is induced from the verified minimum
sorting rule.
-/
theorem exists_measurableSortingRule_of_strictOrder
    {X : Type u} [EMetricSpace X] [Preorder X]
    (hstrict :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 < p.2}) :
    ∃ τ : TuplesSorting.SortingRule X,
      @Measurable (Tuple X) (SortedTuple X)
        (tupleHausdorffBorel (X := X))
        (@borel (SortedTuple X) (sortedTupleTopology (X := X)))
        τ.toSortedTuple :=
  exists_measurableSortingRule_of_sortingRule_strictOrder
    (X := X)
    (_root_.Thesis.Foundations.MarketRepresentation.TuplesSorting.minimumSortingRule
      (X := X)) hstrict

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorting Properties".

Original label: `thm:measurable-sorting-exists`.

Informal statement: if the partial order is Borel, then a Borel measurable
sorting rule exists.

Lean strategy / thesis relation note: the thesis also assumes completeness and separability of the
metric space. Those hypotheses are needed for the surrounding Polish/standard
Borel development; the measurable sorting construction itself only uses the
Borel order relation.
-/
theorem exists_measurableSortingRule_of_borelOrder
    {X : Type u} [EMetricSpace X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [PartialOrder X]
    (hle :
      @MeasurableSet (X × X) (@borel (X × X) inferInstance)
        {p | p.1 ≤ p.2}) :
    ∃ τ : TuplesSorting.SortingRule X,
      @Measurable (Tuple X) (SortedTuple X)
        (tupleHausdorffBorel (X := X))
        (@borel (SortedTuple X) (sortedTupleTopology (X := X)))
        τ.toSortedTuple :=
  exists_measurableSortingRule_of_strictOrder
    (X := X) (measurableSet_strictOrder_of_measurableSet_le (X := X) hle)

end TuplesMeasurableSorting
end MarketRepresentation
end Foundations
end Thesis
