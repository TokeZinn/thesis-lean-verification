import Foundations.MarketRepresentation.TuplesMeasurableSorting

/-!
# Market Actions: Primitive Actions

Blueprint module for
`1 - theoretical foundations/3_market_actions.tex`,
section "Primitive Actions".

Planned formal content:

* `defn:concat-tuple`;
* `defn:sorted-tuple-add`;
* `prop:tuple-monoid`;
* `defn:pairing`;
* `defn:reindex`;
* `defn:cancel`;
* `defn:sorted-cancel`;
* `cor:cancel-closure-sorted`;
* `defn:modification`.
-/

namespace Thesis
namespace Foundations
namespace MarketActions
namespace Primitive

open Thesis.Foundations.MarketRepresentation
open Thesis.Foundations.MarketRepresentation.FiniteSets
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesSorting

universe u

variable {X : Type u}

/-! ## Concatenation -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `defn:concat-tuple`.

Informal statement: append one tuple after another. Entries from the left tuple
occupy the first `x.length` indices, and entries from the right tuple occupy
the following `y.length` indices.

Lean strategy / thesis relation note: the thesis indexes by `{1, ..., n}`. Lean uses `Fin n`, so the
left injection is `Fin.castAdd` and the right injection is `Fin.natAdd`.
-/
def concat (x y : Tuple X) : Tuple X :=
  ⟨x.length + y.length,
    Fin.append (fun i : Fin x.length => Tuple.entry x i)
      (fun i : Fin y.length => Tuple.entry y i)⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: immediate length property of `defn:concat-tuple`.

Informal statement: the length of a concatenation is the sum of the lengths.
-/
@[simp]
theorem concat_length (x y : Tuple X) :
    (concat x y).length = x.length + y.length :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: first case in `defn:concat-tuple`.

Informal statement: on the left embedded domain, concatenation agrees with the
left tuple.
-/
@[simp]
theorem concat_left (x y : Tuple X) (i : Fin x.length) :
    Tuple.entry (concat x y) (Fin.castAdd y.length i) = Tuple.entry x i := by
  cases x with
  | mk n f =>
      cases y with
      | mk m g =>
          simp [concat, Tuple.entry]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: second case in `defn:concat-tuple`.

Informal statement: on the right embedded domain, concatenation agrees with the
right tuple.
-/
@[simp]
theorem concat_right (x y : Tuple X) (i : Fin y.length) :
    Tuple.entry (concat x y) (Fin.natAdd x.length i) = Tuple.entry y i := by
  cases x with
  | mk n f =>
      cases y with
      | mk m g =>
          simp [concat, Tuple.entry]

/-! ## Sorted Addition -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `defn:sorted-tuple-add`.

Informal statement: sorted addition is concatenation followed by a fixed
sorting rule.

Lean strategy / thesis relation note: the thesis writes the codomain as
`\mathscr{S}(X,\preceq)`. Lean uses the subtype `SortedTuple X`, so the
sortedness proof is carried by the return value.
-/
def sortedAdd [Preorder X] (varsigma : SortingRule X) (x y : Tuple X) :
    SortedTuple X :=
  varsigma.toSortedTuple (concat x y)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: defining equation in `defn:sorted-tuple-add`.

Informal statement: the underlying tuple of `x + y` is the chosen sorting of
`x ⊕ y`.
-/
@[simp]
theorem sortedAdd_val [Preorder X] (varsigma : SortingRule X) (x y : Tuple X) :
    (sortedAdd varsigma x y).1 = varsigma.sort (concat x y) :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: codomain assertion in `defn:sorted-tuple-add`.

Informal statement: sorted addition produces a sorted tuple.
-/
theorem sortedAdd_isSorted [Preorder X] (varsigma : SortingRule X) (x y : Tuple X) :
    IsSorted (sortedAdd varsigma x y).1 :=
  (sortedAdd varsigma x y).2

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: sorting-rule dependence in `defn:sorted-tuple-add`.

Informal statement: the result of sorted addition is a finite permutation of
the concatenated tuple.
-/
theorem sortedAdd_exists_sortingPermutation [Preorder X]
    (varsigma : SortingRule X) (x y : Tuple X) :
    ∃ π : SortingPermutations (concat x y),
      (sortedAdd varsigma x y).1 = permute (concat x y) π.1 :=
  varsigma.exists_sortingPermutation (concat x y)

/-! ## Multiplicity Machinery for Sorted Addition -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: multiplicity expression `N_a(z)`.

Informal statement: the entries of a tuple as an ordered list, using the
tuple's finite domain order.

Lean strategy / thesis relation note: this is a proof device. The thesis works directly with
multiplicities on tuple domains; Lean first packages the finite entries as a
list, then passes to a multiset below.
-/
def tupleList (x : Tuple X) : List X :=
  List.ofFn fun i : Fin x.length => Tuple.entry x i

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: multiplicity expression `N_a(z)`.

Informal statement: the entries of a tuple as a multiset, forgetting order but
remembering multiplicity.
-/
def tupleMultiset (x : Tuple X) : Multiset X :=
  tupleList x

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: auxiliary length fact behind `N_a(z)`.

Informal statement: the list of entries has the same length as the tuple.
-/
@[simp]
theorem tupleList_length (x : Tuple X) : (tupleList x).length = x.length := by
  cases x
  simp [tupleList, Tuple.length]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: empty tuple multiplicity fact.

Informal statement: the empty tuple has no entries.
-/
@[simp]
theorem tupleList_empty : tupleList (Tuple.empty X) = [] :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: empty tuple multiplicity fact.

Informal statement: the empty tuple has zero entry multiset.
-/
@[simp]
theorem tupleMultiset_empty : tupleMultiset (Tuple.empty X) = 0 :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: tuple equality from ordered entries.

Informal statement: two Lean tuples are equal when their ordered entry lists
are equal.
-/
theorem tuple_eq_of_tupleList_eq {x y : Tuple X} (h : tupleList x = tupleList y) :
    x = y := by
  cases x with
  | mk n f =>
      cases y with
      | mk m g =>
          have hlen : n = m := by
            simpa [tupleList, Tuple.length] using congrArg List.length h
          subst m
          congr
          exact List.ofFn_inj.mp (by
            simpa [tupleList, Tuple.length, Tuple.entry] using h)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: sorted tuple uniqueness ingredient.

Informal statement: a thesis-sorted tuple over a linear order gives a sorted
Lean list of entries.
-/
theorem tupleList_sortedLE [LinearOrder X] {x : Tuple X} (hx : IsSorted x) :
    (tupleList x).SortedLE := by
  cases x with
  | mk n f =>
      rw [List.sortedLE_iff_pairwise, List.pairwise_iff_getElem]
      intro i j hi hj hij
      have hi' : i < n := by
        simpa [tupleList, Tuple.length] using hi
      have hj' : j < n := by
        simpa [tupleList, Tuple.length] using hj
      have hfin : (⟨i, hi'⟩ : Fin n) ≤ ⟨j, hj'⟩ := by
        simpa using (Nat.le_of_lt hij)
      have hle : f ⟨i, hi'⟩ ≤ f ⟨j, hj'⟩ :=
        le_of_not_gt (hx ⟨i, hi'⟩ ⟨j, hj'⟩ hfin)
      simpa [tupleList, Tuple.entry] using hle

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: "Since both are sorted in the same total order, equality of
all multiplicities implies equality."

Informal statement: sorted tuples over a linear order are determined by their
entry multisets.
-/
theorem sortedTuple_eq_of_tupleMultiset_eq [LinearOrder X]
    {x y : Tuple X} (hx : IsSorted x) (hy : IsSorted y)
    (h : tupleMultiset x = tupleMultiset y) : x = y := by
  have hperm : (tupleList x).Perm (tupleList y) := by
    exact Multiset.coe_eq_coe.mp (by
      simpa [tupleMultiset] using h)
  exact tuple_eq_of_tupleList_eq
    (hperm.eq_of_sortedLE (tupleList_sortedLE hx) (tupleList_sortedLE hy))

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: "concatenation adds multiplicities."

Informal statement: the ordered entries of `x ⊕ y` are the entries of `x`
followed by the entries of `y`.
-/
@[simp]
theorem tupleList_concat (x y : Tuple X) :
    tupleList (concat x y) = tupleList x ++ tupleList y := by
  cases x with
  | mk n f =>
      cases y with
      | mk m g =>
          simp [tupleList, concat, Tuple.length, Tuple.entry]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: `N_a(x + y) = N_a(x) + N_a(y)`, concatenation part.

Informal statement: concatenating tuples adds their entry multisets.
-/
theorem tupleMultiset_concat (x y : Tuple X) :
    tupleMultiset (concat x y) = tupleMultiset x + tupleMultiset y := by
  change (tupleList (concat x y) : Multiset X) =
    (tupleList x : Multiset X) + (tupleList y : Multiset X)
  rw [tupleList_concat]
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: "sorting does not change multiplicities."

Informal statement: permuting a tuple preserves its entry multiset.
-/
theorem tupleMultiset_permute (x : Tuple X) (π : FinitePermutation x.length) :
    tupleMultiset (permute x π) = tupleMultiset x := by
  cases x with
  | mk n f =>
      change (List.ofFn (fun i : Fin n => f (π i)) : Multiset X) =
        (List.ofFn f : Multiset X)
      exact Multiset.coe_eq_coe.mpr (by
        simpa [Function.comp_def] using
          (Equiv.Perm.ofFn_comp_perm π f))

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: "sorting does not change multiplicities."

Informal statement: applying a sorting rule preserves the entry multiset.
-/
theorem tupleMultiset_sort [Preorder X] (varsigma : SortingRule X) (x : Tuple X) :
    tupleMultiset (varsigma.sort x) = tupleMultiset x := by
  rcases varsigma.exists_perm x with ⟨π, hπ⟩
  rw [hπ]
  exact tupleMultiset_permute x π

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: `N_a(x + y) = N_a(x) + N_a(y)`.

Informal statement: sorted addition adds entry multisets.
-/
theorem tupleMultiset_sortedAdd [Preorder X]
    (varsigma : SortingRule X) (x y : Tuple X) :
    tupleMultiset (sortedAdd varsigma x y).1 =
      tupleMultiset x + tupleMultiset y := by
  change tupleMultiset (varsigma.sort (concat x y)) =
    tupleMultiset x + tupleMultiset y
  rw [tupleMultiset_sort, tupleMultiset_concat]

/-! ## Sorted Addition on the Sorted Tuple Space -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proposition
`prop:tuple-monoid`.

Original label: identity element in `property:identity`.

Informal statement: the empty sorted tuple is the identity candidate for the
sorted tuple space.
-/
def sortedEmpty [Preorder X] : SortedTuple X :=
  ⟨Tuple.empty X, empty_isSorted⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proposition
`prop:tuple-monoid`.

Original label: restriction of `defn:sorted-tuple-add` to sorted tuples.

Informal statement: sorted addition as a binary operation on the sorted tuple
space.
-/
def sortedAddOn [Preorder X] (varsigma : SortingRule X)
    (x y : SortedTuple X) : SortedTuple X :=
  sortedAdd varsigma x.1 y.1

/-!
Proof-match note for `prop:tuple-monoid`: the thesis packages the sorted tuple
space as a commutative cancellative monoid. Lean records the algebraic laws as
named theorems below because the operation is parameterized by the chosen
sorting rule `varsigma`; installing a global typeclass instance would hide
that parameter. The proof content is still the thesis multiplicity argument.
-/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proof of
`prop:tuple-monoid`.

Original label: `N_a(x + y) = N_a(x) + N_a(y)` restricted to sorted tuples.

Informal statement: sorted addition on the sorted tuple space adds entry
multisets.
-/
theorem tupleMultiset_sortedAddOn [Preorder X]
    (varsigma : SortingRule X) (x y : SortedTuple X) :
    tupleMultiset (sortedAddOn varsigma x y).1 =
      tupleMultiset x.1 + tupleMultiset y.1 :=
  tupleMultiset_sortedAdd varsigma x.1 y.1

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proposition
`prop:tuple-monoid`.

Original label: `property:associative`.

Informal statement: sorted tuple addition is associative on sorted tuples.
-/
theorem sortedAddOn_assoc [LinearOrder X] (varsigma : SortingRule X)
    (x y z : SortedTuple X) :
    sortedAddOn varsigma (sortedAddOn varsigma x y) z =
      sortedAddOn varsigma x (sortedAddOn varsigma y z) := by
  apply Subtype.ext
  apply sortedTuple_eq_of_tupleMultiset_eq
  · exact (sortedAddOn varsigma (sortedAddOn varsigma x y) z).2
  · exact (sortedAddOn varsigma x (sortedAddOn varsigma y z)).2
  · calc
      tupleMultiset (sortedAddOn varsigma (sortedAddOn varsigma x y) z).1
          = tupleMultiset (sortedAddOn varsigma x y).1 + tupleMultiset z.1 :=
            tupleMultiset_sortedAddOn varsigma (sortedAddOn varsigma x y) z
      _ = (tupleMultiset x.1 + tupleMultiset y.1) + tupleMultiset z.1 := by
            rw [tupleMultiset_sortedAddOn]
      _ = tupleMultiset x.1 + (tupleMultiset y.1 + tupleMultiset z.1) := by
            rw [Multiset.add_assoc]
      _ = tupleMultiset x.1 + tupleMultiset (sortedAddOn varsigma y z).1 := by
            rw [tupleMultiset_sortedAddOn]
      _ = tupleMultiset (sortedAddOn varsigma x (sortedAddOn varsigma y z)).1 :=
            (tupleMultiset_sortedAddOn varsigma x (sortedAddOn varsigma y z)).symm

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proposition
`prop:tuple-monoid`.

Original label: `property:identity`.

Informal statement: the empty sorted tuple is a right identity for sorted
addition.
-/
theorem sortedAddOn_empty_right [LinearOrder X] (varsigma : SortingRule X)
    (x : SortedTuple X) :
    sortedAddOn varsigma x (sortedEmpty (X := X)) = x := by
  apply Subtype.ext
  apply sortedTuple_eq_of_tupleMultiset_eq
  · exact (sortedAddOn varsigma x (sortedEmpty (X := X))).2
  · exact x.2
  · calc
      tupleMultiset (sortedAddOn varsigma x (sortedEmpty (X := X))).1
          = tupleMultiset x.1 + tupleMultiset (Tuple.empty X) :=
            tupleMultiset_sortedAdd varsigma x.1 (Tuple.empty X)
      _ = tupleMultiset x.1 := by simp

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proposition
`prop:tuple-monoid`.

Original label: `property:identity`.

Informal statement: the empty sorted tuple is a left identity for sorted
addition.
-/
theorem sortedAddOn_empty_left [LinearOrder X] (varsigma : SortingRule X)
    (x : SortedTuple X) :
    sortedAddOn varsigma (sortedEmpty (X := X)) x = x := by
  apply Subtype.ext
  apply sortedTuple_eq_of_tupleMultiset_eq
  · exact (sortedAddOn varsigma (sortedEmpty (X := X)) x).2
  · exact x.2
  · calc
      tupleMultiset (sortedAddOn varsigma (sortedEmpty (X := X)) x).1
          = tupleMultiset (Tuple.empty X) + tupleMultiset x.1 :=
            tupleMultiset_sortedAdd varsigma (Tuple.empty X) x.1
      _ = tupleMultiset x.1 := by simp

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proposition
`prop:tuple-monoid`.

Original label: `property:commutative`.

Informal statement: sorted tuple addition is commutative on sorted tuples.
-/
theorem sortedAddOn_comm [LinearOrder X] (varsigma : SortingRule X)
    (x y : SortedTuple X) :
    sortedAddOn varsigma x y = sortedAddOn varsigma y x := by
  apply Subtype.ext
  apply sortedTuple_eq_of_tupleMultiset_eq
  · exact (sortedAddOn varsigma x y).2
  · exact (sortedAddOn varsigma y x).2
  · calc
      tupleMultiset (sortedAddOn varsigma x y).1
          = tupleMultiset x.1 + tupleMultiset y.1 :=
            tupleMultiset_sortedAdd varsigma x.1 y.1
      _ = tupleMultiset y.1 + tupleMultiset x.1 := Multiset.add_comm _ _
      _ = tupleMultiset (sortedAddOn varsigma y x).1 := by
            rw [tupleMultiset_sortedAddOn]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proposition
`prop:tuple-monoid`.

Original label: `property:right-cancel`.

Informal statement: sorted tuple addition has right cancellation.
-/
theorem sortedAddOn_right_cancel [LinearOrder X] (varsigma : SortingRule X)
    {x x' y : SortedTuple X}
    (h : sortedAddOn varsigma x y = sortedAddOn varsigma x' y) :
    x = x' := by
  apply Subtype.ext
  have hmulti :
      tupleMultiset x.1 + tupleMultiset y.1 =
        tupleMultiset x'.1 + tupleMultiset y.1 := by
    have hcongr := congrArg (fun z : SortedTuple X => tupleMultiset z.1) h
    simpa [tupleMultiset_sortedAddOn] using hcongr
  exact sortedTuple_eq_of_tupleMultiset_eq x.2 x'.2 (add_right_cancel hmulti)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, proposition
`prop:tuple-monoid`.

Original label: `property:left-cancel`.

Informal statement: sorted tuple addition has left cancellation.
-/
theorem sortedAddOn_left_cancel [LinearOrder X] (varsigma : SortingRule X)
    {x y y' : SortedTuple X}
    (h : sortedAddOn varsigma x y = sortedAddOn varsigma x y') :
    y = y' := by
  apply Subtype.ext
  have hmulti :
      tupleMultiset x.1 + tupleMultiset y.1 =
        tupleMultiset x.1 + tupleMultiset y'.1 := by
    have hcongr := congrArg (fun z : SortedTuple X => tupleMultiset z.1) h
    simpa [tupleMultiset_sortedAddOn] using hcongr
  exact sortedTuple_eq_of_tupleMultiset_eq y.2 y'.2 (add_left_cancel hmulti)

/-! ## Pairing -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `defn:pairing`.

Informal statement: a finite set in a totally ordered space can be enumerated
as an increasing tuple.

Lean strategy / thesis relation note: the thesis defines the pairing recursively by repeated minima.
Lean uses mathlib's `Finset.orderEmbOfFin`, which is exactly the increasing
enumeration of a finite set in a linear order.

Lean strategy / thesis strategy note: the range theorem `pairing_range_eq` below records the
surjectivity half of the enumeration, making explicit that the pairing lists
every element of the finite set, not just elements drawn from it.
-/
noncomputable def pairing [LinearOrder X] (xi : FiniteSubsets X) : Tuple X :=
  let s := FiniteSubsets.toFinset xi
  ⟨s.card, fun i => s.orderEmbOfFin rfl i⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: cardinality/domain assertion in `defn:pairing`.

Informal statement: the pairing of a finite set has length equal to the set's
cardinality.
-/
@[simp]
theorem pairing_length [LinearOrder X] (xi : FiniteSubsets X) :
    (pairing xi).length = (FiniteSubsets.toFinset xi).card :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: corollary following `defn:pairing`.

Informal statement: the pairing tuple is sorted.
-/
theorem pairing_isSorted [LinearOrder X] (xi : FiniteSubsets X) :
    IsSorted (pairing xi) := by
  rw [isSorted_iff_monotone]
  intro i j hij
  exact (FiniteSubsets.toFinset xi).orderEmbOfFin rfl |>.monotone hij

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: range property implicit in `defn:pairing`.

Informal statement: every entry of the pairing belongs to the finite set being
enumerated.
-/
theorem pairing_entry_mem [LinearOrder X] (xi : FiniteSubsets X)
    (i : Fin (pairing xi).length) :
    Tuple.entry (pairing xi) i ∈ (xi : Set X) := by
  change (FiniteSubsets.toFinset xi).orderEmbOfFin rfl i ∈ (xi : Set X)
  exact (FiniteSubsets.mem_toFinset xi).mp
    ((FiniteSubsets.toFinset xi).orderEmbOfFin_mem rfl i)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: full enumeration property implicit in `defn:pairing`.

Informal statement: the entries of the pairing tuple are exactly the finite set
being paired.

Lean strategy / thesis relation note: this is the range statement for mathlib's increasing
enumeration `Finset.orderEmbOfFin`, translated back from the representative
`Finset` to the thesis finite-subset type.
-/
theorem pairing_range_eq [LinearOrder X] (xi : FiniteSubsets X) :
    Set.range (fun i : Fin (pairing xi).length =>
      Tuple.entry (pairing xi) i) = (xi : Set X) := by
  ext x
  change x ∈ Set.range ((FiniteSubsets.toFinset xi).orderEmbOfFin rfl) ↔
    x ∈ (xi : Set X)
  rw [Finset.range_orderEmbOfFin]
  exact FiniteSubsets.mem_toFinset xi

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: existence direction implicit in `defn:pairing`.

Informal statement: every element of the finite set appears at some index of
its pairing tuple.
-/
theorem exists_pairing_entry_eq_of_mem [LinearOrder X] (xi : FiniteSubsets X)
    {x : X} (hx : x ∈ (xi : Set X)) :
    ∃ i : Fin (pairing xi).length, Tuple.entry (pairing xi) i = x := by
  have hxrange :
      x ∈ Set.range (fun i : Fin (pairing xi).length =>
        Tuple.entry (pairing xi) i) := by
    rw [pairing_range_eq]
    exact hx
  simpa [Set.mem_range] using hxrange

/-! ## Reindexing and Cancellation -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: auxiliary domain object for `defn:reindex`.

Informal statement: the natural-number domain of a tuple is the finite set of
indices below its length.

Lean strategy / thesis relation note: the thesis uses `{1, ..., l(x)}`; Lean uses zero-based
`{n | n < x.length}`.
-/
def tupleDomain (x : Tuple X) : FiniteSubsets ℕ :=
  ⟨(Finset.range x.length : Set ℕ), Finset.finite_toSet _⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: domain membership used in `defn:reindex`.

Informal statement: a natural number belongs to the tuple domain iff it is
below the tuple length.
-/
theorem mem_tupleDomain (x : Tuple X) {n : ℕ} :
    n ∈ (tupleDomain x : Set ℕ) ↔ n < x.length := by
  simp [tupleDomain]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: finite-set intersection used in `defn:reindex`.

Informal statement: intersection of finite index sets is finite.
-/
def finiteSubsetInter {A : Type u} (s t : FiniteSubsets A) : FiniteSubsets A :=
  ⟨(s : Set A) ∩ (t : Set A), s.2.subset Set.inter_subset_left⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: finite-set difference used in `defn:cancel`.

Informal statement: difference of finite index sets is finite.
-/
def finiteSubsetDiff {A : Type u} (s t : FiniteSubsets A) : FiniteSubsets A :=
  ⟨(s : Set A) \ (t : Set A), s.2.subset Set.diff_subset⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `defn:reindex`.

Informal statement: restrict a tuple to a finite set of surviving natural
indices, intersect with the tuple's domain, then compress the surviving
indices back to an initial finite domain.

Lean strategy / thesis relation note: compression is implemented by applying the pairing map to the
finite subset of surviving indices. Since the paired indices lie in
`tupleDomain x`, Lean can construct the required `Fin x.length` index.
-/
noncomputable def reindex (x : Tuple X) (eta : FiniteSubsets ℕ) : Tuple X :=
  let kept := finiteSubsetInter eta (tupleDomain x)
  let p := pairing kept
  ⟨p.length, fun i =>
    let n := Tuple.entry p i
    have hn : n < x.length := by
      have hmem : n ∈ (kept : Set ℕ) := pairing_entry_mem kept i
      exact (mem_tupleDomain x).mp hmem.2
    Tuple.entry x ⟨n, hn⟩⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `defn:reindex`.

Informal statement: the length of a reindexed tuple is the number of surviving
indices after intersecting with the original tuple domain.
-/
@[simp]
theorem reindex_length (x : Tuple X) (eta : FiniteSubsets ℕ) :
    (reindex x eta).length =
      (FiniteSubsets.toFinset (finiteSubsetInter eta (tupleDomain x))).card :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: subsequence step behind `cor:cancel-closure-sorted`.

Informal statement: reindexing a sorted tuple along any finite index set keeps
the remaining entries sorted, because the surviving indices are paired in
increasing order.
-/
theorem reindex_isSorted [LinearOrder X] {x : Tuple X} (hx : IsSorted x)
    (eta : FiniteSubsets ℕ) :
    IsSorted (reindex x eta) := by
  rw [isSorted_iff_monotone] at hx ⊢
  intro i j hij
  let kept := finiteSubsetInter eta (tupleDomain x)
  let p := pairing kept
  have hpmono : ∀ i j : Fin p.length, i ≤ j → Tuple.entry p i ≤ Tuple.entry p j :=
    (isSorted_iff_monotone p).mp (pairing_isSorted kept)
  unfold reindex
  simp only [Tuple.entry, Tuple.length]
  exact hx _ _ (hpmono i j hij)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `defn:cancel`.

Informal statement: cancellation removes the requested finite set of indices
from the tuple domain and then reindexes the survivors.
-/
noncomputable def cancel (x : Tuple X) (eta : FiniteSubsets ℕ) : Tuple X :=
  reindex x (finiteSubsetDiff (tupleDomain x) eta)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: length consequence of `defn:cancel`.

Informal statement: cancellation has the length of the surviving finite index
set.
-/
@[simp]
theorem cancel_length (x : Tuple X) (eta : FiniteSubsets ℕ) :
    (cancel x eta).length =
      (FiniteSubsets.toFinset
        (finiteSubsetInter (finiteSubsetDiff (tupleDomain x) eta)
          (tupleDomain x))).card :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: closure step behind `cor:cancel-closure-sorted`.

Informal statement: cancelling indices from a sorted tuple leaves a sorted
tuple.
-/
theorem cancel_isSorted [LinearOrder X] {x : Tuple X} (hx : IsSorted x)
    (eta : FiniteSubsets ℕ) :
    IsSorted (cancel x eta) := by
  exact reindex_isSorted hx (finiteSubsetDiff (tupleDomain x) eta)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `defn:sorted-cancel`.

Informal statement: sorted cancellation is cancellation followed by the fixed
sorting rule.
-/
noncomputable def sortedCancel [Preorder X] (varsigma : SortingRule X)
    (x : Tuple X) (eta : FiniteSubsets ℕ) : SortedTuple X :=
  varsigma.toSortedTuple (cancel x eta)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: codomain assertion in `defn:sorted-cancel`.

Informal statement: sorted cancellation produces a sorted tuple.
-/
theorem sortedCancel_isSorted [Preorder X] (varsigma : SortingRule X)
    (x : Tuple X) (eta : FiniteSubsets ℕ) :
    IsSorted (sortedCancel varsigma x eta).1 :=
  (sortedCancel varsigma x eta).2

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `cor:cancel-closure-sorted`.

Informal statement: for a sorted tuple in a total order, sorted cancellation
has the same underlying tuple as ordinary cancellation.

Lean strategy / thesis relation note: the thesis invokes idempotency/uniqueness of sorting on sorted
tuples. Lean proves this through the multiplicity theorem
`sortedTuple_eq_of_tupleMultiset_eq`: `cancel x eta` is already sorted, and
any sorting rule returns a sorted permutation of it.
-/
theorem sortedCancel_eq_cancel [LinearOrder X] (varsigma : SortingRule X)
    {x : Tuple X} (hx : IsSorted x) (eta : FiniteSubsets ℕ) :
    (sortedCancel varsigma x eta).1 = cancel x eta := by
  apply sortedTuple_eq_of_tupleMultiset_eq
  · exact (sortedCancel varsigma x eta).2
  · exact cancel_isSorted hx eta
  · change tupleMultiset (varsigma.sort (cancel x eta)) =
      tupleMultiset (cancel x eta)
    exact tupleMultiset_sort varsigma (cancel x eta)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `cor:cancel-closure-sorted`.

Informal statement: as an equality in the sorted-tuple subtype, sorted
cancellation is ordinary cancellation equipped with its sortedness proof.
-/
theorem sortedCancel_eq_cancelSubtype [LinearOrder X] (varsigma : SortingRule X)
    {x : Tuple X} (hx : IsSorted x) (eta : FiniteSubsets ℕ) :
    sortedCancel varsigma x eta = ⟨cancel x eta, cancel_isSorted hx eta⟩ := by
  apply Subtype.ext
  exact sortedCancel_eq_cancel varsigma hx eta

/-! ## Modification -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: auxiliary value choice for `defn:modification`.

Informal statement: if the distinct finite modification set contains a
replacement at index `n`, use it; otherwise keep the default value.

Lean strategy / thesis relation note: uniqueness of the replacement value is supplied by the
`DistinctFiniteSubsets` invariant.
-/
noncomputable def modificationValue (xi : DistinctFiniteSubsets X) (n : ℕ)
    (default : X) : X := by
  classical
  exact
    if h : ∃ z : X, IndexAugmented.mk n z ∈ (xi.1 : Set (IndexAugmented X)) then
      Classical.choose h
    else
      default

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: first case in `defn:modification`.

Informal statement: if no replacement appears at an index, the modification
value is the default value.
-/
theorem modificationValue_eq_default_of_not_exists
    (xi : DistinctFiniteSubsets X) {n : ℕ} {default : X}
    (h : ¬ ∃ z : X, IndexAugmented.mk n z ∈ (xi.1 : Set (IndexAugmented X))) :
    modificationValue xi n default = default := by
  classical
  unfold modificationValue
  rw [dif_neg h]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: second case in `defn:modification`.

Informal statement: if the modification set contains `(n,z)`, then the value
chosen at index `n` is `z`.
-/
theorem modificationValue_eq_of_mem (xi : DistinctFiniteSubsets X)
    {n : ℕ} {z default : X}
    (hz : IndexAugmented.mk n z ∈ (xi.1 : Set (IndexAugmented X))) :
    modificationValue xi n default = z := by
  classical
  unfold modificationValue
  let h : ∃ w : X, IndexAugmented.mk n w ∈ (xi.1 : Set (IndexAugmented X)) :=
    ⟨z, hz⟩
  rw [dif_pos h]
  exact xi.value_eq_of_same_index (Classical.choose_spec h) hz

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: `defn:modification`.

Informal statement: modify an existing tuple by replacing entries whose
indices occur in a distinct finite modification set. Indices outside the tuple
domain are harmless, since the output tuple has the same domain as the input.
-/
noncomputable def modify (x : Tuple X) (xi : DistinctFiniteSubsets X) : Tuple X :=
  ⟨x.length, fun i => modificationValue xi i.1 (Tuple.entry x i)⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: domain assertion in `defn:modification`.

Informal statement: modification keeps the tuple length fixed.
-/
@[simp]
theorem modify_length (x : Tuple X) (xi : DistinctFiniteSubsets X) :
    (modify x xi).length = x.length :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: second case in `defn:modification`.

Informal statement: when a replacement at an input index exists, the modified
tuple has that replacement value at the same index.
-/
theorem modify_entry_of_mem (x : Tuple X) (xi : DistinctFiniteSubsets X)
    (i : Fin x.length) {z : X}
    (hz : IndexAugmented.mk i.1 z ∈ (xi.1 : Set (IndexAugmented X))) :
    Tuple.entry (modify x xi) i = z :=
  modificationValue_eq_of_mem xi hz

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: first case in `defn:modification`.

Informal statement: if no replacement exists at an input index, the modified
tuple agrees with the original tuple there.
-/
theorem modify_entry_of_not_exists (x : Tuple X) (xi : DistinctFiniteSubsets X)
    (i : Fin x.length)
    (h : ¬ ∃ z : X, IndexAugmented.mk i.1 z ∈
      (xi.1 : Set (IndexAugmented X))) :
    Tuple.entry (modify x xi) i = Tuple.entry x i :=
  modificationValue_eq_default_of_not_exists xi h

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: sorted part of `defn:modification`.

Informal statement: sorted modification is modification followed by the fixed
sorting rule.
-/
noncomputable def sortedModify [Preorder X] (varsigma : SortingRule X)
    (x : Tuple X) (xi : DistinctFiniteSubsets X) : SortedTuple X :=
  varsigma.toSortedTuple (modify x xi)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section "Primitive
Actions".

Original label: codomain assertion in `defn:modification`.

Informal statement: sorted modification produces a sorted tuple.
-/
theorem sortedModify_isSorted [Preorder X] (varsigma : SortingRule X)
    (x : Tuple X) (xi : DistinctFiniteSubsets X) :
    IsSorted (sortedModify varsigma x xi).1 :=
  (sortedModify varsigma x xi).2

end Primitive
end MarketActions
end Foundations
end Thesis
