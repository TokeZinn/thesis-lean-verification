import Mathlib.Order.WellFounded
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Order

/-!
# Preliminary set theory, relations, and functions

Typed counterparts of the custom formal blocks in
`A - preliminary theory/sets.tex`.  Lean's foundation is dependent type
theory rather than an untyped ZF universe.  Consequently, the ZF axioms below
are represented by their typed constructions, or (for Russell's argument and
Foundation) by the precise abstract membership hypotheses that the manuscript
uses. `ZFCFoundations` additionally proves the literal set-universe statements,
including set-coded functions and Kuratowski pairs; `SetConstructions` supplies
explicit bridges for non-strict well-orders and union-valued products.
No project-specific axiom is introduced.
-/

namespace Thesis.Foundations.Preliminary.SetTheory

universe u v w

/--
Original label: `axiom:existence`.

Informal statement: there exists a set.

Lean strategy / thesis relation note: for every ambient type, its empty subset
is already a set, so the typed analogue of existence is constructive.
-/
theorem setExistence (α : Type u) : ∃ x : Set α, x = x :=
  ⟨∅, rfl⟩

/--
Original label: `axiom:extensionality`.

Informal statement: two sets with exactly the same elements are equal.

Lean strategy / thesis relation note: this is Mathlib's extensionality theorem
for typed sets, applied directly to the pointwise membership equivalence.
-/
theorem setExtensionality {α : Type u} {x y : Set α}
    (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  Set.ext h

/--
Original label: `axiom:scheme-of-comprehension`.

Informal statement: a property cuts out a subset of any existing set.

Lean strategy / thesis relation note: Lean's set-builder notation is a predicate,
so restricted comprehension is the set whose predicate is membership in `z`
conjoined with `φ`; no new axiom is required.
-/
theorem separation {α : Type u} (z : Set α) (φ : α → Prop) :
    ∃ x : Set α, ∀ y, y ∈ x ↔ y ∈ z ∧ φ y :=
  ⟨{y | y ∈ z ∧ φ y}, fun _ => Iff.rfl⟩

/--
Original label: `prop:empty-set-unique`.

Informal statement: there exists a unique set having no elements.

Lean strategy / thesis relation note: typed restatement of the thesis argument.
Existence (`setExistence`) supplies a set `x`; Separation (`separation`) with
the formula `y ≠ y` cuts out of `x` a set with no elements; Extensionality
(`setExtensionality`) identifies any two sets with no elements, because both
membership predicates are everywhere false. The literal set-universe version is
`ZFC.unique_empty` in `ZFCFoundations`.
-/
theorem existsUniqueEmptySet (α : Type u) :
    ∃! x : Set α, ∀ z, z ∉ x := by
  obtain ⟨x, _⟩ := setExistence α
  obtain ⟨e, he⟩ := separation x (fun y => y ≠ y)
  have hempty : ∀ z, z ∉ e := fun z hz => ((he z).mp hz).2 rfl
  refine ⟨e, hempty, fun y hy => ?_⟩
  exact setExtensionality (fun z => iff_of_false (hy z) (hempty z))

/--
Original label: `defn:empty-set`.

Informal statement: `emptySet α` denotes the set with no elements of `α`.

Lean strategy / thesis relation note: the thesis notation `∅` is represented by
Mathlib's empty typed set and exposed under a descriptive bridge name.
-/
def emptySet (α : Type u) : Set α :=
  ∅

/--
Original label: `thm:no-universal-set`.

Informal statement: an untyped membership universe closed under separation
cannot contain an object that contains every object.

Lean strategy / thesis relation note: Lean has a typed universal subset
`Set.univ`, so the literal untyped ZF sentence would be false after naïve
translation.  We instead formalise the thesis's Russell proof over an abstract
self-membership relation and its separation principle; the diagonal object is
in itself exactly when it is not in itself.
-/
theorem noUniversalObjectOfSeparation {U : Type u} (mem : U → U → Prop)
    (separate : ∀ z : U, ∀ φ : U → Prop,
      ∃ x : U, ∀ y : U, mem y x ↔ mem y z ∧ φ y) :
    ¬ ∃ universal : U, ∀ x : U, mem x universal := by
  rintro ⟨universal, huniversal⟩
  obtain ⟨russell, hrussell⟩ := separate universal (fun x => ¬ mem x x)
  by_cases hself : mem russell russell
  · exact ((hrussell russell).mp hself).2 hself
  · exact hself ((hrussell russell).mpr ⟨huniversal russell, hself⟩)

/--
Original label: `axiom:foundation`.

Informal statement: every nonempty set has an element with no predecessor from
that set under membership.

Lean strategy / thesis relation note: the ZF membership relation is abstracted
as a well-founded relation `r`; `WellFounded.has_min` supplies precisely the
minimal element asserted by Foundation.
-/
theorem foundation {α : Type u} (r : α → α → Prop) (hr : WellFounded r)
    (x : Set α) (hx : x.Nonempty) :
    ∃ y ∈ x, ¬ ∃ z, z ∈ x ∧ r z y := by
  obtain ⟨y, hy, hminimal⟩ := hr.has_min x hx
  refine ⟨y, hy, ?_⟩
  rintro ⟨z, hz, hzy⟩
  exact hminimal z hz hzy

/--
Original label: `axiom:pairing`.

Informal statement: for any two elements there is a set containing exactly
those two elements.

Lean strategy / thesis relation note: the pair set `{x, y}` is a primitive
finite-set notation in Mathlib, and simplification proves its membership law.
-/
theorem pairing {α : Type u} (x y : α) :
    ∃ z : Set α, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  refine ⟨{x, y}, ?_⟩
  intro w
  simp

/--
Original label: `axiom:union`.

Informal statement: a family of sets has a union containing exactly the
elements that occur in one of its members.

Lean strategy / thesis relation note: the witness is the typed predicate
`x ↦ ∃ X ∈ F, x ∈ X`, which is Mathlib's set-theoretic union construction.
-/
theorem unionFamily {α : Type u} (F : Set (Set α)) :
    ∃ U : Set α, ∀ x, x ∈ U ↔ ∃ X ∈ F, x ∈ X :=
  ⟨{x | ∃ X ∈ F, x ∈ X}, fun _ => Iff.rfl⟩

/--
Original label: `defn:product-space`.

Informal statement: the product space consists of the ordered pairs whose first
coordinate is in `X` and whose second coordinate is in `Y`.

Lean strategy / thesis relation note: Lean uses its typed ordered-pair type
instead of the Kuratowski encoding; Mathlib's set product has the same
membership condition used throughout the thesis.
-/
def productSpace {α : Type u} {β : Type v} (X : Set α) (Y : Set β) :
    Set (α × β) :=
  X ×ˢ Y

/--
Original label: `defn:relation`.

Informal statement: a relation from `X` to `Y` is a subset of `X × Y`, with a
domain and range obtained by existential projection.

Lean strategy / thesis relation note: the graph and its subset certificate are
bundled; the definitions `Relation.domain` and `Relation.range` below implement
the two projections in the displayed thesis formulas.
-/
structure Relation {α : Type u} {β : Type v} (X : Set α) (Y : Set β) where
  graph : Set (α × β)
  graph_subset : graph ⊆ productSpace X Y

namespace Relation

def domain {α : Type u} {β : Type v} {X : Set α} {Y : Set β}
    (R : Relation X Y) : Set α :=
  {x | x ∈ X ∧ ∃ y ∈ Y, (x, y) ∈ R.graph}

def range {α : Type u} {β : Type v} {X : Set α} {Y : Set β}
    (R : Relation X Y) : Set β :=
  {y | y ∈ Y ∧ ∃ x ∈ X, (x, y) ∈ R.graph}

end Relation

/--
Original label: `defn:equivalence-relation`.

Informal statement: an equivalence relation on `X` is supported on `X × X` and
is reflexive, symmetric, and transitive there.

Lean strategy / thesis relation note: each of the three thesis clauses is
recorded explicitly, together with the subset-of-product condition implicit in
the manuscript's notation `∼ ⊆ X × X`.
-/
def IsEquivalenceRelationOn {α : Type u} (X : Set α) (r : α → α → Prop) : Prop :=
  (∀ ⦃x y⦄, r x y → x ∈ X ∧ y ∈ X) ∧
  (∀ x ∈ X, r x x) ∧
  (∀ x ∈ X, ∀ y ∈ X, r x y ↔ r y x) ∧
  (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z)

/--
Original label: `defn:equivalence-class`.

Informal statement: the equivalence class of `x` contains the elements of `X`
related to `x`; the quotient is the collection of all such classes.

Lean strategy / thesis relation note: the class is a set-builder predicate,
while `equivalenceClassSpace` below takes its range over representatives in
`X`, matching the two displayed constructions in the thesis.
-/
def equivalenceClass {α : Type u} (X : Set α) (r : α → α → Prop)
    (x : α) : Set α :=
  {x' | x' ∈ X ∧ r x' x}

def equivalenceClassSpace {α : Type u} (X : Set α) (r : α → α → Prop) :
    Set (Set α) :=
  {C | ∃ x ∈ X, C = equivalenceClass X r x}

/--
Original label: `defn:function`.

Informal statement: a function from the set `X` to the set `Y` assigns exactly
one element of `Y` to each element of `X`.

Lean strategy / thesis relation note: the subtype function type `X → Y`
builds totality, uniqueness, and codomain membership into the type itself.
-/
abbrev FunctionBetween {α : Type u} {β : Type v} (X : Set α) (Y : Set β) :=
  X → Y

/--
Original label: `defn:graph`.

Informal statement: the graph of a function is the set of ordered pairs
`(x, f x)`.

Lean strategy / thesis relation note: the graph is represented as the predicate
on subtype pairs whose second coordinate equals the function value.
-/
def graph {α : Type u} {β : Type v} {X : Set α} {Y : Set β}
    (f : FunctionBetween X Y) : Set (X × Y) :=
  {p | p.2 = f p.1}

/--
Original label: `prop:graph-defines`.

Informal statement: a function is completely determined by its graph.

Lean strategy / thesis relation note: functions and graphs have different
types in Lean, so the thesis's set-theoretic equality becomes injectivity of
the graph construction; the proof evaluates graph equality at `(x, f x)`.
-/
theorem graph_injective {α : Type u} {β : Type v} {X : Set α} {Y : Set β} :
    Function.Injective (fun f : FunctionBetween X Y => graph f) := by
  intro f g hgraph
  change graph f = graph g at hgraph
  funext x
  have hx : (x, f x) ∈ graph g := by
    rw [← hgraph]
    rfl
  exact hx

/--
Original label: `prop:empty-domain-function`.

Informal statement: functions with empty domain have the same empty graph,
even when their codomains differ.

Lean strategy / thesis relation note: equality of differently typed functions
is not a well-formed Lean proposition.  Both graphs are therefore embedded in
the common codomain sum; their ranges are equal because an `Empty` input cannot
exist, which is the graph argument used in the thesis proof.
-/
theorem emptyDomainFunctionsHaveEqualGraphs {β : Type v} {γ : Type w}
    (f : Empty → β) (g : Empty → γ) :
    Set.range (fun x : Empty => (x, @Sum.inl β γ (f x))) =
      Set.range (fun x : Empty => (x, @Sum.inr β γ (g x))) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact Empty.elim x
  · rintro ⟨x, rfl⟩
    exact Empty.elim x

/--
Original label: `axiom:replacement`.

Informal statement: the outputs assigned uniquely to the elements of `X` form
a set.

Lean strategy / thesis relation note: dependent type theory already permits
the image predicate `{y | ∃ x ∈ X, φ x y}`; the functional premise is retained
to match the thesis scheme, but no additional axiom is needed to form the set.
-/
theorem replacement {α : Type u} {β : Type v} (X : Set α) (φ : α → β → Prop)
    (_hfunctional : ∀ x ∈ X, ∃! y, φ x y) :
    ∃ Y : Set β, ∀ y, y ∈ Y ↔ ∃ x ∈ X, φ x y :=
  ⟨{y | ∃ x ∈ X, φ x y}, fun _ => Iff.rfl⟩

/--
Original label: `axiom:infinity`.

Informal statement: there is a set containing zero and closed under successor,
and hence an infinite set.

Lean strategy / thesis relation note: the natural-number type is primitive in
Lean; its universal subset witnesses the inductive-set formulation used by the
thesis and is closed under `n ↦ n + 1`.
-/
theorem infinity :
    ∃ X : Set ℕ, 0 ∈ X ∧ ∀ n ∈ X, n + 1 ∈ X := by
  refine ⟨Set.univ, ?_, ?_⟩
  · simp
  · simp

/--
Original label: `defn:subset`.

Informal statement: `Y` is a subset of `X` when membership in `Y` implies
membership in `X`; it is strict when some element of `X` is absent from `Y`.

Lean strategy / thesis relation note: `IsSubset` spells out Mathlib's `Y ⊆ X`
predicate, and `IsStrictSubset` below follows the thesis's explicit witness
formulation rather than relying only on notation.
-/
def IsSubset {α : Type u} (Y X : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ Y → x ∈ X

def IsStrictSubset {α : Type u} (Y X : Set α) : Prop :=
  IsSubset Y X ∧ ∃ x ∈ X, x ∉ Y

/--
Original label: `axiom:power-set`.

Informal statement: for every set `X`, the collection of all subsets of `X`
is itself a set.

Lean strategy / thesis relation note: a set of sets is a predicate on `Set α`;
restricted comprehension with predicate `Z ⊆ X` constructs the witness.
-/
theorem powerSetExistence {α : Type u} (X : Set α) :
    ∃ P : Set (Set α), ∀ Z, Z ∈ P ↔ Z ⊆ X :=
  ⟨{Z | Z ⊆ X}, fun _ => Iff.rfl⟩

/--
Original label: `defn:power-set`.

Informal statement: `powerSet X` is the set of all subsets of `X`.

Lean strategy / thesis relation note: this is the direct typed set-builder
version of the thesis notation `℘(X)`.
-/
def powerSet {α : Type u} (X : Set α) : Set (Set α) :=
  {Z | Z ⊆ X}

/--
Original label: `axiom:choice`.

Informal statement: every family of nonempty sets admits a function selecting
one member from each set.

Lean strategy / thesis relation note: each member of the family is represented
by a subtype element carrying its membership proof; `Classical.choose` selects
from the supplied nonemptiness proof.  This uses Lean's standard classical
choice principle, not a project-specific axiom.
-/
theorem choiceForFamily {α : Type u} (𝒳 : Set (Set α))
    (hne : ∀ A ∈ 𝒳, A.Nonempty) :
    ∃ f : 𝒳 → α, ∀ A : 𝒳, f A ∈ (A : Set α) := by
  classical
  let f : 𝒳 → α := fun A => Classical.choose (hne A.1 A.2)
  refine ⟨f, ?_⟩
  intro A
  exact Classical.choose_spec (hne A.1 A.2)

/--
Original label: `defn:ordered-sets`.

Informal statement: a partial order is reflexive, antisymmetric, and
transitive; totality compares distinct elements, and a well-order gives every
nonempty subset a least element.

Lean strategy / thesis relation note: `PartialOrderRelation` records the three
displayed axioms for an explicit relation.  The predicates `IsTotal` and
`IsWellOrdered` below add the manuscript's remaining clauses without changing
its order convention.
-/
structure PartialOrderRelation (α : Type u) where
  le : α → α → Prop
  refl : ∀ x, le x x
  antisymm : ∀ ⦃x y⦄, le x y → le y x → x = y
  trans : ∀ ⦃x y z⦄, le x y → le y z → le x z

namespace PartialOrderRelation

def IsTotal {α : Type u} (O : PartialOrderRelation α) : Prop :=
  ∀ x y, x ≠ y → O.le x y ∨ O.le y x

def IsWellOrdered {α : Type u} (O : PartialOrderRelation α) : Prop :=
  IsTotal O ∧ ∀ S : Set α, S.Nonempty → ∃ x ∈ S, ∀ y ∈ S, O.le x y

end PartialOrderRelation

/--
Original label: `thm:well-ordering`.

Informal statement: every set can be equipped with a well-order.

Lean strategy / thesis relation note: a thesis set is represented by its
subtype; Mathlib's `WellOrderingRel` supplies a well-founded strict total order
on every type, which is the standard type-theoretic well-ordering theorem.
-/
theorem wellOrderingTheorem (α : Type u) :
    ∃ r : α → α → Prop, IsWellOrder α r :=
  ⟨WellOrderingRel, inferInstance⟩

/--
Original label: `thm:zorns-lemma`.

Informal statement: if every chain in a partially ordered set has an upper
bound, then the set has a maximal element.

Lean strategy / thesis relation note: this is Mathlib's `zorn_le` with the
thesis hypotheses written using `IsChain`, `BddAbove`, and `IsMax` for the
ambient partial order.
-/
theorem zornsLemma {α : Type u} [PartialOrder α]
    (h : ∀ C : Set α, IsChain (· ≤ ·) C → BddAbove C) :
    ∃ maximal : α, IsMax maximal :=
  zorn_le h

/--
Original label: `defn:arbitrary-product-space`.

Informal statement: the arbitrary product of a family `(X i)` is the type of
choice functions whose `i`th value lies in `X i`.

Lean strategy / thesis relation note: returning an element of the subtype
`X i` enforces the displayed membership condition at every index, including
for dependent families.
-/
abbrev ArbitraryProduct {ι : Type u} {α : Type v} (X : ι → Set α) :=
  ∀ i, X i

def binaryFamily {α : Type u} (X Y : Set α) : Bool → Set α
  | false => X
  | true => Y

/--
Original label: `prop:binary-product-space`.

Informal statement: the binary Cartesian product is equivalent to the
two-index arbitrary product.

Lean strategy / thesis relation note: `Bool` is a two-element index type; the
equivalence sends a pair to the dependent function taking `false` to its first
coordinate and `true` to its second, with the inverse given by evaluation.
-/
def binaryProductEquiv {α : Type u} (X Y : Set α) :
    X × Y ≃ ArbitraryProduct (binaryFamily X Y) where
  toFun p
    | false => p.1
    | true => p.2
  invFun f := (f false, f true)
  left_inv _ := rfl
  right_inv f := by
    funext b
    cases b <;> rfl

/--
Original label: `defn:sequence`.

Informal statement: an `X`-sequence is a function from the natural numbers to
`X`, written `(xₙ)ₙ` instead of ordinary function notation.

Lean strategy / thesis relation note: a sequence in the thesis set `X` is the
function type `ℕ → X`, where the subtype codomain records membership in `X`.
-/
abbrev Sequence {α : Type u} (X : Set α) :=
  ℕ → X

end Thesis.Foundations.Preliminary.SetTheory
