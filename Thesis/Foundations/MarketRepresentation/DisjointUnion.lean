import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Market Representation: Disjoint Unions and Static Orders

Formalizes the first chunk of
`1 - theoretical foundations/2_chapter_market_representations.tex`.

This module covers:

* `defn:disjoint-union`;
* `prop:disjoint-isomorphism`;
* `prop:disjoint-product`, in the injective/product-map form natural in Lean;
* `prop:disjoint-partial-order`;
* `prop:disjoint-total-order`;
* `cor:strict-disjoint-total-order`;

Lean/type-theory note: a disjoint union is represented by the dependent sum
`Σ a, X a`. For families of subsets of one ambient type, `Σ a, S a` stores a
tag `a`, an element of the ambient type, and a proof of membership in `S a`.
-/

universe u v

namespace Thesis
namespace Foundations
namespace MarketRepresentation

/-- Thesis `defn:disjoint-union`.

The disjoint union of a family of types. This is Lean's native dependent sum
representation of `\bigsqcup_{\alpha \in A} X_\alpha`.
-/
abbrev DisjointUnion {A : Type u} (X : A → Type v) : Type (max u v) :=
  Sigma X

namespace DisjointUnion

variable {A : Type u} {X : A → Type v}

/-- The index/tag of an element of a disjoint union. -/
def tag (z : DisjointUnion X) : A :=
  z.1

/-- The component value of an element of a disjoint union. -/
def val (z : DisjointUnion X) : X z.tag :=
  z.2

@[simp]
theorem eta (z : DisjointUnion X) : Sigma.mk z.tag z.val = z := by
  cases z
  rfl

end DisjointUnion

/-- Thesis `prop:disjoint-isomorphism` assumption.

A family of subsets is pairwise disjoint when different tags cannot contain the
same ambient element. This is the typed version of
`X_α ∩ X_α' = ∅` for `α ≠ α'`.
-/
def PairwiseDisjoint {A : Type u} {β : Type v} (S : A → Set β) : Prop :=
  ∀ ⦃a b : A⦄, a ≠ b → ∀ ⦃x : β⦄, x ∈ S a → x ∈ S b → False


/-- Thesis `defn:disjoint-union`, subset-family version.

The disjoint union of a family of subsets of a common ambient type.
-/
abbrev SetDisjointUnion {A : Type u} {β : Type v} (S : A → Set β) : Type (max u v) :=
  Σ a, S a

namespace SetDisjointUnion

variable {A : Type u} {β : Type v} {S : A → Set β}

/-- Forget the tag and keep only the ambient element. -/
def forget (z : SetDisjointUnion S) : β :=
  z.2.1

/-- View a tagged element as an element of the ordinary union of the family. -/
def toUnion (z : SetDisjointUnion S) : {x : β // ∃ a, x ∈ S a} :=
  ⟨z.forget, z.1, z.2.2⟩

/-- Thesis `prop:disjoint-product`.

View a tagged element inside the product of the ordinary union and the index
set. This is the Lean version of
`\bigsqcup a, X a ⊆ (\bigcup a, X a) × A`.
-/
def toUnionProduct (z : SetDisjointUnion S) : {x : β // ∃ a, x ∈ S a} × A :=
  (z.toUnion, z.1)

/-- Thesis `prop:disjoint-product`.

The ordinary set-of-pairs representation of the disjoint union
`\bigcup a, S a × {a}`. In Lean this is the subset of `β × A` whose value
belongs to the component selected by its tag.
-/
def taggedUnionSet (S : A → Set β) : Set (β × A) :=
  {p | p.1 ∈ S p.2}

/-- Thesis `prop:disjoint-product`.

The product representation `(\bigcup a, S a) × A`, written as a subset of
`β × A`.
-/
def unionProductSet (S : A → Set β) : Set (β × A) :=
  {p | ∃ a, p.1 ∈ S a}

/-- Thesis `prop:disjoint-product`.

The set-of-pairs disjoint union is contained in the product of the ordinary
union and the index set.
-/
theorem taggedUnionSet_subset_unionProductSet :
    taggedUnionSet S ⊆ unionProductSet S := by
  intro p hp
  exact ⟨p.2, hp⟩

/-- Thesis `prop:disjoint-product`.

The set-of-pairs disjoint union equals the product representation exactly when
all component sets are equal.

Lean strategy / thesis relation note: this is the thesis' equality/iff clause expressed as equality
of subsets of the common ambient product `β × A`, while the typed object
`SetDisjointUnion S = Σ a, S a` remains Lean's safer internal representation.
-/
theorem taggedUnionSet_eq_unionProductSet_iff_all_components_equal :
    taggedUnionSet S = unionProductSet S ↔ ∀ a b, S a = S b := by
  constructor
  · intro h a b
    ext x
    constructor
    · intro hx
      have hp : (x, b) ∈ taggedUnionSet S := by
        rw [h]
        exact ⟨a, hx⟩
      exact hp
    · intro hx
      have hp : (x, a) ∈ taggedUnionSet S := by
        rw [h]
        exact ⟨b, hx⟩
      exact hp
  · intro h
    ext p
    constructor
    · intro hp
      exact taggedUnionSet_subset_unionProductSet (S := S) hp
    · rintro ⟨a, ha⟩
      simpa [taggedUnionSet, h a p.2] using ha

theorem toUnion_surjective : Function.Surjective (toUnion (S := S)) := by
  intro x
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨a, hx⟩
  refine ⟨⟨a, ⟨x, hx⟩⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem forget_injective_of_pairwiseDisjoint (hS : PairwiseDisjoint S) :
    Function.Injective (forget (S := S)) := by
  intro z w h
  cases z with
  | mk a x =>
    cases w with
    | mk b y =>
      cases x with
      | mk x hx =>
        cases y with
        | mk y hy =>
          dsimp [forget] at h
          subst y
          have hab : a = b := by
            by_contra hne
            exact hS hne hx hy
          subst b
          rfl

theorem toUnion_injective_of_pairwiseDisjoint (hS : PairwiseDisjoint S) :
    Function.Injective (toUnion (S := S)) := by
  intro z w h
  apply forget_injective_of_pairwiseDisjoint hS
  exact congrArg Subtype.val h

/-- Thesis `prop:disjoint-isomorphism`.

If the components are pairwise disjoint, the ordinary union and the disjoint
union are equivalent. Lean states "isomorphism of sets" as an `Equiv`.
-/
noncomputable def disjointUnion_equiv_union_of_pairwiseDisjoint (hS : PairwiseDisjoint S) :
    SetDisjointUnion S ≃ {x : β // ∃ a, x ∈ S a} :=
  Equiv.ofBijective (toUnion (S := S))
    ⟨toUnion_injective_of_pairwiseDisjoint hS, toUnion_surjective⟩

theorem toUnionProduct_injective :
    Function.Injective (toUnionProduct (S := S)) := by
  intro z w h
  cases z with
  | mk a x =>
    cases w with
    | mk b y =>
      cases x with
      | mk x hx =>
        cases y with
        | mk y hy =>
          dsimp [toUnionProduct, toUnion, forget] at h
          injection h with hmem htag
          subst b
          have hxy : x = y := congrArg Subtype.val hmem
          subst y
          rfl

/-- Thesis `prop:disjoint-product`.

The tagged product map is injective: keeping both the ordinary-union element
and the tag recovers the original disjoint-union element.
-/
theorem toUnionProduct_embedding_injective :
    Function.Injective (toUnionProduct (S := S)) :=
  toUnionProduct_injective (S := S)

end SetDisjointUnion

namespace DisjointUnion

variable {A : Type u} {X : A → Type v}

/-- Thesis `prop:disjoint-partial-order`.

The order on a disjoint union compares only elements with the same tag, using
the order from that component.

Instance note: `DisjointUnion X` is an `abbrev` for `Σ a, X a`, so this is a
global `LE` instance on every sigma type with ordered fibres. Mathlib's
`Mathlib.Data.Sigma.Order` declares a global disjoint-sum instance on the same
type (`Sigma.LE`, an inductive relation) that is logically equivalent
(`Sigma.le_def`) but not definitionally equal to this one. No project module
currently imports `Mathlib.Data.Sigma.Order` (checked over the import closure
of every module), so the two never coexist. If that import is ever added, make
`instLE`/`instPartialOrder` `scoped` and `open scoped` them where the
disjoint-union order is used.
-/
instance instLE [∀ a, LE (X a)] : LE (DisjointUnion X) where
  le z w := ∃ h : z.1 = w.1, (h ▸ z.2) ≤ w.2

@[simp]
theorem mk_le_mk_same [∀ a, LE (X a)] {a : A} {x y : X a} :
    (Sigma.mk a x : DisjointUnion X) ≤ Sigma.mk a y ↔ x ≤ y := by
  constructor
  · rintro ⟨h, hxy⟩
    cases h
    exact hxy
  · intro hxy
    exact ⟨rfl, hxy⟩

theorem not_le_of_ne [∀ a, LE (X a)] {a b : A} (h : a ≠ b) (x : X a) (y : X b) :
    ¬ (Sigma.mk a x : DisjointUnion X) ≤ Sigma.mk b y := by
  rintro ⟨hab, _⟩
  exact h hab

/-- Thesis `prop:disjoint-partial-order`.

Partial orders on each component induce a partial order on the disjoint union.

Instance note: see `instLE`; Mathlib's `Mathlib.Data.Sigma.Order` carries a
non-definitionally-equal global `PartialOrder (Σ i, α i)` on the same type,
which no project module imports.
-/
instance instPartialOrder [∀ a, PartialOrder (X a)] : PartialOrder (DisjointUnion X) where
  le := (· ≤ ·)
  lt z w := z ≤ w ∧ ¬ w ≤ z
  le_refl := by
    rintro ⟨a, x⟩
    exact ⟨rfl, le_rfl⟩
  le_trans := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ ⟨hab, hxy⟩ ⟨hbc, hyz⟩
    change a = b at hab
    change b = c at hbc
    subst b
    subst c
    exact ⟨rfl, le_trans hxy hyz⟩
  lt_iff_le_not_ge := by
    intro z w
    rfl
  le_antisymm := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨hab, hxy⟩ ⟨hba, hyx⟩
    change a = b at hab
    change b = a at hba
    subst b
    congr
    exact le_antisymm hxy hyx

/-- Thesis `prop:disjoint-total-order`.

The lexicographic non-strict order on a disjoint union. This is kept as a
named relation rather than a global `≤` instance because the thesis also uses
the same-tag-only partial order on the same underlying disjoint union.
-/
def LexLE [LT A] [∀ a, LE (X a)] (z w : DisjointUnion X) : Prop :=
  z.1 < w.1 ∨ ∃ h : z.1 = w.1, (h ▸ z.2) ≤ w.2

theorem lexLE_refl [Preorder A] [∀ a, Preorder (X a)] (z : DisjointUnion X) :
    LexLE z z := by
  right
  exact ⟨rfl, le_rfl⟩

theorem lexLE_trans [Preorder A] [∀ a, Preorder (X a)] {x y z : DisjointUnion X} :
    LexLE x y → LexLE y z → LexLE x z := by
  rcases x with ⟨a, x⟩
  rcases y with ⟨b, y⟩
  rcases z with ⟨c, z⟩
  intro hxy hyz
  rcases hxy with hab_lt | ⟨hab, hxy⟩
  · rcases hyz with hbc_lt | ⟨hbc, _hyz⟩
    · left
      exact lt_trans hab_lt hbc_lt
    · change b = c at hbc
      subst c
      left
      exact hab_lt
  · change a = b at hab
    subst b
    rcases hyz with hac_lt | ⟨hac, hyz⟩
    · left
      exact hac_lt
    · change a = c at hac
      subst c
      right
      exact ⟨rfl, le_trans hxy hyz⟩

theorem lexLE_antisymm [PartialOrder A] [∀ a, PartialOrder (X a)] {x y : DisjointUnion X} :
    LexLE x y → LexLE y x → x = y := by
  rcases x with ⟨a, x⟩
  rcases y with ⟨b, y⟩
  intro hxy hyx
  rcases hxy with hab_lt | ⟨hab, hxy⟩
  · rcases hyx with hba_lt | ⟨hba, _hyx⟩
    · exact False.elim ((lt_asymm hab_lt) hba_lt)
    · change b = a at hba
      subst b
      exact False.elim ((lt_irrefl a) hab_lt)
  · change a = b at hab
    subst b
    rcases hyx with hba_lt | ⟨_hba, hyx⟩
    · exact False.elim ((lt_irrefl a) hba_lt)
    · congr
      exact le_antisymm hxy hyx

theorem lexLE_total [LinearOrder A] [∀ a, LinearOrder (X a)] (x y : DisjointUnion X) :
    LexLE x y ∨ LexLE y x := by
  rcases x with ⟨a, x⟩
  rcases y with ⟨b, y⟩
  rcases lt_trichotomy a b with hab_lt | hab_eq | hba_lt
  · left
    left
    exact hab_lt
  · subst b
    rcases le_total x y with hxy | hyx
    · left
      right
      exact ⟨rfl, hxy⟩
    · right
      right
      exact ⟨rfl, hyx⟩
  · right
    left
    exact hba_lt

/-- Thesis `prop:disjoint-total-order`.

The lexicographic relation is a partial order when the index and component
relations are linear orders.
-/
theorem lexLE_isPartialOrder [LinearOrder A] [∀ a, LinearOrder (X a)] :
    IsPartialOrder (DisjointUnion X) LexLE where
  refl := lexLE_refl
  trans := by
    intro x y z
    exact lexLE_trans
  antisymm := by
    intro x y
    exact lexLE_antisymm

/-- Thesis `prop:disjoint-total-order`.

The lexicographic relation is total when the index and component relations are
linear orders.
-/
theorem lexLE_isTotal [LinearOrder A] [∀ a, LinearOrder (X a)] :
    Std.Total (LexLE (X := X)) where
  total := lexLE_total

/-- Thesis `cor:strict-disjoint-total-order`.

The strict lexicographic order on a disjoint union.
-/
def LexLT [LT A] [∀ a, LT (X a)] (z w : DisjointUnion X) : Prop :=
  z.1 < w.1 ∨ ∃ h : z.1 = w.1, (h ▸ z.2) < w.2

theorem lexLT_irrefl [Preorder A] [∀ a, Preorder (X a)] (z : DisjointUnion X) :
    ¬ LexLT z z := by
  rcases z with ⟨a, x⟩
  intro h
  rcases h with haa | ⟨_haa, hxx⟩
  · exact (lt_irrefl a) haa
  · exact (lt_irrefl x) hxx

theorem lexLT_trans [Preorder A] [∀ a, Preorder (X a)] {x y z : DisjointUnion X} :
    LexLT x y → LexLT y z → LexLT x z := by
  rcases x with ⟨a, x⟩
  rcases y with ⟨b, y⟩
  rcases z with ⟨c, z⟩
  intro hxy hyz
  rcases hxy with hab_lt | ⟨hab, hxy⟩
  · rcases hyz with hbc_lt | ⟨hbc, _hyz⟩
    · left
      exact lt_trans hab_lt hbc_lt
    · change b = c at hbc
      subst c
      left
      exact hab_lt
  · change a = b at hab
    subst b
    rcases hyz with hac_lt | ⟨hac, hyz⟩
    · left
      exact hac_lt
    · change a = c at hac
      subst c
      right
      exact ⟨rfl, lt_trans hxy hyz⟩

theorem lexLT_trichotomous [LinearOrder A] [∀ a, LinearOrder (X a)] :
    Std.Trichotomous (LexLT (X := X)) where
  trichotomous := by
    intro p q hpq hqp
    rcases p with ⟨a, x⟩
    rcases q with ⟨b, y⟩
    rcases lt_trichotomy a b with hab | hab | hba
    · exact False.elim (hpq (Or.inl hab))
    · subst b
      rcases lt_trichotomy x y with hxy | hxy | hyx
      · exact False.elim (hpq (Or.inr ⟨rfl, hxy⟩))
      · subst y
        rfl
      · exact False.elim (hqp (Or.inr ⟨rfl, hyx⟩))
    · exact False.elim (hqp (Or.inl hba))

/-- Thesis `cor:strict-disjoint-total-order`.

The strict lexicographic relation is a strict total order.
-/
theorem lexLT_isStrictTotalOrder [LinearOrder A] [∀ a, LinearOrder (X a)] :
    IsStrictTotalOrder (DisjointUnion X) LexLT where
  trichotomous := by
    exact (lexLT_trichotomous (X := X)).trichotomous
  irrefl := lexLT_irrefl
  trans := by
    intro x y z
    exact lexLT_trans

end DisjointUnion

end MarketRepresentation
end Foundations
end Thesis
