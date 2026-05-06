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
* `exmp:adm-static`;
* `exmp:agent-adm-static`;
* `exmp:adm-dyn`;
* `exmp:agent-adm-dyn`;
* `exmp:partial-order-static-market`.

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

/-- A three-level lexicographic helper used for price-time-quantity priorities.

This is not a separate thesis definition; it packages the recurring proof
pattern in `exmp:total-order-dynamic-market`. The third coordinate is
non-strict because the thesis orders are non-strict priorities.
-/
def Lex3LE {α β γ : Type} [LT α] [LT β] [LE γ]
    (a : α) (b : β) (c : γ) (a' : α) (b' : β) (c' : γ) : Prop :=
  a < a' ∨ (a = a' ∧ b < b') ∨ (a = a' ∧ b = b' ∧ c ≤ c')

namespace Lex3LE

theorem refl {α β γ : Type} [Preorder α] [Preorder β] [Preorder γ]
    (a : α) (b : β) (c : γ) : Lex3LE a b c a b c := by
  right
  right
  exact ⟨rfl, rfl, le_rfl⟩

theorem trans {α β γ : Type} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    {a1 a2 a3 : α} {b1 b2 b3 : β} {c1 c2 c3 : γ} :
    Lex3LE a1 b1 c1 a2 b2 c2 → Lex3LE a2 b2 c2 a3 b3 c3 →
      Lex3LE a1 b1 c1 a3 b3 c3 := by
  intro h12 h23
  rcases h12 with ha12 | ⟨ha12, hb12⟩ | ⟨ha12, hb12, hc12⟩
  · rcases h23 with ha23 | ⟨ha23, _hb23⟩ | ⟨ha23, _hb23, _hc23⟩
    · left
      exact lt_trans ha12 ha23
    · subst a3
      left
      exact ha12
    · subst a3
      left
      exact ha12
  · rcases h23 with ha23 | ⟨ha23, hb23⟩ | ⟨ha23, hb23, _hc23⟩
    · subst a2
      left
      exact ha23
    · subst a2
      subst a3
      right
      left
      exact ⟨rfl, lt_trans hb12 hb23⟩
    · subst a2
      subst a3
      subst b3
      right
      left
      exact ⟨rfl, hb12⟩
  · rcases h23 with ha23 | ⟨ha23, hb23⟩ | ⟨ha23, hb23, hc23⟩
    · subst a2
      left
      exact ha23
    · subst a2
      subst a3
      subst b2
      right
      left
      exact ⟨rfl, hb23⟩
    · subst a2
      subst a3
      subst b2
      subst b3
      right
      right
      exact ⟨rfl, rfl, le_trans hc12 hc23⟩

theorem antisymm {α β γ : Type} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    {a1 a2 : α} {b1 b2 : β} {c1 c2 : γ} :
    Lex3LE a1 b1 c1 a2 b2 c2 → Lex3LE a2 b2 c2 a1 b1 c1 →
      a1 = a2 ∧ b1 = b2 ∧ c1 = c2 := by
  intro h12 h21
  rcases h12 with ha12 | ⟨ha12, hb12⟩ | ⟨ha12, hb12, hc12⟩
  · rcases h21 with ha21 | ⟨ha21, _hb21⟩ | ⟨ha21, _hb21, _hc21⟩
    · exact False.elim ((lt_asymm ha12) ha21)
    · subst a2
      exact False.elim ((lt_irrefl a1) ha12)
    · subst a2
      exact False.elim ((lt_irrefl a1) ha12)
  · rcases h21 with ha21 | ⟨ha21, hb21⟩ | ⟨ha21, hb21, _hc21⟩
    · subst a2
      exact False.elim ((lt_irrefl a1) ha21)
    · subst a2
      exact False.elim ((lt_asymm hb12) hb21)
    · subst a2
      subst b2
      exact False.elim ((lt_irrefl b1) hb12)
  · rcases h21 with ha21 | ⟨ha21, hb21⟩ | ⟨ha21, hb21, hc21⟩
    · subst a2
      exact False.elim ((lt_irrefl a1) ha21)
    · subst a2
      subst b2
      exact False.elim ((lt_irrefl b1) hb21)
    · subst a2
      subst b2
      exact ⟨rfl, rfl, le_antisymm hc12 hc21⟩

theorem total {α β γ : Type} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    (a1 a2 : α) (b1 b2 : β) (c1 c2 : γ) :
    Lex3LE a1 b1 c1 a2 b2 c2 ∨ Lex3LE a2 b2 c2 a1 b1 c1 := by
  rcases lt_trichotomy a1 a2 with ha | ha | ha
  · left
    left
    exact ha
  · subst a2
    rcases lt_trichotomy b1 b2 with hb | hb | hb
    · left
      right
      left
      exact ⟨rfl, hb⟩
    · subst b2
      rcases le_total c1 c2 with hc | hc
      · left
        right
        right
        exact ⟨rfl, rfl, hc⟩
      · right
        right
        right
        exact ⟨rfl, rfl, hc⟩
    · right
      right
      left
      exact ⟨rfl, hb⟩
  · right
    left
    exact ha

end Lex3LE

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

/-- Thesis examples `exmp:adm-static`, `exmp:partial-order-static-market`.

The two order intents used in the first static market examples.
-/
inductive Intent where
  | buy
  | sell
  deriving DecidableEq, Repr

/-- The nonnegative real line, used for quantities and submission times. -/
abbrev NonnegativeReal : Type :=
  {q : ℝ // 0 ≤ q}

/-- Thesis `exmp:adm-static`.

Static orders are real prices paired with nonnegative real quantities.
-/
abbrev StaticOrder : Type :=
  ℝ × NonnegativeReal

namespace StaticOrder

/-- The price coordinate of a static order. -/
def price (o : StaticOrder) : ℝ :=
  o.1

/-- The quantity coordinate of a static order. -/
def quantity (o : StaticOrder) : ℝ :=
  o.2.1

theorem ext {x y : StaticOrder} (hp : price x = price y) (hq : quantity x = quantity y) :
    x = y := by
  cases x with
  | mk px qx =>
    cases y with
    | mk py qy =>
      cases qx with
      | mk qx hqx =>
        cases qy with
        | mk qy hqy =>
          dsimp [price, quantity] at hp hq
          subst py
          subst qy
          rfl

/-- Thesis `exmp:partial-order-static-market`.

Buy-side priority: the left order has priority when it has a larger price, or
the same price and at least as much quantity.
-/
def BuyPriority (x y : StaticOrder) : Prop :=
  price y < price x ∨ (price x = price y ∧ quantity y ≤ quantity x)

/-- Thesis `exmp:partial-order-static-market`.

Sell-side priority: the left order has priority when it has a smaller price, or
the same price and at least as much quantity.
-/
def SellPriority (x y : StaticOrder) : Prop :=
  price x < price y ∨ (price x = price y ∧ quantity y ≤ quantity x)

theorem buyPriority_refl (x : StaticOrder) : BuyPriority x x := by
  right
  exact ⟨rfl, le_rfl⟩

theorem sellPriority_refl (x : StaticOrder) : SellPriority x x := by
  right
  exact ⟨rfl, le_rfl⟩

theorem buyPriority_trans {x y z : StaticOrder} :
    BuyPriority x y → BuyPriority y z → BuyPriority x z := by
  intro hxy hyz
  rcases hxy with hxy | ⟨hp_xy, hq_xy⟩
  · rcases hyz with hyz | ⟨hp_yz, _hq_yz⟩
    · left
      linarith
    · left
      linarith
  · rcases hyz with hyz | ⟨hp_yz, hq_yz⟩
    · left
      linarith
    · right
      constructor
      · linarith
      · exact le_trans hq_yz hq_xy

theorem sellPriority_trans {x y z : StaticOrder} :
    SellPriority x y → SellPriority y z → SellPriority x z := by
  intro hxy hyz
  rcases hxy with hxy | ⟨hp_xy, hq_xy⟩
  · rcases hyz with hyz | ⟨hp_yz, _hq_yz⟩
    · left
      linarith
    · left
      linarith
  · rcases hyz with hyz | ⟨hp_yz, hq_yz⟩
    · left
      linarith
    · right
      constructor
      · linarith
      · exact le_trans hq_yz hq_xy

theorem buyPriority_antisymm {x y : StaticOrder} :
    BuyPriority x y → BuyPriority y x → x = y := by
  intro hxy hyx
  rcases hxy with hxy | ⟨hp_xy, hq_xy⟩
  · rcases hyx with hyx | ⟨hp_yx, _hq_yx⟩
    · linarith
    · linarith
  · rcases hyx with hyx | ⟨hp_yx, hq_yx⟩
    · linarith
    · apply ext hp_xy
      exact le_antisymm hq_yx hq_xy

theorem sellPriority_antisymm {x y : StaticOrder} :
    SellPriority x y → SellPriority y x → x = y := by
  intro hxy hyx
  rcases hxy with hxy | ⟨hp_xy, hq_xy⟩
  · rcases hyx with hyx | ⟨hp_yx, _hq_yx⟩
    · linarith
    · linarith
  · rcases hyx with hyx | ⟨hp_yx, hq_yx⟩
    · linarith
    · apply ext hp_xy
      exact le_antisymm hq_yx hq_xy

theorem buyPriority_total (x y : StaticOrder) : BuyPriority x y ∨ BuyPriority y x := by
  rcases lt_trichotomy (price y) (price x) with hyx | h_eq | hxy
  · left
    left
    exact hyx
  · rcases le_total (quantity y) (quantity x) with hyq | hxq
    · left
      right
      exact ⟨h_eq.symm, hyq⟩
    · right
      right
      exact ⟨h_eq, hxq⟩
  · right
    left
    exact hxy

theorem sellPriority_total (x y : StaticOrder) : SellPriority x y ∨ SellPriority y x := by
  rcases lt_trichotomy (price x) (price y) with hxy | h_eq | hyx
  · left
    left
    exact hxy
  · rcases le_total (quantity y) (quantity x) with hyq | hxq
    · left
      right
      exact ⟨h_eq, hyq⟩
    · right
      right
      exact ⟨h_eq.symm, hxq⟩
  · right
    left
    exact hyx

/-- Thesis `exmp:partial-order-static-market`.

The buy-side static priority relation is a partial order.
-/
theorem buyPriority_isPartialOrder : IsPartialOrder StaticOrder BuyPriority where
  refl := buyPriority_refl
  trans := by
    intro x y z
    exact buyPriority_trans
  antisymm := by
    intro x y
    exact buyPriority_antisymm

/-- Thesis `exmp:partial-order-static-market`.

The sell-side static priority relation is a partial order.
-/
theorem sellPriority_isPartialOrder : IsPartialOrder StaticOrder SellPriority where
  refl := sellPriority_refl
  trans := by
    intro x y z
    exact sellPriority_trans
  antisymm := by
    intro x y
    exact sellPriority_antisymm

end StaticOrder

/-- Thesis `exmp:adm-static`.

The unrestricted static admissible order space
`\bigsqcup_{\kappa \in \{buy, sell\}} ℝ × [0,∞)`.
-/
abbrev StaticAdmissibleOrders : Type :=
  DisjointUnion (fun _ : Intent => StaticOrder)

/-- Thesis `exmp:adm-static`.

The unrestricted static admissible order space is equivalent to the product of
intent and static order because both intent components carry the same
price/quantity type.
-/
def staticAdmissibleOrdersEquivIntentProduct :
    StaticAdmissibleOrders ≃ Intent × StaticOrder where
  toFun z := (z.1, z.2)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro z
    cases z
    rfl
  right_inv := by
    intro p
    cases p
    rfl

/-- Thesis `exmp:agent-adm-static`.

Agent-restricted static admissible orders. `P κ a` is the admissible price set
for intent `κ` and agent `a`; `Q κ a` is the admissible nonnegative-quantity
set. Lean represents the subset constraints as subtype membership proofs.
-/
abbrev AgentStaticAdmissibleOrders (Agent : Type u) (P : Intent → Agent → Set ℝ)
    (Q : Intent → Agent → Set NonnegativeReal) : Type u :=
  DisjointUnion (fun ka : Intent × Agent => P ka.1 ka.2 × Q ka.1 ka.2)

namespace AgentStaticAdmissibleOrders

/-- Thesis `exmp:agent-adm-static`, equation `eq:agent-adm-static-inj`.

The typed injection from restricted tagged orders into the product containing
price, quantity, intent, and agent.
-/
def toProduct {Agent : Type u} {P : Intent → Agent → Set ℝ}
    {Q : Intent → Agent → Set NonnegativeReal}
    (z : AgentStaticAdmissibleOrders Agent P Q) : StaticOrder × Intent × Agent :=
  match z with
  | ⟨(κ, a), pq⟩ => ((pq.1.1, pq.2.1), κ, a)

theorem toProduct_injective {Agent : Type u} {P : Intent → Agent → Set ℝ}
    {Q : Intent → Agent → Set NonnegativeReal} :
    Function.Injective (toProduct (Agent := Agent) (P := P) (Q := Q)) := by
  intro z w h
  rcases z with ⟨⟨κ, a⟩, ⟨p, q⟩⟩
  rcases w with ⟨⟨κ', a'⟩, ⟨p', q'⟩⟩
  dsimp [toProduct] at h
  injection h with horder hka
  injection hka with hκ ha
  subst κ'
  subst a'
  injection horder with hp hq
  cases p with
  | mk p hp_mem =>
    cases p' with
    | mk p' hp'_mem =>
      cases q with
      | mk q hq_mem =>
        cases q' with
        | mk q' hq'_mem =>
          dsimp at hp hq
          subst p'
          subst q'
          rfl

/-- Thesis `exmp:agent-adm-static`.

The restricted product map is injective, matching the thesis'
agent-augmented product representation.
-/
theorem toProduct_embedding_injective {Agent : Type u} {P : Intent → Agent → Set ℝ}
    {Q : Intent → Agent → Set NonnegativeReal} :
    Function.Injective (toProduct (Agent := Agent) (P := P) (Q := Q)) :=
  toProduct_injective (Agent := Agent) (P := P) (Q := Q)

/-- Thesis example "Completing Order for Agent Based Admissible Orders in a
Static Market".

The market-visible part of an agent-restricted order forgets the submitting
agent and remembers only price, quantity, and intent.
-/
def marketView {Agent : Type u} {P : Intent → Agent → Set ℝ}
    {Q : Intent → Agent → Set NonnegativeReal}
    (z : AgentStaticAdmissibleOrders Agent P Q) : StaticAdmissibleOrders :=
  match z with
  | ⟨(κ, _a), pq⟩ => ⟨κ, (pq.1.1, pq.2.1)⟩

/-- Thesis example "Completing Order for Agent Based Admissible Orders in a
Static Market".

Two agent-restricted orders are equivalent when the market sees the same
price, quantity, and intent. This formalizes the thesis relation that ignores
the submitting agent.
-/
def marketSetoid (Agent : Type u) (P : Intent → Agent → Set ℝ)
    (Q : Intent → Agent → Set NonnegativeReal) :
    Setoid (AgentStaticAdmissibleOrders Agent P Q) where
  r z w := marketView z = marketView w
  iseqv :=
    ⟨by
      intro z
      rfl,
     by
      intro z w h
      exact h.symm,
     by
      intro x y z hxy hyz
      exact hxy.trans hyz⟩

/-- The quotient by the market-visible equivalence relation. -/
abbrev MarketQuotient (Agent : Type u) (P : Intent → Agent → Set ℝ)
    (Q : Intent → Agent → Set NonnegativeReal) : Type u :=
  Quotient (marketSetoid Agent P Q)

/-- Thesis example "Completing Order for Agent Based Admissible Orders in a
Static Market".

The quotient maps into the unrestricted static order space by keeping the
market-visible order.
-/
def quotientMarketView {Agent : Type u} {P : Intent → Agent → Set ℝ}
    {Q : Intent → Agent → Set NonnegativeReal} :
    MarketQuotient Agent P Q → StaticAdmissibleOrders :=
  Quotient.lift marketView (by
    intro z w h
    exact h)

theorem quotientMarketView_injective {Agent : Type u} {P : Intent → Agent → Set ℝ}
    {Q : Intent → Agent → Set NonnegativeReal} :
    Function.Injective (quotientMarketView (Agent := Agent) (P := P) (Q := Q)) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | h q =>
    induction r using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      exact h

/-- Thesis example "Completing Order for Agent Based Admissible Orders in a
Static Market".

The market quotient is equivalent to its market-visible image in the
unrestricted static order space. This is the Lean image/range version of the
thesis bijection to the agent-forgetting representation.
-/
noncomputable def quotientEquivRange {Agent : Type u} {P : Intent → Agent → Set ℝ}
    {Q : Intent → Agent → Set NonnegativeReal} :
    MarketQuotient Agent P Q ≃ Set.range
      (quotientMarketView (Agent := Agent) (P := P) (Q := Q)) :=
  Equiv.ofInjective (quotientMarketView (Agent := Agent) (P := P) (Q := Q))
    quotientMarketView_injective

end AgentStaticAdmissibleOrders

/-- Thesis `exmp:adm-dyn`.

Dynamic orders add a nonnegative submission time to static price/quantity
orders.
-/
abbrev DynamicOrder : Type :=
  ℝ × NonnegativeReal × NonnegativeReal

namespace DynamicOrder

/-- The price coordinate of a dynamic order. -/
def price (o : DynamicOrder) : ℝ :=
  o.1

/-- The quantity coordinate of a dynamic order. -/
def quantity (o : DynamicOrder) : ℝ :=
  o.2.1

/-- The submission-time coordinate of a dynamic order. -/
def time (o : DynamicOrder) : ℝ :=
  o.2.2.1

theorem ext {x y : DynamicOrder} (hp : price x = price y) (hq : quantity x = quantity y)
    (ht : time x = time y) : x = y := by
  rcases x with ⟨px, qx, tx⟩
  rcases y with ⟨py, qy, ty⟩
  cases qx with
  | mk qx hqx =>
    cases qy with
    | mk qy hqy =>
      cases tx with
      | mk tx htx =>
        cases ty with
        | mk ty hty =>
          dsimp [price, quantity, time] at hp hq ht
          subst py
          subst qy
          subst ty
          rfl

/-- Thesis `exmp:total-order-dynamic-market`.

Buy-side price-time priority. Lean implements the thesis condition using the
lexicographic key `(-price, time, -quantity)`, so higher price, earlier time,
and larger quantity are preferred in that order.
-/
def BuyPriority (x y : DynamicOrder) : Prop :=
  Lex3LE (-(price x)) (time x) (-(quantity x)) (-(price y)) (time y) (-(quantity y))

/-- Thesis `exmp:total-order-dynamic-market`.

Sell-side price-time priority. Lean implements the thesis condition using the
lexicographic key `(price, time, -quantity)`, so lower price, earlier time, and
larger quantity are preferred in that order.
-/
def SellPriority (x y : DynamicOrder) : Prop :=
  Lex3LE (price x) (time x) (-(quantity x)) (price y) (time y) (-(quantity y))

theorem buyPriority_refl (x : DynamicOrder) : BuyPriority x x :=
  Lex3LE.refl _ _ _

theorem sellPriority_refl (x : DynamicOrder) : SellPriority x x :=
  Lex3LE.refl _ _ _

theorem buyPriority_trans {x y z : DynamicOrder} :
    BuyPriority x y → BuyPriority y z → BuyPriority x z :=
  Lex3LE.trans

theorem sellPriority_trans {x y z : DynamicOrder} :
    SellPriority x y → SellPriority y z → SellPriority x z :=
  Lex3LE.trans

theorem buyPriority_antisymm {x y : DynamicOrder} :
    BuyPriority x y → BuyPriority y x → x = y := by
  intro hxy hyx
  rcases Lex3LE.antisymm hxy hyx with ⟨hp, ht, hq⟩
  apply ext
  · linarith
  · linarith
  · exact ht

theorem sellPriority_antisymm {x y : DynamicOrder} :
    SellPriority x y → SellPriority y x → x = y := by
  intro hxy hyx
  rcases Lex3LE.antisymm hxy hyx with ⟨hp, ht, hq⟩
  apply ext
  · exact hp
  · linarith
  · exact ht

theorem buyPriority_total (x y : DynamicOrder) : BuyPriority x y ∨ BuyPriority y x :=
  Lex3LE.total _ _ _ _ _ _

theorem sellPriority_total (x y : DynamicOrder) : SellPriority x y ∨ SellPriority y x :=
  Lex3LE.total _ _ _ _ _ _

/-- Thesis `exmp:total-order-dynamic-market`.

The buy-side dynamic price-time priority relation is a partial order.
-/
theorem buyPriority_isPartialOrder : IsPartialOrder DynamicOrder BuyPriority where
  refl := buyPriority_refl
  trans := by
    intro x y z
    exact buyPriority_trans
  antisymm := by
    intro x y
    exact buyPriority_antisymm

/-- Thesis `exmp:total-order-dynamic-market`.

The sell-side dynamic price-time priority relation is a partial order.
-/
theorem sellPriority_isPartialOrder : IsPartialOrder DynamicOrder SellPriority where
  refl := sellPriority_refl
  trans := by
    intro x y z
    exact sellPriority_trans
  antisymm := by
    intro x y
    exact sellPriority_antisymm

end DynamicOrder

/-- Thesis `exmp:adm-dyn`.

The unrestricted dynamic admissible order space
`\bigsqcup_{\kappa \in \{buy, sell\}} ℝ × [0,∞) × [0,∞)`.
-/
abbrev DynamicAdmissibleOrders : Type :=
  DisjointUnion (fun _ : Intent => DynamicOrder)

/-- Thesis `exmp:adm-dyn`.

The unrestricted dynamic admissible order space is equivalent to the product
of intent and dynamic order because both intent components carry the same
price/quantity/time type.
-/
def dynamicAdmissibleOrdersEquivIntentProduct :
    DynamicAdmissibleOrders ≃ Intent × DynamicOrder where
  toFun z := (z.1, z.2)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro z
    cases z
    rfl
  right_inv := by
    intro p
    cases p
    rfl

/-- Thesis `exmp:adm-dyn`.

The alternative unrestricted dynamic representation indexed by intent and time:
`\bigsqcup_{(\kappa,t)} ℝ × [0,∞)`. The component is the static price/quantity
payload, while the disjoint-union tag stores the intent and submission time.

Lean strategy / thesis relation note: this is the first displayed dynamic
representation in the manuscript. It is equivalent to `DynamicAdmissibleOrders`
by moving the time coordinate between the tag and the order payload.
-/
abbrev DynamicAdmissibleOrdersTimeIndexed : Type :=
  DisjointUnion (fun _ : Intent × NonnegativeReal => StaticOrder)

/-- Thesis `exmp:adm-dyn`.

The time-indexed dynamic order representation is equivalent to the
intent-indexed dynamic representation.
-/
def dynamicTimeIndexedEquivDynamicAdmissibleOrders :
    DynamicAdmissibleOrdersTimeIndexed ≃ DynamicAdmissibleOrders where
  toFun z :=
    match z with
    | ⟨(κ, t), order⟩ => ⟨κ, (order.1, order.2, t)⟩
  invFun z :=
    match z with
    | ⟨κ, order⟩ => ⟨(κ, order.2.2), (order.1, order.2.1)⟩
  left_inv := by
    intro z
    rcases z with ⟨⟨κ, t⟩, ⟨p, q⟩⟩
    rfl
  right_inv := by
    intro z
    rcases z with ⟨κ, ⟨p, q, t⟩⟩
    rfl

/-- Thesis `exmp:agent-adm-dyn`.

Agent/time-restricted dynamic admissible orders. The index remembers the
intent, agent, and time, while the component stores admissible price and
quantity choices for that index.
-/
abbrev AgentDynamicAdmissibleOrders (Agent : Type u)
    (P : Intent → Agent → NonnegativeReal → Set ℝ)
    (Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal) : Type u :=
  DisjointUnion
    (fun kat : Intent × Agent × NonnegativeReal =>
      P kat.1 kat.2.1 kat.2.2 × Q kat.1 kat.2.1 kat.2.2)

/-- Thesis `exmp:agent-adm-dyn`, equation `eq:agent-adm-dyn-2`.

The time-collapsed admissible price set
`P_{\kappa,a} = \bigcup_t P_{\kappa,a,t}`.
-/
def AgentDynamicPriceTimeUnion {Agent : Type u}
    (P : Intent → Agent → NonnegativeReal → Set ℝ)
    (κ : Intent) (a : Agent) : Set ℝ :=
  {p | ∃ t : NonnegativeReal, p ∈ P κ a t}

/-- Thesis `exmp:agent-adm-dyn`, equation `eq:agent-adm-dyn-2`.

The time-collapsed admissible quantity set
`Q_{\kappa,a} = \bigcup_t Q_{\kappa,a,t}`.
-/
def AgentDynamicQuantityTimeUnion {Agent : Type u}
    (Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal)
    (κ : Intent) (a : Agent) : Set NonnegativeReal :=
  {q | ∃ t : NonnegativeReal, q ∈ Q κ a t}

/-- Thesis `exmp:agent-adm-dyn`, equation `eq:agent-adm-dyn-2`.

The intermediate time-collapsed dynamic space
`\bigsqcup_{(\kappa,a)} P_{\kappa,a} × Q_{\kappa,a} × [0,∞)`.

Lean strategy / thesis relation note: the thesis writes the middle term of the
inclusion chain as an ordinary set expression. Lean keeps the same information
as a typed disjoint union, with membership in the collapsed price/quantity
sets carried by subtypes.
-/
abbrev AgentDynamicTimeCollapsedOrders (Agent : Type u)
    (P : Intent → Agent → NonnegativeReal → Set ℝ)
    (Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal) : Type u :=
  DisjointUnion
    (fun ka : Intent × Agent =>
      AgentDynamicPriceTimeUnion P ka.1 ka.2 ×
        AgentDynamicQuantityTimeUnion Q ka.1 ka.2 × NonnegativeReal)

namespace AgentDynamicAdmissibleOrders

/-- Thesis `exmp:agent-adm-dyn`, equations
`eq:agent-adm-dyn-1` and `eq:agent-adm-dyn-2`.

The first inclusion in the thesis chain: an order admissible at a specific
time is also an order in the time-collapsed agent/intention space, witnessed by
that same time.
-/
def toTimeCollapsed {Agent : Type u}
    {P : Intent → Agent → NonnegativeReal → Set ℝ}
    {Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal}
    (z : AgentDynamicAdmissibleOrders Agent P Q) :
    AgentDynamicTimeCollapsedOrders Agent P Q :=
  match z with
  | ⟨(κ, a, t), pq⟩ =>
      ⟨(κ, a),
        (⟨pq.1.1, ⟨t, pq.1.2⟩⟩,
          ⟨pq.2.1, ⟨t, pq.2.2⟩⟩,
          t)⟩

/-- Thesis `exmp:agent-adm-dyn`, equations
`eq:agent-adm-dyn-1` and `eq:agent-adm-dyn-2`.

The first inclusion in the thesis chain is injective: the time-collapsed image
still remembers the original time, price, quantity, intent, and agent.
-/
theorem toTimeCollapsed_injective {Agent : Type u}
    {P : Intent → Agent → NonnegativeReal → Set ℝ}
    {Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal} :
    Function.Injective (toTimeCollapsed (Agent := Agent) (P := P) (Q := Q)) := by
  intro z w h
  rcases z with ⟨⟨κ, a, t⟩, ⟨p, q⟩⟩
  rcases w with ⟨⟨κ', a', t'⟩, ⟨p', q'⟩⟩
  dsimp [toTimeCollapsed] at h
  injection h with hka hpayload
  injection hka with hκ ha
  subst κ'
  subst a'
  injection hpayload with hprice hrest
  injection hrest with hquantity ht
  subst t'
  cases p with
  | mk p hp =>
    cases p' with
    | mk p' hp' =>
      cases q with
      | mk q hq =>
        cases q' with
        | mk q' hq' =>
          injection hprice with hp_eq
          injection hquantity with hq_eq
          dsimp at hp_eq hq_eq
          subst p'
          subst q'
          rfl

end AgentDynamicAdmissibleOrders

namespace AgentDynamicTimeCollapsedOrders

/-- Thesis `exmp:agent-adm-dyn`, equation `eq:agent-adm-dyn-3`.

The second inclusion in the thesis chain: the time-collapsed representation
embeds in the unrestricted product of dynamic order, intent, and agent.
-/
def toProduct {Agent : Type u}
    {P : Intent → Agent → NonnegativeReal → Set ℝ}
    {Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal}
    (z : AgentDynamicTimeCollapsedOrders Agent P Q) :
    DynamicOrder × Intent × Agent :=
  match z with
  | ⟨(κ, a), pqt⟩ => ((pqt.1.1, pqt.2.1.1, pqt.2.2), κ, a)

/-- Thesis `exmp:agent-adm-dyn`, equation `eq:agent-adm-dyn-3`.

The second inclusion in the thesis chain is injective.
-/
theorem toProduct_injective {Agent : Type u}
    {P : Intent → Agent → NonnegativeReal → Set ℝ}
    {Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal} :
    Function.Injective (toProduct (Agent := Agent) (P := P) (Q := Q)) := by
  intro z w h
  rcases z with ⟨⟨κ, a⟩, ⟨p, q, t⟩⟩
  rcases w with ⟨⟨κ', a'⟩, ⟨p', q', t'⟩⟩
  dsimp [toProduct] at h
  injection h with horder hka
  injection hka with hκ ha
  subst κ'
  subst a'
  injection horder with hp hqt
  injection hqt with hq ht
  subst t'
  cases p with
  | mk p hp_mem =>
    cases p' with
    | mk p' hp'_mem =>
      cases q with
      | mk q hq_mem =>
        cases q' with
        | mk q' hq'_mem =>
          dsimp at hp hq
          subst p'
          subst q'
          rfl

end AgentDynamicTimeCollapsedOrders

namespace AgentDynamicAdmissibleOrders

/-- Thesis `exmp:agent-adm-dyn`, equations
`eq:agent-adm-dyn-1`, `eq:agent-adm-dyn-2`, and `eq:agent-adm-dyn-3`.

The composite injection from the fully time-restricted admissible order space
into the unrestricted dynamic product representation.
-/
def toProduct {Agent : Type u}
    {P : Intent → Agent → NonnegativeReal → Set ℝ}
    {Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal}
    (z : AgentDynamicAdmissibleOrders Agent P Q) :
    DynamicOrder × Intent × Agent :=
  AgentDynamicTimeCollapsedOrders.toProduct
    (AgentDynamicAdmissibleOrders.toTimeCollapsed z)

/-- Thesis `exmp:agent-adm-dyn`, equations
`eq:agent-adm-dyn-1`, `eq:agent-adm-dyn-2`, and `eq:agent-adm-dyn-3`.

The full product map is injective, giving the Lean embedding form of the
thesis' inclusion chain.
-/
theorem toProduct_injective {Agent : Type u}
    {P : Intent → Agent → NonnegativeReal → Set ℝ}
    {Q : Intent → Agent → NonnegativeReal → Set NonnegativeReal} :
    Function.Injective (toProduct (Agent := Agent) (P := P) (Q := Q)) :=
  Function.Injective.comp
    (AgentDynamicTimeCollapsedOrders.toProduct_injective
      (Agent := Agent) (P := P) (Q := Q))
    (AgentDynamicAdmissibleOrders.toTimeCollapsed_injective
      (Agent := Agent) (P := P) (Q := Q))

end AgentDynamicAdmissibleOrders

/-- Thesis `exmp:partial-order-static-market`.

Priority on unrestricted static admissible orders. Buy orders are compared by
buy-side priority, sell orders by sell-side priority, and orders of different
intent are incomparable.
-/
def StaticAdmissiblePriority : StaticAdmissibleOrders → StaticAdmissibleOrders → Prop
  | ⟨Intent.buy, x⟩, ⟨Intent.buy, y⟩ => StaticOrder.BuyPriority x y
  | ⟨Intent.sell, x⟩, ⟨Intent.sell, y⟩ => StaticOrder.SellPriority x y
  | _, _ => False

theorem staticAdmissiblePriority_refl (x : StaticAdmissibleOrders) :
    StaticAdmissiblePriority x x := by
  rcases x with ⟨κ, x⟩
  cases κ
  · exact StaticOrder.buyPriority_refl x
  · exact StaticOrder.sellPriority_refl x

theorem staticAdmissiblePriority_trans {x y z : StaticAdmissibleOrders} :
    StaticAdmissiblePriority x y →
      StaticAdmissiblePriority y z →
        StaticAdmissiblePriority x z := by
  rcases x with ⟨κx, x⟩
  rcases y with ⟨κy, y⟩
  rcases z with ⟨κz, z⟩
  cases κx <;> cases κy <;> cases κz
  · exact StaticOrder.buyPriority_trans
  · intro _ hyz
    exact False.elim hyz
  · intro hxy _
    exact False.elim hxy
  · intro hxy _
    exact False.elim hxy
  · intro hxy _
    exact False.elim hxy
  · intro hxy _
    exact False.elim hxy
  · intro _ hyz
    exact False.elim hyz
  · exact StaticOrder.sellPriority_trans

theorem staticAdmissiblePriority_antisymm {x y : StaticAdmissibleOrders} :
    StaticAdmissiblePriority x y → StaticAdmissiblePriority y x → x = y := by
  rcases x with ⟨κx, x⟩
  rcases y with ⟨κy, y⟩
  cases κx <;> cases κy
  · intro hxy hyx
    rw [StaticOrder.buyPriority_antisymm hxy hyx]
  · intro hxy _
    exact False.elim hxy
  · intro hxy _
    exact False.elim hxy
  · intro hxy hyx
    rw [StaticOrder.sellPriority_antisymm hxy hyx]

/-- Thesis `exmp:partial-order-static-market`.

The static market priority relation is a partial order; buy and sell orders
remain incomparable in this relation.
-/
theorem staticAdmissiblePriority_isPartialOrder :
    IsPartialOrder StaticAdmissibleOrders StaticAdmissiblePriority where
  refl := staticAdmissiblePriority_refl
  trans := by
    intro x y z
    exact staticAdmissiblePriority_trans
  antisymm := by
    intro x y
    exact staticAdmissiblePriority_antisymm

/-- Thesis `exmp:total-order-static-market`.

A total static market order obtained by declaring all buy-side orders to
precede all sell-side orders, and using the side-specific priorities within
each intent. This is separate from `StaticAdmissiblePriority`, where buy and
sell orders are intentionally incomparable.
-/
def StaticAdmissibleLexPriority : StaticAdmissibleOrders → StaticAdmissibleOrders → Prop
  | ⟨Intent.buy, x⟩, ⟨Intent.buy, y⟩ => StaticOrder.BuyPriority x y
  | ⟨Intent.buy, _⟩, ⟨Intent.sell, _⟩ => True
  | ⟨Intent.sell, _⟩, ⟨Intent.buy, _⟩ => False
  | ⟨Intent.sell, x⟩, ⟨Intent.sell, y⟩ => StaticOrder.SellPriority x y

theorem staticAdmissibleLexPriority_refl (x : StaticAdmissibleOrders) :
    StaticAdmissibleLexPriority x x := by
  rcases x with ⟨κ, x⟩
  cases κ
  · exact StaticOrder.buyPriority_refl x
  · exact StaticOrder.sellPriority_refl x

theorem staticAdmissibleLexPriority_trans {x y z : StaticAdmissibleOrders} :
    StaticAdmissibleLexPriority x y →
      StaticAdmissibleLexPriority y z →
        StaticAdmissibleLexPriority x z := by
  rcases x with ⟨κx, x⟩
  rcases y with ⟨κy, y⟩
  rcases z with ⟨κz, z⟩
  cases κx <;> cases κy <;> cases κz
  · exact StaticOrder.buyPriority_trans
  · intro _ _
    trivial
  · intro _ hyz
    exact False.elim hyz
  · intro _ _
    trivial
  · intro hxy _
    exact False.elim hxy
  · intro hxy _
    exact False.elim hxy
  · intro _ hyz
    exact False.elim hyz
  · exact StaticOrder.sellPriority_trans

theorem staticAdmissibleLexPriority_antisymm {x y : StaticAdmissibleOrders} :
    StaticAdmissibleLexPriority x y → StaticAdmissibleLexPriority y x → x = y := by
  rcases x with ⟨κx, x⟩
  rcases y with ⟨κy, y⟩
  cases κx <;> cases κy
  · intro hxy hyx
    rw [StaticOrder.buyPriority_antisymm hxy hyx]
  · intro _ hyx
    exact False.elim hyx
  · intro hxy _
    exact False.elim hxy
  · intro hxy hyx
    rw [StaticOrder.sellPriority_antisymm hxy hyx]

/-- Thesis `exmp:total-order-static-market`.

Any two static admissible orders are comparable under the lexicographic market
priority relation.
-/
theorem staticAdmissibleLexPriority_total (x y : StaticAdmissibleOrders) :
    StaticAdmissibleLexPriority x y ∨ StaticAdmissibleLexPriority y x := by
  rcases x with ⟨κx, x⟩
  rcases y with ⟨κy, y⟩
  cases κx <;> cases κy
  · exact StaticOrder.buyPriority_total x y
  · left
    trivial
  · right
    trivial
  · exact StaticOrder.sellPriority_total x y

/-- Thesis `exmp:total-order-static-market`.

The static lexicographic market priority relation is a partial order.
-/
theorem staticAdmissibleLexPriority_isPartialOrder :
    IsPartialOrder StaticAdmissibleOrders StaticAdmissibleLexPriority where
  refl := staticAdmissibleLexPriority_refl
  trans := by
    intro x y z
    exact staticAdmissibleLexPriority_trans
  antisymm := by
    intro x y
    exact staticAdmissibleLexPriority_antisymm

/-- Thesis `exmp:total-order-static-market`.

The static lexicographic market priority relation is total.
-/
theorem staticAdmissibleLexPriority_isTotal :
    Std.Total StaticAdmissibleLexPriority where
  total := staticAdmissibleLexPriority_total

/-- Thesis `exmp:total-order-dynamic-market`.

A total dynamic market order obtained by declaring all buy-side orders to
precede all sell-side orders, and using price-time priority within each side.
-/
def DynamicAdmissibleLexPriority : DynamicAdmissibleOrders → DynamicAdmissibleOrders → Prop
  | ⟨Intent.buy, x⟩, ⟨Intent.buy, y⟩ => DynamicOrder.BuyPriority x y
  | ⟨Intent.buy, _⟩, ⟨Intent.sell, _⟩ => True
  | ⟨Intent.sell, _⟩, ⟨Intent.buy, _⟩ => False
  | ⟨Intent.sell, x⟩, ⟨Intent.sell, y⟩ => DynamicOrder.SellPriority x y

theorem dynamicAdmissibleLexPriority_refl (x : DynamicAdmissibleOrders) :
    DynamicAdmissibleLexPriority x x := by
  rcases x with ⟨κ, x⟩
  cases κ
  · exact DynamicOrder.buyPriority_refl x
  · exact DynamicOrder.sellPriority_refl x

theorem dynamicAdmissibleLexPriority_trans {x y z : DynamicAdmissibleOrders} :
    DynamicAdmissibleLexPriority x y →
      DynamicAdmissibleLexPriority y z →
        DynamicAdmissibleLexPriority x z := by
  rcases x with ⟨κx, x⟩
  rcases y with ⟨κy, y⟩
  rcases z with ⟨κz, z⟩
  cases κx <;> cases κy <;> cases κz
  · exact DynamicOrder.buyPriority_trans
  · intro _ _
    trivial
  · intro _ hyz
    exact False.elim hyz
  · intro _ _
    trivial
  · intro hxy _
    exact False.elim hxy
  · intro hxy _
    exact False.elim hxy
  · intro _ hyz
    exact False.elim hyz
  · exact DynamicOrder.sellPriority_trans

theorem dynamicAdmissibleLexPriority_antisymm {x y : DynamicAdmissibleOrders} :
    DynamicAdmissibleLexPriority x y → DynamicAdmissibleLexPriority y x → x = y := by
  rcases x with ⟨κx, x⟩
  rcases y with ⟨κy, y⟩
  cases κx <;> cases κy
  · intro hxy hyx
    rw [DynamicOrder.buyPriority_antisymm hxy hyx]
  · intro _ hyx
    exact False.elim hyx
  · intro hxy _
    exact False.elim hxy
  · intro hxy hyx
    rw [DynamicOrder.sellPriority_antisymm hxy hyx]

/-- Thesis `exmp:total-order-dynamic-market`.

Any two dynamic admissible orders are comparable under the price-time
lexicographic market priority relation.
-/
theorem dynamicAdmissibleLexPriority_total (x y : DynamicAdmissibleOrders) :
    DynamicAdmissibleLexPriority x y ∨ DynamicAdmissibleLexPriority y x := by
  rcases x with ⟨κx, x⟩
  rcases y with ⟨κy, y⟩
  cases κx <;> cases κy
  · exact DynamicOrder.buyPriority_total x y
  · left
    trivial
  · right
    trivial
  · exact DynamicOrder.sellPriority_total x y

/-- Thesis `exmp:total-order-dynamic-market`.

The dynamic lexicographic market priority relation is a partial order.
-/
theorem dynamicAdmissibleLexPriority_isPartialOrder :
    IsPartialOrder DynamicAdmissibleOrders DynamicAdmissibleLexPriority where
  refl := dynamicAdmissibleLexPriority_refl
  trans := by
    intro x y z
    exact dynamicAdmissibleLexPriority_trans
  antisymm := by
    intro x y
    exact dynamicAdmissibleLexPriority_antisymm

/-- Thesis `exmp:total-order-dynamic-market`.

The dynamic lexicographic market priority relation is total.
-/
theorem dynamicAdmissibleLexPriority_isTotal :
    Std.Total DynamicAdmissibleLexPriority where
  total := dynamicAdmissibleLexPriority_total

end MarketRepresentation
end Foundations
end Thesis
