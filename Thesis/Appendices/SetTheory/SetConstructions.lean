import Thesis.Appendices.SetTheory.SetTheory
import Thesis.Foundations.MarketRepresentation.DisjointUnion
import Mathlib.Logic.Equiv.Nat

/-! # Explicit representation bridges for the set-theory appendix -/

noncomputable section
open Set

namespace Thesis.Foundations.Preliminary.SetTheory

universe u v

/-- Original label: `thm:well-ordering`.
The conclusion uses the exact non-strict well-order definition in the appendix. -/
theorem wellOrderingTheorem_explicit (α : Type u) :
    ∃ O : PartialOrderRelation α, O.IsWellOrdered := by
  obtain ⟨L, hL⟩ := exists_wellFoundedLT α
  letI := L
  letI := hL
  let O : PartialOrderRelation α :=
    ⟨(· ≤ ·), le_refl, fun {_ _} hxy hyx ↦ le_antisymm hxy hyx,
      fun {_ _ _} hxy hyz ↦ le_trans hxy hyz⟩
  refine ⟨O, (fun x y _ ↦ le_total x y), fun S hS ↦ ?_⟩
  obtain ⟨x, hx, hmin⟩ := wellFounded_lt.has_min S hS
  exact ⟨x, hx, fun y hy ↦ le_of_not_gt (hmin y hy)⟩

/-- Original label: `thm:zorns-lemma`.
Chain upper bounds and maximality use the literal quantified source conditions. -/
theorem zornsLemma_explicit {α : Type u} [PartialOrder α]
    (h : ∀ C : Set α, (∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) →
      ∃ z : α, ∀ c ∈ C, c ≤ z) :
    ∃ m : α, ∀ x, m ≤ x → x = m := by
  obtain ⟨m, hm⟩ := zornsLemma (fun C hC ↦ h C (fun x hx y hy ↦ hC.total hx hy))
  exact ⟨m, fun x hmx ↦ le_antisymm (hm hmx) hmx⟩

/-- Original label: `defn:arbitrary-product-space`.
The dependent product is equivalent to the source's compatible functions with
codomain the ordinary union of the component sets. -/
def arbitraryProductUnionEquiv {ι : Type u} {α : Type v} (X : ι → Set α) :
    ArbitraryProduct X ≃ {f : ι → (⋃ i, X i) // ∀ i, (f i : α) ∈ X i} where
  toFun f := ⟨fun i ↦ ⟨f i, mem_iUnion.mpr ⟨i, (f i).property⟩⟩,
    fun i ↦ (f i).property⟩
  invFun f := fun i ↦ ⟨f.val i, f.property i⟩
  left_inv f := by rfl
  right_inv f := by rfl

/-- Original label: `rem:bijection-not-homeomorphism`.
Two identical infinite component sets overlap but their ordinary and tagged
unions still have a bijection. Thus an arbitrary bijection cannot replace
injectivity of the canonical tag-forgetting map. -/
theorem overlapping_family_has_union_bijection :
    ∃ S : Bool → Set ℕ, ¬ MarketRepresentation.PairwiseDisjoint S ∧
      Nonempty (MarketRepresentation.SetDisjointUnion S ≃ {x : ℕ // ∃ i, x ∈ S i}) := by
  let S : Bool → Set ℕ := fun _ ↦ univ
  have hn : ¬ MarketRepresentation.PairwiseDisjoint S := by
    intro h
    exact h (a := false) (b := true) (x := 0) (by decide) (mem_univ _) (mem_univ _)
  let e : MarketRepresentation.SetDisjointUnion S ≃ Bool × ℕ :=
    { toFun := fun x ↦ (x.1, x.2.val)
      invFun := fun x ↦ ⟨x.1, ⟨x.2, mem_univ _⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let d : ℕ ≃ {x : ℕ // ∃ i, x ∈ S i} :=
    { toFun := fun x ↦ ⟨x, false, mem_univ _⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact ⟨S, hn, ⟨e.trans (Equiv.boolProdNatEquivNat.trans d)⟩⟩

end Thesis.Foundations.Preliminary.SetTheory
