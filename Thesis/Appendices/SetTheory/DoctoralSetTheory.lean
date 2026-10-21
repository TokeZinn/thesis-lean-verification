import Thesis.Appendices.SetTheory.SetConstructions
import Thesis.Foundations.MarketActions.Primitive
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-! # Natural-number recursion and cardinality in the current appendix -/

noncomputable section

namespace Thesis.Foundations.Preliminary.SetTheory

open MarketRepresentation MarketRepresentation.TuplesBasic

universe u v

/-- Original label: `defn:bijection`. -/
abbrev IsInjective {X : Type u} {Y : Type v} (f : X → Y) : Prop := Function.Injective f

/-- Original label: `defn:bijection`. -/
abbrev IsSurjective {X : Type u} {Y : Type v} (f : X → Y) : Prop := Function.Surjective f

/-- Original label: `defn:bijection`. -/
abbrev IsBijective {X : Type u} {Y : Type v} (f : X → Y) : Prop := Function.Bijective f

/-- `ℕ₀ = Set.univ` is contained in every inductive subset of `ℕ`. This is the
typed form of the Infinity clause that `ℕ₀` is the least inductive set; it is
the one place where Lean's natural-number recursor enters. -/
theorem univ_subset_of_inductive (S : Set ℕ) (hzero : 0 ∈ S)
    (hstep : ∀ n, n ∈ S → n + 1 ∈ S) : Set.univ ⊆ S := by
  rintro n -
  induction n with
  | zero => exact hzero
  | succ n ih => exact hstep n ih

/-- Original label: `prop:induction`.

Typed restatement over Lean's `ℕ`, following the thesis inclusions: `S ⊆ ℕ₀`
holds trivially, and `ℕ₀ ⊆ S` because `S` is inductive and `ℕ₀` is the least
inductive set (`univ_subset_of_inductive`); the two inclusions give `S = ℕ₀`.
The mapped set-universe proof, in which `ℕ₀` is literally constructed as the
least inductive set, is `ZFC.induction_naturals` in `ZFCFoundations`. -/
theorem induction_set (S : Set ℕ) (hzero : 0 ∈ S)
    (hstep : ∀ n, n ∈ S → n + 1 ∈ S) : S = Set.univ :=
  Set.Subset.antisymm (Set.subset_univ S) (univ_subset_of_inductive S hzero hstep)

/-- The finite history before the next recursion step. -/
def recursiveHistory {X : Type u} (G : Tuple X → X) : (n : ℕ) → Fin n → X
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (recursiveHistory G n) (G ⟨n, recursiveHistory G n⟩)

/-- Original label: `thm:recursion`.
Lean's value at n corresponds to the manuscript's value at n+1. -/
def recursiveSequence {X : Type u} (G : Tuple X → X) (n : ℕ) : X :=
  G ⟨n, recursiveHistory G n⟩

theorem recursiveHistory_eq_sequence {X : Type u} (G : Tuple X → X) (n : ℕ)
    (i : Fin n) : recursiveHistory G n i = recursiveSequence G i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [recursiveHistory, recursiveSequence]
    · simpa only [recursiveHistory, Fin.snoc_castSucc, Fin.val_castSucc] using ih j

/-- Original label: `thm:recursion`.
The displayed history-dependent rule has exactly one solution, including
rules whose next value depends on every earlier value. -/
theorem recursion_existsUnique {X : Type u} (G : Tuple X → X) :
    ∃! f : ℕ → X, ∀ n, f n = G ⟨n, fun i : Fin n => f i.val⟩ := by
  have hseq (n : ℕ) : recursiveSequence G n =
      G ⟨n, fun i : Fin n => recursiveSequence G i.val⟩ := by
    unfold recursiveSequence
    congr 1
    congr 1
    funext i
    exact recursiveHistory_eq_sequence G n i
  refine ⟨recursiveSequence G, hseq, ?_⟩
  intro f hf
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [hf n, hseq n]
    congr 1
    congr 1
    funext i
    exact ih i.val i.isLt

/-- Original label: `defn:cardinality`. -/
abbrev CardinalLE (X : Type u) (Y : Type v) : Prop := Nonempty (X ↪ Y)

/-- Original label: `defn:cardinality`. -/
abbrev Equinumerous (X : Type u) (Y : Type v) : Prop := Nonempty (X ≃ Y)

/-- Original label: `defn:cardinality`. -/
abbrev IsFiniteType (X : Type u) : Prop := Finite X

/-- Original label: `defn:cardinality`. -/
abbrev IsCountableType (X : Type u) : Prop := Countable X

/-- Original label: `defn:cardinality`. -/
abbrev HasContinuumCardinality (X : Type u) : Prop := Equinumerous X ℝ

/-- Original label: `defn:cardinality`.
The finite-type predicate is equivalent to exactly the source's finite
initial-segment criterion, including the empty type and n=0. -/
theorem isFiniteType_iff (X : Type u) :
    IsFiniteType X ↔ ∃ n : ℕ, Nonempty (X ≃ Fin n) := by
  constructor
  · intro h
    letI : Finite X := h
    letI := Fintype.ofFinite X
    exact ⟨Fintype.card X, ⟨Fintype.equivFin X⟩⟩
  · rintro ⟨n, ⟨e⟩⟩
    exact Finite.of_injective e e.injective

/-- Original label: `defn:cardinality`. -/
theorem isCountableType_iff (X : Type u) : IsCountableType X ↔ CardinalLE X ℕ :=
  countable_iff_nonempty_embedding

/-- Original label: `thm:cantor-schroeder-bernstein`. -/
theorem cantorSchroederBernstein {X : Type u} {Y : Type v}
    (hXY : CardinalLE X Y) (hYX : CardinalLE Y X) : Equinumerous X Y := by
  obtain ⟨f⟩ := hXY
  obtain ⟨g⟩ := hYX
  exact Function.Embedding.antisymm f g

end Thesis.Foundations.Preliminary.SetTheory
