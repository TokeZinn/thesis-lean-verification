import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! # Powers and closure of an arbitrary finite relation

Thesis source: `1 - theoretical foundations/2_chapter_market_representations.tex`.
The relation is not assumed symmetric, reflexive, or transitive.
-/

namespace Thesis.Foundations.MarketRepresentation.FiniteRelationClosure

universe u
variable {X : Type u}

/-- Original label: `defn:reflexive-transitive-closure`.
Relation powers with the manuscript's left-to-right composition convention.
The zeroth power supplies the separately displayed diagonal. -/
def relationPower (R : X → X → Prop) : ℕ → X → X → Prop
  | 0 => Eq
  | n + 1 => fun x z => ∃ y, relationPower R n x y ∧ R y z

/-- Original label: `defn:reflexive-transitive-closure`. -/
@[simp] theorem relationPower_one (R : X → X → Prop) (x y : X) :
    relationPower R 1 x y ↔ R x y := by
  simp [relationPower]

theorem relationPower_head {R : X → X → Prop} {x y z : X} {n : ℕ}
    (hxy : R x y) (hyz : relationPower R n y z) :
    relationPower R (n + 1) x z := by
  induction n generalizing z with
  | zero =>
      change y = z at hyz
      subst z
      exact ⟨x, rfl, hxy⟩
  | succ n ih =>
      obtain ⟨w, hyw, hwz⟩ := hyz
      exact ⟨w, ih hyw, hwz⟩

theorem relationPower_to_closure {R : X → X → Prop} {n : ℕ} {x y : X}
    (h : relationPower R n x y) : Relation.ReflTransGen R x y := by
  induction n generalizing y with
  | zero => exact h ▸ Relation.ReflTransGen.refl
  | succ n ih =>
      obtain ⟨z, hxz, hzy⟩ := h
      exact (ih hxz).tail hzy

/-- Original label: `defn:reflexive-transitive-closure`.
The inductive closure used by tuple connectivity equals the literal union
of relation powers (including the diagonal at power zero). -/
theorem closure_iff_exists_power (R : X → X → Prop) (x y : X) :
    Relation.ReflTransGen R x y ↔ ∃ n, relationPower R n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hzy ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, _, hn, hzy⟩
  · rintro ⟨n, hn⟩
    exact relationPower_to_closure hn

/-- Deleting cycles gives a chain with no repeated vertices. This construction
uses only forward edges, so it also applies to directed relations. -/
theorem closure_exists_nodup_chain {R : X → X → Prop} {x y : X}
    (h : Relation.ReflTransGen R x y) :
    ∃ l : List X, (x :: l).IsChain R ∧ (x :: l).Nodup ∧
      (x :: l).getLast (List.cons_ne_nil _ _) = y := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .singleton _, by simp, rfl⟩
  | @head a c hac _ ih =>
      obtain ⟨l, hchain, hnodup, hlast⟩ := ih
      by_cases ha : a ∈ c :: l
      · obtain ⟨s, t, hst⟩ := List.mem_iff_append.mp ha
        rw [hst] at hchain hnodup
        refine ⟨t, hchain.right_of_append, hnodup.of_append_right, ?_⟩
        simpa only [hst, List.getLast_append_of_right_ne_nil s (a :: t)
          (List.cons_ne_nil _ _)] using hlast
      · exact ⟨c :: l, .cons_cons hac hchain, List.nodup_cons.mpr ⟨ha, hnodup⟩,
          by simpa only [List.getLast_cons_cons] using hlast⟩

theorem chain_relationPower {R : X → X → Prop} {x : X} {l : List X}
    (h : (x :: l).IsChain R) :
    relationPower R l.length x ((x :: l).getLast (List.cons_ne_nil _ _)) := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih =>
      obtain ⟨hxy, htail⟩ := List.isChain_cons_cons.mp h
      exact relationPower_head hxy (ih htail)

/-- Original label: `prop:transitive-closure-finite`.
For every relation on a finite carrier, every reachable pair has a witness
with fewer edges than the number of vertices. No symmetry is needed. -/
theorem closure_iff_exists_bounded_power [Fintype X] (R : X → X → Prop) (x y : X) :
    Relation.ReflTransGen R x y ↔
      ∃ n < Fintype.card X, relationPower R n x y := by
  constructor
  · intro h
    obtain ⟨l, hchain, hnodup, hlast⟩ := closure_exists_nodup_chain h
    refine ⟨l.length, ?_, ?_⟩
    · have hlen := hnodup.length_le_card
      simpa using hlen
    · simpa only [hlast] using chain_relationPower hchain
  · rintro ⟨n, _, hn⟩
    exact relationPower_to_closure hn

/-- Original label: `prop:transitive-closure-finite`.
The exact displayed formula: diagonal union the powers from one to |X|-1.
It also holds for an empty carrier, where there are no pairs to check. -/
theorem finite_closure_formula [Fintype X] (R : X → X → Prop) (x y : X) :
    Relation.ReflTransGen R x y ↔
      x = y ∨ ∃ n, 1 ≤ n ∧ n ≤ Fintype.card X - 1 ∧ relationPower R n x y := by
  constructor
  · intro h
    obtain ⟨n, hn, hpow⟩ := (closure_iff_exists_bounded_power R x y).mp h
    cases n with
    | zero => exact Or.inl hpow
    | succ n => exact Or.inr ⟨n + 1, by omega, by omega, hpow⟩
  · rintro (rfl | ⟨n, _, _, hn⟩)
    · exact Relation.ReflTransGen.refl
    · exact relationPower_to_closure hn

/-- Original label: `defn:reflexive-transitive-closure`.
Literal equality of subsets of X × X, with the diagonal displayed separately. -/
theorem closure_eq_diagonal_union_powers (R : X → X → Prop) :
    {p : X × X | Relation.ReflTransGen R p.1 p.2} =
      {p : X × X | p.1 = p.2} ∪
        ⋃ n ∈ Set.Ici 1, {p : X × X | relationPower R n p.1 p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ici, exists_prop]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (closure_iff_exists_power R x y).mp h
    cases n with
    | zero => exact Or.inl hn
    | succ n => exact Or.inr ⟨n + 1, by omega, hn⟩
  · rintro (rfl | ⟨n, _, hn⟩)
    · exact Relation.ReflTransGen.refl
    · exact relationPower_to_closure hn

/-- Original label: `prop:transitive-closure-finite`.
The finite closure formula as literal equality of relations viewed as sets. -/
theorem finite_closure_eq_diagonal_union_powers [Fintype X] (R : X → X → Prop) :
    {p : X × X | Relation.ReflTransGen R p.1 p.2} =
      {p : X × X | p.1 = p.2} ∪
        ⋃ n ∈ Set.Icc 1 (Fintype.card X - 1),
          {p : X × X | relationPower R n p.1 p.2} := by
  ext ⟨x, y⟩
  simpa only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc,
    exists_prop, and_assoc] using finite_closure_formula R x y

end Thesis.Foundations.MarketRepresentation.FiniteRelationClosure
