import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! # The current finite recursive regression-tree class

Chapter 5, lines 192–204. Every split tests an actual coordinate and threshold;
`ValidOn` requires nonempty terminal regions. This is distinct from the retired
historical representation by arbitrary indexed rectangles.
-/

noncomputable section
namespace Thesis.DayAhead.RecursiveTrees

open Set MeasureTheory

/-- Original label: `defn:rectangular-simple-function`.
An arbitrary finite family of interval rectangles is allowed; recursive tree
partitions form a particular subclass. -/
structure RectangularSimpleFunction (p : ℕ) (H : Type*) where
  domain : Set (Fin p → ℝ)
  count : ℕ
  count_pos : 0 < count
  intervals : Fin count → Fin p → Set ℝ
  interval : ∀ k j, OrdConnected (intervals k j)
  value : Fin count → H

def RectangularSimpleFunction.eval {p : ℕ} {H : Type*} [AddCommMonoid H]
    (r : RectangularSimpleFunction p H) (x : r.domain) : H := by
  classical
  exact ∑ k, if ∀ j, x.val j ∈ r.intervals k j then r.value k else 0

inductive Tree (p : ℕ) (H : Type*) where
  | leaf (value : H)
  | split (coordinate : Fin p) (cut : ℝ) (left right : Tree p H)

namespace Tree

variable {p : ℕ} {H : Type*}

def eval : Tree p H → (Fin p → ℝ) → H
  | .leaf y, _ => y
  | .split j c l r, x => if x j ≤ c then l.eval x else r.eval x

def leafCount : Tree p H → ℕ
  | .leaf _ => 1
  | .split _ _ l r => l.leafCount + r.leafCount

def depth : Tree p H → ℕ
  | .leaf _ => 0
  | .split _ _ l r => max l.depth r.depth + 1

def splitCount : Tree p H → ℕ
  | .leaf _ => 0
  | .split _ _ l r => l.splitCount + r.splitCount + 1

theorem leafCount_eq_splitCount_add_one (t : Tree p H) :
    t.leafCount = t.splitCount + 1 := by
  induction t with
  | leaf y => rfl
  | split j c l r hl hr => simp only [leafCount, splitCount, hl, hr]; omega

def ValidOn (R : Set (Fin p → ℝ)) : Tree p H → Prop
  | .leaf _ => R.Nonempty
  | .split j c l r => ValidOn (R ∩ {x | x j ≤ c}) l ∧ ValidOn (R ∩ {x | c < x j}) r

def leavesOn (R : Set (Fin p → ℝ)) : Tree p H → List (Set (Fin p → ℝ) × H)
  | .leaf y => [(R, y)]
  | .split j c l r => l.leavesOn (R ∩ {x | x j ≤ c}) ++
      r.leavesOn (R ∩ {x | c < x j})

theorem validOn_nonempty (t : Tree p H) (R : Set (Fin p → ℝ)) (h : t.ValidOn R) :
    R.Nonempty := by
  induction t generalizing R with
  | leaf y => exact h
  | split j c l r hl hr => exact (hl _ h.1).mono Set.inter_subset_left

theorem leafCount_pos (t : Tree p H) : 0 < t.leafCount := by
  induction t with
  | leaf _ => exact Nat.zero_lt_one
  | split j c l r hl hr => exact Nat.add_pos_left hl _

theorem leavesOn_length (t : Tree p H) (R : Set (Fin p → ℝ)) :
    (t.leavesOn R).length = t.leafCount := by
  induction t generalizing R with
  | leaf y => rfl
  | split j c l r hl hr => simp [leavesOn, leafCount, hl, hr]

theorem leavesOn_nonempty (t : Tree p H) (R : Set (Fin p → ℝ)) (h : t.ValidOn R) :
    ∀ s ∈ t.leavesOn R, s.1.Nonempty := by
  induction t generalizing R with
  | leaf y => simpa [leavesOn] using h
  | split j c l r hl hr =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hl _ h.1 s hs
    · exact hr _ h.2 s hs

theorem leavesOn_subset (t : Tree p H) (R : Set (Fin p → ℝ)) :
    ∀ s ∈ t.leavesOn R, s.1 ⊆ R := by
  induction t generalizing R with
  | leaf y => simp [leavesOn]
  | split j c l r hl hr =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact (hl _ s hs).trans Set.inter_subset_left
    · exact (hr _ s hs).trans Set.inter_subset_left

theorem leavesOn_cover (t : Tree p H) (R : Set (Fin p → ℝ)) (x : Fin p → ℝ) :
    (∃ s ∈ t.leavesOn R, x ∈ s.1) ↔ x ∈ R := by
  induction t generalizing R with
  | leaf y => simp [leavesOn]
  | split j c l r hl hr =>
    constructor
    · rintro ⟨s, hs, hx⟩
      exact leavesOn_subset (.split j c l r) R s hs hx
    · intro hx
      by_cases hc : x j ≤ c
      · obtain ⟨s, hs, hxs⟩ := (hl (R ∩ {x | x j ≤ c})).mpr ⟨hx, hc⟩
        exact ⟨s, List.mem_append_left _ hs, hxs⟩
      · obtain ⟨s, hs, hxs⟩ := (hr (R ∩ {x | c < x j})).mpr ⟨hx, lt_of_not_ge hc⟩
        exact ⟨s, List.mem_append_right _ hs, hxs⟩

theorem leavesOn_disjoint (t : Tree p H) (R : Set (Fin p → ℝ)) :
    (t.leavesOn R).Pairwise (fun s t => Disjoint s.1 t.1) := by
  induction t generalizing R with
  | leaf y => simp [leavesOn]
  | split j c l r hl hr =>
    apply List.pairwise_append.mpr
    refine ⟨hl _, hr _, ?_⟩
    intro s hs t ht
    apply Set.disjoint_left.mpr
    intro x hxs hxt
    have hsx := l.leavesOn_subset _ s hs hxs
    have htx := r.leavesOn_subset _ t ht hxt
    exact not_lt_of_ge (show x j ≤ c from hsx.2) (show c < x j from htx.2)

theorem eval_finite_range (t : Tree p H) : (Set.range t.eval).Finite := by
  induction t with
  | leaf y => simp [eval]
  | split j c l r hl hr =>
    apply (hl.union hr).subset
    rintro _ ⟨x, rfl⟩
    by_cases hx : x j ≤ c
    · exact Or.inl (by simp only [eval, if_pos hx]; exact Set.mem_range_self x)
    · exact Or.inr (by simp only [eval, if_neg hx]; exact Set.mem_range_self x)

theorem measurable_eval [MeasurableSpace H] (t : Tree p H) : Measurable t.eval := by
  induction t with
  | leaf y => exact measurable_const
  | split j c l r hl hr =>
    exact hl.ite (measurableSet_le (measurable_pi_apply j) measurable_const) hr

open Classical in
def rectangularSum [AddCommMonoid H] (cells : List (Set (Fin p → ℝ) × H)) (x : Fin p → ℝ) : H :=
  (cells.map fun s => if x ∈ s.1 then s.2 else 0).sum

open Classical in
/-- Traversal equals the rectangular simple-function representation, with
the same non-strict left and strict right inequalities as the current source. -/
theorem rectangularSum_leavesOn [AddCommMonoid H] (t : Tree p H)
    (R : Set (Fin p → ℝ)) (x : Fin p → ℝ) :
    rectangularSum (t.leavesOn R) x = if x ∈ R then t.eval x else 0 := by
  classical
  induction t generalizing R with
  | leaf y => simp [rectangularSum, leavesOn, eval]
  | split j c l r hl hr =>
    change rectangularSum
      (l.leavesOn (R ∩ {x | x j ≤ c}) ++ r.leavesOn (R ∩ {x | c < x j})) x = _
    simp only [rectangularSum, List.map_append, List.sum_append]
    change rectangularSum (l.leavesOn (R ∩ {x | x j ≤ c})) x +
      rectangularSum (r.leavesOn (R ∩ {x | c < x j})) x = _
    rw [hl, hr]
    by_cases hx : x ∈ R <;> by_cases hc : x j ≤ c <;>
      simp [hx, hc, eval, not_lt_of_ge, lt_of_not_ge]

theorem rectangularSum_root [AddCommMonoid H] (t : Tree p H) :
    rectangularSum (t.leavesOn Set.univ) = t.eval := by
  funext x
  simpa using rectangularSum_leavesOn t Set.univ x

end Tree

/-- Original label: `defn:k-leaf-tree-class`.
Exact finite recursive class with K nonempty terminal regions. -/
def treeClass (p : ℕ) (H : Type*) (K : ℕ) : Set ((Fin p → ℝ) → H) :=
  {f | ∃ t : Tree p H, t.ValidOn Set.univ ∧ t.leafCount = K ∧ t.eval = f}

end Thesis.DayAhead.RecursiveTrees
