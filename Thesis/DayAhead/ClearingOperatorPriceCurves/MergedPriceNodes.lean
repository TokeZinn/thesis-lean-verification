import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceNodeGaps
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalEncoding

/-! # The source's distinct merged nodal-price grid

Every original price is retained, duplicates are removed, and the finite set
is enumerated in increasing order. Consecutive nodes delimit actual affine
pieces of the supremum-defined excess supply.
-/
noncomputable section
namespace Thesis.DayAhead.MergedPriceNodes

open Set ExcessSupply PLCanonicalEncoding

variable {lo hi : ℝ}

def nodes (m : Book lo hi) : Finset ℝ :=
  Finset.univ.image m.sellPrice ∪ Finset.univ.image m.buyPrice

theorem sell_mem_nodes (m : Book lo hi) (i : Fin (m.sellCount + 1)) :
    m.sellPrice i ∈ nodes m := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem buy_mem_nodes (m : Book lo hi) (i : Fin (m.buyCount + 1)) :
    m.buyPrice i ∈ nodes m := by
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem nodes_nonempty (m : Book lo hi) : (nodes m).Nonempty :=
  ⟨_, sell_mem_nodes m 0⟩

theorem mem_nodes_bounds (m : Book lo hi) {p : ℝ} (hp : p ∈ nodes m) : p ∈ Icc lo hi := by
  rcases Finset.mem_union.mp hp with hs | hb
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact m.sellPrice_bounds i
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact m.buyPrice_bounds i

def gapCount (m : Book lo hi) : ℕ := count (nodes m)

def grid (m : Book lo hi) : Fin (gapCount m + 1) ↪o ℝ :=
  enumeration (nodes m) (nodes_nonempty m)

theorem grid_first (m : Book lo hi) : grid m 0 = lo := by
  apply enumeration_first
  refine ⟨?_, fun p hp => (mem_nodes_bounds m hp).1⟩
  simpa only [m.sellPrice_zero] using sell_mem_nodes m 0

theorem grid_last (m : Book lo hi) : grid m (Fin.last (gapCount m)) = hi := by
  apply enumeration_last
  refine ⟨?_, fun p hp => (mem_nodes_bounds m hp).2⟩
  simpa only [m.buyPrice_zero] using buy_mem_nodes m 0

theorem grid_bounds (m : Book lo hi) (i : Fin (gapCount m + 1)) : grid m i ∈ Icc lo hi :=
  mem_nodes_bounds m (enumeration_mem _ _ i)

theorem sell_eq_grid (m : Book lo hi) (i : Fin (m.sellCount + 1)) :
    ∃ k, grid m k = m.sellPrice i := by
  have h : m.sellPrice i ∈ (nodes m : Set ℝ) := sell_mem_nodes m i
  rw [← enumeration_range (nodes m) (nodes_nonempty m)] at h
  exact h

theorem buy_eq_grid (m : Book lo hi) (i : Fin (m.buyCount + 1)) :
    ∃ k, grid m k = m.buyPrice i := by
  have h : m.buyPrice i ∈ (nodes m : Set ℝ) := buy_mem_nodes m i
  rw [← enumeration_range (nodes m) (nodes_nonempty m)] at h
  exact h

theorem original_nodes_not_in_gap (m : Book lo hi) (j : Fin (gapCount m)) :
    (∀ i, m.sellPrice i ∉ Ioo (grid m j.castSucc) (grid m j.succ)) ∧
      (∀ i, m.buyPrice i ∉ Ioo (grid m j.castSucc) (grid m j.succ)) := by
  constructor
  · intro i hi
    obtain ⟨k, hk⟩ := sell_eq_grid m i
    exact OfferedPartition.node_not_open (grid m) (grid m).monotone k j (hk.symm ▸ hi)
  · intro i hi
    obtain ⟨k, hk⟩ := buy_eq_grid m i
    exact OfferedPartition.node_not_open (grid m) (grid m).monotone k j (hk.symm ▸ hi)

/-- The actual excess supply, on the exact distinct-price grid used by the
source path proof, is affine on every consecutive open segment. -/
theorem actual_excess_affine (m : Book lo hi) (j : Fin (gapCount m)) :
    ∃ A B : ℝ, ∀ p ∈ Ioo (grid m j.castSucc) (grid m j.succ),
      m.excess p = A*p+B := by
  exact PriceNodeGaps.excess_affine_on_gap m
    ((grid m).strictMono (Fin.castSucc_lt_succ (i := j)))
    (original_nodes_not_in_gap m j).1 (original_nodes_not_in_gap m j).2

end Thesis.DayAhead.MergedPriceNodes
