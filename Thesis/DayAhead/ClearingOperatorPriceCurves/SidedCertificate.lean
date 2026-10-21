import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedParametrisation

/-!
# Minimal-representation support for canonical sided certificates

This module supplies the cell-order and endpoint lemmas used by the canonical
side-filtered construction.
-/

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation Set

noncomputable section

def cellReal {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : Set ℝ :=
  Subtype.val '' m.cell i

theorem cellReal_nonempty {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : (cellReal m i).Nonempty := by
  obtain ⟨x, hx⟩ := m.cell_nonempty i
  exact ⟨x, x, hx, rfl⟩

theorem cellReal_bddAbove {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : BddAbove (cellReal m i) := by
  refine ⟨f.rightEndpoint, ?_⟩
  rintro x ⟨y, _hy, rfl⟩
  exact y.property.2

noncomputable def cellSup {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : ℝ :=
  sSup (cellReal m i)

theorem le_cellSup_of_mem {f : PriceCurve} (m : MinimalRepresentation f)
    {i : Fin m.blockCount} {x : Set.Icc f.leftEndpoint f.rightEndpoint}
    (hx : x ∈ m.cell i) : (x : ℝ) ≤ cellSup m i := by
  exact le_csSup (cellReal_bddAbove m i) ⟨x, hx, rfl⟩

theorem leftEndpoint_le_cellSup {f : PriceCurve}
    (m : MinimalRepresentation f) (i : Fin m.blockCount) :
    f.leftEndpoint ≤ cellSup m i := by
  obtain ⟨x, hx⟩ := m.cell_nonempty i
  exact x.property.1.trans (le_cellSup_of_mem m hx)

theorem cellSup_le_rightEndpoint {f : PriceCurve}
    (m : MinimalRepresentation f) (i : Fin m.blockCount) :
    cellSup m i ≤ f.rightEndpoint := by
  apply csSup_le (cellReal_nonempty m i)
  rintro x ⟨y, _hy, rfl⟩
  exact y.property.2

theorem cellSup_mono {f : PriceCurve} (m : MinimalRepresentation f) :
    Monotone (cellSup m) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · apply csSup_le (cellReal_nonempty m i)
    rintro x ⟨xi, hxi, rfl⟩
    obtain ⟨yj, hyj⟩ := m.cell_nonempty j
    calc
      (xi : ℝ) ≤ yj := m.cell_ordered i j hij xi hxi yj hyj
      _ ≤ cellSup m j := le_cellSup_of_mem m hyj

def lastBlock {f : PriceCurve} (m : MinimalRepresentation f) :
    Fin m.blockCount :=
  ⟨m.blockCount - 1, by
    have hpos := m.blockCount_pos
    omega⟩

theorem le_lastBlock {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : i ≤ lastBlock m := by
  apply Fin.mk_le_mk.mpr
  have hpos := m.blockCount_pos
  have hi := i.isLt
  change (i : ℕ) ≤ m.blockCount - 1
  omega

theorem rightEndpoint_mem_lastCell {f : PriceCurve}
    (m : MinimalRepresentation f) :
    (⟨f.rightEndpoint,
      f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg, le_rfl⟩ :
        Set.Icc f.leftEndpoint f.rightEndpoint) ∈ m.cell (lastBlock m) := by
  let rpoint : Set.Icc f.leftEndpoint f.rightEndpoint :=
    ⟨f.rightEndpoint,
      f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg, le_rfl⟩
  have hrUnion : rpoint ∈ ⋃ i, m.cell i := by
    rw [m.cell_cover]
    exact Set.mem_univ rpoint
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hrUnion
  have hile : i ≤ lastBlock m := le_lastBlock m i
  have hiLast : i = lastBlock m := by
    by_contra hne
    have hilast : i < lastBlock m := lt_of_le_of_ne hile hne
    obtain ⟨y, hy⟩ := m.cell_nonempty (lastBlock m)
    have hry : rpoint ≤ y :=
      m.cell_ordered i (lastBlock m) hilast rpoint hi y hy
    have hyr : y ≤ rpoint := y.property.2
    have hyEq : y = rpoint := le_antisymm hyr hry
    rw [hyEq] at hy
    have hdis : Disjoint (m.cell i) (m.cell (lastBlock m)) :=
      m.cell_disjoint (Set.mem_univ i) (Set.mem_univ (lastBlock m)) hne
    exact (Set.disjoint_left.mp hdis) hi hy
  rw [← hiLast]
  exact hi

theorem cellSup_lastBlock {f : PriceCurve}
    (m : MinimalRepresentation f) :
    cellSup m (lastBlock m) = f.rightEndpoint := by
  apply le_antisymm (cellSup_le_rightEndpoint m (lastBlock m))
  exact le_cellSup_of_mem m (rightEndpoint_mem_lastCell m)

theorem price_eq_level_of_mem {f : PriceCurve}
    (m : MinimalRepresentation f) {i : Fin m.blockCount}
    {x : Set.Icc f.leftEndpoint f.rightEndpoint}
    (hx : x ∈ m.cell i) : f.price x = m.level i := by
  rw [m.represents x, Finset.sum_eq_single i]
  · simp only [Set.indicator_of_mem hx]
  · intro j _hj hji
    have hxj : x ∉ m.cell j := by
      intro hxj
      have hdis : Disjoint (m.cell i) (m.cell j) :=
        m.cell_disjoint (Set.mem_univ i) (Set.mem_univ j) hji.symm
      exact (Set.disjoint_left.mp hdis) hx hxj
    simp [Set.indicator, hxj]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem mem_cell_of_previous_sups_lt_of_lt_sup {f : PriceCurve}
    (m : MinimalRepresentation f) (j : Fin m.blockCount)
    (x : Set.Icc f.leftEndpoint f.rightEndpoint)
    (hprevious : ∀ k, k < j → cellSup m k < (x : ℝ))
    (hupper : (x : ℝ) < cellSup m j) :
    x ∈ m.cell j := by
  have hxUnion : x ∈ ⋃ i, m.cell i := by
    rw [m.cell_cover]
    exact Set.mem_univ x
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxUnion
  rcases lt_trichotomy k j with hkj | hkj | hjk
  · exact (not_lt_of_ge (le_cellSup_of_mem m hk) (hprevious k hkj)).elim
  · rw [hkj] at hk
    exact hk
  · have hsupLe : cellSup m j ≤ (x : ℝ) := by
      apply csSup_le (cellReal_nonempty m j)
      rintro y ⟨yj, hyj, rfl⟩
      exact m.cell_ordered j k hjk yj hyj x hk
    exact (not_lt_of_ge hsupLe hupper).elim

end

end Thesis.DayAhead.SidedCertificate
