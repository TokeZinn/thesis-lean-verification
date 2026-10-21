import Thesis.DayAhead.ClearingOperatorPriceCurves.ExcessSupply
import Thesis.DayAhead.ClearingOperatorPriceCurves.PiecewiseAffinePriceCurves

/-! # Affine accepted-volume pieces of the exact interpolated order book

These formulas concern the supremum-defined accepted volume, rather than an
independently postulated inverse. Repeated quantities (zero-volume orders)
are allowed. The affine formula is local to an open interval between adjacent
distinct nodal prices; nodal prices themselves require singleton cells.
-/

noncomputable section
namespace Thesis.DayAhead.InterpolatedOffered

open Set InterpolatedSide ExcessSupply

theorem curve_prefix_le {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0)
    (i : Fin (n + 1)) (q : ℝ) (hq : q ∈ Ioc 0 (Q i)) : curve p Q q ≤ p i := by
  obtain ⟨j, hj⟩ := exists_cell Q hz hq.1 (hq.2.trans (hQ (Fin.le_last i)))
  have hji : j.succ ≤ i := by
    by_contra h
    change ¬(j.val + 1 ≤ i.val) at h
    have hij : i ≤ j.castSucc := by exact_mod_cast (by omega : i.val ≤ j.val)
    exact (not_lt_of_ge (hq.2.trans (hQ hij))) hj.1
  rw [curve_on_cell p Q hQ hz j hj]
  exact (interpolate_mem_Icc (hj.1.trans_le hj.2) ⟨hj.1.le, hj.2⟩
    (hp (Fin.castSucc_le_succ j))).2.trans (hp hji)

theorem curve_suffix_ge {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0)
    (i : Fin (n + 1)) (q : ℝ) (hq : q ∈ Ioc (Q i) (Q (Fin.last n))) :
    p i ≤ curve p Q q := by
  have hqi : 0 ≤ Q i := hz ▸ hQ (Fin.zero_le i)
  obtain ⟨j, hj⟩ := exists_cell Q hz (hqi.trans_lt hq.1) hq.2
  have hij : i ≤ j.castSucc := by
    by_contra h
    change ¬(i.val ≤ j.val) at h
    have hji : j.succ ≤ i := by exact_mod_cast (by omega : j.val + 1 ≤ i.val)
    exact (not_lt_of_ge (hj.2.trans (hQ hji))) hq.1
  rw [curve_on_cell p Q hQ hz j hj]
  exact (hp hij).trans (interpolate_mem_Icc (hj.1.trans_le hj.2) ⟨hj.1.le, hj.2⟩
    (hp (Fin.castSucc_le_succ j))).1

theorem interpolate_strictMono {l r a b : ℝ} (hlr : l < r) (hab : a < b) :
    StrictMono (interpolate l r a b) := by
  intro x y hxy
  rw [interpolate, interpolate, div_lt_div_iff_of_pos_right (sub_pos.mpr hlr)]
  nlinarith [mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hab)]

theorem interpolate_inverse {l r a b : ℝ} (hlr : l ≠ r) (hab : a ≠ b) (x : ℝ) :
    interpolate l r a b (interpolate a b l r x) = x := by
  unfold interpolate
  field_simp [sub_ne_zero.mpr hlr.symm, sub_ne_zero.mpr hab.symm]
  ring

/-- On an open nodal-price interval, the actual accepted quantity is the
affine interpolation with quantity and price axes exchanged. The statement
also covers a zero-volume order, in which case the formula is constant. -/
theorem offered_on_price_cell {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (j : Fin n)
    (level : ℝ) (hlevel : level ∈ Ioo (p j.castSucc) (p j.succ)) :
    offered (Q (Fin.last n)) (curve p Q) level =
      interpolate (p j.castSucc) (p j.succ) (Q j.castSucc) (Q j.succ) level := by
  let t := interpolate (p j.castSucc) (p j.succ) (Q j.castSucc) (Q j.succ) level
  have hpp : p j.castSucc < p j.succ := hlevel.1.trans hlevel.2
  have hQQ : Q j.castSucc ≤ Q j.succ := hQ (Fin.castSucc_le_succ j)
  have ht : t ∈ Icc (Q j.castSucc) (Q j.succ) :=
    interpolate_mem_Icc hpp ⟨hlevel.1.le, hlevel.2.le⟩ hQQ
  have hzero : 0 ≤ Q j.castSucc := hz ▸ hQ (Fin.zero_le _)
  have hdepth : 0 ≤ Q (Fin.last n) := hz ▸ hQ (Fin.zero_le _)
  have htdepth : t ≤ Q (Fin.last n) := ht.2.trans (hQ (Fin.le_last _))
  have haccept : ∀ q ∈ Ioc 0 (Q (Fin.last n)), curve p Q q ≤ level ↔ q ≤ t := by
    intro q hq
    by_cases hleft : q ≤ Q j.castSucc
    · have hs := curve_prefix_le p Q hp hQ hz j.castSucc q ⟨hq.1, hleft⟩
      exact iff_of_true (hs.trans hlevel.1.le) (hleft.trans ht.1)
    · by_cases hright : q ≤ Q j.succ
      · have hcell : q ∈ cell Q j := ⟨lt_of_not_ge hleft, hright⟩
        have hwidth : Q j.castSucc < Q j.succ := hcell.1.trans_le hcell.2
        have hinv : interpolate (Q j.castSucc) (Q j.succ)
            (p j.castSucc) (p j.succ) t = level :=
          interpolate_inverse hwidth.ne hpp.ne level
        rw [curve_on_cell p Q hQ hz j hcell, ← hinv]
        exact (interpolate_strictMono hwidth hpp).le_iff_le
      · have hs := curve_suffix_ge p Q hp hQ hz j.succ q ⟨lt_of_not_ge hright, hq.2⟩
        exact iff_of_false (not_le.mpr (hlevel.2.trans_le hs))
          (not_le.mpr (ht.2.trans_lt (lt_of_not_ge hright)))
  apply le_antisymm
  · apply csSup_le (offeredSet_nonempty _ _ _)
    intro q hq
    rcases hq with rfl | hq
    · exact hzero.trans ht.1
    · exact (haccept q hq.1).mp hq.2
  · apply le_csSup (offeredSet_bddAbove _ hdepth _ _)
    rcases eq_or_lt_of_le (hzero.trans ht.1) with ht0 | htpos
    · exact Or.inl ht0.symm
    · exact Or.inr ⟨⟨htpos, htdepth⟩, (haccept t ⟨htpos, htdepth⟩).mpr le_rfl⟩

theorem offered_on_price_cell_affine {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (j : Fin n) :
    ∃ a b : ℝ, ∀ level ∈ Ioo (p j.castSucc) (p j.succ),
      offered (Q (Fin.last n)) (curve p Q) level = a * level + b := by
  obtain ⟨a, b, h⟩ := interpolate_affine (p j.castSucc) (p j.succ)
    (Q j.castSucc) (Q j.succ)
  exact ⟨a, b, fun level hl => (offered_on_price_cell p Q hp hQ hz j level hl).trans (h level)⟩

end Thesis.DayAhead.InterpolatedOffered
