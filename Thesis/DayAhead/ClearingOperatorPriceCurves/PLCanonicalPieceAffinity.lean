import Thesis.DayAhead.ClearingOperatorPriceCurves.PLBreakpointGrid

/-! # Actual affinity of the canonical maximal positive-width pieces

Restrict the finite candidate path between two retained nodes and merge all
discarded joins. Consecutive canonical nodes contain no intrinsic
breakpoint, so this finite source pruning gives one affine formula there.
-/

noncomputable section
namespace Thesis.DayAhead.PLCanonicalPieceAffinity

open Set PiecewiseAffinePriceCurves PLCanonicalEncoding PLBreakpointGrid

theorem affine_between_grid_nodes (f : Curve) {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hy : StrictMono y)
    (hgaps : ∀ k : Fin n, ∃ A B : ℝ,
      ∀ x ∈ Ioo (y k.castSucc) (y k.succ), f.price x = A * x + B)
    (i j : Fin (n + 1)) (hij : i < j)
    (hjoins : ∀ k, y i < y k → y k < y j → AffineNear f (y k)) :
    ∃ A B : ℝ, ∀ x ∈ Ioo (y i) (y j), f.price x = A * x + B := by
  let d := j.val - i.val - 1
  have hijv : i.val < j.val := hij
  let index : Fin (d + 2) → Fin (n + 1) :=
    fun k => ⟨i.val + k.val, by dsimp [d] at *; omega⟩
  let subgrid : Fin (d + 2) → ℝ := fun k => y (index k)
  have hindex : StrictMono index := by
    intro a b hab
    change i.val + a.val < i.val + b.val
    exact Nat.add_lt_add_left hab _
  have hsub : StrictMono subgrid := hy.comp hindex
  have hfirst : subgrid 0 = y i := by
    change y ⟨i.val + 0, _⟩ = y i
    congr 1
  have hlast : subgrid (Fin.last (d + 1)) = y j := by
    change y ⟨i.val + (d + 1), _⟩ = y j
    congr 1
    apply Fin.ext
    dsimp [d]
    omega
  have hsg : ∀ k : Fin (d + 1), ∃ A B : ℝ,
      ∀ x ∈ Ioo (subgrid k.castSucc) (subgrid k.succ), f.price x = A * x + B := by
    intro k
    let orig : Fin n := ⟨i.val + k.val, by dsimp [d] at *; omega⟩
    have he1 : index k.castSucc = orig.castSucc := by apply Fin.ext; rfl
    have he2 : index k.succ = orig.succ := by apply Fin.ext; dsimp [index, orig]; omega
    simpa only [subgrid, he1, he2] using hgaps orig
  have hsj : ∀ k : Fin d, AffineNear f (subgrid k.succ.castSucc) := by
    intro k
    apply hjoins (index k.succ.castSucc)
    · rw [← hfirst]
      exact hsub (by change 0 < k.val + 1; omega)
    · rw [← hlast]
      exact hsub (by change k.val + 1 < d + 1; omega)
  simpa only [hfirst, hlast] using affine_on_grid_of_local_joins f subgrid hsub hsg hsj

theorem leftKnot_mem_grid (f : Curve) {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hfirst : y 0 = f.leftEndpoint) (hzero : 0 ∈ Set.range y)
    (hbreaks : breakpoints f ⊆ Set.range y) (i : Fin (leftCount f + 1)) :
    leftKnot f i ∈ Set.range y := by
  have hm := enumeration_mem (leftNodes f) (leftNodes_nonempty f) i
  simp only [leftNodes, Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset] at hm
  rcases hm with h | h | h
  · change leftKnot f i = f.leftEndpoint at h
    rw [h]
    exact ⟨0, hfirst⟩
  · change leftKnot f i = 0 at h
    rwa [h]
  · exact hbreaks h.1

theorem rightKnot_mem_grid (f : Curve) {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hlast : y (Fin.last n) = f.rightEndpoint) (hzero : 0 ∈ Set.range y)
    (hbreaks : breakpoints f ⊆ Set.range y) (i : Fin (rightCount f + 1)) :
    rightKnot f i ∈ Set.range y := by
  have hm := enumeration_mem (rightNodes f) (rightNodes_nonempty f) i
  simp only [rightNodes, Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset] at hm
  rcases hm with h | h | h
  · change rightKnot f i = 0 at h
    rwa [h]
  · change rightKnot f i = f.rightEndpoint at h
    rw [h]
    exact ⟨Fin.last n, hlast⟩
  · exact hbreaks h.1

theorem canonical_left_piece_affine (f : Curve) {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hy : StrictMono y) (hfirst : y 0 = f.leftEndpoint)
    (hlast : y (Fin.last n) = f.rightEndpoint) (hzero : 0 ∈ Set.range y)
    (hgaps : ∀ k : Fin n, ∃ A B : ℝ,
      ∀ x ∈ Ioo (y k.castSucc) (y k.succ), f.price x = A * x + B)
    (j : Fin (leftCount f)) :
    ∃ A B : ℝ, ∀ x ∈ Ioo (leftKnot f j.castSucc) (leftKnot f j.succ),
      f.price x = A * x + B := by
  have hbreaks := breakpoints_subset_grid f y hfirst hlast hgaps
  obtain ⟨a, ha⟩ := leftKnot_mem_grid f y hfirst hzero hbreaks j.castSucc
  obtain ⟨b, hb⟩ := leftKnot_mem_grid f y hfirst hzero hbreaks j.succ
  have hknots := (enumeration (leftNodes f) (leftNodes_nonempty f)).strictMono
  have hab : a < b := hy.lt_iff_lt.mp (by rw [ha, hb]; exact hknots (Fin.castSucc_lt_succ (i := j)))
  have hjoins : ∀ k, y a < y k → y k < y b → AffineNear f (y k) := by
    intro k hak hkb
    rw [ha] at hak
    rw [hb] at hkb
    by_contra hlocal
    have hbl := leftNodes_bounds f
      (enumeration_mem (leftNodes f) (leftNodes_nonempty f) j.castSucc)
    have hbr := leftNodes_bounds f
      (enumeration_mem (leftNodes f) (leftNodes_nonempty f) j.succ)
    have hq : y k ∈ breakpoints f :=
      ⟨⟨hbl.1.trans_lt hak, hkb.trans_le (hbr.2.trans f.right_nonneg)⟩,
        ne_of_lt (hkb.trans_le hbr.2), hlocal⟩
    have hm : y k ∈ (leftNodes f : Set ℝ) := by
      simp only [leftNodes, Finset.coe_insert, mem_insert_iff, Finset.mem_coe,
        Finset.mem_filter, Set.Finite.mem_toFinset]
      exact Or.inr (Or.inr ⟨hq, hkb.trans_le hbr.2⟩)
    obtain ⟨z, hz⟩ := (enumeration_range _ (leftNodes_nonempty f)).symm ▸ hm
    apply OfferedPartition.node_not_open (leftKnot f) hknots.monotone z j
    change leftKnot f z = y k at hz
    rw [hz]
    exact ⟨hak, hkb⟩
  simpa only [ha, hb] using affine_between_grid_nodes f y hy hgaps a b hab hjoins

theorem canonical_right_piece_affine (f : Curve) {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hy : StrictMono y) (hfirst : y 0 = f.leftEndpoint)
    (hlast : y (Fin.last n) = f.rightEndpoint) (hzero : 0 ∈ Set.range y)
    (hgaps : ∀ k : Fin n, ∃ A B : ℝ,
      ∀ x ∈ Ioo (y k.castSucc) (y k.succ), f.price x = A * x + B)
    (j : Fin (rightCount f)) :
    ∃ A B : ℝ, ∀ x ∈ Ioo (rightKnot f j.castSucc) (rightKnot f j.succ),
      f.price x = A * x + B := by
  have hbreaks := breakpoints_subset_grid f y hfirst hlast hgaps
  obtain ⟨a, ha⟩ := rightKnot_mem_grid f y hlast hzero hbreaks j.castSucc
  obtain ⟨b, hb⟩ := rightKnot_mem_grid f y hlast hzero hbreaks j.succ
  have hknots := (enumeration (rightNodes f) (rightNodes_nonempty f)).strictMono
  have hab : a < b := hy.lt_iff_lt.mp (by rw [ha, hb]; exact hknots (Fin.castSucc_lt_succ (i := j)))
  have hjoins : ∀ k, y a < y k → y k < y b → AffineNear f (y k) := by
    intro k hak hkb
    rw [ha] at hak
    rw [hb] at hkb
    by_contra hlocal
    have hbl := rightNodes_bounds f
      (enumeration_mem (rightNodes f) (rightNodes_nonempty f) j.castSucc)
    have hbr := rightNodes_bounds f
      (enumeration_mem (rightNodes f) (rightNodes_nonempty f) j.succ)
    have hq : y k ∈ breakpoints f :=
      ⟨⟨(f.left_nonpos.trans hbl.1).trans_lt hak, hkb.trans_le hbr.2⟩,
        ne_of_gt (hbl.1.trans_lt hak), hlocal⟩
    have hm : y k ∈ (rightNodes f : Set ℝ) := by
      simp only [rightNodes, Finset.coe_insert, mem_insert_iff, Finset.mem_coe,
        Finset.mem_filter, Set.Finite.mem_toFinset]
      exact Or.inr (Or.inr ⟨hq, hbl.1.trans_lt hak⟩)
    obtain ⟨z, hz⟩ := (enumeration_range _ (rightNodes_nonempty f)).symm ▸ hm
    apply OfferedPartition.node_not_open (rightKnot f) hknots.monotone z j
    change rightKnot f z = y k at hz
    rw [hz]
    exact ⟨hak, hkb⟩
  simpa only [ha, hb] using affine_between_grid_nodes f y hy hgaps a b hab hjoins

end Thesis.DayAhead.PLCanonicalPieceAffinity
