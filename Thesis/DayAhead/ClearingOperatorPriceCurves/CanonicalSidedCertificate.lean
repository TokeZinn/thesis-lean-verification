import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedCertificate

/-!
# Canonical side-filtered certificates

This module constructs the exact sided decomposition used in the replacement
thesis chapter.  Starting from a global minimal representation, it filters the
blocks meeting `(-∞, 0)` and `(0, ∞)`, enumerates each filtered family in the
inherited order, and proves that the resulting inducing knots and levels form
a `SidedKnotData` certificate for the original curve.

The endpoint arguments include the zero-count cases and blocks reduced to a
singleton at zero.  Thus the construction is total on `PriceCurve`; it does
not silently assume that both sides of the volume domain are nondegenerate.
-/

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation Set

noncomputable section

/-! ## The side-filtered block sets 

 A minimal block is active on the left exactly when it contains a strictly
negative volume.  The strict inequality is the one used in the thesis's
definition of `L_f`. -/
def LeftActive {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : Prop :=
  ∃ x ∈ m.cell i, (x : ℝ) < 0

/-- A minimal block is active on the right exactly when it contains a strictly
positive volume.  The strict inequality is the one used in the thesis's
definition of `U_f`. -/
def RightActive {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : Prop :=
  ∃ x ∈ m.cell i, 0 < (x : ℝ)

noncomputable def leftActiveCells {f : PriceCurve}
    (m : MinimalRepresentation f) : Finset (Fin m.blockCount) := by
  classical
  exact Finset.univ.filter (LeftActive m)

noncomputable def rightActiveCells {f : PriceCurve}
    (m : MinimalRepresentation f) : Finset (Fin m.blockCount) := by
  classical
  exact Finset.univ.filter (RightActive m)

@[simp]
theorem mem_leftActiveCells {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : i ∈ leftActiveCells m ↔ LeftActive m i := by
  classical
  simp [leftActiveCells]

@[simp]
theorem mem_rightActiveCells {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) : i ∈ rightActiveCells m ↔ RightActive m i := by
  classical
  simp [rightActiveCells]

/-- Negative-active minimal cells form a prefix of the ordered cells. -/
theorem leftActive_of_le {f : PriceCurve} (m : MinimalRepresentation f)
    {i j : Fin m.blockCount} (hij : i ≤ j) (hj : LeftActive m j) :
    LeftActive m i := by
  obtain ⟨x, hxcell, hxneg⟩ := hj
  rcases hij.eq_or_lt with rfl | hij
  · exact ⟨x, hxcell, hxneg⟩
  · obtain ⟨y, hycell⟩ := m.cell_nonempty i
    refine ⟨y, hycell, ?_⟩
    have hyx : (y : ℝ) ≤ (x : ℝ) :=
      m.cell_ordered i j hij y hycell x hxcell
    exact hyx.trans_lt hxneg

/-- The thesis count `L_f`. 

 Original label: `defn:sided-essential-decomposition`. -/
noncomputable def leftCount {f : PriceCurve} (m : MinimalRepresentation f) : ℕ :=
  (leftActiveCells m).card

/-- The thesis count `U_f`. 

 Original label: `defn:sided-essential-decomposition`. -/
noncomputable def rightCount {f : PriceCurve} (m : MinimalRepresentation f) : ℕ :=
  (rightActiveCells m).card

/-- Increasing enumeration of the left-active global minimal blocks. -/
noncomputable def leftCell {f : PriceCurve} (m : MinimalRepresentation f) :
    Fin (leftCount m) ↪o Fin m.blockCount :=
  (leftActiveCells m).orderEmbOfFin rfl

/-- Increasing enumeration of the right-active global minimal blocks. -/
noncomputable def rightCell {f : PriceCurve} (m : MinimalRepresentation f) :
    Fin (rightCount m) ↪o Fin m.blockCount :=
  (rightActiveCells m).orderEmbOfFin rfl

theorem leftCell_active {f : PriceCurve} (m : MinimalRepresentation f)
    (j : Fin (leftCount m)) : LeftActive m (leftCell m j) := by
  exact (mem_leftActiveCells m (leftCell m j)).mp
    (Finset.orderEmbOfFin_mem (leftActiveCells m) rfl j)

theorem rightCell_active {f : PriceCurve} (m : MinimalRepresentation f)
    (j : Fin (rightCount m)) : RightActive m (rightCell m j) := by
  exact (mem_rightActiveCells m (rightCell m j)).mp
    (Finset.orderEmbOfFin_mem (rightActiveCells m) rfl j)

theorem exists_leftCell_eq_of_active {f : PriceCurve}
    (m : MinimalRepresentation f) {i : Fin m.blockCount}
    (hi : LeftActive m i) : ∃ j, leftCell m j = i := by
  let target : leftActiveCells m := ⟨i, (mem_leftActiveCells m i).2 hi⟩
  obtain ⟨j, hj⟩ := ((leftActiveCells m).orderIsoOfFin rfl).surjective target
  refine ⟨j, ?_⟩
  exact congrArg Subtype.val hj

theorem exists_rightCell_eq_of_active {f : PriceCurve}
    (m : MinimalRepresentation f) {i : Fin m.blockCount}
    (hi : RightActive m i) : ∃ j, rightCell m j = i := by
  let target : rightActiveCells m := ⟨i, (mem_rightActiveCells m i).2 hi⟩
  obtain ⟨j, hj⟩ := ((rightActiveCells m).orderIsoOfFin rfl).surjective target
  refine ⟨j, ?_⟩
  exact congrArg Subtype.val hj

theorem leftCell_lt_iff {f : PriceCurve} (m : MinimalRepresentation f)
    {i j : Fin (leftCount m)} : leftCell m i < leftCell m j ↔ i < j :=
  (leftCell m).lt_iff_lt

theorem rightCell_lt_iff {f : PriceCurve} (m : MinimalRepresentation f)
    {i j : Fin (rightCount m)} : rightCell m i < rightCell m j ↔ i < j :=
  (rightCell m).lt_iff_lt

def lastOfPos {n : ℕ} (h : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

theorem le_lastOfPos {n : ℕ} (h : 0 < n) (i : Fin n) :
    i ≤ lastOfPos h := by
  apply Fin.mk_le_mk.mpr
  have hi := i.isLt
  change (i : ℕ) ≤ n - 1
  omega

theorem lastOfPos_succ_eq_last {n : ℕ} (h : 0 < n) :
    (lastOfPos h).succ = Fin.last n := by
  apply Fin.ext
  change n - 1 + 1 = n
  omega

def previousFin {n : ℕ} (j : Fin n) : Fin n :=
  ⟨j - 1, by omega⟩

theorem previousFin_succ_eq_castSucc {n : ℕ} (j : Fin n)
    (hj : (j : ℕ) ≠ 0) :
    (previousFin j).succ = j.castSucc := by
  apply Fin.ext
  change (j : ℕ) - 1 + 1 = j
  omega

theorem le_previousFin_of_lt {n : ℕ} {j k : Fin n} (hkj : k < j) :
    k ≤ previousFin j := by
  apply Fin.mk_le_mk.mpr
  change (k : ℕ) ≤ (j : ℕ) - 1
  omega

theorem exists_cell_mem {f : PriceCurve} (m : MinimalRepresentation f)
    (x : Set.Icc f.leftEndpoint f.rightEndpoint) :
    ∃ i, x ∈ m.cell i := by
  have hx : x ∈ ⋃ i, m.cell i := by
    rw [m.cell_cover]
    exact Set.mem_univ x
  exact Set.mem_iUnion.mp hx

theorem cellSup_nonpos_of_not_rightActive {f : PriceCurve}
    (m : MinimalRepresentation f) {i : Fin m.blockCount}
    (hi : ¬ RightActive m i) : cellSup m i ≤ 0 := by
  apply csSup_le (cellReal_nonempty m i)
  rintro y ⟨x, hxcell, rfl⟩
  exact le_of_not_gt (fun hxpos => hi ⟨x, hxcell, hxpos⟩)

theorem leftEndpoint_eq_zero_of_leftCount_eq_zero {f : PriceCurve}
    (m : MinimalRepresentation f) (hzero : leftCount m = 0) :
    f.leftEndpoint = 0 := by
  apply le_antisymm f.leftEndpoint_nonpos
  by_contra hnot
  have hneg : f.leftEndpoint < 0 := lt_of_not_ge hnot
  let x : Set.Icc f.leftEndpoint f.rightEndpoint :=
    ⟨f.leftEndpoint, le_rfl,
      f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg⟩
  obtain ⟨i, hi⟩ := exists_cell_mem m x
  have hactive : LeftActive m i := ⟨x, hi, hneg⟩
  have hnonempty : (leftActiveCells m).Nonempty :=
    ⟨i, (mem_leftActiveCells m i).2 hactive⟩
  have hpos : 0 < leftCount m := by
    exact Finset.card_pos.mpr hnonempty
  omega

theorem rightEndpoint_eq_zero_of_rightCount_eq_zero {f : PriceCurve}
    (m : MinimalRepresentation f) (hzero : rightCount m = 0) :
    f.rightEndpoint = 0 := by
  apply le_antisymm _ f.rightEndpoint_nonneg
  by_contra hnot
  have hpos : 0 < f.rightEndpoint := lt_of_not_ge hnot
  let x : Set.Icc f.leftEndpoint f.rightEndpoint :=
    ⟨f.rightEndpoint,
      f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg, le_rfl⟩
  obtain ⟨i, hi⟩ := exists_cell_mem m x
  have hactive : RightActive m i := ⟨x, hi, hpos⟩
  have hnonempty : (rightActiveCells m).Nonempty :=
    ⟨i, (mem_rightActiveCells m i).2 hactive⟩
  have hcountPos : 0 < rightCount m := by
    exact Finset.card_pos.mpr hnonempty
  omega

/-- Side-filtered inducing knots on the negative half-domain. -/
def canonicalLeftKnot {f : PriceCurve} (m : MinimalRepresentation f) :
    Fin (leftCount m + 1) → ℝ :=
  Fin.cases f.leftEndpoint
    (fun j => min 0 (cellSup m (leftCell m j)))

/-- Side-filtered inducing knots on the positive half-domain. -/
def canonicalRightKnot {f : PriceCurve} (m : MinimalRepresentation f) :
    Fin (rightCount m + 1) → ℝ :=
  Fin.cases 0
    (fun j => max 0 (cellSup m (rightCell m j)))

@[simp]
theorem canonicalLeftKnot_zero {f : PriceCurve}
    (m : MinimalRepresentation f) :
    canonicalLeftKnot m 0 = f.leftEndpoint := rfl

@[simp]
theorem canonicalLeftKnot_succ {f : PriceCurve}
    (m : MinimalRepresentation f) (j : Fin (leftCount m)) :
    canonicalLeftKnot m j.succ = min 0 (cellSup m (leftCell m j)) := rfl

@[simp]
theorem canonicalRightKnot_zero {f : PriceCurve}
    (m : MinimalRepresentation f) :
    canonicalRightKnot m 0 = 0 := rfl

@[simp]
theorem canonicalRightKnot_succ {f : PriceCurve}
    (m : MinimalRepresentation f) (j : Fin (rightCount m)) :
    canonicalRightKnot m j.succ = max 0 (cellSup m (rightCell m j)) := rfl

theorem monotone_canonicalLeftKnot {f : PriceCurve}
    (m : MinimalRepresentation f) : Monotone (canonicalLeftKnot m) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact le_rfl
      | succ j =>
          rw [canonicalLeftKnot_zero, canonicalLeftKnot_succ]
          exact le_min f.leftEndpoint_nonpos
            (leftEndpoint_le_cellSup m (leftCell m j))
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hpos : (0 : Fin (leftCount m + 1)) < i.succ :=
            Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
          exact (not_lt_of_ge hij hpos).elim
      | succ j =>
          rw [canonicalLeftKnot_succ, canonicalLeftKnot_succ]
          exact min_le_min le_rfl
            (cellSup_mono m ((leftCell m).monotone (by simpa using hij)))

theorem monotone_canonicalRightKnot {f : PriceCurve}
    (m : MinimalRepresentation f) : Monotone (canonicalRightKnot m) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact le_rfl
      | succ j =>
          rw [canonicalRightKnot_zero, canonicalRightKnot_succ]
          exact le_max_left 0 _
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hpos : (0 : Fin (rightCount m + 1)) < i.succ :=
            Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
          exact (not_lt_of_ge hij hpos).elim
      | succ j =>
          rw [canonicalRightKnot_succ, canonicalRightKnot_succ]
          exact max_le_max le_rfl
            (cellSup_mono m ((rightCell m).monotone (by simpa using hij)))

theorem zero_le_cellSup_last_leftCell {f : PriceCurve}
    (m : MinimalRepresentation f) (hpos : 0 < leftCount m) :
    0 ≤ cellSup m (leftCell m (lastOfPos hpos)) := by
  by_contra hnot
  have hsupNeg : cellSup m (leftCell m (lastOfPos hpos)) < 0 :=
    lt_of_not_ge hnot
  let xReal : ℝ := cellSup m (leftCell m (lastOfPos hpos)) / 2
  have hsupx : cellSup m (leftCell m (lastOfPos hpos)) < xReal := by
    dsimp only [xReal]
    linarith
  have hxneg : xReal < 0 := by
    dsimp only [xReal]
    linarith
  let x : Set.Icc f.leftEndpoint f.rightEndpoint :=
    ⟨xReal,
      (leftEndpoint_le_cellSup m _).trans hsupx.le,
      hxneg.le.trans f.rightEndpoint_nonneg⟩
  obtain ⟨i, hi⟩ := exists_cell_mem m x
  have hactive : LeftActive m i := ⟨x, hi, hxneg⟩
  obtain ⟨j, hj⟩ := exists_leftCell_eq_of_active m hactive
  have hjlast : j ≤ lastOfPos hpos := le_lastOfPos hpos j
  have hsupLe : cellSup m i ≤
      cellSup m (leftCell m (lastOfPos hpos)) := by
    rw [← hj]
    exact cellSup_mono m ((leftCell m).monotone hjlast)
  have hxLe : xReal ≤ cellSup m i := le_cellSup_of_mem m hi
  linarith

theorem canonicalLeftKnot_last {f : PriceCurve}
    (m : MinimalRepresentation f) :
    canonicalLeftKnot m (Fin.last (leftCount m)) = 0 := by
  by_cases hzero : leftCount m = 0
  · have hendpoint := leftEndpoint_eq_zero_of_leftCount_eq_zero m hzero
    have hlast : Fin.last (leftCount m) = 0 := by
      apply Fin.ext
      simp [hzero]
    rw [hlast, canonicalLeftKnot_zero, hendpoint]
  · have hpos : 0 < leftCount m := Nat.pos_of_ne_zero hzero
    rw [← lastOfPos_succ_eq_last hpos, canonicalLeftKnot_succ,
      min_eq_left (zero_le_cellSup_last_leftCell m hpos)]

theorem last_rightCell_eq_lastBlock {f : PriceCurve}
    (m : MinimalRepresentation f) (hpos : 0 < rightCount m) :
    rightCell m (lastOfPos hpos) = lastBlock m := by
  obtain ⟨x, _hxcell, hxpos⟩ := rightCell_active m (lastOfPos hpos)
  have hrightPos : 0 < f.rightEndpoint := hxpos.trans_le x.property.2
  let rpoint : Set.Icc f.leftEndpoint f.rightEndpoint :=
    ⟨f.rightEndpoint,
      f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg, le_rfl⟩
  have hlastActive : RightActive m (lastBlock m) :=
    ⟨rpoint, rightEndpoint_mem_lastCell m, hrightPos⟩
  obtain ⟨j, hj⟩ := exists_rightCell_eq_of_active m hlastActive
  apply le_antisymm (le_lastBlock m _)
  rw [← hj]
  exact (rightCell m).monotone (le_lastOfPos hpos j)

theorem canonicalRightKnot_last {f : PriceCurve}
    (m : MinimalRepresentation f) :
    canonicalRightKnot m (Fin.last (rightCount m)) = f.rightEndpoint := by
  by_cases hzero : rightCount m = 0
  · have hendpoint := rightEndpoint_eq_zero_of_rightCount_eq_zero m hzero
    have hlast : Fin.last (rightCount m) = 0 := by
      apply Fin.ext
      simp [hzero]
    rw [hlast, canonicalRightKnot_zero, hendpoint]
  · have hpos : 0 < rightCount m := Nat.pos_of_ne_zero hzero
    rw [← lastOfPos_succ_eq_last hpos, canonicalRightKnot_succ,
      last_rightCell_eq_lastBlock m hpos, cellSup_lastBlock,
      max_eq_right f.rightEndpoint_nonneg]

theorem canonicalLeftKnot_nonpos {f : PriceCurve}
    (m : MinimalRepresentation f) (i : Fin (leftCount m + 1)) :
    canonicalLeftKnot m i ≤ 0 := by
  calc
    canonicalLeftKnot m i ≤
        canonicalLeftKnot m (Fin.last (leftCount m)) :=
      monotone_canonicalLeftKnot m (Fin.le_last i)
    _ = 0 := canonicalLeftKnot_last m

theorem canonicalRightKnot_nonneg {f : PriceCurve}
    (m : MinimalRepresentation f) (i : Fin (rightCount m + 1)) :
    0 ≤ canonicalRightKnot m i := by
  calc
    0 = canonicalRightKnot m 0 := (canonicalRightKnot_zero m).symm
    _ ≤ canonicalRightKnot m i :=
      monotone_canonicalRightKnot m (Fin.zero_le i)

theorem canonicalLeftKnot_castSucc_of_ne_zero {f : PriceCurve}
    (m : MinimalRepresentation f) (j : Fin (leftCount m))
    (hj : (j : ℕ) ≠ 0) :
    canonicalLeftKnot m j.castSucc =
      min 0 (cellSup m (leftCell m (previousFin j))) := by
  rw [← previousFin_succ_eq_castSucc j hj, canonicalLeftKnot_succ]

theorem canonicalRightKnot_castSucc_of_ne_zero {f : PriceCurve}
    (m : MinimalRepresentation f) (j : Fin (rightCount m))
    (hj : (j : ℕ) ≠ 0) :
    canonicalRightKnot m j.castSucc =
      max 0 (cellSup m (rightCell m (previousFin j))) := by
  rw [← previousFin_succ_eq_castSucc j hj, canonicalRightKnot_succ]

theorem mem_cell_of_between_canonicalLeftKnots {f : PriceCurve}
    (m : MinimalRepresentation f) (j : Fin (leftCount m))
    (x : Set.Icc f.leftEndpoint f.rightEndpoint)
    (hlower : canonicalLeftKnot m j.castSucc < (x : ℝ))
    (hupper : (x : ℝ) < canonicalLeftKnot m j.succ) :
    x ∈ m.cell (leftCell m j) := by
  have hxneg : (x : ℝ) < 0 :=
    hupper.trans_le (canonicalLeftKnot_nonpos m j.succ)
  have hupper' : (x : ℝ) < cellSup m (leftCell m j) := by
    rw [canonicalLeftKnot_succ] at hupper
    exact hupper.trans_le (min_le_right _ _)
  apply mem_cell_of_previous_sups_lt_of_lt_sup m (leftCell m j) x _ hupper'
  intro k hkj
  have hkactive : LeftActive m k :=
    leftActive_of_le m hkj.le (leftCell_active m j)
  obtain ⟨r, hr⟩ := exists_leftCell_eq_of_active m hkactive
  have hrj : r < j := by
    apply (leftCell_lt_iff m).mp
    rwa [hr]
  by_cases hjzero : (j : ℕ) = 0
  · have hrnat : (r : ℕ) < (j : ℕ) := hrj
    rw [hjzero] at hrnat
    omega
  · have hlower' := hlower
    rw [canonicalLeftKnot_castSucc_of_ne_zero m j hjzero] at hlower'
    have hprevSup : cellSup m (leftCell m (previousFin j)) < (x : ℝ) := by
      by_cases hs : cellSup m (leftCell m (previousFin j)) ≤ 0
      · rwa [min_eq_right hs] at hlower'
      · have hs0 : 0 ≤ cellSup m (leftCell m (previousFin j)) :=
          le_of_not_ge hs
        rw [min_eq_left hs0] at hlower'
        linarith
    calc
      cellSup m k = cellSup m (leftCell m r) := by rw [hr]
      _ ≤ cellSup m (leftCell m (previousFin j)) :=
        cellSup_mono m ((leftCell m).monotone
          (le_previousFin_of_lt hrj))
      _ < (x : ℝ) := hprevSup

theorem mem_cell_of_between_canonicalRightKnots {f : PriceCurve}
    (m : MinimalRepresentation f) (j : Fin (rightCount m))
    (x : Set.Icc f.leftEndpoint f.rightEndpoint)
    (hlower : canonicalRightKnot m j.castSucc < (x : ℝ))
    (hupper : (x : ℝ) < canonicalRightKnot m j.succ) :
    x ∈ m.cell (rightCell m j) := by
  have hxpos : 0 < (x : ℝ) :=
    (canonicalRightKnot_nonneg m j.castSucc).trans_lt hlower
  have hupper' : (x : ℝ) < cellSup m (rightCell m j) := by
    rw [canonicalRightKnot_succ] at hupper
    by_cases hs : 0 ≤ cellSup m (rightCell m j)
    · rwa [max_eq_right hs] at hupper
    · have hs0 : cellSup m (rightCell m j) ≤ 0 := le_of_not_ge hs
      rw [max_eq_left hs0] at hupper
      linarith
  apply mem_cell_of_previous_sups_lt_of_lt_sup m (rightCell m j) x _ hupper'
  intro k hkj
  by_cases hkactive : RightActive m k
  · obtain ⟨r, hr⟩ := exists_rightCell_eq_of_active m hkactive
    have hrj : r < j := by
      apply (rightCell_lt_iff m).mp
      rwa [hr]
    by_cases hjzero : (j : ℕ) = 0
    · have hrnat : (r : ℕ) < (j : ℕ) := hrj
      rw [hjzero] at hrnat
      omega
    · have hlower' := hlower
      rw [canonicalRightKnot_castSucc_of_ne_zero m j hjzero] at hlower'
      have hprevSup : cellSup m (rightCell m (previousFin j)) < (x : ℝ) :=
        (le_max_right 0 _).trans_lt hlower'
      calc
        cellSup m k = cellSup m (rightCell m r) := by rw [hr]
        _ ≤ cellSup m (rightCell m (previousFin j)) :=
          cellSup_mono m ((rightCell m).monotone
            (le_previousFin_of_lt hrj))
        _ < (x : ℝ) := hprevSup
  · exact (cellSup_nonpos_of_not_rightActive m hkactive).trans_lt hxpos

/--
Thesis source: the sided decomposition and inducing-knot display
`eq:inducing-points` in
`2 - day-ahead/2_clearing_operator_price_curves.tex`.

Original label: `eq:inducing-points`.

The exact side-filtered certificate described in the replacement thesis
chapter. Its counts are the numbers of minimal blocks meeting the strict
negative and strict positive half-domains, respectively.
-/
def canonicalSidedKnotDataOfMinimal {f : PriceCurve}
    (m : MinimalRepresentation f) : SidedKnotData f where
  leftCount := leftCount m
  rightCount := rightCount m
  leftKnot := canonicalLeftKnot m
  rightKnot := canonicalRightKnot m
  leftKnot_monotone := monotone_canonicalLeftKnot m
  rightKnot_monotone := monotone_canonicalRightKnot m
  left_first := canonicalLeftKnot_zero m
  left_last := canonicalLeftKnot_last m
  right_first := canonicalRightKnot_zero m
  right_last := canonicalRightKnot_last m
  leftLevel := fun j => m.level (leftCell m j)
  rightLevel := fun j => m.level (rightCell m j)
  left_block_interior := by
    intro j x hlower hupper
    exact price_eq_level_of_mem m
      (mem_cell_of_between_canonicalLeftKnots m j x hlower hupper)
  right_block_interior := by
    intro j x hlower hupper
    exact price_eq_level_of_mem m
      (mem_cell_of_between_canonicalRightKnots m j x hlower hupper)
  leftLevel_strictMono := by
    intro i j hij
    exact m.level_strictMono ((leftCell m).strictMono hij)
  rightLevel_strictMono := by
    intro i j hij
    exact m.level_strictMono ((rightCell m).strictMono hij)

/-- Every chosen minimal representation determines the thesis's exact
side-filtered canonical curve certificate. -/
def canonicalSidedCurveOfMinimal {f : PriceCurve}
    (m : MinimalRepresentation f) : CanonicalSidedCurve :=
  ⟨f, canonicalSidedKnotDataOfMinimal m⟩

end

end Thesis.DayAhead.SidedCertificate
