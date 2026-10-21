import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedCertificate
import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialPriceCurve

/-! # Positive-length cells of the essential sided decomposition -/

noncomputable section

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation Set MeasureTheory

theorem mem_cell_iff_price_eq {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) (x : Icc f.leftEndpoint f.rightEndpoint) :
    x ∈ m.cell i ↔ f.price x = m.level i := by
  constructor
  · exact price_eq_level_of_mem m
  · intro hx
    obtain ⟨j, hj⟩ := exists_cell_mem m x
    have hji : j = i := m.level_strictMono.injective
      ((price_eq_level_of_mem m hj).symm.trans hx)
    simpa only [hji] using hj

theorem essential_cell_interval (f : PriceCurve)
    (hab : f.leftEndpoint < f.rightEndpoint) (m : MinimalRepresentation f.essential)
    (i : Fin m.blockCount) :
    ∃ u v : Icc f.leftEndpoint f.rightEndpoint, u < v ∧ Icc u v ⊆ m.cell i := by
  obtain ⟨x, hx⟩ := m.cell_nonempty i
  obtain ⟨u, v, huv, hconst⟩ := f.essentialPrice_fiber_interval hab x
  refine ⟨u, v, huv, fun y hy => ?_⟩
  apply (mem_cell_iff_price_eq m i y).mpr
  exact (hconst y hy.1 hy.2).trans (price_eq_level_of_mem m hx)

theorem essential_cell_positive_volume (f : PriceCurve)
    (hab : f.leftEndpoint < f.rightEndpoint) (m : MinimalRepresentation f.essential)
    (i : Fin m.blockCount) : 0 < volume (cellReal m i) := by
  obtain ⟨u, v, huv, hcell⟩ := essential_cell_interval f hab m i
  have hsub : Ioo (u : ℝ) v ⊆ cellReal m i := by
    intro y hy
    let yt : Icc f.leftEndpoint f.rightEndpoint :=
      ⟨y, u.property.1.trans hy.1.le, hy.2.le.trans v.property.2⟩
    exact ⟨yt, hcell ⟨hy.1.le, hy.2.le⟩, rfl⟩
  apply lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  exact sub_pos.mpr huv

theorem essential_left_cell_interval (f : PriceCurve) (m : MinimalRepresentation f.essential)
    (i : Fin m.blockCount) (hi : LeftActive m i) :
    ∃ u v : Icc f.leftEndpoint f.rightEndpoint,
      u < v ∧ (v : ℝ) < 0 ∧ Icc u v ⊆ m.cell i := by
  obtain ⟨x, hx, hxneg⟩ := hi
  have hxr : (x : ℝ) < f.rightEndpoint := hxneg.trans_le f.rightEndpoint_nonneg
  obtain ⟨z, hxz, hz⟩ := f.essentialPrice_right_constant x hxr
  have hx0 : x < f.domainZero := hxneg
  obtain ⟨v, hxv, hv⟩ := exists_between (lt_min hxz hx0)
  refine ⟨x, v, hxv, hv.trans_le (min_le_right _ _), ?_⟩
  intro y hy
  apply (mem_cell_iff_price_eq m i y).mpr
  exact (hz y hy.1 (hy.2.trans_lt (hv.trans_le (min_le_left _ _)))).trans
    (price_eq_level_of_mem m hx)

theorem essential_right_cell_interval (f : PriceCurve) (m : MinimalRepresentation f.essential)
    (i : Fin m.blockCount) (hi : RightActive m i) :
    ∃ u v : Icc f.leftEndpoint f.rightEndpoint,
      u < v ∧ 0 < (u : ℝ) ∧ Icc u v ⊆ m.cell i := by
  obtain ⟨x, hx, hxpos⟩ := hi
  by_cases hxr : (x : ℝ) < f.rightEndpoint
  · obtain ⟨z, hxz, hz⟩ := f.essentialPrice_right_constant x hxr
    obtain ⟨v, hxv, hvz⟩ := exists_between hxz
    refine ⟨x, v, hxv, hxpos, fun y hy => ?_⟩
    apply (mem_cell_iff_price_eq m i y).mpr
    exact (hz y hy.1 (hy.2.trans_lt hvz)).trans (price_eq_level_of_mem m hx)
  · have hxeq : x = f.domainRight :=
      Subtype.ext (le_antisymm x.property.2 (not_lt.mp hxr))
    subst x
    have hab : f.leftEndpoint < f.rightEndpoint := f.leftEndpoint_nonpos.trans_lt hxpos
    obtain ⟨z, hzr, hz⟩ := f.essentialPrice_left_constant hab
    have h0r : f.domainZero < f.domainRight := hxpos
    obtain ⟨u, hu, hur⟩ := exists_between (max_lt hzr h0r)
    refine ⟨u, f.domainRight, hur, (le_max_right _ _).trans_lt hu, fun y hy => ?_⟩
    apply (mem_cell_iff_price_eq m i y).mpr
    exact (hz y (((le_max_left _ _).trans_lt hu).trans_le hy.1) hy.2).trans
      (price_eq_level_of_mem m hx)

theorem essential_left_cell_positive_volume (f : PriceCurve)
    (m : MinimalRepresentation f.essential) (i : Fin m.blockCount) (hi : LeftActive m i) :
    0 < volume (cellReal m i ∩ Iio 0) := by
  obtain ⟨u, v, huv, hv, hcell⟩ := essential_left_cell_interval f m i hi
  have hsub : Ioo (u : ℝ) v ⊆ cellReal m i ∩ Iio 0 := by
    intro y hy
    let yt : Icc f.leftEndpoint f.rightEndpoint :=
      ⟨y, u.property.1.trans hy.1.le, hy.2.le.trans v.property.2⟩
    exact ⟨⟨yt, hcell ⟨hy.1.le, hy.2.le⟩, rfl⟩, hy.2.trans hv⟩
  apply lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  exact sub_pos.mpr huv

theorem essential_right_cell_positive_volume (f : PriceCurve)
    (m : MinimalRepresentation f.essential) (i : Fin m.blockCount) (hi : RightActive m i) :
    0 < volume (cellReal m i ∩ Ioi 0) := by
  obtain ⟨u, v, huv, hu, hcell⟩ := essential_right_cell_interval f m i hi
  have hsub : Ioo (u : ℝ) v ⊆ cellReal m i ∩ Ioi 0 := by
    intro y hy
    let yt : Icc f.leftEndpoint f.rightEndpoint :=
      ⟨y, u.property.1.trans hy.1.le, hy.2.le.trans v.property.2⟩
    exact ⟨⟨yt, hcell ⟨hy.1.le, hy.2.le⟩, rfl⟩, hu.trans hy.1⟩
  apply lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  exact sub_pos.mpr huv

theorem cellSup_le_of_later_cell {f : PriceCurve} (m : MinimalRepresentation f)
    {i j : Fin m.blockCount} (hij : i < j)
    {x : Icc f.leftEndpoint f.rightEndpoint} (hx : x ∈ m.cell j) :
    cellSup m i ≤ (x : ℝ) := by
  apply csSup_le (cellReal_nonempty m i)
  rintro _ ⟨y, hy, rfl⟩
  exact m.cell_ordered i j hij y hy x hx

/-- The essential construction has no flat interpolation block on the right. -/
theorem essential_canonicalRightKnot_strictMono (f : PriceCurve)
    (m : MinimalRepresentation f.essential) : StrictMono (canonicalRightKnot m) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
          rw [canonicalRightKnot_zero, canonicalRightKnot_succ]
          obtain ⟨u, v, huv, hu, hcell⟩ :=
            essential_right_cell_interval f m (rightCell m j) (rightCell_active m j)
          exact hu.trans_le ((le_cellSup_of_mem m (hcell ⟨le_rfl, huv.le⟩)).trans
            (le_max_right _ _))
  | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
          rw [canonicalRightKnot_succ, canonicalRightKnot_succ]
          obtain ⟨u, v, huv, hu, hcell⟩ :=
            essential_right_cell_interval f m (rightCell m j) (rightCell_active m j)
          have hij' : rightCell m i < rightCell m j := (rightCell m).strictMono
            (by simpa only [Fin.succ_lt_succ_iff] using hij)
          have hprev := cellSup_le_of_later_cell m hij' (hcell ⟨le_rfl, huv.le⟩)
          have huv' : (u : ℝ) < v := huv
          exact (max_le hu.le hprev).trans_lt
            (huv'.trans_le ((le_cellSup_of_mem m (hcell ⟨huv.le, le_rfl⟩)).trans
              (le_max_right _ _)))

/-- The corresponding no-flat-block statement on the left. -/
theorem essential_canonicalLeftKnot_strictMono (f : PriceCurve)
    (m : MinimalRepresentation f.essential) : StrictMono (canonicalLeftKnot m) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
          rw [canonicalLeftKnot_zero, canonicalLeftKnot_succ]
          obtain ⟨u, v, huv, hv, hcell⟩ :=
            essential_left_cell_interval f m (leftCell m j) (leftCell_active m j)
          exact (u.property.1.trans_lt huv).trans_le
            (le_min hv.le (le_cellSup_of_mem m (hcell ⟨huv.le, le_rfl⟩)))
  | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
          rw [canonicalLeftKnot_succ, canonicalLeftKnot_succ]
          obtain ⟨u, v, huv, hv, hcell⟩ :=
            essential_left_cell_interval f m (leftCell m j) (leftCell_active m j)
          have hij' : leftCell m i < leftCell m j := (leftCell m).strictMono
            (by simpa only [Fin.succ_lt_succ_iff] using hij)
          have hprev := cellSup_le_of_later_cell m hij' (hcell ⟨le_rfl, huv.le⟩)
          have huv' : (u : ℝ) < v := huv
          exact ((min_le_right _ _).trans hprev).trans_lt
            (huv'.trans_le (le_min hv.le (le_cellSup_of_mem m (hcell ⟨huv.le, le_rfl⟩))))

end Thesis.DayAhead.SidedCertificate
