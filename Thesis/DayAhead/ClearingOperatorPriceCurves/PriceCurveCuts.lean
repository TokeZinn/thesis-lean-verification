import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedCertificate

/-! # Recovering actual block boundaries from rational price evaluations

Monotonicity makes a block's right boundary the supremum of the sublevel set
at its price. Rational, clamped evaluations recover this boundary exactly,
including isolated boundary cells. The countable formula can therefore be
used to prove measurability without assuming a measurable choice of cells.
-/

noncomputable section
namespace Thesis.DayAhead.PriceCurves

open Set SidedCertificate

def PriceCurve.clampQuantity (f : PriceCurve) (q : ℝ) :
    Icc f.leftEndpoint f.rightEndpoint :=
  ⟨max f.leftEndpoint (min f.rightEndpoint q), le_max_left _ _,
    max_le (f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg) (min_le_left _ _)⟩

theorem PriceCurve.clampQuantity_coe_of_mem (f : PriceCurve) {q : ℝ}
    (hq : q ∈ Icc f.leftEndpoint f.rightEndpoint) :
    (f.clampQuantity q : ℝ) = q := by
  simp only [PriceCurve.clampQuantity, min_eq_right hq.2, max_eq_right hq.1]

def PriceCurve.rationalCutTerm (f : PriceCurve) (p : ℝ) (r : ℚ) : ℝ :=
  if f.price (f.clampQuantity r) ≤ p then f.clampQuantity r else f.leftEndpoint

def PriceCurve.rationalSublevelCut (f : PriceCurve) (p : ℝ) : ℝ :=
  ⨆ r : ℚ, f.rationalCutTerm p r

theorem PriceCurve.rationalCutTerm_bounds (f : PriceCurve) (p : ℝ) (r : ℚ) :
    f.rationalCutTerm p r ∈ Icc f.leftEndpoint f.rightEndpoint := by
  unfold PriceCurve.rationalCutTerm
  split_ifs
  · exact (f.clampQuantity r).property
  · exact ⟨le_rfl, f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg⟩

theorem PriceCurve.rationalCutTerm_bddAbove (f : PriceCurve) (p : ℝ) :
    BddAbove (range (f.rationalCutTerm p)) := by
  refine ⟨f.rightEndpoint, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact (f.rationalCutTerm_bounds p r).2

theorem PriceCurve.rationalSublevelCut_bounds (f : PriceCurve) (p : ℝ) :
    f.rationalSublevelCut p ∈ Icc f.leftEndpoint f.rightEndpoint := by
  constructor
  · exact (f.rationalCutTerm_bounds p 0).1.trans
      (le_ciSup (f.rationalCutTerm_bddAbove p) 0)
  · exact ciSup_le fun r => (f.rationalCutTerm_bounds p r).2

theorem PriceCurve.quantity_le_cellSup_of_price_le {f : PriceCurve}
    (m : MinimalRepresentation f) (i : Fin m.blockCount)
    (q : Icc f.leftEndpoint f.rightEndpoint) (hq : f.price q ≤ m.level i) :
    (q : ℝ) ≤ cellSup m i := by
  have hcover : q ∈ ⋃ j, m.cell j := by rw [m.cell_cover]; trivial
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcover
  rw [price_eq_level_of_mem m hj] at hq
  exact (le_cellSup_of_mem m hj).trans
    (cellSup_mono m (m.level_strictMono.le_iff_le.mp hq))

theorem PriceCurve.rationalSublevelCut_eq_cellSup {f : PriceCurve}
    (m : MinimalRepresentation f) (i : Fin m.blockCount) :
    f.rationalSublevelCut (m.level i) = cellSup m i := by
  apply le_antisymm
  · apply ciSup_le
    intro r
    unfold PriceCurve.rationalCutTerm
    split_ifs with h
    · exact f.quantity_le_cellSup_of_price_le m i _ h
    · exact leftEndpoint_le_cellSup m i
  · apply csSup_le (cellReal_nonempty m i)
    rintro _ ⟨q, hq, rfl⟩
    by_contra h
    have hlt : f.rationalSublevelCut (m.level i) < (q : ℝ) := lt_of_not_ge h
    obtain ⟨r, hr, hrq⟩ := exists_rat_btwn hlt
    have hclamp : (f.clampQuantity r : ℝ) = r :=
      f.clampQuantity_coe_of_mem
        ⟨(f.rationalSublevelCut_bounds _).1.trans hr.le, hrq.le.trans q.property.2⟩
    have hprice : f.price (f.clampQuantity r) ≤ m.level i := by
      rw [← price_eq_level_of_mem m hq]
      apply f.price_monotone
      change (f.clampQuantity r : ℝ) ≤ q
      rw [hclamp]
      exact hrq.le
    have hle := le_ciSup (f.rationalCutTerm_bddAbove (m.level i)) r
    simp only [PriceCurve.rationalCutTerm, if_pos hprice, hclamp] at hle
    exact (not_le_of_gt hr) hle

end Thesis.DayAhead.PriceCurves
