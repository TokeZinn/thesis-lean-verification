import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveCuts
import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialSidedCertificate
import Thesis.Foundations.Stochastic.MeasurableDistinctCounts

/-! # Rational-evaluation formulas for the actual sided block counts -/

noncomputable section
namespace Thesis.DayAhead.PriceCurves

open Set SidedCertificate

def PriceCurve.rationalLeftLevels (f : PriceCurve) : Set ℝ :=
  (fun r : ℚ => f.essential.price (f.clampQuantity r)) ''
    {r | (f.clampQuantity r : ℝ) < 0}

def PriceCurve.rationalRightLevels (f : PriceCurve) : Set ℝ :=
  (fun r : ℚ => f.essential.price (f.clampQuantity r)) ''
    {r | 0 < (f.clampQuantity r : ℝ)}

theorem PriceCurve.rationalLeftLevels_eq (f : PriceCurve)
    (R : MinimalRepresentation f.essential) :
    f.rationalLeftLevels = R.level '' (leftActiveCells R : Set (Fin R.blockCount)) := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨i, hi⟩ := exists_cell_mem R (f.clampQuantity r)
    exact ⟨i, (mem_leftActiveCells R i).mpr ⟨_, hi, hr⟩,
      (price_eq_level_of_mem R hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨u, v, huv, hv, hcell⟩ :=
      essential_left_cell_interval f R i ((mem_leftActiveCells R i).mp hi)
    obtain ⟨r, hur, hrv⟩ := exists_rat_btwn (show (u : ℝ) < v from huv)
    have hc : (f.clampQuantity r : ℝ) = r :=
      f.clampQuantity_coe_of_mem ⟨u.property.1.trans hur.le, hrv.le.trans v.property.2⟩
    refine ⟨r, ?_, ?_⟩
    · change (f.clampQuantity r : ℝ) < 0
      rw [hc]
      exact hrv.trans hv
    · apply price_eq_level_of_mem R
      apply hcell
      change (u : ℝ) ≤ f.clampQuantity r ∧ (f.clampQuantity r : ℝ) ≤ v
      rw [hc]
      exact ⟨hur.le, hrv.le⟩

theorem PriceCurve.rationalRightLevels_eq (f : PriceCurve)
    (R : MinimalRepresentation f.essential) :
    f.rationalRightLevels = R.level '' (rightActiveCells R : Set (Fin R.blockCount)) := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨i, hi⟩ := exists_cell_mem R (f.clampQuantity r)
    exact ⟨i, (mem_rightActiveCells R i).mpr ⟨_, hi, hr⟩,
      (price_eq_level_of_mem R hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨u, v, huv, hu, hcell⟩ :=
      essential_right_cell_interval f R i ((mem_rightActiveCells R i).mp hi)
    obtain ⟨r, hur, hrv⟩ := exists_rat_btwn (show (u : ℝ) < v from huv)
    have hc : (f.clampQuantity r : ℝ) = r :=
      f.clampQuantity_coe_of_mem ⟨u.property.1.trans hur.le, hrv.le.trans v.property.2⟩
    refine ⟨r, ?_, ?_⟩
    · change 0 < (f.clampQuantity r : ℝ)
      rw [hc]
      exact hu.trans hur
    · apply price_eq_level_of_mem R
      apply hcell
      change (u : ℝ) ≤ f.clampQuantity r ∧ (f.clampQuantity r : ℝ) ≤ v
      rw [hc]
      exact ⟨hur.le, hrv.le⟩

theorem PriceCurve.rationalLeftLevels_ncard (f : PriceCurve)
    (R : MinimalRepresentation f.essential) : f.rationalLeftLevels.ncard = leftCount R := by
  rw [f.rationalLeftLevels_eq R, R.level_strictMono.injective.injOn.ncard_image,
    ncard_coe_finset]
  rfl

theorem PriceCurve.rationalRightLevels_ncard (f : PriceCurve)
    (R : MinimalRepresentation f.essential) : f.rationalRightLevels.ncard = rightCount R := by
  rw [f.rationalRightLevels_eq R, R.level_strictMono.injective.injOn.ncard_image,
    ncard_coe_finset]
  rfl

theorem PriceCurve.rationalLeftLevels_range (f : PriceCurve)
    (R : MinimalRepresentation f.essential) :
    range (fun j => R.level (leftCell R j)) = f.rationalLeftLevels := by
  rw [f.rationalLeftLevels_eq R]
  change range (R.level ∘ (leftActiveCells R).orderEmbOfFin rfl) = _
  rw [range_comp, Finset.range_orderEmbOfFin]

theorem PriceCurve.rationalRightLevels_range (f : PriceCurve)
    (R : MinimalRepresentation f.essential) :
    range (fun j => R.level (rightCell R j)) = f.rationalRightLevels := by
  rw [f.rationalRightLevels_eq R]
  change range (R.level ∘ (rightActiveCells R).orderEmbOfFin rfl) = _
  rw [range_comp, Finset.range_orderEmbOfFin]

end Thesis.DayAhead.PriceCurves
