import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurves
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! # The literal Lebesgue parameter measure on [-1,1] -/
noncomputable section
namespace Thesis.DayAhead.PLParameterMeasure

open Set MeasureTheory PriceCurves

def lebesgue : Measure Parameter := Measure.comap (Subtype.val : Parameter → ℝ) volume

theorem lebesgue_apply (s : Set Parameter) :
    lebesgue s = volume ((Subtype.val : Parameter → ℝ) '' s) :=
  comap_subtype_coe_apply measurableSet_Icc volume s

theorem lebesgue_univ : lebesgue univ = 2 := by
  rw [lebesgue_apply]
  rw [image_univ, Subtype.range_coe]
  change volume (Icc (-1 : ℝ) 1) = 2
  norm_num [Real.volume_Icc]

instance : IsFiniteMeasure lebesgue := ⟨by rw [lebesgue_univ]; norm_num⟩

instance : NoAtoms lebesgue where
  measure_singleton x := by
    rw [lebesgue_apply, image_singleton]
    exact measure_singleton x.val

theorem lebesgue_real_univ : lebesgue.real univ = 2 := by
  rw [Measure.real, lebesgue_univ]
  norm_num

end Thesis.DayAhead.PLParameterMeasure
