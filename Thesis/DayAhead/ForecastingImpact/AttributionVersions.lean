import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic

/-! # Conditional versions and pointwise attribution endpoints

The current forecasting chapter selects arbitrary conditional versions, then
uses pointwise full-information efficiency. Almost-sure equality does not
justify that last pointwise substitution. This example has one predictor and
a zero prediction; the exceptional predictor value occurs on a null outcome.
-/

noncomputable section
namespace Thesis.DayAhead.AttributionVersions

open MeasureTheory

local instance : MeasurableSpace Bool := ⊤

def law : Measure Bool := Measure.dirac false

instance : IsProbabilityMeasure law := by unfold law; infer_instance

def predictor (ω : Bool) : ℝ := if ω then 1 else 0
def prediction (_ : ℝ) : ℝ := 0
def chosenFullVersion (x : ℝ) : ℝ := if x = 1 then 1 else 0

theorem measurable_chosenFullVersion : Measurable chosenFullVersion :=
  measurable_const.ite (measurableSet_singleton (1 : ℝ)) measurable_const

theorem chosenFullVersion_ae :
    (fun ω => chosenFullVersion (predictor ω)) =ᵐ[law]
      (fun ω => prediction (predictor ω)) := by
  simp [law, Filter.EventuallyEq, predictor, prediction, chosenFullVersion]

/-- The selected function is a version of the full-predictor conditional mean. -/
theorem chosenFullVersion_condExp :
    (fun ω => chosenFullVersion (predictor ω)) =ᵐ[law]
      law[(fun ω => prediction (predictor ω)) | MeasurableSpace.comap predictor (borel ℝ)] := by
  change (fun ω => chosenFullVersion (predictor ω)) =ᵐ[law]
    law[(0 : Bool → ℝ) | MeasurableSpace.comap predictor (borel ℝ)]
  rw [condExp_zero]
  exact chosenFullVersion_ae

theorem chosenFullVersion_measurable :
    @Measurable Bool ℝ (MeasurableSpace.comap predictor (borel ℝ)) (borel ℝ)
      (fun ω => chosenFullVersion (predictor ω)) :=
  measurable_chosenFullVersion.comp (measurable_iff_comap_le.mpr le_rfl)

/-- Original equation: pointwise efficiency, forecasting chapter lines 417–422.
At the null outcome the single-feature contribution is one although the actual
prediction minus its zero baseline is zero. -/
theorem fullVersion_pointwise_obstruction :
    chosenFullVersion (predictor true) - 0 ≠ prediction (predictor true) - 0 := by
  norm_num [chosenFullVersion, predictor, prediction]

end Thesis.DayAhead.AttributionVersions
