import Thesis.DayAhead.ForecastingImpact.EmpiricalGeometry

/-! # Actual observation sets in daily averages

A supplied finite observation set supplies the denominator. The current
source drops the repeated 3B labels and pairs daily differences by UTC minus
24 hours. These generic common-index identities support finite averages;
they do not implement that timestamp pairing or reproduce a data pipeline.
-/

noncomputable section
namespace Thesis.DayAhead.EmpiricalCalendar

open scoped BigOperators
open EmpiricalGeometry

variable {ι H : Type*} [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Supporting finite-observation averaging for current Chapter 4, line 18. -/
def dailyMean (hours : Finset ι) (Z : ι → H) : H := cellMean hours Z

/-- Supporting finite-observation averaging for current Chapter 4, line 18.
A generic identity for differences indexed by the same supplied labels.
Current UTC matching must be supplied by the caller. -/
def dailyDifference (today yesterday : Finset ι) (Z W : ι → H) : H :=
  dailyMean (today ∩ yesterday) (fun h => Z h - W h)

theorem common_hour_iff (today yesterday : Finset ι) (h : ι) :
    h ∈ today ∩ yesterday ↔ h ∈ today ∧ h ∈ yesterday := Finset.mem_inter

omit [DecidableEq ι] in
theorem dailyMean_denominator (hours : Finset ι) (Z : ι → H)
    (n : ℕ) (hn : hours.card = n) : dailyMean hours Z = (n : ℝ)⁻¹ • ∑ h ∈ hours, Z h := by
  simp only [dailyMean, cellMean, hn]

omit [DecidableEq ι] in
/-- A generic cardinality identity, not a claim that current retained
observation sets have 25 hours after dropping the repeated 3B label. -/
theorem dailyMean_transition_days (hours : Finset ι) (Z : ι → H) :
    (hours.card = 23 → dailyMean hours Z = (23 : ℝ)⁻¹ • ∑ h ∈ hours, Z h) ∧
    (hours.card = 25 → dailyMean hours Z = (25 : ℝ)⁻¹ • ∑ h ∈ hours, Z h) :=
  ⟨dailyMean_denominator hours Z 23, dailyMean_denominator hours Z 25⟩

theorem dailyDifference_eq (today yesterday : Finset ι) (Z W : ι → H) :
    dailyDifference today yesterday Z W =
      dailyMean (today ∩ yesterday) Z - dailyMean (today ∩ yesterday) W := by
  simp only [dailyDifference, dailyMean, cellMean, Finset.sum_sub_distrib, smul_sub]

end Thesis.DayAhead.EmpiricalCalendar
