import Thesis.Appendices.DayAheadNumerical.NumericalRepresentation
import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedSide

/-! # Historical counterexamples to pointwise and risk inferences

These certify mathematical obstructions that were found in the 2026-10-20
audit snapshot of the thesis (L² node sampling, midpoint information loss,
positive depth versus positive matching, missing integrability). The current
thesis text has since been corrected on each point (selected pointwise
representatives, positive-matching restriction of the vendor-list domain,
Bochner-integrable hypothesis), so these witnesses document the historical
defects rather than claims about the current source.
-/

noncomputable section
namespace Thesis.DayAhead.CurrentCounterexamples

open MeasureTheory Set
open scoped ENNReal

def spike (x : ℝ) : ℝ := if x = 0 then 1 else 0

theorem measurable_spike : Measurable spike :=
  measurable_const.ite (measurableSet_singleton (0 : ℝ)) measurable_const

theorem spike_ae_zero : spike =ᵐ[volume] (fun _ : ℝ => 0) := by
  apply ae_iff.mpr
  apply measure_mono_null (show {x | ¬spike x = 0} ⊆ {0} by
    intro x hx
    by_contra hx0
    have hxne : x ≠ 0 := by simpa only [Set.mem_singleton_iff] using hx0
    exact hx (by simp [spike, hxne]))
  simp

/-- Historical: an earlier appendix draft sampled an L² class at grid nodes;
point-sampling does not descend to L² equivalence classes, even when both
representatives are measurable and square integrable. The current definition
samples a selected representative. -/
theorem node_sampling_not_ae_invariant :
    MemLp spike 2 (volume.restrict (Icc (-1 : ℝ) 1)) ∧
      MemLp (fun _ : ℝ => (0 : ℝ)) 2 (volume.restrict (Icc (-1 : ℝ) 1)) ∧
      spike =ᵐ[volume.restrict (Icc (-1 : ℝ) 1)] (fun _ : ℝ => 0) ∧
      spike 0 ≠ (0 : ℝ) := by
  have hae := ae_restrict_of_ae (s := Icc (-1 : ℝ) 1) spike_ae_zero
  refine ⟨(memLp_congr_ae hae).mpr MemLp.zero, MemLp.zero, hae, ?_⟩
  norm_num [spike]

/-- Historical: exact midpoint recovery contradicts an earlier draft's claim
that the midpoint crossing price is lost once both one-sided limits have been
recovered; the current text distinguishes the exact encoding from the grid
approximation. -/
theorem midpoint_determined_by_limits (left right left' right' : ℝ)
    (hl : left = left') (hr : right = right') :
    (left + right) / 2 = (left' + right') / 2 := by rw [hl, hr]

def populationRisk (prediction : ℝ) : ℝ :=
  (9 / 10 : ℝ) * (0 - prediction) ^ 2 + (1 / 10 : ℝ) * (1 - prediction) ^ 2

def oneObservationRisk (prediction : ℝ) : ℝ := (1 - prediction) ^ 2

/-- A predictor can have smaller test MSE and strictly larger population
MSE (hence larger mean-square distance to the conditional mean). -/
theorem empirical_and_population_rankings_can_reverse :
    oneObservationRisk 1 < oneObservationRisk 0 ∧ populationRisk 0 < populationRisk 1 := by
  norm_num [oneObservationRisk, populationRisk]

def sellPrices (i : Fin 3) : ℝ := if i.val = 0 then -500 else if i.val = 1 then 10 else 20
def sellQuantities (i : Fin 3) : ℝ := if i.val < 2 then 0 else 1
def buyPrices (i : Fin 4) : ℝ := if i.val < 2 then 3000 else if i.val = 2 then -10 else -20
def buyQuantities (i : Fin 4) : ℝ := if i.val < 3 then 0 else 1

theorem sellQuantities_monotone : Monotone sellQuantities := by
  intro i j hij
  by_cases hi : i.val < 2
  · simp only [sellQuantities, if_pos hi]
    split_ifs <;> norm_num
  · have hj : ¬j.val < 2 := by omega
    simp [sellQuantities, hi, hj]

theorem buyQuantities_monotone : Monotone buyQuantities := by
  intro i j hij
  by_cases hi : i.val < 3
  · simp only [buyQuantities, if_pos hi]
    split_ifs <;> norm_num
  · have hj : ¬j.val < 3 := by omega
    simp [buyQuantities, hi, hj]

/-- Historical: both sides have positive total quantity, but their interpolated
curves cannot match any positive quantity. This was the obstruction to the
input domain asserted by an earlier draft of `prop:pl-encoding-measurable`;
the current statement restricts the domain to positive matching, which this
example motivates. -/
theorem positive_depth_without_positive_matching (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    sellQuantities (Fin.last 2) = 1 ∧ buyQuantities (Fin.last 3) = 1 ∧
      ¬∃ price : ℝ,
        InterpolatedSide.curve sellPrices sellQuantities x ≤ price ∧
          price ≤ InterpolatedSide.curve buyPrices buyQuantities x := by
  have hs : InterpolatedSide.curve sellPrices sellQuantities x = 10 + 10 * x := by
    rw [InterpolatedSide.curve_on_cell sellPrices sellQuantities
      sellQuantities_monotone (by norm_num [sellQuantities]) (1 : Fin 2)
      (by simpa [InterpolatedSide.cell, sellQuantities] using And.intro hx hx1)]
    norm_num [sellPrices, sellQuantities, InterpolatedSide.interpolate]
    ring
  have hb : InterpolatedSide.curve buyPrices buyQuantities x = -10 - 10 * x := by
    rw [InterpolatedSide.curve_on_cell buyPrices buyQuantities
      buyQuantities_monotone (by norm_num [buyQuantities]) (2 : Fin 3)
      (by simpa [InterpolatedSide.cell, buyQuantities] using And.intro hx hx1)]
    norm_num [buyPrices, buyQuantities, InterpolatedSide.interpolate]
    ring
  refine ⟨by norm_num [sellQuantities], by norm_num [buyQuantities], ?_⟩
  rintro ⟨price, hp, hp'⟩
  rw [hs] at hp
  rw [hb] at hp'
  linarith

end Thesis.DayAhead.CurrentCounterexamples
