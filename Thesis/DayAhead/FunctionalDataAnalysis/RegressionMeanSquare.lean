import Thesis.DayAhead.FunctionalDataAnalysis.FunctionalData

/-! # Regression in the manuscript's expected squared-error form

The valid regression clause concerns one fixed conditioning sigma-algebra.
The separate counterexample module records the historical false comparison
with conditioning on an unrelated predictor, corrected in UV001.
-/

namespace Thesis.DayAhead.RegressionMeanSquare

open MeasureTheory FunctionalData
open scoped ENNReal

universe u v

variable {Ω : Type u} {H : Type v} {m m₀ : MeasurableSpace Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure[m₀] Ω}

omit [CompleteSpace H] in
theorem norm_sq_eq_integral (f : Ω →₂[μ] H) :
    ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

omit [CompleteSpace H] in
theorem meanSquareError_eq_norm_sq (f g : Ω →₂[μ] H) :
    (∫ ω, ‖f ω - g ω‖ ^ 2 ∂μ) = ‖f - g‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with ω hω
  rw [hω]
  rfl

/-- Original label: `thm:regression-theorem`.
Expected squared error, rather than merely distance in the abstract L² space,
is minimized by the conditional-expectation projection. -/
theorem condExpL2_meanSquareError_le
    (hm : m ≤ m₀) (f : Ω →₂[μ] H) (g : lpMeas H ℝ m 2 μ) :
    (∫ ω, ‖f ω - (condExpL2 H ℝ hm f : Ω →₂[μ] H) ω‖ ^ 2 ∂μ) ≤
      ∫ ω, ‖f ω - (g : Ω →₂[μ] H) ω‖ ^ 2 ∂μ := by
  rw [meanSquareError_eq_norm_sq, meanSquareError_eq_norm_sq]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [condExpL2_minimizes hm f]
  exact ciInf_le ⟨0, fun _ hy ↦ by obtain ⟨g, rfl⟩ := hy; exact norm_nonneg _⟩ g

/-- Original label: `thm:regression-theorem`.
For actual random variables, the chosen conditional-expectation version
minimizes the integral of squared error against every square-integrable
predictor measurable with respect to the same information set. -/
theorem conditionalExpectation_minimizes_meanSquareError
    [IsFiniteMeasure μ] (hm : m ≤ m₀) (X Z : Ω → H)
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ)
    (hZm : AEStronglyMeasurable[m] Z μ) :
    (∫ ω, ‖X ω - μ[X | m] ω‖ ^ 2 ∂μ) ≤
      ∫ ω, ‖X ω - Z ω‖ ^ 2 ∂μ := by
  let f : Ω →₂[μ] H := hX.toLp X
  let g : lpMeas H ℝ m 2 μ := ⟨hZ.toLp Z, by
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    exact hZm.congr hZ.coeFn_toLp.symm⟩
  have hp := hX.condExpL2_ae_eq_condExp (𝕜 := ℝ) hm
  have hleft : (∫ ω, ‖X ω - μ[X | m] ω‖ ^ 2 ∂μ) =
      ∫ ω, ‖f ω - (condExpL2 H ℝ hm f : Ω →₂[μ] H) ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp, hp] with ω hx hpω
    dsimp only [f]
    rw [hx, hpω]
  have hright : (∫ ω, ‖X ω - Z ω‖ ^ 2 ∂μ) =
      ∫ ω, ‖f ω - (g : Ω →₂[μ] H) ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp, hZ.coeFn_toLp] with ω hx hz
    dsimp only [f, g]
    rw [hx, hz]
  rw [hleft, hright]
  exact condExpL2_meanSquareError_le hm f g

end Thesis.DayAhead.RegressionMeanSquare
