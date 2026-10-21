import Thesis.DayAhead.FunctionalDataAnalysis.RegressionMeanSquare
import Mathlib.Probability.Martingale.Basic

/-! # Discrete Fréchet martingales

The metric definition uses actual measurable, square-integrable random elements.
The Hilbert theorem works on L² equivalence classes and identifies the unique
one-step minimizer with the conditional-expectation projection. No nonlinear
tower property or existence of metric-valued minimizers is assumed.
-/

namespace Thesis.Foundations.Research

open MeasureTheory
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E]
  [BorelSpace E]

/-- Original label: `defn:frechet-martingale`.
The admissible competitors at one time have a finite second distance moment.
Measurability is with respect to the declared information sigma-algebra. -/
def MetricL2Predictor (μ : Measure Ω) (m : MeasurableSpace Ω) (z₀ : E) (Y : Ω → E) : Prop :=
  Measurable[m] Y ∧ Integrable (fun ω ↦ dist (Y ω) z₀ ^ 2) μ

/-- Original label: `defn:frechet-martingale`.
Adjacent-time Fréchet minimization, with all admissibility conditions explicit.
Completeness/separability are source hypotheses on applications, not a claimed
existence theorem for this definition. -/
def IsFrechetMartingale (μ : Measure Ω) (ℱ : ℕ → MeasurableSpace Ω)
    (z₀ : E) (Z : ℕ → Ω → E) : Prop :=
  (∀ n, MetricL2Predictor μ (ℱ n) z₀ (Z n)) ∧
    ∀ n Y, MetricL2Predictor μ (ℱ n) z₀ Y →
      (∫ ω, dist (Z (n + 1) ω) (Z n ω) ^ 2 ∂μ) ≤
        ∫ ω, dist (Z (n + 1) ω) (Y ω) ^ 2 ∂μ

section Hilbert

omit [MeasurableSpace Ω]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}

/-- The squared-norm minimum characterizes the projection uniquely. This is
the Hilbert-space reduction following `defn:frechet-martingale`. -/
theorem hilbert_minimizer_iff_condExpL2 (hm : m ≤ m₀)
    (f : Ω →₂[μ] H) (g : lpMeas H ℝ m 2 μ) :
    (∀ y : lpMeas H ℝ m 2 μ,
      ‖f - (g : Ω →₂[μ] H)‖ ^ 2 ≤ ‖f - (y : Ω →₂[μ] H)‖ ^ 2) ↔
      g = condExpL2 H ℝ hm f := by
  letI : Fact (m ≤ m₀) := ⟨hm⟩
  constructor
  · intro h
    have hnorm : ‖f - (g : Ω →₂[μ] H)‖ =
        ⨅ y : lpMeas H ℝ m 2 μ, ‖f - (y : Ω →₂[μ] H)‖ := by
      apply le_antisymm
      · apply le_ciInf
        intro y
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h y)
      · exact ciInf_le ⟨0, fun _ hy ↦ by obtain ⟨y, rfl⟩ := hy; exact norm_nonneg _⟩ g
    have horth := (lpMeas H ℝ m 2 μ).norm_eq_iInf_iff_inner_eq_zero g.property |>.mp hnorm
    apply Subtype.ext
    exact ((lpMeas H ℝ m 2 μ).eq_starProjection_of_mem_of_inner_eq_zero
      g.property horth).symm
  · rintro rfl y
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      rw [DayAhead.FunctionalData.condExpL2_minimizes hm f]
      exact ciInf_le ⟨0, fun _ hy ↦ by obtain ⟨y, rfl⟩ := hy; exact norm_nonneg _⟩ y) 2

/-- Original label: `thm:regression-theorem`.
Uniqueness clause: in expected squared-error form the unique minimizer is the
same L² class, namely the conditional expectation. -/
theorem hilbert_meanSquare_minimizer_iff (hm : m ≤ m₀)
    (f : Ω →₂[μ] H) (g : lpMeas H ℝ m 2 μ) :
    (∀ y : lpMeas H ℝ m 2 μ,
      (∫ ω, ‖f ω - (g : Ω →₂[μ] H) ω‖ ^ 2 ∂μ) ≤
        ∫ ω, ‖f ω - (y : Ω →₂[μ] H) ω‖ ^ 2 ∂μ) ↔
      g = condExpL2 H ℝ hm f := by
  simp_rw [DayAhead.RegressionMeanSquare.meanSquareError_eq_norm_sq]
  exact hilbert_minimizer_iff_condExpL2 hm f g

end Hilbert

end Thesis.Foundations.Research
