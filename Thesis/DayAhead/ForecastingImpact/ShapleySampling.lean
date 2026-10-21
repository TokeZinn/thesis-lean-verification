import Thesis.DayAhead.ForecastingImpact.ShapleyWeights
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.HasLaw
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Sampling the finite Shapley game

Forecasting chapter, lines 500–540. Exact coalition evaluations under independent
uniform permutations have the factorial Shapley value as their expectation and
converge to it almost surely. Conditional simulation of a coalition is a separate
Monte Carlo average: its law, first moment, and sampling independence must hold
for the selected conditional version at the conditioning point.
-/

noncomputable section
namespace Thesis.DayAhead.ShapleyPermutations

open Finset Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {n : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
  [MeasurableSingletonClass (Equiv.Perm (Fin n))]

def uniformMeasure (n : ℕ) [MeasurableSpace (Equiv.Perm (Fin n))] :
    Measure (Equiv.Perm (Fin n)) := (PMF.uniformOfFintype _).toMeasure

instance uniformMeasure_probability : IsProbabilityMeasure (uniformMeasure n) := by
  unfold uniformMeasure
  infer_instance

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem integral_uniform_contribution (V : Finset (Fin n) → H) (i : Fin n) :
    ∫ π, contribution V π i ∂uniformMeasure n = Shapley.value V i := by
  rw [integral_fintype (Integrable.of_finite)]
  have hmass (π : Equiv.Perm (Fin n)) :
      (uniformMeasure n).real {π} = (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ := by
    simp [uniformMeasure, measureReal_def, PMF.uniformOfFintype_apply]
  simp_rw [hmass]
  rw [← smul_sum, uniform_average_eq_value]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [MeasurableSpace H] [BorelSpace H]

omit [MeasurableSpace H] [BorelSpace H] in
theorem contribution_unbiased (V : Finset (Fin n) → H) (i : Fin n)
    {π : Ω → Equiv.Perm (Fin n)} (hπ : HasLaw π (uniformMeasure n) μ) :
    ∫ ω, contribution V (π ω) i ∂μ = Shapley.value V i := by
  change ∫ ω, ((fun σ => contribution V σ i) ∘ π) ω ∂μ = _
  rw [hπ.integral_comp (StronglyMeasurable.of_discrete.aestronglyMeasurable),
    integral_uniform_contribution]

/-- No moment hypothesis on a fixed finite game is needed: its contribution range is finite. -/
theorem sampleValue_tendsto_ae (V : Finset (Fin n) → H) (i : Fin n)
    (π : ℕ → Ω → Equiv.Perm (Fin n))
    (hlaw : ∀ b, HasLaw (π b) (uniformMeasure n) μ)
    (hindep : Pairwise fun b c => π b ⟂ᵢ[μ] π c) :
    ∀ᵐ ω ∂μ, Tendsto (fun B => sampleValue B V (fun b => π b.val ω) i)
      atTop (𝓝 (Shapley.value V i)) := by
  let g : Equiv.Perm (Fin n) → H := fun σ => contribution V σ i
  have hg : Measurable g := measurable_of_countable g
  have hd (b : ℕ) : IdentDistrib (π b) id μ (uniformMeasure n) :=
    ⟨(hlaw b).aemeasurable, measurable_id.aemeasurable, by
      rw [Measure.map_id, (hlaw b).map_eq]⟩
  have hgint : Integrable g (uniformMeasure n) := Integrable.of_finite
  have hint : Integrable (g ∘ π 0) μ := ((hd 0).comp hg).integrable_iff.mpr (by
    simpa only [Function.comp_id] using hgint)
  have hident (b : ℕ) : IdentDistrib (g ∘ π b) (g ∘ π 0) μ μ :=
    ((hd b).trans (hd 0).symm).comp hg
  have hind : Pairwise fun b c => (g ∘ π b) ⟂ᵢ[μ] (g ∘ π c) :=
    fun b c hbc => (hindep hbc).comp hg hg
  have h := strong_law_ae (fun b => g ∘ π b) hint hind hident
  have hmean : ∫ ω, g (π 0 ω) ∂μ = Shapley.value V i := contribution_unbiased V i (hlaw 0)
  have hsample (B : ℕ) (ω : Ω) : sampleValue B V (fun b => π b.val ω) i =
      (B : ℝ)⁻¹ • ∑ b ∈ range B, contribution V (π b ω) i := by
    unfold sampleValue
    rw [Fin.sum_univ_eq_sum_range (fun b => contribution V (π b ω) i) B]
  simpa only [hsample, Function.comp_def, hmean, g] using h

end Thesis.DayAhead.ShapleyPermutations
