import Thesis.DayAhead.ForecastingImpact.ShapleySampling

/-! # Conditional simulation at a selected predictor value

Forecasting chapter, lines 520–540. The missing coordinates are sampled from a
selected conditional law at the declared predictor value. The following proofs
require its first moment at that point; unconditional integrability alone gives
such a condition only almost everywhere. The retained coordinates are copied
from the declared predictor value, exactly as in the source's bracket notation.
-/

noncomputable section
namespace Thesis.DayAhead.ConditionalSimulation

open Finset Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

variable {n : ℕ}

def completeInput (x : Fin n → ℝ) (A : Finset (Fin n)) (z : Fin n → ℝ) (j : Fin n) : ℝ :=
  if j ∈ A then x j else z j

theorem completeInput_retained (x z : Fin n → ℝ) (A : Finset (Fin n))
    {j : Fin n} (hj : j ∈ A) : completeInput x A z j = x j := if_pos hj

theorem completeInput_missing (x z : Fin n → ℝ) (A : Finset (Fin n))
    {j : Fin n} (hj : j ∉ A) : completeInput x A z j = z j := if_neg hj

theorem completeInput_empty (x z : Fin n → ℝ) : completeInput x ∅ z = z := by
  funext j; simp [completeInput]

theorem completeInput_full (x z : Fin n → ℝ) : completeInput x univ z = x := by
  funext j; simp [completeInput]

theorem measurable_completeInput (x : Fin n → ℝ) (A : Finset (Fin n)) :
    Measurable (completeInput x A) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j ∈ A
  · simpa only [completeInput, if_pos hj] using
      (measurable_const : Measurable (fun _ : Fin n → ℝ => x j))
  · simpa only [completeInput, if_neg hj] using measurable_pi_apply j

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- `ν` is the law of the sampled missing coordinates, with unused coordinates ignored. -/
def coalitionValue (f : (Fin n → ℝ) → H) (x : Fin n → ℝ) (A : Finset (Fin n))
    (ν : Measure (Fin n → ℝ)) : H := ∫ z, f (completeInput x A z) ∂ν

def sampleCoalition (M : ℕ) (f : (Fin n → ℝ) → H) (x : Fin n → ℝ)
    (A : Finset (Fin n)) (z : Fin M → (Fin n → ℝ)) : H :=
  (M : ℝ)⁻¹ • ∑ m, f (completeInput x A (z m))

theorem coalitionValue_empty (f : (Fin n → ℝ) → H) (x : Fin n → ℝ)
    (ν : Measure (Fin n → ℝ)) : coalitionValue f x ∅ ν = ∫ z, f z ∂ν := by
  simp only [coalitionValue, completeInput_empty]

theorem coalitionValue_full [CompleteSpace H] (f : (Fin n → ℝ) → H) (x : Fin n → ℝ)
    (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν] :
    coalitionValue f x univ ν = f x := by
  simp [coalitionValue, completeInput_full]

theorem sampleCoalition_full {M : ℕ} (hM : 0 < M) (f : (Fin n → ℝ) → H)
    (x : Fin n → ℝ) (z : Fin M → (Fin n → ℝ)) : sampleCoalition M f x univ z = f x := by
  simp only [sampleCoalition, completeInput_full, sum_const, card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by positivity : (M : ℝ) ≠ 0), one_smul]

variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [CompleteSpace H] in
theorem sampleCoalition_unbiased {M : ℕ} (hM : 0 < M) (f : (Fin n → ℝ) → H)
    (x : Fin n → ℝ) (A : Finset (Fin n)) (ν : Measure (Fin n → ℝ))
    (hf : Measurable f) (hint : Integrable (fun z => f (completeInput x A z)) ν)
    (z : Fin M → Ω → (Fin n → ℝ)) (hlaw : ∀ m, HasLaw (z m) ν μ) :
    ∫ ω, sampleCoalition M f x A (fun m => z m ω) ∂μ = coalitionValue f x A ν := by
  let g : (Fin n → ℝ) → H := fun u => f (completeInput x A u)
  have hg : Measurable g := hf.comp (measurable_completeInput x A)
  have hd (m : Fin M) : IdentDistrib (z m) id μ ν :=
    ⟨(hlaw m).aemeasurable, measurable_id.aemeasurable, by
      rw [Measure.map_id, (hlaw m).map_eq]⟩
  have hzint (m : Fin M) : Integrable (g ∘ z m) μ :=
    ((hd m).comp hg).integrable_iff.mpr (by simpa only [Function.comp_id] using hint)
  change ∫ ω, (M : ℝ)⁻¹ • ∑ m, (g ∘ z m) ω ∂μ = _
  rw [integral_smul, integral_finset_sum _ (fun m _ => hzint m)]
  have hmean (m : Fin M) : ∫ ω, (g ∘ z m) ω ∂μ = coalitionValue f x A ν :=
    (hlaw m).integral_comp hint.aestronglyMeasurable
  simp only [hmean, sum_const, card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by positivity : (M : ℝ) ≠ 0), one_smul]

/-- An actual first-moment condition on the selected conditional law is explicit. -/
theorem sampleCoalition_tendsto_ae (f : (Fin n → ℝ) → H) (x : Fin n → ℝ)
    (A : Finset (Fin n)) (ν : Measure (Fin n → ℝ))
    (hf : Measurable f) (hint : Integrable (fun z => f (completeInput x A z)) ν)
    (z : ℕ → Ω → (Fin n → ℝ)) (hlaw : ∀ m, HasLaw (z m) ν μ)
    (hindep : Pairwise fun b c => z b ⟂ᵢ[μ] z c) :
    ∀ᵐ ω ∂μ, Tendsto (fun M => sampleCoalition M f x A (fun m => z m.val ω))
      atTop (𝓝 (coalitionValue f x A ν)) := by
  let g : (Fin n → ℝ) → H := fun u => f (completeInput x A u)
  have hg : Measurable g := hf.comp (measurable_completeInput x A)
  have hd (m : ℕ) : IdentDistrib (z m) id μ ν :=
    ⟨(hlaw m).aemeasurable, measurable_id.aemeasurable, by
      rw [Measure.map_id, (hlaw m).map_eq]⟩
  have h0int : Integrable (g ∘ z 0) μ :=
    ((hd 0).comp hg).integrable_iff.mpr (by simpa only [Function.comp_id] using hint)
  have hident (m : ℕ) : IdentDistrib (g ∘ z m) (g ∘ z 0) μ μ :=
    ((hd m).trans (hd 0).symm).comp hg
  have hind : Pairwise fun b c => (g ∘ z b) ⟂ᵢ[μ] (g ∘ z c) :=
    fun b c hbc => (hindep hbc).comp hg hg
  have h := strong_law_ae (fun m => g ∘ z m) h0int hind hident
  have hmean : ∫ ω, g (z 0 ω) ∂μ = coalitionValue f x A ν :=
    (hlaw 0).integral_comp hint.aestronglyMeasurable
  have hsample (M : ℕ) (ω : Ω) : sampleCoalition M f x A (fun m => z m.val ω) =
      (M : ℝ)⁻¹ • ∑ m ∈ range M, g (z m ω) := by
    unfold sampleCoalition
    rw [Fin.sum_univ_eq_sum_range (fun m => f (completeInput x A (z m ω))) M]
  simpa only [hsample, Function.comp_def, hmean] using h

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Subtracting the two sample averages is exactly the displayed average of paired differences.
The pairing is algebraic and does not assume independence between the two coalitions. -/
theorem sampleCoalition_sub (M : ℕ) (f : (Fin n → ℝ) → H) (x : Fin n → ℝ)
    (A B : Finset (Fin n)) (z w : Fin M → (Fin n → ℝ)) :
    sampleCoalition M f x A z - sampleCoalition M f x B w =
      (M : ℝ)⁻¹ • ∑ m, (f (completeInput x A (z m)) - f (completeInput x B (w m))) := by
  simp only [sampleCoalition, sum_sub_distrib, smul_sub]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace Ω] in
theorem value_tendsto {ι : Type*} {l : Filter ι} {V : ι → Finset (Fin n) → H}
    {W : Finset (Fin n) → H} (hV : ∀ A, Tendsto (fun m => V m A) l (𝓝 (W A)))
    (i : Fin n) : Tendsto (fun m => Shapley.value (V m) i) l (𝓝 (Shapley.value W i)) := by
  unfold Shapley.value Shapley.marginal
  apply tendsto_finset_sum
  intro A _
  exact ((hV (insert i A)).sub (hV A)).const_smul _

/-- All finitely many simulated coalition values can be substituted into the Shapley formula.
Different coalitions may share randomness; each coalition's sequence must satisfy its own law
and independence assumptions. -/
theorem simulation_attribution_tendsto_ae (f : (Fin n → ℝ) → H) (x : Fin n → ℝ)
    (ν : Finset (Fin n) → Measure (Fin n → ℝ)) (hf : Measurable f)
    (hint : ∀ A, Integrable (fun z => f (completeInput x A z)) (ν A))
    (z : Finset (Fin n) → ℕ → Ω → (Fin n → ℝ))
    (hlaw : ∀ A m, HasLaw (z A m) (ν A) μ)
    (hindep : ∀ A, Pairwise fun b c => z A b ⟂ᵢ[μ] z A c) (i : Fin n) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun M => Shapley.value (fun A => sampleCoalition M f x A (fun m => z A m.val ω)) i)
      atTop (𝓝 (Shapley.value (fun A => coalitionValue f x A (ν A)) i)) := by
  have hall : ∀ᵐ ω ∂μ, ∀ A, Tendsto
      (fun M => sampleCoalition M f x A (fun m => z A m.val ω))
      atTop (𝓝 (coalitionValue f x A (ν A))) :=
    ae_all_iff.mpr fun A =>
      sampleCoalition_tendsto_ae f x A (ν A) hf (hint A) (z A) (hlaw A) (hindep A)
  filter_upwards [hall] with ω hω
  exact value_tendsto hω i

end Thesis.DayAhead.ConditionalSimulation
