import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Max

/-! # The valid filtration consequence of ideal PIT calibration

A constant conditional law at each forecast origin, together with observation
by origin plus horizon, implies independence along each horizon-spaced
subsequence. It does not assert independence of separated blocks.

`ConditionalLaw` is the event-integral characterization of a conditional law.
The general randomized-CDF transformation establishing this characterization
from an ideal conditional CDF is a separate bridge; it is not assumed to have
been proved by the finite counterexample in `PITCounterexample`.
-/

noncomputable section
namespace Thesis.Foundations.Research.PITCalibration

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]

/-- The constant conditional law of `U` given an information sigma algebra,
expressed through the defining event-integral identity. -/
def ConditionalLaw (μ : Measure Ω) (information : MeasurableSpace Ω)
    (U : Ω → E) (ν : Measure E) : Prop :=
  ∀ A B, MeasurableSet[information] A → MeasurableSet B →
    μ (A ∩ U ⁻¹' B) = μ A * ν B

theorem ConditionalLaw.marginal {μ : Measure Ω} [IsProbabilityMeasure μ]
    {information : MeasurableSpace Ω} {U : Ω → E} {ν : Measure E}
    (h : ConditionalLaw (mΩ := mΩ) μ information U ν) {B : Set E} (hB : MeasurableSet B) :
    μ (U ⁻¹' B) = ν B := by
  simpa using h univ B MeasurableSet.univ hB

theorem ConditionalLaw.map_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {information : MeasurableSpace Ω} {U : Ω → E} {ν : Measure E}
    (h : ConditionalLaw (mΩ := mΩ) μ information U ν)
    (hU : @Measurable Ω E mΩ _ U) : @Measure.map Ω E mΩ _ U μ = ν := by
  ext B hB
  rw [Measure.map_apply hU hB, ConditionalLaw.marginal (mΩ := mΩ) h hB]

/-- The source's valid horizon-spaced independence claim. The proof peels off
the latest forecast origin; all earlier selected PITs are then measurable in
its information sigma algebra. The target law can be any constant law. -/
theorem horizon_spaced_independent (μ : Measure Ω) [IsProbabilityMeasure μ] {ν : Measure E}
    (information : Filtration ℕ mΩ) (U : ℕ → Ω → E)
    (horizon : ℕ) (_hh : 0 < horizon)
    (observed : ∀ n, Measurable[information (n + horizon)] (U n))
    (calibrated : ∀ n, ConditionalLaw μ (information n) (U n) ν)
    (residue : ℕ) : iIndepFun (fun k => U (residue + k * horizon)) μ := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hsets
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    have hnot : a ∉ S := fun ha => lt_irrefl a (hlt a ha)
    have hmA : MeasurableSet[information (residue + a * horizon)]
        (⋂ i ∈ S, U (residue + i * horizon) ⁻¹' sets i) := by
      apply MeasurableSet.biInter S.countable_toSet
      intro i hi
      have hi' : i < a := hlt i hi
      have htime : residue + i * horizon + horizon ≤ residue + a * horizon := by
        nlinarith
      exact (information.mono htime) _
        ((observed _) (hsets i (Finset.mem_insert_of_mem hi)))
    have hma := hsets a (Finset.mem_insert_self a S)
    have hfact := calibrated (residue + a * horizon)
      (⋂ i ∈ S, U (residue + i * horizon) ⁻¹' sets i) (sets a) hmA hma
    have hinter : (⋂ i ∈ insert a S, U (residue + i * horizon) ⁻¹' sets i) =
        U (residue + a * horizon) ⁻¹' sets a ∩
          (⋂ i ∈ S, U (residue + i * horizon) ⁻¹' sets i) := by
      ext ω
      simp
    rw [hinter, inter_comm, hfact,
      ← (calibrated (residue + a * horizon)).marginal hma,
      ih (fun i hi => hsets i (Finset.mem_insert_of_mem hi)),
      Finset.prod_insert hnot, mul_comm]

/-- Lebesgue probability measure on the unit interval, equivalent to the
usual continuous uniform law on `(0,1)`. -/
def uniformLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure uniformLaw := by
  constructor
  norm_num [uniformLaw]

theorem uniformLaw_Iic (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    uniformLaw (Iic u) = ENNReal.ofReal u := by
  have he : Iic u ∩ Icc (0 : ℝ) 1 = Icc 0 u := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxu, h0x, _⟩
      exact ⟨h0x, hxu⟩
    · rintro ⟨h0x, hxu⟩
      exact ⟨hxu, h0x, hxu.trans hu.2⟩
  simp only [uniformLaw, Measure.restrict_apply measurableSet_Iic, he,
    Real.volume_Icc, sub_zero]

/-- The threshold form of conditional uniformity used in the corrected
appendix, expressed without choosing versions of conditional probabilities. -/
theorem conditional_uniform_threshold {μ : Measure Ω}
    {information : MeasurableSpace Ω} {U : Ω → ℝ}
    (h : ConditionalLaw (mΩ := mΩ) μ information U uniformLaw)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (A : Set Ω)
    (hA : MeasurableSet[information] A) :
    μ (A ∩ U ⁻¹' Iic u) = μ A * ENNReal.ofReal u := by
  rw [h A (Iic u) hA measurableSet_Iic, uniformLaw_Iic u hu]

/-- Conditional uniformity implies marginal uniformity. This is the exact
event-integral formulation; the CDF-transform bridge remains separate. -/
theorem conditional_uniform_marginal {μ : Measure Ω} [IsProbabilityMeasure μ]
    {information : MeasurableSpace Ω} {U : Ω → ℝ}
    (h : ConditionalLaw (mΩ := mΩ) μ information U uniformLaw)
    (hU : @Measurable Ω ℝ mΩ _ U) :
    @Measure.map Ω ℝ mΩ _ U μ = uniformLaw :=
  ConditionalLaw.map_eq (mΩ := mΩ) h hU

/-- Each fixed-residue subsequence has independent uniform coordinates under
the corrected origin-information and observation-time hypotheses. -/
theorem horizon_spaced_uniform (μ : Measure Ω) [IsProbabilityMeasure μ]
    (information : Filtration ℕ mΩ) (U : ℕ → Ω → ℝ)
    (horizon : ℕ) (hh : 0 < horizon)
    (observed : ∀ n, Measurable[information (n + horizon)] (U n))
    (calibrated : ∀ n, ConditionalLaw μ (information n) (U n) uniformLaw)
    (residue : ℕ) :
    iIndepFun (fun k => U (residue + k * horizon)) μ ∧
      ∀ k, μ.map (U (residue + k * horizon)) = uniformLaw := by
  refine ⟨horizon_spaced_independent μ information U horizon hh observed calibrated residue, ?_⟩
  intro k
  exact (calibrated _).map_eq ((observed _).mono (information.le _) le_rfl)

end Thesis.Foundations.Research.PITCalibration
