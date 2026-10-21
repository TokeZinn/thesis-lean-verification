import Thesis.DayAhead.FunctionalDataAnalysis.Covariance
import Thesis.DayAhead.FunctionalDataAnalysis.CompactSpectralExpansion
import Mathlib.Analysis.Convex.Integral

/-!
# Compact covariance and finite-rank approximation

The properties stated after `defn:covariance-operator` are proved for the
actual Bochner covariance operator. Compactness follows because rank-one
operators are compact and the compact operators form a closed convex set.
The finite-rank approximation criterion is proved for every bounded operator
on a real Hilbert space, without a separability assumption.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace Thesis.DayAhead.Covariance

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem tensorProduct_isCompactOperator (x y : H) :
    IsCompactOperator (FunctionalData.tensorProduct x y) := by
  have h := (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ x)).continuous_comp
    (continuous_id.smul continuous_const : Continuous (fun c : ℝ => c • y))
  exact h

/-- Thesis source: the compactness assertion immediately after
`defn:covariance-operator`, `2 - day-ahead/3_functional_data_analysis.tex`.

Original label: `defn:covariance-operator`.

Square integrability supplies the Bochner integrability needed here. -/
theorem covarianceOperator_isCompactOperator [CompleteSpace H]
    {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → H) (hX : MemLp X 2 μ) :
    IsCompactOperator (FunctionalData.covarianceOperator μ X) := by
  rw [covarianceOperator_eq_integral_covarianceIntegrand]
  exact (compactOperator (RingHom.id ℝ) H H).convex.integral_mem
    isClosed_setOf_isCompactOperator
    (Filter.Eventually.of_forall fun ω => tensorProduct_isCompactOperator _ _)
    (integrable_covarianceIntegrand_of_memLp_two μ X hX)

theorem partialProjection_comp_finiteDimensional_range
    {ι : Type*} (e : ι → H) (s : Finset ι) (A : H →L[ℝ] H) :
    FiniteDimensional ℝ
      (LinearMap.range ((CompactSpectralExpansion.partialProjection e s).comp A).toLinearMap) := by
  let W := Submodule.span ℝ (e '' (s : Set ι))
  haveI : FiniteDimensional ℝ W :=
    FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image e)
  apply Submodule.finiteDimensional_of_le (S₂ := W)
  rintro _ ⟨x, rfl⟩
  change CompactSpectralExpansion.partialProjection e s (A x) ∈ W
  rw [CompactSpectralExpansion.partialProjection_apply]
  exact Submodule.sum_mem W fun i hi =>
    W.smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem isCompactOperator_of_finiteDimensional_range (A : H →L[ℝ] H)
    [FiniteDimensional ℝ (LinearMap.range A.toLinearMap)] :
    IsCompactOperator A := by
  let R := LinearMap.range A.toLinearMap
  let B : H →L[ℝ] R := A.codRestrict R (fun x => LinearMap.mem_range_self _ x)
  exact (isCompactOperator_of_locallyCompactSpace_dom B).continuous_comp
    continuous_subtype_val

/-- A compact Hilbert-space operator is a sequential operator-norm limit of
operators with finite-dimensional image. -/
theorem exists_finiteRank_approximation [CompleteSpace H]
    (A : H →L[ℝ] H) (hA : IsCompactOperator A) :
    ∃ B : ℕ → H →L[ℝ] H,
      (∀ n, FiniteDimensional ℝ (LinearMap.range (B n).toLinearMap)) ∧
      Tendsto B atTop (𝓝 A) := by
  obtain ⟨I, b, _⟩ := exists_hilbertBasis ℝ H
  let F := fun s : Finset I => (CompactSpectralExpansion.partialProjection b s).comp A
  have hlim : Tendsto F atTop (𝓝 A) :=
    CompactSpectralExpansion.partialProjection_comp_tendsto b b.orthonormal A hA
      (by rw [b.dense_span]; exact le_top)
  have hclosure : A ∈ closure (Set.range F) :=
    mem_closure_of_tendsto hlim (Filter.Eventually.of_forall Set.mem_range_self)
  obtain ⟨B, hB, hlimB⟩ := mem_closure_iff_seq_limit.mp hclosure
  refine ⟨B, fun n => ?_, hlimB⟩
  obtain ⟨s, hs⟩ := hB n
  rw [← hs]
  exact partialProjection_comp_finiteDimensional_range b s A

/-- Thesis source: the finite-rank approximation criterion in the prose after
`defn:covariance-operator`. This proves both directions of the equivalence.

Original label: `defn:covariance-operator`.
-/
theorem isCompactOperator_iff_finiteRank_approximation [CompleteSpace H]
    (A : H →L[ℝ] H) :
    IsCompactOperator A ↔
      ∃ B : ℕ → H →L[ℝ] H,
        (∀ n, FiniteDimensional ℝ (LinearMap.range (B n).toLinearMap)) ∧
        Tendsto (fun n => ‖A - B n‖) atTop (𝓝 0) := by
  constructor
  · intro hA
    obtain ⟨B, hB, hlim⟩ := exists_finiteRank_approximation A hA
    exact ⟨B, hB, by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A)).sub
        hlim).norm⟩
  · rintro ⟨B, hB, hlim⟩
    have hlimB : Tendsto B atTop (𝓝 A) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa only [norm_sub_rev] using hlim
    apply isCompactOperator_of_tendsto hlimB
    exact Filter.Eventually.of_forall fun n => by
      letI := hB n
      exact isCompactOperator_of_finiteDimensional_range (B n)

end Thesis.DayAhead.Covariance
