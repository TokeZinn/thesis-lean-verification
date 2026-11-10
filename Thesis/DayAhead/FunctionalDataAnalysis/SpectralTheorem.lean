import Thesis.DayAhead.FunctionalDataAnalysis.FunctionalData
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Compact self-adjoint spectral theory for the day-ahead chapter

This file bridges the spectral theorem quoted in
`2 - day-ahead/3_functional_data_analysis.tex`. Mathlib proves the decisive
completeness and finite-multiplicity statements for eigenspaces of compact
self-adjoint operators. The manuscript additionally packages those facts as
an operator-norm-convergent rank-one expansion. The nonzero eigenspaces are
assembled into a countable orthonormal family, and compactness upgrades its
pointwise projection convergence to convergence in operator norm.
-/

namespace Thesis
namespace DayAhead
namespace SpectralTheorem

open Filter
open scoped BigOperators Topology

universe u v

/-- Every nonzero eigenspace of a compact operator has finite dimension. -/
theorem compact_nonzero_eigenspace_finiteDimensional
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H)
    (hcompact : IsCompactOperator A) (a : ℝ) (ha : a ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace A.toLinearMap a) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hcompact a ha

/-- Distinct eigenspaces of a self-adjoint operator are orthogonal. -/
theorem selfAdjoint_distinct_eigenvectors_orthogonal
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H)
    (hsymm : A.toLinearMap.IsSymmetric)
    {eigenvalue₁ eigenvalue₂ : ℝ} (hne : eigenvalue₁ ≠ eigenvalue₂)
    {x y : H}
    (hx : x ∈ Module.End.eigenspace A.toLinearMap eigenvalue₁)
    (hy : y ∈ Module.End.eigenspace A.toLinearMap eigenvalue₂) :
    inner ℝ x y = 0 := by
  exact hsymm.orthogonalFamily_eigenspaces
    hne ⟨x, hx⟩ ⟨y, hy⟩

/-- A nonzero-eigenvalue eigenspace lies in the range of the operator. -/
theorem nonzero_eigenspace_le_range
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H) (eigenvalue : ℝ)
    (hne : eigenvalue ≠ 0) :
    Module.End.eigenspace A.toLinearMap eigenvalue ≤
      LinearMap.range A.toLinearMap := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx
  refine ⟨eigenvalue⁻¹ • x, ?_⟩
  simp only [map_smul, hx]
  rw [← mul_smul]
  simp [hne]

/-- The closed range of a self-adjoint operator is the orthogonal complement
of its kernel.  This is the structural fact behind the manuscript's statement
that a nonzero eigenbasis spans `closure (range A)` and may be extended by a
basis of the kernel. -/
theorem selfAdjoint_closure_range_eq_orthogonal_ker
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H)
    (hsymm : A.toLinearMap.IsSymmetric) :
    (LinearMap.range A.toLinearMap).topologicalClosure =
      (LinearMap.ker A.toLinearMap)ᗮ := by
  have hadjoint : A.adjoint = A :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hsymm.isSelfAdjoint
  simpa only [hadjoint] using (A.orthogonal_ker).symm

/-- The supremum of all nonzero eigenspaces is contained in the closed range. -/
theorem iSup_nonzero_eigenspaces_le_closure_range
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H) :
    (⨆ eigenvalue : {a : ℝ // a ≠ 0},
      Module.End.eigenspace A.toLinearMap eigenvalue.1) ≤
        (LinearMap.range A.toLinearMap).topologicalClosure := by
  refine iSup_le fun eigenvalue => ?_
  exact (nonzero_eigenspace_le_range A eigenvalue.1 eigenvalue.2).trans
    (LinearMap.range A.toLinearMap).le_topologicalClosure

/-! ## Fully internal finite-dimensional expansion -/

/-- An operator-norm-convergent rank-one eigen-expansion necessarily has
closed eigenvector span equal to the closed operator range. -/
theorem closedSpan_eq_closure_range_of_rankOne_expansion
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H)
    {ι : Type v} (e : ι → H) (eigenvalue : ι → ℝ)
    (hne : ∀ i, eigenvalue i ≠ 0)
    (heigen : ∀ i, A (e i) = eigenvalue i • e i)
    (hseries : Tendsto
      (fun s : Finset ι =>
        ∑ i ∈ s, eigenvalue i • FunctionalData.tensorProduct (e i) (e i))
      atTop (𝓝 A)) :
    (Submodule.span ℝ (Set.range e)).topologicalClosure =
      (LinearMap.range A.toLinearMap).topologicalClosure := by
  let W : Submodule ℝ H := Submodule.span ℝ (Set.range e)
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply (LinearMap.range A.toLinearMap).le_topologicalClosure
      refine ⟨(eigenvalue i)⁻¹ • e i, ?_⟩
      change A ((eigenvalue i)⁻¹ • e i) = e i
      rw [map_smul, heigen, ← mul_smul]
      simp [hne i]
    · exact Submodule.isClosed_topologicalClosure _
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      have happly : Tendsto
          (fun s : Finset ι =>
            (∑ i ∈ s,
              eigenvalue i • FunctionalData.tensorProduct (e i) (e i)) x)
          atTop (𝓝 (A x)) := by
        simpa only [Function.comp_apply] using
          ((((ContinuousLinearMap.apply ℝ H) x).continuous.tendsto A).comp
            hseries)
      have hpartial (s : Finset ι) :
          (∑ i ∈ s,
            eigenvalue i • FunctionalData.tensorProduct (e i) (e i)) x ∈ W := by
        simp only [ContinuousLinearMap.sum_apply]
        refine Submodule.sum_mem W fun i hi => ?_
        rw [ContinuousLinearMap.smul_apply, FunctionalData.tensorProduct_apply,
          smul_smul]
        exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
      exact (Submodule.isClosed_topologicalClosure W).mem_of_tendsto happly
        (Filter.Eventually.of_forall fun s => W.le_topologicalClosure (hpartial s))
    · exact Submodule.isClosed_topologicalClosure _

end SpectralTheorem
end DayAhead
end Thesis
