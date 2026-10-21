import Thesis.DayAhead.FunctionalDataAnalysis.FunctionalData
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Thesis.DayAhead.FunctionalDataAnalysis.CompactSpectralExpansion

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

/--
Thesis source: `2 - day-ahead/3_functional_data_analysis.tex`, spectral
completeness core of Theorem `thm:spectral-thm`.

Original label: `thm:spectral-thm`.

Informal statement: the eigenspaces of a compact self-adjoint operator span a
dense subspace of the Hilbert space (including the zero eigenspace, i.e. the
kernel).

Lean strategy / thesis relation note: this is Mathlib's compact self-adjoint
spectral theorem. The manuscript's basis of `closure (range A)` is obtained by
discarding the zero eigenspace; a basis of the kernel then extends it to the
whole space.
-/
theorem compact_selfAdjoint_eigenspaces_complete
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H)
    (hcompact : IsCompactOperator A) (hsymm : A.toLinearMap.IsSymmetric) :
    (⨆ a : ℝ, Module.End.eigenspace A.toLinearMap a)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    hcompact hsymm

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

/-- For a compact self-adjoint operator, the orthogonal complement of the
nonzero eigenspaces is exactly the kernel. -/
theorem orthogonal_iSup_nonzero_eigenspaces_eq_ker
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H)
    (hcompact : IsCompactOperator A) (hsymm : A.toLinearMap.IsSymmetric) :
    (⨆ eigenvalue : {a : ℝ // a ≠ 0},
      Module.End.eigenspace A.toLinearMap eigenvalue.1)ᗮ =
        LinearMap.ker A.toLinearMap := by
  let V : Submodule ℝ H :=
    ⨆ eigenvalue : {a : ℝ // a ≠ 0},
      Module.End.eigenspace A.toLinearMap eigenvalue.1
  have hcomplete :
      (⨆ eigenvalue : ℝ,
        Module.End.eigenspace A.toLinearMap eigenvalue)ᗮ = ⊥ :=
    compact_selfAdjoint_eigenspaces_complete A hcompact hsymm
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker]
    have hAx : A x ∈
        (⨆ eigenvalue : ℝ,
          Module.End.eigenspace A.toLinearMap eigenvalue)ᗮ := by
      rw [← Submodule.iInf_orthogonal]
      refine (Submodule.mem_iInf _).mpr fun eigenvalue => ?_
      intro y hy
      rw [Module.End.mem_eigenspace_iff] at hy
      change A y = eigenvalue • y at hy
      by_cases heigenvalue : eigenvalue = 0
      · subst eigenvalue
        calc
          inner ℝ y (A x) = inner ℝ (A y) x := (hsymm y x).symm
          _ = inner ℝ (0 : H) x := by rw [hy, zero_smul]
          _ = 0 := inner_zero_left x
      · have hyE : y ∈ Module.End.eigenspace A.toLinearMap eigenvalue := by
          rw [Module.End.mem_eigenspace_iff]
          exact hy
        have hyV : y ∈ V := by
          change y ∈ (⨆ a : {a : ℝ // a ≠ 0},
            Module.End.eigenspace A.toLinearMap a.1)
          exact (le_iSup
            (fun a : {a : ℝ // a ≠ 0} =>
              Module.End.eigenspace A.toLinearMap a.1)
            ⟨eigenvalue, heigenvalue⟩) hyE
        calc
          inner ℝ y (A x) = inner ℝ (A y) x := (hsymm y x).symm
          _ = inner ℝ (eigenvalue • y) x := by rw [hy]
          _ = 0 := by simp [real_inner_smul_left, hx y hyV]
    rw [hcomplete] at hAx
    exact hAx
  · intro x hx
    change x ∈ Vᗮ
    rw [← Submodule.iInf_orthogonal]
    refine (Submodule.mem_iInf _).mpr fun eigenvalue => ?_
    intro y hy
    have hxzero : x ∈ Module.End.eigenspace A.toLinearMap 0 := by
      rw [Module.End.mem_eigenspace_iff, zero_smul]
      exact LinearMap.mem_ker.mp hx
    exact selfAdjoint_distinct_eigenvectors_orthogonal A hsymm
      eigenvalue.2 hy hxzero

/--
Thesis source: subspace-completeness clause of Theorem `thm:spectral-thm` in
`2 - day-ahead/3_functional_data_analysis.tex`.

Original label: `thm:spectral-thm`.

The closed span of all nonzero eigenspaces is exactly the closure of the
operator range.  This verifies the subspace-completeness clause of the
manuscript's spectral theorem without invoking the external rank-one series.
-/
theorem closure_iSup_nonzero_eigenspaces_eq_closure_range
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H)
    (hcompact : IsCompactOperator A) (hsymm : A.toLinearMap.IsSymmetric) :
    (⨆ eigenvalue : {a : ℝ // a ≠ 0},
      Module.End.eigenspace A.toLinearMap eigenvalue.1).topologicalClosure =
        (LinearMap.range A.toLinearMap).topologicalClosure := by
  let V : Submodule ℝ H :=
    ⨆ eigenvalue : {a : ℝ // a ≠ 0},
      Module.End.eigenspace A.toLinearMap eigenvalue.1
  calc
    V.topologicalClosure = Vᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure V).symm
    _ = (LinearMap.ker A.toLinearMap)ᗮ := by
      rw [orthogonal_iSup_nonzero_eigenspaces_eq_ker A hcompact hsymm]
    _ = (LinearMap.range A.toLinearMap).topologicalClosure :=
      (selfAdjoint_closure_range_eq_orthogonal_ker A hsymm).symm

/-! ## Fully internal finite-dimensional expansion -/

/--
Thesis source: finite-dimensional specialisation of Theorem
`thm:spectral-thm` in
`2 - day-ahead/3_functional_data_analysis.tex`.

Original label: `thm:spectral-thm`.

In finite dimension the complete rank-one eigen-expansion follows directly
from Mathlib's orthonormal eigenvector basis.  No compactness hypothesis or
external theorem is needed in this case.
-/
theorem finiteDimensional_selfAdjoint_rankOne_expansion
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (A : H →L[ℝ] H) (hsymm : A.toLinearMap.IsSymmetric) :
    let e := hsymm.eigenvectorBasis
      (n := Module.finrank ℝ H) rfl
    let eigenvalue := hsymm.eigenvalues
      (n := Module.finrank ℝ H) rfl
    ∑ i, eigenvalue i • FunctionalData.tensorProduct (e i) (e i) = A := by
  dsimp only
  let e := hsymm.eigenvectorBasis
    (n := Module.finrank ℝ H) rfl
  let eigenvalue := hsymm.eigenvalues
    (n := Module.finrank ℝ H) rfl
  apply ContinuousLinearMap.ext
  intro x
  symm
  calc
    A x = A (∑ i, inner ℝ (e i) x • e i) := by
      rw [e.sum_repr']
    _ = ∑ i, inner ℝ (e i) x • A (e i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
    _ = ∑ i, inner ℝ (e i) x • (eigenvalue i • e i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show A (e i) = eigenvalue i • e i by
        exact hsymm.apply_eigenvectorBasis rfl i]
    _ = (∑ i, eigenvalue i •
        FunctionalData.tensorProduct (e i) (e i)) x := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        FunctionalData.tensorProduct_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul, smul_smul]
      congr 1
      ring

/-- The finite-subset net of the preceding finite-dimensional expansion is
eventually equal to the operator. -/
theorem finiteDimensional_selfAdjoint_rankOne_expansion_tendsto
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (A : H →L[ℝ] H) (hsymm : A.toLinearMap.IsSymmetric) :
    let I := Fin (Module.finrank ℝ H)
    let e := hsymm.eigenvectorBasis
      (n := Module.finrank ℝ H) rfl
    let eigenvalue := hsymm.eigenvalues
      (n := Module.finrank ℝ H) rfl
    Tendsto
      (fun s : Finset I ↦
        ∑ i ∈ s, eigenvalue i •
          FunctionalData.tensorProduct (e i) (e i))
      atTop (𝓝 A) := by
  dsimp only
  apply tendsto_atTop_of_eventually_const
    (i₀ := Finset.univ)
  intro s hs
  have hsUniv : s = Finset.univ := Finset.eq_univ_iff_forall.mpr fun i ↦
    hs (Finset.mem_univ i)
  rw [hsUniv]
  simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
    finiteDimensional_selfAdjoint_rankOne_expansion A hsymm

/-- Removing the zero-eigenvalue indices from the finite-dimensional
expansion does not change the represented operator. -/
theorem finiteDimensional_selfAdjoint_nonzero_rankOne_expansion
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (A : H →L[ℝ] H) (hsymm : A.toLinearMap.IsSymmetric) :
    let eBasis := hsymm.eigenvectorBasis
      (n := Module.finrank ℝ H) rfl
    let eigenvalue := hsymm.eigenvalues
      (n := Module.finrank ℝ H) rfl
    let I := {i : Fin (Module.finrank ℝ H) // eigenvalue i ≠ 0}
    ∑ i : I, eigenvalue i.1 •
      FunctionalData.tensorProduct (eBasis i.1) (eBasis i.1) = A := by
  classical
  dsimp only
  let eBasis := hsymm.eigenvectorBasis
    (n := Module.finrank ℝ H) rfl
  let eigenvalue := hsymm.eigenvalues
    (n := Module.finrank ℝ H) rfl
  let term : Fin (Module.finrank ℝ H) → H →L[ℝ] H := fun i ↦
    eigenvalue i • FunctionalData.tensorProduct (eBasis i) (eBasis i)
  have hsubtype :
      (∑ i : {i : Fin (Module.finrank ℝ H) // eigenvalue i ≠ 0},
        term i.1) =
        ∑ i ∈ Finset.univ.filter (fun i ↦ eigenvalue i ≠ 0), term i := by
    symm
    exact Finset.sum_subtype
      (Finset.univ.filter (fun i ↦ eigenvalue i ≠ 0))
      (fun i ↦ by simp) term
  rw [hsubtype]
  have hfilter :
      (∑ i ∈ Finset.univ.filter (fun i ↦ eigenvalue i ≠ 0), term i) =
        ∑ i, term i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hzero : eigenvalue i = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
    simp [term, hzero]
  rw [hfilter]
  exact finiteDimensional_selfAdjoint_rankOne_expansion A hsymm

/-- In finite dimension, the thesis's nonzero-eigenvector series package is
fully internal, including countability and convergence of the finite-subset
net. -/
theorem finiteDimensional_rankOne_expansion_data
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H] [FiniteDimensional ℝ H]
    (A : H →L[ℝ] H) (hsymm : A.toLinearMap.IsSymmetric) :
    ∃ (I : Type) (_hI : Countable I) (e : I → H) (eigenvalue : I → ℝ),
      Orthonormal ℝ e ∧
      (∀ i, eigenvalue i ≠ 0) ∧
      (∀ i, A (e i) = eigenvalue i • e i) ∧
      Tendsto
        (fun s : Finset I ↦
          ∑ i ∈ s, eigenvalue i • FunctionalData.tensorProduct (e i) (e i))
        atTop (𝓝 A) := by
  classical
  let eBasis := hsymm.eigenvectorBasis
    (n := Module.finrank ℝ H) rfl
  let eigenvalueFull := hsymm.eigenvalues
    (n := Module.finrank ℝ H) rfl
  let I := {i : Fin (Module.finrank ℝ H) // eigenvalueFull i ≠ 0}
  let e : I → H := fun i ↦ eBasis i.1
  let eigenvalue : I → ℝ := fun i ↦ eigenvalueFull i.1
  refine ⟨I, inferInstance, e, eigenvalue, ?_, ?_, ?_, ?_⟩
  · exact eBasis.orthonormal.comp _ Subtype.val_injective
  · exact fun i ↦ i.2
  · intro i
    exact hsymm.apply_eigenvectorBasis rfl i.1
  · apply tendsto_atTop_of_eventually_const (i₀ := Finset.univ)
    intro s hs
    have hsUniv : s = Finset.univ := Finset.eq_univ_iff_forall.mpr fun i ↦
      hs (Finset.mem_univ i)
    rw [hsUniv]
    simpa only [e, eigenvalue] using
      finiteDimensional_selfAdjoint_nonzero_rankOne_expansion A hsymm

/--
Exact operator-series packaging of thesis Theorem `thm:spectral-thm`.

Original label: `thm:spectral-thm`.

Proof: choose an orthonormal basis of each finite-dimensional nonzero
eigenspace and combine them using orthogonality of distinct eigenspaces.
Separability makes the resulting family countable. Its closed span contains
the operator range, and finite orthogonal projections converge uniformly on
the compact closure of the image of the unit ball. This gives convergence in
operator norm. The historical declaration name is retained for compatibility;
it no longer introduces an axiom.

The finite-subset net avoids choosing an arbitrary enumeration. Countability
matches the separability assumption in the thesis. The closed-span conclusion
is no longer assumed here: it is derived below from the operator-norm limit.
-/
theorem compact_selfAdjoint_rankOne_expansion_external
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (A : H →L[ℝ] H) (hcompact : IsCompactOperator A)
    (hsymm : A.toLinearMap.IsSymmetric)
    (_hInfinite : ¬ FiniteDimensional ℝ H) :
    ∃ (ι : Type) (_hι : Countable ι) (e : ι → H) (eigenvalue : ι → ℝ),
      Orthonormal ℝ e ∧
      (∀ i, eigenvalue i ≠ 0) ∧
      (∀ i, A (e i) = eigenvalue i • e i) ∧
      Tendsto
        (fun s : Finset ι =>
          ∑ i ∈ s, eigenvalue i • FunctionalData.tensorProduct (e i) (e i))
        atTop (𝓝 A) := by
  classical
  let E (a : {a : ℝ // a ≠ 0}) := Module.End.eigenspace A.toLinearMap a.val
  haveI (a : {a : ℝ // a ≠ 0}) : FiniteDimensional ℝ (E a) :=
    compact_nonzero_eigenspace_finiteDimensional A hcompact a.val a.property
  let b (a : {a : ℝ // a ≠ 0}) := stdOrthonormalBasis ℝ (E a)
  let I := Σ a : {a : ℝ // a ≠ 0}, Fin (Module.finrank ℝ (E a))
  let e : I → H := fun i => b i.1 i.2
  let eigenvalue : I → ℝ := fun i => i.1.val
  have horth : OrthogonalFamily ℝ (fun a => E a) (fun a => (E a).subtypeₗᵢ) :=
    hsymm.orthogonalFamily_eigenspaces.comp Subtype.val_injective
  have he : Orthonormal ℝ e :=
    horth.orthonormal_sigma_orthonormal (fun a => (b a).orthonormal)
  have hcount : Countable I := CompactSpectralExpansion.countable_of_orthonormal e he
  have heigen (i : I) : A (e i) = eigenvalue i • e i :=
    Module.End.mem_eigenspace_iff.mp (b i.1 i.2).property
  have hspan : Submodule.span ℝ (Set.range e) = ⨆ a, E a := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.mem_iSup_of_mem i.1 (b i.1 i.2).property
    · apply iSup_le
      intro a
      have hEa : Submodule.span ℝ (Set.range fun i => ((b a i : E a) : H)) = E a := by
        have hb := (E a).span_val_image_eq_iff (Set.range (b a))
        rw [← Set.range_comp] at hb
        exact hb.mpr (b a).toBasis.span_eq
      rw [← hEa]
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨a, i⟩, rfl⟩
  refine ⟨I, hcount, e, eigenvalue, he, fun i => i.1.property, heigen, ?_⟩
  apply CompactSpectralExpansion.rankOne_expansion_tendsto e he A hcompact hsymm
    eigenvalue heigen
  rw [hspan]
  change LinearMap.range A.toLinearMap ≤
    (⨆ a : {a : ℝ // a ≠ 0}, Module.End.eigenspace A.toLinearMap a.val).topologicalClosure
  rw [closure_iSup_nonzero_eigenspaces_eq_closure_range A hcompact hsymm]
  exact (LinearMap.range A.toLinearMap).le_topologicalClosure

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

/--
Full operator-series formulation of thesis Theorem `thm:spectral-thm`.

Original label: `thm:spectral-thm`.

Both the finite- and infinite-dimensional expansions are proved internally.
The basis-of-closed-range clause follows from the operator-norm series limit
and the nonzero eigenvalue identities.
-/
theorem compact_selfAdjoint_rankOne_expansion
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (A : H →L[ℝ] H) (hcompact : IsCompactOperator A)
    (hsymm : A.toLinearMap.IsSymmetric) :
    ∃ (ι : Type) (_hι : Countable ι) (e : ι → H) (eigenvalue : ι → ℝ),
      Orthonormal ℝ e ∧
      (Submodule.span ℝ (Set.range e)).topologicalClosure =
        (LinearMap.range A.toLinearMap).topologicalClosure ∧
      (∀ i, A (e i) = eigenvalue i • e i) ∧
      Tendsto
        (fun s : Finset ι =>
          ∑ i ∈ s, eigenvalue i • FunctionalData.tensorProduct (e i) (e i))
        atTop (𝓝 A) := by
  classical
  by_cases hfinite : FiniteDimensional ℝ H
  · letI : FiniteDimensional ℝ H := hfinite
    obtain ⟨ι, hι, e, eigenvalue, he, hne, heigen, hseries⟩ :=
      finiteDimensional_rankOne_expansion_data A hsymm
    exact ⟨ι, hι, e, eigenvalue, he,
      closedSpan_eq_closure_range_of_rankOne_expansion
        A e eigenvalue hne heigen hseries,
      heigen, hseries⟩
  · obtain ⟨ι, hι, e, eigenvalue, he, hne, heigen, hseries⟩ :=
      compact_selfAdjoint_rankOne_expansion_external A hcompact hsymm hfinite
    exact ⟨ι, hι, e, eigenvalue, he,
      closedSpan_eq_closure_range_of_rankOne_expansion
        A e eigenvalue hne heigen hseries,
      heigen, hseries⟩

end SpectralTheorem
end DayAhead
end Thesis
