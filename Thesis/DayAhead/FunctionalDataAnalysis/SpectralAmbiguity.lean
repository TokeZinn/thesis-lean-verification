import Thesis.DayAhead.FunctionalDataAnalysis.SpectralTheorem

/-! # Basis choices and invariant eigenspace projections -/

noncomputable section
namespace Thesis.DayAhead.SpectralTheorem

open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Original block id: `source:2 - day-ahead/3_functional_data_analysis.tex:105:rem:5`.
Normalization leaves exactly a sign choice in a one-dimensional eigenspace. -/
theorem unit_vectors_eq_or_neg_of_finrank_one (U : Submodule ℝ H)
    (hU : Module.finrank ℝ U = 1) {x y : U} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    y = x ∨ y = -x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hU hx0 y
  have habs : |c| = 1 := by simpa [norm_smul, hx] using (congrArg norm hc).trans hy
  have hsign : c = 1 ∨ c = -1 := by
    rcases le_total 0 c with h | h
    · exact Or.inl (by simpa only [abs_of_nonneg h] using habs)
    · exact Or.inr (by rw [abs_of_nonpos h] at habs; linarith)
  rcases hsign with rfl | rfl
  · exact Or.inl (by simpa using hc.symm)
  · exact Or.inr (by simpa using hc.symm)

/-- Original block id: `source:2 - day-ahead/3_functional_data_analysis.tex:105:rem:5`.
Both signs are unit eigenvectors for the same eigenvalue. -/
theorem neg_unit_eigenvector (A : H →L[ℝ] H) (eigenvalue : ℝ) {x : H}
    (hx : A x = eigenvalue • x) (hn : ‖x‖ = 1) :
    A (-x) = eigenvalue • (-x) ∧ ‖-x‖ = 1 := by
  simp [hx, hn]

/-- Original block id: `source:2 - day-ahead/3_functional_data_analysis.tex:105:rem:5`.
Distinct orthonormal basis vectors can be exchanged within one eigenspace. -/
theorem orthonormalBasis_swap_ne {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ H) {i j : ι} (hij : i ≠ j) :
    ∃ c : OrthonormalBasis ι ℝ H, c ≠ b ∧ c i = b j ∧ c j = b i := by
  classical
  refine ⟨b.reindex (Equiv.swap i j), ?_, ?_, ?_⟩
  · intro h
    have he := congrArg (fun a : OrthonormalBasis ι ℝ H => a i) h
    dsimp only at he
    rw [b.reindex_apply] at he
    simp only [Equiv.symm_swap, Equiv.swap_apply_left] at he
    exact hij (b.toBasis.injective he).symm
  · simp only [b.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left]
  · simp only [b.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right]

/-- Original block id: `source:2 - day-ahead/3_functional_data_analysis.tex:105:rem:5`.
The sum of rank-one projections depends only on the eigenspace, for any two
orthonormal bases, even with different finite index types. -/
theorem orthonormalBasis_projection_invariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Submodule ℝ H) [U.HasOrthogonalProjection]
    (b : OrthonormalBasis ι ℝ U) (c : OrthonormalBasis κ ℝ U) :
    (∑ i, InnerProductSpace.rankOne ℝ (b i : H) (b i : H)) =
      ∑ j, InnerProductSpace.rankOne ℝ (c j : H) (c j : H) := by
  rw [← b.starProjection_eq_sum_rankOne, ← c.starProjection_eq_sum_rankOne]

end Thesis.DayAhead.SpectralTheorem
