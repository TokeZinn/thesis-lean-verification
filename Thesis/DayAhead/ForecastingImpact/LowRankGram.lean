import Thesis.DayAhead.ForecastingImpact.TreeImpurity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-! # The retained low-rank Gram factor in the current forecasting chapter

The current numerical appendix uses no separate eigenvalue tolerance.
Retained negative eigenvalues are clipped to zero. The displayed column-sum
identities are exact for the retained surrogate matrix; the exact spectral
truncation error is formalized separately.
-/

noncomputable section
namespace Thesis.DayAhead.LowRankGram

open scoped BigOperators Matrix
open TreeImpurity

def retainedEigenvalue (ev : ℝ) : ℝ := max 0 ev

theorem retainedEigenvalue_nonneg (ev : ℝ) : 0 ≤ retainedEigenvalue ev := le_max_left _ _

theorem retainedEigenvalue_of_nonneg {ev : ℝ} (hev : 0 ≤ ev) : retainedEigenvalue ev = ev :=
  max_eq_right hev

theorem retainedEigenvalue_of_negative {ev : ℝ} (hev : ev < 0) : retainedEigenvalue ev = 0 :=
  max_eq_left hev.le

variable {ι ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- The source's `C_r = sqrt(Λ_r) U_rᵀ`, with the retained eigenvalue convention explicit. -/
def factor (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) : Matrix ρ ι ℝ :=
  Matrix.diagonal (fun k => Real.sqrt (retainedEigenvalue (ev k))) * U.transpose

def surrogateGram (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) : Matrix ι ι ℝ :=
  U * Matrix.diagonal (fun k => retainedEigenvalue (ev k)) * U.transpose

theorem factor_apply (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) (k : ρ) (i : ι) :
    factor U ev k i = Real.sqrt (retainedEigenvalue (ev k)) * U i k := by
  simp only [factor, Matrix.diagonal_mul, Matrix.transpose_apply]

theorem factor_transpose_mul (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) :
    (factor U ev).transpose * factor U ev = surrogateGram U ev := by
  ext i j
  change (∑ k, factor U ev k i * factor U ev k j) =
    ∑ k, (U * Matrix.diagonal (fun k => retainedEigenvalue (ev k))) i k * U j k
  simp only [factor_apply, Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (Real.sqrt (retainedEigenvalue (ev k)) * U i k) *
        (Real.sqrt (retainedEigenvalue (ev k)) * U j k) =
      Real.sqrt (retainedEigenvalue (ev k)) ^ 2 * U i k * U j k := by ring
    _ = _ := by rw [Real.sq_sqrt (retainedEigenvalue_nonneg _)]; ring

/-- Euclidean columns; the plain function space's maximum norm is not used. -/
def column (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) (i : ι) : EuclideanSpace ℝ ρ :=
  WithLp.toLp 2 (fun k => factor U ev k i)

theorem inner_columns (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) (i j : ι) :
    inner ℝ (column U ev i) (column U ev j) = surrogateGram U ev i j := by
  rw [← factor_transpose_mul]
  simp only [column, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem surrogateGram_posSemidef [Finite ι] (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) :
    (surrogateGram U ev).PosSemidef := by
  rw [← factor_transpose_mul]
  simpa only [Matrix.conjTranspose, star_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (factor U ev)

def matrixBlock (G : Matrix ι ι ℝ) (s t : Finset ι) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ t, G i j

theorem surrogate_block_eq_inner (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) (s t : Finset ι) :
    matrixBlock (surrogateGram U ev) s t =
      inner ℝ (∑ i ∈ s, column U ev i) (∑ j ∈ t, column U ev j) := by
  rw [← gramBlock_eq_inner]
  simp only [matrixBlock, gramBlock, inner_columns]

theorem surrogate_block_eq_norm_sq (U : Matrix ι ρ ℝ) (ev : ρ → ℝ) (s : Finset ι) :
    matrixBlock (surrogateGram U ev) s s = ‖∑ i ∈ s, column U ev i‖ ^ 2 := by
  rw [surrogate_block_eq_inner, real_inner_self_eq_norm_sq]

omit [Fintype ρ] [DecidableEq ρ] in
theorem matrixBlock_error_bound (G G' : Matrix ι ι ℝ) (s t : Finset ι) (ε : ℝ)
    (hε : ∀ i ∈ s, ∀ j ∈ t, |G i j - G' i j| ≤ ε) :
    |matrixBlock G s t - matrixBlock G' s t| ≤ (s.card : ℝ) * t.card * ε := by
  simp only [matrixBlock, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, |G i j - G' i j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, ∑ _j ∈ t, ε :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hε i hi j hj
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Thesis.DayAhead.LowRankGram
