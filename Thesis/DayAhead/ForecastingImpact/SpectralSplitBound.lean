import Thesis.DayAhead.ForecastingImpact.LowRankGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive

/-! # The actual spectral-truncation error for a tree split -/

noncomputable section
namespace Thesis.DayAhead.SpectralSplitBound

open scoped BigOperators InnerProductSpace Matrix
open Matrix TreeImpurity

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def gramOperator (y : ι → H) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (Matrix.gram ℝ y).toEuclideanLin

theorem gram_positive (y : ι → H) : (gramOperator y).IsPositive :=
  Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.posSemidef_gram ℝ y)

def eigenBasis (y : ι → H) : OrthonormalBasis (Fin (Fintype.card ι)) ℝ (EuclideanSpace ℝ ι) :=
  (gram_positive y).1.eigenvectorBasis finrank_euclideanSpace

def eigenvalue (y : ι → H) : Fin (Fintype.card ι) → ℝ :=
  (gram_positive y).1.eigenvalues finrank_euclideanSpace

theorem eigenvalue_antitone (y : ι → H) : Antitone (eigenvalue y) :=
  (gram_positive y).1.eigenvalues_antitone finrank_euclideanSpace

theorem eigenvalue_nonneg (y : ι → H) (i : Fin (Fintype.card ι)) : 0 ≤ eigenvalue y i := by
  have h := (gram_positive y).2 (eigenBasis y i)
  change 0 ≤ inner ℝ (gramOperator y (eigenBasis y i)) (eigenBasis y i) at h
  have he := (gram_positive y).1.apply_eigenvectorBasis finrank_euclideanSpace i
  change gramOperator y (eigenBasis y i) = eigenvalue y i • eigenBasis y i at he
  rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq,
    (eigenBasis y).orthonormal.1 i] at h
  simpa using h

def truncatedQuadratic (y : ι → H) (r : ℕ) (w : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i : Fin (Fintype.card ι), if i.val < r then
    eigenvalue y i * inner ℝ (eigenBasis y i) w ^ 2 else 0

def tailEigenvalue (y : ι → H) (r : ℕ) : ℝ :=
  if hr : r < Fintype.card ι then eigenvalue y ⟨r, hr⟩ else 0

theorem tail_nonneg (y : ι → H) (r : ℕ) : 0 ≤ tailEigenvalue y r := by
  unfold tailEigenvalue
  split_ifs
  · exact eigenvalue_nonneg y _
  · exact le_rfl

theorem quadratic_eigen_expansion (y : ι → H) (w : EuclideanSpace ℝ ι) :
    inner ℝ w (gramOperator y w) =
      ∑ i : Fin (Fintype.card ι), eigenvalue y i * inner ℝ (eigenBasis y i) w ^ 2 := by
  rw [← (eigenBasis y).sum_inner_mul_inner w (gramOperator y w)]
  apply Finset.sum_congr rfl
  intro i _
  have hi := (gram_positive y).1.eigenvectorBasis_apply_self_apply finrank_euclideanSpace w i
  change (eigenBasis y).repr (gramOperator y w) i =
    eigenvalue y i * (eigenBasis y).repr w i at hi
  rw [(eigenBasis y).repr_apply_apply, (eigenBasis y).repr_apply_apply] at hi
  rw [hi, real_inner_comm w]
  ring

/-- A genuine residual Rayleigh bound, for the sorted spectral truncation of
the actual response Gram operator. The `r ≥ n` tail is exactly zero. -/
theorem spectral_error_bound (y : ι → H) (r : ℕ) (w : EuclideanSpace ℝ ι) :
    0 ≤ inner ℝ w (gramOperator y w) - truncatedQuadratic y r w ∧
      inner ℝ w (gramOperator y w) - truncatedQuadratic y r w ≤
        tailEigenvalue y r * ‖w‖ ^ 2 := by
  rw [quadratic_eigen_expansion, truncatedQuadratic, ← Finset.sum_sub_distrib]
  have hterm (i : Fin (Fintype.card ι)) :
      eigenvalue y i * inner ℝ (eigenBasis y i) w ^ 2 -
        (if i.val < r then eigenvalue y i * inner ℝ (eigenBasis y i) w ^ 2 else 0) =
      if i.val < r then 0 else eigenvalue y i * inner ℝ (eigenBasis y i) w ^ 2 := by
    split_ifs <;> ring
  simp_rw [hterm]
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (eigenvalue_nonneg y i) (sq_nonneg _)
  · calc
      _ ≤ ∑ i : Fin (Fintype.card ι), tailEigenvalue y r * inner ℝ (eigenBasis y i) w ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact mul_nonneg (tail_nonneg y r) (sq_nonneg _)
        · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          have hr : r < Fintype.card ι := lt_of_le_of_lt (Nat.le_of_not_gt hi) i.isLt
          rw [tailEigenvalue, dif_pos hr]
          exact eigenvalue_antitone y (show (⟨r, hr⟩ : Fin _) ≤ i from Nat.le_of_not_gt hi)
      _ = _ := by rw [← Finset.mul_sum, (eigenBasis y).sum_sq_inner_right]

def contrast (s t : Finset ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ (if i ∈ s then (s.card : ℝ)⁻¹ else 0) -
    (if i ∈ t then (t.card : ℝ)⁻¹ else 0))

def splitScale (s t : Finset ι) : ℝ :=
  Real.sqrt ((s.card : ℝ) * t.card) / (s ∪ t).card

def splitWeights (s t : Finset ι) : EuclideanSpace ℝ ι := splitScale s t • contrast s t

theorem contrast_norm_sq (s t : Finset ι) (hd : Disjoint s t) :
    ‖contrast s t‖ ^ 2 = (s.card : ℝ) * (s.card : ℝ)⁻¹ ^ 2 +
      (t.card : ℝ) * (t.card : ℝ)⁻¹ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hp (i : ι) :
      ((if i ∈ s then (s.card : ℝ)⁻¹ else 0) -
        (if i ∈ t then (t.card : ℝ)⁻¹ else 0)) ^ 2 =
      (if i ∈ s then (s.card : ℝ)⁻¹ ^ 2 else 0) +
        (if i ∈ t then (t.card : ℝ)⁻¹ ^ 2 else 0) := by
    by_cases hs : i ∈ s
    · have ht : i ∉ t := fun ht ↦ Finset.disjoint_left.mp hd hs ht
      simp [hs, ht]
    · by_cases ht : i ∈ t <;> simp [hs, ht]
  change (∑ i, ((if i ∈ s then (s.card : ℝ)⁻¹ else 0) -
    (if i ∈ t then (t.card : ℝ)⁻¹ else 0)) ^ 2) = _
  simp_rw [hp]
  simp [Finset.sum_add_distrib]

theorem splitWeights_norm_sq (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : Disjoint s t) : ‖splitWeights s t‖ ^ 2 = ((s ∪ t).card : ℝ)⁻¹ := by
  have ha : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hb : (t.card : ℝ) ≠ 0 := by exact_mod_cast ht.card_ne_zero
  have hab : ((s ∪ t).card : ℝ) = s.card + t.card := by
    exact_mod_cast Finset.card_union_of_disjoint hd
  have hn : ((s ∪ t).card : ℝ) ≠ 0 := by positivity
  rw [splitWeights, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    contrast_norm_sq s t hd, splitScale, div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  nlinarith [hab]

theorem weighted_response (s t : Finset ι) (y : ι → H) :
    (∑ i, splitWeights s t i • y i) =
      splitScale s t • (EmpiricalGeometry.cellMean s y - EmpiricalGeometry.cellMean t y) := by
  change (∑ i, (splitScale s t * ((if i ∈ s then (s.card : ℝ)⁻¹ else 0) -
    (if i ∈ t then (t.card : ℝ)⁻¹ else 0))) • y i) = _
  simp only [SemigroupAction.mul_smul, sub_smul]
  simp [EmpiricalGeometry.cellMean, smul_sub, Finset.smul_sum]

theorem quadratic_eq_impurityGain (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : Disjoint s t) (y : ι → H) :
    inner ℝ (splitWeights s t) (gramOperator y (splitWeights s t)) = impurityGain s t y := by
  have he := Matrix.star_dotProduct_gram_mulVec y (splitWeights s t) (splitWeights s t)
  have he' : inner ℝ (splitWeights s t) (gramOperator y (splitWeights s t)) =
      ‖∑ i, splitWeights s t i • y i‖ ^ 2 := by
    change ((Matrix.gram ℝ y) *ᵥ (fun i ↦ splitWeights s t i)) ⬝ᵥ
      (fun i ↦ splitWeights s t i) = _
    rw [dotProduct_comm]
    simpa only [star_trivial, real_inner_self_eq_norm_sq] using he
  rw [he', weighted_response, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    splitScale, div_pow, Real.sq_sqrt (by positivity),
    impurityGain_eq_mean_distance s t hs ht hd y]

/-- The retained largest-eigenvalue surrogate's gain, in its exact quadratic
form with the source's actual contrast vector. -/
def truncatedSplitGain (y : ι → H) (r : ℕ) (s t : Finset ι) : ℝ :=
  truncatedQuadratic y r (splitWeights s t)

/-- Original label: `prop:gram-split-gain-bound`.
The actual spectral residual is nonnegative and bounded by the first omitted
eigenvalue divided by the parent cell size. Rank at least n has zero error. -/
theorem splitGain_spectral_bound (y : ι → H) (r : ℕ) (s t : Finset ι)
    (hs : s.Nonempty) (ht : t.Nonempty) (hd : Disjoint s t) :
    0 ≤ impurityGain s t y - truncatedSplitGain y r s t ∧
      impurityGain s t y - truncatedSplitGain y r s t ≤ tailEigenvalue y r / (s ∪ t).card := by
  have h := spectral_error_bound y r (splitWeights s t)
  rw [quadratic_eq_impurityGain s t hs ht hd y, splitWeights_norm_sq s t hs ht hd] at h
  simpa only [truncatedSplitGain, div_eq_mul_inv] using h

/-- The columns of the retained square-root spectral factor. Keeping zero
coordinates for omitted directions has exactly the same Gram matrix as the
source's r-row factor. -/
def spectralVectors (y : ι → H) (r : ℕ) (i : ι) :
    EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
  WithLp.toLp 2 (fun k ↦ if k.val < r then Real.sqrt (eigenvalue y k) * eigenBasis y k i else 0)

theorem spectralVectors_gram (y : ι → H) (r : ℕ) (i j : ι) :
    inner ℝ (spectralVectors y r i) (spectralVectors y r j) =
      ∑ k : Fin (Fintype.card ι), if k.val < r then
        eigenvalue y k * eigenBasis y k i * eigenBasis y k j else 0 := by
  change (∑ k, (if k.val < r then Real.sqrt (eigenvalue y k) * eigenBasis y k j else 0) *
    (if k.val < r then Real.sqrt (eigenvalue y k) * eigenBasis y k i else 0)) = _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · calc
      _ = Real.sqrt (eigenvalue y k) ^ 2 * eigenBasis y k i * eigenBasis y k j := by ring
      _ = _ := by rw [Real.sq_sqrt (eigenvalue_nonneg y k)]
  · ring

theorem spectralVectors_weighted_norm (y : ι → H) (r : ℕ) (w : EuclideanSpace ℝ ι) :
    ‖∑ i, w i • spectralVectors y r i‖ ^ 2 = truncatedQuadratic y r w := by
  have hc (k : Fin (Fintype.card ι)) :
      (∑ i, w i • spectralVectors y r i) k =
        if k.val < r then Real.sqrt (eigenvalue y k) * inner ℝ (eigenBasis y k) w else 0 := by
    change (PiLp.projₗ 2 (fun _ : Fin (Fintype.card ι) ↦ ℝ) k :
      EuclideanSpace ℝ (Fin (Fintype.card ι)) →ₗ[ℝ] ℝ)
      (∑ i, w i • spectralVectors y r i) = _
    rw [map_sum]
    simp only [PiLp.projₗ_apply, PiLp.smul_apply, smul_eq_mul]
    change (∑ i, w i * (if k.val < r then Real.sqrt (eigenvalue y k) * eigenBasis y k i else 0)) = _
    by_cases hk : k.val < r
    · simp only [if_pos hk]
      change (∑ i, w i * (Real.sqrt (eigenvalue y k) * eigenBasis y k i)) =
        Real.sqrt (eigenvalue y k) * ∑ i, w i * eigenBasis y k i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp [hk]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hc]
  unfold truncatedQuadratic
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · rw [mul_pow, Real.sq_sqrt (eigenvalue_nonneg y k)]
  · ring

theorem weighted_norm_eq_gain (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : Disjoint s t) (y : ι → H) :
    ‖∑ i, splitWeights s t i • y i‖ ^ 2 = impurityGain s t y := by
  rw [weighted_response, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    splitScale, div_pow, Real.sq_sqrt (by positivity),
    impurityGain_eq_mean_distance s t hs ht hd y]

/-- The surrogate gain in the bound is exactly the tree gain of the
square-root factor columns whose Gram matrix is U_r Λ_r U_rᵀ. -/
theorem truncatedSplitGain_eq_factor_gain (y : ι → H) (r : ℕ) (s t : Finset ι)
    (hs : s.Nonempty) (ht : t.Nonempty) (hd : Disjoint s t) :
    truncatedSplitGain y r s t = impurityGain s t (spectralVectors y r) := by
  rw [← weighted_norm_eq_gain s t hs ht hd (spectralVectors y r), spectralVectors_weighted_norm]
  rfl

end Thesis.DayAhead.SpectralSplitBound
