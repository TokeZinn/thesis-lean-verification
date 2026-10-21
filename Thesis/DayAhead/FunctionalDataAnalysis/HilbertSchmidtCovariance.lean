import Thesis.DayAhead.FunctionalDataAnalysis.LimitTheorems
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Hilbert--Schmidt coordinates for covariance operators

Mathlib does not currently bundle the infinite-dimensional Hilbert--Schmidt
operator ideal.  For the covariance strong law used in the thesis, it is
enough to work in the isometric coordinate model `ℓ²(ι × ι, ℝ)` associated
with a fixed countable Hilbert basis.  Rank-one operators then become outer
products of square-summable coefficient sequences.
-/

namespace Thesis
namespace DayAhead
namespace HilbertSchmidtCovariance

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

universe u v

/-- Square-summable real matrices, used as the coordinate model for
Hilbert--Schmidt operators. -/
abbrev HilbertSchmidtCoordinatesOn (ι : Type*) :=
  lp (fun _ : ι × ι ↦ ℝ) 2

/-- Compatibility name for the natural-number coordinate model. -/
abbrev HilbertSchmidtCoordinates := HilbertSchmidtCoordinatesOn ℕ

variable {ι : Type*}

/-- Coordinates of the rank-one operator `u ⊗ v` in a Hilbert basis.  The
index order matches
`inner (b i) ((u ⊗ v) (b j)) = inner (b i) v * inner (b j) u`. -/
noncomputable def tensorCoordinates
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (u v : H) : (HilbertSchmidtCoordinatesOn ι) := by
  let cu : lp (fun _ : ι ↦ ℝ) 2 := b.repr u
  let cv : lp (fun _ : ι ↦ ℝ) 2 := b.repr v
  refine ⟨fun ij ↦ cv ij.1 * cu ij.2, ?_⟩
  apply memℓp_gen
  have hcu : Summable (fun i ↦ ‖cu i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp cu).summable (by norm_num)
  have hcv : Summable (fun i ↦ ‖cv i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp cv).summable (by norm_num)
  have hprod := hcv.mul_of_nonneg hcu
    (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  convert hprod using 1
  funext ij
  norm_num [norm_mul, mul_pow]

@[simp]
theorem tensorCoordinates_apply
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (u v : H) (ij : ι × ι) :
    tensorCoordinates b u v ij =
      b.repr v ij.1 * b.repr u ij.2 :=
  rfl

theorem summable_basisCoefficient_norm_sq
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (x : H) :
    Summable (fun i ↦ ‖b.repr x i‖ ^ 2) := by
  have h := (lp.memℓp (b.repr x)).summable (by norm_num)
  simpa using h

theorem tsum_basisCoefficient_norm_sq
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (x : H) :
    ∑' i, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (b.repr x)
  norm_num at h
  calc
    (∑' i, ‖b.repr x i‖ ^ 2) =
        ∑' i, (b.repr x i) ^ 2 := by
          apply tsum_congr
          intro i
          rw [Real.norm_eq_abs, sq_abs]
    _ = ‖x‖ ^ 2 := h.symm

/-- The coordinate norm of a rank-one operator is the product of the two
vector norms. -/
theorem norm_tensorCoordinates
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (u v : H) :
    ‖tensorCoordinates b u v‖ = ‖u‖ * ‖v‖ := by
  have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (tensorCoordinates b u v)
  norm_num at hnorm
  have hu := summable_basisCoefficient_norm_sq b u
  have hv := summable_basisCoefficient_norm_sq b v
  have hprod : Summable (fun ij : ι × ι ↦
      ‖b.repr v ij.1‖ ^ 2 * ‖b.repr u ij.2‖ ^ 2) :=
    hv.mul_of_nonneg hu (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  have htsum := hv.tsum_mul_tsum hu hprod
  rw [tsum_basisCoefficient_norm_sq b v,
    tsum_basisCoefficient_norm_sq b u] at htsum
  have hcoord : (∑' ij : ι × ι,
      ‖tensorCoordinates b u v ij‖ ^ 2) =
      ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
    calc
      (∑' ij : ι × ι, ‖tensorCoordinates b u v ij‖ ^ 2) =
          ∑' ij : ι × ι,
            ‖b.repr v ij.1‖ ^ 2 * ‖b.repr u ij.2‖ ^ 2 := by
              apply tsum_congr
              intro ij
              simp only [tensorCoordinates_apply, norm_mul, mul_pow]
      _ = ‖v‖ ^ 2 * ‖u‖ ^ 2 := htsum.symm
  have hcoord' : (∑' ij : ι × ι,
      (|b.repr v ij.1| * |b.repr u ij.2|) ^ 2) =
      ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
    simpa only [tensorCoordinates_apply, Real.norm_eq_abs, norm_mul]
      using hcoord
  rw [hcoord'] at hnorm
  apply (sq_eq_sq₀ (norm_nonneg (tensorCoordinates b u v))
    (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mp
  calc
    ‖tensorCoordinates b u v‖ ^ 2 =
        ‖v‖ ^ 2 * ‖u‖ ^ 2 := hnorm
    _ = (‖u‖ * ‖v‖) ^ 2 := by ring

theorem tensorCoordinates_add_left
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (u₁ u₂ v : H) :
    tensorCoordinates b (u₁ + u₂) v =
      tensorCoordinates b u₁ v + tensorCoordinates b u₂ v := by
  apply lp.ext
  funext ij
  simp only [tensorCoordinates_apply, map_add, lp.coeFn_add, Pi.add_apply]
  ring

theorem tensorCoordinates_smul_left
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (a : ℝ) (u v : H) :
    tensorCoordinates b (a • u) v = a • tensorCoordinates b u v := by
  apply lp.ext
  funext ij
  simp only [tensorCoordinates_apply, map_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem tensorCoordinates_add_right
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (u v₁ v₂ : H) :
    tensorCoordinates b u (v₁ + v₂) =
      tensorCoordinates b u v₁ + tensorCoordinates b u v₂ := by
  apply lp.ext
  funext ij
  simp only [tensorCoordinates_apply, map_add, lp.coeFn_add, Pi.add_apply]
  ring

theorem tensorCoordinates_smul_right
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (a : ℝ) (u v : H) :
    tensorCoordinates b u (a • v) = a • tensorCoordinates b u v := by
  apply lp.ext
  funext ij
  simp only [tensorCoordinates_apply, map_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The rank-one coordinate construction as a continuous bilinear map. -/
noncomputable def tensorCoordinatesBilinear
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) :
    H →L[ℝ] H →L[ℝ] (HilbertSchmidtCoordinatesOn ι) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (tensorCoordinates b)
      (tensorCoordinates_add_left b)
      (tensorCoordinates_smul_left b)
      (tensorCoordinates_add_right b)
      (tensorCoordinates_smul_right b))
    1 (fun u v ↦ by
      simp only [LinearMap.mk₂_apply, norm_tensorCoordinates, one_mul]
      exact le_rfl)

@[simp]
theorem tensorCoordinatesBilinear_apply
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (u v : H) :
    tensorCoordinatesBilinear b u v = tensorCoordinates b u v := by
  rfl

/-- Coordinates of `x ⊗ x`. -/
noncomputable def rankOneCoordinates
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (x : H) : (HilbertSchmidtCoordinatesOn ι) :=
  tensorCoordinates b x x

theorem norm_rankOneCoordinates
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (x : H) :
    ‖rankOneCoordinates b x‖ = ‖x‖ ^ 2 := by
  rw [rankOneCoordinates, norm_tensorCoordinates, pow_two]

theorem continuous_rankOneCoordinates
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) :
    Continuous (rankOneCoordinates b) := by
  change Continuous (fun x : H ↦ tensorCoordinatesBilinear b x x)
  fun_prop

/-- The coordinate tensor of two square-integrable Hilbert-valued random
elements is Bochner integrable in `ℓ²(ι×ι)`. -/
theorem integrable_tensorCoordinates_of_memLp_two
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) (b : HilbertBasis ι ℝ H)
    (X Y : Ω → H) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω ↦ tensorCoordinates b (X ω) (Y ω)) μ := by
  have hcontinuous : Continuous
      (fun p : H × H ↦ tensorCoordinatesBilinear b p.1 p.2) := by
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun ω ↦ tensorCoordinates b (X ω) (Y ω)) μ := by
    simpa only [tensorCoordinatesBilinear_apply] using
      hcontinuous.comp_aestronglyMeasurable (hX.1.prodMk hY.1)
  have hnormProduct : Integrable
      (fun ω ↦ ‖X ω‖ * ‖Y ω‖) μ := by
    simpa only [Pi.mul_apply] using hX.norm.integrable_mul hY.norm
  refine hnormProduct.mono' hmeas ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [norm_tensorCoordinates]

theorem integrable_rankOneCoordinates_of_memLp_two
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) (b : HilbertBasis ι ℝ H)
    (X : Ω → H) (hX : MemLp X 2 μ) :
    Integrable (fun ω ↦ rankOneCoordinates b (X ω)) μ := by
  have hmeas : AEStronglyMeasurable
      (fun ω ↦ rankOneCoordinates b (X ω)) μ :=
    (continuous_rankOneCoordinates b).comp_aestronglyMeasurable hX.1
  refine (hX.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mono'
    hmeas ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [norm_rankOneCoordinates]

/-- Centred cross-covariance represented as a square-summable matrix of basis
coefficients. -/
noncomputable def crossCovarianceCoordinates
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (b : HilbertBasis ι ℝ H) (X Y : Ω → H) :
    (HilbertSchmidtCoordinatesOn ι) :=
  ∫ ω, tensorCoordinates b
    (X ω - FunctionalData.hilbertExpectation μ X)
    (Y ω - FunctionalData.hilbertExpectation μ Y) ∂μ

/--
Thesis source: analytic Hilbert--Schmidt clause used by Proposition
`prop:weak-stationarity` in
`2 - day-ahead/3_functional_data_analysis.tex`.

Original label: `prop:weak-stationarity`.

Square-integrability of the two random elements makes their centred
cross-covariance integrable in Hilbert--Schmidt coordinates.  In particular,
the operator-valued lag covariance invoked in the manuscript has a
square-summable matrix, rather than merely coordinatewise finite entries.
-/
theorem integrable_centered_tensorCoordinates_of_memLp_two
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (b : HilbertBasis ι ℝ H) (X Y : Ω → H)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω ↦ tensorCoordinates b
      (X ω - FunctionalData.hilbertExpectation μ X)
      (Y ω - FunctionalData.hilbertExpectation μ Y)) μ := by
  have hXcentered : MemLp
      (fun ω ↦ X ω - FunctionalData.hilbertExpectation μ X) 2 μ := by
    simpa only [Pi.sub_apply] using
      hX.sub (memLp_const (FunctionalData.hilbertExpectation μ X))
  have hYcentered : MemLp
      (fun ω ↦ Y ω - FunctionalData.hilbertExpectation μ Y) 2 μ := by
    simpa only [Pi.sub_apply] using
      hY.sub (memLp_const (FunctionalData.hilbertExpectation μ Y))
  exact integrable_tensorCoordinates_of_memLp_two μ b _ _
    hXcentered hYcentered

/-- Empirical raw second-moment coordinates. -/
noncomputable def rawSecondMomentCoordinates
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H)
    (n : ℕ) (ω : Ω) : (HilbertSchmidtCoordinatesOn ι) :=
  (n : ℝ)⁻¹ •
    ∑ i ∈ Finset.range n, rankOneCoordinates b (X i ω)

/-- The raw rank-one second moment satisfies the Banach-valued strong law in
the Hilbert--Schmidt coordinate space under only a second moment of `X`. -/
theorem rawSecondMomentCoordinates_strong_law_ae
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) (b : HilbertBasis ι ℝ H)
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ rawSecondMomentCoordinates b X n ω) atTop
      (𝓝 (∫ ω, rankOneCoordinates b (X 0 ω) ∂μ)) := by
  letI : MeasurableSpace (HilbertSchmidtCoordinatesOn ι) :=
    borel (HilbertSchmidtCoordinatesOn ι)
  letI : BorelSpace (HilbertSchmidtCoordinatesOn ι) := ⟨rfl⟩
  let Y : ℕ → Ω → (HilbertSchmidtCoordinatesOn ι) :=
    fun i ω ↦ rankOneCoordinates b (X i ω)
  have hYint : Integrable (Y 0) μ := by
    simpa only [Y] using
      integrable_rankOneCoordinates_of_memLp_two μ b (X 0) hX
  have hmap : Measurable (rankOneCoordinates b) :=
    (continuous_rankOneCoordinates b).measurable
  have hindepY : iIndepFun Y μ := by
    change iIndepFun (fun i ↦ rankOneCoordinates b ∘ X i) μ
    exact hindep.comp (fun _ ↦ rankOneCoordinates b) (fun _ ↦ hmap)
  have hpairY : Pairwise fun i j ↦ Y i ⟂ᵢ[μ] Y j :=
    fun i j hij ↦ hindepY.indepFun hij
  have hidentY : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := by
    intro i
    change IdentDistrib (rankOneCoordinates b ∘ X i)
      (rankOneCoordinates b ∘ X 0) μ μ
    exact (hident i).comp hmap
  simpa only [rawSecondMomentCoordinates, Y] using
    ProbabilityTheory.strong_law_ae Y hYint hpairY hidentY

/-- Population covariance represented in Hilbert--Schmidt coordinates as raw
second moment minus the rank-one mean correction. -/
noncomputable def covarianceCoordinates
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (b : HilbertBasis ι ℝ H) (X : Ω → H) :
    (HilbertSchmidtCoordinatesOn ι) :=
  (∫ ω, rankOneCoordinates b (X ω) ∂μ) -
    rankOneCoordinates b (FunctionalData.hilbertExpectation μ X)

/-- Biased empirical covariance in Hilbert--Schmidt coordinates. -/
noncomputable def biasedCovarianceCoordinates
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H)
    (n : ℕ) (ω : Ω) : (HilbertSchmidtCoordinatesOn ι) :=
  rawSecondMomentCoordinates b X n ω -
    rankOneCoordinates b (LimitTheorems.empiricalMean X n ω)

/-- The biased covariance coordinates converge almost surely in their
`ℓ²(ι×ι)` norm. -/
theorem biasedCovarianceCoordinates_strong_law_ae
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H)
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ biasedCovarianceCoordinates b X n ω) atTop
      (𝓝 (covarianceCoordinates μ b (X 0))) := by
  have hpair : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j :=
    fun i j hij ↦ hindep.indepFun hij
  have hmeanLaw : ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ LimitTheorems.empiricalMean X n ω) atTop
      (𝓝 (FunctionalData.hilbertExpectation μ (X 0))) := by
    simpa only [LimitTheorems.empiricalMean] using
      LimitTheorems.hilbert_strong_law_ae X
        (hX.integrable (by norm_num)) hpair hident
  filter_upwards
    [rawSecondMomentCoordinates_strong_law_ae μ b X hX hindep hident,
      hmeanLaw] with ω hraw hmean
  have hrankOne : Tendsto
      (fun n ↦ rankOneCoordinates b
        (LimitTheorems.empiricalMean X n ω))
      atTop
      (𝓝 (rankOneCoordinates b
        (FunctionalData.hilbertExpectation μ (X 0)))) :=
    ((continuous_rankOneCoordinates b).tendsto
      (FunctionalData.hilbertExpectation μ (X 0))).comp hmean
  simpa only [biasedCovarianceCoordinates, covarianceCoordinates] using
    hraw.sub hrankOne

/-- The thesis's unbiased covariance estimator in Hilbert--Schmidt
coordinates. -/
noncomputable def sampleCovarianceCoordinates
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H)
    (n : ℕ) (ω : Ω) : (HilbertSchmidtCoordinatesOn ι) :=
  (((n - 1 : ℕ) : ℝ)⁻¹) •
    ∑ i ∈ Finset.range n,
      rankOneCoordinates b
        (X i ω - LimitTheorems.empiricalMean X n ω)

/-- A tensor coordinate is the corresponding matrix coefficient of the
rank-one continuous operator. -/
theorem tensorCoordinates_eq_matrixCoefficient
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (u v : H) (i j : ι) :
    tensorCoordinates b u v (i, j) =
      inner ℝ (b i) (FunctionalData.tensorProduct u v (b j)) := by
  rw [tensorCoordinates_apply, b.repr_apply_apply, b.repr_apply_apply,
    FunctionalData.tensorProduct_apply, real_inner_smul_right]
  rw [real_inner_comm u (b j)]
  ring

theorem rankOneCoordinates_eq_matrixCoefficient
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (x : H) (i j : ι) :
    rankOneCoordinates b x (i, j) =
      inner ℝ (b i) (FunctionalData.tensorProduct x x (b j)) := by
  exact tensorCoordinates_eq_matrixCoefficient b x x i j

theorem sampleCovarianceCoordinates_apply_eq_matrixCoefficient
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H)
    (n : ℕ) (ω : Ω) (i j : ι) :
    sampleCovarianceCoordinates b X n ω (i, j) =
      inner ℝ (b i) (LimitTheorems.sampleCovariance X n ω (b j)) := by
  simp only [sampleCovarianceCoordinates, LimitTheorems.sampleCovariance,
    lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum, Finset.sum_apply,
    smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, inner_sum, real_inner_smul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact rankOneCoordinates_eq_matrixCoefficient b
    (X k ω - LimitTheorems.empiricalMean X n ω) i j

theorem rawSecondMomentCoordinates_apply_eq_matrixCoefficient
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H)
    (n : ℕ) (ω : Ω) (i j : ι) :
    rawSecondMomentCoordinates b X n ω (i, j) =
      inner ℝ (b i) (LimitTheorems.rawSecondMomentOperator X n ω (b j)) := by
  simp only [rawSecondMomentCoordinates, LimitTheorems.rawSecondMomentOperator,
    lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum, Finset.sum_apply,
    smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, inner_sum, real_inner_smul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact rankOneCoordinates_eq_matrixCoefficient b (X k ω) i j

theorem biasedCovarianceCoordinates_apply_eq_matrixCoefficient
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H)
    (n : ℕ) (ω : Ω) (i j : ι) :
    biasedCovarianceCoordinates b X n ω (i, j) =
      inner ℝ (b i)
        (LimitTheorems.biasedCovarianceOperator X n ω (b j)) := by
  rw [biasedCovarianceCoordinates, LimitTheorems.biasedCovarianceOperator]
  simp only [lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
    inner_sub_right]
  rw [rawSecondMomentCoordinates_apply_eq_matrixCoefficient,
    rankOneCoordinates_eq_matrixCoefficient]

/-- The same exact `n/(n-1)` correction identity holds in Hilbert--Schmidt
coordinates. -/
theorem sampleCovarianceCoordinates_eq_unbiasedFactor_smul_biased
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H)
    (n : ℕ) (ω : Ω) (hn : 0 < n) :
    sampleCovarianceCoordinates b X n ω =
      ((n : ℝ) * (((n - 1 : ℕ) : ℝ)⁻¹)) •
        biasedCovarianceCoordinates b X n ω := by
  apply lp.ext
  funext ij
  rcases ij with ⟨i, j⟩
  rw [sampleCovarianceCoordinates_apply_eq_matrixCoefficient]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [biasedCovarianceCoordinates_apply_eq_matrixCoefficient,
    LimitTheorems.sampleCovariance_eq_unbiasedFactor_smul_biased
      X n ω hn]
  simp only [ContinuousLinearMap.smul_apply, real_inner_smul_right]

/-- The exact unbiased covariance estimator converges almost surely in the
`ℓ²(ι×ι)` Hilbert--Schmidt coordinate norm. -/
theorem sampleCovarianceCoordinates_strong_law_ae
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H)
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k ↦ sampleCovarianceCoordinates b X (k + 2) ω)
      atTop (𝓝 (covarianceCoordinates μ b (X 0))) := by
  filter_upwards
    [biasedCovarianceCoordinates_strong_law_ae
      μ b X hX hindep hident] with ω hω
  have hshift : Tendsto (fun k : ℕ ↦ k + 2) atTop atTop :=
    tendsto_add_atTop_nat 2
  have hproduct := LimitTheorems.unbiasedFactor_tendsto_one.smul
    (hω.comp hshift)
  have hproduct' : Tendsto
      (fun k : ℕ ↦
        (((k + 2 : ℕ) : ℝ) *
          (((k + 2 - 1 : ℕ) : ℝ)⁻¹)) •
          biasedCovarianceCoordinates b X (k + 2) ω)
      atTop (𝓝 (covarianceCoordinates μ b (X 0))) := by
    simpa only [one_smul] using hproduct
  refine hproduct'.congr'
    (Filter.Eventually.of_forall fun k ↦ ?_)
  exact (sampleCovarianceCoordinates_eq_unbiasedFactor_smul_biased
    b X (k + 2) ω (by omega)).symm

/-- The population coordinate object is exactly the matrix of the population
covariance operator in the chosen Hilbert basis. -/
theorem covarianceCoordinates_apply_eq_matrixCoefficient
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) (X : Ω → H)
    (hX : MemLp X 2 μ) (i j : ι) :
    covarianceCoordinates μ b X (i, j) =
      inner ℝ (b i) (FunctionalData.covarianceOperator μ X (b j)) := by
  have hcoordInt : Integrable (fun ω ↦ rankOneCoordinates b (X ω)) μ :=
    integrable_rankOneCoordinates_of_memLp_two μ b X hX
  have hopInt : Integrable
      (fun ω ↦ FunctionalData.tensorProduct (X ω) (X ω)) μ :=
    Covariance.integrable_tensorProduct_self_of_memLp_two μ X hX
  let eval : (HilbertSchmidtCoordinatesOn ι) →L[ℝ] ℝ :=
    lp.evalCLM ℝ (fun _ : ι × ι ↦ ℝ) 2 (i, j)
  have hevalIntegral :
      (∫ ω, rankOneCoordinates b (X ω) ∂μ) (i, j) =
        ∫ ω, rankOneCoordinates b (X ω) (i, j) ∂μ := by
    have hcomm := eval.integral_comp_comm hcoordInt
    exact hcomm.symm
  rw [covarianceCoordinates, lp.coeFn_sub, Pi.sub_apply,
    Covariance.covarianceOperator_eq_rawSecondMoment_sub_mean μ X hX,
    ContinuousLinearMap.sub_apply, inner_sub_right]
  rw [hevalIntegral, rankOneCoordinates_eq_matrixCoefficient]
  congr 1
  rw [ContinuousLinearMap.integral_apply hopInt (b j)]
  have hopApplyInt : Integrable
      (fun ω ↦ FunctionalData.tensorProduct (X ω) (X ω) (b j)) μ :=
    ((ContinuousLinearMap.apply ℝ H) (b j)).integrable_comp hopInt
  rw [← integral_inner hopApplyInt (b i)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦
    rankOneCoordinates_eq_matrixCoefficient b (X ω) i j

/-- Coordinate differences agree pointwise with the matrix coefficients of
the corresponding operator difference. -/
theorem sampleCovarianceCoordinates_sub_covariance_apply
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H)
    (hX : MemLp (X 0) 2 μ) (n : ℕ) (ω : Ω) (i j : ι) :
    (sampleCovarianceCoordinates b X n ω -
      covarianceCoordinates μ b (X 0)) (i, j) =
      inner ℝ (b i)
        ((LimitTheorems.sampleCovariance X n ω -
          FunctionalData.covarianceOperator μ (X 0)) (b j)) := by
  rw [lp.coeFn_sub, Pi.sub_apply,
    sampleCovarianceCoordinates_apply_eq_matrixCoefficient,
    covarianceCoordinates_apply_eq_matrixCoefficient μ b (X 0) hX,
    ContinuousLinearMap.sub_apply, inner_sub_right]

/-- Any bounded operator whose matrix coefficients are represented by an
`ℓ²(ι×ι)` element has extended Hilbert--Schmidt norm equal to the
ordinary norm of that coordinate element. -/
theorem hilbertSchmidtENorm_eq_of_coordinates
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H)
    (C : (HilbertSchmidtCoordinatesOn ι))
    (hC : ∀ i j, C (i, j) = inner ℝ (b i) (A (b j))) :
    LimitTheorems.hilbertSchmidtENorm b A = ENNReal.ofReal ‖C‖ := by
  have hCsummable : Summable (fun ij : ι × ι ↦ ‖C ij‖ ^ 2) := by
    have h := (lp.memℓp C).summable (by norm_num)
    simpa using h
  have hcolumnSummable (j : ι) :
      Summable (fun i : ι ↦ ‖C (i, j)‖ ^ 2) := by
    simpa using hCsummable.comp_injective
      (fun i₁ i₂ h ↦ congrArg Prod.fst h)
  have hcolumn (j : ι) :
      (∑' i : ι, ‖C (i, j)‖ ^ 2) = ‖A (b j)‖ ^ 2 := by
    calc
      (∑' i : ι, ‖C (i, j)‖ ^ 2) =
          ∑' i : ι, ‖b.repr (A (b j)) i‖ ^ 2 := by
            apply tsum_congr
            intro i
            rw [hC i j, b.repr_apply_apply]
      _ = ‖A (b j)‖ ^ 2 := tsum_basisCoefficient_norm_sq b (A (b j))
  have hnormTsum :
      (∑' ij : ι × ι, ‖C ij‖ ^ 2) = ‖C‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) C
    norm_num at h
    calc
      (∑' ij : ι × ι, ‖C ij‖ ^ 2) =
          ∑' ij : ι × ι, (C ij) ^ 2 := by
            apply tsum_congr
            intro ij
            rw [Real.norm_eq_abs, sq_abs]
      _ = ‖C‖ ^ 2 := h.symm
  have hsum :
      (∑' j : ι, ENNReal.ofReal (‖A (b j)‖ ^ 2)) =
        ENNReal.ofReal (‖C‖ ^ 2) := by
    calc
      (∑' j : ι, ENNReal.ofReal (‖A (b j)‖ ^ 2)) =
          ∑' j : ι, ENNReal.ofReal
            (∑' i : ι, ‖C (i, j)‖ ^ 2) := by
              apply tsum_congr
              intro j
              rw [hcolumn j]
      _ = ∑' j : ι, ∑' i : ι,
          ENNReal.ofReal (‖C (i, j)‖ ^ 2) := by
            apply tsum_congr
            intro j
            rw [ENNReal.ofReal_tsum_of_nonneg
              (fun _ ↦ sq_nonneg _) (hcolumnSummable j)]
      _ = ∑' i : ι, ∑' j : ι,
          ENNReal.ofReal (‖C (i, j)‖ ^ 2) := ENNReal.tsum_comm
      _ = ∑' ij : ι × ι, ENNReal.ofReal (‖C ij‖ ^ 2) := by
            rw [ENNReal.tsum_prod']
      _ = ENNReal.ofReal (∑' ij : ι × ι, ‖C ij‖ ^ 2) := by
            rw [ENNReal.ofReal_tsum_of_nonneg
              (fun _ ↦ sq_nonneg _) hCsummable]
      _ = ENNReal.ofReal (‖C‖ ^ 2) := by rw [hnormTsum]
  unfold LimitTheorems.hilbertSchmidtENorm
  rw [hsum, ENNReal.ofReal_pow (norm_nonneg C) 2]
  convert ENNReal.pow_rpow_inv_natCast
    (by norm_num : (2 : ℕ) ≠ 0) (ENNReal.ofReal ‖C‖) using 1
  all_goals norm_num

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Theorem `thm:lln-covariance`.

Original label: `thm:lln-covariance`.

The exact unbiased sample covariance converges almost surely to the population
covariance in Hilbert--Schmidt norm.  The proof realises rank-one operators in
the complete coordinate space `ℓ²(ι×ι)`, applies Mathlib's Banach-valued
strong law there, and then identifies the coordinate norm with the basis
definition of the extended Hilbert--Schmidt norm.
-/
theorem sampleCovariance_hilbertSchmidt_strong_law_ae
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H)
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k ↦ LimitTheorems.hilbertSchmidtENorm b
        (LimitTheorems.sampleCovariance X (k + 2) ω -
          FunctionalData.covarianceOperator μ (X 0)))
      atTop (𝓝 0) := by
  filter_upwards
    [sampleCovarianceCoordinates_strong_law_ae
      μ b X hX hindep hident] with ω hω
  have hdiff := hω.sub
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ covarianceCoordinates μ b (X 0))
      atTop (𝓝 (covarianceCoordinates μ b (X 0))))
  have hdiff0 : Tendsto
      (fun k ↦ sampleCovarianceCoordinates b X (k + 2) ω -
        covarianceCoordinates μ b (X 0))
      atTop (𝓝 0) := by
    simpa using hdiff
  have hnorm : Tendsto
      (fun k ↦ ‖sampleCovarianceCoordinates b X (k + 2) ω -
        covarianceCoordinates μ b (X 0)‖)
      atTop (𝓝 0) := by
    simpa using hdiff0.norm
  have henorm : Tendsto
      (fun k ↦ ENNReal.ofReal
        ‖sampleCovarianceCoordinates b X (k + 2) ω -
          covarianceCoordinates μ b (X 0)‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
  refine henorm.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
  symm
  apply hilbertSchmidtENorm_eq_of_coordinates b
    (LimitTheorems.sampleCovariance X (k + 2) ω -
      FunctionalData.covarianceOperator μ (X 0))
    (sampleCovarianceCoordinates b X (k + 2) ω -
      covarianceCoordinates μ b (X 0))
  intro i j
  exact sampleCovarianceCoordinates_sub_covariance_apply
    μ b X hX (k + 2) ω i j

end HilbertSchmidtCovariance
end DayAhead
end Thesis
