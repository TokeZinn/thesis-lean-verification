import Thesis.DayAhead.FunctionalDataAnalysis.Covariance
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.StrongLaw

/-!
# Day-ahead Hilbert-space limit theorems

The strong-law clause used by the thesis is available in Mathlib for
Banach-valued random variables. `DayAhead.HilbertCLT` proves the full
separable Hilbert-space central limit theorem from scalar CLTs and uniform
tightness, including identification of the Gaussian limit and its covariance.
-/

namespace Thesis
namespace DayAhead
namespace LimitTheorems

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

universe u v w

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`, strong-law clause of
Theorem `thm:lln-clt-mean`.

Original label: `thm:lln-clt-mean`.

Informal statement: empirical means of independent identically distributed
integrable Hilbert-valued random variables converge almost surely to the
Bochner expectation.

Lean strategy / thesis relation note: mathlib proves the stronger
Banach-valued result under pairwise independence.
-/
theorem hilbert_strong_law_ae
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    {μ : Measure Ω} (X : ℕ → Ω → H) (hX : Integrable (X 0) μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      atTop (𝓝 (FunctionalData.hilbertExpectation μ (X 0))) := by
  simpa only [FunctionalData.hilbertExpectation] using
    ProbabilityTheory.strong_law_ae X hX hindep hident

/-- Scalar projection along a fixed Hilbert-space direction. -/
def scalarProjection
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h x : H) : ℝ :=
  inner ℝ h x

/--
Thesis source: finite-dimensional marginal core of the central-limit clause of
Theorem `thm:lln-clt-mean` in
`2 - day-ahead/3_functional_data_analysis.tex`.

Original label: `thm:lln-clt-mean`.

Lean strategy / thesis relation note: every fixed scalar projection of the
normalised Hilbert-valued sum satisfies the ordinary real central limit
theorem. `DayAhead.HilbertCLTInfinite` combines these projections with
uniform tightness to construct the Gaussian limit in the whole space. -/
theorem scalarProjection_central_limit
    {Ω : Type u} {Ω' : Type w} {H : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h : H) (Y : Ω' → ℝ)
    (hY : HasLaw Y
      (gaussianReal 0
        Var[(fun ω => scalarProjection h (X 0 ω)); μ].toNNReal) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, scalarProjection h (X k ω) -
          n * μ[fun ω => scalarProjection h (X 0 ω)]))
      atTop Y (fun _ => μ) μ' := by
  let Z : ℕ → Ω → ℝ := fun i ω => scalarProjection h (X i ω)
  change HasLaw Y (gaussianReal 0 Var[Z 0; μ].toNNReal) μ' at hY
  have hproj : Measurable (scalarProjection h) := by
    change Measurable (fun x : H => inner ℝ h x)
    exact (continuous_const.inner continuous_id).measurable
  have hZ : MemLp (Z 0) 2 μ := by
    simpa only [Z, scalarProjection] using hX.const_inner h
  have hindepZ : iIndepFun Z μ := by
    change iIndepFun (fun i => scalarProjection h ∘ X i) μ
    exact hindep.comp (fun _ => scalarProjection h) (fun _ => hproj)
  have hidentZ : ∀ i, IdentDistrib (Z i) (Z 0) μ μ := by
    intro i
    change IdentDistrib (scalarProjection h ∘ X i)
      (scalarProjection h ∘ X 0) μ μ
    exact (hident i).comp hproj
  change TendstoInDistribution
    (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
      (∑ k ∈ Finset.range n, Z k ω - n * μ[Z 0]))
    atTop Y (fun _ => μ) μ'
  exact ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    hY hZ hindepZ hidentZ

/-- The preceding projection CLT with the identity random variable on the
canonical centred Gaussian law as its explicit limit. -/
theorem scalarProjection_central_limit_gaussianReal
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (h : H) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, scalarProjection h (X k ω) -
          n * μ[fun ω => scalarProjection h (X 0 ω)]))
      atTop id (fun _ => μ)
        (gaussianReal 0
          Var[(fun ω => scalarProjection h (X 0 ω)); μ].toNNReal) := by
  exact scalarProjection_central_limit μ
    (gaussianReal 0
      Var[(fun ω => scalarProjection h (X 0 ω)); μ].toNNReal)
    X hX hindep hident h id HasLaw.id

/-! ## Sample covariance -/

/-- Empirical raw rank-one second-moment operator. -/
noncomputable def rawSecondMomentOperator
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) : H →L[ℝ] H :=
  (n : ℝ)⁻¹ •
    ∑ i ∈ Finset.range n,
      FunctionalData.tensorProduct (X i ω) (X i ω)

/-- Biased empirical covariance of two fixed scalar projections. -/
noncomputable def scalarBiasedCovariance
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (h k : H) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n,
        scalarProjection h (X i ω) * scalarProjection k (X i ω) -
    ((n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, scalarProjection h (X i ω)) *
    ((n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, scalarProjection k (X i ω))

/-- Elementary centring identity for two finite scalar samples. -/
theorem sum_centered_mul_centered
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s,
        (a i - (s.card : ℝ)⁻¹ * ∑ j ∈ s, a j) *
          (b i - (s.card : ℝ)⁻¹ * ∑ j ∈ s, b j)) =
      (∑ i ∈ s, a i * b i) -
        (s.card : ℝ) *
          ((s.card : ℝ)⁻¹ * ∑ i ∈ s, a i) *
          ((s.card : ℝ)⁻¹ * ∑ i ∈ s, b i) := by
  by_cases hs0 : s.card = 0
  · rw [Finset.card_eq_zero.mp hs0]
    simp
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs0
  let A : ℝ := ∑ i ∈ s, a i
  let B : ℝ := ∑ i ∈ s, b i
  let m : ℝ := (s.card : ℝ)⁻¹
  have hsumRight :
      (∑ i ∈ s, a i * (m * B)) = A * (m * B) := by
    calc
      (∑ i ∈ s, a i * (m * B)) =
          (∑ i ∈ s, a i) * (m * B) := (Finset.sum_mul _ _ _).symm
      _ = A * (m * B) := by rfl
  have hsumLeft :
      (∑ i ∈ s, (m * A) * b i) = (m * A) * B := by
    calc
      (∑ i ∈ s, (m * A) * b i) =
          (m * A) * ∑ i ∈ s, b i := (Finset.mul_sum _ _ _).symm
      _ = (m * A) * B := by rfl
  have hsumConst :
      (∑ _i ∈ s, (m * A) * (m * B)) =
        (s.card : ℝ) * ((m * A) * (m * B)) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  change
    (∑ i ∈ s, (a i - m * A) * (b i - m * B)) =
      (∑ i ∈ s, a i * b i) - (s.card : ℝ) * (m * A) * (m * B)
  have hexpand :
      (∑ i ∈ s, (a i - m * A) * (b i - m * B)) =
        (∑ i ∈ s, a i * b i) - A * (m * B) - (m * A) * B +
          (s.card : ℝ) * ((m * A) * (m * B)) := by
    calc
      (∑ i ∈ s, (a i - m * A) * (b i - m * B)) =
          ∑ i ∈ s,
            (a i * b i - a i * (m * B) - (m * A) * b i +
              (m * A) * (m * B)) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = (∑ i ∈ s, a i * b i) - A * (m * B) - (m * A) * B +
          (s.card : ℝ) * ((m * A) * (m * B)) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [hsumRight, hsumLeft, hsumConst]
  rw [hexpand]
  dsimp [m]
  field_simp [hcard]
  ring

/-- Empirical mean of the first `n` observations, using the thesis convention. -/
noncomputable def empiricalMean
    {Ω : Type u} {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) : H :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω

/-- Taking a scalar projection commutes with the empirical mean. -/
theorem scalarProjection_empiricalMean
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) (h : H) :
    scalarProjection h (empiricalMean X n ω) =
      (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, scalarProjection h (X i ω) := by
  unfold scalarProjection empiricalMean
  rw [real_inner_smul_right, inner_sum]

/-- Matrix coefficients of the empirical raw second-moment operator. -/
theorem inner_rawSecondMomentOperator_apply
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) (h k : H) :
    inner ℝ h (rawSecondMomentOperator X n ω k) =
      (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n,
          scalarProjection h (X i ω) * scalarProjection k (X i ω) := by
  simp only [rawSecondMomentOperator, ContinuousLinearMap.smul_apply,
    real_inner_smul_right, ContinuousLinearMap.sum_apply, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [FunctionalData.tensorProduct_apply, real_inner_smul_right,
    scalarProjection]
  rw [real_inner_comm (X i ω) k]
  ring

/-- Biased empirical covariance operator, written as raw second moment minus
the rank-one empirical-mean correction. -/
noncomputable def biasedCovarianceOperator
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) : H →L[ℝ] H :=
  rawSecondMomentOperator X n ω -
    FunctionalData.tensorProduct
      (empiricalMean X n ω) (empiricalMean X n ω)

/-- Every matrix coefficient of the biased covariance operator is the scalar
biased covariance already used in the coefficientwise proof. -/
theorem inner_biasedCovarianceOperator_apply
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) (h k : H) :
    inner ℝ h (biasedCovarianceOperator X n ω k) =
      scalarBiasedCovariance X h k n ω := by
  rw [biasedCovarianceOperator, ContinuousLinearMap.sub_apply, inner_sub_right,
    inner_rawSecondMomentOperator_apply]
  rw [show inner ℝ h
      (FunctionalData.tensorProduct
        (empiricalMean X n ω) (empiricalMean X n ω) k) =
      scalarProjection h (empiricalMean X n ω) *
        scalarProjection k (empiricalMean X n ω) by
    simp only [FunctionalData.tensorProduct_apply, real_inner_smul_right,
      scalarProjection]
    rw [real_inner_comm (empiricalMean X n ω) k]
    ring]
  rw [scalarProjection_empiricalMean X n ω h,
    scalarProjection_empiricalMean X n ω k]
  rfl

/--
Thesis source: equation `eq:covariance-operator-estimate` in
`2 - day-ahead/3_functional_data_analysis.tex`.

Original label: `eq:covariance-operator-estimate`.

The definition is total on natural indices, while the convergence theorem
below deliberately evaluates it only at `n = k + 2`, where the manuscript's
unbiased denominator is nonzero. -/
noncomputable def sampleCovariance
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) : H →L[ℝ] H :=
  ((n - 1 : ℕ) : ℝ)⁻¹ •
    ∑ i ∈ Finset.range n,
      FunctionalData.tensorProduct
        (X i ω - empiricalMean X n ω)
        (X i ω - empiricalMean X n ω)

/-- Pointwise action of the empirical covariance operator. -/
theorem sampleCovariance_apply
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) (z : H) :
    sampleCovariance X n ω z =
      ((n - 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n,
          inner ℝ (X i ω - empiricalMean X n ω) z •
            (X i ω - empiricalMean X n ω) := by
  simp [sampleCovariance, FunctionalData.tensorProduct_apply]

/-- Every matrix coefficient of the empirical covariance operator is the
usual empirical cross-covariance of the corresponding scalar projections. -/
theorem inner_sampleCovariance_apply
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) (h k : H) :
    inner ℝ h (sampleCovariance X n ω k) =
      ((n - 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n,
          scalarProjection h (X i ω - empiricalMean X n ω) *
            scalarProjection k (X i ω - empiricalMean X n ω) := by
  rw [sampleCovariance_apply]
  simp only [real_inner_smul_right, inner_sum, scalarProjection]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]
  rw [real_inner_comm (X i ω - empiricalMean X n ω) k]

/-- The unbiased operator estimator differs from the biased scalar covariance
coefficient by the usual factor `n/(n-1)`. -/
theorem inner_sampleCovariance_eq_unbiasedFactor
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) (h k : H) (hn : 0 < n) :
    inner ℝ h (sampleCovariance X n ω k) =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ)⁻¹ *
        scalarBiasedCovariance X h k n ω := by
  rw [inner_sampleCovariance_apply]
  simp_rw [show ∀ i,
      scalarProjection h (X i ω - empiricalMean X n ω) =
        scalarProjection h (X i ω) -
          scalarProjection h (empiricalMean X n ω) by
    intro i
    simp [scalarProjection, inner_sub_right]]
  simp_rw [show ∀ i,
      scalarProjection k (X i ω - empiricalMean X n ω) =
        scalarProjection k (X i ω) -
          scalarProjection k (empiricalMean X n ω) by
    intro i
    simp [scalarProjection, inner_sub_right]]
  rw [scalarProjection_empiricalMean X n ω h,
    scalarProjection_empiricalMean X n ω k]
  have hcenter := sum_centered_mul_centered (Finset.range n)
    (fun i => scalarProjection h (X i ω))
    (fun i => scalarProjection k (X i ω))
  simp only [Finset.card_range] at hcenter
  rw [hcenter]
  simp only [scalarBiasedCovariance]
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnReal]

/-- Exact operator identity behind the scalar unbiased-correction formula. -/
theorem sampleCovariance_eq_unbiasedFactor_smul_biased
    {Ω : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) (hn : 0 < n) :
    sampleCovariance X n ω =
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ)⁻¹) •
        biasedCovarianceOperator X n ω := by
  apply ContinuousLinearMap.ext
  intro k
  apply ext_inner_left ℝ
  intro h
  rw [inner_sampleCovariance_eq_unbiasedFactor X n ω h k hn,
    ContinuousLinearMap.smul_apply, real_inner_smul_right,
    inner_biasedCovarianceOperator_apply]

/-- The unbiased correction factor along the safe indexing `n + 2` tends to
one. -/
theorem unbiasedFactor_tendsto_one :
    Tendsto
      (fun n : ℕ => ((n + 2 : ℕ) : ℝ) *
        (((n + 2 - 1 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hadd : Tendsto (fun n : ℕ => 1 + ((n : ℝ) + 1)⁻¹)
      atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hinv
  convert hadd using 1
  · funext n
    rw [show n + 2 - 1 = n + 1 by omega]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
    ring
  · norm_num

/-- Original label: `thm:lln-covariance`.
The current thesis asks for operator-norm convergence. This proves that
statement directly in the Banach space of bounded operators, under precisely
the second-moment assumption; no fourth moment is needed. -/
theorem sampleCovariance_operatorNorm_strong_law_ae
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => sampleCovariance X (k + 2) ω)
      atTop (𝓝 (FunctionalData.covarianceOperator μ (X 0))) := by
  letI : MeasurableSpace (H →L[ℝ] H) := borel (H →L[ℝ] H)
  letI : BorelSpace (H →L[ℝ] H) := ⟨rfl⟩
  let R : H → H →L[ℝ] H := fun x => FunctionalData.tensorProduct x x
  have hR : Measurable R := Covariance.continuous_tensorProduct_self.measurable
  let Y : ℕ → Ω → H →L[ℝ] H := fun i => R ∘ X i
  have hYint : Integrable (Y 0) μ :=
    Covariance.integrable_tensorProduct_self_of_memLp_two μ (X 0) hX
  have hindepY : iIndepFun Y μ := hindep.comp (fun _ => R) (fun _ => hR)
  have hidentY : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i => (hident i).comp hR
  have hraw := ProbabilityTheory.strong_law_ae Y hYint
    (fun _ _ hij => hindepY.indepFun hij) hidentY
  have hmean := hilbert_strong_law_ae X (hX.integrable (by norm_num))
    (fun _ _ hij => hindep.indepFun hij) hident
  filter_upwards [hraw, hmean] with ω hr hm
  have hbiased : Tendsto (fun n => biasedCovarianceOperator X n ω) atTop
      (𝓝 (FunctionalData.covarianceOperator μ (X 0))) := by
    rw [Covariance.covarianceOperator_eq_rawSecondMoment_sub_mean μ (X 0) hX]
    exact hr.sub (Covariance.continuous_tensorProduct_self.tendsto _ |>.comp hm)
  have hresult := unbiasedFactor_tendsto_one.smul
    (hbiased.comp (tendsto_add_atTop_nat 2))
  have hresult' : Tendsto (fun k : ℕ =>
      (((k + 2 : ℕ) : ℝ) * (((k + 2 - 1 : ℕ) : ℝ)⁻¹)) •
        biasedCovarianceOperator X (k + 2) ω) atTop
      (𝓝 (FunctionalData.covarianceOperator μ (X 0))) := by
    simpa only [one_smul, Function.comp_apply] using hresult
  exact hresult'.congr' (Filter.Eventually.of_forall fun k =>
    (sampleCovariance_eq_unbiasedFactor_smul_biased X (k + 2) ω (by omega)).symm)

/-- Extended Hilbert--Schmidt norm computed in a fixed Hilbert basis.  The
value may be `∞` for a general bounded operator. -/
noncomputable def hilbertSchmidtENorm
    {ι : Type*} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) : ℝ≥0∞ :=
  (∑' n, ENNReal.ofReal (‖A (b n)‖ ^ 2)) ^ (1 / 2 : ℝ)

/-!
The Hilbert--Schmidt sample-covariance strong law is proved without an axiom
in `DayAhead.HilbertSchmidtCovariance`.  That companion module constructs the
missing operator ideal concretely as square-summable basis coordinates and
identifies its norm with `hilbertSchmidtENorm` above.
-/

end LimitTheorems
end DayAhead
end Thesis
