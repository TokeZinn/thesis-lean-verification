import Thesis.DayAhead.FunctionalDataAnalysis.FunctionalData
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Properties of Hilbert-space covariance operators

This proof-support module supplies covariance identities and positivity facts
used by the formal limit theorems.
-/

namespace Thesis
namespace DayAhead
namespace Covariance

open MeasureTheory

universe u v

/-- A diagonal rank-one operator is symmetric. -/
theorem tensorProduct_self_isSymmetric
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : H) :
    (FunctionalData.tensorProduct x x).toLinearMap.IsSymmetric := by
  simpa only [FunctionalData.tensorProduct] using
    (InnerProductSpace.isSymmetric_rankOne_self (𝕜 := ℝ) x)

/-- A diagonal rank-one operator is positive semidefinite. -/
theorem tensorProduct_self_isPositive
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : H) :
    (FunctionalData.tensorProduct x x).IsPositive := by
  simpa only [FunctionalData.tensorProduct] using
    (InnerProductSpace.isPositive_rankOne_self (𝕜 := ℝ) x)

/-- The diagonal rank-one operator depends continuously on its vector. -/
theorem continuous_tensorProduct_self
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    Continuous (fun x : H => FunctionalData.tensorProduct x x) := by
  unfold FunctionalData.tensorProduct
  exact
    (ContinuousLinearMap.apply' (H →L[ℝ] H) (starRingEnd ℝ)).continuous.clm_apply
      ((ContinuousLinearMap.smulRightL ℝ H H).continuous.comp
        (innerSL ℝ).continuous)

/-- The centred rank-one integrand whose Bochner integral is the covariance
operator. -/
noncomputable def covarianceIntegrand
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : Ω → H) (ω : Ω) : H →L[ℝ] H :=
  let mean := FunctionalData.hilbertExpectation μ X
  FunctionalData.tensorProduct (X ω - mean) (X ω - mean)

theorem covarianceOperator_eq_integral_covarianceIntegrand
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : Ω → H) :
    FunctionalData.covarianceOperator μ X =
      ∫ ω, covarianceIntegrand μ X ω ∂μ := by
  rfl

theorem covarianceIntegrand_isSymmetric
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : Ω → H) (ω : Ω) :
    (covarianceIntegrand μ X ω).toLinearMap.IsSymmetric := by
  exact tensorProduct_self_isSymmetric _

theorem covarianceIntegrand_isPositive
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : Ω → H) (ω : Ω) :
    (covarianceIntegrand μ X ω).IsPositive := by
  exact tensorProduct_self_isPositive _

/-- A square-integrable Hilbert-valued random element has an integrable
operator-valued covariance integrand. This discharges the analytic hypothesis
used by the covariance properties below from the thesis assumption
`E ‖X‖² < ∞`. -/
theorem integrable_covarianceIntegrand_of_memLp_two
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → H) (hX : MemLp X 2 μ) :
    Integrable (covarianceIntegrand μ X) μ := by
  let centered : Ω → H := fun ω =>
    X ω - FunctionalData.hilbertExpectation μ X
  have hcentered : MemLp centered 2 μ := by
    simpa only [centered, Pi.sub_apply] using
      hX.sub (memLp_const (FunctionalData.hilbertExpectation μ X))
  have hmeas : AEStronglyMeasurable (covarianceIntegrand μ X) μ := by
    simpa only [covarianceIntegrand, centered] using
      continuous_tensorProduct_self.comp_aestronglyMeasurable hcentered.1
  refine (hcentered.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mono'
    hmeas ?_
  exact Filter.Eventually.of_forall fun ω => by
    simp only [covarianceIntegrand, centered, FunctionalData.norm_tensorProduct]
    rw [pow_two]

/-- A square-integrable Hilbert-valued random element has an integrable raw
rank-one second-moment operator. -/
theorem integrable_tensorProduct_self_of_memLp_two
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) (X : Ω → H) (hX : MemLp X 2 μ) :
    Integrable (fun ω => FunctionalData.tensorProduct (X ω) (X ω)) μ := by
  have hmeas : AEStronglyMeasurable
      (fun ω => FunctionalData.tensorProduct (X ω) (X ω)) μ :=
    continuous_tensorProduct_self.comp_aestronglyMeasurable hX.1
  refine (hX.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mono'
    hmeas ?_
  exact Filter.Eventually.of_forall fun ω => by
    simp only [FunctionalData.norm_tensorProduct]
    rw [pow_two]

/-- Every matrix coefficient of the covariance operator is the integral of
the corresponding product of centred scalar coordinates. -/
theorem inner_covarianceOperator_apply_eq_integral_centered
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → H) (hX : MemLp X 2 μ)
    (h k : H) :
    inner ℝ h (FunctionalData.covarianceOperator μ X k) =
      ∫ ω,
        inner ℝ h (X ω - FunctionalData.hilbertExpectation μ X) *
          inner ℝ k (X ω - FunctionalData.hilbertExpectation μ X) ∂μ := by
  have hI : Integrable (covarianceIntegrand μ X) μ :=
    integrable_covarianceIntegrand_of_memLp_two μ X hX
  rw [covarianceOperator_eq_integral_covarianceIntegrand,
    ContinuousLinearMap.integral_apply hI k]
  have hIk : Integrable (fun ω => covarianceIntegrand μ X ω k) μ :=
    ((ContinuousLinearMap.apply ℝ H) k).integrable_comp hI
  rw [← integral_inner hIk h]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [covarianceIntegrand, FunctionalData.tensorProduct_apply,
    real_inner_smul_right]
  rw [real_inner_comm (X ω - FunctionalData.hilbertExpectation μ X) k]
  ring

/-- Every matrix coefficient of the covariance operator is the corresponding
raw second moment minus the product of the two scalar means. -/
theorem inner_covarianceOperator_apply_eq_rawMoments
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → H) (hX : MemLp X 2 μ) (h k : H) :
    inner ℝ h (FunctionalData.covarianceOperator μ X k) =
      (∫ ω, inner ℝ h (X ω) * inner ℝ k (X ω) ∂μ) -
        (∫ ω, inner ℝ h (X ω) ∂μ) *
          ∫ ω, inner ℝ k (X ω) ∂μ := by
  have hXint : Integrable X μ := hX.integrable (by norm_num)
  have hh2 : MemLp (fun ω => inner ℝ h (X ω)) 2 μ := hX.const_inner h
  have hk2 : MemLp (fun ω => inner ℝ k (X ω)) 2 μ := hX.const_inner k
  have hh : Integrable (fun ω => inner ℝ h (X ω)) μ :=
    hh2.integrable (by norm_num)
  have hk : Integrable (fun ω => inner ℝ k (X ω)) μ :=
    hk2.integrable (by norm_num)
  have hhk : Integrable
      (fun ω => inner ℝ h (X ω) * inner ℝ k (X ω)) μ :=
    hh2.integrable_mul hk2
  have hmean_h :
      inner ℝ h (FunctionalData.hilbertExpectation μ X) =
        ∫ ω, inner ℝ h (X ω) ∂μ :=
    FunctionalData.inner_hilbertExpectation hXint h
  have hmean_k :
      inner ℝ k (FunctionalData.hilbertExpectation μ X) =
        ∫ ω, inner ℝ k (X ω) ∂μ :=
    FunctionalData.inner_hilbertExpectation hXint k
  rw [inner_covarianceOperator_apply_eq_integral_centered μ X hX h k]
  simp_rw [inner_sub_right, hmean_h, hmean_k, sub_mul, mul_sub]
  let mh : ℝ := ∫ ω, inner ℝ h (X ω) ∂μ
  let mk : ℝ := ∫ ω, inner ℝ k (X ω) ∂μ
  have hconst : Integrable (fun _ : Ω => mh * mk) μ := integrable_const _
  have hleft : Integrable
      (fun ω => inner ℝ h (X ω) * inner ℝ k (X ω) -
        inner ℝ h (X ω) * mk) μ :=
    hhk.sub (hh.mul_const mk)
  have hright : Integrable
      (fun ω => mh * inner ℝ k (X ω) - mh * mk) μ :=
    (hk.const_mul mh).sub hconst
  change
    (∫ ω,
      (inner ℝ h (X ω) * inner ℝ k (X ω) - inner ℝ h (X ω) * mk) -
        (mh * inner ℝ k (X ω) - mh * mk) ∂μ) =
      (∫ ω, inner ℝ h (X ω) * inner ℝ k (X ω) ∂μ) - mh * mk
  rw [integral_sub hleft hright,
    integral_sub hhk (hh.mul_const mk),
    integral_sub (hk.const_mul mh) hconst,
    integral_mul_const, integral_const_mul]
  simp
  ring

/-- The covariance operator is the raw rank-one second moment minus the
rank-one operator formed from the population mean. -/
theorem covarianceOperator_eq_rawSecondMoment_sub_mean
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → H) (hX : MemLp X 2 μ) :
    FunctionalData.covarianceOperator μ X =
      (∫ ω, FunctionalData.tensorProduct (X ω) (X ω) ∂μ) -
        FunctionalData.tensorProduct
          (FunctionalData.hilbertExpectation μ X)
          (FunctionalData.hilbertExpectation μ X) := by
  have hraw := integrable_tensorProduct_self_of_memLp_two μ X hX
  have hXint : Integrable X μ := hX.integrable (by norm_num)
  apply ContinuousLinearMap.ext
  intro k
  apply ext_inner_left ℝ
  intro h
  rw [inner_covarianceOperator_apply_eq_rawMoments μ X hX h k]
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
  rw [ContinuousLinearMap.integral_apply hraw k]
  have hrawk : Integrable
      (fun ω => FunctionalData.tensorProduct (X ω) (X ω) k) μ :=
    ((ContinuousLinearMap.apply ℝ H) k).integrable_comp hraw
  rw [← integral_inner hrawk h]
  have hmean_h := FunctionalData.inner_hilbertExpectation hXint h
  have hmean_k := FunctionalData.inner_hilbertExpectation hXint k
  rw [show inner ℝ h
      (FunctionalData.tensorProduct
        (FunctionalData.hilbertExpectation μ X)
        (FunctionalData.hilbertExpectation μ X) k) =
      inner ℝ h (FunctionalData.hilbertExpectation μ X) *
        inner ℝ k (FunctionalData.hilbertExpectation μ X) by
    simp only [FunctionalData.tensorProduct_apply, real_inner_smul_right]
    rw [real_inner_comm (FunctionalData.hilbertExpectation μ X) k]
    ring]
  rw [hmean_h, hmean_k]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [FunctionalData.tensorProduct_apply, real_inner_smul_right]
  rw [real_inner_comm (X ω) k]
  ring

/-- The diagonal matrix coefficient of the covariance operator is the
expected squared centred scalar score. -/
theorem inner_covarianceOperator_apply_self_eq_integral_sq
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → H) (hX : MemLp X 2 μ) (h : H) :
    inner ℝ h (FunctionalData.covarianceOperator μ X h) =
      ∫ ω,
        (inner ℝ h (X ω - FunctionalData.hilbertExpectation μ X)) ^ 2 ∂μ := by
  simpa only [pow_two] using
    inner_covarianceOperator_apply_eq_integral_centered μ X hX h h

/-- The covariance operator is self-adjoint whenever its operator-valued
integrand is Bochner integrable. -/
theorem covarianceOperator_isSymmetric
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : Ω → H)
    (hI : Integrable (covarianceIntegrand μ X) μ) :
    (FunctionalData.covarianceOperator μ X).toLinearMap.IsSymmetric := by
  rw [covarianceOperator_eq_integral_covarianceIntegrand]
  intro x y
  have hIx : Integrable (fun ω => covarianceIntegrand μ X ω x) μ :=
    ((ContinuousLinearMap.apply ℝ H) x).integrable_comp hI
  have hIy : Integrable (fun ω => covarianceIntegrand μ X ω y) μ :=
    ((ContinuousLinearMap.apply ℝ H) y).integrable_comp hI
  change inner ℝ ((∫ ω, covarianceIntegrand μ X ω ∂μ) x) y =
    inner ℝ x ((∫ ω, covarianceIntegrand μ X ω ∂μ) y)
  rw [ContinuousLinearMap.integral_apply hI x,
    ContinuousLinearMap.integral_apply hI y]
  rw [← real_inner_comm, ← integral_inner hIx y, ← integral_inner hIy x]
  exact integral_congr_ae <| Filter.Eventually.of_forall fun ω =>
    (real_inner_comm (covarianceIntegrand μ X ω x) y).trans
      (covarianceIntegrand_isSymmetric μ X ω x y)

/-- The covariance operator is positive semidefinite whenever its
operator-valued integrand is Bochner integrable. -/
theorem covarianceOperator_isPositive
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : Ω → H)
    (hI : Integrable (covarianceIntegrand μ X) μ) :
    (FunctionalData.covarianceOperator μ X).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨covarianceOperator_isSymmetric μ X hI, fun x => ?_⟩
  rw [covarianceOperator_eq_integral_covarianceIntegrand,
    ContinuousLinearMap.integral_apply hI x]
  have hIx : Integrable (fun ω => covarianceIntegrand μ X ω x) μ :=
    ((ContinuousLinearMap.apply ℝ H) x).integrable_comp hI
  rw [← real_inner_comm, ← integral_inner hIx x]
  apply integral_nonneg
  intro ω
  change (0 : ℝ) ≤ inner ℝ x (covarianceIntegrand μ X ω x)
  rw [real_inner_comm]
  exact (covarianceIntegrand_isPositive μ X ω).2 x

/-- Positive semidefiniteness under the square-integrability hypothesis used
in the functional-data chapter. -/
theorem covarianceOperator_isPositive_of_memLp_two
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → H) (hX : MemLp X 2 μ) :
    (FunctionalData.covarianceOperator μ X).IsPositive :=
  covarianceOperator_isPositive μ X
    (integrable_covarianceIntegrand_of_memLp_two μ X hX)

end Covariance
end DayAhead
end Thesis
