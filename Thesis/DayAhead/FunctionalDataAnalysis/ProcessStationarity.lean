import Thesis.DayAhead.FunctionalDataAnalysis.HilbertSchmidtCovariance

/-!
# Weak stationarity of an actual square-integrable Hilbert-valued process

This connects the deterministic moment characterization to Bochner expectations,
scalar centered cross-moments, and the Hilbert--Schmidt condition in the thesis.
Time zero is the arbitrary reference time used in the manuscript's proof.
-/

namespace Thesis.DayAhead.ProcessStationarity

open MeasureTheory FunctionalData HilbertSchmidtCovariance
open scoped ENNReal

universe u v

variable {ι : Type*}

variable {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem continuous_tensorProduct :
    Continuous (fun p : H × H ↦ tensorProduct p.1 p.2) := by
  change Continuous (fun p : H × H ↦
    ((ContinuousLinearMap.smulRightL ℝ H H).comp (innerSL ℝ)) p.1 p.2)
  exact (((ContinuousLinearMap.smulRightL ℝ H H).comp (innerSL ℝ)).continuous.comp
    continuous_fst).clm_apply continuous_snd

omit [CompleteSpace H] in
theorem integrable_tensorProduct_of_memLp_two
    (μ : Measure Ω) (X Y : Ω → H) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω ↦ tensorProduct (X ω) (Y ω)) μ := by
  have hm := continuous_tensorProduct.comp_aestronglyMeasurable (hX.1.prodMk hY.1)
  have hn : Integrable (fun ω ↦ ‖X ω‖ * ‖Y ω‖) μ :=
    hX.norm.integrable_mul hY.norm
  exact hn.mono' hm (Filter.Eventually.of_forall fun ω ↦ by rw [norm_tensorProduct])

/-- The tensor order agrees with the thesis: the first argument is the input
functional and the second is the output vector. -/
noncomputable def crossCovarianceOperator (μ : Measure Ω) (X Y : Ω → H) :
    H →L[ℝ] H :=
  ∫ ω, tensorProduct (X ω - hilbertExpectation μ X)
    (Y ω - hilbertExpectation μ Y) ∂μ

omit [CompleteSpace H] in
theorem integrable_centered_tensorProduct_of_memLp_two
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y : Ω → H)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω ↦ tensorProduct (X ω - hilbertExpectation μ X)
      (Y ω - hilbertExpectation μ Y)) μ := by
  apply integrable_tensorProduct_of_memLp_two
  · exact hX.sub (memLp_const _)
  · exact hY.sub (memLp_const _)

theorem inner_crossCovarianceOperator_apply
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y : Ω → H)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a c : H) :
    inner ℝ c (crossCovarianceOperator μ X Y a) =
      ∫ ω, inner ℝ a (X ω - hilbertExpectation μ X) *
        inner ℝ c (Y ω - hilbertExpectation μ Y) ∂μ := by
  have hi := integrable_centered_tensorProduct_of_memLp_two μ X Y hX hY
  rw [crossCovarianceOperator, ContinuousLinearMap.integral_apply hi a]
  have hia : Integrable (fun ω ↦ tensorProduct (X ω - hilbertExpectation μ X)
      (Y ω - hilbertExpectation μ Y) a) μ :=
    ((ContinuousLinearMap.apply ℝ H) a).integrable_comp hi
  rw [← integral_inner hia c]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ by
    simp only [tensorProduct_apply, real_inner_smul_right]
    rw [real_inner_comm (X ω - hilbertExpectation μ X) a]

theorem crossCovarianceCoordinates_apply_eq_matrixCoefficient
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : HilbertBasis ι ℝ H)
    (X Y : Ω → H) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (i j : ι) :
    crossCovarianceCoordinates μ b X Y (i, j) =
      inner ℝ (b i) (crossCovarianceOperator μ X Y (b j)) := by
  let ev : HilbertSchmidtCoordinatesOn ι →L[ℝ] ℝ :=
    lp.evalCLM ℝ (fun _ : ι × ι ↦ ℝ) 2 (i, j)
  have hcomm : (∫ ω, tensorCoordinates b (X ω - hilbertExpectation μ X)
      (Y ω - hilbertExpectation μ Y) ∂μ) (i, j) =
      ∫ ω, tensorCoordinates b (X ω - hilbertExpectation μ X)
        (Y ω - hilbertExpectation μ Y) (i, j) ∂μ :=
    (ev.integral_comp_comm
      (integrable_centered_tensorCoordinates_of_memLp_two μ b X Y hX hY)).symm
  change (∫ ω, tensorCoordinates b (X ω - hilbertExpectation μ X)
    (Y ω - hilbertExpectation μ Y) ∂μ) (i, j) = _
  rw [hcomm, inner_crossCovarianceOperator_apply μ X Y hX hY]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ by
    simp only [tensorCoordinates_apply, HilbertBasis.repr_apply_apply]
    ring

/-- Square summability of all matrix entries is the Hilbert--Schmidt condition
in the fixed orthonormal basis. -/
def IsHilbertSchmidt (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) : Prop :=
  Summable (fun ij : ι × ι ↦ ‖inner ℝ (b ij.1) (A (b ij.2))‖ ^ 2)

/-- Original label: `prop:weak-stationarity`.
The cross-covariance operator is genuinely Hilbert--Schmidt; this is stronger
than proving finiteness of its individual scalar entries. -/
theorem crossCovarianceOperator_isHilbertSchmidt
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : HilbertBasis ι ℝ H)
    (X Y : Ω → H) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    IsHilbertSchmidt b (crossCovarianceOperator μ X Y) := by
  have hc := (lp.memℓp (crossCovarianceCoordinates μ b X Y)).summable (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    crossCovarianceCoordinates_apply_eq_matrixCoefficient μ b X Y hX hY]
    using hc

/-- Original label: `defn:weak-stationarity`.
The actual process definition, including the required Hilbert--Schmidt lag
operators. Centering at each time's own expectation equals centering at the
common mean under the first conjunct. -/
def WeaklyStationaryProcess (μ : Measure Ω) (b : HilbertBasis ι ℝ H)
    (X : ℕ → Ω → H) : Prop :=
  (∃ a : H, ∀ t, hilbertExpectation μ (X t) = a) ∧
    ∃ s : ℕ → H →L[ℝ] H, (∀ h, IsHilbertSchmidt b (s h)) ∧
      ∀ t h, crossCovarianceOperator μ (X (t + h)) (X t) = s h

/-- Scalar stationarity in exactly the expectation and centered-product form
of the manuscript, with a single coordinate mean for every time. -/
def ScalarStationaryProcess (μ : Measure Ω) (b : HilbertBasis ι ℝ H)
    (X : ℕ → Ω → H) : Prop :=
  ∃ a : ι → ℝ, (∀ t n, (∫ ω, score b n (X t ω) ∂μ) = a n) ∧
    ∃ s : ℕ → ι → ι → ℝ, ∀ t h n m,
      (∫ ω, (score b n (X (t + h) ω) - a n) *
        (score b m (X t ω) - a m) ∂μ) = s h n m

theorem score_crossCovarianceOperator
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : HilbertBasis ι ℝ H)
    (X Y : Ω → H) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (n m : ι) :
    score b m (crossCovarianceOperator μ X Y (b n)) =
      ∫ ω, (score b n (X ω) - ∫ η, score b n (X η) ∂μ) *
        (score b m (Y ω) - ∫ η, score b m (Y η) ∂μ) ∂μ := by
  rw [score, inner_crossCovarianceOperator_apply μ X Y hX hY]
  simp only [inner_sub_right, inner_hilbertExpectation (hX.integrable (by norm_num)),
    inner_hilbertExpectation (hY.integrable (by norm_num)), score]

theorem weaklyStationaryProcess_iff_moments
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : HilbertBasis ι ℝ H)
    (X : ℕ → Ω → H) (hX : ∀ t, MemLp (X t) 2 μ) :
    WeaklyStationaryProcess μ b X ↔
      WeaklyStationaryMoments (fun t ↦ hilbertExpectation μ (X t))
        (fun t s ↦ crossCovarianceOperator μ (X t) (X s)) := by
  constructor
  · rintro ⟨hm, s, _, hs⟩
    exact ⟨hm, s, hs⟩
  · rintro ⟨hm, s, hs⟩
    refine ⟨hm, s, fun h ↦ ?_, hs⟩
    rw [← hs 0 h, zero_add]
    exact crossCovarianceOperator_isHilbertSchmidt μ b _ _ (hX h) (hX 0)

/-- Original label: `prop:weak-stationarity`.
Full stochastic version: expectations and covariance operators are constructed
from the square-integrable process, their scalar formulas are proved, and the
Hilbert--Schmidt requirement is discharged. No moment-identification assumptions
are supplied by the caller. -/
theorem weaklyStationaryProcess_iff_scalar
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : HilbertBasis ι ℝ H)
    (X : ℕ → Ω → H) (hX : ∀ t, MemLp (X t) 2 μ) :
    WeaklyStationaryProcess μ b X ↔ ScalarStationaryProcess μ b X := by
  rw [weaklyStationaryProcess_iff_moments μ b X hX,
    weaklyStationaryMoments_iff_coordinates b]
  have hmean (t n) : score b n (hilbertExpectation μ (X t)) =
      ∫ ω, score b n (X t ω) ∂μ :=
    inner_hilbertExpectation ((hX t).integrable (by norm_num)) (b n)
  have hcov (t s n m) := score_crossCovarianceOperator μ b
    (X t) (X s) (hX t) (hX s) n m
  simp only [CoordinatewiseStationaryMoments, hmean, hcov]
  constructor
  · rintro ⟨hm, hc⟩
    refine ⟨fun n ↦ ∫ ω, score b n (X 0 ω) ∂μ, hm,
      fun h n m ↦ ∫ ω, (score b n (X h ω) - ∫ η, score b n (X 0 η) ∂μ) *
        (score b m (X 0 ω) - ∫ η, score b m (X 0 η) ∂μ) ∂μ, ?_⟩
    intro t h n m
    simpa only [hm] using hc t h n m
  · rintro ⟨a, hm, s, hs⟩
    constructor
    · intro t n
      rw [hm t n, hm 0 n]
    · intro t h n m
      simp only [hm]
      exact (hs t h n m).trans (by simpa only [zero_add] using (hs 0 h n m).symm)

end Thesis.DayAhead.ProcessStationarity
