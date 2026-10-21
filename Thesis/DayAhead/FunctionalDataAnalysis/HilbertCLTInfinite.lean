import Thesis.DayAhead.FunctionalDataAnalysis.HilbertCLTBasic
import Thesis.DayAhead.FunctionalDataAnalysis.HilbertCLTTightness
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Central limit theorem in a separable Hilbert space

Uniform tightness gives a subsequential weak limit. Scalar CLTs identify
its characteristic function as the centered Gaussian with the source
covariance. Tightness and uniqueness of that characteristic function then
give convergence of the entire sequence.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology BoundedContinuousFunction Real
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace Thesis.DayAhead.LimitTheorems

variable {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [IsProbabilityMeasure μ] in
theorem normalizedHilbertSum_eq_centered (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) :
    normalizedHilbertSum μ X n ω = HilbertCLTMoments.normalizedSum
      (fun i ω => X i ω - FunctionalData.hilbertExpectation μ (X 0)) n ω := by
  by_cases hn : n = 0
  · subst n
    simp [normalizedHilbertSum, HilbertCLTMoments.normalizedSum]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
  have hcoeff : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
    field_simp
    exact Real.sq_sqrt hnpos.le
  have hcoeff' : (Real.sqrt n)⁻¹ * n = Real.sqrt n := by
    field_simp
    exact (Real.sq_sqrt hnpos.le).symm
  simp only [normalizedHilbertSum, HilbertCLTMoments.normalizedSum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_sub, smul_smul, hcoeff, hcoeff']

omit [SecondCountableTopology H] in
theorem normalizedHilbertSum_memLp (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    MemLp (normalizedHilbertSum μ X n) 2 μ := by
  have hc (i : ℕ) : MemLp
      (fun ω => X i ω - FunctionalData.hilbertExpectation μ (X 0)) 2 μ :=
    ((hident i).memLp_iff.mpr hX).sub (memLp_const _)
  simpa only [funext (normalizedHilbertSum_eq_centered μ X n)] using
    HilbertCLTMoments.normalizedSum_memLp _ hc n

theorem normalizedHilbertSum_isTight (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    IsTightMeasureSet (range fun n => μ.map (normalizedHilbertSum μ X n)) := by
  let m := FunctionalData.hilbertExpectation μ (X 0)
  let Y : ℕ → Ω → H := fun i ω => X i ω - m
  have hY : MemLp (Y 0) 2 μ := hX.sub (memLp_const m)
  have hmean : ∫ ω, Y 0 ω ∂μ = 0 := by
    rw [show Y 0 = fun ω => X 0 ω - m from rfl,
      integral_sub (hX.integrable (by norm_num)) (integrable_const m)]
    simp [m, FunctionalData.hilbertExpectation]
  have hindepY : iIndepFun Y μ := hindep.comp (fun x => fun y => y - m) (fun _ => by fun_prop)
  have hidentY (i : ℕ) : IdentDistrib (Y i) (Y 0) μ μ := (hident i).sub_const m
  simpa only [funext fun n => funext (normalizedHilbertSum_eq_centered μ X n)] using
    HilbertCLTTightness.normalizedSum_isTight Y hY hmean hindepY hidentY

theorem normalizedHilbertSum_charFun_tendsto (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (t : H) :
    Tendsto (fun n => charFun (μ.map (normalizedHilbertSum μ X n)) t) atTop
      (𝓝 (Complex.exp (- (covarianceBilin (μ.map (X 0)) t t : ℂ) / 2))) := by
  letI : IsProbabilityMeasure (μ.map (X 0)) := Measure.isProbabilityMeasure_map hX.1.aemeasurable
  have hId : MemLp id 2 (μ.map (X 0)) :=
    (memLp_map_measure_iff (by fun_prop) hX.1.aemeasurable).mpr hX
  have hquad : covarianceBilin (μ.map (X 0)) t t =
      Var[(fun ω => scalarProjection t (X 0 ω)); μ] := by
    rw [covarianceBilin_self hId, variance_map (by fun_prop) hX.1.aemeasurable]
    rfl
  have hscalar := scalarProjection_central_limit_gaussianReal μ X hX hindep hident t
  have hscalarZ : TendstoInDistribution
      (fun n ω => scalarProjection t (normalizedHilbertSum μ X n ω)) atTop id
      (fun _ : ℕ => μ) (gaussianReal 0
        Var[(fun ω => scalarProjection t (X 0 ω)); μ].toNNReal) := by
    convert hscalar using 1
    funext n ω
    exact scalarProjection_normalizedHilbertSum μ X hX n ω t
  have hchar := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hscalarZ.tendsto) 1
  change Tendsto (fun n => charFun
    (μ.map (fun ω => scalarProjection t (normalizedHilbertSum μ X n ω))) 1) atTop
    (𝓝 (charFun (Measure.map id (gaussianReal 0
      Var[(fun ω => scalarProjection t (X 0 ω)); μ].toNNReal)) 1)) at hchar
  have hseq (n : ℕ) := charFun_map_eq_scalarProjection_one μ (normalizedHilbertSum μ X n)
    (normalizedHilbertSum_memLp μ X hX hident n).1.aemeasurable t
  simp_rw [hseq]
  rw [hquad]
  simpa [charFun_gaussianReal, neg_div] using hchar

/-- Original label: `thm:lln-clt-mean`.
The central limit theorem in every real separable Hilbert space, proved
from tightness and the scalar projection CLTs. -/
theorem separable_hilbert_central_limit (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∃ ν : ProbabilityMeasure H,
      IsGaussian (ν : Measure H) ∧
      FunctionalData.hilbertExpectation (ν : Measure H) id = 0 ∧
      FunctionalData.covarianceOperator (ν : Measure H) id =
        FunctionalData.covarianceOperator μ (X 0) ∧
      TendstoInDistribution (normalizedHilbertSum μ X) atTop id
        (fun _ : ℕ => μ) (ν : Measure H) := by
  let laws : ℕ → ProbabilityMeasure H := fun n =>
    ⟨μ.map (normalizedHilbertSum μ X n), Measure.isProbabilityMeasure_map
      (normalizedHilbertSum_memLp μ X hX hident n).1.aemeasurable⟩
  have htight : IsTightMeasureSet (range fun n => (laws n : Measure H)) :=
    normalizedHilbertSum_isTight μ X hX hindep hident
  have hcompact : IsCompact (closure (range laws)) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using htight)
  obtain ⟨ν, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hchar (t : H) : charFun (ν : Measure H) t =
      Complex.exp (- (covarianceBilin (μ.map (X 0)) t t : ℂ) / 2) := by
    have hweakchar : Tendsto (fun n => charFun (laws (φ n) : Measure H) t) atTop
        (𝓝 (charFun (ν : Measure H) t)) := by
      simpa only [charFun_eq_integral_innerProbChar] using
        (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim (innerProbChar t)
    exact tendsto_nhds_unique hweakchar
      ((normalizedHilbertSum_charFun_tendsto μ X hX hindep hident t).comp hφ.tendsto_atTop)
  let f := covarianceBilin (μ.map (X 0))
  have hf : f.toBilinForm.IsPosSemidef := isPosSemidef_covarianceBilin
  have hformula (t : H) : charFun (ν : Measure H) t =
      Complex.exp ((inner ℝ t (0 : H) : ℂ) * Complex.I - f t t / 2) := by
    simpa only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div] using hchar t
  have hgaussian : IsGaussian (ν : Measure H) :=
    isGaussian_iff_gaussian_charFun.mpr ⟨0, f, hf, hformula⟩
  letI : IsGaussian (ν : Measure H) := hgaussian
  obtain ⟨hmean, hcov⟩ := gaussian_charFun_congr (μ := (ν : Measure H)) 0 f hf hformula
  refine ⟨ν, hgaussian, hmean.symm, ?_, ?_⟩
  · letI : IsProbabilityMeasure (μ.map (X 0)) :=
      Measure.isProbabilityMeasure_map hX.1.aemeasurable
    have hId : MemLp id 2 (μ.map (X 0)) :=
      (memLp_map_measure_iff (by fun_prop) hX.1.aemeasurable).mpr hX
    rw [← covarianceOperator_map_eq μ (X 0) hX]
    apply ContinuousLinearMap.ext
    intro k
    apply ext_inner_left ℝ
    intro h
    calc
      inner ℝ h (FunctionalData.covarianceOperator (ν : Measure H) id k) =
          covarianceBilin (ν : Measure H) h k := by
        rw [Covariance.inner_covarianceOperator_apply_eq_integral_centered
          (ν : Measure H) id IsGaussian.memLp_two_id h k,
          covarianceBilin_apply IsGaussian.memLp_two_id h k]
        rfl
      _ = covarianceBilin (μ.map (X 0)) h k := by rw [← hcov]
      _ = inner ℝ h (FunctionalData.covarianceOperator (μ.map (X 0)) id k) := by
        rw [Covariance.inner_covarianceOperator_apply_eq_integral_centered
          (μ.map (X 0)) id hId h k, covarianceBilin_apply hId h k]
        rfl
  · have hcharlim (t : H) : Tendsto (fun n => charFun (laws n : Measure H) t) atTop
        (𝓝 (charFun (ν : Measure H) t)) := by
      rw [hchar]
      exact normalizedHilbertSum_charFun_tendsto μ X hX hindep hident t
    have hweak : Tendsto laws atTop (𝓝 ν) := by
      apply ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℂ (by simpa using htight)
        (A := charPoly continuous_probChar (L := innerₗ H) continuous_inner)
      · exact separatesPoints_charPoly continuous_probChar probChar_ne_one _
          (fun v hv => DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩)
      · exact fun g hg => ProbabilityMeasure.tendsto_charPoly_of_tendsto_charFun hcharlim hg
    refine ⟨fun n => (normalizedHilbertSum_memLp μ X hX hident n).1.aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using hweak

/-- Original label: `thm:lln-clt-mean`.
The former external boundary, retained under its historical name for existing
source links. The full Hilbert-space result now has an internal proof. -/
theorem hilbert_central_limit_external (_hInfinite : ¬ FiniteDimensional ℝ H)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∃ ν : ProbabilityMeasure H,
      IsGaussian (ν : Measure H) ∧
      FunctionalData.hilbertExpectation (ν : Measure H) id = 0 ∧
      FunctionalData.covarianceOperator (ν : Measure H) id =
        FunctionalData.covarianceOperator μ (X 0) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n •
          ((n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω) -
            FunctionalData.hilbertExpectation μ (X 0)))
        atTop id (fun _ : ℕ => μ) (ν : Measure H) :=
  separable_hilbert_central_limit μ X hX hindep hident

end Thesis.DayAhead.LimitTheorems
