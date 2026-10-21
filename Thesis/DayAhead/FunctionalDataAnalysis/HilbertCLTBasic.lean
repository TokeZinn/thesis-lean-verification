import Thesis.DayAhead.FunctionalDataAnalysis.LimitTheorems
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Finite-dimensional Hilbert-space central limit theorem

This module proves the thesis's Hilbert-space central limit theorem internally
in every finite dimension.  The Euclidean proof constructs the centred
multivariate Gaussian with the source covariance operator and obtains weak
convergence from the scalar projection CLTs through Lévy's continuity theorem.
An orthonormal basis then transports the result to an arbitrary
finite-dimensional real Hilbert space.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology RealInnerProductSpace MatrixOrder

namespace Thesis.DayAhead.LimitTheorems

universe u

theorem matrixBilin_eq_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (h k : EuclideanSpace ℝ ι) :
    h.ofLp ⬝ᵥ
        ((LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
          (EuclideanSpace.basisFun ι ℝ).toBasis) A.toLinearMap).mulVec k.ofLp =
      inner ℝ h (A k) := by
  have hre (x : EuclideanSpace ℝ ι) :
      (EuclideanSpace.basisFun ι ℝ).repr x = x := by
    ext i
    rfl
  have hsymm (x : EuclideanSpace ℝ ι) :
      (EuclideanSpace.basisFun ι ℝ).repr.symm x = x := by
    apply (EuclideanSpace.basisFun ι ℝ).repr.injective
    rw [LinearIsometryEquiv.apply_symm_apply, hre]
  simp only [LinearMap.toMatrix, OrthonormalBasis.coe_toBasis_repr,
    LinearEquiv.trans_apply, LinearMap.toMatrix'_mulVec,
    LinearEquiv.arrowCongr_apply, LinearEquiv.trans_symm,
    WithLp.linearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe,
    Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
    WithLp.addEquiv_symm_apply, WithLp.toLp_ofLp,
    LinearIsometryEquiv.coe_symm_toLinearEquiv, hsymm,
    ContinuousLinearMap.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    hre, WithLp.linearEquiv_apply, Equiv.toFun_as_coe, EquivLike.coe_coe,
    WithLp.addEquiv_apply]
  calc
    h.ofLp ⬝ᵥ (A k).ofLp = (A k).ofLp ⬝ᵥ h.ofLp :=
      dotProduct_comm _ _
    _ = inner ℝ h (A k) := by
      simpa using (EuclideanSpace.inner_eq_star_dotProduct h (A k)).symm

theorem gaussian_covarianceOperator_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hA : A.IsPositive) :
    FunctionalData.covarianceOperator
        (multivariateGaussian 0
          ((LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
            (EuclideanSpace.basisFun ι ℝ).toBasis) A.toLinearMap)) id = A := by
  let S := (LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
    (EuclideanSpace.basisFun ι ℝ).toBasis) A.toLinearMap
  have hS : S.PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun ι ℝ)).2 hA
  let ν : Measure (EuclideanSpace ℝ ι) := multivariateGaussian 0 S
  have hν : MemLp id 2 ν := IsGaussian.memLp_two_id
  apply ContinuousLinearMap.ext
  intro k
  apply ext_inner_left ℝ
  intro h
  calc
    inner ℝ h (FunctionalData.covarianceOperator ν id k) =
        covarianceBilin ν h k := by
      rw [Covariance.inner_covarianceOperator_apply_eq_integral_centered ν id hν h k,
        covarianceBilin_apply hν h k]
      rfl
    _ = h.ofLp ⬝ᵥ S.mulVec k.ofLp :=
      covarianceBilin_multivariateGaussian hS h k
    _ = inner ℝ h (A k) := matrixBilin_eq_inner A h k

/-- The normalised empirical sum appearing in the central-limit clause of
Theorem `thm:lln-clt-mean`.

Original label: `thm:lln-clt-mean`. -/
noncomputable def normalizedHilbertSum
    {Ω : Type*} {H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) : H :=
  Real.sqrt n •
    ((n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω) -
      FunctionalData.hilbertExpectation μ (X 0))

theorem scalarProjection_normalizedHilbertSum
    {Ω : Type*} {H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (n : ℕ) (ω : Ω) (h : H) :
    scalarProjection h (normalizedHilbertSum μ X n ω) =
      (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, scalarProjection h (X k ω) -
          n * μ[fun ω => scalarProjection h (X 0 ω)]) := by
  have hXint : Integrable (X 0) μ := hX.integrable (by norm_num)
  have hmean := FunctionalData.inner_hilbertExpectation hXint h
  by_cases hn : n = 0
  · subst n
    simp [normalizedHilbertSum, scalarProjection]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  rw [normalizedHilbertSum, scalarProjection, inner_smul_right, inner_sub_right,
    inner_smul_right, hmean]
  simp_rw [scalarProjection]
  simp only [inner_sum]
  field_simp [ne_of_gt hsqrtpos, hn]
  rw [hsqrtSq]

theorem matrixQuad_covariance_eq_variance
    {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ ι) (hX : MemLp X 2 μ)
    (t : EuclideanSpace ℝ ι) :
    t.ofLp ⬝ᵥ
        ((LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
          (EuclideanSpace.basisFun ι ℝ).toBasis)
            (FunctionalData.covarianceOperator μ X).toLinearMap).mulVec t.ofLp =
      Var[(fun ω => scalarProjection t (X ω)); μ] := by
  rw [matrixBilin_eq_inner]
  rw [Covariance.inner_covarianceOperator_apply_self_eq_integral_sq μ X hX t]
  have hproj : AEMeasurable (fun ω => scalarProjection t (X ω)) μ :=
    (hX.const_inner t).1.aemeasurable
  rw [ProbabilityTheory.variance_eq_integral hproj]
  have hXint : Integrable X μ := hX.integrable (by norm_num)
  have hmean := FunctionalData.inner_hilbertExpectation hXint t
  simp_rw [scalarProjection, inner_sub_right, hmean]

theorem charFun_map_eq_scalarProjection_one
    {Ω : Type*} {H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [BorelSpace H]
    (μ : Measure Ω) (Y : Ω → H) (hY : AEMeasurable Y μ) (t : H) :
    charFun (μ.map Y) t =
      charFun (μ.map (fun ω => scalarProjection t (Y ω))) 1 := by
  rw [charFun_apply, integral_map hY]
  · rw [charFun_apply, integral_map]
    · apply integral_congr_ae
      filter_upwards [] with ω
      have hleft : inner ℝ (Y ω) t = scalarProjection t (Y ω) := by
        exact real_inner_comm _ _
      have hright : inner ℝ (scalarProjection t (Y ω)) (1 : ℝ) =
          scalarProjection t (Y ω) := by
        rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
        simp
      rw [hleft, hright]
    · have hproj : Measurable (scalarProjection t) := by
        change Measurable (fun x : H => inner ℝ t x)
        fun_prop
      exact hproj.comp_aemeasurable hY
    · fun_prop
  · fun_prop

theorem memLp_comp_linearIsometryEquiv
    {Ω : Type*} {H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (μ : Measure Ω) (e : H ≃ₗᵢ[ℝ] K) {X : Ω → H}
    (hX : MemLp X 2 μ) : MemLp (fun ω => e (X ω)) 2 μ := by
  apply hX.norm.mono'
  · exact e.continuous.comp_aestronglyMeasurable hX.1
  · exact Filter.Eventually.of_forall fun ω => by rw [e.norm_map]

theorem covarianceOperator_comp_linearIsometryEquiv
    {Ω : Type*} {H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (e : H ≃ₗᵢ[ℝ] K) (X : Ω → H) (hX : MemLp X 2 μ) :
    FunctionalData.covarianceOperator μ (fun ω => e (X ω)) =
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((FunctionalData.covarianceOperator μ X).comp
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  let Y : Ω → K := fun ω => e (X ω)
  have hY : MemLp Y 2 μ := memLp_comp_linearIsometryEquiv μ e hX
  have hmean : FunctionalData.hilbertExpectation μ Y =
      e (FunctionalData.hilbertExpectation μ X) := by
    exact e.toContinuousLinearEquiv.integral_comp_comm X
  apply ContinuousLinearMap.ext
  intro k
  apply ext_inner_left ℝ
  intro h
  rw [Covariance.inner_covarianceOperator_apply_eq_integral_centered μ Y hY h k]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← e.apply_symm_apply h, ← e.apply_symm_apply k,
    hmean]
  simp only [Y]
  simp_rw [← e.map_sub, e.inner_map_map]
  change _ = inner ℝ (e (e.symm h))
    (e (FunctionalData.covarianceOperator μ X (e.symm (e (e.symm k)))))
  rw [e.symm_apply_apply, e.inner_map_map]
  exact (Covariance.inner_covarianceOperator_apply_eq_integral_centered
    μ X hX (e.symm h) (e.symm k)).symm

theorem covarianceOperator_map_eq
    {Ω : Type*} {H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → H) (hX : MemLp X 2 μ) :
    FunctionalData.covarianceOperator (μ.map X) id =
      FunctionalData.covarianceOperator μ X := by
  letI : IsProbabilityMeasure (μ.map X) :=
    Measure.isProbabilityMeasure_map hX.1.aemeasurable
  have hId : MemLp id 2 (μ.map X) := by
    rw [memLp_map_measure_iff (by fun_prop) hX.1.aemeasurable]
    simpa using hX
  apply ContinuousLinearMap.ext
  intro k
  apply ext_inner_left ℝ
  intro h
  rw [Covariance.inner_covarianceOperator_apply_eq_rawMoments
      (μ.map X) id hId h k,
    Covariance.inner_covarianceOperator_apply_eq_rawMoments μ X hX h k]
  simp only [id_eq]
  rw [integral_map hX.1.aemeasurable (by fun_prop),
    integral_map hX.1.aemeasurable (by fun_prop),
    integral_map hX.1.aemeasurable (by fun_prop)]

theorem normalizedHilbertSum_comp_linearIsometryEquiv
    {Ω : Type*} {H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (μ : Measure Ω) (e : H ≃ₗᵢ[ℝ] K)
    (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) :
    normalizedHilbertSum μ (fun i ω => e (X i ω)) n ω =
      e (normalizedHilbertSum μ X n ω) := by
  have hmean : FunctionalData.hilbertExpectation μ (fun ω => e (X 0 ω)) =
      e (FunctionalData.hilbertExpectation μ (X 0)) := by
    exact e.toContinuousLinearEquiv.integral_comp_comm (X 0)
  rw [normalizedHilbertSum, normalizedHilbertSum, hmean]
  simp only [map_smul, map_sub, map_sum]

/--
Euclidean form of the central-limit clause of Theorem `thm:lln-clt-mean`.

Original label: `thm:lln-clt-mean`.

The limit is constructed as the centred multivariate Gaussian whose covariance
matrix represents the source covariance operator.  Lévy's continuity theorem
upgrades the already formalised scalar projection CLTs to weak convergence of
the vector-valued laws. -/
theorem euclidean_central_limit
    {Ω : Type u} {ι : Type*} [Fintype ι]
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ ι),
      IsGaussian (ν : Measure (EuclideanSpace ℝ ι)) ∧
      FunctionalData.hilbertExpectation
        (ν : Measure (EuclideanSpace ℝ ι)) id = 0 ∧
      FunctionalData.covarianceOperator
        (ν : Measure (EuclideanSpace ℝ ι)) id =
          FunctionalData.covarianceOperator μ (X 0) ∧
      TendstoInDistribution
        (normalizedHilbertSum μ X) atTop id (fun _ : ℕ => μ)
          (ν : Measure (EuclideanSpace ℝ ι)) := by
  classical
  let b := EuclideanSpace.basisFun ι ℝ
  let A := FunctionalData.covarianceOperator μ (X 0)
  let S := (LinearMap.toMatrix b.toBasis b.toBasis) A.toLinearMap
  have hA : A.IsPositive :=
    Covariance.covarianceOperator_isPositive_of_memLp_two μ (X 0) hX
  have hS : S.PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).2 hA
  let νm : Measure (EuclideanSpace ℝ ι) := multivariateGaussian 0 S
  let ν : ProbabilityMeasure (EuclideanSpace ℝ ι) :=
    ⟨νm, by infer_instance⟩
  refine ⟨ν, ?_, ?_, ?_, ?_⟩
  · change IsGaussian νm
    infer_instance
  · change ∫ x, id x ∂νm = 0
    exact integral_id_multivariateGaussian
  · change FunctionalData.covarianceOperator νm id = A
    exact gaussian_covarianceOperator_eq A hA
  · have hZmeas (n : ℕ) : AEMeasurable (normalizedHilbertSum μ X n) μ := by
      have hsum : AEMeasurable
          (fun ω => ∑ i ∈ Finset.range n, X i ω) μ :=
        Finset.aemeasurable_fun_sum _ fun i _hi => (hident i).aemeasurable_fst
      change AEMeasurable (fun ω => Real.sqrt n •
        ((n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω) -
          FunctionalData.hilbertExpectation μ (X 0))) μ
      exact ((hsum.const_smul ((n : ℝ)⁻¹)).sub
        aemeasurable_const).const_smul (Real.sqrt n)
    have hweak : Tendsto
        (fun n => (⟨μ.map (normalizedHilbertSum μ X n),
          Measure.isProbabilityMeasure_map (hZmeas n)⟩ :
            ProbabilityMeasure (EuclideanSpace ℝ ι)))
        atTop (@nhds (ProbabilityMeasure (EuclideanSpace ℝ ι))
          ProbabilityMeasure.instTopologicalSpace ν) := by
      apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
      intro t
      have hscalar := scalarProjection_central_limit_gaussianReal
        μ X hX hindep hident t
      have hscalarZ : TendstoInDistribution
          (fun n ω => scalarProjection t (normalizedHilbertSum μ X n ω))
          atTop id (fun _ : ℕ => μ)
          (gaussianReal 0
            Var[(fun ω => scalarProjection t (X 0 ω)); μ].toNNReal) := by
        convert hscalar using 1
        · funext n ω
          exact scalarProjection_normalizedHilbertSum μ X hX n ω t
      have hchar :=
        (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hscalarZ.tendsto) 1
      have hsequence (n : ℕ) :
          charFun (μ.map (normalizedHilbertSum μ X n)) t =
            charFun
              (μ.map (fun ω =>
                scalarProjection t (normalizedHilbertSum μ X n ω))) 1 :=
        charFun_map_eq_scalarProjection_one μ
          (normalizedHilbertSum μ X n) (hZmeas n) t
      have hquad : t.ofLp ⬝ᵥ S.mulVec t.ofLp =
          Var[(fun ω => scalarProjection t (X 0 ω)); μ] := by
        exact matrixQuad_covariance_eq_variance μ (X 0) hX t
      have hlimit :
          charFun
              (gaussianReal 0
                Var[(fun ω => scalarProjection t (X 0 ω)); μ].toNNReal) 1 =
            charFun νm t := by
        rw [charFun_gaussianReal, charFun_multivariateGaussian hS]
        rw [hquad]
        simp
      change Tendsto
        (fun n => charFun (μ.map (normalizedHilbertSum μ X n)) t)
        atTop (𝓝 (charFun νm t))
      rw [show (fun n => charFun (μ.map (normalizedHilbertSum μ X n)) t) =
          (fun n => charFun
            (μ.map (fun ω =>
              scalarProjection t (normalizedHilbertSum μ X n ω))) 1) by
        funext n
        exact hsequence n]
      rw [← hlimit]
      simpa only [Measure.map_id] using hchar
    refine ⟨hZmeas, measurable_id.aemeasurable, ?_⟩
    simpa [ν, νm] using hweak

/--
Finite-dimensional Hilbert-space form of the central-limit clause of Theorem
`thm:lln-clt-mean`.

Original label: `thm:lln-clt-mean`.

An orthonormal basis transports the internally proved Euclidean CLT, including
the Gaussian law, zero mean, covariance operator, and weak convergence. -/
theorem finiteDimensional_hilbert_central_limit
    {Ω : Type u} {H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∃ ν : ProbabilityMeasure H,
      IsGaussian (ν : Measure H) ∧
      FunctionalData.hilbertExpectation (ν : Measure H) id = 0 ∧
      FunctionalData.covarianceOperator (ν : Measure H) id =
        FunctionalData.covarianceOperator μ (X 0) ∧
      TendstoInDistribution
        (normalizedHilbertSum μ X) atTop id (fun _ : ℕ => μ)
          (ν : Measure H) := by
  let b := stdOrthonormalBasis ℝ H
  let Y : ℕ → Ω → EuclideanSpace ℝ (Fin (Module.finrank ℝ H)) :=
    fun i ω => b.repr (X i ω)
  have hY : MemLp (Y 0) 2 μ :=
    memLp_comp_linearIsometryEquiv μ b.repr hX
  have hindepY : iIndepFun Y μ := by
    exact hindep.comp (fun _ => b.repr) (fun _ => b.repr.continuous.measurable)
  have hidentY : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := by
    intro i
    exact (hident i).comp b.repr.continuous.measurable
  obtain ⟨νE, hgaussianE, hmeanE, hcovE, hconvE⟩ :=
    euclidean_central_limit μ Y hY hindepY hidentY
  letI : IsGaussian
      (νE : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ H)))) :=
    hgaussianE
  let e := b.repr.symm
  let νm : Measure H := (νE : Measure _).map e
  let ν : ProbabilityMeasure H :=
    ⟨νm, Measure.isProbabilityMeasure_map e.continuous.aemeasurable⟩
  refine ⟨ν, ?_, ?_, ?_, ?_⟩
  · change IsGaussian νm
    change IsGaussian ((νE : Measure _).map e.toContinuousLinearEquiv)
    infer_instance
  · change ∫ x, id x ∂νm = 0
    change ∫ x, id x ∂((νE : Measure _).map e) = 0
    rw [integral_map e.continuous.aemeasurable (by fun_prop)]
    change ∫ x, e x ∂(νE : Measure _) = 0
    calc
      (∫ x, e x ∂(νE : Measure _)) =
          e (∫ x, id x ∂(νE : Measure _)) := by
        exact e.toContinuousLinearEquiv.integral_comp_comm id
      _ = 0 := by
        change e (FunctionalData.hilbertExpectation (νE : Measure _) id) = 0
        rw [hmeanE, map_zero]
  · change FunctionalData.covarianceOperator νm id =
      FunctionalData.covarianceOperator μ (X 0)
    have hIdE : MemLp
        (id : EuclideanSpace ℝ (Fin (Module.finrank ℝ H)) →
          EuclideanSpace ℝ (Fin (Module.finrank ℝ H)))
        2 (νE : Measure _) := by
      exact ProbabilityTheory.IsGaussian.memLp_two_id
    have he : MemLp e 2 (νE : Measure _) := by
      simpa only [id_eq] using
        (memLp_comp_linearIsometryEquiv (νE : Measure _) e
          (X := id) hIdE)
    calc
      FunctionalData.covarianceOperator νm id =
          FunctionalData.covarianceOperator (νE : Measure _) e := by
        exact covarianceOperator_map_eq (νE : Measure _) e he
      _ = e.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((FunctionalData.covarianceOperator (νE : Measure _) id).comp
            e.symm.toContinuousLinearEquiv.toContinuousLinearMap) :=
        covarianceOperator_comp_linearIsometryEquiv (νE : Measure _) e id hIdE
      _ = e.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((FunctionalData.covarianceOperator μ (Y 0)).comp
            e.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by rw [hcovE]
      _ = FunctionalData.covarianceOperator μ (X 0) := by
        rw [covarianceOperator_comp_linearIsometryEquiv μ b.repr (X 0) hX]
        apply ContinuousLinearMap.ext
        intro x
        simp [e]
  · have hconvMapped := hconvE.continuous_comp e.continuous
    have hsource (n : ℕ) :
        e ∘ normalizedHilbertSum μ Y n = normalizedHilbertSum μ X n := by
      funext ω
      simp only [Function.comp_apply, Y]
      rw [normalizedHilbertSum_comp_linearIsometryEquiv μ b.repr X n ω]
      exact e.apply_symm_apply _
    have hconvSource : TendstoInDistribution
        (normalizedHilbertSum μ X) atTop (e ∘ id)
        (fun _ : ℕ => μ) (νE : Measure _) := by
      apply hconvMapped.congr
      · intro n
        exact Filter.Eventually.of_forall fun ω => congrFun (hsource n) ω
      · exact Filter.Eventually.of_forall fun x => rfl
    refine ⟨hconvSource.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
    convert hconvSource.tendsto using 1
    apply congrArg nhds
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map id νm = Measure.map (e ∘ id) (νE : Measure _)
    simp [νm]

end Thesis.DayAhead.LimitTheorems
