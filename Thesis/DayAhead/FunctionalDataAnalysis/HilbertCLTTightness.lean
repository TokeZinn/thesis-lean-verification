import Thesis.DayAhead.FunctionalDataAnalysis.HilbertCLTMoments
import Thesis.DayAhead.FunctionalDataAnalysis.CompactSpectralExpansion
import Thesis.Foundations.Stochastic.UniformTightness

/-! # Tightness of centered Hilbert-space sums

Finite-dimensional orthogonal projections approximate a square-integrable
random element in mean square. The normalized sums have uniformly bounded
second moments, including after each complementary projection. Markov's
inequality and finite covers of compact projected balls then prove tightness.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Metric
open scoped BigOperators ENNReal NNReal

namespace Thesis.DayAhead.HilbertCLTTightness

open CompactSpectralExpansion HilbertCLTMoments

variable {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H] in
theorem measure_norm_ge_le {Y : Ω → H} (hY : MemLp Y 2 μ) {r ε : ℝ}
    (hr : 0 < r) (hbound : (∫ ω, ‖Y ω‖ ^ 2 ∂μ) ≤ ε * r ^ 2) :
    μ {ω | r ≤ ‖Y ω‖} ≤ ENNReal.ofReal ε := by
  have heq : {ω | r ^ 2 ≤ ‖Y ω‖ ^ 2} = {ω | r ≤ ‖Y ω‖} := by
    ext ω
    exact sq_le_sq₀ hr.le (norm_nonneg _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => sq_nonneg ‖Y ω‖) hY.norm.integrable_sq (r ^ 2)
  rw [heq] at hmarkov
  have hreal : μ.real {ω | r ≤ ‖Y ω‖} ≤ ε := by nlinarith [sq_pos_of_pos hr]
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
theorem partialProjection_isCompact {ι : Type*} (e : ι → H) (s : Finset ι) :
    IsCompactOperator (partialProjection e s) := by
  change partialProjection e s ∈ compactOperator (RingHom.id ℝ) H H
  apply Submodule.sum_mem
  intro i _
  change IsCompactOperator ((ContinuousLinearMap.toSpanSingleton ℝ (e i)) ∘L innerSL ℝ (e i))
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ (e i))).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℝ (e i))

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] [IsProbabilityMeasure μ] in
theorem integral_projection_error_tendsto {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ H) {Y : Ω → H} (hY : MemLp Y 2 μ) :
    Tendsto (fun s : Finset ι => ∫ ω, ‖Y ω - partialProjection b s (Y ω)‖ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  classical
  have hbound (s : Finset ι) (ω : Ω) :
      ‖‖Y ω - partialProjection b s (Y ω)‖ ^ 2‖ ≤ 4 * ‖Y ω‖ ^ 2 := by
    have hnorm := (norm_sub_le (Y ω) (partialProjection b s (Y ω))).trans
      (add_le_add_right (partialProjection_norm_le b b.orthonormal s (Y ω)) _)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (Y ω - partialProjection b s (Y ω)), norm_nonneg (Y ω)]
  have hlim (ω : Ω) : Tendsto (fun s => ‖Y ω - partialProjection b s (Y ω)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have hp := partialProjection_tendsto b b.orthonormal
      (show Y ω ∈ (Submodule.span ℝ (range b)).topologicalClosure from by
        rw [b.dense_span]
        trivial)
    simpa using ((tendsto_const_nhds (x := Y ω)).sub hp).norm.pow 2
  simpa using tendsto_integral_filter_of_dominated_convergence (fun ω => 4 * ‖Y ω‖ ^ 2)
    (Eventually.of_forall fun s =>
      (hY.1.sub ((partialProjection b s).continuous.comp_aestronglyMeasurable hY.1)).norm.pow 2)
    (Eventually.of_forall fun s => ae_of_all μ (hbound s))
    (hY.norm.integrable_sq.const_mul 4) (ae_of_all μ hlim)

theorem normalizedSum_finite_mass_cover {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ H) (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ S : Set H, S.Finite ∧ ∀ n,
      (μ.map (normalizedSum X n)) (thickening r S)ᶜ ≤ ENNReal.ofReal ε := by
  classical
  let C : ℝ := ∫ ω, ‖X 0 ω‖ ^ 2 ∂μ
  obtain ⟨R, hR⟩ := exists_gt (max 1 (C / (ε / 2)))
  have hRone : 1 < R := (le_max_left _ _).trans_lt hR
  have hRpos : 0 < R := zero_lt_one.trans hRone
  have hCR : C ≤ (ε / 2) * R ^ 2 := by
    have hCR' := (div_lt_iff₀ (half_pos hε)).mp ((le_max_right _ _).trans_lt hR)
    have hRsq : R ≤ R ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hRsq (half_pos hε).le]
  obtain ⟨s, hs⟩ := ((integral_projection_error_tendsto b hX).eventually
    (gt_mem_nhds (show 0 < (ε / 2) * (r / 2) ^ 2 by positivity))).exists
  let P := partialProjection b s
  let Q : H →L[ℝ] H := ContinuousLinearMap.id ℝ H - P
  let K := closure (P '' closedBall 0 R)
  have hK : IsCompact K := (partialProjection_isCompact b s).isCompact_closure_image_closedBall R
  obtain ⟨S, _, hS, hcover⟩ := hK.finite_cover_balls (half_pos hr)
  refine ⟨S, hS, fun n => ?_⟩
  let Y := normalizedSum X n
  have hY : MemLp Y 2 μ := normalizedSum_memLp X (fun i => (hident i).memLp_iff.mpr hX) n
  have hnorm : μ {ω | R ≤ ‖Y ω‖} ≤ ENNReal.ofReal (ε / 2) :=
    measure_norm_ge_le hY hRpos
      ((normalizedSum_secondMoment_le X hX hmean hindep hident n).trans hCR)
  have herror : μ {ω | r / 2 ≤ ‖Y ω - P (Y ω)‖} ≤ ENNReal.ofReal (ε / 2) := by
    have hQY : MemLp (fun ω => Q (Y ω)) 2 μ := Q.comp_memLp' hY
    have hmom := normalizedSum_linear_secondMoment_le X hX hmean hindep hident Q n
    exact measure_norm_ge_le hQY (half_pos hr) (hmom.trans hs.le)
  rw [Measure.map_apply_of_aemeasurable hY.1.aemeasurable
    isOpen_thickening.measurableSet.compl]
  have hbad : Y ⁻¹' (thickening r S)ᶜ ⊆
      {ω | R ≤ ‖Y ω‖} ∪ {ω | r / 2 ≤ ‖Y ω - P (Y ω)‖} := by
    intro ω hω
    by_cases hnormω : R ≤ ‖Y ω‖
    · exact Or.inl hnormω
    · right
      by_contra herrω
      have hPY : P (Y ω) ∈ K := subset_closure (mem_image_of_mem P
        (mem_closedBall.mpr (by simpa only [dist_zero_right] using (lt_of_not_ge hnormω).le)))
      obtain ⟨z, hz⟩ := mem_iUnion.mp (hcover hPY)
      obtain ⟨hzS, hzdist⟩ := mem_iUnion.mp hz
      apply hω
      apply mem_thickening_iff.mpr
      refine ⟨z, hzS, ?_⟩
      have hdist : dist (Y ω) (P (Y ω)) < r / 2 := by
        simpa only [dist_eq_norm] using lt_of_not_ge herrω
      have hzdist' := mem_ball.mp hzdist
      linarith [dist_triangle (Y ω) (P (Y ω)) z]
  calc
    μ (Y ⁻¹' (thickening r S)ᶜ) ≤
        μ ({ω | R ≤ ‖Y ω‖} ∪ {ω | r / 2 ≤ ‖Y ω - P (Y ω)‖}) := measure_mono hbad
    _ ≤ μ {ω | R ≤ ‖Y ω‖} + μ {ω | r / 2 ≤ ‖Y ω - P (Y ω)‖} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hnorm herror
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      ring

theorem normalizedSum_isTight (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    IsTightMeasureSet (range fun n => μ.map (normalizedSum X n)) := by
  obtain ⟨I, b, _⟩ := exists_hilbertBasis ℝ H
  letI : Countable I := countable_of_orthonormal b b.orthonormal
  apply Foundations.Stochastic.UniformTightness.of_finite_mass_covers
  intro r ε hr hε
  exact normalizedSum_finite_mass_cover b X hX hmean hindep hident hr hε

end Thesis.DayAhead.HilbertCLTTightness
