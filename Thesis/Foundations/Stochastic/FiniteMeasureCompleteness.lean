import Thesis.Foundations.Stochastic.FiniteMeasureDensity
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! # Completeness of the finite-measure Prokhorov metric

A Prokhorov Cauchy sequence admits uniform finite covers with arbitrarily
small mass outside them. Intersecting closed covers at decreasing scales
proves tightness on a complete base space. Prokhorov compactness then gives
a convergent subsequence, and the Cauchy property gives convergence of the
whole sequence.
-/

noncomputable section

open Set Filter MeasureTheory Topology Metric TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace Thesis.Foundations.Stochastic.FiniteMeasureCompleteness

open FiniteMeasureProkhorov FiniteMeasureDensity

universe u

variable {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X] [OpensMeasurableSpace X]

theorem exists_finite_mass_cover [Nonempty X] [SeparableSpace X]
    (u : ℕ → LP X) (hu : CauchySeq u) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ S : Set X, S.Finite ∧
      ∀ n, (u n).toMeasure.toMeasure (thickening r S)ᶜ ≤ ENNReal.ofReal ε := by
  classical
  let δ : ℝ := min r ε / 3
  have hδ : 0 < δ := div_pos (lt_min hr hε) (by norm_num)
  have hδr : 2 * δ ≤ r := by dsimp [δ]; have := min_le_left r ε; linarith
  have hδε : 2 * δ ≤ ε := by dsimp [δ]; have := min_le_right r ε; linarith
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hu δ hδ
  choose k b x hx using fun j : Fin (N + 1) =>
    exists_atomic_approximation (u j).toMeasure hδ
  let S : Set X := ⋃ j : Fin (N + 1), range (x j)
  have hS : S.Finite := finite_iUnion fun j => finite_range (x j)
  refine ⟨S, hS, fun n => ?_⟩
  have hnear : ∃ j : Fin (N + 1),
      dist (u n) (LevyProkhorov.ofMeasure (atomic (b j) (x j))) < 2 * δ := by
    by_cases hn : n ≤ N
    · exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, (hx _).trans (by linarith)⟩
    · refine ⟨⟨N, Nat.lt_succ_self N⟩, (dist_triangle _ (u N) _).trans_lt ?_⟩
      exact (add_lt_add (hN n (Nat.le_of_lt (Nat.lt_of_not_ge hn))) (hx _)).trans_eq
        (by ring)
  obtain ⟨j, hj⟩ := hnear
  let B : Set X := (thickening r S)ᶜ
  have hB : MeasurableSet B := isOpen_thickening.measurableSet.compl
  have hzero : (atomic (b j) (x j) : Measure X) (thickening (2 * δ) B) = 0 := by
    rw [atomic_apply _ _ isOpen_thickening.measurableSet]
    apply Finset.sum_eq_zero
    intro i _
    have hi : x j i ∉ thickening (2 * δ) B := by
      intro hi
      obtain ⟨z, hz, hdist⟩ := mem_thickening_iff.mp hi
      apply hz
      apply mem_thickening_iff.mpr
      exact ⟨x j i, mem_iUnion.mpr ⟨j, mem_range_self i⟩,
        (by simpa [dist_comm] using hdist.trans_le hδr)⟩
    simp [hi]
  have hed : levyProkhorovEDist (u n).toMeasure.toMeasure
      (atomic (b j) (x j) : Measure X) < ENNReal.ofReal (2 * δ) := by
    change edist (u n) (LevyProkhorov.ofMeasure (atomic (b j) (x j))) < _
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hj
  have hmass := left_measure_le_of_levyProkhorovEDist_lt hed hB
  rw [ENNReal.toReal_ofReal (by positivity), hzero, zero_add] at hmass
  exact hmass.trans (ENNReal.ofReal_le_ofReal hδε)

theorem cauchySeq_isTight [Nonempty X] [SeparableSpace X] [CompleteSpace X]
    (u : ℕ → LP X) (hu : CauchySeq u) :
    IsTightMeasureSet (range fun n => (u n).toMeasure.toMeasure) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, he, hsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  obtain ⟨r, _, hr, hrlim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  choose S hS hmass using fun m => exists_finite_mass_cover u hu (hr m)
    (show 0 < (e m : ℝ) from he m)
  let K : ℕ → Set X := fun m => ⋃ y ∈ S m, closedBall y (r m)
  have hKclosed (m : ℕ) : IsClosed (K m) :=
    (hS m).isClosed_biUnion fun _ _ => isClosed_closedBall
  have hcover (m : ℕ) : thickening (r m) (S m) ⊆ K m := by
    intro z hz
    obtain ⟨y, hy, hdist⟩ := mem_thickening_iff.mp hz
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, mem_closedBall.mpr hdist.le⟩⟩
  have htail (n m : ℕ) : (u n).toMeasure.toMeasure (K m)ᶜ ≤ e m := by
    calc
      _ ≤ (u n).toMeasure.toMeasure (thickening (r m) (S m))ᶜ :=
        measure_mono (compl_subset_compl.mpr (hcover m))
      _ ≤ e m := by simpa only [ENNReal.ofReal_coe_nnreal] using hmass m n
  have hbounded : TotallyBounded (⋂ m, K m) := by
    rw [Metric.totallyBounded_iff]
    intro δ hδ
    obtain ⟨m, hm⟩ := (hrlim.eventually (gt_mem_nhds hδ)).exists
    refine ⟨S m, hS m, fun z hz => ?_⟩
    obtain ⟨y, hy⟩ := mem_iUnion.mp (mem_iInter.mp hz m)
    obtain ⟨hyS, hzy⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hyS, mem_ball.mpr
      ((mem_closedBall.mp hzy).trans_lt hm)⟩⟩
  refine ⟨⋂ m, K m, hbounded.isCompact_of_isClosed (isClosed_iInter hKclosed), ?_⟩
  rintro _ ⟨n, rfl⟩
  calc
    (u n).toMeasure.toMeasure (⋂ m, K m)ᶜ =
        (u n).toMeasure.toMeasure (⋃ m, (K m)ᶜ) := by rw [compl_iInter]
    _ ≤ ∑' m, (u n).toMeasure.toMeasure (K m)ᶜ := measure_iUnion_le _
    _ ≤ ∑' m, (e m : ℝ≥0∞) := ENNReal.tsum_le_tsum (htail n)
    _ ≤ ε := hsum.le

/-- Original label: finite-measure completeness clause of
`thm:prokhorov-metric-weak-convergence-polish`. -/
theorem completeSpace [BorelSpace X] [SeparableSpace X] [CompleteSpace X] [T2Space X] :
    CompleteSpace (LP X) := by
  cases isEmpty_or_nonempty X with
  | inl h =>
    haveI : Subsingleton (LP X) := ⟨fun μ ν => by
      cases μ
      cases ν
      congr 1
      ext B
      rw [show B = ∅ from Set.eq_empty_of_isEmpty B]
      simp⟩
    infer_instance
  | inr h =>
    letI : SeparableSpace (LP X) := FiniteMeasureDensity.separableSpace
    letI : SecondCountableTopology (FiniteMeasure X) :=
      (finiteMeasureHomeomorph (X := X)).secondCountableTopology
    apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    have hmass := mass_lipschitz.uniformContinuous.comp_cauchySeq hu
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hmass
    obtain ⟨C, hC⟩ := ha.bddAbove_range
    obtain ⟨e, _, he, helim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ≥0)
    have htight := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (cauchySeq_isTight u hu)
    choose K hK htail using fun n => htight (e n) (ENNReal.coe_pos.mpr (he n))
    have hcompact := isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le C helim hK
      (Or.inl (inferInstance : NormalSpace X))
    have hmem (n : ℕ) : (u n).toMeasure ∈
        {μ : FiniteMeasure X | μ.mass ≤ C ∧ ∀ m, μ (K m)ᶜ ≤ e m} := by
      refine ⟨hC (mem_range_self n), fun m => ?_⟩
      apply ENNReal.coe_le_coe.mp
      simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        htail m _ (mem_range_self n)
    obtain ⟨ν, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
    refine ⟨LevyProkhorov.ofMeasure ν, tendsto_nhds_of_cauchySeq_of_subseq hu
      hφ.tendsto_atTop ?_⟩
    exact (continuous_ofMeasure.tendsto ν).comp hlim

omit [PseudoMetricSpace X] [OpensMeasurableSpace X] in
theorem probabilityInclusion_range :
    range (probabilityInclusion (X := X)) = {μ : LP X | μ.toMeasure.mass = 1} := by
  ext μ
  constructor
  · rintro ⟨P, rfl⟩
    exact P.toMeasure.mass_toFiniteMeasure
  · intro hμ
    have hmem : μ.toMeasure ∈ range (ProbabilityMeasure.toFiniteMeasure (Ω := X)) := by
      rw [ProbabilityMeasure.range_toFiniteMeasure]
      exact hμ
    obtain ⟨P, hP⟩ := hmem
    exact ⟨LevyProkhorov.ofMeasure P, congrArg LevyProkhorov.ofMeasure hP⟩

theorem probability_completeSpace [BorelSpace X] [SeparableSpace X]
    [CompleteSpace X] [T2Space X] : CompleteSpace (LevyProkhorov (ProbabilityMeasure X)) := by
  letI : CompleteSpace (LP X) := completeSpace
  apply probabilityInclusion_isometry.isUniformInducing.completeSpace
  rw [probabilityInclusion_range]
  exact (isClosed_eq mass_lipschitz.continuous continuous_const).isComplete

theorem probability_separableSpace [SeparableSpace X] :
    SeparableSpace (LevyProkhorov (ProbabilityMeasure X)) := by
  letI : SeparableSpace (LP X) := FiniteMeasureDensity.separableSpace
  have hinc := (probabilityInclusion_isometry (X := X)).isUniformInducing.isInducing
  letI := hinc.secondCountableTopology
  infer_instance

end Thesis.Foundations.Stochastic.FiniteMeasureCompleteness
