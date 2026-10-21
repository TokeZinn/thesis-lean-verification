import Thesis.Foundations.Stochastic.FiniteMeasureProkhorov
import Mathlib.MeasureTheory.Measure.DiracProba

/-! # Finite atomic measures are dense in the Prokhorov topology

A countable measurable partition into sets of small diameter gives an atomic
approximation. Keeping finitely many cells loses arbitrarily little mass.
The finite atomic parameter spaces are separable, giving separability of the
whole finite-measure space.
-/

noncomputable section

open Set Filter MeasureTheory Topology Metric
open scoped ENNReal NNReal BigOperators

namespace Thesis.Foundations.Stochastic.FiniteMeasureDensity

open FiniteMeasureProkhorov

universe u

variable {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X] [OpensMeasurableSpace X]

def atomic {n : ℕ} (b : Fin n → ℝ≥0) (x : Fin n → X) : FiniteMeasure X :=
  ∑ i, b i • (diracProba (x i)).toFiniteMeasure

omit [PseudoMetricSpace X] [OpensMeasurableSpace X] in
open Classical in
theorem atomic_apply {n : ℕ} (b : Fin n → ℝ≥0) (x : Fin n → X)
    {B : Set X} (hB : MeasurableSet B) :
    (atomic b x : Measure X) B = ∑ i, if x i ∈ B then (b i : ℝ≥0∞) else 0 := by
  classical
  simp only [atomic, FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul,
    Measure.finset_sum_apply, Measure.coe_nnreal_smul_apply,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    diracProba_toMeasure_apply' _ hB, Set.indicator_apply, Pi.one_apply, mul_ite,
    mul_one, mul_zero]

theorem continuous_atomic (n : ℕ) :
    Continuous (fun p : (Fin n → ℝ≥0) × (Fin n → X) => atomic p.1 p.2) := by
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply i).comp continuous_fst).smul
    (ProbabilityMeasure.toFiniteMeasure_continuous.comp
      (continuous_diracProba.comp ((continuous_apply i).comp continuous_snd)))

theorem approximation_bound {n : ℕ} (μ : FiniteMeasure X) (E : Fin n → Set X)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (x : Fin n → X) (hx : ∀ i, (E i).Nonempty → x i ∈ E i)
    (δ : ℝ) (hδ : 0 < δ) (hdiam : ∀ i, Bornology.IsBounded (E i) ∧ diam (E i) ≤ δ)
    (htail : (μ : Measure X) (⋃ i, E i)ᶜ ≤ ENNReal.ofReal δ) :
    levyProkhorovEDist (μ : Measure X) (atomic (fun i => μ (E i)) x : Measure X) ≤
      ENNReal.ofReal δ := by
  classical
  let U := ⋃ i, E i
  have hU : MeasurableSet U := MeasurableSet.iUnion hE
  have hsum (B : Set X) (hB : MeasurableSet B) :
      (μ : Measure X) (B ∩ U) = ∑ i, (μ : Measure X) (B ∩ E i) := by
    rw [show B ∩ U = ⋃ i, B ∩ E i from inter_iUnion B E,
      measure_iUnion (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right)
        (fun i => hB.inter (hE i)), tsum_fintype]
  apply levyProkhorovEDist_le_of_forall
  intro ε B hδε hεtop hB
  have hδεreal : δ < ε.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hδ.le hεtop.ne).mp hδε
  have hcoord (i : Fin n) (y : X) (hy : y ∈ E i) : dist y (x i) < ε.toReal :=
    ((dist_le_diam_of_mem (hdiam i).1 hy (hx i ⟨y, hy⟩)).trans (hdiam i).2).trans_lt hδεreal
  have htB : MeasurableSet (thickening ε.toReal B) := isOpen_thickening.measurableSet
  constructor
  · rw [atomic_apply _ _ htB]
    calc
      (μ : Measure X) B = (μ : Measure X) (B ∩ U) + (μ : Measure X) (B \ U) :=
        (measure_inter_add_diff B hU).symm
      _ ≤ (∑ i, if x i ∈ thickening ε.toReal B then (↑(μ (E i)) : ℝ≥0∞) else 0) +
          (μ : Measure X) Uᶜ := by
        apply add_le_add
        · rw [hsum B hB]
          apply Finset.sum_le_sum
          intro i _
          by_cases hnon : (B ∩ E i).Nonempty
          · obtain ⟨y, hyB, hyE⟩ := hnon
            have hxi : x i ∈ thickening ε.toReal B :=
              mem_thickening_iff.mpr ⟨y, hyB, by simpa [dist_comm] using hcoord i y hyE⟩
            simpa [hxi, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
              (measure_mono inter_subset_right : (μ : Measure X) (B ∩ E i) ≤ (μ : Measure X) (E i))
          · simp [Set.not_nonempty_iff_eq_empty.mp hnon]
        · exact measure_mono (diff_subset_compl B U)
      _ ≤ _ := add_le_add le_rfl (htail.trans hδε.le)
  · rw [atomic_apply _ _ hB]
    apply le_add_of_le_left
    calc
      (∑ i, if x i ∈ B then (↑(μ (E i)) : ℝ≥0∞) else 0) ≤
          ∑ i, (μ : Measure X) (thickening ε.toReal B ∩ E i) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hxi : x i ∈ B
        · have hsub : E i ⊆ thickening ε.toReal B :=
            fun y hy => mem_thickening_iff.mpr ⟨x i, hxi, hcoord i y hy⟩
          simp [hxi, inter_eq_right.mpr hsub, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        · simp [hxi]
      _ = (μ : Measure X) (thickening ε.toReal B ∩ U) := (hsum _ htB).symm
      _ ≤ _ := measure_mono inter_subset_left

theorem exists_atomic_approximation [Nonempty X] [TopologicalSpace.SeparableSpace X]
    (μ : FiniteMeasure X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (b : Fin n → ℝ≥0) (x : Fin n → X),
      dist (LevyProkhorov.ofMeasure μ) (LevyProkhorov.ofMeasure (atomic b x)) < ε := by
  classical
  obtain ⟨E, hE, hbdd, hdiam, hcover, hdisj⟩ :=
    MeasureTheory.SeparableSpace.exists_measurable_partition_diam_le X (half_pos hε)
  obtain ⟨N, hN⟩ : ∃ N, (μ : Measure X) (⋃ j ∈ Iio N, E j)ᶜ < ENNReal.ofReal (ε / 2) := by
    have exhaust := @tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint X _ (μ : Measure X) _
      E (fun n => (hE n).nullMeasurableSet) hdisj
    obtain ⟨N, hN⟩ := eventually_atTop.mp (exhaust.eventually_lt_const
      (ENNReal.ofReal_pos.mpr (half_pos hε)))
    refine ⟨N, ?_⟩
    have hcompl := biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ hcover hdisj (Iio N)
    rw [hcompl]
    simpa only [Function.comp_apply, compl_Iio, mem_Ici] using hN N le_rfl
  let x : Fin N → X := fun i => if h : (E i.val).Nonempty then h.choose else Classical.arbitrary X
  have hx (i : Fin N) (hi : (E i.val).Nonempty) : x i ∈ E i.val := by
    simp only [x, dif_pos hi]
    exact hi.choose_spec
  have hU : (⋃ i : Fin N, E i.val) = ⋃ j ∈ Iio N, E j := by
    ext y
    simp only [mem_iUnion, mem_Iio]
    exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.isLt, hi⟩, fun ⟨j, hj, hy⟩ => ⟨⟨j, hj⟩, hy⟩⟩
  have hbound := approximation_bound μ (fun i : Fin N => E i.val) (fun i => hE i.val)
    (fun i j hij => hdisj (fun heq => hij (Fin.ext heq))) x hx (ε / 2) (half_pos hε)
    (fun i => ⟨hbdd i.val, hdiam i.val⟩) (by simpa only [hU] using hN.le)
  refine ⟨N, (fun i => μ (E i.val)), x, ?_⟩
  have hdist := ENNReal.toReal_le_of_le_ofReal (half_pos hε).le hbound
  exact hdist.trans_lt (half_lt_self hε)

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`.
All finite measures form a separable Prokhorov space whenever the base is
separable. Finite atomic approximations give a dense continuous image of
a countable union of finite-product parameter spaces. -/
theorem separableSpace [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (LP X) := by
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
    let F : (Σ n : ℕ, (Fin n → ℝ≥0) × (Fin n → X)) → LP X :=
      fun p => LevyProkhorov.ofMeasure (atomic p.2.1 p.2.2)
    have hF : Continuous F := continuous_sigma fun n =>
      FiniteMeasureProkhorov.continuous_ofMeasure.comp (continuous_atomic n)
    have hdense : DenseRange F := by
      rw [Metric.denseRange_iff]
      intro μ ε hε
      obtain ⟨n, b, x, h⟩ := exists_atomic_approximation μ.toMeasure hε
      exact ⟨⟨n, b, x⟩, h⟩
    exact hdense.separableSpace hF

end Thesis.Foundations.Stochastic.FiniteMeasureDensity
