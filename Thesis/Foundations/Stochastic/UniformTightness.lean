import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Uniform finite covers imply tightness

In a complete metric space, uniform finite covers with arbitrarily small
mass tails give tightness. This form applies both to Prokhorov Cauchy
sequences and to finite-dimensional approximations of Hilbert-valued laws.
-/

noncomputable section

open Set Filter MeasureTheory Topology Metric
open scoped ENNReal NNReal

namespace Thesis.Foundations.Stochastic.UniformTightness

theorem of_finite_mass_covers {X ι : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [CompleteSpace X] (μ : ι → Measure X)
    (hcovers : ∀ (r ε : ℝ), 0 < r → 0 < ε →
      ∃ S : Set X, S.Finite ∧ ∀ i, μ i (thickening r S)ᶜ ≤ ENNReal.ofReal ε) :
    IsTightMeasureSet (range μ) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, he, hsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  obtain ⟨r, _, hr, hrlim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  choose S hS hmass using fun m => hcovers (r m) (e m) (hr m)
    (show 0 < (e m : ℝ) from he m)
  let K : ℕ → Set X := fun m => ⋃ y ∈ S m, closedBall y (r m)
  have hKclosed (m : ℕ) : IsClosed (K m) :=
    (hS m).isClosed_biUnion fun _ _ => isClosed_closedBall
  have hcover (m : ℕ) : thickening (r m) (S m) ⊆ K m := by
    intro z hz
    obtain ⟨y, hy, hdist⟩ := mem_thickening_iff.mp hz
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, mem_closedBall.mpr hdist.le⟩⟩
  have htail (i : ι) (m : ℕ) : μ i (K m)ᶜ ≤ e m := by
    calc
      _ ≤ μ i (thickening (r m) (S m))ᶜ := measure_mono (compl_subset_compl.mpr (hcover m))
      _ ≤ e m := by simpa only [ENNReal.ofReal_coe_nnreal] using hmass m i
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
  rintro _ ⟨i, rfl⟩
  calc
    μ i (⋂ m, K m)ᶜ = μ i (⋃ m, (K m)ᶜ) := by rw [compl_iInter]
    _ ≤ ∑' m, μ i (K m)ᶜ := measure_iUnion_le _
    _ ≤ ∑' m, (e m : ℝ≥0∞) := ENNReal.tsum_le_tsum (htail i)
    _ ≤ ε := hsum.le

end Thesis.Foundations.Stochastic.UniformTightness
