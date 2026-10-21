import Thesis.Appendices.Analysis.SkorokhodTimeChangeMetric
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Completeness of the Skorokhod metric

A rapidly Cauchy subsequence admits consecutive time changes with summable
distortion and path error. Their cumulative products converge in the complete
time-change space, while the aligned paths converge uniformly. Undoing the
limiting time change produces the required regular-path limit.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal NNReal UniformConvergence

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ}

def cumulativeTimeChanges (e : ℕ → IncreasingIntervalBijection a b) :
    ℕ → IncreasingIntervalBijection a b
  | 0 => IncreasingIntervalBijection.refl a b
  | n + 1 => (e n).comp (cumulativeTimeChanges e n)

theorem cumulativeTimeChanges_edist_succ (e : ℕ → IncreasingIntervalBijection a b) (n : ℕ) :
    edist (cumulativeTimeChanges e n) (cumulativeTimeChanges e (n + 1)) = timeDistortion (e n) := by
  rw [edist_comm, IncreasingIntervalBijection.edist_def]
  simp only [cumulativeTimeChanges, IncreasingIntervalBijection.comp_assoc,
    IncreasingIntervalBijection.comp_self_symm, IncreasingIntervalBijection.comp_refl]

variable {X : Type*} [MetricSpace X] [CompleteSpace X] {side : PathOrientation}

theorem regularPath_limit_of_summable_timeChanges (hab : a ≤ b)
    (F : ℕ → RegularPath a b X side) (e : ℕ → IncreasingIntervalBijection a b)
    (r : ℕ → ℝ≥0) (hr : Summable r)
    (he : ∀ n, timeDistortion (e n) ≤ r n)
    (herror : ∀ n, supPathEDistance (F n).val (fun t => (F (n + 1)).val (e n t)) ≤ r n) :
    ∃ f : RegularPath a b X side, ConvergesFor skorokhodEDistance F f := by
  let α := cumulativeTimeChanges e
  let G : ℕ → RegularPath a b X side := fun n => (F n).compTimeChange (α n)
  have hαcauchy : CauchySeq α :=
    cauchySeq_of_edist_le_of_summable r
      (fun n => by simpa only [α, cumulativeTimeChanges_edist_succ] using he n) hr
  letI : CompleteSpace (IncreasingIntervalBijection a b) :=
    IncreasingIntervalBijection.completeSpace hab
  obtain ⟨αlim, hαlim⟩ := cauchySeq_tendsto_of_complete hαcauchy
  have hGstep (n : ℕ) : supPathEDistance (G n).val (G (n + 1)).val ≤ r n := by
    change supPathEDistance (fun t => (F n).val (α n t))
      (fun t => (F (n + 1)).val (e n (α n t))) ≤ r n
    rw [supPathEDistance_comp (F n).val (fun t => (F (n + 1)).val (e n t)) (α n)]
    exact herror n
  have hGcauchy : CauchySeq (fun n => UniformFun.ofFun (G n).val) :=
    cauchySeq_of_edist_le_of_summable r (fun n => by
      simpa only [UniformFun.edist_def, UniformFun.toFun_ofFun,
        ← supPathEDistance_eq_iSup] using hGstep n) hr
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hGcauchy
  have huniform : TendstoUniformly (fun n => (G n).val) (UniformFun.toFun g) atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.mp hg
  let gpath : RegularPath a b X side :=
    ⟨UniformFun.toFun g, isOneSidedRegularPath_of_uniform_limit G huniform⟩
  let f := gpath.compTimeChange αlim.symm
  let correction : ℕ → IncreasingIntervalBijection a b := fun n => αlim.comp (α n).symm
  have hcost : Tendsto (fun n => timeDistortion (correction n)) atTop (𝓝 0) := by
    change Tendsto (fun n => edist αlim (α n)) atTop (𝓝 0)
    simpa only [edist_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => αlim) atTop (𝓝 αlim)).edist hαlim
  have herr_eq (n : ℕ) : supPathEDistance (F n).val (fun t => f.val (correction n t)) =
      supPathEDistance (G n).val gpath.val := by
    rw [← supPathEDistance_comp (F n).val (fun t => f.val (correction n t)) (α n)]
    simp only [f, correction, RegularPath.compTimeChange, IncreasingIntervalBijection.comp_apply,
      IncreasingIntervalBijection.symm_apply_apply]
    rfl
  have herr : Tendsto (fun n => supPathEDistance (F n).val (fun t => f.val (correction n t)))
      atTop (𝓝 0) := by
    simp_rw [herr_eq]
    exact (supPathEDistance_tendsto_zero_iff _ _).mpr huniform
  refine ⟨f, (convergesFor_iff_tendsto _ _ _).mpr ?_⟩
  have hmax := hcost.max herr
  simp only [max_self] at hmax
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmax
    (fun _ => zero_le _) (fun n => skorokhodEDistance_le (F n) f (correction n))

/-- Original label: `prop:skorokhod-metric`.
Completeness requires only completeness of the state space; separability is
not needed for this clause. -/
theorem skorokhodDistance_complete (hab : a ≤ b) (side : PathOrientation) :
    IsCompleteFor (@skorokhodEDistance a b X _ side) := by
  intro F hF
  letI : MetricSpace (RegularPath a b X side) := skorokhodMetricSpace hab side
  letI : UniformSpace (RegularPath a b X side) := (skorokhodMetricSpace hab side).toUniformSpace
  letI : TopologicalSpace (RegularPath a b X side) :=
    (skorokhodMetricSpace hab side).toUniformSpace.toTopologicalSpace
  have hFcauchy : CauchySeq F := (cauchySeq_skorokhod_iff hab F).mpr hF
  let r : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ n
  have hr : Summable r := NNReal.summable_geometric (by norm_num)
  have hrpos (n : ℕ) : 0 < r n := pow_pos (by norm_num) _
  obtain ⟨φ, hφ, hφbound⟩ := Metric.exists_subseq_bounded_of_cauchySeq F hFcauchy
    (fun n => (r n : ℝ)) (fun n => hrpos n)
  have hdist (n : ℕ) : skorokhodEDistance (F (φ n)) (F (φ (n + 1))) ≤ r n := by
    have h := hφbound n (φ (n + 1)) (hφ.monotone (by omega))
    rw [dist_comm] at h
    simpa only [ENNReal.ofReal_coe_nnreal] using (edist_lt_ofReal.mpr h).le
  choose e he using fun n => exists_timeChange_le_add (F (φ n)) (F (φ (n + 1)))
    (ENNReal.coe_pos.mpr (hrpos n))
  have hbound (n : ℕ) : max (timeDistortion (e n))
      (supPathEDistance (F (φ n)).val (fun t => (F (φ (n + 1))).val (e n t))) ≤
      ((2 * r n : ℝ≥0) : ℝ≥0∞) := by
    apply (he n).trans
    calc
      skorokhodEDistance (F (φ n)) (F (φ (n + 1))) + r n ≤ r n + r n :=
        add_le_add (hdist n) le_rfl
      _ = ((2 * r n : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  obtain ⟨f, hf⟩ := regularPath_limit_of_summable_timeChanges hab (fun n => F (φ n)) e
    (fun n => 2 * r n) (hr.mul_left 2)
    (fun n => (le_max_left _ _).trans (hbound n))
    (fun n => (le_max_right _ _).trans (hbound n))
  refine ⟨f, (tendsto_skorokhod_iff hab F f).mp ?_⟩
  apply tendsto_nhds_of_cauchySeq_of_subseq hFcauchy hφ.tendsto_atTop
  exact (tendsto_skorokhod_iff hab (fun n => F (φ n)) f).mpr hf

end Thesis.Foundations.Preliminary.Analysis
