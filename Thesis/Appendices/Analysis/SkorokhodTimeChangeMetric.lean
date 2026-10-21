import Thesis.Appendices.Analysis.SkorokhodTimeChangeLimits

/-! # The logarithmic metric on time changes

The distortion of the relative time change is a right-invariant extended
metric. Cauchy sequences with bounded distortion converge in this metric.
Normalizing a Cauchy tail supplies such a bound and proves completeness.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal UniformConvergence

namespace Thesis.Foundations.Preliminary.Analysis

namespace IncreasingIntervalBijection

variable {a b : ℝ}

@[simp] theorem comp_self_symm (e : IncreasingIntervalBijection a b) :
    e.comp e.symm = refl a b := by
  apply ext
  intro t
  simp

@[simp] theorem symm_comp_self (e : IncreasingIntervalBijection a b) :
    e.symm.comp e = refl a b := by
  apply ext
  intro t
  simp

@[simp] theorem comp_refl (e : IncreasingIntervalBijection a b) : e.comp (refl a b) = e := by
  apply ext
  intro t
  rfl

@[simp] theorem refl_comp (e : IncreasingIntervalBijection a b) : (refl a b).comp e = e := by
  apply ext
  intro t
  rfl

theorem comp_assoc (e d c : IncreasingIntervalBijection a b) :
    (e.comp d).comp c = e.comp (d.comp c) := by
  apply ext
  intro t
  rfl

@[simp] theorem symm_comp (e d : IncreasingIntervalBijection a b) :
    (e.comp d).symm = d.symm.comp e.symm := by
  apply ext
  intro t
  apply (e.comp d).bijective.1
  rw [apply_symm_apply]
  simp

@[simp] theorem symm_symm (e : IncreasingIntervalBijection a b) : e.symm.symm = e := by
  apply ext
  intro t
  apply e.symm.bijective.1
  simp

instance instEMetricSpace (a b : ℝ) : EMetricSpace (IncreasingIntervalBijection a b) where
  edist e d := timeDistortion (e.comp d.symm)
  edist_self e := by simp
  edist_comm e d := by rw [← timeDistortion_symm, symm_comp, symm_symm]
  edist_triangle e d c := by
    have h := timeDistortion_comp_le (e.comp d.symm) (d.comp c.symm)
    simpa only [comp_assoc, ← comp_assoc d.symm d, symm_comp_self, refl_comp] using h
  eq_of_edist_eq_zero := by
    intro e d h
    by_cases hab : a ≤ b
    · have he := (timeDistortion_eq_zero_iff hab (e.comp d.symm)).mp h
      apply ext
      intro t
      have ht := congrArg (fun k : IncreasingIntervalBijection a b => k (d t)) he
      simpa using ht
    · apply ext
      intro t
      exact False.elim (hab (t.property.1.trans t.property.2))

theorem edist_def (e d : IncreasingIntervalBijection a b) :
    edist e d = timeDistortion (e.comp d.symm) := rfl

theorem edist_comp_right (e d c : IncreasingIntervalBijection a b) :
    edist (e.comp c) (d.comp c) = edist e d := by
  simp only [edist_def, symm_comp, comp_assoc, ← comp_assoc c c.symm,
    comp_self_symm, refl_comp]

theorem isometry_comp_right (c : IncreasingIntervalBijection a b) :
    Isometry (fun e : IncreasingIntervalBijection a b => e.comp c) :=
  fun e d => edist_comp_right e d c

theorem uniform_edist_le_shift (e d : IncreasingIntervalBijection a b) :
    edist (UniformFun.ofFun e.toFun) (UniformFun.ofFun d.toFun) ≤
      timeShiftNorm (e.comp d.symm) := by
  rw [UniformFun.edist_le]
  intro t
  have h : ENNReal.ofReal |((e.comp d.symm) (d t) : ℝ) - d t| ≤
      timeShiftNorm (e.comp d.symm) := le_sSup (mem_range_self (d t))
  simpa only [comp_apply, symm_apply_apply, edist_dist, Subtype.dist_eq, Real.dist_eq] using h

theorem cauchySeq_uniformFun (hab : a ≤ b) {e : ℕ → IncreasingIntervalBijection a b}
    (he : CauchySeq e) : CauchySeq (fun n => UniformFun.ofFun (e n).toFun) := by
  rw [EMetric.cauchySeq_iff_NNReal]
  intro ε hε
  have hεreal : (0 : ℝ) < ε := hε
  let L := b - a
  have hL : 0 ≤ L := sub_nonneg.mpr hab
  let c := Real.log (1 + (ε : ℝ) / (L + 1))
  have hc : 0 < c := Real.log_pos (by
    have h := div_pos hεreal (show 0 < L + 1 by positivity)
    linarith)
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp he (ENNReal.ofReal c) (ENNReal.ofReal_pos.mpr hc)
  refine ⟨N, fun n hn => ?_⟩
  have hrel := hN n hn N le_rfl
  have hshift := timeShiftNorm_le_of_distortion_le hab ((e n).comp (e N).symm) hc.le hrel.le
  apply ((uniform_edist_le_shift (e n) (e N)).trans hshift).trans_lt
  have hc_exp : Real.exp c = 1 + (ε : ℝ) / (L + 1) := Real.exp_log (by positivity)
  rw [hc_exp]
  change ENNReal.ofReal ((1 + (ε : ℝ) / (L + 1) - 1) * L) < ε
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hεreal]
  have hden : 0 < L + 1 := by positivity
  have hdiv : (ε : ℝ) / (L + 1) * L < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  simpa only [add_sub_cancel_left] using hdiv

theorem cauchySeq_tendsto_of_distortion_bounded (hab : a ≤ b)
    {e : ℕ → IncreasingIntervalBijection a b} (he : CauchySeq e)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ n, timeDistortion (e n) ≤ ENNReal.ofReal c) :
    ∃ g : IncreasingIntervalBijection a b, Tendsto e atTop (𝓝 g) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_uniformFun hab he)
  have huniform : TendstoUniformly (fun n => (e n).toFun) (UniformFun.toFun g) atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.mp hg
  let limit := ofUniformLimit e huniform hc hbound
  refine ⟨limit, EMetric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp he δ hδ
  refine ⟨N, fun n hn => ?_⟩
  rw [edist_comm, edist_def]
  apply lt_of_le_of_lt ?_ hδε
  apply timeDistortion_le_of_tendsto_ennreal (fun m => (e m).comp (e n).symm)
    (limit.comp (e n).symm)
  · intro t
    exact huniform.tendsto_at ((e n).symm t)
  · filter_upwards [eventually_ge_atTop N] with m hm
    exact (hN m hm n hn).le

theorem completeSpace (hab : a ≤ b) : CompleteSpace (IncreasingIntervalBijection a b) := by
  apply EMetric.complete_of_cauchySeq_tendsto
  intro e he
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp he 1 zero_lt_one
  let relative : ℕ → IncreasingIntervalBijection a b :=
    fun n => (e (n + N)).comp (e N).symm
  have hrelative : CauchySeq relative :=
    (isometry_comp_right (e N).symm).uniformContinuous.comp_cauchySeq
      (he.comp_tendsto (tendsto_add_atTop_nat N))
  have hbound (n : ℕ) : timeDistortion (relative n) ≤ ENNReal.ofReal 1 := by
    simpa only [ENNReal.ofReal_one] using (hN (n + N) (by omega) N le_rfl).le
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_distortion_bounded hab hrelative zero_le_one hbound
  refine ⟨g.comp (e N), (tendsto_add_atTop_iff_nat N).mp ?_⟩
  have h := (isometry_comp_right (e N)).continuous.tendsto g |>.comp hg
  simpa only [relative, Function.comp_def, comp_assoc, symm_comp_self, comp_refl] using h

end IncreasingIntervalBijection

end Thesis.Foundations.Preliminary.Analysis
