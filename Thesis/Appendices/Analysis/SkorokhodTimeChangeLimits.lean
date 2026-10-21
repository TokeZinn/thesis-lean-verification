import Thesis.Appendices.Analysis.SkorokhodUniform
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Limits of time changes with bounded logarithmic distortion

A common distortion bound prevents increasing time changes from collapsing
an interval in the limit. Uniform limits are therefore still increasing
bijections, and the distortion bound passes to the limit.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal UniformConvergence

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ}

theorem timeChange_increment_lower (e : IncreasingIntervalBijection a b)
    {c : ℝ} (hc : 0 ≤ c) (he : timeDistortion e ≤ ENNReal.ofReal c)
    {s t : ClosedInterval a b} (hst : s ≤ t) :
    (t : ℝ) - s ≤ Real.exp c * ((e t : ℝ) - e s) := by
  have h := timeChange_increment_le e.symm hc (by simpa using he)
    (e.strictMono.monotone hst)
  simpa only [IncreasingIntervalBijection.symm_apply_apply] using h

theorem timeChange_uniformLimit_strictMono (e : ℕ → IncreasingIntervalBijection a b)
    {g : ClosedInterval a b → ClosedInterval a b}
    (hg : TendstoUniformly (fun n => (e n).toFun) g atTop)
    {c : ℝ} (hc : 0 ≤ c) (he : ∀ n, timeDistortion (e n) ≤ ENNReal.ofReal c) :
    StrictMono g := by
  intro s t hst
  have hval (x : ClosedInterval a b) : Tendsto (fun n => (e n x : ℝ)) atTop (𝓝 (g x : ℝ)) :=
    continuous_subtype_val.tendsto _ |>.comp (hg.tendsto_at x)
  have hlim := ((hval t).sub (hval s)).const_mul (Real.exp c)
  have h := ge_of_tendsto' hlim (fun n => timeChange_increment_lower (e n) hc (he n) hst.le)
  change (g s : ℝ) < g t
  have hst' : (s : ℝ) < t := hst
  have hexp := Real.exp_pos c
  nlinarith

theorem timeChange_uniformLimit_surjective (e : ℕ → IncreasingIntervalBijection a b)
    {g : ClosedInterval a b → ClosedInterval a b}
    (hg : TendstoUniformly (fun n => (e n).toFun) g atTop) : Function.Surjective g := by
  have hgcont : Continuous g :=
    hg.continuous (Eventually.of_forall fun n => (e n).continuous).frequently
  intro y
  choose x hx using fun n => (e n).bijective.2 y
  obtain ⟨z, _, φ, hφ, hz⟩ :=
    (isCompact_univ : IsCompact (univ : Set (ClosedInterval a b))).tendsto_subseq
      (fun n => mem_univ (x n))
  have hsub : TendstoUniformly (fun n => (e (φ n)).toFun) g atTop := by
    rw [EMetric.tendstoUniformly_iff] at hg ⊢
    exact fun ε hε => hφ.tendsto_atTop.eventually (hg ε hε)
  have hlim := hsub.tendsto_comp hgcont.continuousAt hz
  have heq : (fun n => e (φ n) (x (φ n))) = fun _ : ℕ => y := funext fun n => hx (φ n)
  simp only [Function.comp_apply] at hlim
  rw [heq] at hlim
  exact ⟨z, (tendsto_nhds_unique tendsto_const_nhds hlim).symm⟩

def IncreasingIntervalBijection.ofUniformLimit (e : ℕ → IncreasingIntervalBijection a b)
    {g : ClosedInterval a b → ClosedInterval a b}
    (hg : TendstoUniformly (fun n => (e n).toFun) g atTop)
    {c : ℝ} (hc : 0 ≤ c) (he : ∀ n, timeDistortion (e n) ≤ ENNReal.ofReal c) :
    IncreasingIntervalBijection a b where
  toFun := g
  strictMono := timeChange_uniformLimit_strictMono e hg hc he
  bijective := ⟨(timeChange_uniformLimit_strictMono e hg hc he).injective,
    timeChange_uniformLimit_surjective e hg⟩

theorem timeDistortion_le_of_tendsto (e : ℕ → IncreasingIntervalBijection a b)
    (g : IncreasingIntervalBijection a b)
    (hg : ∀ t, Tendsto (fun n => e n t) atTop (𝓝 (g t)))
    {c : ℝ} (hc : 0 ≤ c) (he : ∀ᶠ n in atTop, timeDistortion (e n) ≤ ENNReal.ofReal c) :
    timeDistortion g ≤ ENNReal.ofReal c := by
  rw [timeDistortion_le_iff]
  intro s t hst
  have hval (x : ClosedInterval a b) : Tendsto (fun n => (e n x : ℝ)) atTop (𝓝 (g x : ℝ)) :=
    continuous_subtype_val.tendsto _ |>.comp (hg x)
  have hslope : Tendsto (fun n => timeChangeSecantSlope (e n) s t) atTop
      (𝓝 (timeChangeSecantSlope g s t)) := ((hval t).sub (hval s)).div_const _
  have hlog :=
    ((Real.continuousAt_log (timeChangeSecantSlope_pos g hst).ne').tendsto.comp hslope).abs
  apply ENNReal.ofReal_le_ofReal
  apply le_of_tendsto hlog
  filter_upwards [he] with n hn
  exact (ENNReal.ofReal_le_ofReal_iff hc).mp ((logSecant_le_timeDistortion (e n) hst).trans hn)

theorem timeDistortion_ofUniformLimit_le (e : ℕ → IncreasingIntervalBijection a b)
    {g : ClosedInterval a b → ClosedInterval a b}
    (hg : TendstoUniformly (fun n => (e n).toFun) g atTop)
    {c : ℝ} (hc : 0 ≤ c) (he : ∀ n, timeDistortion (e n) ≤ ENNReal.ofReal c) :
    timeDistortion (IncreasingIntervalBijection.ofUniformLimit e hg hc he) ≤ ENNReal.ofReal c :=
  timeDistortion_le_of_tendsto e _ hg.tendsto_at hc (Eventually.of_forall he)

theorem timeDistortion_le_of_tendsto_ennreal (e : ℕ → IncreasingIntervalBijection a b)
    (g : IncreasingIntervalBijection a b)
    (hg : ∀ t, Tendsto (fun n => e n t) atTop (𝓝 (g t)))
    {c : ℝ≥0∞} (he : ∀ᶠ n in atTop, timeDistortion (e n) ≤ c) : timeDistortion g ≤ c := by
  by_cases hc : c = ∞
  · simp [hc]
  · have h := timeDistortion_le_of_tendsto e g hg (c := c.toReal) ENNReal.toReal_nonneg
      (by simpa only [ENNReal.ofReal_toReal hc] using he)
    simpa only [ENNReal.ofReal_toReal hc] using h

end Thesis.Foundations.Preliminary.Analysis
