import Thesis.Appendices.Analysis.SkorokhodInterpolation

/-! # The reverse Skorokhod time-change criterion

For a fixed accuracy, choose finitely many cuts of the limiting path.
Interpolate the given time changes at those cuts with small logarithmic
distortion. The residual time change fixes the cuts, hence changes the
limiting path by at most the chosen oscillation tolerance.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ} {X : Type*} [MetricSpace X] {side : PathOrientation}

theorem skorokhodEDistance_le_aligned (f g : RegularPath a b X side)
    (e : IncreasingIntervalBijection a b) :
    skorokhodEDistance f g ≤ max (timeDistortion e) (alignedPathError f g e) := by
  rw [skorokhodEDistance_symm]
  simpa only [supPathEDistance, alignedPathError, edist_comm] using skorokhodEDistance_le g f e

theorem alignedPathError_interpolation_le (f g : RegularPath a b X side)
    (e d : IncreasingIntervalBijection a b) {ε : ℝ≥0∞}
    (hosc : supPathEDistance g.val (fun t => g.val ((e.symm.comp d) t)) ≤ ε) :
    alignedPathError f g d ≤ alignedPathError f g e + ε := by
  let residual := e.symm.comp d
  have hfirst : supPathEDistance (fun t => f.val (d t)) (fun t => g.val (residual t)) =
      alignedPathError f g e := by
    have h := supPathEDistance_comp (fun t => f.val (e t)) g.val residual
    simpa only [residual, IncreasingIntervalBijection.comp_apply,
      IncreasingIntervalBijection.apply_symm_apply] using h
  have hsecond : supPathEDistance (fun t => g.val (residual t)) g.val ≤ ε := by
    rw [supPathEDistance_symm]
    exact hosc
  have h := supPathEDistance_triangle (fun t => f.val (d t))
    (fun t => g.val (residual t)) g.val
  rw [hfirst] at h
  exact h.trans (add_le_add le_rfl hsecond)

/-- Original block id: `source:A - appendices/analysis.tex:504:prop:39`.
The reverse implication is valid for arbitrary metric state spaces. -/
theorem skorokhodConvergence_of_timeChanges_core (hab : a ≤ b)
    (F : ℕ → RegularPath a b X side) (f : RegularPath a b X side)
    (e : ℕ → IncreasingIntervalBijection a b)
    (hshift : Tendsto (fun n => timeShiftNorm (e n)) atTop (𝓝 0))
    (herror : Tendsto (fun n => alignedPathError (F n) f (e n)) atTop (𝓝 0)) :
    ConvergesFor skorokhodEDistance F f := by
  intro ε hε
  obtain ⟨r, _, hrpos, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hrpos
  have hthird : 0 < r / 3 := by positivity
  obtain ⟨S, ha, hb, hS, hosc⟩ := regularPath_small_error_of_fixes_cuts hab f hthird
  obtain ⟨η, hη, hinterp⟩ := finite_timeChange_interpolation hab S ha hb hS hthird
  have hshift' := hshift.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  have herror' := herror.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hthird))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hshift'.and herror')
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨d, hdist, hmatch⟩ := hinterp (e n) (hN n hn).1.le
  have hfix : ∀ t : ClosedInterval a b, (t : ℝ) ∈ S → ((e n).symm.comp d) t = t := by
    intro t ht
    simp only [IncreasingIntervalBijection.comp_apply, hmatch t ht,
      IncreasingIntervalBijection.symm_apply_apply]
  have herr := alignedPathError_interpolation_le (F n) f (e n) d (hosc _ hfix)
  apply lt_of_le_of_lt ?_ hrε
  apply (skorokhodEDistance_le_aligned (F n) f d).trans
  apply max_le
  · exact hdist.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · apply herr.trans
    calc
      alignedPathError (F n) f (e n) + ENNReal.ofReal (r / 3) ≤
          ENNReal.ofReal (r / 3) + ENNReal.ofReal (r / 3) :=
        add_le_add (hN n hn).2.le le_rfl
      _ = ENNReal.ofReal (r / 3 + r / 3) :=
        (ENNReal.ofReal_add hthird.le hthird.le).symm
      _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal (by linarith)

end Thesis.Foundations.Preliminary.Analysis
