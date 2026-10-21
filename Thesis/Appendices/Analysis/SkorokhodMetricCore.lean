import Thesis.Appendices.Analysis.SkorokhodTimeChanges

/-! # Basic Skorokhod distance estimates

The infimum formula is symmetric and satisfies the triangle inequality.
Its convergence implies the uniform time-change criterion in the thesis.
These proofs do not use completeness or separability of the state space.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

section Supremum

variable {a b : ℝ} {X : Type*} [PseudoEMetricSpace X]

theorem supPathEDistance_eq_iSup (f g : ClosedInterval a b → X) :
    supPathEDistance f g = ⨆ t, edist (f t) (g t) := sSup_range

theorem edist_le_supPathEDistance (f g : ClosedInterval a b → X) (t : ClosedInterval a b) :
    edist (f t) (g t) ≤ supPathEDistance f g := le_sSup (mem_range_self t)

theorem supPathEDistance_le_iff (f g : ClosedInterval a b → X) (c : ℝ≥0∞) :
    supPathEDistance f g ≤ c ↔ ∀ t, edist (f t) (g t) ≤ c := by
  simp only [supPathEDistance_eq_iSup, iSup_le_iff]

@[simp] theorem supPathEDistance_self (f : ClosedInterval a b → X) :
    supPathEDistance f f = 0 := by simp [supPathEDistance_eq_iSup]

theorem supPathEDistance_symm (f g : ClosedInterval a b → X) :
    supPathEDistance f g = supPathEDistance g f := by
  simp only [supPathEDistance_eq_iSup, edist_comm]

theorem supPathEDistance_triangle (f g h : ClosedInterval a b → X) :
    supPathEDistance f h ≤ supPathEDistance f g + supPathEDistance g h := by
  rw [supPathEDistance_le_iff]
  intro t
  exact (edist_triangle (f t) (g t) (h t)).trans
    (add_le_add (edist_le_supPathEDistance f g t) (edist_le_supPathEDistance g h t))

theorem supPathEDistance_comp (f g : ClosedInterval a b → X)
    (e : IncreasingIntervalBijection a b) :
    supPathEDistance (fun t => f (e t)) (fun t => g (e t)) = supPathEDistance f g := by
  simp only [supPathEDistance_eq_iSup]
  exact e.bijective.2.iSup_comp (fun t : ClosedInterval a b => edist (f t) (g t))

theorem supPathEDistance_align_symm (f g : ClosedInterval a b → X)
    (e : IncreasingIntervalBijection a b) :
    supPathEDistance g (fun t => f (e.symm t)) =
      supPathEDistance f (fun t => g (e t)) := by
  rw [← supPathEDistance_comp g (fun t => f (e.symm t)) e]
  simp only [IncreasingIntervalBijection.symm_apply_apply]
  exact supPathEDistance_symm _ _

end Supremum

variable {a b : ℝ} {X : Type*} [MetricSpace X] {side : PathOrientation}

theorem skorokhodEDistance_eq_iInf (f g : RegularPath a b X side) :
    skorokhodEDistance f g = ⨅ e : IncreasingIntervalBijection a b,
      max (timeDistortion e) (supPathEDistance f (fun t => g.val (e t))) := sInf_range

theorem skorokhodEDistance_le (f g : RegularPath a b X side)
    (e : IncreasingIntervalBijection a b) :
    skorokhodEDistance f g ≤
      max (timeDistortion e) (supPathEDistance f (fun t => g.val (e t))) :=
  sInf_le (mem_range_self e)

theorem skorokhodEDistance_le_sup (f g : RegularPath a b X side) :
    skorokhodEDistance f g ≤ supPathEDistance f.val g.val := by
  simpa using skorokhodEDistance_le f g (IncreasingIntervalBijection.refl a b)

@[simp] theorem skorokhodEDistance_self (f : RegularPath a b X side) :
    skorokhodEDistance f f = 0 := by
  exact le_antisymm (by simpa using skorokhodEDistance_le_sup f f) (zero_le _)

theorem skorokhodEDistance_symm (f g : RegularPath a b X side) :
    skorokhodEDistance f g = skorokhodEDistance g f := by
  have hle (f g : RegularPath a b X side) : skorokhodEDistance f g ≤ skorokhodEDistance g f := by
    rw [skorokhodEDistance_eq_iInf]
    apply le_iInf
    intro e
    simpa only [timeDistortion_symm, supPathEDistance_align_symm] using
      skorokhodEDistance_le f g e.symm
  exact le_antisymm (hle f g) (hle g f)

theorem skorokhodEDistance_triangle (f g h : RegularPath a b X side) :
    skorokhodEDistance f h ≤ skorokhodEDistance f g + skorokhodEDistance g h := by
  rw [skorokhodEDistance_eq_iInf f g, skorokhodEDistance_eq_iInf g h]
  apply ENNReal.le_iInf_add_iInf
  intro e d
  apply (skorokhodEDistance_le f h (d.comp e)).trans
  apply max_le
  · exact (timeDistortion_comp_le d e).trans (by
      rw [add_comm]
      exact add_le_add (le_max_left _ _) (le_max_left _ _))
  · have herr := supPathEDistance_triangle f (fun t => g.val (e t))
      (fun t => h.val (d (e t)))
    rw [supPathEDistance_comp g (fun t => h.val (d t)) e] at herr
    exact herr.trans (add_le_add (le_max_right _ _) (le_max_right _ _))

theorem convergesFor_iff_tendsto {Z : Type*} (d : Z → Z → ℝ≥0∞)
    (x : ℕ → Z) (z : Z) :
    ConvergesFor d x z ↔ Tendsto (fun n => d (x n) z) atTop (𝓝 0) := by
  rw [ENNReal.nhds_zero_basis.tendsto_right_iff]
  simp only [ConvergesFor, eventually_atTop, mem_Iio]

theorem exists_timeChange_le_add (f g : RegularPath a b X side)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ e : IncreasingIntervalBijection a b,
      max (timeDistortion e) (supPathEDistance f (fun t => g.val (e t))) ≤
        skorokhodEDistance f g + ε := by
  by_cases hd : skorokhodEDistance f g = ∞
  · exact ⟨IncreasingIntervalBijection.refl a b, by simp [hd]⟩
  have hlt : skorokhodEDistance f g < skorokhodEDistance f g + ε :=
    ENNReal.lt_add_right hd hε.ne'
  rw [skorokhodEDistance_eq_iInf] at hlt
  obtain ⟨e, he⟩ := iInf_lt_iff.mp hlt
  exact ⟨e, he.le⟩

/-- Original block id: `source:A - appendices/analysis.tex:504:prop:39`.
The forward time-change criterion, proved for arbitrary metric state spaces. -/
theorem skorokhodConvergence_has_timeChanges (hab : a ≤ b)
    (fseq : ℕ → RegularPath a b X side) (f : RegularPath a b X side)
    (hf : ConvergesFor skorokhodEDistance fseq f) :
    ∃ timeChanges : ℕ → IncreasingIntervalBijection a b,
      Tendsto (fun n => timeShiftNorm (timeChanges n)) atTop (𝓝 0) ∧
        Tendsto (fun n => alignedPathError (fseq n) f (timeChanges n)) atTop (𝓝 0) := by
  let ε : ℕ → ℝ≥0∞ := fun n => ((n : ℝ≥0∞) + 1)⁻¹
  have hε (n : ℕ) : 0 < ε n := ENNReal.inv_pos.mpr (by simp)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  choose e he using fun n => exists_timeChange_le_add (fseq n) f (hε n)
  have hlim : Tendsto (fun n => skorokhodEDistance (fseq n) f + ε n) atTop (𝓝 0) := by
    simpa only [add_zero] using ((convergesFor_iff_tendsto _ _ _).mp hf).add hεlim
  have hdist : Tendsto (fun n => timeDistortion (e n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le _) (fun n => (le_max_left _ _).trans (he n))
  have herr : Tendsto (fun n => supPathEDistance (fseq n) (fun t => f.val (e n t)))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le _) (fun n => (le_max_right _ _).trans (he n))
  refine ⟨fun n => (e n).symm, ?_, ?_⟩
  · simpa only [timeShiftNorm_symm] using timeShiftNorm_tendsto_zero hab e hdist
  · have heq (n : ℕ) : alignedPathError (fseq n) f (e n).symm =
        supPathEDistance (fseq n) (fun t => f.val (e n t)) := by
      change supPathEDistance (fun t => (fseq n).val ((e n).symm t)) f = _
      rw [supPathEDistance_symm, supPathEDistance_align_symm]
    simpa only [heq] using herr

end Thesis.Foundations.Preliminary.Analysis
