import Thesis.Appendices.MeasureTheory.MeasureTheory
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Recovering regular representatives from almost-everywhere classes -/

noncomputable section

open Set Filter Topology MeasureTheory

namespace Thesis.Foundations.Preliminary.MeasureTheory

variable {V : Type*} [TopologicalSpace V] [T2Space V]
  {a b : ℝ} {f g : ℝ → V}

/-- Original label: `rem:lp-point-evaluation`.
Continuity recovers both endpoints on a nondegenerate interval. -/
theorem continuous_eqOn_of_ae_eq (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (h : f =ᵐ[volume.restrict (Icc a b)] g) : EqOn f g (Icc a b) :=
  Measure.eqOn_Icc_of_ae_eq (μ := volume) hab.ne h hf hg

/-- Right continuity recovers every point except the terminal point. -/
theorem rightContinuous_eqOn_of_ae_eq
    (hf : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b ∩ Ici x) x)
    (hg : ∀ x ∈ Icc a b, ContinuousWithinAt g (Icc a b ∩ Ici x) x)
    (h : f =ᵐ[volume.restrict (Icc a b)] g) : EqOn f g (Ico a b) := by
  intro x hx
  by_contra hne
  have hn : {y | f y ≠ g y} ∈ 𝓝[Icc a b ∩ Ici x] x :=
    ((hf x ⟨hx.1, hx.2.le⟩).prodMk_nhds (hg x ⟨hx.1, hx.2.le⟩))
      (isClosed_diagonal.isOpen_compl.mem_nhds hne)
  have hs : Icc a b ∩ Ici x = Icc x b := by
    ext y
    simp only [mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · tauto
    · intro hy
      exact ⟨⟨hx.1.trans hy.1, hy.2⟩, hy.1⟩
  rw [hs, nhdsWithin_Icc_eq_nhdsGE hx.2] at hn
  obtain ⟨c, hxc, hc⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hn
  have hd : x < min c b := lt_min hxc hx.2
  have hsub : Ioo x (min c b) ⊆ Icc a b := fun y hy =>
    ⟨hx.1.trans hy.1.le, hy.2.le.trans (min_le_right _ _)⟩
  obtain ⟨y, hy, he⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_Ioo.measure_ne_zero volume (nonempty_Ioo.mpr hd))
    (ae_restrict_of_ae_restrict_of_subset hsub h)
  exact hc ⟨hy.1.le, hy.2.trans_le (min_le_left _ _)⟩ he

/-- Left continuity recovers every point except the initial point. -/
theorem leftContinuous_eqOn_of_ae_eq
    (hf : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b ∩ Iic x) x)
    (hg : ∀ x ∈ Icc a b, ContinuousWithinAt g (Icc a b ∩ Iic x) x)
    (h : f =ᵐ[volume.restrict (Icc a b)] g) : EqOn f g (Ioc a b) := by
  intro x hx
  by_contra hne
  have hn : {y | f y ≠ g y} ∈ 𝓝[Icc a b ∩ Iic x] x :=
    ((hf x ⟨hx.1.le, hx.2⟩).prodMk_nhds (hg x ⟨hx.1.le, hx.2⟩))
      (isClosed_diagonal.isOpen_compl.mem_nhds hne)
  have hs : Icc a b ∩ Iic x = Icc a x := by
    ext y
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · tauto
    · intro hy
      exact ⟨⟨hy.1, hy.2.trans hx.2⟩, hy.2⟩
  rw [hs, nhdsWithin_Icc_eq_nhdsLE hx.1] at hn
  obtain ⟨c, hcx, hc⟩ := mem_nhdsLE_iff_exists_Ioc_subset.mp hn
  have hd : max c a < x := max_lt hcx hx.1
  have hsub : Ioo (max c a) x ⊆ Icc a b := fun y hy =>
    ⟨(le_max_right _ _).trans hy.1.le, hy.2.le.trans hx.2⟩
  obtain ⟨y, hy, he⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_Ioo.measure_ne_zero volume (nonempty_Ioo.mpr hd))
    (ae_restrict_of_ae_restrict_of_subset hsub h)
  exact hc ⟨(le_max_left _ _).trans_lt hy.1, hy.2.le⟩ he

/-- Original label: `rem:lp-point-evaluation`.
A càdlàg representative and its terminal value determine the entire path. -/
theorem cadlag_eqOn_of_ae_eq_of_terminal
    (hf : IsCadlagOn f (Icc a b)) (hg : IsCadlagOn g (Icc a b))
    (h : f =ᵐ[volume.restrict (Icc a b)] g) (hb : f b = g b) :
    EqOn f g (Icc a b) := by
  intro x hx
  rcases hx.2.lt_or_eq with hxb | rfl
  · exact rightContinuous_eqOn_of_ae_eq hf.1 hg.1 h ⟨hx.1, hxb⟩
  · exact hb

/-- Original label: `rem:lp-point-evaluation`.
A càglàd representative and its initial value determine the entire path. -/
theorem caglad_eqOn_of_ae_eq_of_initial
    (hf : IsCagladOn f (Icc a b)) (hg : IsCagladOn g (Icc a b))
    (h : f =ᵐ[volume.restrict (Icc a b)] g) (ha : f a = g a) :
    EqOn f g (Icc a b) := by
  intro x hx
  rcases hx.1.lt_or_eq with hax | rfl
  · exact leftContinuous_eqOn_of_ae_eq hf.1 hg.1 h ⟨hax, hx.2⟩
  · exact ha

end Thesis.Foundations.Preliminary.MeasureTheory
