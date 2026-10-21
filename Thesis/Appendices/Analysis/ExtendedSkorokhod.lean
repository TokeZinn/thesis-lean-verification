import Thesis.Appendices.Analysis.Analysis
import Thesis.Appendices.Analysis.ExtendedAnalysis

/-! # Skorokhod paths over extended metric spaces

Regularity is unchanged by truncating the state metric. The Skorokhod
distance below still uses the original extended distances in its exact
formula. Its small balls agree with those for the truncated state metric.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

universe u v

theorem smallError_truncated_iff {I : Type v} {X : Type u} [EMetricSpace X]
    (P : ℝ → I → Prop) (f g : I → X) :
    (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ i, P δ i →
      @dist X (BoundedMetric.truncatedMetricSpace X).toDist (f i) (g i) < ε) ↔
    (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ i, P δ i →
      edist (f i) (g i) < ENNReal.ofReal ε) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hbound⟩ := h (min ε 1) (lt_min hε zero_lt_one)
    refine ⟨δ, hδ, fun i hi ↦ ?_⟩
    have hmin : min (edist (f i) (g i)) 1 < ENNReal.ofReal (min ε 1) :=
      @edist_lt_ofReal X (BoundedMetric.truncatedMetricSpace X).toPseudoMetricSpace
        (f i) (g i) (min ε 1) |>.mpr (hbound i hi)
    have hle : ENNReal.ofReal (min ε 1) ≤ 1 := by
      rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
      exact min_le_right _ _
    exact ((min_lt_iff.mp hmin).resolve_right (not_lt_of_ge hle)).trans_le
      (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  · intro h ε hε
    obtain ⟨δ, hδ, hbound⟩ := h ε hε
    refine ⟨δ, hδ, fun i hi ↦ ?_⟩
    apply (@edist_lt_ofReal X (BoundedMetric.truncatedMetricSpace X).toPseudoMetricSpace
      (f i) (g i) ε).mp
    exact (min_le_left _ _).trans_lt (hbound i hi)

/-- Original block id: `source:A - appendices/analysis.tex:425:defn:35`.
The same one-sided paths, represented using a bounded metric with the
original uniformity. The four equivalences below certify the original
extended-distance epsilon conditions. -/
abbrev ExtendedRegularPath (a b : ℝ) (X : Type u) [EMetricSpace X]
    (side : PathOrientation) :=
  @RegularPath a b X (BoundedMetric.truncatedMetricSpace X).toPseudoMetricSpace side

variable {a b : ℝ} {X : Type u} [EMetricSpace X]

/-- Original block id: `source:A - appendices/analysis.tex:425:defn:35`. -/
theorem extended_rightContinuous_iff (f : ClosedInterval a b → X) :
    @IsRightContinuousOnIcc X (BoundedMetric.truncatedMetricSpace X).toPseudoMetricSpace a b f ↔
      ∀ t₀ : ClosedInterval a b, (t₀ : ℝ) < b → ∀ ε > (0 : ℝ),
        ∃ δ > (0 : ℝ), ∀ t : ClosedInterval a b,
          (t₀ : ℝ) < t → (t : ℝ) < min ((t₀ : ℝ) + δ) b →
            edist (f t) (f t₀) < ENNReal.ofReal ε := by
  unfold IsRightContinuousOnIcc
  apply forall_congr'
  intro t₀
  apply forall_congr'
  intro _
  simpa only [and_imp] using smallError_truncated_iff
    (fun (δ : ℝ) (t : ClosedInterval a b) ↦ (t₀ : ℝ) < t ∧ (t : ℝ) < min ((t₀ : ℝ) + δ) b)
    f (fun _ ↦ f t₀)

/-- Original block id: `source:A - appendices/analysis.tex:425:defn:35`. -/
theorem extended_leftContinuous_iff (f : ClosedInterval a b → X) :
    @IsLeftContinuousOnIcc X (BoundedMetric.truncatedMetricSpace X).toPseudoMetricSpace a b f ↔
      ∀ t₀ : ClosedInterval a b, a < (t₀ : ℝ) → ∀ ε > (0 : ℝ),
        ∃ δ > (0 : ℝ), ∀ t : ClosedInterval a b,
          max a ((t₀ : ℝ) - δ) < t → (t : ℝ) < t₀ →
            edist (f t) (f t₀) < ENNReal.ofReal ε := by
  unfold IsLeftContinuousOnIcc
  apply forall_congr'
  intro t₀
  apply forall_congr'
  intro _
  simpa only [and_imp] using smallError_truncated_iff
    (fun (δ : ℝ) (t : ClosedInterval a b) ↦ max a ((t₀ : ℝ) - δ) < t ∧ (t : ℝ) < t₀)
    f (fun _ ↦ f t₀)

/-- Original block id: `source:A - appendices/analysis.tex:425:defn:35`. -/
theorem extended_rightLimits_iff (f : ClosedInterval a b → X) :
    @HasRightLimitsOnIcc X (BoundedMetric.truncatedMetricSpace X).toPseudoMetricSpace a b f ↔
      ∀ t₀ : ClosedInterval a b, (t₀ : ℝ) < b → ∃ R : X, ∀ ε > (0 : ℝ),
        ∃ δ > (0 : ℝ), ∀ t : ClosedInterval a b,
          (t₀ : ℝ) < t → (t : ℝ) < min ((t₀ : ℝ) + δ) b →
            edist (f t) R < ENNReal.ofReal ε := by
  unfold HasRightLimitsOnIcc
  apply forall_congr'
  intro t₀
  apply forall_congr'
  intro _
  apply exists_congr
  intro R
  simpa only [and_imp] using smallError_truncated_iff
    (fun (δ : ℝ) (t : ClosedInterval a b) ↦ (t₀ : ℝ) < t ∧ (t : ℝ) < min ((t₀ : ℝ) + δ) b)
    f (fun _ ↦ R)

/-- Original block id: `source:A - appendices/analysis.tex:425:defn:35`. -/
theorem extended_leftLimits_iff (f : ClosedInterval a b → X) :
    @HasLeftLimitsOnIcc X (BoundedMetric.truncatedMetricSpace X).toPseudoMetricSpace a b f ↔
      ∀ t₀ : ClosedInterval a b, a < (t₀ : ℝ) → ∃ L : X, ∀ ε > (0 : ℝ),
        ∃ δ > (0 : ℝ), ∀ t : ClosedInterval a b,
          max a ((t₀ : ℝ) - δ) < t → (t : ℝ) < t₀ →
            edist (f t) L < ENNReal.ofReal ε := by
  unfold HasLeftLimitsOnIcc
  apply forall_congr'
  intro t₀
  apply forall_congr'
  intro _
  apply exists_congr
  intro L
  simpa only [and_imp] using smallError_truncated_iff
    (fun (δ : ℝ) (t : ClosedInterval a b) ↦ max a ((t₀ : ℝ) - δ) < t ∧ (t : ℝ) < t₀)
    f (fun _ ↦ L)

theorem supPathEDistance_truncated (f g : ClosedInterval a b → X) :
    @supPathEDistance a b X (BoundedMetric.truncatedMetricSpace X).toPseudoEMetricSpace f g =
      min (supPathEDistance f g) 1 := by
  simp only [supPathEDistance_eq_iSup, BoundedMetric.truncated_edist]
  exact (iSup_inf_eq _ _).symm

variable {side : PathOrientation}

/-- The manuscript's original distance, without truncating either the time
distortion or the spatial error. It can be infinite. -/
def extendedSkorokhodEDistance (f g : ExtendedRegularPath a b X side) : ℝ≥0∞ :=
  ⨅ e : IncreasingIntervalBijection a b,
    max (timeDistortion e) (supPathEDistance f.val (fun t ↦ g.val (e t)))

theorem extendedSkorokhod_small_lt_iff (f g : ExtendedRegularPath a b X side)
    {ε : ℝ≥0∞} (hε : ε ≤ 1) :
    @skorokhodEDistance a b X (BoundedMetric.truncatedMetricSpace X) side f g < ε ↔
      extendedSkorokhodEDistance f g < ε := by
  rw [@skorokhodEDistance_eq_iInf a b X (BoundedMetric.truncatedMetricSpace X) side f g,
    extendedSkorokhodEDistance]
  simp only [iInf_lt_iff, max_lt_iff, supPathEDistance_truncated, min_lt_iff,
    not_lt_of_ge hε, or_false]

theorem cauchyFor_of_small_lt {Z : Type*} {d e : Z → Z → ℝ≥0∞}
    (h : ∀ x y ε, ε ≤ 1 → d x y < ε → e x y < ε)
    {F : ℕ → Z} (hF : IsCauchyFor d F) : IsCauchyFor e F := by
  intro ε hε
  obtain ⟨N, hN⟩ := hF (min ε 1) (lt_min hε zero_lt_one)
  exact ⟨N, fun m hm n hn ↦
    (h _ _ _ (min_le_right _ _) (hN m hm n hn)).trans_le (min_le_left _ _)⟩

theorem convergesFor_of_small_lt {Z : Type*} {d e : Z → Z → ℝ≥0∞}
    (h : ∀ x y ε, ε ≤ 1 → d x y < ε → e x y < ε)
    {F : ℕ → Z} {f : Z} (hF : ConvergesFor d F f) : ConvergesFor e F f := by
  intro ε hε
  obtain ⟨N, hN⟩ := hF (min ε 1) (lt_min hε zero_lt_one)
  exact ⟨N, fun n hn ↦
    (h _ _ _ (min_le_right _ _) (hN n hn)).trans_le (min_le_left _ _)⟩

theorem separableFor_of_small_lt {Z : Type*} {d e : Z → Z → ℝ≥0∞}
    (h : ∀ x y ε, ε ≤ 1 → d x y < ε → e x y < ε)
    (hd : IsSeparableFor d) : IsSeparableFor e := by
  obtain ⟨D, hD, hdense⟩ := hd
  refine ⟨D, hD, fun x ε hε ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := hdense x (min ε 1) (lt_min hε zero_lt_one)
  exact ⟨y, hy, (h _ _ _ (min_le_right _ _) hxy).trans_le (min_le_left _ _)⟩

theorem extendedSkorokhod_le (f g : ExtendedRegularPath a b X side)
    (e : IncreasingIntervalBijection a b) :
    extendedSkorokhodEDistance f g ≤
      max (timeDistortion e) (supPathEDistance f.val (fun t ↦ g.val (e t))) :=
  iInf_le _ e

theorem truncatedSkorokhod_le_extended (f g : ExtendedRegularPath a b X side) :
    @skorokhodEDistance a b X (BoundedMetric.truncatedMetricSpace X) side f g ≤
      extendedSkorokhodEDistance f g := by
  rw [@skorokhodEDistance_eq_iInf a b X (BoundedMetric.truncatedMetricSpace X) side f g,
    extendedSkorokhodEDistance]
  apply iInf_mono
  intro e
  rw [supPathEDistance_truncated]
  exact max_le_max le_rfl (min_le_left _ _)

theorem extendedSkorokhod_self (f : ExtendedRegularPath a b X side) :
    extendedSkorokhodEDistance f f = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa only [IncreasingIntervalBijection.refl_apply, timeDistortion_refl,
    supPathEDistance_self, max_self] using
      extendedSkorokhod_le f f (IncreasingIntervalBijection.refl a b)

theorem extendedSkorokhod_symm (f g : ExtendedRegularPath a b X side) :
    extendedSkorokhodEDistance f g = extendedSkorokhodEDistance g f := by
  have hle (f g : ExtendedRegularPath a b X side) :
      extendedSkorokhodEDistance f g ≤ extendedSkorokhodEDistance g f := by
    apply le_iInf
    intro e
    simpa only [timeDistortion_symm, supPathEDistance_align_symm] using
      extendedSkorokhod_le f g e.symm
  exact le_antisymm (hle f g) (hle g f)

theorem extendedSkorokhod_triangle (f g h : ExtendedRegularPath a b X side) :
    extendedSkorokhodEDistance f h ≤
      extendedSkorokhodEDistance f g + extendedSkorokhodEDistance g h := by
  unfold extendedSkorokhodEDistance
  apply ENNReal.le_iInf_add_iInf
  intro e d
  apply (extendedSkorokhod_le f h (d.comp e)).trans
  apply max_le
  · exact (timeDistortion_comp_le d e).trans (by
      rw [add_comm]
      exact add_le_add (le_max_left _ _) (le_max_left _ _))
  · have herr := supPathEDistance_triangle f.val (fun t ↦ g.val (e t))
      (fun t ↦ h.val (d (e t)))
    rw [supPathEDistance_comp g.val (fun t ↦ h.val (d t)) e] at herr
    exact herr.trans (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- Original label: `prop:skorokhod-metric`.
The metric-axiom clause for every extended metric state space, without
completeness or separability assumptions. -/
theorem extendedSkorokhod_isExtendedMetric (hab : a ≤ b) (side : PathOrientation) :
    IsExtendedMetric (@extendedSkorokhodEDistance a b X _ side) := by
  refine ⟨fun f g ↦ ⟨?_, ?_⟩, extendedSkorokhod_symm, extendedSkorokhod_triangle⟩
  · intro hfg
    have ht : @skorokhodEDistance a b X (BoundedMetric.truncatedMetricSpace X) side f g = 0 :=
      le_antisymm (hfg ▸ truncatedSkorokhod_le_extended f g) (zero_le _)
    exact (@skorokhodEDistance_eq_zero_iff a b X
      (BoundedMetric.truncatedMetricSpace X) hab side f g).mp ht
  · rintro rfl
    exact extendedSkorokhod_self _

/-- Original label: `prop:skorokhod-metric`.
Completeness for the exact original extended-distance formula. -/
theorem extendedSkorokhod_complete [CompleteSpace X] (hab : a ≤ b) (side : PathOrientation) :
    IsCompleteFor (@extendedSkorokhodEDistance a b X _ side) := by
  intro F hF
  have hF' := cauchyFor_of_small_lt
    (fun f g _ hε ↦ (extendedSkorokhod_small_lt_iff f g hε).mpr) hF
  obtain ⟨f, hf⟩ := @skorokhodDistance_complete a b X
    (BoundedMetric.truncatedMetricSpace X) (BoundedMetric.truncated_complete X) hab side F hF'
  exact ⟨f, convergesFor_of_small_lt
    (fun f g _ hε ↦ (extendedSkorokhod_small_lt_iff f g hε).mp) hf⟩

/-- Original label: `prop:skorokhod-metric`.
Separability for the exact original extended-distance formula. -/
theorem extendedSkorokhod_separable [TopologicalSpace.SeparableSpace X]
    (hab : a ≤ b) (side : PathOrientation) :
    IsSeparableFor (@extendedSkorokhodEDistance a b X _ side) :=
  separableFor_of_small_lt
    (fun f g _ hε ↦ (extendedSkorokhod_small_lt_iff f g hε).mp)
    (@skorokhodDistance_separable_core a b X (BoundedMetric.truncatedMetricSpace X)
      hab (BoundedMetric.truncated_separable X) side)

theorem tendsto_truncated_zero_iff {I : Type*} {l : Filter I} (f : I → ℝ≥0∞) :
    Tendsto (fun i ↦ min (f i) 1) l (𝓝 0) ↔ Tendsto f l (𝓝 0) := by
  rw [ENNReal.nhds_zero_basis.tendsto_right_iff,
    ENNReal.nhds_zero_basis.tendsto_right_iff]
  constructor
  · intro h ε hε
    filter_upwards [h (min ε 1) (lt_min hε zero_lt_one)] with i hi
    change min (f i) 1 < min ε 1 at hi
    change f i < ε
    exact ((min_lt_iff.mp hi).resolve_right
      (not_lt_of_ge (min_le_right _ _))).trans_le (min_le_left _ _)
  · intro h ε hε
    filter_upwards [h ε hε] with i hi
    change f i < ε at hi
    change min (f i) 1 < ε
    exact (min_le_left _ _).trans_lt hi

def extendedAlignedPathError (g f : ExtendedRegularPath a b X side)
    (e : IncreasingIntervalBijection a b) : ℝ≥0∞ :=
  supPathEDistance (fun t ↦ g.val (e t)) f.val

theorem alignedPathError_truncated (g f : ExtendedRegularPath a b X side)
    (e : IncreasingIntervalBijection a b) :
    @alignedPathError a b X (BoundedMetric.truncatedMetricSpace X) side g f e =
      min (extendedAlignedPathError g f e) 1 :=
  supPathEDistance_truncated _ _

/-- Original block id: `source:A - appendices/analysis.tex:504:prop:39`.
Both implications of the time-change criterion, retaining the original
extended distances in the Skorokhod and aligned-error formulas. -/
theorem extendedSkorokhodConvergence_iff_timeChanges
    (hab : a < b) (side : PathOrientation)
    (F : ℕ → ExtendedRegularPath a b X side) (f : ExtendedRegularPath a b X side) :
    ConvergesFor (@extendedSkorokhodEDistance a b X _ side) F f ↔
      ∃ e : ℕ → IncreasingIntervalBijection a b,
        Tendsto (fun n ↦ timeShiftNorm (e n)) atTop (𝓝 0) ∧
          Tendsto (fun n ↦ extendedAlignedPathError (F n) f (e n)) atTop (𝓝 0) := by
  have hconv : ConvergesFor (@extendedSkorokhodEDistance a b X _ side) F f ↔
      ConvergesFor (@skorokhodEDistance a b X (BoundedMetric.truncatedMetricSpace X) side)
        F f :=
    ⟨convergesFor_of_small_lt
        (fun f g _ hε ↦ (extendedSkorokhod_small_lt_iff f g hε).mpr),
      convergesFor_of_small_lt
        (fun f g _ hε ↦ (extendedSkorokhod_small_lt_iff f g hε).mp)⟩
  rw [hconv, @skorokhodConvergence_iff_timeChanges a b hab X
    (BoundedMetric.truncatedMetricSpace X) side F f]
  apply exists_congr
  intro e
  simp only [alignedPathError_truncated, tendsto_truncated_zero_iff]

/-- The completeness assertion in the paragraph preceding the increasing
interval bijection definition, with the original extended supremum metric. -/
theorem extendedRegularPath_sup_complete [CompleteSpace X] (side : PathOrientation) :
    IsCompleteFor (fun f g : ExtendedRegularPath a b X side ↦
      supPathEDistance f.val g.val) := by
  have hsmall (f g : ExtendedRegularPath a b X side) (ε : ℝ≥0∞) (hε : ε ≤ 1) :
      @supPathEDistance a b X (BoundedMetric.truncatedMetricSpace X).toPseudoEMetricSpace
        f.val g.val < ε ↔ supPathEDistance f.val g.val < ε := by
    rw [supPathEDistance_truncated, min_lt_iff]
    simp only [not_lt_of_ge hε, or_false]
  intro F hF
  have hF' := cauchyFor_of_small_lt (fun f g ε hε ↦ (hsmall f g ε hε).mpr) hF
  obtain ⟨f, hf⟩ := @regularPath_sup_complete a b X (BoundedMetric.truncatedMetricSpace X)
    (BoundedMetric.truncated_complete X) side F hF'
  exact ⟨f, convergesFor_of_small_lt (fun f g ε hε ↦ (hsmall f g ε hε).mp) hf⟩

end Thesis.Foundations.Preliminary.Analysis
