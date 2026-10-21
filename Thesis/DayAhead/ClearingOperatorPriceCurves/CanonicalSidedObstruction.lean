import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedLaws
import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedCurveLp

/-! # Excluding the midpoint from the normalized total canonical image -/

noncomputable section

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation SidedCurveLp Set MeasureTheory

theorem twoThreeAverage_clamp_volume {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (twoThreeAverage (clampParameter x)).1 = (5 / 2 : ℝ) * x := by
  let u : PositiveParameter := ⟨x, hx0, hx1⟩
  rw [show clampParameter x = positiveParameter u by
    simpa [u] using clampParameter_positiveParameter u]
  change (1 / 2 : ℝ) *
    (sidedParametrisationOperator canonicalTwoBlockCurve (positiveParameter u)).1 +
    (1 / 2 : ℝ) *
    (sidedParametrisationOperator canonicalThreeBlockCurve (positiveParameter u)).1 = _
  rw [canonicalTwoBlock_volume (positiveParameter u) hx0,
    canonicalThreeBlock_volume (positiveParameter u) hx0]
  dsimp [u, positiveParameter]
  ring

theorem rightEndpoint_pos_of_canonical_ae_eq_average (f : PriceCurve)
    (hae : (fun x : ℝ => canonicalSidedEncoding f (clampParameter x)) =ᵐ[
      sidedLebesgueMeasure] (fun x => twoThreeAverage (clampParameter x))) :
    0 < f.rightEndpoint := by
  let p := sidedAdmissibleParametrisation (canonicalCertificate f).knots
  let v : ℝ → ℝ := fun x => (p (clampParameter x) : ℝ)
  have hv : Continuous v :=
    continuous_subtype_val.comp (p.continuous.comp continuous_clampParameter)
  have hsub : Ioo (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hlocal : v =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x => (5 / 2 : ℝ) * x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae,
      ae_restrict_mem measurableSet_Ioo] with x hx hxin
    have hx' := congrArg Prod.fst hx
    exact hx'.trans (twoThreeAverage_clamp_volume hxin.1.le hxin.2.le)
  have hpoint := Measure.eqOn_open_of_ae_eq (μ := volume) hlocal isOpen_Ioo
    hv.continuousOn (continuous_const.mul continuous_id).continuousOn
  have hhalf := hpoint (show (1 / 2 : ℝ) ∈ Ioo 0 1 by constructor <;> norm_num)
  have hbound : v (1 / 2) ≤ f.rightEndpoint := (p (clampParameter (1 / 2))).property.2
  rw [hhalf] at hbound
  linarith

/-- No curve, including a curve with a collapsed side, can have a normalized
canonical encoding equal almost everywhere to the explicit midpoint. -/
theorem twoThreeAverage_not_ae_in_canonical_range :
    ¬ ∃ f : PriceCurve, (fun x : ℝ => canonicalSidedEncoding f (clampParameter x)) =ᵐ[
      sidedLebesgueMeasure] (fun x => twoThreeAverage (clampParameter x)) := by
  rintro ⟨f, hf⟩
  have hr := rightEndpoint_pos_of_canonical_ae_eq_average f hf
  apply twoThreeAverage_not_ae_in_minimal_range
  exact ⟨canonicalMinimalSidedCertificate f hr, hf⟩

theorem twoThreeAverage_not_in_canonical_range :
    twoThreeAverage ∉ range canonicalSidedEncoding := by
  rintro ⟨f, hf⟩
  apply twoThreeAverage_not_ae_in_canonical_range
  exact ⟨f, Filter.Eventually.of_forall (fun x => congrFun hf (clampParameter x))⟩

end Thesis.DayAhead.SidedCertificate
