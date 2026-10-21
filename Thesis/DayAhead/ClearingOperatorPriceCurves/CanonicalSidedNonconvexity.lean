import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedObstruction
import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedWitnesses
import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedLp

/-! # Non-convexity of the current normalized canonical encoder

The two witnesses are encoded by the total construction, including its
essential-representative normalization. Their midpoint is excluded from the
whole canonical image even after passing to almost-everywhere equivalence.
-/

noncomputable section

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation SidedCurveLp Set Filter MeasureTheory
open Foundations.Stochastic.KernelHilbert

/-- Original label: `cor:sided-parametrisation-not-weakly-convex`.
The full normalized canonical image fails midpoint closure even almost everywhere. -/
theorem canonicalSidedEncoding_not_weaklyConvexAE :
    ¬ IsWeaklyConvexAE canonicalSidedEncoding := by
  intro hweak
  obtain ⟨h, hh⟩ := hweak twoBlockCurve threeBlockCurve (1 / 2) (1 / 2)
    (by norm_num) (by norm_num)
  apply twoThreeAverage_not_ae_in_canonical_range
  refine ⟨h, ?_⟩
  filter_upwards [hh, canonicalTwo_ae_eq_legacy, canonicalThree_ae_eq_legacy]
    with x hx htwo hthree
  simpa only [representativeCombination, htwo, hthree, twoThreeAverage] using hx

/-- Original label: `cor:sided-parametrisation-not-weakly-convex`.
The actual total canonical encoder is not weakly convex. -/
theorem canonicalSidedEncoding_not_weaklyConvex :
    ¬ IsWeaklyConvex canonicalSidedEncoding := by
  intro hweak
  apply canonicalSidedEncoding_not_weaklyConvexAE
  intro f g α β hα hβ
  obtain ⟨h, hh⟩ := hweak f g α β hα hβ
  exact ⟨h, Eventually.of_forall (fun x => congrFun hh (clampParameter x))⟩

/-- Original label: `cor:sided-parametrisation-not-weakly-convex`. -/
theorem range_canonicalSidedEncoding_not_convexCone :
    ¬ ConvexCone (range canonicalSidedEncoding) := by
  intro hcone
  apply canonicalSidedEncoding_not_weaklyConvex
  intro f g α β hα hβ
  obtain ⟨h, hh⟩ := hcone ⟨f, rfl⟩ ⟨g, rfl⟩ hα hβ
  exact ⟨h, hh⟩

theorem range_essentialSidedEncoding :
    range essentialSidedEncoding = range canonicalSidedEncoding := by
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f.toEssential, canonicalSidedEncoding_essential f⟩

/-- Original label: `cor:sided-parametrisation-not-weakly-convex`.
The same failure holds on the thesis's domain of essential curves. -/
theorem range_essentialSidedEncoding_not_convexCone :
    ¬ ConvexCone (range essentialSidedEncoding) := by
  rw [range_essentialSidedEncoding]
  exact range_canonicalSidedEncoding_not_convexCone

theorem essentialSidedEncoding_not_weaklyConvex :
    ¬ IsWeaklyConvex essentialSidedEncoding := by
  intro hweak
  apply canonicalSidedEncoding_not_weaklyConvex
  intro f g α β hα hβ
  obtain ⟨h, hh⟩ := hweak f.toEssential g.toEssential α β hα hβ
  refine ⟨h.val, ?_⟩
  simpa only [essentialSidedEncoding, PriceCurve.toEssential,
    canonicalSidedEncoding_essential] using hh

end Thesis.DayAhead.SidedCertificate

namespace Thesis.DayAhead.CanonicalSidedLp

open PriceCurves SidedParametrisation SidedCurveLp SidedCertificate PriceCurveHilbert
open Set Filter MeasureTheory Foundations.Stochastic.KernelHilbert

/-- Original label: `cor:sided-parametrisation-not-weakly-convex`.
The full normalized canonical Hilbert encoder fails weak convexity. -/
theorem canonicalSidedEncodingLpReal_not_weaklyConvex :
    ¬ WeaklyConvexOperator PriceCurve (PriceHilbertSpace sidedLebesgueMeasure)
      canonicalSidedEncodingLpReal := by
  intro hweak
  apply canonicalSidedEncoding_not_weaklyConvexAE
  intro f g α β hα hβ
  obtain ⟨h, hh⟩ := hweak hα hβ f g
  refine ⟨h, ?_⟩
  filter_upwards [coeFn_canonicalSidedEncodingLpReal h,
    coeFn_canonicalSidedEncodingLpReal f, coeFn_canonicalSidedEncodingLpReal g,
    Lp.coeFn_add (α • canonicalSidedEncodingLpReal f) (β • canonicalSidedEncodingLpReal g),
    Lp.coeFn_smul α (canonicalSidedEncodingLpReal f),
    Lp.coeFn_smul β (canonicalSidedEncodingLpReal g)] with x hH hF hG hadd hsmulF hsmulG
  apply pairEquiv.injective
  have hx := congrArg (fun v : PriceHilbertSpace sidedLebesgueMeasure => v x) hh
  dsimp only at hx
  dsimp only [Pi.add_apply, Pi.smul_apply] at hadd hsmulF hsmulG
  rw [hH, hadd, hsmulF, hsmulG, hF, hG] at hx
  simpa only [representativeCombination, map_add, map_smul] using hx

/-- Original label: `cor:sided-parametrisation-not-weakly-convex`. -/
theorem range_canonicalSidedEncodingLpReal_not_convexCone :
    ¬ ConvexCone (range canonicalSidedEncodingLpReal) := by
  intro hcone
  exact canonicalSidedEncodingLpReal_not_weaklyConvex
    ((weaklyConvexOperator_iff_range_convexCone canonicalSidedEncodingLpReal).mpr hcone)

theorem range_essentialSidedEncodingLpReal :
    range essentialSidedEncodingLpReal = range canonicalSidedEncodingLpReal := by
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f.toEssential, canonicalSidedEncodingLpReal_essential f⟩

/-- Original label: `cor:sided-parametrisation-not-weakly-convex`. -/
theorem range_essentialSidedEncodingLpReal_not_convexCone :
    ¬ ConvexCone (range essentialSidedEncodingLpReal) := by
  rw [range_essentialSidedEncodingLpReal]
  exact range_canonicalSidedEncodingLpReal_not_convexCone

theorem essentialSidedEncodingLpReal_not_weaklyConvex :
    ¬ WeaklyConvexOperator EssentialPriceCurve (PriceHilbertSpace sidedLebesgueMeasure)
      essentialSidedEncodingLpReal := by
  intro hweak
  apply canonicalSidedEncodingLpReal_not_weaklyConvex
  intro α β hα hβ f g
  obtain ⟨h, hh⟩ := hweak hα hβ f.toEssential g.toEssential
  refine ⟨h.val, ?_⟩
  simpa only [essentialSidedEncodingLpReal, PriceCurve.toEssential,
    canonicalSidedEncodingLpReal_essential] using hh

end Thesis.DayAhead.CanonicalSidedLp
