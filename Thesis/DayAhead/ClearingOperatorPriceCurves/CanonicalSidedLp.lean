import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedEncoding
import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedCurveLp

/-!
# Canonical sided `L²` encoding of price curves

This module maps the current essential-representative encoder into the
ambient Euclidean-valued `L²` space. The total map on `PriceCurve` first
normalizes isolated knot values, as specified in the current chapter.
-/

namespace Thesis.DayAhead.CanonicalSidedLp

open MeasureTheory
open PriceCurves SidedParametrisation SidedCertificate SidedCurveLp PriceCurveHilbert

noncomputable section

/--
Thesis source: the Hilbert-valued operator in Definition
`defn:parametrisation-operator`.

Original label: `defn:parametrisation-operator`.

The canonical sided encoding of the selected essential representative as an
ambient Euclidean-valued `L²` element.
-/
noncomputable def canonicalSidedEncodingLp
    (μ : Measure Parameter) [IsFiniteMeasure μ]
    (f : PriceCurve) : PriceCurveLpSpace μ :=
  sidedParametrisationLp μ (canonicalCertificate f)

/-- The selected representative of the canonical `L²` encoding agrees almost
everywhere with the total actual encoder. -/
theorem coeFn_canonicalSidedEncodingLp
    (μ : Measure Parameter) [IsFiniteMeasure μ]
    (f : PriceCurve) :
    ((canonicalSidedEncodingLp μ f : PriceCurveLpSpace μ) :
        Parameter → PricePair) =ᵐ[μ] (fun u => pairEquiv (canonicalSidedEncoding f u)) := by
  exact coeFn_sidedParametrisationLp μ (canonicalCertificate f)

/-- Normalizing twice gives the same Hilbert encoding. This concerns the
physical-domain essential representative, not a choice of an arbitrary
representative of an ambient parameter-space `L²` class. -/
theorem canonicalSidedEncodingLp_essential
    (μ : Measure Parameter) [IsFiniteMeasure μ] (f : PriceCurve) :
    canonicalSidedEncodingLp μ f.essential = canonicalSidedEncodingLp μ f := by
  unfold canonicalSidedEncodingLp canonicalCertificate
  rw [f.essential_idempotent]

/-- The normalized actual representative on the literal real parameter interval. -/
def canonicalSidedRepresentativeReal (f : PriceCurve) (x : ℝ) : ℝ × ℝ :=
  canonicalSidedEncoding f (clampParameter x)

theorem canonicalSidedRepresentativeReal_memLp
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : PriceCurve) :
    MemLp (canonicalSidedRepresentativeReal f) 2 μ := by
  exact (PriceCurveLp.parametrisedGraph_memLp_two (Measure.map clampParameter μ)
    (canonicalCertificate f).curve
    (sidedAdmissibleParametrisation (canonicalCertificate f).knots)).comp_of_map
      continuous_clampParameter.measurable.aemeasurable

/-- Original label: `defn:parametrisation-operator`.
The full normalized canonical operator in Euclidean-valued `L²([-1,1])`. -/
def canonicalSidedEncodingLpReal (f : PriceCurve) : PriceHilbertSpace sidedLebesgueMeasure :=
  liftLp sidedLebesgueMeasure
    ((canonicalSidedRepresentativeReal_memLp sidedLebesgueMeasure f).toLp
      (canonicalSidedRepresentativeReal f))

theorem coeFn_canonicalSidedEncodingLpReal (f : PriceCurve) :
    ((canonicalSidedEncodingLpReal f : PriceHilbertSpace sidedLebesgueMeasure) :
      ℝ → PricePair) =ᵐ[sidedLebesgueMeasure]
      (fun x => pairEquiv (canonicalSidedEncoding f (clampParameter x))) :=
  coeFn_liftLp_toLp sidedLebesgueMeasure
    (canonicalSidedRepresentativeReal_memLp sidedLebesgueMeasure f)

theorem canonicalSidedEncodingLpReal_essential (f : PriceCurve) :
    canonicalSidedEncodingLpReal f.essential = canonicalSidedEncodingLpReal f := by
  apply congrArg (liftLp sidedLebesgueMeasure)
  apply (MemLp.toLp_eq_toLp_iff _ _).mpr
  exact Filter.Eventually.of_forall (fun x => congrFun (canonicalSidedEncoding_essential f)
    (clampParameter x))

/-- The same Hilbert operator with domain restricted to essential curves. -/
def essentialSidedEncodingLpReal (f : EssentialPriceCurve) :
    PriceHilbertSpace sidedLebesgueMeasure := canonicalSidedEncodingLpReal f.val

end

end Thesis.DayAhead.CanonicalSidedLp
