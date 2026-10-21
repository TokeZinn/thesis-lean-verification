import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveLp
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveHilbert
import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedParametrisation
import Thesis.Foundations.Stochastic.KernelHilbert

/-!
# Hilbert-valued sided price-curve encodings

This module sends actual sided representatives to their `L²` equivalence
classes and proves the formal non-weak-convexity proposition in the literal
restricted-Lebesgue Hilbert space.
-/

namespace Thesis.DayAhead.SidedCurveLp

open MeasureTheory
open PriceCurves SidedParametrisation PriceCurveHilbert
open Foundations.Stochastic.KernelHilbert

noncomputable section

/-- The ambient `L²` space of two-component representatives over the common
parameter interval. -/
abbrev PriceCurveLpSpace (μ : Measure Parameter) :=
  PriceHilbertSpace μ

/-- The Hilbert-valued sided encoding `overline Ψ = π₂ ∘ Ψ` from the
replacement chapter. -/
noncomputable def sidedParametrisationLp
    (μ : Measure Parameter) [IsFiniteMeasure μ]
    (c : CanonicalSidedCurve) : PriceCurveLpSpace μ :=
  liftLp μ ((PriceCurveLp.parametrisedGraph_memLp_two μ c.curve
    (sidedAdmissibleParametrisation c.knots)).toLp
      (sidedParametrisationOperator c))

/-- A representative of the encoded `L²` class agrees almost everywhere with
the actual sided parametrisation. -/
theorem coeFn_sidedParametrisationLp
    (μ : Measure Parameter) [IsFiniteMeasure μ]
    (c : CanonicalSidedCurve) :
    ((sidedParametrisationLp μ c : PriceCurveLpSpace μ) :
        Parameter → PricePair) =ᵐ[μ]
      (fun u => pairEquiv (sidedParametrisationOperator c u)) := by
  exact coeFn_liftLp_toLp μ (PriceCurveLp.parametrisedGraph_memLp_two μ c.curve
    (sidedAdmissibleParametrisation c.knots))

/-! ## Literal restricted-Lebesgue `L²` non-convexity -/

/-- The total real-to-parameter clamp used in the almost-everywhere witness is
continuous. -/
theorem continuous_clampParameter : Continuous clampParameter := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_const.min continuous_id)

/-- A minimal sided representative pulled back to the real line and clamped
to `[-1,1]`. -/
def minimalSidedRepresentativeReal
    (c : MinimalCanonicalSidedCurve) (x : ℝ) : ℝ × ℝ :=
  minimalSidedParametrisationOperator c (clampParameter x)

theorem minimalSidedRepresentativeReal_measurable
    (c : MinimalCanonicalSidedCurve) :
    Measurable (minimalSidedRepresentativeReal c) := by
  exact (PriceCurveLp.parametrisedGraph_measurable c.raw.curve
    (sidedAdmissibleParametrisation c.raw.knots)).comp
      continuous_clampParameter.measurable

/-- The clamped real representative belongs to `L²` for every finite measure. -/
theorem minimalSidedRepresentativeReal_memLp
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : MinimalCanonicalSidedCurve) :
    MemLp (minimalSidedRepresentativeReal c) 2 μ := by
  obtain ⟨priceBound, hpriceBound⟩ :=
    PriceCurveLp.exists_price_norm_bound c.raw.curve
  let volumeBound : ℝ :=
    max |c.raw.curve.leftEndpoint| |c.raw.curve.rightEndpoint|
  let graphBound : ℝ := max volumeBound priceBound
  refine MemLp.of_bound
    (minimalSidedRepresentativeReal_measurable c).aestronglyMeasurable
      graphBound
    (Filter.Eventually.of_forall fun x => ?_)
  rw [minimalSidedRepresentativeReal, minimalSidedParametrisationOperator,
    sidedParametrisationOperator, parametrisedGraph, Prod.norm_def]
  apply max_le
  · have hvolume :
        ‖((sidedAdmissibleParametrisation c.raw.knots)
          (clampParameter x) : ℝ)‖ ≤ volumeBound := by
      rw [Real.norm_eq_abs]
      exact abs_le_max_abs_abs
        ((sidedAdmissibleParametrisation c.raw.knots)
          (clampParameter x)).property.1
        ((sidedAdmissibleParametrisation c.raw.knots)
          (clampParameter x)).property.2
    exact hvolume.trans (le_max_left _ _)
  · exact (hpriceBound ((sidedAdmissibleParametrisation c.raw.knots)
      (clampParameter x))).trans (le_max_right _ _)

/-- Restricted Lebesgue measure on the literal real interval `[-1,1]`. -/
abbrev sidedLebesgueMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (-1 : ℝ) 1)

/-- An auxiliary quotient with the ordinary product norm, used only for
algebraic and almost-everywhere arguments. -/
noncomputable def minimalSidedParametrisationBanachLpReal
    (c : MinimalCanonicalSidedCurve) :
    Lp (ℝ × ℝ) 2 sidedLebesgueMeasure :=
  (minimalSidedRepresentativeReal_memLp sidedLebesgueMeasure c).toLp
    (minimalSidedRepresentativeReal c)

/-- The minimal canonical sided operator in the Euclidean-valued `L²` space. -/
noncomputable def minimalSidedParametrisationLpReal
    (c : MinimalCanonicalSidedCurve) : PriceHilbertSpace sidedLebesgueMeasure :=
  liftLp sidedLebesgueMeasure (minimalSidedParametrisationBanachLpReal c)

/-- Auxiliary non-convexity for the ordinary-product quotient. The argument
uses only the almost-everywhere midpoint obstruction; the theorem below
transports it to the Euclidean-valued Hilbert encoding. -/
theorem minimalSidedParametrisationBanachLpReal_not_weaklyConvex :
    ¬ WeaklyConvexOperator MinimalCanonicalSidedCurve
      (Lp (ℝ × ℝ) 2 sidedLebesgueMeasure)
      minimalSidedParametrisationBanachLpReal := by
  intro hweakLp
  apply sidedParametrisationHilbert_not_weaklyConvex
  intro f g α β hα hβ
  obtain ⟨h, hh⟩ := hweakLp hα hβ f g
  refine ⟨h, ?_⟩
  let F := minimalSidedRepresentativeReal f
  let G := minimalSidedRepresentativeReal g
  let H := minimalSidedRepresentativeReal h
  let hf : MemLp F 2 sidedLebesgueMeasure :=
    minimalSidedRepresentativeReal_memLp sidedLebesgueMeasure f
  let hg : MemLp G 2 sidedLebesgueMeasure :=
    minimalSidedRepresentativeReal_memLp sidedLebesgueMeasure g
  let hH : MemLp H 2 sidedLebesgueMeasure :=
    minimalSidedRepresentativeReal_memLp sidedLebesgueMeasure h
  let hcomb : MemLp (α • F + β • G) 2 sidedLebesgueMeasure :=
    (hf.const_smul α).add (hg.const_smul β)
  have htoLpCombo :
      hcomb.toLp (α • F + β • G) =
        α • minimalSidedParametrisationBanachLpReal f +
          β • minimalSidedParametrisationBanachLpReal g := by
    calc
      hcomb.toLp (α • F + β • G) =
          (hf.const_smul α).toLp (α • F) +
            (hg.const_smul β).toLp (β • G) := by
        exact MemLp.toLp_add (hf.const_smul α) (hg.const_smul β)
      _ = α • hf.toLp F + β • hg.toLp G := by
        rw [MemLp.toLp_const_smul, MemLp.toLp_const_smul]
      _ = α • minimalSidedParametrisationBanachLpReal f +
          β • minimalSidedParametrisationBanachLpReal g := rfl
  have hEqLp : hH.toLp H = hcomb.toLp (α • F + β • G) := by
    calc
      hH.toLp H = minimalSidedParametrisationBanachLpReal h := rfl
      _ = α • minimalSidedParametrisationBanachLpReal f +
          β • minimalSidedParametrisationBanachLpReal g := hh
      _ = hcomb.toLp (α • F + β • G) := htoLpCombo.symm
  have hae : H =ᵐ[sidedLebesgueMeasure] α • F + β • G :=
    (MemLp.toLp_eq_toLp_iff hH hcomb).mp hEqLp
  simpa [H, F, G, minimalSidedRepresentativeReal,
    representativeCombination] using hae

/-- Original label: `cor:sided-parametrisation-not-weakly-convex`.
The non-convexity obstruction holds in the thesis's Euclidean Hilbert norm. -/
theorem minimalSidedParametrisationLpReal_not_weaklyConvex :
    ¬ WeaklyConvexOperator MinimalCanonicalSidedCurve
      (PriceHilbertSpace sidedLebesgueMeasure) minimalSidedParametrisationLpReal := by
  intro hweak
  apply minimalSidedParametrisationBanachLpReal_not_weaklyConvex
  intro α β hα hβ f g
  obtain ⟨h, hh⟩ := hweak hα hβ f g
  refine ⟨h, liftLp_injective sidedLebesgueMeasure ?_⟩
  simpa only [map_add, map_smul] using hh

noncomputable instance : Nonempty MinimalCanonicalSidedCurve :=
  ⟨minimalTwoBlockCurve⟩

/-- Equivalently, the image of the actual canonical sided operator is not a
convex cone. -/
theorem range_minimalSidedParametrisationOperator_not_convexCone :
    ¬ ConvexCone (Set.range minimalSidedParametrisationOperator) := by
  intro hcone
  apply sidedParametrisation_not_weaklyConvex
  intro f g α β hα hβ
  obtain ⟨h, hh⟩ := hcone
    (show minimalSidedParametrisationOperator f ∈
      Set.range minimalSidedParametrisationOperator from ⟨f, rfl⟩)
    (show minimalSidedParametrisationOperator g ∈
      Set.range minimalSidedParametrisationOperator from ⟨g, rfl⟩)
    hα hβ
  refine ⟨h, ?_⟩
  simpa [representativeCombination] using hh

/-- Equivalently, the image of the literal `L²`-valued sided operator is not
a convex cone, completing the final clause of the replacement proposition.

Original label: `cor:sided-parametrisation-not-weakly-convex`. -/
theorem range_minimalSidedParametrisationLpReal_not_convexCone :
    ¬ ConvexCone (Set.range minimalSidedParametrisationLpReal) := by
  intro hcone
  exact minimalSidedParametrisationLpReal_not_weaklyConvex
    ((weaklyConvexOperator_iff_range_convexCone
      minimalSidedParametrisationLpReal).mpr hcone)

end

end Thesis.DayAhead.SidedCurveLp
