import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurves
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveLp
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveHilbert
import Thesis.Foundations.Stochastic.KernelHilbert

/-!
# Canonical sided-linear price-curve parametrisation

This module implements the replacement chapter's operator `Λ` on actual price
curves.  It proves that the piecewise-linear domain map is admissible and,
crucially, that every sided-linear graph-admissible pair is fixed by
graph-wise decoding followed by canonical linear re-encoding.  That identity
closes the gap between cone closure of an abstract representative class and
weak convexity of the actual canonical encoding.
-/

namespace Thesis.DayAhead.LinearParametrisation

open MeasureTheory PriceCurves Set PriceCurveHilbert
open Foundations.Stochastic.KernelHilbert

noncomputable section

/-- Original label: `defn:linear-parametrisation-operator`.
The current sided-linear domain map, here restricted to the retained simple-curve
carrier. The formula depends only on the two domain endpoints. -/
def linearVolumeReal (f : PriceCurve) (u : ℝ) : ℝ :=
  if u ≤ 0 then -f.leftEndpoint * u else f.rightEndpoint * u

theorem continuous_linearVolumeReal (f : PriceCurve) :
    Continuous (linearVolumeReal f) := by
  have hleft : Continuous (fun u : ℝ => -f.leftEndpoint * u) :=
    continuous_const.mul continuous_id
  have hright : Continuous (fun u : ℝ => f.rightEndpoint * u) :=
    continuous_const.mul continuous_id
  apply hleft.if_le hright continuous_id continuous_const
  intro u hu
  have hu0 : u = 0 := by simpa using hu
  subst u
  simp

theorem monotone_linearVolumeReal (f : PriceCurve) :
    Monotone (linearVolumeReal f) := by
  intro u v huv
  simp only [linearVolumeReal]
  split_ifs with hu hv
  · nlinarith [f.leftEndpoint_nonpos]
  · nlinarith [f.leftEndpoint_nonpos, f.rightEndpoint_nonneg]
  · nlinarith
  · nlinarith [f.rightEndpoint_nonneg]

@[simp]
theorem linearVolumeReal_left (f : PriceCurve) :
    linearVolumeReal f (-1) = f.leftEndpoint := by
  simp [linearVolumeReal]

@[simp]
theorem linearVolumeReal_zero (f : PriceCurve) :
    linearVolumeReal f 0 = 0 := by
  simp [linearVolumeReal]

@[simp]
theorem linearVolumeReal_right (f : PriceCurve) :
    linearVolumeReal f 1 = f.rightEndpoint := by
  simp [linearVolumeReal]

/-- The sided-linear domain map restricted to the common parameter interval. -/
def linearDomainMap (f : PriceCurve) :
    Parameter → Set.Icc f.leftEndpoint f.rightEndpoint := fun u =>
  ⟨linearVolumeReal f u,
    by
      calc
        f.leftEndpoint = linearVolumeReal f (-1) :=
          (linearVolumeReal_left f).symm
        _ ≤ linearVolumeReal f u := monotone_linearVolumeReal f u.2.1,
    by
      calc
        linearVolumeReal f u ≤ linearVolumeReal f 1 :=
          monotone_linearVolumeReal f u.2.2
        _ = f.rightEndpoint := linearVolumeReal_right f⟩

theorem continuous_linearDomainMap (f : PriceCurve) :
    Continuous (linearDomainMap f) := by
  exact Continuous.subtype_mk
    ((continuous_linearVolumeReal f).comp continuous_subtype_val) _

theorem monotone_linearDomainMap (f : PriceCurve) :
    Monotone (linearDomainMap f) := by
  intro u v huv
  exact monotone_linearVolumeReal f huv

theorem surjective_linearDomainMap (f : PriceCurve) :
    Function.Surjective (linearDomainMap f) := by
  intro x
  have himage : (x : ℝ) ∈ linearVolumeReal f '' Set.Icc (-1 : ℝ) 1 := by
    apply intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
      (continuous_linearVolumeReal f).continuousOn
    rw [linearVolumeReal_left, linearVolumeReal_right]
    exact x.2
  obtain ⟨u, hu, hux⟩ := himage
  refine ⟨⟨u, hu⟩, ?_⟩
  exact Subtype.ext hux

/-- Every sided-linear domain map is an admissible parametrisation. -/
def linearAdmissibleParametrisation (f : PriceCurve) :
    AdmissibleParametrisation f where
  toFun := linearDomainMap f
  continuous := continuous_linearDomainMap f
  monotone := monotone_linearDomainMap f
  surjective := surjective_linearDomainMap f
  map_zero := Subtype.ext (linearVolumeReal_zero f)

/--
The actual sided-linear price-curve encoding `Λ`.

Original label: `prop:linear-parametrisation-convex`.
-/
def linearParametrisationOperator (f : PriceCurve) :
    ActualRepresentative :=
  parametrisedGraph f (linearAdmissibleParametrisation f)

/-- The canonical linear representative bundled with its graph laws. -/
def linearGraphAdmissiblePair (f : PriceCurve) : GraphAdmissiblePair :=
  (linearAdmissibleParametrisation f).toGraphAdmissiblePair f

/-- The canonical linear representative bundled with its sided-linear laws. -/
def linearAdmissiblePair (f : PriceCurve) : LinearAdmissiblePair where
  toGraphAdmissiblePair := linearGraphAdmissiblePair f
  leftEndpoint := f.leftEndpoint
  rightEndpoint := f.rightEndpoint
  leftEndpoint_nonpos := f.leftEndpoint_nonpos
  rightEndpoint_nonneg := f.rightEndpoint_nonneg
  volume_left := by
    intro u hu
    change linearVolumeReal f (u : ℝ) = -f.leftEndpoint * (u : ℝ)
    rw [linearVolumeReal, if_pos hu]
  volume_right := by
    intro u hu
    change linearVolumeReal f (u : ℝ) = f.rightEndpoint * (u : ℝ)
    simp only [linearVolumeReal]
    split_ifs with hle
    · have hu0 : (u : ℝ) = 0 := le_antisymm hle hu
      rw [hu0]
      simp
    · rfl

@[simp]
theorem linearAdmissiblePair_volume_parameterLeft
    (p : LinearAdmissiblePair) :
    p.volume parameterLeft = p.leftEndpoint := by
  rw [p.volume_left parameterLeft (by norm_num [parameterLeft])]
  norm_num [parameterLeft]

@[simp]
theorem linearAdmissiblePair_volume_parameterRight
    (p : LinearAdmissiblePair) :
    p.volume parameterRight = p.rightEndpoint := by
  rw [p.volume_right parameterRight (by norm_num [parameterRight])]
  norm_num [parameterRight]

theorem linearVolumeReal_decodePriceCurve
    (p : LinearAdmissiblePair) (u : Parameter) :
    linearVolumeReal (decodePriceCurve p.toGraphAdmissiblePair) u =
      p.volume u := by
  by_cases hu : (u : ℝ) ≤ 0
  · rw [linearVolumeReal, if_pos hu]
    change -p.volume parameterLeft * (u : ℝ) = p.volume u
    rw [linearAdmissiblePair_volume_parameterLeft, p.volume_left u hu]
  · have hu0 : 0 ≤ (u : ℝ) := le_of_not_ge hu
    rw [linearVolumeReal, if_neg hu]
    change p.volume parameterRight * (u : ℝ) = p.volume u
    rw [linearAdmissiblePair_volume_parameterRight, p.volume_right u hu0]

theorem linearDomainMap_decodePriceCurve
    (p : LinearAdmissiblePair) (u : Parameter) :
    linearDomainMap (decodePriceCurve p.toGraphAdmissiblePair) u =
      volumeDomainPoint p.toGraphAdmissiblePair u := by
  apply Subtype.ext
  exact linearVolumeReal_decodePriceCurve p u

/-- Every sided-linear graph-admissible representative is recovered exactly
by graph-wise decoding followed by canonical linear re-encoding. -/
theorem linearParametrisation_reencode_decode
    (p : LinearAdmissiblePair) :
    linearParametrisationOperator
        (decodePriceCurve p.toGraphAdmissiblePair) =
      fun u => (p.volume u, p.price u) := by
  funext u
  apply Prod.ext
  · exact linearVolumeReal_decodePriceCurve p u
  · change (decodePriceCurve p.toGraphAdmissiblePair).price
      (linearDomainMap (decodePriceCurve p.toGraphAdmissiblePair) u) =
        p.price u
    rw [linearDomainMap_decodePriceCurve]
    exact decodePriceCurve_price_volume p.toGraphAdmissiblePair u

/--
Thesis source: Proposition `prop:linear-parametrisation-convex` in the
replacement price-curve chapter.

Original label: `prop:linear-parametrisation-convex`.

Every nonnegative pointwise combination of two canonical linear encodings is
the canonical encoding of the graph-wise decoded combination curve. -/
theorem linearParametrisation_isWeaklyConvex :
    IsWeaklyConvex linearParametrisationOperator := by
  intro f g α β hα hβ
  let p := linearConicCombination α β
    (linearAdmissiblePair f) (linearAdmissiblePair g) hα hβ
  refine ⟨decodePriceCurve p.toGraphAdmissiblePair, ?_⟩
  rw [linearParametrisation_reencode_decode]
  funext u
  rfl

/-! ## Hilbert-valued linear parametrisation -/

/-- Pointwise representative combinations agree with ordinary scalar
multiplication and addition in the actual function space. -/
theorem representativeCombination_eq_smul_add
    (α β : ℝ) (f g : ActualRepresentative) :
    representativeCombination α β f g = α • f + β • g := by
  funext u
  rfl

/-- The actual weak-convexity theorem in the generic operator vocabulary used
by the theoretical foundations. -/
theorem linearParametrisation_weaklyConvexOperator :
    WeaklyConvexOperator PriceCurve ActualRepresentative
      linearParametrisationOperator := by
  intro α β hα hβ f g
  obtain ⟨h, hh⟩ := linearParametrisation_isWeaklyConvex f g α β hα hβ
  refine ⟨h, ?_⟩
  rw [hh, representativeCombination_eq_smul_add]

/-- Thus the actual image of the canonical linear parametrisation is a convex
cone, the first “in particular” clause of the thesis proposition. -/
theorem range_linearParametrisationOperator_convexCone :
    ConvexCone (Set.range linearParametrisationOperator) :=
  (weaklyConvexOperator_iff_range_convexCone
    linearParametrisationOperator).mp
      linearParametrisation_weaklyConvexOperator

/-- The actual linear representative is square-integrable for every finite
measure on the common parameter interval. -/
def linearParametrisationMemLp
    (μ : Measure Parameter) [IsFiniteMeasure μ] (f : PriceCurve) :
    MemLp (linearParametrisationOperator f) 2 μ :=
  PriceCurveLp.parametrisedGraph_memLp_two μ f
    (linearAdmissibleParametrisation f)

/-- Auxiliary `L²` quotient with the ordinary product norm. -/
noncomputable def linearParametrisationBanachLp
    (μ : Measure Parameter) [IsFiniteMeasure μ] (f : PriceCurve) :
    Lp (ℝ × ℝ) 2 μ :=
  (linearParametrisationMemLp μ f).toLp (linearParametrisationOperator f)

/-- The thesis's Hilbert-valued linear encoding uses the Euclidean norm on
the pair of volume and price coordinates. -/
noncomputable def linearParametrisationLp
    (μ : Measure Parameter) [IsFiniteMeasure μ] (f : PriceCurve) :
    PriceHilbertSpace μ := liftLp μ (linearParametrisationBanachLp μ f)

/-- Auxiliary weak convexity for the ordinary-product quotient. The theorem
below transports this identity to the Euclidean-valued Hilbert encoding. -/
theorem linearParametrisationBanachLp_isWeaklyConvex
    (μ : Measure Parameter) [IsFiniteMeasure μ] :
    WeaklyConvexOperator PriceCurve (Lp (ℝ × ℝ) 2 μ)
      (linearParametrisationBanachLp μ) := by
  intro α β hα hβ f g
  obtain ⟨h, hh⟩ := linearParametrisation_isWeaklyConvex f g α β hα hβ
  refine ⟨h, ?_⟩
  let F := linearParametrisationOperator f
  let G := linearParametrisationOperator g
  have hfun : linearParametrisationOperator h = α • F + β • G := by
    rw [hh, representativeCombination_eq_smul_add]
  let hf : MemLp F 2 μ := linearParametrisationMemLp μ f
  let hg : MemLp G 2 μ := linearParametrisationMemLp μ g
  let hhmem : MemLp (linearParametrisationOperator h) 2 μ :=
    linearParametrisationMemLp μ h
  let hcomb : MemLp (α • F + β • G) 2 μ :=
    (hf.const_smul α).add (hg.const_smul β)
  calc
    linearParametrisationBanachLp μ h =
        hcomb.toLp (α • F + β • G) := by
      exact MemLp.toLp_congr hhmem hcomb
        (Filter.Eventually.of_forall fun u => congrFun hfun u)
    _ = (hf.const_smul α).toLp (α • F) +
        (hg.const_smul β).toLp (β • G) := by
      exact MemLp.toLp_add (hf.const_smul α) (hg.const_smul β)
    _ = α • hf.toLp F + β • hg.toLp G := by
      rw [MemLp.toLp_const_smul, MemLp.toLp_const_smul]
    _ = α • linearParametrisationBanachLp μ f +
        β • linearParametrisationBanachLp μ g := rfl

/-- Original label: `prop:linear-parametrisation-convex`.
Original block id: `source:2 - day-ahead/2_clearing_operator_price_curves.tex:261:cor:11`
The linear image remains weakly convex in the Euclidean-valued Hilbert space. -/
theorem linearParametrisationLp_isWeaklyConvex
    (μ : Measure Parameter) [IsFiniteMeasure μ] :
    WeaklyConvexOperator PriceCurve (PriceHilbertSpace μ) (linearParametrisationLp μ) := by
  intro α β hα hβ f g
  obtain ⟨h, hh⟩ := linearParametrisationBanachLp_isWeaklyConvex μ hα hβ f g
  refine ⟨h, ?_⟩
  change liftLp μ (linearParametrisationBanachLp μ h) = _
  rw [hh, map_add, map_smul, map_smul]
  rfl

/-- The Hilbert-valued image is likewise a convex cone, completing the second
“in particular” clause of `prop:linear-parametrisation-convex`.

Original label: `prop:linear-parametrisation-convex`. -/
theorem range_linearParametrisationLp_convexCone
    (μ : Measure Parameter) [IsFiniteMeasure μ] :
    ConvexCone (Set.range (linearParametrisationLp μ)) :=
  (weaklyConvexOperator_iff_range_convexCone
    (linearParametrisationLp μ)).mp
      (linearParametrisationLp_isWeaklyConvex μ)

end

end Thesis.DayAhead.LinearParametrisation
