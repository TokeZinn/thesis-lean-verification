import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveGraph
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveLp
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveHilbert
import Thesis.Foundations.Stochastic.KernelHilbert

/-! # Actual graph-admissible representatives and their Hilbert classes

The graph-wise decoder supplies an admissible parametrisation of one unique
price curve. The actual representative and its Euclidean-valued `L²` class
both lie in cones closed under all nonnegative combinations.
-/

noncomputable section

namespace Thesis.DayAhead.PriceCurves

open MeasureTheory

def graphAdmissibleRepresentative (f : GraphAdmissiblePair) : Parameter → ℝ × ℝ :=
  fun u => (f.volume u, f.price u)

def decodedAdmissibleParametrisation (f : GraphAdmissiblePair) :
    AdmissibleParametrisation (decodePriceCurve f) where
  toFun := volumeDomainPoint f
  continuous := f.volume_continuous.subtype_mk _
  monotone := f.volume_monotone
  surjective := by
    intro x
    obtain ⟨u, hu⟩ := (toVolumeRange f x).property
    exact ⟨u, Subtype.ext hu⟩
  map_zero := Subtype.ext f.volume_zero

theorem parametrisedGraph_decoded (f : GraphAdmissiblePair) :
    parametrisedGraph (decodePriceCurve f) (decodedAdmissibleParametrisation f) =
      graphAdmissibleRepresentative f := by
  funext u
  exact Prod.ext rfl (decodedPrice_volumeDomainPoint f u)

/-- Original label: `prop:admissible-parametrisations-cone`.
The decoded graph determines a unique actual price curve, including its domain. -/
theorem graphAdmissible_unique_priceCurve (f : GraphAdmissiblePair) :
    ∃! g : PriceCurve, g.graph = Set.range (graphAdmissibleRepresentative f) := by
  refine ⟨decodePriceCurve f, (range_representative_eq_decodePriceCurve_graph f).symm, ?_⟩
  intro g hg
  apply PriceCurve.graph_injective
  exact hg.trans (range_representative_eq_decodePriceCurve_graph f)

theorem graphAdmissibleRepresentative_conicCombination
    (α β : ℝ) (f g : GraphAdmissiblePair) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    graphAdmissibleRepresentative (conicCombination α β f g hα hβ) =
      α • graphAdmissibleRepresentative f + β • graphAdmissibleRepresentative g := rfl

/-- Original label: `prop:admissible-parametrisations-cone`.
The cone consists of actual functions, with their pointwise endpoint values. -/
theorem range_graphAdmissibleRepresentative_convexCone :
    Foundations.Stochastic.KernelHilbert.ConvexCone
      (Set.range graphAdmissibleRepresentative) := by
  rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩ α β hα hβ
  exact ⟨conicCombination α β f g hα hβ,
    graphAdmissibleRepresentative_conicCombination α β f g hα hβ⟩

variable (μ : Measure Parameter) [IsFiniteMeasure μ]

theorem graphAdmissibleRepresentative_memLp (f : GraphAdmissiblePair) :
    MemLp (graphAdmissibleRepresentative f) 2 μ := by
  rw [← parametrisedGraph_decoded]
  exact PriceCurveLp.parametrisedGraph_memLp_two μ _ _

/-- Supporting lemma for the prose around `prop:admissible-parametrisations-cone`
(not the mapped statement): an integrability side lemma.  Every such actual
graph belongs to the Euclidean-valued `L²` carrier. -/
theorem graphAdmissibleEuclidean_memLp (f : GraphAdmissiblePair) :
    MemLp (PriceCurveHilbert.pairEquiv ∘ graphAdmissibleRepresentative f) 2 μ :=
  PriceCurveHilbert.pairEquiv.toContinuousLinearMap.comp_memLp'
    (graphAdmissibleRepresentative_memLp μ f)

def graphAdmissibleLp (f : GraphAdmissiblePair) :
    PriceCurveHilbert.PriceHilbertSpace μ :=
  (graphAdmissibleEuclidean_memLp μ f).toLp _

theorem graphAdmissibleLp_conicCombination
    (α β : ℝ) (f g : GraphAdmissiblePair) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    graphAdmissibleLp μ (conicCombination α β f g hα hβ) =
      α • graphAdmissibleLp μ f + β • graphAdmissibleLp μ g := by
  apply Lp.ext
  filter_upwards [(graphAdmissibleEuclidean_memLp μ
    (conicCombination α β f g hα hβ)).coeFn_toLp,
    (graphAdmissibleEuclidean_memLp μ f).coeFn_toLp,
    (graphAdmissibleEuclidean_memLp μ g).coeFn_toLp,
    Lp.coeFn_add (α • graphAdmissibleLp μ f) (β • graphAdmissibleLp μ g),
    Lp.coeFn_smul α (graphAdmissibleLp μ f),
    Lp.coeFn_smul β (graphAdmissibleLp μ g)] with u huv hf hg hadd hsmulf hsmulg
  rw [hadd, Pi.add_apply, hsmulf, hsmulg]
  change _ = α • ((graphAdmissibleEuclidean_memLp μ f).toLp _) u +
    β • ((graphAdmissibleEuclidean_memLp μ g).toLp _) u
  rw [hf, hg]
  change ((graphAdmissibleEuclidean_memLp μ _).toLp _) u = _
  rw [huv]
  simp only [Function.comp_apply, graphAdmissibleRepresentative_conicCombination,
    Pi.add_apply, Pi.smul_apply, map_add, map_smul]

/-- Original label: `prop:admissible-parametrisations-cone`.
Passing to actual Euclidean `L²` classes preserves the cone property. -/
theorem range_graphAdmissibleLp_convexCone :
    Foundations.Stochastic.KernelHilbert.ConvexCone (Set.range (graphAdmissibleLp μ)) := by
  rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩ α β hα hβ
  exact ⟨conicCombination α β f g hα hβ,
    graphAdmissibleLp_conicCombination μ α β f g hα hβ⟩

end Thesis.DayAhead.PriceCurves
