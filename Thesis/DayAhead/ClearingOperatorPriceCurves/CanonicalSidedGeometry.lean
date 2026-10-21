import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialEncodingInjectivity
import Thesis.Foundations.Stochastic.KernelMetric

/-! # Metric quotient, closed span, and generated cone of the canonical image

These constructions use the actual Euclidean-valued canonical encoding.
They never assert that its image is linear or convex. The metric is on the
kernel quotient. Injectivity on selected essential curves is proved separately
and gives that domain the same metric without a further quotient.
-/

noncomputable section

namespace Thesis.DayAhead.CanonicalSidedGeometry

open Set
open PriceCurves PriceCurveHilbert SidedCurveLp CanonicalSidedLp
open Foundations.Stochastic.KernelHilbert

abbrev Ambient := PriceHilbertSpace sidedLebesgueMeasure

/-- Original label: `defn:parametrisation-operator`.
On selected essential curves, the L² pullback is a metric, not merely a
pseudometric. The separation axiom uses the proved injectivity theorem. -/
noncomputable instance : MetricSpace EssentialPriceCurve :=
  MetricSpace.induced essentialSidedEncodingLpReal
    essentialSidedEncodingLpReal_injective inferInstance

theorem essentialSidedEncodingLpReal_isometry : Isometry essentialSidedEncodingLpReal :=
  Isometry.of_dist_eq fun _ _ => rfl

theorem essential_dist (f g : EssentialPriceCurve) :
    dist f g = ‖essentialSidedEncodingLpReal f - essentialSidedEncodingLpReal g‖ :=
  dist_eq_norm (essentialSidedEncodingLpReal f) (essentialSidedEncodingLpReal g)

/-- Original label: `defn:parametrisation-operator`.
The kernel quotient of the actual canonical Hilbert-valued map. -/
abbrev SidedQuotient := FunctionKernelQuotient canonicalSidedEncodingLpReal

instance : MetricSpace SidedQuotient :=
  functionKernelMetricSpace canonicalSidedEncodingLpReal

/-- Original label: `defn:parametrisation-operator`.
The quotient has exactly the distance prescribed by the manuscript. -/
theorem sidedQuotient_dist (f g : PriceCurve) :
    dist (functionKernelClass canonicalSidedEncodingLpReal f)
      (functionKernelClass canonicalSidedEncodingLpReal g) =
      ‖canonicalSidedEncodingLpReal f - canonicalSidedEncodingLpReal g‖ := by
  change dist (canonicalSidedEncodingLpReal f) (canonicalSidedEncodingLpReal g) = _
  exact dist_eq_norm (canonicalSidedEncodingLpReal f) (canonicalSidedEncodingLpReal g)

/-- Original label: `defn:parametrisation-operator`. -/
def sidedQuotientIsometry : SidedQuotient ≃ᵢ range canonicalSidedEncodingLpReal :=
  functionKernelIsometryEquivRange canonicalSidedEncodingLpReal

/-- The particular closed linear span used for sided-curve statistics. -/
def sidedSpan : Submodule ℝ Ambient :=
  (Submodule.span ℝ (range canonicalSidedEncodingLpReal)).topologicalClosure

instance : CompleteSpace sidedSpan := Submodule.topologicalClosure.completeSpace _

/-- Supporting lemma for the prose around `cor:sided-parametrisation-not-weakly-convex`
(not the mapped statement).  Its following paragraph uses this complete
inner-product space. -/
theorem sidedSpan_hilbert :
    Nonempty (InnerProductSpace ℝ sidedSpan) ∧ Nonempty (CompleteSpace sidedSpan) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

def encodingInSpan (f : PriceCurve) : sidedSpan :=
  ⟨canonicalSidedEncodingLpReal f,
    Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self f))⟩

/-- The intersection definition includes zero explicitly, so it also works for
an empty generating set. It is the least closed convex cone containing the image. -/
def sidedCone : Set sidedSpan :=
  ⋂₀ {C : Set sidedSpan | range encodingInSpan ⊆ C ∧ ConvexCone C ∧ IsClosed C ∧ 0 ∈ C}

theorem sidedCone_zero : (0 : sidedSpan) ∈ sidedCone := by
  intro C hC
  exact hC.2.2.2

theorem sidedCone_contains (f : PriceCurve) : encodingInSpan f ∈ sidedCone := by
  intro C hC
  exact hC.1 (mem_range_self f)

theorem sidedCone_closed : IsClosed sidedCone :=
  isClosed_sInter fun _ hC => hC.2.2.1

theorem sidedCone_convexCone : ConvexCone sidedCone := by
  intro x y hx hy a b ha hb C hC
  exact hC.2.1 (hx C hC) (hy C hC) ha hb

theorem sidedCone_minimal {C : Set sidedSpan} (himage : range encodingInSpan ⊆ C)
    (hcone : ConvexCone C) (hclosed : IsClosed C) (hzero : 0 ∈ C) : sidedCone ⊆ C :=
  fun _ hx => hx C ⟨himage, hcone, hclosed, hzero⟩

/-- Supporting lemma for the prose around `cor:sided-parametrisation-not-weakly-convex`
(not the mapped statement).  The generated cone in the actual closed span has a
unique metric projection. -/
theorem sidedCone_projection_existsUnique (u : sidedSpan) :
    ∃! p : sidedSpan, p ∈ sidedCone ∧
      ‖u - p‖ = ⨅ w : sidedCone, ‖u - (w : sidedSpan)‖ :=
  closedConvexCone_metricProjection_existsUnique sidedCone_convexCone sidedCone_closed
    ⟨0, sidedCone_zero⟩ u

end Thesis.DayAhead.CanonicalSidedGeometry
