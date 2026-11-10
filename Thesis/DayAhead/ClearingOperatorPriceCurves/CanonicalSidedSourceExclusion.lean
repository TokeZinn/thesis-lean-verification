import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedExample
import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialEncodingInjectivity
import Thesis.DayAhead.ClearingOperatorPriceCurves.GraphAdmissibleCone

/-! # Source graph-and-quarter-knot proof of sided nonconvexity

Almost-everywhere equality first fixes the continuous quantity coordinate.
The selected prices then fix the same physical four-block graph. Its canonical
quarter knot is 5/6, while the actual average quantity there is 5/8.
-/
noncomputable section
namespace Thesis.DayAhead.SidedSourceExclusion

open Set MeasureTheory
open PriceCurves SidedParametrisation SidedCertificate SidedCurveLp CanonicalSidedLp

def transportAdmissible {f g : PriceCurve} (h : f = g)
    (a : AdmissibleParametrisation f) : AdmissibleParametrisation g := h ▸ a

theorem parametrisedGraph_transport {f g : PriceCurve} (h : f = g)
    (a : AdmissibleParametrisation f) :
    parametrisedGraph g (transportAdmissible h a) = parametrisedGraph f a := by
  cases h
  rfl

def averageAdmissible : AdmissibleParametrisation selectedAverageCurve.essential :=
  transportAdmissible selectedAverageCurve_essential.symm
    (decodedAdmissibleParametrisation selectedAverageGraph.toGraphAdmissiblePair)

theorem averageAdmissible_graph :
    parametrisedGraph selectedAverageCurve.essential averageAdmissible =
      selectedTwoThreeAverage := by
  rw [averageAdmissible, parametrisedGraph_transport]
  exact parametrisedGraph_decoded selectedAverageGraph.toGraphAdmissiblePair

/-- The source first step: a.e. equality forces both continuous quantity
coordinates to agree at every parameter, including the quarter knot. -/
theorem quantity_eq_everywhere {f : PriceCurve}
    (hae : (fun x => canonicalSidedEncoding f (clampParameter x))
      =ᵐ[sidedLebesgueMeasure] (fun x => selectedTwoThreeAverage (clampParameter x))) :
    (fun u => (canonicalSidedEncoding f u).1) =
      (fun u => (selectedTwoThreeAverage u).1) := by
  apply continuous_parameter_eq_of_ae
    (continuous_subtype_val.comp
      (sidedAdmissibleParametrisation (canonicalCertificate f).knots).continuous)
    selectedAverageGraph.volume_continuous
  exact hae.mono (fun _ h => congrArg Prod.fst h)

/-- The source same-graph step. The physical curve is the explicit selected
four-block curve, not merely another curve with a bounded block count. -/
theorem same_four_block_curve {f : PriceCurve}
    (hae : (fun x => canonicalSidedEncoding f (clampParameter x))
      =ᵐ[sidedLebesgueMeasure] (fun x => selectedTwoThreeAverage (clampParameter x))) :
    f.essential = selectedAverageCurve := by
  have h := essential_eq_of_parametrisedGraph_ae
    (sidedAdmissibleParametrisation (canonicalCertificate f).knots)
    averageAdmissible (by simpa only [averageAdmissible_graph] using hae)
  exact h.trans selectedAverageCurve_essential

/-- Original label: `exmp:sided-average-not-canonical`.
This exclusion follows the supplied continuous-quantity/same-four-block-graph
argument and the 5/6 versus 5/8 quarter-knot contradiction. -/
theorem selected_average_not_ae_in_canonical_range_source :
    ¬ ∃ f : PriceCurve, (fun x => canonicalSidedEncoding f (clampParameter x))
      =ᵐ[sidedLebesgueMeasure] (fun x => selectedTwoThreeAverage (clampParameter x)) := by
  rintro ⟨f, hf⟩
  have hq := quantity_eq_everywhere hf
  have hgraph := same_four_block_curve hf
  have hcanonical : canonicalSidedEncoding f = canonicalSidedEncoding selectedAverageCurve :=
    (canonicalSidedEncoding_eq_iff_essential_eq _ _).mpr
      (hgraph.trans selectedAverageCurve_essential.symm)
  have hquarter := congrFun hq (⟨1/4, by constructor <;> norm_num⟩ : Parameter)
  rw [hcanonical, selectedAverage_canonical_quarter,
    selectedTwoThreeAverage_endpoints.2.2.2.2] at hquarter
  norm_num at hquarter

end Thesis.DayAhead.SidedSourceExclusion
