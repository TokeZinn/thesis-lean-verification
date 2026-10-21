import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurves
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Square-integrability of parametrised price curves

The corrected price-curve chapter distinguishes actual parametrised graphs
from their `L²` classes.  This file proves the missing analytic bridge: an
admissible parametrised graph of a finite-level monotone price curve is
measurable, bounded, and belongs to `L²` for every finite measure on the common
parameter interval.
-/

namespace Thesis
namespace DayAhead
namespace PriceCurveLp

open MeasureTheory
open PriceCurves

noncomputable section

/-- The actual parametrised graph is Borel measurable. -/
theorem parametrisedGraph_measurable
    (f : PriceCurve) (a : AdmissibleParametrisation f) :
    Measurable (parametrisedGraph f a) := by
  have hvolume : Measurable (fun u : Parameter => (a u : ℝ)) :=
    (continuous_subtype_val.comp a.continuous).measurable
  have hprice : Measurable f.price := f.price_monotone.measurable
  exact Measurable.prod hvolume (hprice.comp a.continuous.measurable)

/-- The norms of the finitely many price levels admit a common real bound. -/
theorem exists_price_norm_bound (f : PriceCurve) :
    ∃ bound : ℝ, ∀ x, ‖f.price x‖ ≤ bound := by
  have hfinite : (Set.range fun x => ‖f.price x‖).Finite := by
    refine (f.price_finite.image (fun y : ℝ => ‖y‖)).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨f.price x, ⟨x, rfl⟩, rfl⟩
  obtain ⟨bound, hbound⟩ := hfinite.bddAbove
  exact ⟨bound, fun x => hbound (Set.mem_range_self x)⟩

/--
Thesis source: analytic membership clause following Definition
`defn:admissible-price-curve-parametrisation` in the replacement price-curve
chapter.

Original label: `defn:admissible-price-curve-parametrisation`.

Every admissible parametrised graph belongs to `L²` on the common compact
parameter interval.  The theorem is measure-agnostic and applies in
particular to restricted Lebesgue measure.
-/
theorem parametrisedGraph_memLp_two
    (μ : Measure Parameter) [IsFiniteMeasure μ]
    (f : PriceCurve) (a : AdmissibleParametrisation f) :
    MemLp (parametrisedGraph f a) 2 μ := by
  obtain ⟨priceBound, hpriceBound⟩ := exists_price_norm_bound f
  let volumeBound : ℝ := max |f.leftEndpoint| |f.rightEndpoint|
  let graphBound : ℝ := max volumeBound priceBound
  refine MemLp.of_bound
    (parametrisedGraph_measurable f a).aestronglyMeasurable graphBound
    (Filter.Eventually.of_forall fun u => ?_)
  rw [parametrisedGraph, Prod.norm_def]
  apply max_le
  · have hvolume : ‖(a u : ℝ)‖ ≤ volumeBound := by
      rw [Real.norm_eq_abs]
      exact abs_le_max_abs_abs (a u).property.1 (a u).property.2
    exact hvolume.trans (le_max_left _ _)
  · exact (hpriceBound (a u)).trans (le_max_right _ _)

end

end PriceCurveLp
end DayAhead
end Thesis
