import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLMidpoint

/-! # Measurable actual price evaluation in arbitrary measurable families -/
noncomputable section
namespace Thesis.DayAhead.VendorPLPriceEvaluation

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLPriceCells VendorPLMidpoint
open FinitePolygonInverse Foundations.MarketRepresentation TuplesMeasurableSorting

/-- The source finite price-cell arithmetic applies to any measurable family
of literal paired lists and measurable admissible quantity arguments. -/
theorem measurable_actual_price_family
    {Ω : Type*} [MeasurableSpace Ω] {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}
    (input : Ω → BoundedLayer lo hi ns nb) (hinput : Measurable input)
    (q : Ω → ℝ) (hq : Measurable q)
    (hdom : ∀ w, q w ∈ (book hlohi (input w)).domain) :
    Measurable (fun w => (book hlohi (input w)).price (q w)) := by
  let cells (p : VendorPLPriceCells.Pattern ns nb) := input ⁻¹' VendorPLPriceCells.cell hlohi p
  apply measurable_of_measurable_restrict_countable_cover
    (S := cells) (fun p => (VendorPLPriceCells.measurableSet_cell hlohi p).preimage hinput) (by
      ext w
      simp only [mem_iUnion, mem_univ, iff_true]
      exact VendorPLPriceCells.cell_cover hlohi (input w))
  intro p
  have hin : Measurable (fun w : cells p => input w.val) := hinput.comp measurable_subtype_coe
  have ha := (measurable_endpointA hlohi p).comp hin
  have hb := (measurable_endpointB hlohi p).comp hin
  have hq' : Measurable (fun w : cells p => q w.val) := hq.comp measurable_subtype_coe
  convert measurable_finiteMidpoint lo hi _ _ _ ha hb hq' using 1
  funext w
  exact actual_midpoint_eq hlohi p ⟨input w.val, w.property⟩ (q w.val) (hdom w.val)

end Thesis.DayAhead.VendorPLPriceEvaluation
