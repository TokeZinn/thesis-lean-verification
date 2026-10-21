import Thesis.Appendices.MeasureTheory.ExtendedProkhorov

/-! # Evaluation measurability for the original extended-metric convention -/

namespace Thesis.Foundations.Preliminary.MeasureTheory

open _root_.MeasureTheory

/-- Original block id: `source:A - appendices/measure.tex:438:prop:25`.
The metric used for Prokhorov's distance is exactly the source's capped
extended metric. Its topology and Borel sets agree with those of the original
extended metric; no finiteness of the original base distance is required. -/
theorem randomMeasure_iff_prokhorovMeasurable_extended
    {Ω X : Type*} [MeasurableSpace Ω] [d : EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (Ξ : Ω → FiniteMeasure X) :
    letI bounded := @BoundedMetric.truncatedMetricSpace X d
    letI : EMetricSpace X := bounded.toEMetricSpace
    IsEvaluationMeasurable Ξ ↔ IsProkhorovBorelMeasurable Ξ := by
  exact @randomMeasure_iff_prokhorovMeasurable Ω X _
    (@BoundedMetric.truncatedMetricSpace X d) _ _ _ _ Ξ

end Thesis.Foundations.Preliminary.MeasureTheory
