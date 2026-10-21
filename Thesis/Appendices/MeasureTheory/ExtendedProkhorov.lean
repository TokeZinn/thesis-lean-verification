import Thesis.Appendices.MeasureTheory.MeasureTheory
import Thesis.Appendices.Analysis.BoundedMetric

/-! # Prokhorov's metric for the thesis's extended base distance -/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.MeasureTheory

/-- Original label: `thm:prokhorov-metric`.
The library neighborhood is the existential open neighborhood of the source,
including its empty-set convention. Apply this with the truncated metric. -/
theorem prokhorov_neighborhood_formula
    {X : Type*} [PseudoMetricSpace X] (B : Set X) (ε : ℝ) :
    Metric.thickening ε B = {x | ∃ b ∈ B, dist x b < ε} ∧
      Metric.thickening ε (∅ : Set X) = ∅ := by
  exact ⟨Set.ext (fun _ => Metric.mem_thickening_iff), Metric.thickening_empty ε⟩

/-- Original label: `thm:prokhorov-metric`.
All four assertions apply to the literal min(d,1) metric specified by the
current source. Its topology, Borel sets and complete uniformity agree with
the original extended metric, as proved in BoundedMetric. -/
theorem prokhorovMetricTheorem_extended
    {X : Type*} [d : EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    letI bounded := @BoundedMetric.truncatedMetricSpace X d
    letI : EMetricSpace X := bounded.toEMetricSpace
    (∀ μ ν : ProkhorovFiniteMeasures X, dist μ ν = 0 ↔ μ = ν) ∧
      CompleteSpace (ProkhorovFiniteMeasures X) ∧
      TopologicalSpace.SeparableSpace (ProkhorovFiniteMeasures X) ∧
      ∀ (μ : ℕ → FiniteMeasures X) (ν : FiniteMeasures X),
        Tendsto (fun n => LevyProkhorov.ofMeasure (μ n)) atTop
          (𝓝 (LevyProkhorov.ofMeasure ν)) ↔ Tendsto μ atTop (𝓝 ν) := by
  exact @prokhorovMetricTheorem X (@BoundedMetric.truncatedMetricSpace X d)
    _ _ _ _

/-- Original label: `thm:prokhorov-metric`.
Original label: `thm:prokhorov-metric-weak-convergence-polish`.
Restricting the infimum to finite strictly positive radii leaves the library
distance unchanged. This matches the radius convention of the source. -/
theorem levyProkhorovEDist_eq_positive_inf
    {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    levyProkhorovEDist μ ν = sInf {ε : ℝ≥0∞ | 0 < ε ∧ ε < ∞ ∧
      ∀ B, MeasurableSet B → μ B ≤ ν (Metric.thickening ε.toReal B) + ε ∧
        ν B ≤ μ (Metric.thickening ε.toReal B) + ε} := by
  apply le_antisymm
  · exact sInf_le_sInf (fun _ h => h.2.2)
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hd := levyProkhorovEDist_ne_top μ ν
    have hlt : levyProkhorovEDist μ ν < levyProkhorovEDist μ ν + ε :=
      ENNReal.lt_add_right hd (by exact_mod_cast hε.ne')
    refine sInf_le ⟨(zero_le _).trans_lt hlt, by finiteness, fun B hB => ?_⟩
    exact ⟨left_measure_le_of_levyProkhorovEDist_lt hlt hB,
      right_measure_le_of_levyProkhorovEDist_lt hlt hB⟩

end Thesis.Foundations.Preliminary.MeasureTheory
