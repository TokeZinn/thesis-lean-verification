import Thesis.Appendices.Analysis.ExtendedAnalysis

/-! # Countable rational interval constraints for continuous paths

The source's rational-window separability construction now lives on the
primary module `AnalysisBasic` (`Analysis.ContinuousPathSeparability`:
`Window`, `region`, `Covers`, `constraint`, `exists_constraint`), where it
proves the separability clause of `prop:spc-continuous`
(`Analysis.continuousPathSpace_metric_complete_separable`).  This module keeps
the instance form of that clause without a completeness hypothesis and its
extended-distance variant, which the primary extended statement
(`Analysis.continuousPathSpace_extended_complete_separable`) obtains from
Mathlib's instance instead; the moved names are re-exported for interface
stability.
-/

noncomputable section
namespace Thesis.Foundations.Preliminary.ContinuousPathSource

open Set Filter Topology TopologicalSpace
open Analysis

export Thesis.Foundations.Preliminary.Analysis.ContinuousPathSeparability
  (Window region Covers constraint exists_constraint)

/-- Alternative route for `prop:spc-continuous` (not the mapped proof): the
separability clause as an instance, for a nonempty separable metric target and
without a completeness hypothesis.  One selected continuous path per nonempty
countable rational-constraint cell of `Analysis.ContinuousPathSeparability`
forms the dense set; no compact-open second-countability theorem is used.  The
mapped proof is `Analysis.continuousPathSpace_metric_complete_separable`. -/
theorem continuousPath_separable_source (a b : ℝ) (X : Type*) [MetricSpace X]
    [Nonempty X] [SeparableSpace X] : SeparableSpace C(Icc a b, X) := by
  classical
  obtain ⟨d : ℕ → X, hd⟩ := exists_dense_seq X
  let Index := {i : Finset Window × ℚ // (constraint (a := a) (b := b) d i).Nonempty}
  let chosen : Index → C(Icc a b, X) := fun i => Classical.choose i.property
  have hchosen : ∀ i, chosen i ∈ constraint d i.1 := fun i => Classical.choose_spec i.property
  refine ⟨Set.range chosen, Set.countable_range chosen, ?_⟩
  apply Metric.dense_iff.mpr
  intro f ε hε
  obtain ⟨i, hfi, hnear⟩ := exists_constraint d hd f ε hε
  let j : Index := ⟨i, ⟨f, hfi⟩⟩
  refine ⟨chosen j, ⟨?_, ⟨j, rfl⟩⟩⟩
  simpa only [Metric.mem_ball, dist_comm] using (hnear (chosen j) (hchosen j))

/-- Alternative route for `prop:spc-continuous` (not the mapped proof):
separability in the extended-distance scope.  Separability is topological; the
capped compatible metric retains the original topology and lets the same
rational-constraint construction apply.  The mapped statement
`Analysis.continuousPathSpace_extended_complete_separable` obtains this clause
from Mathlib's instance instead. -/
theorem continuousPath_extended_separable_source (a b : ℝ) (X : Type*)
    [d : EMetricSpace X] [Nonempty X] [SeparableSpace X] :
    letI := continuousPathSpaceEMetricSpace a b X
    SeparableSpace C(Icc a b, X) := by
  exact @continuousPath_separable_source a b X (@BoundedMetric.truncatedMetricSpace X d) _ _

end Thesis.Foundations.Preliminary.ContinuousPathSource
