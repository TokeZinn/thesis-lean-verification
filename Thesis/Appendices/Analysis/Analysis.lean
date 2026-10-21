import Thesis.Appendices.Analysis.SkorokhodCompleteness
import Thesis.Appendices.Analysis.SkorokhodConvergence
import Thesis.Appendices.Analysis.SkorokhodSeparability

/-! # Preliminary analysis and the Skorokhod metric

`AnalysisBasic` supplies the general topology and analysis results and the
literal path definitions. The Skorokhod companion modules prove the
metric axioms, finiteness, completeness, separability, and both directions of
the time-change criterion, with no project-specific axioms.
-/

open Filter Set Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

universe u

/-- Separability for the logarithmic-distortion Skorokhod metric, proved using
finite step paths with cuts and values in countable dense sets. -/
theorem skorokhodDistance_separable
    {a b : ℝ} (hab : a < b) (X : Type u) [MetricSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (side : PathOrientation) :
    IsSeparableFor (@skorokhodEDistance a b X _ side) :=
  skorokhodDistance_separable_core hab.le side

/-- Compatibility theorem for the former combined external obligation.
Both completeness and separability are now proved internally. -/
theorem skorokhodDistance_complete_separable
    {a b : ℝ} (hab : a < b) (X : Type u) [MetricSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (side : PathOrientation) :
    IsCompleteFor (@skorokhodEDistance a b X _ side) ∧
      IsSeparableFor (@skorokhodEDistance a b X _ side) :=
  ⟨skorokhodDistance_complete hab.le side, skorokhodDistance_separable hab X side⟩

/-- Original label: `prop:skorokhod-metric`.
The metric, finiteness, completeness, and separability clauses are all proved
internally for the thesis's exact logarithmic-distortion formula. -/
theorem skorokhodDistance_metric_complete_separable
    {a b : ℝ} (hab : a < b) (X : Type u) [MetricSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (side : PathOrientation) :
    IsExtendedMetric (@skorokhodEDistance a b X _ side) ∧
      (∀ f g, @skorokhodEDistance a b X _ side f g ≠ ∞) ∧
      IsCompleteFor (@skorokhodEDistance a b X _ side) ∧
      IsSeparableFor (@skorokhodEDistance a b X _ side) := by
  obtain ⟨hcomplete, hseparable⟩ := skorokhodDistance_complete_separable hab X side
  exact ⟨skorokhodEDistance_isExtendedMetric hab.le side,
    skorokhodEDistance_ne_top, hcomplete, hseparable⟩

/-- Uniformly small time changes and vanishing aligned path error imply
convergence for logarithmic distortion. The proof uses finite oscillation
cuts and Lipschitz interpolation, with no project-specific axiom. -/
theorem skorokhodConvergence_of_timeChanges
    {a b : ℝ} (hab : a < b) (X : Type u) [MetricSpace X]
    (side : PathOrientation) (fseq : ℕ → RegularPath a b X side)
    (f : RegularPath a b X side)
    (timeChanges : ℕ → IncreasingIntervalBijection a b)
    (hshift : Tendsto (fun n => timeShiftNorm (timeChanges n)) atTop (𝓝 0))
    (herror : Tendsto (fun n => alignedPathError (fseq n) f (timeChanges n)) atTop (𝓝 0)) :
    ConvergesFor (@skorokhodEDistance a b X _ side) fseq f :=
  skorokhodConvergence_of_timeChanges_core hab.le fseq f timeChanges hshift herror

/-- Original block id: `source:A - appendices/analysis.tex:504:prop:39`.
Both implications are proved internally, using the thesis's exact logarithmic
distortion formula and its uniform-displacement convergence criterion. -/
theorem skorokhodConvergence_iff_timeChanges
    {a b : ℝ} (hab : a < b) (X : Type u) [MetricSpace X]
    (side : PathOrientation) (fseq : ℕ → RegularPath a b X side)
    (f : RegularPath a b X side) :
    ConvergesFor (@skorokhodEDistance a b X _ side) fseq f ↔
      ∃ timeChanges : ℕ → IncreasingIntervalBijection a b,
        Tendsto (fun n => timeShiftNorm (timeChanges n)) atTop (𝓝 0) ∧
          Tendsto (fun n => alignedPathError (fseq n) f (timeChanges n)) atTop (𝓝 0) := by
  refine ⟨skorokhodConvergence_has_timeChanges hab.le fseq f, ?_⟩
  rintro ⟨timeChanges, hshift, herror⟩
  exact skorokhodConvergence_of_timeChanges hab X side fseq f timeChanges hshift herror

end Thesis.Foundations.Preliminary.Analysis
