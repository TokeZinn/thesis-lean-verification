import Thesis.DayAhead.ForecastingImpact.ShapleyPermutations
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.HasLaw
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Sampling the finite Shapley game

Forecasting chapter, lines 500–540. Exact coalition evaluations under independent
uniform permutations have the factorial Shapley value as their expectation and
converge to it almost surely. Conditional simulation of a coalition is a separate
Monte Carlo average: its law, first moment, and sampling independence must hold
for the selected conditional version at the conditioning point.
-/

noncomputable section
namespace Thesis.DayAhead.ShapleyPermutations

open Finset Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {n : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
  [MeasurableSingletonClass (Equiv.Perm (Fin n))]

def uniformMeasure (n : ℕ) [MeasurableSpace (Equiv.Perm (Fin n))] :
    Measure (Equiv.Perm (Fin n)) := (PMF.uniformOfFintype _).toMeasure

instance uniformMeasure_probability : IsProbabilityMeasure (uniformMeasure n) := by
  unfold uniformMeasure
  infer_instance

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [MeasurableSpace H] [BorelSpace H]

end Thesis.DayAhead.ShapleyPermutations
