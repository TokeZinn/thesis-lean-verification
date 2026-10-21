import Thesis.DayAhead.FunctionalDataAnalysis.ScoreInformationSource
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul

/-! # The L² Lévy-upward branch for scores

The `L²` Lévy-upward branch (conditional Jensen, uniform integrability of the
conditional means of `Y²`, and `levy_upward_L2`) and the resulting `L²` clause
of `thm:scores-sigma-algebra` now live on the primary module `FunctionalData`
(`eLpNorm_square`, `conditional_square_le`, `conditional_uniformIntegrable_two`,
`levy_upward_L2`, `condExp_scoreFiltration_tendsto_eLpNorm_two`).  This module
is retained for interface stability and only re-exports those results under
their former names. -/

noncomputable section
namespace Thesis.DayAhead.ScoreLevyL2Source

export Thesis.DayAhead.FunctionalData
  (eLpNorm_square conditional_square_le conditional_uniformIntegrable_two levy_upward_L2)

/-- Moved to `FunctionalData` as `condExp_scoreFiltration_tendsto_eLpNorm_two` (the labelled
`L²` clause, stated there for any finite measure); kept as an alias. -/
alias condExp_scores_tendsto_L2 := FunctionalData.condExp_scoreFiltration_tendsto_eLpNorm_two

end Thesis.DayAhead.ScoreLevyL2Source
