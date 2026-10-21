import Thesis.DayAhead.FunctionalDataAnalysis.CompactSpectralExpansion
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Source finite-projection proof of coordinate conditional expectation

The thesis proof of `thm:conditional-expect-Hilbert` by finite projections,
integrable domination, conditional dominated convergence and finite-sum
commutation now lives on the primary module `FunctionalData`
(`scoreProjection`, `scoreProjection_residual_sq`,
`scoreProjection_residual_antitone`, `conditional_antitone_dominated_zero`,
`condExp_scoreProjection_tendsto`, `condExp_scoreProjection_eq_finite_scores`,
`condExp_partialSums_tendsto`).  This module is retained for interface
stability and only re-exports those results under their former names. -/

noncomputable section
namespace Thesis.DayAhead.ConditionalBasisSource

export Thesis.DayAhead.FunctionalData (conditional_antitone_dominated_zero)

/-- Moved to `FunctionalData` as `scoreProjection` (the same finite sum of rank-one
projections, formerly written `partialProjection b (Finset.range N)`); kept as an alias. -/
alias projection := FunctionalData.scoreProjection

/-- Moved to `FunctionalData` as `scoreProjection_apply`; kept as an alias. -/
alias projection_apply := FunctionalData.scoreProjection_apply

/-- Moved to `FunctionalData` as `scoreProjection_residual_sq`; kept as an alias. -/
alias residual_norm_sq := FunctionalData.scoreProjection_residual_sq

/-- Moved to `FunctionalData` as `scoreProjection_residual_antitone`; kept as an alias. -/
alias residual_norm_antitone := FunctionalData.scoreProjection_residual_antitone

/-- Moved to `FunctionalData` as `condExp_scoreProjection_tendsto`; kept as an alias. -/
alias condExp_projections_tendsto := FunctionalData.condExp_scoreProjection_tendsto

/-- Moved to `FunctionalData` as `condExp_scoreProjection_eq_finite_scores`; kept as an alias. -/
alias condExp_projection_eq_finite_scores :=
  FunctionalData.condExp_scoreProjection_eq_finite_scores

/-- Moved to `FunctionalData` as `condExp_partialSums_tendsto` (the labelled theorem for the
series clause of `thm:conditional-expect-Hilbert`); kept as an alias. -/
alias conditional_basis_series_source := FunctionalData.condExp_partialSums_tendsto

end Thesis.DayAhead.ConditionalBasisSource
