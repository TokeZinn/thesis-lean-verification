import Thesis.DayAhead.FunctionalDataAnalysis.FunctionalData
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # Source proof of information in the score sequence

The thesis route to `thm:scores-sigma-algebra` (Parseval squared distances,
measurable ball preimages, the countable dense rational-ball basis, and Lévy's
upward theorem for the almost-sure and `L¹` clauses) now lives on the primary
module `FunctionalData` (`squaredDistance_hasSum`, `squaredDistance_measurable`,
`ball_preimage_measurable`, `dense_rational_ball_basis`,
`scoreDomain_toH_measurable_from_balls`, `scoreMeasurableSpace_eq_borel`,
`iSup_scoreFiltration_eq_comap_borel`, `condExp_scoreFiltration_tendsto_ae`,
`condExp_scoreFiltration_tendsto_L1`).  This module is retained for interface
stability and only re-exports those results under their former names. -/

noncomputable section
namespace Thesis.DayAhead.ScoreInformationSource

export Thesis.DayAhead.FunctionalData
  (squaredDistance_hasSum squaredDistance_measurable ball_preimage_measurable
    dense_rational_ball_basis scoreDomain_toH_measurable_from_balls)

/-- Moved to `FunctionalData` as `scoreMeasurableSpace_eq_borel`; kept as an alias. -/
alias score_sigma_eq_borel := FunctionalData.scoreMeasurableSpace_eq_borel

/-- Moved to `FunctionalData` as `iSup_scoreFiltration_eq_comap_borel`; kept as an alias. -/
alias iSup_scores_eq_comap_source := FunctionalData.iSup_scoreFiltration_eq_comap_borel

/-- Moved to `FunctionalData` as `condExp_scoreFiltration_tendsto_ae` (stated there for any
finite measure); kept as an alias. -/
alias condExp_scores_tendsto_ae_source := FunctionalData.condExp_scoreFiltration_tendsto_ae

/-- Moved to `FunctionalData` as `condExp_scoreFiltration_tendsto_L1` (the labelled `L¹`
clause, stated there for any finite measure); kept as an alias. -/
alias condExp_scores_tendsto_L1 := FunctionalData.condExp_scoreFiltration_tendsto_L1

end Thesis.DayAhead.ScoreInformationSource
