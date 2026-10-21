import Thesis.Appendices.FunctionalAnalysis.DoctoralFunctionalAnalysis
import Thesis.Appendices.Analysis.AnalysisBasic

/-! # Explicit radius and remainder arguments from the doctoral source

The thesis-faithful proofs that used to live here now sit on the primary
modules: `AnalysisBasic` carries `half_slack_refinement` and
`metricBalls_isTopologicalBase` (`prop:topology-extended-pseudometric`) and
`half_distance_balls_disjoint` and `pseudoEMetricTopology_hausdorff_iff`
(`source:A - appendices/analysis.tex:255:prop:19`); `DoctoralFunctionalAnalysis`
carries `squared_loss_remainder`, `squared_loss_linear_bound`,
`squared_loss_remainder_ratio`, `squared_loss_remainder_ratio_tendsto` and
`squared_loss_hasFDerivAt` (`lem:squared-loss-gradient`).  This module is
retained for interface stability and only re-exports those names. -/

noncomputable section
namespace Thesis.Foundations.Preliminary.SourceAnalysisProofs

export Thesis.Foundations.Preliminary.Analysis
  (half_slack_refinement half_distance_balls_disjoint)

/-- Moved to `AnalysisBasic` as `metricBalls_isTopologicalBase`; kept as an alias. -/
alias metricBalls_isTopologicalBase_source :=
  Thesis.Foundations.Preliminary.Analysis.metricBalls_isTopologicalBase

/-- Moved to `AnalysisBasic` as `pseudoEMetricTopology_hausdorff_iff`; kept as an alias. -/
alias pseudoEMetricTopology_hausdorff_iff_source :=
  Thesis.Foundations.Preliminary.Analysis.pseudoEMetricTopology_hausdorff_iff

export Thesis.Foundations.Preliminary.DoctoralFunctionalAnalysis
  (squared_loss_remainder squared_loss_linear_bound squared_loss_remainder_ratio
    squared_loss_remainder_ratio_tendsto)

/-- Moved to `DoctoralFunctionalAnalysis` as `squared_loss_hasFDerivAt`; kept as an alias. -/
alias squared_loss_hasFDerivAt_source :=
  Thesis.Foundations.Preliminary.DoctoralFunctionalAnalysis.squared_loss_hasFDerivAt

end Thesis.Foundations.Preliminary.SourceAnalysisProofs
