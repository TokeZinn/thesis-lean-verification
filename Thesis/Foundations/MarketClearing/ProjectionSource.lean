import Thesis.Foundations.MarketClearing.Alignment

/-! # Tuple projection continuity by the source's Hausdorff estimate

The thesis `δ = ε` proof of `prop:tuple-projection-continuous` now lives in
`Selection` (`continuous_tupleProjection_tupleHausdorff` and its coordinatewise
consequence `continuous_tupleDecomposition_tupleHausdorff`), where it is the
mapped proof. This module is retained for interface stability and only aliases
those names. -/

namespace Thesis.Foundations.MarketClearing.ProjectionSource

open MarketRepresentation TuplesBasic TuplesMetricTopology Selection Alignment

/-- Alias of the mapped proof `Selection.continuous_tupleProjection_tupleHausdorff`. -/
alias continuous_tupleProjection := Selection.continuous_tupleProjection_tupleHausdorff

/-- Alias of the mapped proof `Selection.continuous_tupleDecomposition_tupleHausdorff`. -/
alias continuous_tupleDecomposition := Selection.continuous_tupleDecomposition_tupleHausdorff

end Thesis.Foundations.MarketClearing.ProjectionSource
