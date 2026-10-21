import Thesis.Foundations.MarketClearing.DoctoralSemicontinuity
import Mathlib.Topology.Order.LiminfLimsup

/-! # The thesis proof of executable-volume upper semicontinuity

The thesis route to `prop:executable-volume-usc` (i) (fix the limit's lengths,
exclude its finitely many infeasible pairs, dominate by the maximum `g` over its
fixed feasible index set, and take the limsup) now lives in
`DoctoralSemicontinuity` (`fixedIndexVolume`, `eventually_feasible_subset`,
`eventually_le_fixedIndexVolume`, `sequence_limsup_le`,
`upperSemicontinuous_equilibriumQuantity`), where it is the mapped proof. This
module is retained for interface stability and only re-exports / aliases those
names. -/

noncomputable section
namespace Thesis.Foundations.MarketClearing.DoctoralSemicontinuitySource

open MarketRepresentation TuplesBasic TuplesMetricTopology
open Sorting Equilibrium MidpointPrice DoctoralSemicontinuity
open Filter Set Topology

export DoctoralSemicontinuity (fixedIndexVolume fixedIndexVolume_self
  continuous_fixedIndexVolume eventually_feasible_subset
  eventually_le_fixedIndexVolume sequence_limsup_le)

/-- Alias of the mapped proof `DoctoralSemicontinuity.upperSemicontinuous_equilibriumQuantity`. -/
alias upperSemicontinuous_equilibriumQuantity_sourceProof :=
  DoctoralSemicontinuity.upperSemicontinuous_equilibriumQuantity

end Thesis.Foundations.MarketClearing.DoctoralSemicontinuitySource
