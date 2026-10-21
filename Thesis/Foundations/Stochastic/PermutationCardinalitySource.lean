import Thesis.Foundations.Stochastic.PermutationMultiplicity
import Mathlib.Data.Fintype.BigOperators

/-! # The exact permutation-class cardinality formula (interface module)

The equal-fibre counting argument of `prop:finite-equivalence-classes` now
lives in `PermutationMultiplicity` (`toOrbit`, `orbit_card_mul_multiplicities`,
`orbit_ncard_eq_factorial_div`), which carries the label. This module is
retained for interface stability only: it re-exports those declarations under
their former qualified names.
-/

noncomputable section
namespace Thesis.Foundations.Stochastic.PermutationCardinalitySource

export Thesis.Foundations.Stochastic.PermutationMultiplicity
  (toOrbit orbit_card_mul_multiplicities orbit_ncard_eq_factorial_div)

end Thesis.Foundations.Stochastic.PermutationCardinalitySource
