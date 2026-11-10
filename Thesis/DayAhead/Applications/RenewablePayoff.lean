import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # The paired renewable payoff proxies

Applications chapter, lines 79–110. The viability screen is all-or-nothing;
both proxies use the same eligible periods and the same scheduled production.
The realized production enters residual production, not the submitted volume.
These definitions require the source curve at zero and at the negative schedule.
-/

noncomputable section
namespace Thesis.DayAhead.RenewablePayoff

open scoped BigOperators

/-- Screened submitted volume, as used by both payoff and residual formulas. -/
def accepted (P : ℝ → ℝ) (marginal schedule : ℝ) : ℝ :=
  if marginal ≤ P (-schedule) then schedule else 0

theorem accepted_bounds (P : ℝ → ℝ) (marginal : ℝ) {schedule : ℝ} (hq : 0 ≤ schedule) :
    0 ≤ accepted P marginal schedule ∧ accepted P marginal schedule ≤ schedule := by
  unfold accepted
  split <;> simp_all

/-- Adding nonnegative sell volume cannot raise an increasing impact curve's price. -/
theorem price_impact_nonpos (P : ℝ → ℝ) (hP : Monotone P) {schedule : ℝ}
    (hq : 0 ≤ schedule) : P (-schedule) ≤ P 0 := hP (neg_nonpos.mpr hq)

theorem impact_acceptance_implies_baseline (P : ℝ → ℝ) (hP : Monotone P)
    {marginal schedule : ℝ} (hq : 0 ≤ schedule) (haccept : marginal ≤ P (-schedule)) :
    marginal ≤ P 0 := haccept.trans (price_impact_nonpos P hP hq)

end Thesis.DayAhead.RenewablePayoff
