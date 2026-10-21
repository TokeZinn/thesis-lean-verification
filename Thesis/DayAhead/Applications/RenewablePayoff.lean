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

/-- Original label: `defn:viability-screen-impact-cost`. -/
def screen (P : ℝ → ℝ) (marginal schedule : ℝ) : ℝ :=
  if marginal ≤ P (-schedule) then 1 else 0

/-- Screened submitted volume, as used by both payoff and residual formulas. -/
def accepted (P : ℝ → ℝ) (marginal schedule : ℝ) : ℝ :=
  if marginal ≤ P (-schedule) then schedule else 0

theorem accepted_eq_screened_schedule (P : ℝ → ℝ) (marginal schedule : ℝ) :
    accepted P marginal schedule = screen P marginal schedule * schedule := by
  unfold accepted screen
  split <;> simp

/-- Original label: `defn:viability-screen-impact-cost`. -/
def impactPayoff (P : ℝ → ℝ) (marginal schedule : ℝ) : ℝ :=
  accepted P marginal schedule * P (-schedule)

/-- Original label: `defn:viability-screen-impact-cost`. -/
def baselinePayoff (P : ℝ → ℝ) (marginal schedule : ℝ) : ℝ :=
  if marginal ≤ P 0 then schedule * P 0 else 0

/-- Original label: `defn:viability-screen-impact-cost`. -/
def residual (production : ℝ) (P : ℝ → ℝ) (marginal schedule : ℝ) : ℝ :=
  production - accepted P marginal schedule

theorem accepted_bounds (P : ℝ → ℝ) (marginal : ℝ) {schedule : ℝ} (hq : 0 ≤ schedule) :
    0 ≤ accepted P marginal schedule ∧ accepted P marginal schedule ≤ schedule := by
  unfold accepted
  split <;> simp_all

theorem residual_balance (production : ℝ) (P : ℝ → ℝ) (marginal schedule : ℝ) :
    residual production P marginal schedule + accepted P marginal schedule = production := by
  simp [residual]

theorem residual_rejected (production : ℝ) (P : ℝ → ℝ) (marginal schedule : ℝ)
    (hreject : P (-schedule) < marginal) :
    residual production P marginal schedule = production := by
  simp [residual, accepted, not_le.mpr hreject]

/-- Adding nonnegative sell volume cannot raise an increasing impact curve's price. -/
theorem price_impact_nonpos (P : ℝ → ℝ) (hP : Monotone P) {schedule : ℝ}
    (hq : 0 ≤ schedule) : P (-schedule) ≤ P 0 := hP (neg_nonpos.mpr hq)

theorem impact_acceptance_implies_baseline (P : ℝ → ℝ) (hP : Monotone P)
    {marginal schedule : ℝ} (hq : 0 ≤ schedule) (haccept : marginal ≤ P (-schedule)) :
    marginal ≤ P 0 := haccept.trans (price_impact_nonpos P hP hq)

/-- At a nonnegative marginal-price screen, the paired impact difference is nonnegative.
The exercise uses marginal price zero. -/
theorem payoff_le_baseline (P : ℝ → ℝ) (hP : Monotone P) {marginal schedule : ℝ}
    (hc : 0 ≤ marginal) (hq : 0 ≤ schedule) :
    impactPayoff P marginal schedule ≤ baselinePayoff P marginal schedule := by
  by_cases ha : marginal ≤ P (-schedule)
  · have hb := impact_acceptance_implies_baseline P hP hq ha
    simp only [impactPayoff, accepted, baselinePayoff, if_pos ha, if_pos hb]
    exact mul_le_mul_of_nonneg_left (price_impact_nonpos P hP hq) hq
  · simp only [impactPayoff, accepted, if_neg ha, zero_mul, baselinePayoff]
    split_ifs with hb
    · exact mul_nonneg hq (hc.trans hb)
    · rfl

/-- Original label: `defn:viability-screen-impact-cost`. -/
def pairedDifference {T : Type*} (eligible : Finset T) (P : T → ℝ → ℝ)
    (marginal : ℝ) (schedule : T → ℝ) : ℝ :=
  ∑ t ∈ eligible, (baselinePayoff (P t) marginal (schedule t) -
    impactPayoff (P t) marginal (schedule t))

theorem pairedDifference_eq_totals {T : Type*} (eligible : Finset T) (P : T → ℝ → ℝ)
    (marginal : ℝ) (schedule : T → ℝ) : pairedDifference eligible P marginal schedule =
      (∑ t ∈ eligible, baselinePayoff (P t) marginal (schedule t)) -
      ∑ t ∈ eligible, impactPayoff (P t) marginal (schedule t) := by
  exact Finset.sum_sub_distrib _ _

end Thesis.DayAhead.RenewablePayoff
