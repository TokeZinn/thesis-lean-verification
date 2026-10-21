import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

namespace Thesis.Foundations.Research.RevenueConcavity

/-- A continuous monotone piecewise-affine impact curve. -/
def price (q : ℝ) : ℝ := min q 1

theorem price_monotone : Monotone price := fun _ _ h ↦ min_le_min_right 1 h
theorem price_continuous : Continuous price := continuous_id.min continuous_const

def revenue (q : ℝ) : ℝ := -q * price q

/-- Monotone impact does not imply concave hourly battery revenue. This is the
specific false inference in conclusion.tex:76. Dynamic programming on a finite
state grid does not require concavity. -/
theorem revenue_violates_midpoint_concavity :
    revenue ((1 / 2 + 3 / 2) / 2) < (revenue (1 / 2) + revenue (3 / 2)) / 2 := by
  norm_num [revenue, price]

theorem revenue_not_concave : ¬ ConcaveOn ℝ (Set.Icc (0 : ℝ) 2) revenue := by
  intro h
  have hc := h.2 (show (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 2 by norm_num)
    (show (3 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num [revenue, price] at hc

end Thesis.Foundations.Research.RevenueConcavity
