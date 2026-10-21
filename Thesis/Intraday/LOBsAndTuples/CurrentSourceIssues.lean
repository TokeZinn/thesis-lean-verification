import Mathlib.Tactic

/-! # Historical counterexamples and domain witnesses (earlier thesis draft)

These witnesses supported source discrepancies found in the 2026-10-20 audit
snapshot of the thesis. The current thesis text has since been corrected
(explicit reconstruction-time restriction; strict lexicographic identifier
order `h`), so they document the historical defect and are not statements
about the current source. They are not substitutes for any of the thesis's
positive theorems.
-/

namespace Thesis.Intraday.CurrentSourceIssues

/-- Historical: an earlier draft's reconstruction accepted broadcast/priority
times that the order space cannot contain, without a restriction or
re-normalisation; the current text restricts reconstruction times. -/
theorem reconstruction_time_outside_order_space :
    (1.02 : ℝ) ∈ Set.Ico (0 : ℝ) 1.05 ∧ ¬((1.02 : ℝ) ∈ Set.Icc (0 : ℝ) 1) := by
  norm_num

/-- Historical: an earlier draft's identifier relation used an undefined
priority-tie notation with weak identifier inequality; read as equal
price-time keys, that violates antisymmetry at repeated identifiers and
different quantities. The current definition uses the strict lexicographic
side–price–time key instead. -/
def weakIdentifierTie (x y : ℝ × ℕ) : Prop := x.2 ≤ y.2

theorem weak_identifier_tie_not_antisymmetric :
    weakIdentifierTie (1, 7) (2, 7) ∧ weakIdentifierTie (2, 7) (1, 7) ∧
      ((1, 7) : ℝ × ℕ) ≠ (2, 7) := by
  norm_num [weakIdentifierTie]

end Thesis.Intraday.CurrentSourceIssues
