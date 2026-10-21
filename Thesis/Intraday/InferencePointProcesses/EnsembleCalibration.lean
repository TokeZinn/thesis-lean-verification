import Thesis.Intraday.InferencePointProcesses.EnsembleRanks
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Exact discrete reference for current ensemble coverage

`defn:ensemble-mid-rank-coverage` and the finite reference-law calculation of
`prop:midrank-coverage-expectations`. Strict-rank uniformity from exchangeability
and the asymptotic count limits remain separate probability/combinatorics work.
The old constant-model counterexample is compatible with the new no-ties
assumption and is not reported as an error in the current proposition.
-/

noncomputable section
namespace Thesis.Intraday.EnsembleCalibration
open MeasureTheory
open scoped BigOperators

def central (alpha u : ℝ) : Prop := alpha / 2 ≤ u ∧ u ≤ 1 - alpha / 2

instance (alpha u : ℝ) : Decidable (central alpha u) :=
  inferInstanceAs (Decidable (alpha / 2 ≤ u ∧ u ≤ 1 - alpha / 2))

def centralReference (B : ℕ) (alpha : ℝ) : ℝ :=
  (∑ j : Fin (B + 1), if central alpha ((j.val : ℝ) / B) then (1 : ℝ) else 0) / (B + 1)

def centralFraction {D : ℕ} (alpha : ℝ) (ranks : Fin D → ℝ) : ℝ :=
  (∑ d, if central alpha (ranks d) then (1 : ℝ) else 0) / D

def upperFraction {D : ℕ} (alpha : ℝ) (ranks : Fin D → ℝ) : ℝ :=
  (∑ d, if ranks d ≤ 1 - alpha then (1 : ℝ) else 0) / D

theorem centralReference_card (B : ℕ) (alpha : ℝ) :
    centralReference B alpha =
      ((Finset.univ.filter fun j : Fin (B+1) => central alpha ((j.val : ℝ) / B)).card : ℝ) /
        (B+1) := by
  simp [centralReference]

/-- The finite-B reference probability, after strict-rank uniformity has
been established. This retains the endpoints 0 and B and divides by B+1. -/
theorem central_reference_expectation (B : ℕ) (alpha : ℝ) :
    ∫ j : Fin (B+1), (if central alpha ((j.val : ℝ) / B) then (1 : ℝ) else 0)
      ∂(PMF.uniformOfFintype (Fin (B+1))).toMeasure = centralReference B alpha := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  simp_rw [mul_comm ((B+1 : ℕ) : ℝ)⁻¹]
  simp only [centralReference, div_eq_mul_inv, Finset.sum_mul, Nat.cast_add, Nat.cast_one]

theorem constant_coverage_one {D : ℕ} (hD : 0 < D) (alpha : ℝ) (ha : alpha ≤ 1) :
    centralFraction alpha (fun _ : Fin D => 1/2) = 1 := by
  have hcentral : central alpha (1/2) := by constructor <;> linarith
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  simp only [centralFraction, if_pos hcentral, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, div_self hd]

end Thesis.Intraday.EnsembleCalibration
