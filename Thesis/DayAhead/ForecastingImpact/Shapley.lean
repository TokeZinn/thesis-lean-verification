import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-! # Finite coalition games

The current forecasting chapter, equations `eq:Shapley-value` and
`eq:delta-shap`. The algebra applies to Hilbert-valued games, but needs only
a real module. Substitution of conditional-expectation endpoints is a
separate question: see `AttributionVersions.lean`.
-/

noncomputable section
namespace Thesis.DayAhead.Shapley

open Finset
open scoped BigOperators

variable {α H : Type*} [Fintype α] [DecidableEq α]
variable [AddCommGroup H] [Module ℝ H]

def weight (n k : ℕ) : ℝ :=
  (k.factorial : ℝ) * ((n - k - 1).factorial : ℝ) / (n.factorial : ℝ)

theorem weight_nonneg (n k : ℕ) : 0 ≤ weight n k := by
  unfold weight
  positivity

theorem subsets_without (i : α) :
    (univ.erase i).powerset = (univ : Finset (Finset α)).filter (fun S => i ∉ S) := by
  ext S
  simp [subset_erase]

omit [Module ℝ H] in
theorem sum_insert_without (i : α) (f : Finset α → H) :
    (∑ S ∈ (univ : Finset (Finset α)).filter (fun S => i ∉ S), f (insert i S)) =
      ∑ T ∈ (univ : Finset (Finset α)).filter (fun T => i ∈ T), f T := by
  refine sum_bij (fun S _ => insert i S) ?_ ?_ ?_ ?_
  · intro S _
    simp
  · intro S hS T hT h
    have hS' : i ∉ S := (mem_filter.mp hS).2
    have hT' : i ∉ T := (mem_filter.mp hT).2
    simpa [erase_insert hS', erase_insert hT'] using congrArg (fun U => U.erase i) h
  · intro T hT
    refine ⟨T.erase i, by simp, ?_⟩
    exact insert_erase (mem_filter.mp hT).2
  · intro S _
    rfl

theorem positive_contributions (V : Finset α → H) (i : α) :
    (∑ S ∈ (univ.erase i).powerset,
      weight (Fintype.card α) S.card • V (insert i S)) =
      ∑ T ∈ (univ : Finset (Finset α)).filter (fun T => i ∈ T),
        weight (Fintype.card α) (T.card - 1) • V T := by
  rw [subsets_without]
  calc
    _ = ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => i ∉ S),
        weight (Fintype.card α) ((insert i S).card - 1) • V (insert i S) := by
      apply sum_congr rfl
      intro S hS
      simp [card_insert_of_notMem (mem_filter.mp hS).2]
    _ = _ := sum_insert_without i (fun T => weight (Fintype.card α) (T.card - 1) • V T)

theorem weight_balance {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    (k : ℝ) * weight n (k - 1) = ((n - k : ℕ) : ℝ) * weight n k := by
  have hkfac : k.factorial = k * (k - 1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, Nat.factorial_succ]
    rw [Nat.sub_add_cancel hk]
  have hnfac : (n - k).factorial = (n - k) * (n - k - 1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n - k), Nat.factorial_succ]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n - k)]
  have he : n - (k - 1) - 1 = n - k := by omega
  simp only [weight, he, hkfac, hnfac, Nat.cast_mul]
  ring

theorem weight_endpoint {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * weight n 0 = 1 ∧ (n : ℝ) * weight n (n - 1) = 1 := by
  have hfac : n.factorial = n * (n - 1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, Nat.factorial_succ]
    rw [Nat.sub_add_cancel hn]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hf : ((n - 1).factorial : ℝ) ≠ 0 := by positivity
  have he : n - (n - 1) - 1 = 0 := by omega
  simp only [weight, he, hfac, Nat.cast_mul, Nat.factorial_zero, Nat.cast_one,
    Nat.sub_zero, one_mul, mul_one]
  constructor <;> field_simp

def membershipGame (i : α) (S : Finset α) : ℝ := if i ∈ S then 1 else 0

end Thesis.DayAhead.Shapley
