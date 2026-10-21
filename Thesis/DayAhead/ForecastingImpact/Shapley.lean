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

/-- Original label: `defn:hilbert-shapley-value`. -/
def marginal (V : Finset α → H) (S : Finset α) (i : α) : H := V (insert i S) - V S

/-- Original label: `defn:hilbert-shapley-value`. -/
def value (V : Finset α → H) (i : α) : H :=
  ∑ S ∈ (univ.erase i).powerset, weight (Fintype.card α) S.card • marginal V S i

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

theorem value_coefficient_formula (V : Finset α → H) :
    ∑ i, value V i = ∑ T : Finset α,
      ((T.card : ℝ) * weight (Fintype.card α) (T.card - 1) -
        ((Fintype.card α - T.card : ℕ) : ℝ) * weight (Fintype.card α) T.card) • V T := by
  simp only [value, marginal, smul_sub, sum_sub_distrib]
  simp_rw [positive_contributions, subsets_without, sum_filter]
  conv_lhs => lhs; rw [sum_comm]
  conv_lhs => rhs; rw [sum_comm]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro T _
  have hmem : (univ.filter fun i : α => i ∈ T) = T := by ext; simp
  have hnmem : (univ.filter fun i : α => i ∉ T) = univ \ T := by ext; simp
  simp only [← sum_filter, sum_const, hmem, hnmem, card_sdiff, inter_univ, card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul,
    ← sub_smul]

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

/-- Efficiency for the actual factorial-weighted coalition formula. -/
theorem efficiency_nonempty [Nonempty α] (V : Finset α → H) :
    ∑ i, value V i = V univ - V ∅ := by
  classical
  rw [value_coefficient_formula]
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hend := weight_endpoint hn
  have he : (∅ : Finset α) ≠ univ := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  have hterm (T : Finset α) :
      ((T.card : ℝ) * weight (Fintype.card α) (T.card - 1) -
        ((Fintype.card α - T.card : ℕ) : ℝ) * weight (Fintype.card α) T.card) • V T =
      (if T = univ then V univ else 0) - (if T = ∅ then V ∅ else 0) := by
    by_cases hzero : T = ∅
    · subst T
      simp [he, hend.1]
    by_cases hfull : T = univ
    · subst T
      simp [Ne.symm he, hend.2]
    have hk : 0 < T.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hzero)
    have hkn : T.card < Fintype.card α := by
      have := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ T, hfull⟩)
      simpa using this
    rw [weight_balance hk hkn, sub_self, zero_smul]
    simp [hzero, hfull]
  simp_rw [hterm]
  rw [sum_sub_distrib]
  simp

theorem efficiency (V : Finset α → H) : ∑ i, value V i = V univ - V ∅ := by
  cases isEmpty_or_nonempty α with
  | inl h =>
    letI : IsEmpty α := h
    simp
  | inr h =>
    letI : Nonempty α := h
    exact efficiency_nonempty V

/-- Pointwise prediction efficiency needs explicit endpoint values. -/
theorem efficiency_of_endpoints (V : Finset α → H) (prediction baseline : H)
    (hfull : V univ = prediction) (hempty : V ∅ = baseline) :
    ∑ i, value V i = prediction - baseline := by
  rw [efficiency, hfull, hempty]

theorem value_add (V W : Finset α → H) (i : α) :
    value (fun S => V S + W S) i = value V i + value W i := by
  simp only [value, marginal, add_sub_add_comm, smul_add, sum_add_distrib]

theorem value_smul (r : ℝ) (V : Finset α → H) (i : α) :
    value (fun S => r • V S) i = r • value V i := by
  simp only [value, marginal, ← smul_sub, smul_comm (weight _ _), smul_sum]

/-- A feature with zero marginal contribution on every eligible coalition has zero value. -/
theorem value_dummy (V : Finset α → H) (i : α)
    (h : ∀ S : Finset α, i ∉ S → V (insert i S) = V S) : value V i = 0 := by
  apply sum_eq_zero
  intro S hS
  have hi : i ∉ S := by
    have hs := mem_powerset.mp hS
    exact notMem_mono hs (notMem_erase i univ)
  simp [marginal, h S hi]

def membershipGame (i : α) (S : Finset α) : ℝ := if i ∈ S then 1 else 0

theorem value_membership_other {i j : α} (hij : i ≠ j) : value (membershipGame i) j = 0 := by
  apply value_dummy
  intro S _
  simp [membershipGame, hij]

theorem value_membership_self (i : α) : value (membershipGame i) i =
    ∑ S ∈ (univ.erase i).powerset, weight (Fintype.card α) S.card := by
  apply sum_congr rfl
  intro S hS
  have hi : i ∉ S := notMem_mono (mem_powerset.mp hS) (notMem_erase i univ)
  simp [marginal, membershipGame, hi]

/-- The factorial coefficients are a probability weight on eligible coalitions. -/
theorem weight_sum (i : α) :
    ∑ S ∈ (univ.erase i).powerset, weight (Fintype.card α) S.card = 1 := by
  rw [← value_membership_self]
  have hs : ∑ j, value (membershipGame i) j = value (membershipGame i) i := by
    apply sum_eq_single i
    · intro j _ hj
      exact value_membership_other (Ne.symm hj)
    · simp
  rw [← hs, efficiency]
  simp [membershipGame]

end Thesis.DayAhead.Shapley
