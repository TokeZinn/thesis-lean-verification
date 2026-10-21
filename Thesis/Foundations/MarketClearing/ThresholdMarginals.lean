import Thesis.Foundations.MarketClearing.ThresholdClearing
import Thesis.Foundations.MarketClearing.MidpointPrice

/-! # Characterizing the selected marginal price by cumulative price cuts -/

noncomputable section
namespace Thesis.Foundations.MarketClearing.ThresholdMarginals

open MarketRepresentation Sorting Equilibrium MidpointPrice ThresholdClearing

theorem below_reaches_index {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (r : ℝ) (v : Quantity) (hv : 0 < v) (hvr : v ≤ below p q r) :
    ∃ k, p k ≤ r ∧ v ≤ prefixQuantity q k := by
  let s := Finset.univ.filter (fun i => p i ≤ r)
  have hs : s.Nonempty := by
    by_contra hs
    have hz : below p q r = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => hs ⟨i, by simp [s, h]⟩)
    exact (not_le_of_gt hv) (hz ▸ hvr)
  let k := s.max' hs
  refine ⟨k, (Finset.mem_filter.mp (Finset.max'_mem s hs)).2, hvr.trans ?_⟩
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : p i ≤ r
  · have hik : i ≤ k := Finset.le_max' s i (by simp [s, hi])
    simp only [if_pos hi, if_pos hik]
    exact le_rfl
  · simp only [if_neg hi]
    exact zero_le _

theorem above_reaches_index {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (r : ℝ) (v : Quantity) (hv : 0 < v) (hvr : v ≤ above p q r) :
    ∃ k, r ≤ p k ∧ v ≤ prefixQuantity q k := by
  let s := Finset.univ.filter (fun i => r ≤ p i)
  have hs : s.Nonempty := by
    by_contra hs
    have hz : above p q r = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => hs ⟨i, by simp [s, h]⟩)
    exact (not_le_of_gt hv) (hz ▸ hvr)
  let k := s.max' hs
  refine ⟨k, (Finset.mem_filter.mp (Finset.max'_mem s hs)).2, hvr.trans ?_⟩
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : r ≤ p i
  · have hik : i ≤ k := Finset.le_max' s i (by simp [s, hi])
    simp only [if_pos hi, if_pos hik]
    exact le_rfl
  · simp only [if_neg hi]
    exact zero_le _

theorem marginal_le_iff_below {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (hp : Monotone p) (v : Quantity) {i : ℕ}
    (hi : ReachesFirst ((cumulativeQuantityTuple ⟨n, q⟩, ⟨n, p⟩), v) i) (r : ℝ) :
    marginalPrice ((cumulativeQuantityTuple ⟨n, q⟩, ⟨n, p⟩), v) ≤ r ↔ v ≤ below p q r := by
  have hilt : i < n := reachesFirst_in_domain hi
  have hv : v ≤ prefixQuantity q ⟨i, hilt⟩ := by
    have he := eval_cumulative q ⟨i, hilt⟩
    exact he ▸ hi.2.1
  rw [marginalPrice_eq hi]
  simp only [tuplePriceEval, dif_pos hilt]
  constructor
  · intro hpr
    apply hv.trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ (⟨i, hilt⟩ : Fin n)
    · simp only [if_pos hj, if_pos ((hp hj).trans hpr)]
      exact le_rfl
    · simp only [if_neg hj]
      exact zero_le _
  · intro hvr
    obtain ⟨k, hpk, hvk⟩ := below_reaches_index p q r v hi.1 hvr
    have hik : (⟨i, hilt⟩ : Fin n) ≤ k := by
      by_contra h
      have hk := hi.2.2 k.val (Nat.lt_of_not_ge h)
      rw [eval_cumulative] at hk
      exact (not_lt_of_ge hvk) hk
    exact (hp hik).trans hpk

theorem le_marginal_iff_above {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (hp : Antitone p) (v : Quantity) {i : ℕ}
    (hi : ReachesFirst ((cumulativeQuantityTuple ⟨n, q⟩, ⟨n, p⟩), v) i) (r : ℝ) :
    r ≤ marginalPrice ((cumulativeQuantityTuple ⟨n, q⟩, ⟨n, p⟩), v) ↔ v ≤ above p q r := by
  have hilt : i < n := reachesFirst_in_domain hi
  have hv : v ≤ prefixQuantity q ⟨i, hilt⟩ := by
    have he := eval_cumulative q ⟨i, hilt⟩
    exact he ▸ hi.2.1
  rw [marginalPrice_eq hi]
  simp only [tuplePriceEval, dif_pos hilt]
  constructor
  · intro hpr
    apply hv.trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ (⟨i, hilt⟩ : Fin n)
    · simp only [if_pos hj, if_pos (hpr.trans (hp hj))]
      exact le_rfl
    · simp only [if_neg hj]
      exact zero_le _
  · intro hvr
    obtain ⟨k, hpk, hvk⟩ := above_reaches_index p q r v hi.1 hvr
    have hik : (⟨i, hilt⟩ : Fin n) ≤ k := by
      by_contra h
      have hk := hi.2.2 k.val (Nat.lt_of_not_ge h)
      rw [eval_cumulative] at hk
      exact (not_lt_of_ge hvk) hk
    exact hpk.trans (hp hik)

end Thesis.Foundations.MarketClearing.ThresholdMarginals
