import Thesis.DayAhead.ClearingOperatorPriceCurves.ImpactVolumeBounds
import Thesis.Foundations.MarketClearing.QuantityPerturbation

/-! # Extreme-price perturbations and the actual marginal selector

The added order may occur anywhere among equal extreme prices. Tracking its
position gives the marginal-price comparison without a tie-breaking shortcut.
-/

noncomputable section
namespace Thesis.DayAhead.ImpactMarginals

open Foundations.MarketRepresentation
open Foundations.MarketClearing.Sorting Foundations.MarketClearing.Equilibrium
open Foundations.MarketClearing.MidpointPrice
open Foundations.MarketClearing.QuantityPerturbation

theorem perturbed_marginal_index_le (x : Tuple Quantity) (p : Fin x.1 → ℝ)
    (t : Fin x.1) (δ v w : Quantity) {i j : ℕ}
    (hi : ReachesFirst ((cumulativeQuantityTuple x, ⟨x.1, p⟩), v) i)
    (hj : ReachesFirst ((cumulativeQuantityTuple (addAt x t δ), ⟨x.1, p⟩), w) j)
    (hw : w ≤ v + δ) : j ≤ max i t.val := by
  have hilt : i < x.1 := reachesFirst_in_domain hi
  let k : Fin x.1 := ⟨max i t.val, max_lt hilt t.isLt⟩
  have htk : t ≤ k := show t.val ≤ max i t.val from le_max_right _ _
  have hik : (⟨i, hilt⟩ : Fin x.1) ≤ k := le_max_left _ _
  have hcum : v ≤ (cumulativeQuantityTuple x).2 ⟨i, hilt⟩ := by
    have he : tupleQuantityEval i (cumulativeQuantityTuple x) =
        (cumulativeQuantityTuple x).2 ⟨i, hilt⟩ := dif_pos hilt
    exact he ▸ hi.2.1
  have hnew : w ≤ (cumulativeQuantityTuple (addAt x t δ)).2 k := by
    rw [cumulative_addAt, if_pos htk]
    exact hw.trans (add_le_add (hcum.trans (cumulative_monotone x hik)) le_rfl)
  by_contra h
  have hklt : k.val < j := Nat.lt_of_not_ge h
  have hbefore := hj.2.2 k.val hklt
  have hk : k.val < x.1 := k.isLt
  have he : tupleQuantityEval k.val (cumulativeQuantityTuple (addAt x t δ)) =
      (cumulativeQuantityTuple (addAt x t δ)).2 k := dif_pos hk
  exact (not_lt_of_ge hnew) (he ▸ hbefore)

theorem buy_marginal_addAt (x : Tuple Quantity) (p : Fin x.1 → ℝ)
    (hp : Antitone p) (t : Fin x.1) (ht : ∀ k, p k ≤ p t) (δ v w : Quantity) {i j : ℕ}
    (hi : ReachesFirst ((cumulativeQuantityTuple x, ⟨x.1, p⟩), v) i)
    (hj : ReachesFirst ((cumulativeQuantityTuple (addAt x t δ), ⟨x.1, p⟩), w) j)
    (hw : w ≤ v + δ) :
    marginalPrice ((cumulativeQuantityTuple x, ⟨x.1, p⟩), v) ≤
      marginalPrice ((cumulativeQuantityTuple (addAt x t δ), ⟨x.1, p⟩), w) := by
  have hilt : i < x.1 := reachesFirst_in_domain hi
  have hjlt : j < x.1 := reachesFirst_in_domain hj
  have hbound := perturbed_marginal_index_le x p t δ v w hi hj hw
  rw [marginalPrice_eq hi, marginalPrice_eq hj]
  simp only [tuplePriceEval, dif_pos hilt, dif_pos hjlt]
  change p ⟨i, hilt⟩ ≤ p ⟨j, hjlt⟩
  rcases le_total i t.val with h | h
  · rw [max_eq_right h] at hbound
    exact (ht ⟨i, hilt⟩).trans (hp (show (⟨j, hjlt⟩ : Fin x.1) ≤ t from hbound))
  · rw [max_eq_left h] at hbound
    exact hp (show (⟨j, hjlt⟩ : Fin x.1) ≤ ⟨i, hilt⟩ from hbound)

theorem sell_marginal_addAt (x : Tuple Quantity) (p : Fin x.1 → ℝ)
    (hp : Monotone p) (t : Fin x.1) (ht : ∀ k, p t ≤ p k) (δ v w : Quantity) {i j : ℕ}
    (hi : ReachesFirst ((cumulativeQuantityTuple x, ⟨x.1, p⟩), v) i)
    (hj : ReachesFirst ((cumulativeQuantityTuple (addAt x t δ), ⟨x.1, p⟩), w) j)
    (hw : w ≤ v + δ) :
    marginalPrice ((cumulativeQuantityTuple (addAt x t δ), ⟨x.1, p⟩), w) ≤
      marginalPrice ((cumulativeQuantityTuple x, ⟨x.1, p⟩), v) := by
  have hilt : i < x.1 := reachesFirst_in_domain hi
  have hjlt : j < x.1 := reachesFirst_in_domain hj
  have hbound := perturbed_marginal_index_le x p t δ v w hi hj hw
  rw [marginalPrice_eq hi, marginalPrice_eq hj]
  simp only [tuplePriceEval, dif_pos hilt, dif_pos hjlt]
  change p ⟨j, hjlt⟩ ≤ p ⟨i, hilt⟩
  rcases le_total i t.val with h | h
  · rw [max_eq_right h] at hbound
    exact (hp (show (⟨j, hjlt⟩ : Fin x.1) ≤ t from hbound)).trans (ht ⟨i, hilt⟩)
  · rw [max_eq_left h] at hbound
    exact hp (show (⟨j, hjlt⟩ : Fin x.1) ≤ ⟨i, hilt⟩ from hbound)

end Thesis.DayAhead.ImpactMarginals
