import Thesis.Foundations.MarketClearing.MidpointPrice
import Mathlib.Tactic

/-! # Volume inequalities underlying the market-impact proof

The positive perturbation argument in Chapter 10, lines 124–136, uses a
finite maximum of compatible cumulative quantities. This module verifies
its monotonicity and unit increment bound, and the actual marginal selector's
order property. `ImpactClearing.lean` proves those volume inequalities for
the actual perturbed raw market directly, while `ImpactMonotonicity.lean`
proves the price comparisons under explicit positive-volume hypotheses.
-/

noncomputable section
namespace Thesis.DayAhead.ImpactVolumeBounds

open Finset
open scoped NNReal
open Foundations.MarketClearing.MidpointPrice Foundations.MarketClearing.Equilibrium
open Foundations.MarketClearing.Sorting
open Foundations.MarketRepresentation TuplesBasic TuplesMeasurableSorting

def volume (compatible : Finset (ℕ × ℕ)) (supply demand : ℕ → ℝ≥0) (q : ℝ≥0) : ℝ≥0 :=
  max q (compatible.sup fun ij => min (supply ij.1) (q + demand ij.2))

theorem added_le_volume (compatible : Finset (ℕ × ℕ)) (supply demand : ℕ → ℝ≥0)
    (q : ℝ≥0) : q ≤ volume compatible supply demand q := le_max_left _ _

theorem volume_monotone (compatible : Finset (ℕ × ℕ)) (supply demand : ℕ → ℝ≥0) :
    Monotone (volume compatible supply demand) := by
  intro q r hqr
  apply max_le_max hqr
  apply Finset.sup_mono_fun
  intro ij _
  exact min_le_min_left _ (add_le_add hqr le_rfl)

theorem volume_add_le (compatible : Finset (ℕ × ℕ)) (supply demand : ℕ → ℝ≥0)
    (q δ : ℝ≥0) :
    volume compatible supply demand (q + δ) ≤ volume compatible supply demand q + δ := by
  apply max_le
  · exact add_le_add (added_le_volume compatible supply demand q) le_rfl
  apply Finset.sup_le
  intro ij hij
  calc
    min (supply ij.1) (q + δ + demand ij.2) ≤
        min (supply ij.1 + δ) (q + demand ij.2 + δ) := by
      apply min_le_min
      · exact le_add_of_nonneg_right (zero_le δ)
      · exact le_of_eq (by ac_rfl)
    _ = min (supply ij.1) (q + demand ij.2) + δ := min_add_add_right _ _ _
    _ ≤ volume compatible supply demand q + δ := by
      exact add_le_add ((le_sup (f := fun ij => min (supply ij.1) (q + demand ij.2)) hij).trans
        (le_max_right _ _)) le_rfl

theorem volume_increment (compatible : Finset (ℕ × ℕ)) (supply demand : ℕ → ℝ≥0)
    {q r : ℝ≥0} (hqr : q ≤ r) :
    0 ≤ (volume compatible supply demand r : ℝ) - volume compatible supply demand q ∧
      (volume compatible supply demand r : ℝ) - volume compatible supply demand q ≤
        (r : ℝ) - q := by
  have hm := volume_monotone compatible supply demand hqr
  have hu := volume_add_le compatible supply demand q (r - q)
  rw [add_tsub_cancel_of_le hqr] at hu
  have hc : ((r - q : ℝ≥0) : ℝ) = (r : ℝ) - q := NNReal.coe_sub hqr
  constructor
  · exact sub_nonneg.mpr hm
  · change (volume compatible supply demand r : ℝ) ≤
      (volume compatible supply demand q : ℝ) + ((r - q : ℝ≥0) : ℝ) at hu
    rw [hc] at hu
    linarith

theorem originalDemand_antitone (compatible : Finset (ℕ × ℕ)) (supply demand : ℕ → ℝ≥0) :
    Antitone (fun q : ℝ≥0 => (volume compatible supply demand q : ℝ) - q) := by
  intro q r hqr
  have h := (volume_increment compatible supply demand hqr).2
  linarith

/-- Increasing positive executed volume cannot move the first-reaching index backwards. -/
theorem reachesFirst_index_mono {s t : MarginalInput} {i j : ℕ}
    (hs : ReachesFirst s i) (ht : ReachesFirst t j) (hQ : s.1.1 = t.1.1)
    (hq : s.2 ≤ t.2) : i ≤ j := by
  by_contra hij
  have hj := hs.2.2 j (Nat.lt_of_not_ge hij)
  rw [hQ] at hj
  exact (not_lt_of_ge (hq.trans ht.2.1)) hj

theorem marginalPrice_mono {s t : MarginalInput} {i j : ℕ}
    (hs : ReachesFirst s i) (ht : ReachesFirst t j) (hQ : s.1.1 = t.1.1)
    (hp : s.1.2 = t.1.2) (hq : s.2 ≤ t.2)
    (hlen : s.1.1.1 = s.1.2.1)
    (hsorted : ∀ a b : ℕ, a ≤ b → b < s.1.2.1 →
      tuplePriceEval a s.1.2 ≤ tuplePriceEval b s.1.2) :
    marginalPrice s ≤ marginalPrice t := by
  rw [marginalPrice_eq hs, marginalPrice_eq ht, ← hp]
  apply hsorted i j (reachesFirst_index_mono hs ht hQ hq)
  rw [← hlen, hQ]
  exact reachesFirst_in_domain ht

theorem marginalPrice_antitone {s t : MarginalInput} {i j : ℕ}
    (hs : ReachesFirst s i) (ht : ReachesFirst t j) (hQ : s.1.1 = t.1.1)
    (hp : s.1.2 = t.1.2) (hq : s.2 ≤ t.2) (hlen : s.1.1.1 = s.1.2.1)
    (hsorted : ∀ a b : ℕ, a ≤ b → b < s.1.2.1 →
      tuplePriceEval b s.1.2 ≤ tuplePriceEval a s.1.2) :
    marginalPrice t ≤ marginalPrice s := by
  rw [marginalPrice_eq hs, marginalPrice_eq ht, ← hp]
  apply hsorted i j (reachesFirst_index_mono hs ht hQ hq)
  rw [← hlen, hQ]
  exact reachesFirst_in_domain ht

theorem tuplePriceEval_mono_of_isSorted {p : Tuple ℝ} (hp : IsSorted p)
    {i j : ℕ} (hij : i ≤ j) (hj : j < p.1) : tuplePriceEval i p ≤ tuplePriceEval j p := by
  have hi := lt_of_le_of_lt hij hj
  simp only [tuplePriceEval, dif_pos hi, dif_pos hj]
  exact (isSorted_iff_monotone p).mp hp ⟨i, hi⟩ ⟨j, hj⟩ hij

theorem dualize_sortedBuyPrice (m : MarketTuple) :
    dualizeRealTuple (sortedBuyPriceTuple m) =
      permutationMap (dualizeRealTuple (buyPriceTuple m))
        (realMinimalPermutationGE (buyPriceTuple m)) := by
  change dualizeRealTuple (permutationMap _ _) = _
  generalize buyPriceTuple m = x
  rcases x with ⟨n, x⟩
  simp only [realMinimalPermutationGE]
  rfl

/-- The actual sorted sell-book marginal is monotone in its positive executed volume. -/
theorem sell_marginal_mono (m : MarketTuple) {q r : Quantity} {i j : ℕ}
    (hq : ReachesFirst ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m), q) i)
    (hr : ReachesFirst ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m), r) j)
    (hqr : q ≤ r) :
    marginalPrice ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m), q) ≤
      marginalPrice ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m), r) := by
  apply marginalPrice_mono hq hr rfl rfl hqr (cumulativeSell_length_eq_price_length m)
  intro a b hab hb
  exact tuplePriceEval_mono_of_isSorted
    (realMinimalPermutationLE_sorts (sellPriceTuple m)) hab hb

/-- The actual sorted buy-book marginal is antitone in its positive executed volume. -/
theorem buy_marginal_antitone (m : MarketTuple) {q r : Quantity} {i j : ℕ}
    (hq : ReachesFirst ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m), q) i)
    (hr : ReachesFirst ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m), r) j)
    (hqr : q ≤ r) :
    marginalPrice ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m), r) ≤
      marginalPrice ((cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m), q) := by
  apply marginalPrice_antitone hq hr rfl rfl hqr (cumulativeBuy_length_eq_price_length m)
  intro a b hab hb
  have ha := lt_of_le_of_lt hab hb
  have hs : IsSorted (dualizeRealTuple (sortedBuyPriceTuple m)) := by
    rw [dualize_sortedBuyPrice]
    exact realMinimalPermutationGE_sorts_dual _
  simp only [tuplePriceEval, dif_pos ha, dif_pos hb]
  exact (isSorted_iff_monotone _).mp hs ⟨a, ha⟩ ⟨b, hb⟩ hab

theorem midpoint_monotone (compatible : Finset (ℕ × ℕ)) (supply demand : ℕ → ℝ≥0)
    (S B : ℝ → ℝ) (hS : Monotone S) (hB : Antitone B) :
    Monotone (fun q : ℝ≥0 =>
      (S (volume compatible supply demand q) +
        B ((volume compatible supply demand q : ℝ) - q)) / 2) := by
  intro q r hqr
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact add_le_add (hS (volume_monotone compatible supply demand hqr))
    (hB (originalDemand_antitone compatible supply demand hqr))

end Thesis.DayAhead.ImpactVolumeBounds
