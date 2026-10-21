import Thesis.DayAhead.ClearingOperatorPriceCurves.ImpactClearing
import Thesis.DayAhead.ClearingOperatorPriceCurves.ImpactMarginals

/-! # Monotonicity of the actual positive-volume market-impact branches -/

noncomputable section
namespace Thesis.DayAhead.ImpactMonotonicity

open Foundations.MarketRepresentation TuplesBasic
open Foundations.MarketClearing.Sorting Foundations.MarketClearing.Equilibrium
open Foundations.MarketClearing.MidpointPrice
open MarketImpact ImpactBooks ImpactClearing ImpactVolumeBounds ImpactMarginals

/-- The full raw-book midpoint comparison for nonnegative perturbations.
The initial perturbed state must have positive matched volume; the source's
identification of the zero-quantity perturbation with the original state is
a separate endpoint obligation. -/
theorem impactPrice_nonneg_add (upper : ℝ) (hupper : 0 ≤ upper)
    (m : MarketTuple) (hm : priceBounded upper m) (q δ : Quantity)
    (hv : 0 < positiveVolume upper m q) :
    impactPrice upper (m, (q : ℝ)) ≤ impactPrice upper (m, ((q + δ : Quantity) : ℝ)) := by
  let m₀ := adjoinExtreme upper (m, (q : ℝ))
  let m₁ := adjoinExtreme upper (m, ((q + δ : Quantity) : ℝ))
  have hv₀ : 0 < marketEquilibriumQuantity m₀ := hv
  have hvol := positiveVolume_add_bounds upper m q δ
  have hv₁ : 0 < marketEquilibriumQuantity m₁ := hv₀.trans_le hvol.1
  obtain ⟨i, j, hsi, hbi, _, _, _, _, _⟩ := marketMidpointPrice_positive_formula m₀ hv₀
  obtain ⟨i', j', hsj, hbj, _, _, _, _, _⟩ := marketMidpointPrice_positive_formula m₁ hv₁
  have hps : sortedSellPriceTuple m₀ = sortedSellPriceTuple m₁ := by
    simp only [m₀, m₁, sortedSellPriceTuple,
      sellPriceTuple_adjoin_nonneg _ _ q.coe_nonneg,
      sellPriceTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg]
  have hpb : sortedBuyPriceTuple m₁ = sortedBuyPriceTuple m₀ := by
    simp only [m₀, m₁, sortedBuyPriceTuple,
      buyPriceTuple_adjoin_nonneg _ _ q.coe_nonneg,
      buyPriceTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg]
  have hqs : cumulativeSellQuantityTuple m₀ = cumulativeSellQuantityTuple m₁ := by
    simp only [m₀, m₁, cumulativeSellQuantityTuple, sortedSellQuantityTuple,
      sellQuantityTuple_adjoin_nonneg _ _ q.coe_nonneg,
      sellQuantityTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg,
      sellPriceTuple_adjoin_nonneg _ _ q.coe_nonneg,
      sellPriceTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg]
  have hs : marginalPrice ((cumulativeSellQuantityTuple m₀, sortedSellPriceTuple m₀),
      marketEquilibriumQuantity m₀) ≤
      marginalPrice ((cumulativeSellQuantityTuple m₁, sortedSellPriceTuple m₁),
        marketEquilibriumQuantity m₁) := by
    apply marginalPrice_mono hsi hsj hqs hps hvol.1 (cumulativeSell_length_eq_price_length m₀)
    intro a b hab hb
    exact tuplePriceEval_mono_of_isSorted
      (realMinimalPermutationLE_sorts (sellPriceTuple m₀)) hab hb
  obtain ⟨n, a, p, t, ha₀, ha₁, hp₀, hpt⟩ := positive_sorted_buy_increase upper m q δ
  change sortedBuyQuantityTuple m₀ = ⟨n, a⟩ at ha₀
  change sortedBuyQuantityTuple m₁ = _ at ha₁
  change sortedBuyPriceTuple m₀ = ⟨n, p⟩ at hp₀
  have hp₁ : sortedBuyPriceTuple m₁ = ⟨n, p⟩ := hpb.trans hp₀
  have hsort : Antitone p := by
    have h : IsSorted (dualizeRealTuple (sortedBuyPriceTuple m₀)) := by
      rw [dualize_sortedBuyPrice]
      exact realMinimalPermutationGE_sorts_dual _
    rw [hp₀] at h
    exact (isSorted_iff_monotone _).mp h
  have hmax : ∀ k, p k ≤ p t := by
    intro k
    rw [hpt]
    have hb := (sortedPrice_all (fun p => p ≤ upper) m₀
      (adjoinExtreme_all (fun p => p ≤ upper) upper (m, (q : ℝ))
        (by linarith) le_rfl (fun i => (hm i).2))).2
    rw [hp₀] at hb
    exact hb k
  have hb : marginalPrice ((cumulativeBuyQuantityTuple m₀, sortedBuyPriceTuple m₀),
      marketEquilibriumQuantity m₀) ≤
      marginalPrice ((cumulativeBuyQuantityTuple m₁, sortedBuyPriceTuple m₁),
        marketEquilibriumQuantity m₁) := by
    rw [cumulativeBuyQuantityTuple, ha₀, hp₀] at hbi ⊢
    rw [cumulativeBuyQuantityTuple, ha₁, hp₁] at hbj ⊢
    exact buy_marginal_addAt ⟨n, a⟩ p hsort t hmax δ _ _ hbi hbj hvol.2
  change marketMidpointPrice m₀ ≤ marketMidpointPrice m₁
  exact div_le_div_of_nonneg_right (add_le_add hs hb) (by norm_num)

theorem impactPrice_nonneg_mono (upper : ℝ) (hupper : 0 ≤ upper)
    (m : MarketTuple) (hm : priceBounded upper m) {q r : Quantity} (hqr : q ≤ r)
    (hv : 0 < positiveVolume upper m q) :
    impactPrice upper (m, (q : ℝ)) ≤ impactPrice upper (m, (r : ℝ)) := by
  have h := impactPrice_nonneg_add upper hupper m hm q (r - q) hv
  rwa [add_tsub_cancel_of_le hqr] at h

theorem impactPrice_neg_add (upper : ℝ) (hupper : 0 ≤ upper)
    (m : MarketTuple) (hm : priceBounded upper m) (q δ : Quantity) (hq : 0 < q)
    (hv : 0 < negativeVolume upper m q) :
    impactPrice upper (m, -((q + δ : Quantity) : ℝ)) ≤ impactPrice upper (m, -(q : ℝ)) := by
  have hq' : -(q : ℝ) < 0 := neg_neg_of_pos hq
  have hqd : -((q + δ : Quantity) : ℝ) < 0 := neg_neg_of_pos (lt_of_lt_of_le hq
    (le_add_of_nonneg_right δ.coe_nonneg))
  let m₀ := adjoinExtreme upper (m, -(q : ℝ))
  let m₁ := adjoinExtreme upper (m, -((q + δ : Quantity) : ℝ))
  have hv₀ : 0 < marketEquilibriumQuantity m₀ := hv
  have hvol := negativeVolume_add_bounds upper m q δ hq
  have hv₁ : 0 < marketEquilibriumQuantity m₁ := hv₀.trans_le hvol.1
  obtain ⟨i, j, hsi, hbi, _, _, _, _, _⟩ := marketMidpointPrice_positive_formula m₀ hv₀
  obtain ⟨i', j', hsj, hbj, _, _, _, _, _⟩ := marketMidpointPrice_positive_formula m₁ hv₁
  have hps : sortedSellPriceTuple m₁ = sortedSellPriceTuple m₀ := by
    simp only [m₀, m₁, sortedSellPriceTuple, sellPriceTuple_adjoin_neg _ _ hq',
      sellPriceTuple_adjoin_neg _ _ hqd]
  have hpb : sortedBuyPriceTuple m₀ = sortedBuyPriceTuple m₁ := by
    simp only [m₀, m₁, sortedBuyPriceTuple, buyPriceTuple_adjoin_neg _ _ hq',
      buyPriceTuple_adjoin_neg _ _ hqd]
  have hqb : cumulativeBuyQuantityTuple m₀ = cumulativeBuyQuantityTuple m₁ := by
    simp only [m₀, m₁, cumulativeBuyQuantityTuple, sortedBuyQuantityTuple,
      buyQuantityTuple_adjoin_neg _ _ hq', buyQuantityTuple_adjoin_neg _ _ hqd,
      buyPriceTuple_adjoin_neg _ _ hq', buyPriceTuple_adjoin_neg _ _ hqd]
  have hb : marginalPrice ((cumulativeBuyQuantityTuple m₁, sortedBuyPriceTuple m₁),
      marketEquilibriumQuantity m₁) ≤
      marginalPrice ((cumulativeBuyQuantityTuple m₀, sortedBuyPriceTuple m₀),
        marketEquilibriumQuantity m₀) := by
    apply marginalPrice_antitone hbi hbj hqb hpb hvol.1 (cumulativeBuy_length_eq_price_length m₀)
    intro a b hab hblt
    have halt := lt_of_le_of_lt hab hblt
    have h : IsSorted (dualizeRealTuple (sortedBuyPriceTuple m₀)) := by
      rw [dualize_sortedBuyPrice]
      exact realMinimalPermutationGE_sorts_dual _
    simp only [tuplePriceEval, dif_pos halt, dif_pos hblt]
    exact (isSorted_iff_monotone _).mp h ⟨a, halt⟩ ⟨b, hblt⟩ hab
  obtain ⟨n, a, p, t, ha₀, ha₁, hp₀, hpt⟩ := negative_sorted_sell_increase upper m q δ hq
  change sortedSellQuantityTuple m₀ = ⟨n, a⟩ at ha₀
  change sortedSellQuantityTuple m₁ = _ at ha₁
  change sortedSellPriceTuple m₀ = ⟨n, p⟩ at hp₀
  have hp₁ : sortedSellPriceTuple m₁ = ⟨n, p⟩ := hps.trans hp₀
  have hsort : Monotone p := by
    have h := realMinimalPermutationLE_sorts (sellPriceTuple m₀)
    change IsSorted (sortedSellPriceTuple m₀) at h
    rw [hp₀] at h
    exact (isSorted_iff_monotone _).mp h
  have hmin : ∀ k, p t ≤ p k := by
    intro k
    rw [hpt]
    have hs := (sortedPrice_all (fun p => -500 ≤ p) m₀
      (adjoinExtreme_all (fun p => -500 ≤ p) upper (m, -(q : ℝ))
        le_rfl (by linarith) (fun i => (hm i).1))).1
    rw [hp₀] at hs
    exact hs k
  have hs : marginalPrice ((cumulativeSellQuantityTuple m₁, sortedSellPriceTuple m₁),
      marketEquilibriumQuantity m₁) ≤
      marginalPrice ((cumulativeSellQuantityTuple m₀, sortedSellPriceTuple m₀),
        marketEquilibriumQuantity m₀) := by
    dsimp only [cumulativeSellQuantityTuple] at hsi hsj ⊢
    rw [ha₀, hp₀] at hsi ⊢
    rw [ha₁, hp₁] at hsj ⊢
    exact sell_marginal_addAt ⟨n, a⟩ p hsort t hmin δ _ _ hsi hsj hvol.2
  change marketMidpointPrice m₁ ≤ marketMidpointPrice m₀
  exact div_le_div_of_nonneg_right (add_le_add hs hb) (by norm_num)

theorem impactPrice_neg_mono (upper : ℝ) (hupper : 0 ≤ upper)
    (m : MarketTuple) (hm : priceBounded upper m) {q r : Quantity} (hq : 0 < q) (hqr : q ≤ r)
    (hv : 0 < negativeVolume upper m q) :
    impactPrice upper (m, -(r : ℝ)) ≤ impactPrice upper (m, -(q : ℝ)) := by
  have h := impactPrice_neg_add upper hupper m hm q (r - q) hq hv
  rwa [add_tsub_cancel_of_le hqr] at h

end Thesis.DayAhead.ImpactMonotonicity
