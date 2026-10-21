import Thesis.DayAhead.ClearingOperatorPriceCurves.ImpactBooks
import Thesis.Foundations.MarketClearing.QuantityPerturbation

/-! # Volume bounds for the actual perturbed order book

These results apply to the thesis's actual separation, minimal-price sorting,
cumulative quantities and finite compatible maximum. They prove the volume
increment argument without replacing the order book by an assumed curve.
-/

noncomputable section
namespace Thesis.DayAhead.ImpactClearing

open Foundations.MarketRepresentation
open Foundations.MarketClearing.Sorting Foundations.MarketClearing.Equilibrium
open Foundations.MarketClearing.QuantityPerturbation
open MarketImpact ImpactBooks

def positiveVolume (upper : ℝ) (m : MarketTuple) (q : Quantity) : Quantity :=
  marketEquilibriumQuantity (adjoinExtreme upper (m, (q : ℝ)))

theorem positiveVolume_add_bounds (upper : ℝ) (m : MarketTuple) (q δ : Quantity) :
    positiveVolume upper m q ≤ positiveVolume upper m (q + δ) ∧
      positiveVolume upper m (q + δ) ≤ positiveVolume upper m q + δ := by
  let m₀ := adjoinExtreme upper (m, (q : ℝ))
  let m₁ := adjoinExtreme upper (m, ((q + δ : Quantity) : ℝ))
  have hps : sortedSellPriceTuple m₁ = sortedSellPriceTuple m₀ := by
    simp only [m₀, m₁, sortedSellPriceTuple, sellPriceTuple_adjoin_nonneg _ _
      (show 0 ≤ ((q + δ : Quantity) : ℝ) from (q + δ).coe_nonneg),
      sellPriceTuple_adjoin_nonneg _ _ q.coe_nonneg]
  have hpb : sortedBuyPriceTuple m₁ = sortedBuyPriceTuple m₀ := by
    simp only [m₀, m₁, sortedBuyPriceTuple, buyPriceTuple_adjoin_nonneg _ _
      (show 0 ≤ ((q + δ : Quantity) : ℝ) from (q + δ).coe_nonneg),
      buyPriceTuple_adjoin_nonneg _ _ q.coe_nonneg]
  have hqs : sortedSellQuantityTuple m₁ = sortedSellQuantityTuple m₀ := by
    simp only [m₀, m₁, sortedSellQuantityTuple,
      sellQuantityTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg,
      sellQuantityTuple_adjoin_nonneg _ _ q.coe_nonneg,
      sellPriceTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg,
      sellPriceTuple_adjoin_nonneg _ _ q.coe_nonneg]
  have hqb : IncreasesWithin (sortedBuyQuantityTuple m₀) (sortedBuyQuantityTuple m₁) δ := by
    dsimp only [m₀, m₁, sortedBuyQuantityTuple]
    rw [buyQuantityTuple_adjoin_nonneg _ _ q.coe_nonneg,
      buyQuantityTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg,
      buyPriceTuple_adjoin_nonneg _ _ q.coe_nonneg,
      buyPriceTuple_adjoin_nonneg _ _ (q + δ).coe_nonneg]
    exact (increasesWithin_prepend (buyQuantityTuple m) q δ).permutationMap _
  change marketEquilibriumQuantity m₀ ≤ marketEquilibriumQuantity m₁ ∧
    marketEquilibriumQuantity m₁ ≤ marketEquilibriumQuantity m₀ + δ
  unfold marketEquilibriumQuantity equilibriumQuantity
  rw [hps, hpb]
  apply maxCleared_bounds
  · intro k
    simp only [cumulativeSellQuantityTuple, hqs]
    exact ⟨le_rfl, le_add_of_nonneg_right δ.coe_nonneg⟩
  · exact hqb.cumulative_bounds

theorem positiveVolume_monotone (upper : ℝ) (m : MarketTuple) :
    Monotone (positiveVolume upper m) := by
  intro q r hqr
  have h := (positiveVolume_add_bounds upper m q (r - q)).1
  rwa [add_tsub_cancel_of_le hqr] at h

theorem positiveVolume_increment (upper : ℝ) (m : MarketTuple) {q r : Quantity} (hqr : q ≤ r) :
    0 ≤ (positiveVolume upper m r : ℝ) - positiveVolume upper m q ∧
      (positiveVolume upper m r : ℝ) - positiveVolume upper m q ≤ (r : ℝ) - q := by
  have hm := positiveVolume_monotone upper m hqr
  have hu := (positiveVolume_add_bounds upper m q (r - q)).2
  rw [add_tsub_cancel_of_le hqr] at hu
  have hc : ((r - q : Quantity) : ℝ) = (r : ℝ) - q := NNReal.coe_sub hqr
  constructor
  · exact sub_nonneg.mpr hm
  · change (positiveVolume upper m r : ℝ) ≤
      (positiveVolume upper m q : ℝ) + ((r - q : Quantity) : ℝ) at hu
    rw [hc] at hu
    linarith

theorem positive_originalDemand_antitone (upper : ℝ) (m : MarketTuple) :
    Antitone (fun q : Quantity => (positiveVolume upper m q : ℝ) - q) := by
  intro q r hqr
  have h := (positiveVolume_increment upper m hqr).2
  linarith

def negativeVolume (upper : ℝ) (m : MarketTuple) (a : Quantity) : Quantity :=
  marketEquilibriumQuantity (adjoinExtreme upper (m, -(a : ℝ)))

/-- The source uses the sell branch strictly below zero. The zero endpoint is
kept separate because its specified order is a zero-volume buy order. -/
theorem negativeVolume_add_bounds (upper : ℝ) (m : MarketTuple) (a δ : Quantity) (ha : 0 < a) :
    negativeVolume upper m a ≤ negativeVolume upper m (a + δ) ∧
      negativeVolume upper m (a + δ) ≤ negativeVolume upper m a + δ := by
  have ha' : -(a : ℝ) < 0 := neg_neg_of_pos ha
  have had : -((a + δ : Quantity) : ℝ) < 0 := neg_neg_of_pos (lt_of_lt_of_le ha
    (le_add_of_nonneg_right δ.coe_nonneg))
  let m₀ := adjoinExtreme upper (m, -(a : ℝ))
  let m₁ := adjoinExtreme upper (m, -((a + δ : Quantity) : ℝ))
  have hps : sortedSellPriceTuple m₁ = sortedSellPriceTuple m₀ := by
    simp only [m₀, m₁, sortedSellPriceTuple, sellPriceTuple_adjoin_neg _ _ had,
      sellPriceTuple_adjoin_neg _ _ ha']
  have hpb : sortedBuyPriceTuple m₁ = sortedBuyPriceTuple m₀ := by
    simp only [m₀, m₁, sortedBuyPriceTuple, buyPriceTuple_adjoin_neg _ _ had,
      buyPriceTuple_adjoin_neg _ _ ha']
  have hqb : sortedBuyQuantityTuple m₁ = sortedBuyQuantityTuple m₀ := by
    simp only [m₀, m₁, sortedBuyQuantityTuple, buyQuantityTuple_adjoin_neg _ _ had,
      buyQuantityTuple_adjoin_neg _ _ ha', buyPriceTuple_adjoin_neg _ _ had,
      buyPriceTuple_adjoin_neg _ _ ha']
  have hqs : IncreasesWithin (sortedSellQuantityTuple m₀) (sortedSellQuantityTuple m₁) δ := by
    dsimp only [m₀, m₁, sortedSellQuantityTuple]
    rw [sellQuantityTuple_adjoin_neg _ _ ha', sellQuantityTuple_adjoin_neg _ _ had,
      sellPriceTuple_adjoin_neg _ _ ha', sellPriceTuple_adjoin_neg _ _ had]
    simp only [neg_neg]
    exact (increasesWithin_prepend (sellQuantityTuple m) a δ).permutationMap _
  change marketEquilibriumQuantity m₀ ≤ marketEquilibriumQuantity m₁ ∧
    marketEquilibriumQuantity m₁ ≤ marketEquilibriumQuantity m₀ + δ
  unfold marketEquilibriumQuantity equilibriumQuantity
  rw [hps, hpb]
  apply maxCleared_bounds
  · exact hqs.cumulative_bounds
  · intro k
    simp only [cumulativeBuyQuantityTuple, hqb]
    exact ⟨le_rfl, le_add_of_nonneg_right δ.coe_nonneg⟩

theorem negativeVolume_increment (upper : ℝ) (m : MarketTuple) {a b : Quantity}
    (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ (negativeVolume upper m b : ℝ) - negativeVolume upper m a ∧
      (negativeVolume upper m b : ℝ) - negativeVolume upper m a ≤ (b : ℝ) - a := by
  have h := negativeVolume_add_bounds upper m a (b - a) ha
  rw [add_tsub_cancel_of_le hab] at h
  have hc : ((b - a : Quantity) : ℝ) = (b : ℝ) - a := NNReal.coe_sub hab
  constructor
  · exact sub_nonneg.mpr h.1
  · have hu := h.2
    change (negativeVolume upper m b : ℝ) ≤
      (negativeVolume upper m a : ℝ) + ((b - a : Quantity) : ℝ) at hu
    rw [hc] at hu
    linarith

theorem negative_originalSupply_antitone (upper : ℝ) (m : MarketTuple) {a b : Quantity}
    (ha : 0 < a) (hab : a ≤ b) :
    (negativeVolume upper m b : ℝ) - b ≤ (negativeVolume upper m a : ℝ) - a := by
  have h := (negativeVolume_increment upper m ha hab).2
  linarith

end Thesis.DayAhead.ImpactClearing
