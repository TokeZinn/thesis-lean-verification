import Thesis.DayAhead.ClearingOperatorPriceCurves.ImpactThresholds

/-! # Joining the actual impact-price branches at zero -/

noncomputable section
namespace Thesis.DayAhead.ImpactJoin

open Foundations.MarketRepresentation
open Foundations.MarketClearing.Sorting Foundations.MarketClearing.Equilibrium
open Foundations.MarketClearing.MidpointPrice
open MarketImpact ImpactBaseline ImpactThresholds

theorem impactPrice_zero (upper : ℝ) (m : MarketTuple) (hm : m ∈ positiveStates) :
    impactPrice upper (m, 0) = marketMidpointPrice m := by
  let m₀ := adjoinExtreme upper (m, 0)
  have hm₀ : m₀ ∈ positiveStates := perturbation_positive upper m hm 0
  have hvol : marketEquilibriumQuantity m₀ = marketEquilibriumQuantity m :=
    market_volume_zero_perturbation upper m
  have hsc (r : ℝ) : sellCut m₀ r = sellCut m r :=
    sellCut_adjoin_nonneg upper m (le_refl 0) r
  have hbc (r : ℝ) : buyCut m₀ r = buyCut m r := by
    have h := buyCut_adjoin_nonneg upper m 0 r
    simpa only [NNReal.coe_zero, ite_self, zero_add] using h
  have hsiff (r : ℝ) : sellMarginal m₀ ≤ r ↔ sellMarginal m ≤ r := by
    rw [sellMarginal_le_iff m₀ hm₀, sellMarginal_le_iff m hm, hvol, hsc]
  have hbiff (r : ℝ) : r ≤ buyMarginal m₀ ↔ r ≤ buyMarginal m := by
    rw [le_buyMarginal_iff m₀ hm₀, le_buyMarginal_iff m hm, hvol, hbc]
  have hs : sellMarginal m₀ = sellMarginal m := le_antisymm
    ((hsiff _).mpr le_rfl) ((hsiff _).mp le_rfl)
  have hb : buyMarginal m₀ = buyMarginal m := le_antisymm
    ((hbiff _).mp le_rfl) ((hbiff _).mpr le_rfl)
  change (sellMarginal m₀ + buyMarginal m₀) / 2 = (sellMarginal m + buyMarginal m) / 2
  rw [hs, hb]

theorem negative_price_le_baseline (upper : ℝ) (m : MarketTuple)
    (hm : m ∈ positiveStates) (hp : priceBounded upper m) (q : Quantity) (hq : 0 < q) :
    impactPrice upper (m, -(q : ℝ)) ≤ marketMidpointPrice m := by
  let m₁ := adjoinExtreme upper (m, -(q : ℝ))
  have hm₁ : m₁ ∈ positiveStates := perturbation_positive upper m hm _
  have hq' : -(q : ℝ) < 0 := neg_neg_of_pos hq
  have hb : buyMarginal m₁ ≤ buyMarginal m := by
    apply (le_buyMarginal_iff m hm _).mpr
    have h := (le_buyMarginal_iff m₁ hm₁ (buyMarginal m₁)).mp le_rfl
    change marketEquilibriumQuantity m₁ ≤ buyCut (adjoinExtreme upper (m, -(q : ℝ))) _ at h
    rw [buyCut_adjoin_neg upper m hq'] at h
    exact (market_volume_le_perturbed upper m _).trans h
  have hs : sellMarginal m₁ ≤ sellMarginal m := by
    apply (sellMarginal_le_iff m₁ hm₁ _).mpr
    have hcut : sellCut m₁ (sellMarginal m) = q + sellCut m (sellMarginal m) := by
      change sellCut (adjoinExtreme upper (m, -(q : ℝ))) (sellMarginal m) = _
      rw [sellCut_adjoin_neg upper m q hq,
        if_pos (sellMarginal_mem_bounds upper m hm hp).1]
    rw [hcut, add_comm q]
    exact (negative_volume_le_baseline_add upper m q hq).trans
      (add_le_add ((sellMarginal_le_iff m hm _).mp le_rfl) le_rfl)
  change (sellMarginal m₁ + buyMarginal m₁) / 2 ≤ (sellMarginal m + buyMarginal m) / 2
  exact div_le_div_of_nonneg_right (add_le_add hs hb) (by norm_num)

/-- The entire actual impact map is monotone, hence so is its restriction to
the source's available-depth interval. All price ties and zero orders are retained. -/
theorem impactPrice_monotone (upper : ℝ) (hupper : 0 ≤ upper)
    (m : MarketTuple) (hm : m ∈ positiveStates) (hp : priceBounded upper m) :
    Monotone (fun q : ℝ => impactPrice upper (m, q)) := by
  intro q r hqr
  by_cases hq : 0 ≤ q
  · exact impactPrice_nonneg_mono_of_positive_state upper hupper m hp hm hq hqr
  · have hq' : q < 0 := lt_of_not_ge hq
    by_cases hr : r < 0
    · exact impactPrice_neg_mono_of_positive_state upper hupper m hp hm hqr hr
    · have hr' : 0 ≤ r := le_of_not_gt hr
      have hpos : (0 : Quantity) < ⟨-q, neg_nonneg.mpr hq'.le⟩ :=
        show (0 : ℝ) < -q from neg_pos.mpr hq'
      have hleft := negative_price_le_baseline upper m hm hp ⟨-q, neg_nonneg.mpr hq'.le⟩ hpos
      change impactPrice upper (m, -(-q)) ≤ marketMidpointPrice m at hleft
      rw [neg_neg, ← impactPrice_zero upper m hm] at hleft
      exact hleft.trans (impactPrice_nonneg_mono_of_positive_state upper hupper m hp hm
        (le_refl 0) hr')

end Thesis.DayAhead.ImpactJoin
