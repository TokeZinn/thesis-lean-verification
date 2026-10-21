import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialPriceCurve
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! # Deterministic sampling of the selected one-sided price

The essential representative can be recovered as a pointwise limit of
evaluations at explicit interior points. This gives a measurable construction
when the original price and the endpoints depend measurably on a state.
-/

noncomputable section
namespace Thesis.DayAhead.PriceCurves

open Set Filter Topology

def essentialSample (a b q : ℝ) (n : ℕ) : ℝ :=
  if q < b then q + (b - q) / (n + 1) else q - (q - a) / (n + 1)

theorem sample_fraction_bounds (n : ℕ) :
    0 < (1 : ℝ) / (n + 1) ∧ (1 : ℝ) / (n + 1) ≤ 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr (by linarith)

theorem essentialSample_mem {a b q : ℝ} (hq : q ∈ Icc a b) (n : ℕ) :
    essentialSample a b q n ∈ Icc a b := by
  have hf := sample_fraction_bounds n
  unfold essentialSample
  split_ifs <;> rw [div_eq_mul_one_div] <;> constructor <;> nlinarith [hq.1, hq.2]

def PriceCurve.sample (f : PriceCurve) (q : Icc f.leftEndpoint f.rightEndpoint)
    (n : ℕ) : Icc f.leftEndpoint f.rightEndpoint :=
  ⟨essentialSample f.leftEndpoint f.rightEndpoint q n, essentialSample_mem q.property n⟩

theorem tendsto_essentialSample {a b q : ℝ} :
    Tendsto (essentialSample a b q) atTop (𝓝 q) := by
  change Tendsto (fun n => essentialSample a b q n) atTop (𝓝 q)
  by_cases hq : q < b
  · simpa [essentialSample, hq, div_eq_mul_inv] using
      (tendsto_const_nhds (x := q)).add
        ((tendsto_const_nhds (x := b - q)).mul
          tendsto_one_div_add_atTop_nhds_zero_nat)
  · simpa [essentialSample, hq, div_eq_mul_inv] using
      (tendsto_const_nhds (x := q)).sub
        ((tendsto_const_nhds (x := q - a)).mul
          tendsto_one_div_add_atTop_nhds_zero_nat)

theorem PriceCurve.tendsto_sample_price (f : PriceCurve)
    (q : Icc f.leftEndpoint f.rightEndpoint) :
    Tendsto (fun n => f.price (f.sample q n)) atTop (𝓝 (f.essentialPrice q)) := by
  have ht : Tendsto (f.sample q) atTop (𝓝 q) :=
    tendsto_subtype_rng.mpr tendsto_essentialSample
  by_cases hq : (q : ℝ) < f.rightEndpoint
  · rw [PriceCurve.essentialPrice, if_pos hq]
    apply (f.price_monotone.tendsto_rightLim q).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht, Eventually.of_forall fun n => ?_⟩
    change (q : ℝ) < essentialSample f.leftEndpoint f.rightEndpoint q n
    simp only [essentialSample, if_pos hq]
    have hp : 0 < (f.rightEndpoint - q) / (n + 1) := div_pos (sub_pos.mpr hq) (by positivity)
    linarith
  · have hqr : (q : ℝ) = f.rightEndpoint := le_antisymm q.property.2 (not_lt.mp hq)
    by_cases ha : f.leftEndpoint < (q : ℝ)
    · rw [PriceCurve.essentialPrice, if_neg hq]
      apply (f.price_monotone.tendsto_leftLim q).comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨ht, Eventually.of_forall fun n => ?_⟩
      change essentialSample f.leftEndpoint f.rightEndpoint q n < (q : ℝ)
      simp only [essentialSample, if_neg hq]
      have hp : 0 < ((q : ℝ) - f.leftEndpoint) / (n + 1) :=
        div_pos (sub_pos.mpr ha) (by positivity)
      linarith
    · have hla : f.leftEndpoint = (q : ℝ) := le_antisymm q.property.1 (not_lt.mp ha)
      have hs (n : ℕ) : f.sample q n = q := by
        apply Subtype.ext
        simp [PriceCurve.sample, essentialSample, hq, hla]
      simpa only [hs, f.essentialPrice_of_singleton (hla.trans hqr)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => f.price q) atTop (𝓝 (f.price q)))

end Thesis.DayAhead.PriceCurves
