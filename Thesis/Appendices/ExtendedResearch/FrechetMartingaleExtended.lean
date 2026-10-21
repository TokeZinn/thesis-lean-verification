import Thesis.Appendices.ExtendedResearch.FrechetMartingale

/-! # Fréchet loss with the original, possibly infinite, metric

Finite second moments are measured using the original extended distance;
truncating that distance would change the minimization problem. The loss is
a nonnegative extended integral and is finite for admissible competitors.
-/

namespace Thesis.Foundations.Research

open MeasureTheory
open scoped ENNReal NNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [EMetricSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- Original label: `defn:frechet-martingale`.
Admissibility retains the original extended metric and finite second moment. -/
def ExtendedMetricL2Predictor (μ : Measure Ω) (m : MeasurableSpace Ω)
    (z₀ : E) (Y : Ω → E) : Prop :=
  Measurable[m] Y ∧ (∫⁻ ω, edist (Y ω) z₀ ^ 2 ∂μ) < ∞

/-- Original label: `defn:frechet-martingale`.
The criterion is invariant under almost-sure equality and therefore defines
the same minimization on admissible equivalence classes. -/
def IsExtendedFrechetMartingale (μ : Measure Ω) (ℱ : ℕ → MeasurableSpace Ω)
    (z₀ : E) (Z : ℕ → Ω → E) : Prop :=
  (∀ n, ExtendedMetricL2Predictor μ (ℱ n) z₀ (Z n)) ∧
    ∀ n Y, ExtendedMetricL2Predictor μ (ℱ n) z₀ Y →
      (∫⁻ ω, edist (Z (n + 1) ω) (Z n ω) ^ 2 ∂μ) ≤
        ∫⁻ ω, edist (Z (n + 1) ω) (Y ω) ^ 2 ∂μ

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  by_cases ha : a = ∞
  · simp [ha]
  by_cases hb : b = ∞
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  exact_mod_cast add_sq_le (a := a) (b := b)

omit [MeasurableSpace E] [BorelSpace E] in
theorem edist_sq_le_moments (x y z₀ : E) :
    edist x y ^ 2 ≤ 2 * (edist x z₀ ^ 2 + edist y z₀ ^ 2) := by
  calc
    edist x y ^ 2 ≤ (edist x z₀ + edist z₀ y) ^ 2 :=
      pow_le_pow_left' (edist_triangle x z₀ y) 2
    _ ≤ 2 * (edist x z₀ ^ 2 + edist y z₀ ^ 2) := by
      simpa only [edist_comm z₀ y] using ennreal_add_sq_le (edist x z₀) (edist z₀ y)

omit [MeasurableSpace E] [BorelSpace E] in
theorem extended_squared_loss_ae_congr {μ : Measure Ω} {X X' Y Y' : Ω → E}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    (∫⁻ ω, edist (X ω) (Y ω) ^ 2 ∂μ) = ∫⁻ ω, edist (X' ω) (Y' ω) ^ 2 ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hX, hY] with ω hx hy
  rw [hx, hy]

/-- Finite original-distance second moments imply a finite measurable loss;
the real expectation agrees with this nonnegative integral after `toReal`. -/
theorem extended_squared_loss_integrable [TopologicalSpace.SeparableSpace E]
    (μ : Measure Ω) (X Y : Ω → E) (z₀ : E) (hX : Measurable X) (hY : Measurable Y)
    (hXm : (∫⁻ ω, edist (X ω) z₀ ^ 2 ∂μ) < ∞)
    (hYm : (∫⁻ ω, edist (Y ω) z₀ ^ 2 ∂μ) < ∞) :
    Measurable (fun ω => edist (X ω) (Y ω) ^ 2) ∧
      (∫⁻ ω, edist (X ω) (Y ω) ^ 2 ∂μ) < ∞ ∧
      Integrable (fun ω => (edist (X ω) (Y ω) ^ 2).toReal) μ := by
  have hmX : Measurable (fun ω => edist (X ω) z₀ ^ 2) := by fun_prop
  have hmY : Measurable (fun ω => edist (Y ω) z₀ ^ 2) := by fun_prop
  have hm : Measurable (fun ω => edist (X ω) (Y ω) ^ 2) := by fun_prop
  have hi : (∫⁻ ω, edist (X ω) (Y ω) ^ 2 ∂μ) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono (fun ω => edist_sq_le_moments (X ω) (Y ω) z₀))
    rw [lintegral_const_mul 2 (hmX.add hmY), lintegral_add_left hmX]
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hXm, hYm⟩)
  exact ⟨hm, hi, integrable_toReal_of_lintegral_ne_top hm.aemeasurable hi.ne⟩

/-- The extended nonnegative expectation is the ordinary real expectation
used by the source once finite second moments have been established. -/
theorem extended_squared_loss_expectation [TopologicalSpace.SeparableSpace E]
    (μ : Measure Ω) (X Y : Ω → E) (z₀ : E) (hX : Measurable X) (hY : Measurable Y)
    (hXm : (∫⁻ ω, edist (X ω) z₀ ^ 2 ∂μ) < ∞)
    (hYm : (∫⁻ ω, edist (Y ω) z₀ ^ 2 ∂μ) < ∞) :
    (∫ ω, (edist (X ω) (Y ω) ^ 2).toReal ∂μ) =
      (∫⁻ ω, edist (X ω) (Y ω) ^ 2 ∂μ).toReal := by
  have h := extended_squared_loss_integrable μ X Y z₀ hX hY hXm hYm
  exact integral_toReal h.1.aemeasurable (ae_lt_top h.1 h.2.1.ne)

end Thesis.Foundations.Research
