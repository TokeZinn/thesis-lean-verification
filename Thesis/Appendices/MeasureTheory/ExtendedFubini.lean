import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.EReal.Inv

/-! # Tonelli--Fubini for extended-real inputs

The manuscript permits values in `[-∞,∞]`. Signed integration below is the
difference of the nonnegative positive- and negative-part integrals. Finiteness
of the absolute integral proves that the function is real-valued almost
everywhere; thus passage to the Bochner integral does not discard infinite
values on a set of positive measure.
-/

namespace Thesis.Foundations.Preliminary.ExtendedFubini

open MeasureTheory Filter
open scoped ENNReal

universe u v

variable {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]

noncomputable def extendedIntegral (μ : Measure S) (f : S → EReal) : EReal :=
  ((∫⁻ s, (f s).toENNReal ∂μ) : EReal) -
    ((∫⁻ s, (-f s).toENNReal ∂μ) : EReal)

theorem measurable_abs : Measurable EReal.abs := by
  apply EReal.measurable_of_measurable_real
  simpa only [EReal.abs_def] using
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable : Measurable (fun r : ℝ ↦ |r|))

theorem toENNReal_le_abs (x : EReal) : x.toENNReal ≤ x.abs := by
  induction x <;> simp [EReal.abs_def, le_abs_self]

theorem enorm_toReal_le_abs (x : EReal) : ‖x.toReal‖ₑ ≤ x.abs := by
  induction x <;> simp [EReal.abs_def, ← ofReal_norm, Real.norm_eq_abs]

theorem ae_coe_toReal_of_lintegral_abs_lt_top
    (μ : Measure S) {f : S → EReal} (hf : Measurable f)
    (hfinite : ∫⁻ s, (f s).abs ∂μ < ∞) :
    (fun s ↦ ((f s).toReal : EReal)) =ᵐ[μ] f := by
  filter_upwards [ae_lt_top (measurable_abs.comp hf) hfinite.ne] with s hs
  exact EReal.coe_toReal (by intro h; simp [h] at hs) (by intro h; simp [h] at hs)

theorem integrable_toReal_of_lintegral_abs_lt_top
    (μ : Measure S) {f : S → EReal} (hf : Measurable f)
    (hfinite : ∫⁻ s, (f s).abs ∂μ < ∞) :
    Integrable (fun s ↦ (f s).toReal) μ := by
  refine ⟨hf.ereal_toReal.aestronglyMeasurable, ?_⟩
  change (∫⁻ s, ‖(f s).toReal‖ₑ ∂μ) < ∞
  exact (lintegral_mono fun s ↦ enorm_toReal_le_abs (f s)).trans_lt hfinite

theorem extendedIntegral_congr_ae (μ : Measure S) {f g : S → EReal}
    (hfg : f =ᵐ[μ] g) : extendedIntegral μ f = extendedIntegral μ g := by
  unfold extendedIntegral
  have hp : (fun s ↦ (f s).toENNReal) =ᵐ[μ] (fun s ↦ (g s).toENNReal) :=
    hfg.fun_comp EReal.toENNReal
  have hn : (fun s ↦ (-f s).toENNReal) =ᵐ[μ] (fun s ↦ (-g s).toENNReal) :=
    hfg.fun_comp fun x ↦ (-x).toENNReal
  rw [lintegral_congr_ae hp, lintegral_congr_ae hn]

theorem extendedIntegral_coe (μ : Measure S) {f : S → ℝ} (hf : Integrable f μ) :
    extendedIntegral μ (fun s ↦ (f s : EReal)) = (∫ s, f s ∂μ : ℝ) := by
  have hp : (∫⁻ s, ENNReal.ofReal (f s) ∂μ) < ∞ :=
    (lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.2
  have hn : (∫⁻ s, ENNReal.ofReal (-f s) ∂μ) < ∞ :=
    (lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.neg.2
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, EReal.coe_sub,
    EReal.coe_ennreal_toReal hp.ne, EReal.coe_ennreal_toReal hn.ne]
  simp only [extendedIntegral, ← EReal.coe_neg, EReal.real_coe_toENNReal]

theorem extendedIntegral_eq_integral_toReal
    (μ : Measure S) {f : S → EReal} (hf : Measurable f)
    (hfinite : ∫⁻ s, (f s).abs ∂μ < ∞) :
    extendedIntegral μ f = ((∫ s, (f s).toReal ∂μ : ℝ) : EReal) := by
  rw [← extendedIntegral_congr_ae μ
    (ae_coe_toReal_of_lintegral_abs_lt_top μ hf hfinite)]
  exact extendedIntegral_coe μ (integrable_toReal_of_lintegral_abs_lt_top μ hf hfinite)

theorem extendedIntegral_of_nonneg (μ : Measure S) {f : S → EReal}
    (hf : ∀ s, 0 ≤ f s) :
    extendedIntegral μ f = ((∫⁻ s, (f s).toENNReal ∂μ) : EReal) := by
  have hn : (fun s ↦ (-f s).toENNReal) = fun _ ↦ (0 : ℝ≥0∞) := by
    funext s
    exact EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr (hf s))
  simp only [extendedIntegral, hn, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

/-- Original label: `thm:tonelli-fubini`.
Tonelli's nonnegative clause for extended-real inputs, with measurable partial
integrals and both orders of integration, including infinite integrals. -/
theorem tonelli_extendedReal
    (μ : Measure S) (ν : Measure T) [SigmaFinite μ] [SigmaFinite ν]
    (f : S × T → EReal) (hf : Measurable f) (hnonneg : ∀ z, 0 ≤ f z) :
    Measurable (fun s ↦ extendedIntegral ν (fun t ↦ f (s, t))) ∧
    Measurable (fun t ↦ extendedIntegral μ (fun s ↦ f (s, t))) ∧
    extendedIntegral (μ.prod ν) f =
      extendedIntegral μ (fun s ↦ extendedIntegral ν (fun t ↦ f (s, t))) ∧
    extendedIntegral (μ.prod ν) f =
      extendedIntegral ν (fun t ↦ extendedIntegral μ (fun s ↦ f (s, t))) := by
  have hr : (fun s ↦ extendedIntegral ν (fun t ↦ f (s, t))) =
      fun s ↦ ((∫⁻ t, (f (s, t)).toENNReal ∂ν) : EReal) := by
    funext s
    exact extendedIntegral_of_nonneg ν (fun t ↦ hnonneg (s, t))
  have hl : (fun t ↦ extendedIntegral μ (fun s ↦ f (s, t))) =
      fun t ↦ ((∫⁻ s, (f (s, t)).toENNReal ∂μ) : EReal) := by
    funext t
    exact extendedIntegral_of_nonneg μ (fun s ↦ hnonneg (s, t))
  rw [hr, hl]
  refine ⟨hf.ereal_toENNReal.lintegral_prod_right'.coe_ereal_ennreal,
    hf.ereal_toENNReal.lintegral_prod_left'.coe_ereal_ennreal, ?_, ?_⟩
  · rw [extendedIntegral_of_nonneg (μ.prod ν) hnonneg,
      extendedIntegral_of_nonneg μ (fun _ ↦ EReal.coe_ennreal_nonneg _)]
    simp only [EReal.toENNReal_coe]
    exact congrArg (fun x : ℝ≥0∞ ↦ (x : EReal))
      (lintegral_prod _ hf.ereal_toENNReal.aemeasurable)
  · rw [extendedIntegral_of_nonneg (μ.prod ν) hnonneg,
      extendedIntegral_of_nonneg ν (fun _ ↦ EReal.coe_ennreal_nonneg _)]
    simp only [EReal.toENNReal_coe]
    exact congrArg (fun x : ℝ≥0∞ ↦ (x : EReal))
      (lintegral_prod_symm _ hf.ereal_toENNReal.aemeasurable)

/-- Original label: `thm:tonelli-fubini`.
The signed clause in the full extended-real scope of the thesis. The absolute
integrability assumption yields almost-everywhere integrable sections and
justifies both iterated signed integrals. -/
theorem fubini_extendedReal
    (μ : Measure S) (ν : Measure T) [SigmaFinite μ] [SigmaFinite ν]
    (f : S × T → EReal) (hf : Measurable f)
    (hfinite : ∫⁻ z, (f z).abs ∂μ.prod ν < ∞) :
    (∀ᵐ s ∂μ, Measurable (fun t ↦ f (s, t)) ∧ ∫⁻ t, (f (s, t)).abs ∂ν < ∞) ∧
    (∀ᵐ t ∂ν, Measurable (fun s ↦ f (s, t)) ∧ ∫⁻ s, (f (s, t)).abs ∂μ < ∞) ∧
    extendedIntegral (μ.prod ν) f =
      extendedIntegral μ (fun s ↦ extendedIntegral ν (fun t ↦ f (s, t))) ∧
    extendedIntegral (μ.prod ν) f =
      extendedIntegral ν (fun t ↦ extendedIntegral μ (fun s ↦ f (s, t))) := by
  have habs := measurable_abs.comp hf
  have hrfin : ∀ᵐ s ∂μ, ∫⁻ t, (f (s, t)).abs ∂ν < ∞ := by
    apply ae_lt_top habs.lintegral_prod_right'
    rw [← lintegral_prod _ habs.aemeasurable]
    exact hfinite.ne
  have hlfin : ∀ᵐ t ∂ν, ∫⁻ s, (f (s, t)).abs ∂μ < ∞ := by
    apply ae_lt_top habs.lintegral_prod_left'
    rw [← lintegral_prod_symm _ habs.aemeasurable]
    exact hfinite.ne
  have hmeasr (s : S) : Measurable (fun t ↦ f (s, t)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hmeasl (t : T) : Measurable (fun s ↦ f (s, t)) :=
    hf.comp (measurable_id.prodMk measurable_const)
  have hfint := integrable_toReal_of_lintegral_abs_lt_top (μ.prod ν) hf hfinite
  have hr : (fun s ↦ extendedIntegral ν (fun t ↦ f (s, t))) =ᵐ[μ]
      fun s ↦ ((∫ t, (f (s, t)).toReal ∂ν : ℝ) : EReal) := by
    filter_upwards [hrfin] with s hs
    exact extendedIntegral_eq_integral_toReal ν (hmeasr s) hs
  have hl : (fun t ↦ extendedIntegral μ (fun s ↦ f (s, t))) =ᵐ[ν]
      fun t ↦ ((∫ s, (f (s, t)).toReal ∂μ : ℝ) : EReal) := by
    filter_upwards [hlfin] with t ht
    exact extendedIntegral_eq_integral_toReal μ (hmeasl t) ht
  refine ⟨hrfin.mono (fun s hs ↦ ⟨hmeasr s, hs⟩),
    hlfin.mono (fun t ht ↦ ⟨hmeasl t, ht⟩), ?_, ?_⟩
  · rw [extendedIntegral_eq_integral_toReal (μ.prod ν) hf hfinite,
      extendedIntegral_congr_ae μ hr,
      extendedIntegral_coe μ hfint.integral_prod_left]
    exact congrArg (fun x : ℝ ↦ (x : EReal)) (integral_prod _ hfint)
  · rw [extendedIntegral_eq_integral_toReal (μ.prod ν) hf hfinite,
      extendedIntegral_congr_ae ν hl,
      extendedIntegral_coe ν hfint.integral_prod_right]
    exact congrArg (fun x : ℝ ↦ (x : EReal)) (integral_prod_symm _ hfint)

/-- Original label: `thm:tonelli-fubini`.
The signed partial integrals are explicitly zeroed on the measurable null sets
of non-integrable sections. These versions are measurable and integrable;
both of their ordinary integrals equal the full signed extended integral. -/
theorem fubini_zeroed_partial_versions
    (μ : Measure S) (ν : Measure T) [SigmaFinite μ] [SigmaFinite ν]
    (f : S × T → EReal) (hf : Measurable f)
    (hfinite : ∫⁻ z, (f z).abs ∂μ.prod ν < ∞) :
    ∃ g : S → ℝ, ∃ h : T → ℝ,
      Measurable g ∧ Measurable h ∧ Integrable g μ ∧ Integrable h ν ∧
      (∀ s, g s = if (∫⁻ t, (f (s, t)).abs ∂ν) < ∞ then
        ∫ t, (f (s, t)).toReal ∂ν else 0) ∧
      (∀ t, h t = if (∫⁻ s, (f (s, t)).abs ∂μ) < ∞ then
        ∫ s, (f (s, t)).toReal ∂μ else 0) ∧
      ((fun s => (g s : EReal)) =ᵐ[μ]
        fun s => extendedIntegral ν (fun t => f (s, t))) ∧
      ((fun t => (h t : EReal)) =ᵐ[ν]
        fun t => extendedIntegral μ (fun s => f (s, t))) ∧
      extendedIntegral (μ.prod ν) f = (∫ s, g s ∂μ : ℝ) ∧
      extendedIntegral (μ.prod ν) f = (∫ t, h t ∂ν : ℝ) := by
  classical
  let g : S → ℝ := fun s => if (∫⁻ t, (f (s, t)).abs ∂ν) < ∞ then
    ∫ t, (f (s, t)).toReal ∂ν else 0
  let h : T → ℝ := fun t => if (∫⁻ s, (f (s, t)).abs ∂μ) < ∞ then
    ∫ s, (f (s, t)).toReal ∂μ else 0
  have hparts := fubini_extendedReal μ ν f hf hfinite
  have hg : g =ᵐ[μ] fun s => ∫ t, (f (s, t)).toReal ∂ν := by
    filter_upwards [hparts.1] with s hs
    simp [g, hs.2]
  have hh : h =ᵐ[ν] fun t => ∫ s, (f (s, t)).toReal ∂μ := by
    filter_upwards [hparts.2.1] with t ht
    simp [h, ht.2]
  have habs := measurable_abs.comp hf
  have hgmeas : Measurable g := Measurable.ite
    (measurableSet_lt habs.lintegral_prod_right' measurable_const)
    hf.ereal_toReal.stronglyMeasurable.integral_prod_right'.measurable measurable_const
  have hhmeas : Measurable h := Measurable.ite
    (measurableSet_lt habs.lintegral_prod_left' measurable_const)
    hf.ereal_toReal.stronglyMeasurable.integral_prod_left'.measurable measurable_const
  have hfint := integrable_toReal_of_lintegral_abs_lt_top (μ.prod ν) hf hfinite
  refine ⟨g, h, hgmeas, hhmeas, hfint.integral_prod_left.congr hg.symm,
    hfint.integral_prod_right.congr hh.symm, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hg, hparts.1] with s hs hint
    rw [hs]
    exact (extendedIntegral_eq_integral_toReal ν hint.1 hint.2).symm
  · filter_upwards [hh, hparts.2.1] with t ht hint
    rw [ht]
    exact (extendedIntegral_eq_integral_toReal μ hint.1 hint.2).symm
  · rw [extendedIntegral_eq_integral_toReal (μ.prod ν) hf hfinite,
      integral_congr_ae hg]
    exact congrArg (fun r : ℝ => (r : EReal)) (integral_prod _ hfint)
  · rw [extendedIntegral_eq_integral_toReal (μ.prod ν) hf hfinite,
      integral_congr_ae hh]
    exact congrArg (fun r : ℝ => (r : EReal)) (integral_prod_symm _ hfint)

end Thesis.Foundations.Preliminary.ExtendedFubini
