import Thesis.Appendices.Analysis.AnalysisBasic
import Mathlib.Topology.Order.MonotoneContinuity

/-! # Algebra and distortion of interval time changes

These estimates use the thesis's logarithmic secant-slope distortion.
They are independent of either remaining Skorokhod axiom.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

namespace IncreasingIntervalBijection

variable {a b : ℝ}

@[ext] theorem ext {e d : IncreasingIntervalBijection a b}
    (h : ∀ t, e t = d t) : e = d := by
  cases e
  cases d
  congr
  exact funext h

def toOrderIso (e : IncreasingIntervalBijection a b) :
    ClosedInterval a b ≃o ClosedInterval a b where
  toEquiv := Equiv.ofBijective e e.bijective
  map_rel_iff' := e.strictMono.le_iff_le

def ofOrderIso (e : ClosedInterval a b ≃o ClosedInterval a b) :
    IncreasingIntervalBijection a b := ⟨e, e.strictMono, e.bijective⟩

def refl (a b : ℝ) : IncreasingIntervalBijection a b :=
  ofOrderIso (OrderIso.refl _)

def symm (e : IncreasingIntervalBijection a b) : IncreasingIntervalBijection a b :=
  ofOrderIso e.toOrderIso.symm

def comp (e d : IncreasingIntervalBijection a b) : IncreasingIntervalBijection a b :=
  ofOrderIso (d.toOrderIso.trans e.toOrderIso)

@[simp] theorem refl_apply (t : ClosedInterval a b) : refl a b t = t := rfl

@[simp] theorem comp_apply (e d : IncreasingIntervalBijection a b)
    (t : ClosedInterval a b) : e.comp d t = e (d t) := rfl

@[simp] theorem symm_apply_apply (e : IncreasingIntervalBijection a b)
    (t : ClosedInterval a b) : e.symm (e t) = t := e.toOrderIso.symm_apply_apply t

@[simp] theorem apply_symm_apply (e : IncreasingIntervalBijection a b)
    (t : ClosedInterval a b) : e (e.symm t) = t := e.toOrderIso.apply_symm_apply t

theorem continuous (e : IncreasingIntervalBijection a b) : Continuous e :=
  e.toOrderIso.continuous

@[simp] theorem apply_left (e : IncreasingIntervalBijection a b) (hab : a ≤ b) :
    e ⟨a, le_rfl, hab⟩ = ⟨a, le_rfl, hab⟩ :=
  e.toOrderIso.map_bot' (fun t => t.property.1) (fun t => t.property.1)

@[simp] theorem apply_right (e : IncreasingIntervalBijection a b) (hab : a ≤ b) :
    e ⟨b, hab, le_rfl⟩ = ⟨b, hab, le_rfl⟩ :=
  e.toOrderIso.map_top' (fun t => t.property.2) (fun t => t.property.2)

end IncreasingIntervalBijection

variable {a b : ℝ}

theorem timeChangeSecantSlope_pos (e : IncreasingIntervalBijection a b)
    {s t : ClosedInterval a b} (hst : s < t) : 0 < timeChangeSecantSlope e s t :=
  div_pos (sub_pos.mpr (e.strictMono hst)) (sub_pos.mpr hst)

theorem timeChangeSecantSlope_comp (e d : IncreasingIntervalBijection a b)
    {s t : ClosedInterval a b} (hst : s < t) :
    timeChangeSecantSlope (e.comp d) s t =
      timeChangeSecantSlope e (d s) (d t) * timeChangeSecantSlope d s t := by
  unfold timeChangeSecantSlope
  simp only [IncreasingIntervalBijection.comp_apply]
  field_simp [sub_ne_zero.mpr (ne_of_gt (show (d s : ℝ) < d t from d.strictMono hst))]

theorem timeChangeSecantSlope_symm (e : IncreasingIntervalBijection a b)
    (s t : ClosedInterval a b) :
    timeChangeSecantSlope e.symm (e s) (e t) = (timeChangeSecantSlope e s t)⁻¹ := by
  simp [timeChangeSecantSlope, inv_div]

theorem logSecant_le_timeDistortion (e : IncreasingIntervalBijection a b)
    {s t : ClosedInterval a b} (hst : s < t) :
    ENNReal.ofReal |Real.log (timeChangeSecantSlope e s t)| ≤ timeDistortion e :=
  le_sSup ⟨s, t, hst, rfl⟩

theorem timeDistortion_le_iff (e : IncreasingIntervalBijection a b) (c : ℝ≥0∞) :
    timeDistortion e ≤ c ↔ ∀ s t : ClosedInterval a b, s < t →
      ENNReal.ofReal |Real.log (timeChangeSecantSlope e s t)| ≤ c := by
  constructor
  · exact fun h s t hst => (logSecant_le_timeDistortion e hst).trans h
  · intro h
    apply sSup_le
    rintro _ ⟨s, t, hst, rfl⟩
    exact h s t hst

@[simp] theorem timeDistortion_refl :
    timeDistortion (IncreasingIntervalBijection.refl a b) = 0 := by
  apply le_antisymm _ (zero_le _)
  rw [timeDistortion_le_iff]
  intro s t hst
  simp [timeChangeSecantSlope, sub_ne_zero.mpr (ne_of_gt (show (s : ℝ) < t from hst))]

theorem timeDistortion_comp_le (e d : IncreasingIntervalBijection a b) :
    timeDistortion (e.comp d) ≤ timeDistortion e + timeDistortion d := by
  rw [timeDistortion_le_iff]
  intro s t hst
  rw [timeChangeSecantSlope_comp e d hst,
    Real.log_mul (ne_of_gt (timeChangeSecantSlope_pos e (d.strictMono hst)))
      (ne_of_gt (timeChangeSecantSlope_pos d hst))]
  calc
    ENNReal.ofReal |Real.log (timeChangeSecantSlope e (d s) (d t)) +
        Real.log (timeChangeSecantSlope d s t)| ≤
        ENNReal.ofReal (|Real.log (timeChangeSecantSlope e (d s) (d t))| +
          |Real.log (timeChangeSecantSlope d s t)|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |Real.log (timeChangeSecantSlope e (d s) (d t))| +
        ENNReal.ofReal |Real.log (timeChangeSecantSlope d s t)| :=
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ timeDistortion e + timeDistortion d :=
      add_le_add (logSecant_le_timeDistortion e (d.strictMono hst))
        (logSecant_le_timeDistortion d hst)

@[simp] theorem timeDistortion_symm (e : IncreasingIntervalBijection a b) :
    timeDistortion e.symm = timeDistortion e := by
  have hle (d : IncreasingIntervalBijection a b) : timeDistortion d.symm ≤ timeDistortion d := by
    rw [timeDistortion_le_iff]
    intro s t hst
    obtain ⟨s, rfl⟩ := d.bijective.2 s
    obtain ⟨t, rfl⟩ := d.bijective.2 t
    rw [timeChangeSecantSlope_symm, Real.log_inv, abs_neg]
    exact logSecant_le_timeDistortion d (d.strictMono.lt_iff_lt.mp hst)
  refine le_antisymm (hle e) ?_
  have h := hle e.symm
  have heq : e.symm.symm = e := by
    apply IncreasingIntervalBijection.ext
    intro t
    apply e.symm.bijective.1
    simp
  simpa only [heq] using h

theorem timeChange_increment_le (e : IncreasingIntervalBijection a b)
    {c : ℝ} (hc : 0 ≤ c) (he : timeDistortion e ≤ ENNReal.ofReal c)
    {s t : ClosedInterval a b} (hst : s ≤ t) :
    (e t : ℝ) - e s ≤ Real.exp c * ((t : ℝ) - s) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hlog : |Real.log (timeChangeSecantSlope e s t)| ≤ c :=
    (ENNReal.ofReal_le_ofReal_iff hc).mp ((logSecant_le_timeDistortion e hst).trans he)
  have hslope := (Real.log_le_iff_le_exp (timeChangeSecantSlope_pos e hst)).mp
    ((le_abs_self _).trans hlog)
  exact (div_le_iff₀ (sub_pos.mpr (show (s : ℝ) < t from hst))).mp hslope

theorem timeShiftNorm_le_of_distortion_le (hab : a ≤ b)
    (e : IncreasingIntervalBijection a b) {c : ℝ} (hc : 0 ≤ c)
    (he : timeDistortion e ≤ ENNReal.ofReal c) :
    timeShiftNorm e ≤ ENNReal.ofReal ((Real.exp c - 1) * (b - a)) := by
  apply sSup_le
  rintro _ ⟨t, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  rw [abs_sub_le_iff]
  have hc' : 0 ≤ Real.exp c - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hc)
  have hleft := timeChange_increment_le e hc he
    (s := ⟨a, le_rfl, hab⟩) (t := t) t.property.1
  have hright := timeChange_increment_le e hc he
    (s := t) (t := ⟨b, hab, le_rfl⟩) t.property.2
  have hleftfix : (e.toFun ⟨a, le_rfl, hab⟩ : ℝ) = a :=
    congrArg Subtype.val (e.apply_left hab)
  have hrightfix : (e.toFun ⟨b, hab, le_rfl⟩ : ℝ) = b :=
    congrArg Subtype.val (e.apply_right hab)
  rw [hleftfix] at hleft
  rw [hrightfix] at hright
  constructor
  · have h := mul_le_mul_of_nonneg_left (sub_le_sub_right t.property.2 a) hc'
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (sub_le_sub_left t.property.1 b) hc'
    nlinarith

theorem timeShiftNorm_symm (e : IncreasingIntervalBijection a b) :
    timeShiftNorm e.symm = timeShiftNorm e := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨t, rfl⟩
    have h : ENNReal.ofReal |(e (e.symm t) : ℝ) - e.symm t| ≤ timeShiftNorm e :=
      le_sSup (mem_range_self _)
    simpa only [IncreasingIntervalBijection.apply_symm_apply, abs_sub_comm] using h
  · apply sSup_le
    rintro _ ⟨t, rfl⟩
    have h : ENNReal.ofReal |(e.symm (e t) : ℝ) - e t| ≤ timeShiftNorm e.symm :=
      le_sSup (mem_range_self _)
    simpa only [IncreasingIntervalBijection.symm_apply_apply, abs_sub_comm] using h

theorem timeDistortion_eq_zero_iff (hab : a ≤ b) (e : IncreasingIntervalBijection a b) :
    timeDistortion e = 0 ↔ e = IncreasingIntervalBijection.refl a b := by
  refine ⟨fun he => ?_, fun he => he ▸ timeDistortion_refl⟩
  have hshift := timeShiftNorm_le_of_distortion_le hab e (c := 0) le_rfl (by simp [he])
  simp only [Real.exp_zero, sub_self, zero_mul, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hshift
  apply IncreasingIntervalBijection.ext
  intro t
  apply Subtype.ext
  have h : ENNReal.ofReal |(e t : ℝ) - t| ≤ timeShiftNorm e := le_sSup (mem_range_self _)
  rw [hshift, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem timeShiftNorm_tendsto_zero {ι : Type*} {l : Filter ι} (hab : a ≤ b)
    (e : ι → IncreasingIntervalBijection a b)
    (he : Tendsto (fun i => timeDistortion (e i)) l (𝓝 0)) :
    Tendsto (fun i => timeShiftNorm (e i)) l (𝓝 0) := by
  have hc : Tendsto (fun i => (timeDistortion (e i)).toReal) l (𝓝 0) :=
    ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp he
  have hbound : Tendsto (fun i => ENNReal.ofReal
      ((Real.exp (timeDistortion (e i)).toReal - 1) * (b - a))) l (𝓝 0) := by
    convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuous_exp.continuousAt.tendsto.comp hc).sub_const 1 |>.mul_const (b - a)) using 1
    simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Filter.Eventually.of_forall fun _ => zero_le _)
  filter_upwards [he.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ∞ from ENNReal.zero_lt_top))]
    with i hi
  apply timeShiftNorm_le_of_distortion_le hab (e i) ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal hi.ne]

end Thesis.Foundations.Preliminary.Analysis
