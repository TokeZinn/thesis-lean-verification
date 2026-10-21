import Thesis.Appendices.Analysis.SkorokhodReversal
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue

/-! # Interpolating finitely many time-change values with small distortion

Small displacement on a finite set gives a small Lipschitz constant for the
displacement data. A real Lipschitz extension then produces an increasing
interval bijection whose secant slopes are uniformly close to one.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal NNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ}

theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ S, 0 < w i) : ∃ r > 0, ∀ i ∈ S, r ≤ w i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i S hi ih =>
      obtain ⟨r, hr, hS⟩ := ih (fun j hj => hw j (Finset.mem_insert_of_mem hj))
      refine ⟨min r (w i), lt_min hr (hw i (Finset.mem_insert_self _ _)), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hS j hj)

theorem finite_real_separation (S : Finset ℝ) :
    ∃ r > 0, ∀ s ∈ S, ∀ t ∈ S, s ≠ t → r ≤ |s - t| := by
  classical
  let P := (S ×ˢ S).filter fun p => p.1 ≠ p.2
  obtain ⟨r, hr, hP⟩ := finite_positive_lower_bound P (fun p => |p.1 - p.2|)
    (fun p hp => abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2))
  refine ⟨r, hr, fun s hs t ht hst => hP (s, t) ?_⟩
  simp only [P, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hs, ht⟩, hst⟩

theorem exists_timeChange_of_lipschitz_perturbation (hab : a ≤ b) {K : ℝ≥0}
    (g : ℝ → ℝ) (hg : LipschitzWith K g) (hK : (K : ℝ) < 1)
    (ha : g a = 0) (hb : g b = 0) :
    ∃ e : IncreasingIntervalBijection a b, ∀ t : ClosedInterval a b, (e t : ℝ) = t + g t := by
  let raw : ℝ → ℝ := fun t => t + g t
  have hraw : StrictMono raw := by
    intro s t hst
    have h := hg.dist_le_mul t s
    rw [Real.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr hst)] at h
    have hlo := (abs_le.mp h).1
    have hpos := mul_pos (sub_pos.mpr hK) (sub_pos.mpr hst)
    dsimp [raw]
    nlinarith
  have hrawa : raw a = a := by simp [raw, ha]
  have hrawb : raw b = b := by simp [raw, hb]
  have hcont : Continuous raw := continuous_id.add hg.continuous
  let e : ClosedInterval a b → ClosedInterval a b := fun t =>
    ⟨raw t, by constructor
               · simpa only [hrawa] using hraw.monotone t.property.1
               · simpa only [hrawb] using hraw.monotone t.property.2⟩
  have hmono : StrictMono e := fun s t hst => hraw hst
  have hsurj : Function.Surjective e := by
    intro y
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc hab hcont.continuousOn
      (show (y : ℝ) ∈ Icc (raw a) (raw b) by simpa only [hrawa, hrawb] using y.property)
    exact ⟨⟨t, ht⟩, Subtype.ext hty⟩
  exact ⟨⟨e, hmono, hmono.injective, hsurj⟩, fun _ => rfl⟩

theorem finite_timeChange_interpolation_data (hab : a ≤ b) (S : Finset ℝ)
    (ha : a ∈ S) (hb : b ∈ S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ v : ℝ → ℝ, v a = a → v b = b →
      (∀ s ∈ S, |v s - s| ≤ η) →
      ∃ d : IncreasingIntervalBijection a b, timeDistortion d ≤ ENNReal.ofReal ε ∧
        ∀ t : ClosedInterval a b, (t : ℝ) ∈ S → (d t : ℝ) = v t := by
  classical
  have hlo : 0 < 1 - Real.exp (-ε) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (by linarith))
  have hhi : 0 < Real.exp ε - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hε)
  let k : ℝ := min (1 - Real.exp (-ε)) (Real.exp ε - 1) / 2
  have hk : 0 < k := div_pos (lt_min hlo hhi) (by norm_num)
  have hklo : k ≤ 1 - Real.exp (-ε) := by
    have h := min_le_left (1 - Real.exp (-ε)) (Real.exp ε - 1)
    dsimp [k]
    linarith
  have hkhi : k ≤ Real.exp ε - 1 := by
    have h := min_le_right (1 - Real.exp (-ε)) (Real.exp ε - 1)
    dsimp [k]
    linarith
  have hkone : k < 1 := by linarith [Real.exp_pos (-ε)]
  let K : ℝ≥0 := ⟨k, hk.le⟩
  obtain ⟨r, hr, hsep⟩ := finite_real_separation S
  refine ⟨k * r / 2, by positivity, fun v hva hvb hsmall => ?_⟩
  let displacement : ℝ → ℝ := fun t => v t - t
  have hlip : LipschitzOnWith K displacement (S : Set ℝ) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro s hs t ht
    by_cases hst : s = t
    · simp [hst]
    rw [Real.dist_eq, Real.dist_eq]
    have h := abs_sub (displacement s) (displacement t)
    have hmul := mul_le_mul_of_nonneg_left (hsep s hs t ht hst) hk.le
    change |displacement s - displacement t| ≤ k * |s - t|
    linarith [hsmall s hs, hsmall t ht]
  obtain ⟨g, hg, hmatch⟩ := hlip.extend_real
  have hga : g a = 0 := by
    rw [← hmatch ha]
    simp only [displacement, hva, sub_self]
  have hgb : g b = 0 := by
    rw [← hmatch hb]
    simp only [displacement, hvb, sub_self]
  obtain ⟨d, hd⟩ := exists_timeChange_of_lipschitz_perturbation hab g hg hkone hga hgb
  refine ⟨d, ?_, ?_⟩
  · rw [timeDistortion_le_iff]
    intro s t hst
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]
    have hden : 0 < (t : ℝ) - s := sub_pos.mpr hst
    have h := hg.dist_le_mul (t : ℝ) (s : ℝ)
    rw [Real.dist_eq, Real.dist_eq, abs_of_pos hden] at h
    change |g t - g s| ≤ k * ((t : ℝ) - s) at h
    obtain ⟨hglow, hgupp⟩ := abs_le.mp h
    constructor
    · apply (Real.le_log_iff_exp_le (timeChangeSecantSlope_pos d hst)).mpr
      rw [timeChangeSecantSlope, le_div_iff₀ hden, hd t, hd s]
      have hmul := mul_le_mul_of_nonneg_right hklo hden.le
      nlinarith
    · apply (Real.log_le_iff_le_exp (timeChangeSecantSlope_pos d hst)).mpr
      rw [timeChangeSecantSlope, div_le_iff₀ hden, hd t, hd s]
      have hmul := mul_le_mul_of_nonneg_right hkhi hden.le
      nlinarith
  · intro t ht
    rw [hd t, ← hmatch ht]
    dsimp only [displacement]
    ring

theorem finite_timeChange_interpolation (hab : a ≤ b) (S : Finset ℝ)
    (ha : a ∈ S) (hb : b ∈ S) (hS : ∀ s ∈ S, s ∈ Icc a b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ e : IncreasingIntervalBijection a b,
      timeShiftNorm e ≤ ENNReal.ofReal η →
      ∃ d : IncreasingIntervalBijection a b, timeDistortion d ≤ ENNReal.ofReal ε ∧
        ∀ t : ClosedInterval a b, (t : ℝ) ∈ S → d t = e t := by
  classical
  obtain ⟨η, hη, hinterp⟩ := finite_timeChange_interpolation_data hab S ha hb hε
  refine ⟨η, hη, fun e he => ?_⟩
  let v : ℝ → ℝ := fun t => if ht : t ∈ Icc a b then (e ⟨t, ht⟩ : ℝ) else t
  have hva : v a = a := by
    dsimp only [v]
    rw [dif_pos ⟨le_rfl, hab⟩]
    exact congrArg Subtype.val (e.apply_left hab)
  have hvb : v b = b := by
    dsimp only [v]
    rw [dif_pos ⟨hab, le_rfl⟩]
    exact congrArg Subtype.val (e.apply_right hab)
  have hsmall (s : ℝ) (hs : s ∈ S) : |v s - s| ≤ η := by
    dsimp only [v]
    rw [dif_pos (hS s hs)]
    apply (ENNReal.ofReal_le_ofReal_iff hη.le).mp
    exact (le_sSup (mem_range_self (⟨s, hS s hs⟩ : ClosedInterval a b))).trans he
  obtain ⟨d, hd, hmatch⟩ := hinterp v hva hvb hsmall
  refine ⟨d, hd, fun t ht => Subtype.ext ?_⟩
  simpa only [v, dif_pos t.property] using hmatch t ht

end Thesis.Foundations.Preliminary.Analysis
