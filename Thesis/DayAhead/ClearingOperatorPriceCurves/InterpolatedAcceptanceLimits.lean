import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedAcceptanceFormula
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Lattice

/-! # Arithmetic one-sided limits of actual interpolated acceptance

The source constructs excess-supply vertices from one-sided accepted volumes.
These limits are obtained directly from the same finite cell formulas: at a
cell's starting price the left endpoint is excluded, while the right limit
keeps the accepted endpoint. Finite maxima commute with these limits.
-/
noncomputable section
namespace Thesis.DayAhead.InterpolatedAcceptanceLimits

open Set Filter MeasureTheory InterpolatedSide InterpolatedOffered ExcessSupply
open InterpolatedAcceptanceFormula
open scoped Topology

def cellLeftEndpoint (l r a b level : ℝ) : ℝ :=
  if l < r ∧ a < level then
    if b ≤ level then r else interpolate a b l r level
  else 0

theorem interpolate_at_right {a b l r : ℝ} (hab : a < b) :
    interpolate a b l r b = r := by
  unfold interpolate
  field_simp [sub_ne_zero.mpr hab.ne']
  ring

/-- The exact left-sided cell endpoint, including flat-price and empty cells. -/
theorem cellEndpoint_tendsto_left {l r a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    Tendsto (cellEndpoint l r a b) (𝓝[<] x) (𝓝 (cellLeftEndpoint l r a b x)) := by
  by_cases hw : l < r
  · by_cases hxa : x ≤ a
    · rw [cellLeftEndpoint, if_neg (fun h => not_lt_of_ge hxa h.2)]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hva : v < a := (show v < x from hv).trans_le hxa
      exact (if_neg (show ¬(l < r ∧ a ≤ v) from fun h => not_le_of_gt hva h.2)).symm
    · have hax : a < x := lt_of_not_ge hxa
      by_cases hbx : b < x
      · rw [cellLeftEndpoint, if_pos ⟨hw, hax⟩, if_pos hbx.le]
        apply tendsto_const_nhds.congr'
        filter_upwards [(nhdsWithin_le_nhds : 𝓝[<] x ≤ 𝓝 x) (Ioi_mem_nhds hbx)] with v hv
        have hbv : b < v := hv
        simp only [cellEndpoint,
          if_pos (show l < r ∧ a ≤ v from ⟨hw, hab.trans hbv.le⟩), if_pos hbv.le]
      · have hxb : x ≤ b := le_of_not_gt hbx
        have hab' : a < b := hax.trans_le hxb
        have hvalue : cellLeftEndpoint l r a b x = interpolate a b l r x := by
          rw [cellLeftEndpoint, if_pos ⟨hw, hax⟩]
          split_ifs with hbx'
          · have hxeq : x = b := le_antisymm hxb hbx'
            rw [hxeq, interpolate_at_right hab']
          · rfl
        rw [hvalue]
        have hc : Continuous (interpolate a b l r) := by unfold interpolate; fun_prop
        apply (hc.tendsto x |>.mono_left nhdsWithin_le_nhds).congr'
        filter_upwards [self_mem_nhdsWithin,
          (nhdsWithin_le_nhds : 𝓝[<] x ≤ 𝓝 x) (Ioi_mem_nhds hax)] with v hv hval
        have hav : a < v := hval
        have hvb : v < b := (show v < x from hv).trans_le hxb
        simp only [cellEndpoint,
          if_pos (show l < r ∧ a ≤ v from ⟨hw, hav.le⟩), if_neg (not_le_of_gt hvb)]
  · have heq : cellEndpoint l r a b = fun _ => (0 : ℝ) := by
      funext v
      simp [cellEndpoint, hw]
    simp only [heq, cellLeftEndpoint, hw, false_and, ↓reduceIte]
    exact tendsto_const_nhds

/-- The actual cell endpoint is right-continuous as a function of price. -/
theorem cellEndpoint_tendsto_right {l r a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    Tendsto (cellEndpoint l r a b) (𝓝[>] x) (𝓝 (cellEndpoint l r a b x)) := by
  by_cases hw : l < r
  · by_cases hxa : x < a
    · rw [cellEndpoint, if_neg (fun h => not_le_of_gt hxa h.2)]
      apply tendsto_const_nhds.congr'
      filter_upwards [(nhdsWithin_le_nhds : 𝓝[>] x ≤ 𝓝 x) (Iio_mem_nhds hxa)] with v hv
      have hva : v < a := hv
      exact (if_neg (show ¬(l < r ∧ a ≤ v) from fun h => not_le_of_gt hva h.2)).symm
    · have hax : a ≤ x := le_of_not_gt hxa
      by_cases hbx : b ≤ x
      · rw [cellEndpoint, if_pos ⟨hw, hax⟩, if_pos hbx]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with v hv
        have hbv : b < v := hbx.trans_lt (show x < v from hv)
        simp only [cellEndpoint,
          if_pos (show l < r ∧ a ≤ v from ⟨hw, hab.trans hbv.le⟩), if_pos hbv.le]
      · have hxb : x < b := lt_of_not_ge hbx
        rw [cellEndpoint, if_pos ⟨hw, hax⟩, if_neg hbx]
        have hc : Continuous (interpolate a b l r) := by unfold interpolate; fun_prop
        apply (hc.tendsto x |>.mono_left nhdsWithin_le_nhds).congr'
        filter_upwards [self_mem_nhdsWithin,
          (nhdsWithin_le_nhds : 𝓝[>] x ≤ 𝓝 x) (Iio_mem_nhds hxb)] with v hv hvb
        have hav : a < v := hax.trans_lt (show x < v from hv)
        have hvb' : v < b := hvb
        simp only [cellEndpoint,
          if_pos (show l < r ∧ a ≤ v from ⟨hw, hav.le⟩), if_neg (not_le_of_gt hvb')]
  · have heq : cellEndpoint l r a b = fun _ => (0 : ℝ) := by
      funext v
      simp [cellEndpoint, hw]
    simp only [heq]
    exact tendsto_const_nhds

def finiteAcceptedLeft {n : ℕ} (p Q : Fin (n + 1) → ℝ) (level : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1))).sup' (by simp)
    (Fin.cases 0 (fun j =>
      cellLeftEndpoint (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) level))

/-- Actual accepted volume tends from the left to the finite arithmetic
left-vertex formula. This is the one-sided data used by the source path. -/
theorem offered_tendsto_left {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (level : ℝ) :
    Tendsto (offered (Q (Fin.last n)) (curve p Q)) (𝓝[<] level)
      (𝓝 (finiteAcceptedLeft p Q level)) := by
  have heq : offered (Q (Fin.last n)) (curve p Q) = finiteAccepted p Q :=
    funext (offered_eq_finiteAccepted p Q hp hQ hz)
  rw [heq]
  apply Tendsto.finset_sup'_nhds_apply
  intro i _
  refine Fin.cases tendsto_const_nhds (fun j => ?_) i
  exact cellEndpoint_tendsto_left (hp (Fin.castSucc_le_succ j)) level

theorem offered_leftLim_eq {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (level : ℝ) :
    (offered (Q (Fin.last n)) (curve p Q)).leftLim level = finiteAcceptedLeft p Q level := by
  exact leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (offered_tendsto_left p Q hp hQ hz level)

theorem offered_tendsto_right {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (level : ℝ) :
    Tendsto (offered (Q (Fin.last n)) (curve p Q)) (𝓝[>] level)
      (𝓝 (finiteAccepted p Q level)) := by
  have heq : offered (Q (Fin.last n)) (curve p Q) = finiteAccepted p Q :=
    funext (offered_eq_finiteAccepted p Q hp hQ hz)
  rw [heq]
  apply Tendsto.finset_sup'_nhds_apply
  intro i _
  refine Fin.cases tendsto_const_nhds (fun j => ?_) i
  exact cellEndpoint_tendsto_right (hp (Fin.castSucc_le_succ j)) level

theorem offered_rightLim_eq {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (level : ℝ) :
    (offered (Q (Fin.last n)) (curve p Q)).rightLim level = finiteAccepted p Q level := by
  exact rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (offered_tendsto_right p Q hp hQ hz level)

/-- All arithmetic operations in a fixed cell are Borel, including its zero
and full acceptance branches. -/
theorem measurable_cellLeftEndpoint :
    Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) =>
      cellLeftEndpoint x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold cellLeftEndpoint interpolate
  have hin : Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) =>
      if x.2.2.2.1 ≤ x.2.2.2.2 then x.2.1 else
        ((x.2.2.2.1-x.2.2.2.2)*x.1+(x.2.2.2.2-x.2.2.1)*x.2.1) /
          (x.2.2.2.1-x.2.2.1)) :=
    (show Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) => x.2.1) by fun_prop).ite
      (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
  have hcond : MeasurableSet {x : (ℝ × ℝ × ℝ × ℝ × ℝ) |
      x.1 < x.2.1 ∧ x.2.2.1 < x.2.2.2.2} :=
    (measurableSet_lt (show Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) => x.1) by fun_prop)
      (by fun_prop)).inter (measurableSet_lt
        (show Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) => x.2.2.1) by fun_prop)
        (by fun_prop))
  exact hin.ite hcond measurable_const

/-- Borel finite maximum assembly of the actual local acceptance formulas. -/
theorem measurable_finiteAcceptedLeft {n : ℕ} :
    Measurable (fun x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ =>
      finiteAcceptedLeft x.1 x.2.1 x.2.2) := by
  let f : Fin (n + 1) → ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ) → ℝ :=
    fun i x => Fin.cases (0 : ℝ) (fun j : Fin n =>
      cellLeftEndpoint (x.2.1 j.castSucc) (x.2.1 j.succ)
        (x.1 j.castSucc) (x.1 j.succ) x.2.2) i
  have hsup : Measurable ((Finset.univ : Finset (Fin (n + 1))).sup' (by simp) f) := by
    apply Finset.measurable_sup'
    intro i _
    refine Fin.cases measurable_const (fun j => ?_) i
    change Measurable (fun x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ =>
      cellLeftEndpoint (x.2.1 j.castSucc) (x.2.1 j.succ)
        (x.1 j.castSucc) (x.1 j.succ) x.2.2)
    have hdata : Measurable (fun x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ =>
      (x.2.1 j.castSucc, x.2.1 j.succ, x.1 j.castSucc, x.1 j.succ, x.2.2)) := by
      fun_prop
    exact measurable_cellLeftEndpoint.comp hdata
  convert hsup using 1
  funext x
  exact (Finset.sup'_apply _ f x).symm


/-- Joint Borel dependence of the actual one-sided accepted volume. -/
theorem measurable_actual_offered_leftLim
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (p Q : Ω → Fin (n + 1) → ℝ) (level : Ω → ℝ)
    (hp : Measurable p) (hQ : Measurable Q) (hlevel : Measurable level)
    (hpm : ∀ ω, Monotone (p ω)) (hQm : ∀ ω, Monotone (Q ω))
    (hzero : ∀ ω, Q ω 0 = 0) :
    Measurable (fun ω =>
      (offered (Q ω (Fin.last n)) (curve (p ω) (Q ω))).leftLim (level ω)) := by
  have hdata := hp.prodMk (hQ.prodMk hlevel)
  convert measurable_finiteAcceptedLeft.comp hdata using 1
  funext ω
  exact offered_leftLim_eq (p ω) (Q ω) (hpm ω) (hQm ω) (hzero ω) (level ω)

/-- Joint Borel dependence of the actual right-sided accepted volume. -/
theorem measurable_actual_offered_rightLim
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (p Q : Ω → Fin (n + 1) → ℝ) (level : Ω → ℝ)
    (hp : Measurable p) (hQ : Measurable Q) (hlevel : Measurable level)
    (hpm : ∀ ω, Monotone (p ω)) (hQm : ∀ ω, Monotone (Q ω))
    (hzero : ∀ ω, Q ω 0 = 0) :
    Measurable (fun ω =>
      (offered (Q ω (Fin.last n)) (curve (p ω) (Q ω))).rightLim (level ω)) := by
  have hdata := hp.prodMk (hQ.prodMk hlevel)
  convert measurable_finiteAccepted.comp hdata using 1
  funext ω
  exact offered_rightLim_eq (p ω) (Q ω) (hpm ω) (hQm ω) (hzero ω) (level ω)

end Thesis.DayAhead.InterpolatedAcceptanceLimits
