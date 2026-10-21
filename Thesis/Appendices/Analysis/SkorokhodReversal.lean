import Thesis.Appendices.Analysis.SkorokhodPartitions

/-! # Time reversal and finite cuts for càglàd paths -/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ} {X : Type*} [MetricSpace X]

def intervalReverse (a b : ℝ) (t : ClosedInterval a b) : ClosedInterval a b :=
  ⟨a + b - t, by constructor <;> linarith [t.property.1, t.property.2]⟩

def intervalReverseOrderIso (a b : ℝ) :
    ClosedInterval a b ≃o OrderDual (ClosedInterval a b) where
  toFun := intervalReverse a b
  invFun t := intervalReverse a b t
  left_inv t := Subtype.ext (by dsimp [intervalReverse]; ring)
  right_inv t := Subtype.ext (by dsimp [intervalReverse]; ring)
  map_rel_iff' := by
    intro s t
    change a + b - (t : ℝ) ≤ a + b - s ↔ (s : ℝ) ≤ t
    constructor <;> intro h <;> linarith

@[simp] theorem intervalReverse_val (t : ClosedInterval a b) :
    (intervalReverse a b t : ℝ) = a + b - t := rfl

@[simp] theorem intervalReverse_reverse (t : ClosedInterval a b) :
    intervalReverse a b (intervalReverse a b t) = t :=
  Subtype.ext (by dsimp [intervalReverse]; ring)

theorem caglad_reverse_isCadlag (f : RegularPath a b X .caglad) :
    IsOneSidedRegularPath .cadlag (fun t => f.val (intervalReverse a b t)) := by
  constructor
  · apply isRightContinuousOnIcc_of_continuousWithinAt
    intro t
    exact (f.property.1.continuousWithinAt (intervalReverse a b t)).comp
      (intervalReverseOrderIso a b).continuous.continuousWithinAt
      (fun _ hx => (intervalReverseOrderIso a b).monotone hx)
  · apply hasLeftLimitsOnIcc_of_tendsto
    intro t
    obtain ⟨L, hL⟩ := f.property.2.tendsto (intervalReverse a b t)
    exact ⟨L, hL.comp
      ((intervalReverseOrderIso a b).continuous.continuousWithinAt.tendsto_nhdsWithin
        (fun _ hx => (intervalReverseOrderIso a b).strictMono hx))⟩

def SameStrictCutCell (S : Finset ℝ) (u v : ℝ) : Prop := ∀ s ∈ S, s < u ↔ s < v

theorem caglad_finite_cuts (hab : a ≤ b) (f : RegularPath a b X .caglad)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, a ∈ S ∧ b ∈ S ∧ (∀ s ∈ S, s ∈ Icc a b) ∧
      ∀ u v : ClosedInterval a b, SameStrictCutCell S u v → dist (f.val u) (f.val v) < ε := by
  classical
  let g : RegularPath a b X .cadlag :=
    ⟨fun t => f.val (intervalReverse a b t), caglad_reverse_isCadlag f⟩
  obtain ⟨S, ha, hb, hS, hosc⟩ := cadlag_finite_cuts hab g hε
  let T := S.image fun s => a + b - s
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨b, hb, by ring⟩
  · exact Finset.mem_image.mpr ⟨a, ha, by ring⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have ht' := hS t ht
    constructor <;> linarith [ht'.1, ht'.2]
  · intro u v hcell
    have hsame : SameCutCell S (intervalReverse a b u) (intervalReverse a b v) := by
      intro s hs
      have h := hcell (a + b - s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
      simp only [intervalReverse_val]
      constructor
      · intro hu
        by_contra hv
        have hv' : a + b - s < (v : ℝ) := by linarith
        have hu' := h.mpr hv'
        linarith
      · intro hv
        by_contra hu
        have hu' : a + b - s < (u : ℝ) := by linarith
        have hv' := h.mp hu'
        linarith
    simpa only [g, intervalReverse_reverse] using
      hosc (intervalReverse a b u) (intervalReverse a b v) hsame

theorem regularPath_small_error_of_fixes_cuts (hab : a ≤ b) {side : PathOrientation}
    (f : RegularPath a b X side) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, a ∈ S ∧ b ∈ S ∧ (∀ s ∈ S, s ∈ Icc a b) ∧
      ∀ e : IncreasingIntervalBijection a b,
        (∀ s : ClosedInterval a b, (s : ℝ) ∈ S → e s = s) →
        supPathEDistance f.val (fun t => f.val (e t)) ≤ ENNReal.ofReal ε := by
  cases side with
  | cadlag =>
      obtain ⟨S, ha, hb, hS, hosc⟩ := cadlag_finite_cuts hab f hε
      refine ⟨S, ha, hb, hS, fun e he => ?_⟩
      rw [supPathEDistance_le_iff]
      intro t
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      apply (hosc t (e t) ?_).le
      intro s hs
      let st : ClosedInterval a b := ⟨s, hS s hs⟩
      have hfix := he st hs
      have hiff := e.strictMono.le_iff_le (a := st) (b := t)
      rw [hfix] at hiff
      exact hiff.symm
  | caglad =>
      obtain ⟨S, ha, hb, hS, hosc⟩ := caglad_finite_cuts hab f hε
      refine ⟨S, ha, hb, hS, fun e he => ?_⟩
      rw [supPathEDistance_le_iff]
      intro t
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      apply (hosc t (e t) ?_).le
      intro s hs
      let st : ClosedInterval a b := ⟨s, hS s hs⟩
      have hfix := he st hs
      have hiff := e.strictMono.lt_iff_lt (a := st) (b := t)
      rw [hfix] at hiff
      exact hiff.symm

end Thesis.Foundations.Preliminary.Analysis
