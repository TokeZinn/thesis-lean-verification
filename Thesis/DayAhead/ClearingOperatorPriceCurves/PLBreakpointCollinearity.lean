import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalEncoding

/-! # Intrinsic affine breakpoints at positive-width joins

The finite comparison-cell argument in `prop:pl-encoding-measurable` removes
an interior vertex precisely when its two adjacent positive-width segments
are collinear. The selected value at the join is included explicitly, so an
isolated exceptional value cannot silently be discarded by this pointwise
local-affinity argument.
-/

noncomputable section
namespace Thesis.DayAhead.PLBreakpointCollinearity

open Set Filter Topology PiecewiseAffinePriceCurves PLCanonicalEncoding

theorem slope_eq_iff_collinear {a b c p₀ p₁ p₂ : ℝ} (hab : a < b) (hbc : b < c) :
    (p₁ - p₀) / (b - a) = (p₂ - p₁) / (c - b) ↔
      (b - a) * (p₂ - p₁) = (p₁ - p₀) * (c - b) := by
  rw [div_eq_div_iff (sub_pos.mpr hab).ne' (sub_pos.mpr hbc).ne']
  constructor <;> intro h <;> nlinarith

/-- The actual intrinsic `AffineNear` predicate, not merely a formal
comparison flag, is equivalent to the source cross-product equality. -/
theorem affineNear_iff_collinear (f : Curve) {a b c p₀ p₁ p₂ : ℝ}
    (hab : a < b) (hbc : b < c) (hb : f.price b = p₁)
    (hl : ∀ x ∈ Ioo a b, f.price x = p₁ + ((p₁ - p₀) / (b - a)) * (x - b))
    (hr : ∀ x ∈ Ioo b c, f.price x = p₁ + ((p₂ - p₁) / (c - b)) * (x - b)) :
    AffineNear f b ↔ (b - a) * (p₂ - p₁) = (p₁ - p₀) * (c - b) := by
  let L := (p₁ - p₀) / (b - a)
  let R := (p₂ - p₁) / (c - b)
  rw [← slope_eq_iff_collinear hab hbc]
  change AffineNear f b ↔ L = R
  constructor
  · rintro ⟨A, B, hlocal⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
    let δ := min (ε / 2) (min ((b - a) / 2) ((c - b) / 2))
    have hδ : 0 < δ := lt_min (by positivity)
      (lt_min (by linarith) (by linarith))
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδa : δ ≤ (b - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδc : δ ≤ (c - b) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hbl : f.price (b - δ) = A * (b - δ) + B := hball (by
      simpa only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hδ] using hδε)
    have hbr : f.price (b + δ) = A * (b + δ) + B := hball (by
      simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ] using hδε)
    have hb₀ : f.price b = A * b + B := hball (by simpa using hε)
    rw [hb] at hb₀
    have hpl := hl (b - δ) ⟨by linarith, by linarith⟩
    have hpr := hr (b + δ) ⟨by linarith, by linarith⟩
    change f.price (b - δ) = p₁ + L * ((b - δ) - b) at hpl
    change f.price (b + δ) = p₁ + R * ((b + δ) - b) at hpr
    have hAL : A * δ = L * δ := by nlinarith
    have hAR : A * δ = R * δ := by nlinarith
    exact (mul_right_cancel₀ hδ.ne' hAL).symm.trans (mul_right_cancel₀ hδ.ne' hAR)
  · intro hLR
    refine ⟨L, p₁ - L * b, ?_⟩
    filter_upwards [Ioo_mem_nhds hab hbc] with x hx
    rcases lt_trichotomy x b with hxb | rfl | hbx
    · rw [hl x ⟨hx.1, hxb⟩]
      change p₁ + L * (x - b) = L * x + (p₁ - L * b)
      ring
    · rw [hb]
      ring
    · rw [hr x ⟨hbx, hx.2⟩]
      change p₁ + R * (x - b) = L * x + (p₁ - L * b)
      rw [← hLR]
      ring

theorem measurableSet_collinear {A : Type*} [MeasurableSpace A]
    (a b c p₀ p₁ p₂ : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hp₀ : Measurable p₀) (hp₁ : Measurable p₁) (hp₂ : Measurable p₂) :
    MeasurableSet {w | (b w - a w) * (p₂ w - p₁ w) =
      (p₁ w - p₀ w) * (c w - b w)} :=
  measurableSet_eq_fun ((hb.sub ha).mul (hp₂.sub hp₁))
    ((hp₁.sub hp₀).mul (hc.sub hb))

theorem isClosed_collinear {A : Type*} [TopologicalSpace A]
    (a b c p₀ p₁ p₂ : A → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hp₀ : Continuous p₀) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂) :
    IsClosed {w | (b w - a w) * (p₂ w - p₁ w) =
      (p₁ w - p₀ w) * (c w - b w)} :=
  isClosed_eq ((hb.sub ha).mul (hp₂.sub hp₁)) ((hp₁.sub hp₀).mul (hc.sub hb))

theorem affineNear_continuousAt (f : Curve) (b : ℝ) (h : AffineNear f b) :
    ContinuousAt f.price b := by
  obtain ⟨A, B, hlocal⟩ := h
  exact (show ContinuousAt (fun x : ℝ => A * x + B) b by fun_prop).congr_of_eventuallyEq hlocal

/-- A vertical jump is always an intrinsic breakpoint, regardless of the
selected point value. Thus jump cells cannot be discarded as collinear joins. -/
theorem not_affineNear_of_distinct_oneSidedLimits (f : Curve) (b leftValue rightValue : ℝ)
    (hl : Tendsto f.price (𝓝[<] b) (𝓝 leftValue))
    (hr : Tendsto f.price (𝓝[>] b) (𝓝 rightValue))
    (hne : leftValue ≠ rightValue) : ¬AffineNear f b := by
  intro ha
  have hc := affineNear_continuousAt f b ha
  have hleft : leftValue = f.price b :=
    tendsto_nhds_unique hl (hc.mono_left nhdsWithin_le_nhds)
  have hright : rightValue = f.price b :=
    tendsto_nhds_unique hr (hc.mono_left nhdsWithin_le_nhds)
  exact hne (hleft.trans hright.symm)

end Thesis.DayAhead.PLBreakpointCollinearity
