import Thesis.DayAhead.ClearingOperatorPriceCurves.FinitePricePathSource
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLBreakpointCollinearity

/-! # Actual local-affinity comparisons at transposed path vertices

Two adjacent affine formulas may have different one-sided limits. A source
vertex is removable exactly when both limits equal its selected point value
and the two slopes agree. The continuous case is precisely the source's
polynomial collinearity comparison; jumps are retained.
-/

noncomputable section
namespace Thesis.DayAhead.PLJoinComparison

open Set Filter Topology PiecewiseAffinePriceCurves PLCanonicalEncoding
open FinitePricePathSource PLBreakpointCollinearity

theorem affineNear_iff_slopes_of_values (f : Curve) {a b c L B R D : ℝ}
    (hab : a < b) (hbc : b < c)
    (hl : ∀ x ∈ Ioo a b, f.price x = L * x + B)
    (hr : ∀ x ∈ Ioo b c, f.price x = R * x + D)
    (hbl : f.price b = L * b + B) (hbr : f.price b = R * b + D) :
    AffineNear f b ↔ L = R := by
  have hls : (f.price b - (L * a + B)) / (b - a) = L := by
    rw [hbl]
    rw [div_eq_iff (sub_pos.mpr hab).ne']
    ring
  have hrs : ((R * c + D) - f.price b) / (c - b) = R := by
    rw [hbr]
    rw [div_eq_iff (sub_pos.mpr hbc).ne']
    ring
  have hleft : ∀ x ∈ Ioo a b, f.price x = f.price b +
      ((f.price b - (L * a + B)) / (b - a)) * (x - b) := by
    intro x hx
    rw [hl x hx, hls, hbl]
    ring
  have hright : ∀ x ∈ Ioo b c, f.price x = f.price b +
      (((R * c + D) - f.price b) / (c - b)) * (x - b) := by
    intro x hx
    rw [hr x hx, hrs, hbr]
    ring
  rw [affineNear_iff_collinear f hab hbc rfl hleft hright,
    ← slope_eq_iff_collinear hab hbc, hls, hrs]

theorem affineNear_iff_two_lines (f : Curve) {a b c L B R D : ℝ}
    (hab : a < b) (hbc : b < c)
    (hl : ∀ x ∈ Ioo a b, f.price x = L * x + B)
    (hr : ∀ x ∈ Ioo b c, f.price x = R * x + D) :
    AffineNear f b ↔ f.price b = L * b + B ∧ f.price b = R * b + D ∧ L = R := by
  constructor
  · intro h
    have hc := affineNear_continuousAt f b h
    have hbl : f.price b = L * b + B :=
      hc.continuousWithinAt.leftLim_eq.symm.trans (affine_gap_limits f.price hab hl).2.1
    have hbr : f.price b = R * b + D :=
      hc.continuousWithinAt.rightLim_eq.symm.trans (affine_gap_limits f.price hbc hr).1
    exact ⟨hbl, hbr, (affineNear_iff_slopes_of_values f hab hbc hl hr hbl hbr).mp h⟩
  · rintro ⟨hbl, hbr, hLR⟩
    exact (affineNear_iff_slopes_of_values f hab hbc hl hr hbl hbr).mpr hLR

/-- Thus the actual intrinsic-breakpoint decision is a finite collection
of Borel coordinate comparisons on every adjacent-affine cell. -/
theorem measurableSet_affineNear {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Curve) (a b c L B R D : Ω → ℝ)
    (hab : ∀ w, a w < b w) (hbc : ∀ w, b w < c w)
    (hl : ∀ w x, x ∈ Ioo (a w) (b w) → (f w).price x = L w * x + B w)
    (hr : ∀ w x, x ∈ Ioo (b w) (c w) → (f w).price x = R w * x + D w)
    (hb : Measurable b) (hL : Measurable L) (hB : Measurable B)
    (hR : Measurable R) (hD : Measurable D)
    (hvalue : Measurable (fun w => (f w).price (b w))) :
    MeasurableSet {w | AffineNear (f w) (b w)} := by
  have he : {w | AffineNear (f w) (b w)} =
      {w | (f w).price (b w) = L w * b w + B w} ∩
        {w | (f w).price (b w) = R w * b w + D w} ∩ {w | L w = R w} := by
    ext w
    simp only [mem_inter_iff, mem_setOf_eq,
      affineNear_iff_two_lines (f w) (hab w) (hbc w) (hl w) (hr w)]
    tauto
  rw [he]
  exact ((measurableSet_eq_fun hvalue ((hL.mul hb).add hB)).inter
    (measurableSet_eq_fun hvalue ((hR.mul hb).add hD))).inter
      (measurableSet_eq_fun hL hR)

def firstSample (a b : ℝ) : ℝ := (2 * a + b) / 3
def secondSample (a b : ℝ) : ℝ := (a + 2 * b) / 3
def sampledSlope (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (f (secondSample a b) - f (firstSample a b)) /
    (secondSample a b - firstSample a b)
def sampledIntercept (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  f (firstSample a b) - sampledSlope f a b * firstSample a b

/-- Two fixed interior samples recover the affine formula, so its
coefficients need no measurable choice of affine witnesses. -/
theorem affine_eq_sampled (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (h : ∃ A B : ℝ, ∀ x ∈ Ioo a b, f x = A * x + B) :
    ∀ x ∈ Ioo a b, f x = sampledSlope f a b * x + sampledIntercept f a b := by
  obtain ⟨A, B, hAB⟩ := h
  have hfirst : firstSample a b ∈ Ioo a b := by
    unfold firstSample
    constructor <;> linarith
  have hsecond : secondSample a b ∈ Ioo a b := by
    unfold secondSample
    constructor <;> linarith
  have hsample : firstSample a b < secondSample a b := by
    unfold firstSample secondSample
    linarith
  have hslope : sampledSlope f a b = A := by
    unfold sampledSlope
    rw [hAB _ hsecond, hAB _ hfirst, div_eq_iff (sub_pos.mpr hsample).ne']
    ring
  intro x hx
  rw [sampledIntercept, hslope, hAB _ hfirst, hAB x hx]
  ring

theorem measurableSet_affineNear_of_gaps {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Curve) (a b c : Ω → ℝ)
    (hab : ∀ w, a w < b w) (hbc : ∀ w, b w < c w)
    (hl : ∀ w, ∃ A B : ℝ, ∀ x ∈ Ioo (a w) (b w), (f w).price x = A * x + B)
    (hr : ∀ w, ∃ A B : ℝ, ∀ x ∈ Ioo (b w) (c w), (f w).price x = A * x + B)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hleftFirst : Measurable (fun w => (f w).price (firstSample (a w) (b w))))
    (hleftSecond : Measurable (fun w => (f w).price (secondSample (a w) (b w))))
    (hrightFirst : Measurable (fun w => (f w).price (firstSample (b w) (c w))))
    (hrightSecond : Measurable (fun w => (f w).price (secondSample (b w) (c w))))
    (hvalue : Measurable (fun w => (f w).price (b w))) :
    MeasurableSet {w | AffineNear (f w) (b w)} := by
  have hlf : Measurable (fun w => firstSample (a w) (b w)) := by
    unfold firstSample
    fun_prop
  have hls : Measurable (fun w => secondSample (a w) (b w)) := by
    unfold secondSample
    fun_prop
  have hrf : Measurable (fun w => firstSample (b w) (c w)) := by
    unfold firstSample
    fun_prop
  have hrs : Measurable (fun w => secondSample (b w) (c w)) := by
    unfold secondSample
    fun_prop
  have hL : Measurable (fun w => sampledSlope (f w).price (a w) (b w)) :=
    (hleftSecond.sub hleftFirst).div (hls.sub hlf)
  have hR : Measurable (fun w => sampledSlope (f w).price (b w) (c w)) :=
    (hrightSecond.sub hrightFirst).div (hrs.sub hrf)
  exact measurableSet_affineNear f a b c
    (fun w => sampledSlope (f w).price (a w) (b w))
    (fun w => sampledIntercept (f w).price (a w) (b w))
    (fun w => sampledSlope (f w).price (b w) (c w))
    (fun w => sampledIntercept (f w).price (b w) (c w)) hab hbc
    (fun w => affine_eq_sampled (f w).price (hab w) (hl w))
    (fun w => affine_eq_sampled (f w).price (hbc w) (hr w)) hb hL
    (hleftFirst.sub (hL.mul hlf)) hR (hrightFirst.sub (hR.mul hrf)) hvalue

end Thesis.DayAhead.PLJoinComparison
