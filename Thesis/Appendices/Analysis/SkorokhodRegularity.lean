import Thesis.Appendices.Analysis.SkorokhodSeparation
import Thesis.Appendices.Analysis.RegularPaths

/-! # Boundedness of the thesis's one-sided regular paths

The literal epsilon definitions imply the usual one-sided filter limits.
Compactness then bounds each path, so the Skorokhod distance is finite.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ} {X : Type*} [MetricSpace X] {f : ClosedInterval a b → X}

theorem IsRightContinuousOnIcc.continuousWithinAt (hf : IsRightContinuousOnIcc f)
    (t : ClosedInterval a b) : ContinuousWithinAt f (Ici t) t := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  by_cases ht : (t : ℝ) = b
  · refine ⟨1, zero_lt_one, fun x hx _ => ?_⟩
    have hxt : x = t := Subtype.ext (by
      change (t : ℝ) ≤ x at hx
      linarith [x.property.2])
    simpa only [hxt, dist_self] using hε
  have htb := lt_of_le_of_ne t.property.2 ht
  obtain ⟨δ, hδ, hlocal⟩ := hf t htb ε hε
  refine ⟨min δ (b - t), lt_min hδ (sub_pos.mpr htb), fun x hx hdist => ?_⟩
  rcases (show t ≤ x from hx).eq_or_lt with hxt | hxt
  · simpa only [hxt, dist_self] using hε
  have habs : |(x : ℝ) - t| < min δ (b - t) := hdist
  have hxδ := (abs_lt.mp habs).2
  apply hlocal x hxt
  apply lt_min <;> linarith [min_le_left δ (b - t), min_le_right δ (b - t)]

theorem IsLeftContinuousOnIcc.continuousWithinAt (hf : IsLeftContinuousOnIcc f)
    (t : ClosedInterval a b) : ContinuousWithinAt f (Iic t) t := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  by_cases ht : (t : ℝ) = a
  · refine ⟨1, zero_lt_one, fun x hx _ => ?_⟩
    have hxt : x = t := Subtype.ext (by
      change (x : ℝ) ≤ t at hx
      linarith [x.property.1])
    simpa only [hxt, dist_self] using hε
  have hta := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  obtain ⟨δ, hδ, hlocal⟩ := hf t hta ε hε
  refine ⟨min δ (t - a), lt_min hδ (sub_pos.mpr hta), fun x hx hdist => ?_⟩
  rcases (show x ≤ t from hx).eq_or_lt with hxt | hxt
  · simpa only [hxt, dist_self] using hε
  have habs : |(x : ℝ) - t| < min δ (t - a) := hdist
  have hxδ := (abs_lt.mp habs).1
  apply hlocal x _ hxt
  apply max_lt <;> linarith [min_le_left δ (t - a), min_le_right δ (t - a)]

theorem HasLeftLimitsOnIcc.tendsto (hf : HasLeftLimitsOnIcc f)
    (t : ClosedInterval a b) : ∃ L, Tendsto f (𝓝[Iio t] t) (𝓝 L) := by
  by_cases ht : (t : ℝ) = a
  · refine ⟨f t, Metric.tendsto_nhdsWithin_nhds.mpr fun ε _ =>
      ⟨1, zero_lt_one, fun x hx _ => ?_⟩⟩
    have hxt : (x : ℝ) < t := hx
    exact False.elim (by linarith [x.property.1])
  have hta := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  obtain ⟨L, hL⟩ := hf t hta
  refine ⟨L, Metric.tendsto_nhdsWithin_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := hL ε hε
  refine ⟨min δ (t - a), lt_min hδ (sub_pos.mpr hta), fun x hx hdist => ?_⟩
  have habs : |(x : ℝ) - t| < min δ (t - a) := hdist
  have hxδ := (abs_lt.mp habs).1
  apply hlocal x _ hx
  apply max_lt <;> linarith [min_le_left δ (t - a), min_le_right δ (t - a)]

theorem HasRightLimitsOnIcc.tendsto (hf : HasRightLimitsOnIcc f)
    (t : ClosedInterval a b) : ∃ L, Tendsto f (𝓝[Ioi t] t) (𝓝 L) := by
  by_cases ht : (t : ℝ) = b
  · refine ⟨f t, Metric.tendsto_nhdsWithin_nhds.mpr fun ε _ =>
      ⟨1, zero_lt_one, fun x hx _ => ?_⟩⟩
    have hxt : (t : ℝ) < x := hx
    exact False.elim (by linarith [x.property.2])
  have htb := lt_of_le_of_ne t.property.2 ht
  obtain ⟨L, hL⟩ := hf t htb
  refine ⟨L, Metric.tendsto_nhdsWithin_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := hL ε hε
  refine ⟨min δ (b - t), lt_min hδ (sub_pos.mpr htb), fun x hx hdist => ?_⟩
  have habs : |(x : ℝ) - t| < min δ (b - t) := hdist
  have hxδ := (abs_lt.mp habs).2
  apply hlocal x hx
  apply lt_min <;> linarith [min_le_left δ (b - t), min_le_right δ (b - t)]

theorem RegularPath.isBounded_range {side : PathOrientation} (f : RegularPath a b X side) :
    Bornology.IsBounded (range f.val) := by
  cases side with
  | cadlag =>
      exact RegularPaths.bounded_range_of_right_continuous_left_limits
        f.property.1.continuousWithinAt f.property.2.tendsto
  | caglad =>
      letI : CompactSpace (OrderDual (ClosedInterval a b)) :=
        inferInstanceAs (CompactSpace (ClosedInterval a b))
      exact RegularPaths.bounded_range_of_right_continuous_left_limits
        (α := OrderDual (ClosedInterval a b))
        f.property.1.continuousWithinAt f.property.2.tendsto

theorem supPathEDistance_ne_top {side : PathOrientation} (f g : RegularPath a b X side) :
    supPathEDistance f.val g.val ≠ ∞ := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (f.isBounded_range.union g.isBounded_range)
  apply ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ∞ from ENNReal.ofReal_ne_top)
  rw [supPathEDistance_le_iff]
  intro t
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hC (Or.inl (mem_range_self t)) (Or.inr (mem_range_self t)))

/-- Original label: `prop:skorokhod-metric`.
The finiteness clause follows from boundedness of regular paths. -/
theorem skorokhodEDistance_ne_top {side : PathOrientation} (f g : RegularPath a b X side) :
    skorokhodEDistance f g ≠ ∞ :=
  ne_top_of_le_ne_top (supPathEDistance_ne_top f g) (skorokhodEDistance_le_sup f g)

/-- The actual metric structure induced by the thesis's infimum formula.
It is kept explicit so it cannot conflict with unrelated function topologies. -/
abbrev skorokhodMetricSpace (hab : a ≤ b) (side : PathOrientation) :
    MetricSpace (RegularPath a b X side) := by
  letI : EMetricSpace (RegularPath a b X side) :=
    { edist := skorokhodEDistance
      edist_self := skorokhodEDistance_self
      edist_comm := skorokhodEDistance_symm
      edist_triangle := skorokhodEDistance_triangle
      eq_of_edist_eq_zero := fun {f g} h => (skorokhodEDistance_eq_zero_iff hab f g).mp h }
  exact EMetricSpace.toMetricSpace skorokhodEDistance_ne_top

theorem cauchySeq_skorokhod_iff (hab : a ≤ b) {side : PathOrientation}
    (f : ℕ → RegularPath a b X side) :
    @CauchySeq (RegularPath a b X side) ℕ
      (skorokhodMetricSpace (X := X) hab side).toUniformSpace _ f ↔
      IsCauchyFor skorokhodEDistance f := by
  letI := skorokhodMetricSpace (X := X) hab side
  exact EMetric.cauchySeq_iff (u := f)

theorem tendsto_skorokhod_iff (hab : a ≤ b) {side : PathOrientation}
    (fseq : ℕ → RegularPath a b X side) (f : RegularPath a b X side) :
    Tendsto fseq atTop (@nhds (RegularPath a b X side)
      (skorokhodMetricSpace (X := X) hab side).toUniformSpace.toTopologicalSpace f) ↔
      ConvergesFor skorokhodEDistance fseq f := by
  letI := skorokhodMetricSpace (X := X) hab side
  exact EMetric.tendsto_atTop (u := fseq) (a := f)

end Thesis.Foundations.Preliminary.Analysis
