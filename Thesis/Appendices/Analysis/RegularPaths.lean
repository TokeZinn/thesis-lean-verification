import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Measurability and boundedness of paths with one-sided limits -/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.RegularPaths

universe u v

/--
Thesis source:
`A - appendices/analysis.tex`, Lemma `lem:regular-paths-bounded-borel`.

Original label: `lem:regular-paths-bounded-borel`, Borel-measurability clause.

Informal statement: a right-continuous map from a second-countable linearly
ordered space into a Borel space is Borel measurable (càdlàg paths; càglàd
paths follow by order reversal, continuous paths as a special case).

Lean strategy / thesis relation note: the thesis approximates `f` by step
functions on a uniform grid and takes the pointwise limit; Lean reaches the
same conclusion directly through the right-neighbourhood measurability
criterion `MeasurableSet.of_mem_nhdsGT`, which is the measure-theoretic
content of that limit argument.
-/
theorem measurable_of_right_continuous
    {α : Type u} {V : Type v} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    {f : α → V} (hf : ∀ x, ContinuousWithinAt f (Ici x) x) : Measurable f := by
  apply measurable_of_isOpen
  intro U hU
  apply MeasurableSet.of_mem_nhdsGT
  intro x hx
  exact (hf x).mono Ioi_subset_Ici_self (hU.mem_nhds hx)

/--
Thesis source:
`A - appendices/analysis.tex`, Lemma `lem:regular-paths-bounded-borel`.

Original label: `lem:regular-paths-bounded-borel`, boundedness clause.

Informal statement: on a compact linearly ordered space, a map with one-sided
limits on both sides (right-continuous with left limits, as for càdlàg paths)
into a pseudometric space has bounded range.

Lean strategy / thesis relation note: the thesis argues by contradiction
along a monotone subsequence and its one-sided limit; Lean uses the equivalent
local-boundedness criterion on a compact space, with the two one-sided limits
supplying bounded images of a left and a right neighbourhood of each point.
-/
theorem bounded_range_of_right_continuous_left_limits
    {α : Type u} {V : Type v} [TopologicalSpace α] [LinearOrder α]
    [CompactSpace α] [PseudoMetricSpace V]
    {f : α → V} (hr : ∀ x, ContinuousWithinAt f (Ici x) x)
    (hl : ∀ x, ∃ l, Tendsto f (𝓝[Iio x] x) (𝓝 l)) :
    Bornology.IsBounded (Set.range f) := by
  rw [← image_univ]
  apply Bornology.isBounded_image_of_isLocallyBounded_of_isCompact isCompact_univ
  intro x
  obtain ⟨l, hl⟩ := hl x
  obtain ⟨L, hL, hLb⟩ := Metric.exists_isBounded_image_of_tendsto hl
  obtain ⟨R, hR, hRb⟩ := Metric.exists_isBounded_image_of_tendsto (hr x)
  refine ⟨L ∪ R, ?_, ?_⟩
  · have h : L ∪ R ∈ 𝓝[Iio x] x ⊔ 𝓝[Ici x] x :=
      mem_sup.mpr ⟨mem_of_superset hL subset_union_left,
        mem_of_superset hR subset_union_right⟩
    simpa only [← nhdsWithin_union, Iio_union_Ici, nhdsWithin_univ] using h
  · rw [image_union]
    exact hLb.union hRb

theorem memLp_restrict_of_right_continuous_left_limits
    {α : Type u} {V : Type v} [TopologicalSpace α] [LinearOrder α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup V] [TopologicalSpace.SeparableSpace V]
    {s : Set α} [OrderTopology s] {μ : Measure α} [IsFiniteMeasure (μ.restrict s)]
    (hs : IsCompact s) (hsm : MeasurableSet s) {f : α → V}
    (hr : ∀ x ∈ s, ContinuousWithinAt f (s ∩ Ici x) x)
    (hl : ∀ x ∈ s, ∃ l, Tendsto f (𝓝[s ∩ Iio x] x) (𝓝 l))
    (p : ℝ≥0∞) : MemLp f p (μ.restrict s) := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  have hright (x : s) : ContinuousWithinAt (fun y : s => f y) (Ici x) x := by
    exact (hr x x.property).comp continuous_subtype_val.continuousWithinAt
      (fun y hy => ⟨y.property, hy⟩)
  have hleft (x : s) : ∃ l, Tendsto (fun y : s => f y) (𝓝[Iio x] x) (𝓝 l) := by
    obtain ⟨l, hl⟩ := hl x x.property
    refine ⟨l, hl.comp ?_⟩
    exact continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin
      (fun y hy => ⟨y.property, hy⟩)
  have hm : Measurable (fun y : s => f y) := measurable_of_right_continuous hright
  have hb := bounded_range_of_right_continuous_left_limits hright hleft
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  apply MemLp.of_bound (aemeasurable_restrict_of_measurable_subtype hsm hm).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hsm] with x hx
  exact hC (f x) ⟨⟨x, hx⟩, rfl⟩

theorem memLp_restrict_of_left_continuous_right_limits
    {α : Type u} {V : Type v} [TopologicalSpace α] [LinearOrder α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup V] [TopologicalSpace.SeparableSpace V]
    {s : Set α} [OrderTopology s] {μ : Measure α} [IsFiniteMeasure (μ.restrict s)]
    (hs : IsCompact s) (hsm : MeasurableSet s) {f : α → V}
    (hl : ∀ x ∈ s, ContinuousWithinAt f (s ∩ Iic x) x)
    (hr : ∀ x ∈ s, ∃ l, Tendsto f (𝓝[s ∩ Ioi x] x) (𝓝 l))
    (p : ℝ≥0∞) : MemLp f p (μ.restrict s) := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  have hleft (x : s) : ContinuousWithinAt (fun y : s => f y) (Iic x) x := by
    exact (hl x x.property).comp continuous_subtype_val.continuousWithinAt
      (fun y hy => ⟨y.property, hy⟩)
  have hright (x : s) : ∃ l, Tendsto (fun y : s => f y) (𝓝[Ioi x] x) (𝓝 l) := by
    obtain ⟨l, hr⟩ := hr x x.property
    refine ⟨l, hr.comp ?_⟩
    exact continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin
      (fun y hy => ⟨y.property, hy⟩)
  have hm : Measurable (fun y : s => f y) :=
    measurable_of_right_continuous (α := OrderDual s) hleft
  letI : CompactSpace (OrderDual s) := ‹CompactSpace s›
  have hb := bounded_range_of_right_continuous_left_limits (α := OrderDual s) hleft hright
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  apply MemLp.of_bound (aemeasurable_restrict_of_measurable_subtype hsm hm).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hsm] with x hx
  exact hC (f x) ⟨⟨x, hx⟩, rfl⟩

end Thesis.Foundations.Preliminary.RegularPaths
