import Thesis.Appendices.Analysis.AnalysisBasic
import Thesis.Appendices.Analysis.BoundedMetric
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Connected.Clopen

/-! # Analysis with the thesis's extended-distance convention

These statements retain infinite coordinate distances and separate hypotheses
when the manuscript makes independent completeness and separability claims.
-/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

universe u v

/-- Original label: `rem:extended-metric-convention`.
Historical DA-043: even after truncating every point distance, Hausdorff distance from a
nonempty set to the empty set remains infinite. -/
theorem truncated_hausdorff_empty {X : Type u} [EMetricSpace X]
    (A : Set X) (hA : A.Nonempty) :
    letI := BoundedMetric.truncatedMetricSpace X
    Metric.hausdorffEDist A ∅ = ∞ := by
  letI := BoundedMetric.truncatedMetricSpace X
  exact Metric.hausdorffEDist_empty hA

/-- Original label: `rem:extended-metric-convention`.
Truncating the base distance bounds Hausdorff distances between nonempty sets.
The separate empty-set theorem above retains the source's infinite value. -/
theorem truncated_hausdorff_le_one {X : Type u} [d : EMetricSpace X]
    (A B : Set X) (hA : A.Nonempty) (hB : B.Nonempty) :
    letI bounded := @BoundedMetric.truncatedMetricSpace X d
    letI : EMetricSpace X := bounded.toEMetricSpace
    Metric.hausdorffEDist A B ≤ 1 := by
  letI bounded := @BoundedMetric.truncatedMetricSpace X d
  letI : EMetricSpace X := bounded.toEMetricSpace
  apply Metric.hausdorffEDist_le_of_mem_edist
  · intro x _
    obtain ⟨y, hy⟩ := hB
    exact ⟨y, hy, min_le_right _ _⟩
  · intro y _
    obtain ⟨x, hx⟩ := hA
    exact ⟨x, hx, min_le_right _ _⟩

/-- Original block id: `source:A - appendices/analysis.tex:376:defn:32`.
The literal epsilon-delta definition with extended, rather than only real,
distances is equivalent to continuity. -/
theorem extended_epsilonDeltaContinuous_iff {X : Type u} {Y : Type v}
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x₀ : X, ∀ ε > (0 : ℝ≥0∞), ∃ δ > (0 : ℝ≥0∞),
      ∀ x : X, edist x x₀ < δ → edist (f x) (f x₀) < ε := by
  rw [continuous_iff_continuousAt]
  exact forall_congr' fun _ ↦ EMetric.tendsto_nhds_nhds

/-- Original label: `prop:spc-continuous`.
The actual supremum extended metric on continuous paths, with exactly the
compact-open uniformity. No completeness or separability is assumed. -/
@[implicit_reducible]
def continuousPathSpaceEMetricSpace (a b : ℝ) (X : Type u) [EMetricSpace X] :
    EMetricSpace C(ClosedInterval a b, X) := by
  let h := ContinuousMap.isUniformEmbedding_uniformFunOfFun
    (α := ClosedInterval a b) (β := X)
  letI : PseudoEMetricSpace C(ClosedInterval a b, X) :=
    (PseudoEMetricSpace.induced (fun f : C(ClosedInterval a b, X) ↦
      UniformFun.ofFun (f : ClosedInterval a b → X))
      inferInstance).replaceUniformity h.comap_uniformity.symm
  exact EMetricSpace.ofT0PseudoEMetricSpace _

/-- Original label: `prop:spc-continuous`.
The full source scope allows infinite distances between paths. It retains
the displayed supremum formula, completeness, and separability. -/
theorem continuousPathSpace_extended_complete_separable (a b : ℝ) (X : Type u)
    [EMetricSpace X] [CompleteSpace X] [SeparableSpace X] :
    letI := continuousPathSpaceEMetricSpace a b X
    (∀ f g : C(ClosedInterval a b, X), edist f g = ⨆ t, edist (f t) (g t)) ∧
      Nonempty (CompleteSpace C(ClosedInterval a b, X)) ∧
      Nonempty (SeparableSpace C(ClosedInterval a b, X)) := by
  letI := continuousPathSpaceEMetricSpace a b X
  exact ⟨fun _ _ ↦ rfl, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

theorem isClopen_eball_top {X : Type u} [PseudoEMetricSpace X] (x : X) :
    IsClopen (Metric.eball x ∞) := by
  refine ⟨isOpen_compl_iff.mp ?_, Metric.isOpen_eball⟩
  apply EMetric.isOpen_iff.mpr
  intro y hy
  refine ⟨1, zero_lt_one, ?_⟩
  intro z hz hzfin
  apply hy
  change edist y x < ∞
  change edist z x < ∞ at hzfin
  change edist z y < 1 at hz
  exact (edist_triangle y z x).trans_lt
    (ENNReal.add_lt_top.mpr ⟨by simpa only [edist_comm] using hz.trans (by simp), hzfin⟩)

theorem continuous_preconnected_edist_lt_top {A : Type v} {X : Type u}
    [TopologicalSpace A] [PreconnectedSpace A] [PseudoEMetricSpace X]
    (f : A → X) (hf : Continuous f) (s t : A) : edist (f s) (f t) < ∞ := by
  have hall : f ⁻¹' Metric.eball (f t) ∞ = univ :=
    ((isClopen_eball_top (f t)).preimage hf).eq_univ ⟨t, by simp⟩
  have hs : s ∈ f ⁻¹' Metric.eball (f t) ∞ := hall.symm ▸ mem_univ s
  exact hs

/-- Original block id: `source:A - appendices/analysis.tex:408:prop:34`.
The graph is compact and closed, and is bounded for the displayed sum
extended metric. Connectedness of the interval, in addition to compactness,
puts the graph in a finite-distance component. -/
theorem continuousGraph_extended_compact_closed_bounded {a b : ℝ} (hab : a ≤ b)
    {X : Type u} [EMetricSpace X] (f : C(ClosedInterval a b, X)) :
    IsCompact (continuousGraph f) ∧ IsClosed (continuousGraph f) ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ s t : ClosedInterval a b,
        edist s t + edist (f s) (f t) ≤ C := by
  have hc : IsCompact (continuousGraph f) :=
    isCompact_range (continuous_id.prodMk f.continuous)
  refine ⟨hc, hc.isClosed, ?_⟩
  letI : PreconnectedSpace (ClosedInterval a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let t₀ : ClosedInterval a b := ⟨a, le_rfl, hab⟩
  let Y := Metric.eball (f t₀) ∞
  letI : MetricSpace Y := metricSpaceEMetricBall (f t₀) ∞
  let g : C(ClosedInterval a b, Y) :=
    ⟨fun t ↦ ⟨f t, continuous_preconnected_edist_lt_top f f.continuous t t₀⟩,
      f.continuous.subtype_mk _⟩
  have hdom : Metric.ediam (univ : Set (ClosedInterval a b)) < ∞ :=
    lt_top_iff_ne_top.mpr isCompact_univ.isBounded.ediam_ne_top
  have hrange : Metric.ediam (range g) < ∞ :=
    lt_top_iff_ne_top.mpr (isCompact_range g.continuous).isBounded.ediam_ne_top
  refine ⟨Metric.ediam (univ : Set (ClosedInterval a b)) + Metric.ediam (range g),
    ENNReal.add_lt_top.mpr ⟨hdom, hrange⟩, ?_⟩
  intro s t
  exact add_le_add (Metric.edist_le_ediam_of_mem (mem_univ s) (mem_univ t))
    (Metric.edist_le_ediam_of_mem (mem_range_self s : g s ∈ range g) (mem_range_self t))

end Thesis.Foundations.Preliminary.Analysis
