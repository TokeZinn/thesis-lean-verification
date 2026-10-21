import Thesis.Foundations.Stochastic.PointProcessAlignment
import Thesis.Foundations.Stochastic.IntegerMeasureCompleteness
import Thesis.Appendices.Analysis.BoundedMetric

/-! # Prokhorov results for the original extended base metric

Small Prokhorov balls depend only on base distances below one. Truncating the
base therefore preserves the Prokhorov uniformity, without changing the
original distance formula in the theorem statements.
-/

noncomputable section
open Set Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace Thesis.Foundations.Stochastic.ExtendedPointMeasures
open Preliminary.BoundedMetric PointProcesses FiniteMeasureProkhorov

universe u v
variable {X : Type u} [d : EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem thickening_truncated (r : ℝ) (hr : r ≤ 1) (B : Set X) :
    @Metric.thickening X (truncatedMetricSpace X).toPseudoEMetricSpace r B =
      Metric.thickening r B := by
  ext x
  simp only [Metric.mem_thickening_iff_exists_edist_lt]
  have hr' : ENNReal.ofReal r ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hr
  simp only [truncated_edist, min_lt_iff, not_lt_of_ge hr', or_false]

omit [BorelSpace X] in
/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`.
The original and truncated-base Prokhorov distances have identical small balls. -/
theorem prokhorov_small_ball (μ ν : Measure X) {ε : ℝ≥0∞} (hε : ε ≤ 1) :
    @levyProkhorovEDist X _ (truncatedMetricSpace X).toPseudoEMetricSpace μ ν < ε ↔
      levyProkhorovEDist μ ν < ε := by
  simp only [levyProkhorovEDist, sInf_lt_iff]
  constructor <;> rintro ⟨δ, hδ, hδε⟩ <;> refine ⟨δ, ?_, hδε⟩
  · intro B hB
    have hr : δ.toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) (hδε.le.trans hε)
    simpa only [thickening_truncated _ hr] using hδ B hB
  · intro B hB
    have hr : δ.toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) (hδε.le.trans hε)
    simpa only [thickening_truncated _ hr] using hδ B hB

@[implicit_reducible]
def boundedLPMetric : PseudoMetricSpace (LP X) :=
  @LevyProkhorov.instPseudoMetricSpaceFiniteMeasure X _
    (truncatedMetricSpace X).toPseudoEMetricSpace inferInstance

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`. -/
theorem prokhorov_uniformSpace_eq :
    (inferInstance : UniformSpace (LP X)) = (boundedLPMetric (X := X)).toUniformSpace := by
  apply UniformSpace.ext
  apply (uniformity_basis_edist' (α := LP X) 1 zero_lt_one).ext
    (@uniformity_basis_edist' _ (boundedLPMetric (X := X)).toPseudoEMetricSpace
      1 zero_lt_one)
  · intro ε hε
    exact ⟨ε, hε, fun p hp => (prokhorov_small_ball _ _ hε.2.le).mp hp⟩
  · intro ε hε
    exact ⟨ε, hε, fun p hp => (prokhorov_small_ball _ _ hε.2.le).mpr hp⟩

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`.
Completeness uses the original, possibly infinite base metric. -/
theorem completeSpace [CompleteSpace X] [SeparableSpace X] : CompleteSpace (LP X) := by
  have hU := prokhorov_uniformSpace_eq (X := X)
  have hc : @CompleteSpace (LP X) (boundedLPMetric (X := X)).toUniformSpace := by
    letI b := truncatedMetricSpace X
    letI : EMetricSpace X := b.toEMetricSpace
    exact FiniteMeasureCompleteness.completeSpace (X := X)
  rw [← hU] at hc
  exact hc

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`. -/
theorem separableSpace [SeparableSpace X] : SeparableSpace (LP X) := by
  have hT := congrArg (fun U : UniformSpace (LP X) => U.toTopologicalSpace)
    (prokhorov_uniformSpace_eq (X := X))
  have hs : @SeparableSpace (LP X)
      (boundedLPMetric (X := X)).toUniformSpace.toTopologicalSpace := by
    letI b := truncatedMetricSpace X
    letI : EMetricSpace X := b.toEMetricSpace
    exact FiniteMeasureDensity.separableSpace (X := X)
  exact Eq.mpr (congrArg (fun T : TopologicalSpace (LP X) =>
    @SeparableSpace (LP X) T) hT) hs

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`.
The weak topology is the topology of the original Prokhorov distance. -/
def finiteMeasureHomeomorph [SeparableSpace X] : FiniteMeasure X ≃ₜ LP X := by
  have hT := congrArg (fun U : UniformSpace (LP X) => U.toTopologicalSpace)
    (prokhorov_uniformSpace_eq (X := X))
  have hf : @Continuous (FiniteMeasure X) (LP X) inferInstance
      (boundedLPMetric (X := X)).toUniformSpace.toTopologicalSpace
      LevyProkhorov.ofMeasure := by
    letI b := truncatedMetricSpace X
    letI : EMetricSpace X := b.toEMetricSpace
    exact (FiniteMeasureProkhorov.finiteMeasureHomeomorph (X := X)).continuous_toFun
  have hg : @Continuous (LP X) (FiniteMeasure X)
      (boundedLPMetric (X := X)).toUniformSpace.toTopologicalSpace inferInstance
      LevyProkhorov.toMeasure := by
    letI b := truncatedMetricSpace X
    letI : EMetricSpace X := b.toEMetricSpace
    exact (FiniteMeasureProkhorov.finiteMeasureHomeomorph (X := X)).continuous_invFun
  exact {
    toEquiv := LevyProkhorov.toMeasureEquiv.symm
    continuous_toFun := Eq.mpr (congrArg (fun T : TopologicalSpace (LP X) =>
      @Continuous (FiniteMeasure X) (LP X) inferInstance T LevyProkhorov.ofMeasure) hT) hf
    continuous_invFun := Eq.mpr (congrArg (fun T : TopologicalSpace (LP X) =>
      @Continuous (LP X) (FiniteMeasure X) T inferInstance LevyProkhorov.toMeasure) hT) hg }

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`. -/
theorem tendsto_iff [SeparableSpace X] {ι : Type*} {L : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} :
    Tendsto (fun i => LevyProkhorov.ofMeasure (μs i)) L
      (𝓝 (LevyProkhorov.ofMeasure μ)) ↔ Tendsto μs L (𝓝 μ) := by
  have hT := congrArg (fun U : UniformSpace (LP X) => U.toTopologicalSpace)
    (prokhorov_uniformSpace_eq (X := X))
  change @Tendsto _ _ (fun i => LevyProkhorov.ofMeasure (μs i)) L
    (@nhds _ (inferInstance : TopologicalSpace (LP X)) (LevyProkhorov.ofMeasure μ)) ↔ _
  change (inferInstance : TopologicalSpace (LP X)) = _ at hT
  rw [hT]
  letI b := truncatedMetricSpace X
  letI : EMetricSpace X := b.toEMetricSpace
  exact FiniteMeasureProkhorov.tendsto_iff

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`.
The original distance separates finite Borel measures. -/
theorem dist_eq_zero_iff [SeparableSpace X] (μ ν : LP X) : dist μ ν = 0 ↔ μ = ν := by
  letI : T2Space (LP X) := (finiteMeasureHomeomorph (X := X)).symm.isEmbedding.t2Space
  exact ⟨fun h => (Metric.inseparable_iff.mpr h).eq, fun h => h ▸ dist_self μ⟩

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`.
The integer-valued subspace is complete for the original Prokhorov distance. -/
theorem integer_completeSpace [CompleteSpace X] [SeparableSpace X] :
    CompleteSpace (ProkhorovFiniteIntegerMeasures X) := by
  have hU := congrArg (fun U : UniformSpace (LP X) =>
    UniformSpace.comap (fun μ : ProkhorovFiniteIntegerMeasures X => μ.val) U)
    (prokhorov_uniformSpace_eq (X := X))
  have hc : @CompleteSpace (ProkhorovFiniteIntegerMeasures X)
      (UniformSpace.comap Subtype.val (boundedLPMetric (X := X)).toUniformSpace) := by
    letI b := truncatedMetricSpace X
    letI : EMetricSpace X := b.toEMetricSpace
    exact IntegerMeasureCompleteness.completeSpace
  exact Eq.mpr (congrArg (fun U : UniformSpace (ProkhorovFiniteIntegerMeasures X) =>
    @CompleteSpace _ U) hU) hc

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`. -/
theorem integer_separableSpace [CompleteSpace X] [SeparableSpace X] :
    SeparableSpace (ProkhorovFiniteIntegerMeasures X) := by
  letI b := truncatedMetricSpace X
  haveI : StandardBorelSpace X := inferInstance
  exact IntegerMeasureSeparability.separableSpace

/-- Original label: `rem:point-process-measurability-equivalence`.
Evaluation-wise measurability equals measurability into the actual integer
measure space with its original Prokhorov Borel sigma-algebra. -/
theorem integer_measurable_iff [SeparableSpace X]
    {Ω : Type v} [MeasurableSpace Ω] (Ξ : Ω → ProkhorovFiniteIntegerMeasures X) :
    (∀ B : Set X, MeasurableSet B →
      Measurable (fun ω => ((Ξ ω).val.toMeasure : Measure X) B)) ↔
      @Measurable Ω (ProkhorovFiniteIntegerMeasures X) _ (borel _) Ξ := by
  letI : BorelSpace (FiniteMeasure X) := by
    letI b := truncatedMetricSpace X
    exact FiniteMeasureBorel.weak_borelSpace
  letI : MeasurableSpace (LP X) := borel _
  letI : BorelSpace (LP X) := ⟨rfl⟩
  letI : MeasurableSpace (ProkhorovFiniteIntegerMeasures X) := borel _
  letI : BorelSpace (ProkhorovFiniteIntegerMeasures X) := ⟨rfl⟩
  constructor
  · intro h
    have hm : Measurable (fun ω => (Ξ ω).val.toMeasure) :=
      (Measure.measurable_measure.mpr h).subtype_mk
    have hp := (finiteMeasureHomeomorph (X := X)).continuous.measurable.comp hm
    change @Measurable Ω (ProkhorovFiniteIntegerMeasures X) _
      (@borel _ (TopologicalSpace.induced Subtype.val inferInstance)) Ξ
    rw [borel_comap]
    exact hp.subtype_mk
  · intro h B hB
    have hp := continuous_subtype_val.measurable.comp h
    have hm := (finiteMeasureHomeomorph (X := X)).symm.continuous.measurable.comp hp
    exact (Measure.measurable_coe hB).comp (measurable_subtype_coe.comp hm)

/-- Original label: `lem:measurable-enumeration`.
The identity from Prokhorov Borel measures to evaluation-measurable measures. -/
theorem measurable_fromProkhorovInteger [SeparableSpace X] :
    @Measurable (ProkhorovFiniteIntegerMeasures X) (FiniteIntegerMeasures X)
      (borel _) inferInstance PointProcessAlignment.fromProkhorovInteger := by
  letI : MeasurableSpace (ProkhorovFiniteIntegerMeasures X) := borel _
  have he := (integer_measurable_iff (id : ProkhorovFiniteIntegerMeasures X → _)).mpr
    (@measurable_id _ (borel _))
  exact ((Measure.measurable_measure.mpr he).subtype_mk).subtype_mk

/-- Original label: `lem:measurable-enumeration`.
The measurable representative exists for the original extended-base metric. -/
theorem measurableEnumeration_prokhorovBorel [CompleteSpace X] [SeparableSpace X] :
    ∃ τ : ProkhorovFiniteIntegerMeasures X → MarketRepresentation.Tuple X,
      @Measurable _ _ (borel _) (MarketRepresentation.TuplesMetricTopology.tupleHausdorffBorel
        (X := X)) τ ∧
      ∀ μ, TupleMeasures.tupleInducedIntegerMeasure (τ μ) =
        PointProcessAlignment.fromProkhorovInteger μ := by
  haveI : StandardBorelSpace X := by
    letI := truncatedMetricSpace X
    infer_instance
  refine ⟨fun μ => TupleMeasures.measurableEnumeration
      (PointProcessAlignment.fromProkhorovInteger μ),
    (TupleMeasures.measurable_measurableEnumeration (X := X)).comp
      measurable_fromProkhorovInteger, ?_⟩
  exact fun μ => TupleMeasures.tupleInducedIntegerMeasure_measurableEnumeration _

end Thesis.Foundations.Stochastic.ExtendedPointMeasures
