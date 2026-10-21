import Thesis.Foundations.MarketRepresentation.FiniteSets

/-! # Current doctoral-thesis terminology

The October manuscript renames “isolative” to “uniformly discrete” and
“distinct finite sets” to “labelled finite sets”. These are public aliases of
the same constructions; old names remain only as implementation support.
-/

namespace Thesis.Foundations.MarketRepresentation.DoctoralGeometry

open FiniteSets FiniteSets.FiniteSubsets

universe u

/-- Original label: `defn:uniformly-discrete`. -/
abbrev UniformlyDiscrete (X : Type u) [EDist X] : Prop := Isolative X

/-- Original label: `prop:uniformly-discrete-complete`.
Every Cauchy sequence in a uniformly discrete extended metric space is
eventually constant. -/
theorem eventually_constant_of_uniformlyDiscrete {X : Type u} [PseudoEMetricSpace X]
    (h : UniformlyDiscrete X) {x : ℕ → X} (hx : CauchySeq x) :
    ∃ N, ∀ n, N ≤ n → x n = x N :=
  eventually_constant_of_isolative h hx

/-- Original label: `prop:uniformly-discrete-complete`. -/
theorem complete_of_uniformlyDiscrete {X : Type u} [PseudoEMetricSpace X]
    (h : UniformlyDiscrete X) : CompleteSpace X :=
  completeSpace_of_isolative h

/-- Original label: `prop:finite-hausdorff-uniformly-discrete`. -/
theorem finiteSubsets_uniformlyDiscrete {X : Type u} [PseudoEMetricSpace X]
    (h : UniformlyDiscrete X) : UniformlyDiscrete (FiniteSubsets X) :=
  finiteSubsets_isolative h

/-- Original label: `prop:finite-hausdorff-uniformly-discrete-iff`. -/
theorem finiteSubsets_uniformlyDiscrete_iff {X : Type u} [PseudoEMetricSpace X] :
    UniformlyDiscrete (FiniteSubsets X) ↔ UniformlyDiscrete X :=
  finiteSubsets_isolative_iff_isolative

/-- Original label: `defn:labelled-finite-sets`.
Labels use zero-based naturals internally; adding one is the isometry to
the manuscript's positive-natural labels. -/
abbrev LabelledFiniteSubsets (X : Type u) := DistinctFiniteSubsets X

/-- Original label: `thm:labelled-properties`. -/
theorem labelledProperties {X : Type u} [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [CompleteSpace X] :
    TopologicalSpace.SeparableSpace (LabelledFiniteSubsets X) ∧
      CompleteSpace (LabelledFiniteSubsets X) :=
  DistinctFiniteSubsets.distinctProperties

end Thesis.Foundations.MarketRepresentation.DoctoralGeometry
