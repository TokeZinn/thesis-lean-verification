import Thesis.Foundations.MarketRepresentation.FiniteSetExamples
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Gluing

/-! # Complete finite-set spaces without a uniform isolation bound

The prose following `prop:finite-hausdorff-uniformly-discrete-iff` asserts
that isolation is sufficient, but not necessary, for finite-set completeness.
We use a discrete disjoint union of two-point metric spaces, whose internal
distances tend to zero. Distinct components stay at least distance one apart.
-/

noncomputable section

namespace Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets

open Set TopologicalSpace

universe u

/-- On a discrete metric space compact subsets are exactly finite subsets.
Both hyperspaces use the actual Hausdorff extended distance, including empty sets. -/
def finiteSubsetsEquivCompacts {X : Type u} [EMetricSpace X] [DiscreteTopology X] :
    FiniteSubsets X ≃ᵢ Compacts X where
  toFun s := ⟨s.val, s.property.isCompact⟩
  invFun s := ⟨s, s.isCompact.finite_of_discrete⟩
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun _ _ := rfl

/-- Completeness follows from compact-hyperspace completeness, without any
uniform lower bound on distances between distinct base points. -/
theorem finiteSubsets_complete_of_complete_discrete {X : Type u}
    [EMetricSpace X] [CompleteSpace X] [DiscreteTopology X] :
    CompleteSpace (FiniteSubsets X) :=
  completeSpace_congr finiteSubsetsEquivCompacts.isometry.isUniformEmbedding |>.mpr inferInstance

namespace ShrinkingPairs

/-- The `n`th component has two real points separated by `1/(n+1)`. -/
def Pair (n : ℕ) := {x : ℝ // x ∈ ({0, (n + 1 : ℝ)⁻¹} : Set ℝ)}

instance (n : ℕ) : MetricSpace (Pair n) := inferInstanceAs (MetricSpace (Subtype _))

instance (n : ℕ) : Finite (Pair n) :=
  ((Set.finite_singleton (n + 1 : ℝ)⁻¹).insert 0).to_subtype

instance (n : ℕ) : CompleteSpace (Pair n) := inferInstance

instance (n : ℕ) : DiscreteTopology (Pair n) := inferInstance

/-- A countable union of shrinking pairs, with distinct components separated. -/
def Space := Σ n, Pair n

instance : MetricSpace Space := Metric.Sigma.metricSpace

instance : CompleteSpace Space := Metric.Sigma.completeSpace

instance : DiscreteTopology Space := inferInstanceAs (DiscreteTopology (Σ n, Pair n))

def leftPoint (n : ℕ) : Space := ⟨n, ⟨0, by simp⟩⟩

def rightPoint (n : ℕ) : Space := ⟨n, ⟨(n + 1 : ℝ)⁻¹, by simp⟩⟩

theorem leftPoint_ne_rightPoint (n : ℕ) : leftPoint n ≠ rightPoint n := by
  intro h
  have hv := congrArg (fun p : Space => p.2.val) h
  change (0 : ℝ) = (n + 1 : ℝ)⁻¹ at hv
  have hpos : 0 < (n + 1 : ℝ)⁻¹ := by positivity
  linarith

theorem dist_leftPoint_rightPoint (n : ℕ) :
    dist (leftPoint n) (rightPoint n) = 1 / (n + 1 : ℝ) := by
  change @dist (Σ n, Pair n) Metric.Sigma.instDist
    (Sigma.mk n ⟨0, by simp⟩) (Sigma.mk n ⟨(n + 1 : ℝ)⁻¹, by simp⟩) = _
  rw [Metric.Sigma.dist_same]
  change dist (0 : ℝ) (n + 1 : ℝ)⁻¹ = _
  simp [Real.dist_eq, abs_of_nonneg (show 0 ≤ (n + 1 : ℝ)⁻¹ by positivity)]

/-- Original label: `prop:finite-hausdorff-uniformly-discrete-iff`.
Evidence for the following informal non-necessity claim: no uniform bound
works for this complete, discrete metric space. -/
theorem not_isolative : ¬ Isolative Space := by
  rw [isolative_iff_real_bound]
  rintro ⟨B, hB, hsep⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hB
  have hle := hsep (leftPoint n) (rightPoint n) (leftPoint_ne_rightPoint n)
  rw [edist_dist, dist_leftPoint_rightPoint] at hle
  have : B ≤ 1 / (n + 1 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  exact (not_lt_of_ge this) hn

/-- Original label: `prop:finite-hausdorff-uniformly-discrete-iff`.
The complete finite-subset Hausdorff space in the source's informal claim,
with an ordinary finite-valued metric on its non-isolative base. -/
theorem finiteSubsets_complete_without_isolation :
    CompleteSpace (FiniteSubsets Space) ∧ ¬ Isolative Space :=
  ⟨finiteSubsets_complete_of_complete_discrete, not_isolative⟩

end ShrinkingPairs

end Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
