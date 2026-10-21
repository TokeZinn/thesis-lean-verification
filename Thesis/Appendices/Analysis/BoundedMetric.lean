import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Polish

/-! # Truncating extended metrics without changing their uniformity -/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.BoundedMetric

universe u

@[implicit_reducible]
private def rawTruncatedEMetricSpace (X : Type u) [EMetricSpace X] : EMetricSpace X where
  edist x y := min (edist x y) 1
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  eq_of_edist_eq_zero := by
    intro x y h
    exact edist_eq_zero.mp (by simpa using h)
  edist_triangle x y z := by
    by_cases hxy : edist x y ≤ 1
    · by_cases hyz : edist y z ≤ 1
      · rw [min_eq_left hxy, min_eq_left hyz]
        exact (min_le_left _ _).trans (edist_triangle x y z)
      · rw [min_eq_right (le_of_not_ge hyz)]
        exact (min_le_right _ _).trans (le_add_left le_rfl)
    · rw [min_eq_right (le_of_not_ge hxy)]
      exact (min_le_right _ _).trans (le_add_right le_rfl)

private theorem truncation_uniformity (X : Type u) [EMetricSpace X] :
    (inferInstance : UniformSpace X).uniformity =
      (rawTruncatedEMetricSpace X).toUniformSpace.uniformity := by
  apply (uniformity_basis_edist' (α := X) 1 zero_lt_one).ext
    (@uniformity_basis_edist' _ (rawTruncatedEMetricSpace X).toPseudoEMetricSpace
      1 zero_lt_one)
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro p hp
    change min (edist p.1 p.2) 1 < ε at hp
    exact (min_lt_iff.mp hp).resolve_right (not_lt_of_ge hε.2.le)
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro p hp
    change edist p.1 p.2 < ε at hp
    change min (edist p.1 p.2) 1 < ε
    exact lt_of_le_of_lt (min_le_left _ _) hp

/-- Original label: `rem:extended-metric-convention`.
The bounded metric `min(edist,1)` retains exactly the original uniformity and
topology. Consequently Cauchy filters, limits, continuity, and Borel sets are
unchanged, including when the original distance can be infinite. -/
@[implicit_reducible]
def truncatedMetricSpace (X : Type u) [EMetricSpace X] : MetricSpace X := by
  letI : EMetricSpace X :=
    (rawTruncatedEMetricSpace X).replaceUniformity (truncation_uniformity X)
  apply EMetricSpace.toMetricSpace
  intro x y
  change min _ (1 : ℝ≥0∞) ≠ ⊤
  exact ne_top_of_le_ne_top (by simp) (min_le_right _ _)

theorem truncated_edist (X : Type u) [EMetricSpace X] (x y : X) :
    @edist X (truncatedMetricSpace X).toEDist x y = min (edist x y) 1 := rfl

/-- Original label: `rem:extended-metric-convention`. -/
theorem truncated_complete (X : Type u) [EMetricSpace X] [CompleteSpace X] :
    @CompleteSpace X (truncatedMetricSpace X).toUniformSpace := inferInstance

/-- Original label: `rem:extended-metric-convention`. -/
theorem truncated_separable (X : Type u) [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] :
    @TopologicalSpace.SeparableSpace X
      (truncatedMetricSpace X).toUniformSpace.toTopologicalSpace := inferInstance

end Thesis.Foundations.Preliminary.BoundedMetric
