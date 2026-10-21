import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Formal forecasting definitions

This module contains only the explicitly formal definitions in
`2 - day-ahead/5_forecasting_impact.tex`.  The chapter's intermediate loss,
boosting, attribution, impurity, and traversal displays remain informal.
-/

namespace Thesis.DayAhead.Forecasting

open Filter Topology

universe u v w

/-! ## Fréchet differentiability -/

/--
Thesis source: Definition `defn:frechet-derivative`.

Original label: `defn:frechet-derivative`.

Mathlib's `HasFDerivAt` is the little-o formulation of the displayed
norm-quotient limit.
-/
def IsFrechetDerivativeAt
    {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace G]
    (f : H → G) (x : H) (A : H →L[ℝ] G) : Prop :=
  HasFDerivAt f A x

/-- Fréchet differentiability is existence of a bounded linear derivative.

Original label: `defn:frechet-derivative`. -/
def FrechetDifferentiableAt
    {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace G]
    (f : H → G) (x : H) : Prop :=
  ∃ A : H →L[ℝ] G, IsFrechetDerivativeAt f x A

/-- Original label: `defn:frechet-derivative`.
The library's little-o derivative is equivalent to the manuscript's exact
increment and norm-quotient limit. At zero the real quotient is totalized to
zero, so including the zero increment does not change the limit. -/
theorem isFrechetDerivativeAt_iff_norm_quotient
    {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace G]
    (f : H → G) (x : H) (A : H →L[ℝ] G) :
    IsFrechetDerivativeAt f x A ↔
      Tendsto (fun h => ‖f (x + h) - f x - A h‖ / ‖h‖) (𝓝 0) (𝓝 0) := by
  rw [IsFrechetDerivativeAt, hasFDerivAt_iff_isLittleO_nhds_zero,
    ← Asymptotics.isLittleO_norm_left, ← Asymptotics.isLittleO_norm_right,
    Asymptotics.isLittleO_iff_tendsto]
  intro h hh
  have hz : h = 0 := norm_eq_zero.mp hh
  simp [hz]

/-- Original label: `defn:frechet-derivative`.
The derivative notation denotes a unique bounded linear operator. -/
theorem frechetDerivative_unique
    {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace G]
    {f : H → G} {x : H} {A B : H →L[ℝ] G}
    (hA : IsFrechetDerivativeAt f x A) (hB : IsFrechetDerivativeAt f x B) : A = B :=
  hA.unique hB

/-- Original label: `defn:frechet-derivative`.
The derivative field is the actual bounded-linear-operator-valued function.
Its values are asserted only under the source's differentiability hypothesis. -/
noncomputable def frechetDerivative
    {H : Type u} {G : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : H → G) : H → H →L[ℝ] G :=
  fderiv ℝ f

theorem frechetDerivative_spec
    {H : Type u} {G : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : H → G} {x : H}
    {A : H →L[ℝ] G} (h : HasFDerivAt f A x) : frechetDerivative f x = A :=
  h.fderiv

theorem frechetDerivative_hasFDerivAt
    {H : Type u} {G : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : H → G}
    (h : Differentiable ℝ f) (x : H) : HasFDerivAt f (frechetDerivative f x) x :=
  (h x).hasFDerivAt

end Thesis.DayAhead.Forecasting
