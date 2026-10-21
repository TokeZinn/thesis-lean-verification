import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Preliminary Functional Analysis

Mathlib-backed formulations of the twelve original custom formal blocks in
`A - preliminary theory/linear-algebra.tex`.
The current thirteenth block, on ambient Hilbert admissibility, is formalized
in `Foundations/CurrentThesisContext.lean`.

The source works over real vector spaces.  We therefore specialise Mathlib's
normed-space, inner-product-space, continuous-linear-map, completeness, and
topological-vector-space interfaces to `ℝ` throughout.
-/

universe u v

open scoped RealInnerProductSpace

namespace Thesis
namespace Foundations
namespace Preliminary
namespace FunctionalAnalysis

/--
Original label: `defn:norm`.

Informal statement: a real normed space is a real vector space equipped with
a nonnegative size function that vanishes exactly at zero, is homogeneous
under real scalar multiplication, and satisfies the triangle inequality.

Lean strategy / thesis relation note: `NormedAddCommGroup V` supplies the
definite norm and triangle inequality, while `NormedSpace ℝ V` extends the
real module structure and supplies scalar compatibility.  Over `ℝ`, Mathlib's
`norm_smul` is precisely the thesis identity `‖a • v‖ = |a| ‖v‖`.
-/
abbrev RealNormedSpace (V : Type u) [NormedAddCommGroup V] := NormedSpace ℝ V

/--
Original label: `defn:inner-product`.

Informal statement: a real inner product is symmetric, real-linear, positive
semidefinite, and positive definite; a vector space carrying it is a real
inner-product space.

Lean strategy / thesis relation note: `InnerProductSpace.Core ℝ V` is
Mathlib's raw inner-product structure on an additive real module; importantly,
it assumes no pre-existing norm.  Over `ℝ`, its Hermitian symmetry and
conjugate-linearity fields are exactly the symmetry and real-linearity in the
thesis, while `re_inner_nonneg` and `definite` are its two positivity clauses.
-/
abbrev RealInnerProductSpace (V : Type u) [AddCommGroup V] [Module ℝ V] :=
  InnerProductSpace.Core ℝ V

/--
Original label: `prop:norm-induced-by-inner-product`.

Informal statement: in a real inner-product space, the formula
`v ↦ sqrt ⟨v,v⟩` defines a norm.

Lean strategy / thesis relation note: the dependent pair returned below
contains both the induced `Norm V` (`‖v‖ = sqrt ⟪v, v⟫`) and a
`NormedSpace.Core ℝ V` proof of the textbook norm facts; no norm is assumed in
the input.  Nonnegativity, definiteness and real homogeneity (conditions (i)
and (ii) of `defn:norm`) are immediate from the inner-product axioms and are
taken from Mathlib's core verification.  The triangle inequality (iii) is
proved here along the thesis's route: Cauchy--Schwarz `⟪u,v⟫ ≤ ‖u‖‖v‖`
(`InnerProductSpace.Core.norm_inner_le_norm`) gives
`‖u+v‖² = ‖u‖² + 2⟪u,v⟫ + ‖v‖² ≤ (‖u‖ + ‖v‖)²`, and taking square roots
(`nonneg_le_nonneg_of_sq_le_sq`) yields `‖u+v‖ ≤ ‖u‖ + ‖v‖`.  The following
helper theorem records that the constructed norm is definitionally the
thesis's square-root formula.
-/
noncomputable def inducedNormOfInnerProduct
    (V : Type u) [AddCommGroup V] [Module ℝ V]
    (core : RealInnerProductSpace V) :
    { inducedNorm : Norm V //
      @NormedSpace.Core ℝ V _ _ _ inducedNorm } := by
  letI : InnerProductSpace.Core ℝ V := core
  letI : Norm V := InnerProductSpace.Core.toNorm (𝕜 := ℝ)
  have mathlibCore : NormedSpace.Core ℝ V := InnerProductSpace.Core.toNormedSpaceCore core
  refine ⟨InnerProductSpace.Core.toNorm (𝕜 := ℝ),
    { norm_nonneg := mathlibCore.norm_nonneg
      norm_eq_zero_iff := mathlibCore.norm_eq_zero_iff
      norm_smul := mathlibCore.norm_smul
      norm_triangle := ?_ }⟩
  intro x y
  have hcs : core.inner x y ≤ ‖x‖ * ‖y‖ :=
    (RCLike.re_le_norm (core.inner x y)).trans
      (InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℝ) x y)
  have hxx : core.inner x x = ‖x‖ * ‖x‖ :=
    InnerProductSpace.Core.inner_self_eq_norm_mul_norm (𝕜 := ℝ) x
  have hyy : core.inner y y = ‖y‖ * ‖y‖ :=
    InnerProductSpace.Core.inner_self_eq_norm_mul_norm (𝕜 := ℝ) y
  have hxy : core.inner (x + y) (x + y) = ‖x + y‖ * ‖x + y‖ :=
    InnerProductSpace.Core.inner_self_eq_norm_mul_norm (𝕜 := ℝ) (x + y)
  have hsymm : core.inner y x = core.inner x y := core.conj_inner_symm x y
  have hexpand : core.inner (x + y) (x + y) =
      core.inner x x + core.inner x y + core.inner y x + core.inner y y :=
    InnerProductSpace.Core.inner_add_add_self (𝕜 := ℝ) x y
  have hsq : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
    rw [← hxy, hexpand, hxx, hyy, hsymm]
    nlinarith [hcs]
  exact nonneg_le_nonneg_of_sq_le_sq
    (add_nonneg (mathlibCore.norm_nonneg x) (mathlibCore.norm_nonneg y)) hsq

theorem inducedNormOfInnerProduct_apply
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (core : RealInnerProductSpace V) (v : V) :
    @norm V (inducedNormOfInnerProduct V core).1 v =
      Real.sqrt (core.inner v v) :=
  rfl

/--
Original label: `prop:metric-induced-by-norm`.

Informal statement: for a normed space `(V, ‖·‖)`, the formula
`d(u, v) = ‖u - v‖` defines a metric on `V`.

Lean strategy / thesis relation note: the input is a bare real vector space
with a norm function and the norm axioms of `defn:norm` (`NormedSpace.Core`:
nonnegativity, definiteness, real homogeneity, triangle inequality), with no
pre-existing distance, uniformity or topology.  The metric space is built from
the thesis's three verifications: `d(u,v) = ‖u − v‖ = 0 ↔ u − v = 0 ↔ u = v`
by definiteness; symmetry from `‖u − v‖ = ‖(−1)•(v − u)‖ = |−1| ‖v − u‖` by
homogeneity; and the triangle inequality from
`‖u − v‖ = ‖(u − w) + (w − v)‖ ≤ ‖u − w‖ + ‖w − v‖`.  The companion lemma
`metricSpaceOfNorm_dist` records that the constructed distance is
definitionally the displayed formula.
-/
@[implicit_reducible]
noncomputable def metricSpaceOfNorm
    (V : Type u) [AddCommGroup V] [Module ℝ V] [Norm V]
    (core : NormedSpace.Core ℝ V) : MetricSpace V where
  dist u v := ‖u - v‖
  dist_self u := by
    show ‖u - u‖ = 0
    rw [sub_self]
    exact (core.norm_eq_zero_iff 0).mpr rfl
  dist_comm u v := by
    show ‖u - v‖ = ‖v - u‖
    have h : u - v = (-1 : ℝ) • (v - u) := by rw [neg_one_smul, neg_sub]
    rw [h, core.norm_smul, norm_neg, norm_one, one_mul]
  dist_triangle u v w := by
    show ‖u - w‖ ≤ ‖u - v‖ + ‖v - w‖
    rw [← sub_add_sub_cancel u v w]
    exact core.norm_triangle _ _
  eq_of_dist_eq_zero := by
    intro u v h
    have h' : ‖u - v‖ = 0 := h
    exact sub_eq_zero.mp ((core.norm_eq_zero_iff (u - v)).mp h')

theorem metricSpaceOfNorm_dist
    {V : Type u} [AddCommGroup V] [Module ℝ V] [Norm V]
    (core : NormedSpace.Core ℝ V) (u v : V) :
    letI := metricSpaceOfNorm V core
    dist u v = ‖u - v‖ :=
  rfl

/--
Bundled-instance corollary of `prop:metric-induced-by-norm` (not the mapped
proof, which is `metricSpaceOfNorm`): on a Mathlib `NormedAddCommGroup` the
pre-installed distance is the thesis formula `d(u, v) = ‖u - v‖`
(`dist_eq_norm`), so downstream uses of the formula on bundled types remain
valid.
-/
theorem dist_eq_norm_sub
    {V : Type u} [NormedAddCommGroup V] (u v : V) :
    dist u v = ‖u - v‖ :=
  dist_eq_norm u v

/--
Original label: `cor:metric-induced-by-inner-product`.

Informal statement: in a real inner-product space,
`d(u, v) = sqrt ⟪u - v, u - v⟫` defines a metric on `V`.

Lean strategy / thesis relation note: exactly the thesis's two-step
composition.  `inducedNormOfInnerProduct` (`prop:norm-induced-by-inner-product`)
turns the inner product into the norm `‖v‖ = sqrt ⟪v, v⟫` together with its
norm axioms, and `metricSpaceOfNorm` (`prop:metric-induced-by-norm`) turns that
norm into the metric `d(u, v) = ‖u - v‖`.  The companion lemma
`metricSpaceOfInnerProduct_dist` records that the resulting distance is
definitionally the displayed square-root formula.
-/
@[implicit_reducible]
noncomputable def metricSpaceOfInnerProduct
    (V : Type u) [AddCommGroup V] [Module ℝ V]
    (core : RealInnerProductSpace V) : MetricSpace V :=
  letI : Norm V := (inducedNormOfInnerProduct V core).1
  metricSpaceOfNorm V (inducedNormOfInnerProduct V core).2

theorem metricSpaceOfInnerProduct_dist
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (core : RealInnerProductSpace V) (u v : V) :
    letI := metricSpaceOfInnerProduct V core
    dist u v = Real.sqrt (core.inner (u - v) (u - v)) :=
  rfl

/--
Bundled-instance corollary of `cor:metric-induced-by-inner-product` (not the
mapped proof, which is `metricSpaceOfInnerProduct`): on a Mathlib real
inner-product space, rewrite the bundled metric using `dist_eq_norm`, then the
norm using `norm_eq_sqrt_real_inner`.
-/
theorem dist_eq_sqrt_inner_sub
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v : V) :
    dist u v = Real.sqrt (⟪u - v, u - v⟫) := by
  rw [dist_eq_norm, norm_eq_sqrt_real_inner]

/--
Original label: `defn:banach-hilbert-separable`.

Informal statement: a normed space is Banach when its induced metric is
complete, an inner-product space is Hilbert when that same metric is complete,
and either kind of space is separable when its induced metric is separable.

Lean strategy / thesis relation note: use a normed type `B` for the Banach
clause and an inner-product type `H` for the Hilbert clause, so the words cannot
be applied to a bare pseudometric space.  Their completeness predicates are
both Mathlib's `CompleteSpace` after the appropriate induced metric has been
fixed.  The final pair records separability for each of the two ambient
structures.
-/
def banachHilbertSeparablePredicates
    (B : Type u) (H : Type v)
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    Prop × Prop × (Prop × Prop) :=
  (CompleteSpace B, CompleteSpace H,
    (TopologicalSpace.SeparableSpace B, TopologicalSpace.SeparableSpace H))

/--
Original label: `defn:bounded-linear-operator`.

Informal statement: a bounded linear operator from real normed space `V` to
real normed space `W` is a linear map `T` for which some nonnegative constant
`C` satisfies `‖T v‖ ≤ C ‖v‖` for every `v`; the collection is denoted
`𝓛(V, W)`.

Lean strategy / thesis relation note: Mathlib's `ContinuousLinearMap`, written
`V →L[ℝ] W`, bundles a real linear map with continuity and exposes the thesis
bound through `ContinuousLinearMap.bound`.  The later mapped proposition
`prop:bounded-iff-continuous` verifies that this is equivalent to the thesis's
boundedness formulation.
-/
abbrev BoundedLinearOperator
    (V : Type u) (W : Type v)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] :=
  V →L[ℝ] W

/--
Original label: `defn:operator-norm`.

Informal statement: the operator norm of a bounded linear operator `T` is the
supremum of `‖T v‖` over `‖v‖ ≤ 1`; on a nonzero domain it is equivalently the
supremum over `‖v‖ = 1`.

Lean strategy / thesis relation note: the norm on `V →L[ℝ] W` is Mathlib's
operator norm.  The two conjuncts invoke its closed-unit-ball and unit-sphere
supremum theorems.  Mathlib's sphere formula also covers the zero space by its
`sSup ∅ = 0` convention, so it slightly strengthens the thesis's second clause,
which assumes `V ≠ {0}`.
-/
theorem operatorNorm_eq_sSup
    {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) :
    ‖T‖ = sSup ((fun v : V => ‖T v‖) '' Metric.closedBall 0 1) ∧
      ‖T‖ = sSup ((fun v : V => ‖T v‖) '' Metric.sphere 0 1) :=
  ⟨T.sSup_unitClosedBall_eq_norm.symm, T.sSup_sphere_eq_norm.symm⟩

/--
Original label: `prop:bounded-iff-continuous`.

Informal statement: a real linear map between normed spaces admits a global
bound `‖T v‖ ≤ C ‖v‖` if and only if its underlying function is continuous.

Lean strategy / thesis relation note: `IsBoundedLinearMap ℝ T` is Mathlib's
predicate consisting of linearity together with such a norm bound.  The
forward implication uses its `continuous` theorem.  Conversely, the linearity
already bundled in `T : V →ₗ[ℝ] W`, together with continuity, is converted by
`isLinearMap_and_continuous_iff_isBoundedLinearMap`.
-/
theorem linearMap_bounded_iff_continuous
    {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →ₗ[ℝ] W) :
    IsBoundedLinearMap ℝ T ↔ Continuous T := by
  constructor
  · exact fun hT => hT.continuous
  · intro hT
    exact
      (IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap T).mp
        ⟨T.isLinear, hT⟩

/--
Original label: `defn:dual-space`.

Informal statement: the continuous dual `V*` of a real normed space `V` is the
real vector space `𝓛(V, ℝ)` of bounded linear functionals from `V` to `ℝ`.

Lean strategy / thesis relation note: specialise the continuous-linear-map
type used for bounded operators to codomain `ℝ`.  Mathlib supplies its real
vector-space operations pointwise and its operator norm automatically.
-/
abbrev DualSpace
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  V →L[ℝ] ℝ

/--
Original label: `thm:riesz-representation`.

Informal statement: for every continuous real linear functional `φ` on a real
Hilbert space `H`, there is a unique vector `hφ` such that
`φ u = ⟪u, hφ⟫` for every `u`, and the operator norm of `φ` equals `‖hφ‖`.

Lean strategy / thesis relation note: Mathlib's Fréchet--Riesz theorem is the
surjective linear isometry `InnerProductSpace.toDual ℝ H`.  Take its inverse
at `φ`, use real-inner-product symmetry to match the thesis's argument order,
use injectivity for uniqueness, and use the inverse isometry's `norm_map` for
the norm identity.  This is entirely Mathlib-verified; no external assumption is
introduced.
-/
theorem rieszRepresentation
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (φ : DualSpace H) :
    ∃! hφ : H, (∀ u : H, φ u = ⟪u, hφ⟫) ∧ ‖φ‖ = ‖hφ‖ := by
  let hφ : H := (InnerProductSpace.toDual ℝ H).symm φ
  have hφ_apply (u : H) : φ u = ⟪u, hφ⟫ := by
    calc
      φ u = ⟪hφ, u⟫ :=
        (InnerProductSpace.toDual_symm_apply (x := u) (y := φ)).symm
      _ = ⟪u, hφ⟫ := (real_inner_comm hφ u).symm
  refine ⟨hφ, ⟨hφ_apply, ?_⟩, ?_⟩
  · exact ((InnerProductSpace.toDual ℝ H).symm.norm_map φ).symm
  · intro h hh
    apply (InnerProductSpace.toDual ℝ H).injective
    apply ContinuousLinearMap.ext
    intro u
    calc
      InnerProductSpace.toDual ℝ H h u = ⟪h, u⟫ := rfl
      _ = ⟪u, h⟫ := (real_inner_comm h u).symm
      _ = φ u := (hh.1 u).symm
      _ = ⟪u, hφ⟫ := hφ_apply u
      _ = ⟪hφ, u⟫ := (real_inner_comm u hφ).symm
      _ = InnerProductSpace.toDual ℝ H hφ u := rfl

end FunctionalAnalysis
end Preliminary
end Foundations
end Thesis
