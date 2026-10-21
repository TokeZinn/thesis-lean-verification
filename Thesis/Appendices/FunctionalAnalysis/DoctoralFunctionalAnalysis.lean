import Thesis.Appendices.FunctionalAnalysis.FunctionalAnalysis
import Thesis.Appendices.Analysis.DoctoralAnalysis
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Additional functional-analysis clauses in the doctoral manuscript -/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace

namespace Thesis.Foundations.Preliminary.DoctoralFunctionalAnalysis

universe u v

/-- Original label: `prop:finite-products`.
The finite product has the sum inner product, hence the L² product norm.
The ordinary function-space type has the maximum norm instead. -/
abbrev HilbertProduct {I : Type u} (H : I → Type v) := PiLp 2 H

/-- Original label: `prop:finite-products`. -/
theorem hilbertProduct_inner {I : Type u} [Fintype I] {H : I → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    (x y : HilbertProduct H) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ := rfl

/-- Original label: `prop:finite-products`.
The manuscript's comparison between the `ℓ²` product norm and the maximum norm
of `prop:finite-metric-products`: `max_i ‖v_i‖ ≤ ‖v‖ ≤ |I|^{1/2} max_i ‖v_i‖`.
The maximum norm is Mathlib's supremum norm on the plain product `∀ i, H i`
(`Pi.norm_def`), reached through `WithLp.ofLp`. -/
theorem hilbertProduct_norm_comparison {I : Type u} [Fintype I] {H : I → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    (v : HilbertProduct H) :
    ‖WithLp.ofLp v‖ ≤ ‖v‖ ∧ ‖v‖ ≤ Real.sqrt (Fintype.card I) * ‖WithLp.ofLp v‖ := by
  constructor
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i => PiLp.norm_apply_le v i
  · rw [PiLp.norm_eq_of_L2]
    calc Real.sqrt (∑ i, ‖v i‖ ^ 2)
        ≤ Real.sqrt (∑ _i : I, ‖WithLp.ofLp v‖ ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (WithLp.ofLp v) i) 2)
      _ = Real.sqrt (Fintype.card I) * ‖WithLp.ofLp v‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Original label: `prop:finite-products`.
Completeness from `prop:finite-metric-products` through the norm comparison:
the lower bound makes `WithLp.ofLp` `1`-Lipschitz, so a Cauchy sequence of the
`ℓ²` product is Cauchy for the maximum metric and converges coordinatewise by
`DoctoralAnalysis.finite_maximum_complete`; the upper bound makes
`WithLp.toLp` `|I|^{1/2}`-Lipschitz, so that limit is also the `ℓ²` limit.
This includes the empty index type. -/
theorem hilbertProduct_complete {I : Type u} [Finite I] {H : I → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] : CompleteSpace (HilbertProduct H) := by
  letI := Fintype.ofFinite I
  haveI : CompleteSpace ((i : I) → H i) := DoctoralAnalysis.finite_maximum_complete H
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hcauchy : CauchySeq fun n => WithLp.ofLp (u n) :=
    (PiLp.lipschitzWith_ofLp 2 H).uniformContinuous.comp_cauchySeq hu
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨WithLp.toLp 2 x, ?_⟩
  have h := ((PiLp.lipschitzWith_toLp 2 H).continuous.tendsto x).comp hx
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using h

/-- Original label: `prop:finite-products`.
Separability from `prop:finite-metric-products` through the norm comparison:
`WithLp.toLp` is continuous (upper bound) and surjective, so the countable dense
subset of the maximum-metric product given by
`DoctoralAnalysis.finite_maximum_separable` maps onto a countable dense subset
of the `ℓ²` product. -/
theorem hilbertProduct_separable {I : Type u} [Finite I] {H : I → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, TopologicalSpace.SeparableSpace (H i)] :
    TopologicalSpace.SeparableSpace (HilbertProduct H) := by
  letI := Fintype.ofFinite I
  haveI : TopologicalSpace.SeparableSpace ((i : I) → H i) :=
    DoctoralAnalysis.finite_maximum_separable H
  exact (WithLp.toLp_surjective 2).denseRange.separableSpace
    (PiLp.lipschitzWith_toLp 2 H).continuous

/-- Original label: `defn:adjoint-compact-operators`. -/
abbrev adjoint {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) := ContinuousLinearMap.adjoint T

/-- Original label: `defn:adjoint-compact-operators`. -/
theorem adjoint_identity {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (T : H →L[ℝ] H) (u v : H) :
    ⟪T u, v⟫ = ⟪u, adjoint T v⟫ :=
  (ContinuousLinearMap.adjoint_inner_right T u v).symm

/-- Original label: `defn:adjoint-compact-operators`. -/
def IsSelfAdjoint {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) : Prop := adjoint T = T

/-- Original label: `defn:adjoint-compact-operators`. -/
def HasFiniteRank {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) : Prop := FiniteDimensional ℝ (LinearMap.range T.toLinearMap)

/-- Original label: `defn:adjoint-compact-operators`. -/
def IsCompact {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) : Prop :=
  _root_.IsCompact (closure (T '' Metric.closedBall (0 : H) 1))

/-- Original label: `lem:squared-loss-gradient`.
The manuscript's expansion of the increment:
`𝔣(ŷ+h) − 𝔣(ŷ) − 2⟨ŷ−y,h⟩ = ‖y − ŷ − h‖² − ‖y − ŷ‖² − 2⟨ŷ−y,h⟩ = ‖h‖²`,
before taking any limit. -/
theorem squared_loss_remainder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y p h : H) :
    ‖y - (p + h)‖ ^ 2 - ‖y - p‖ ^ 2 -
      (2 • innerSL ℝ (p - y)) h = ‖h‖ ^ 2 := by
  have he : y - (p + h) = -((p - y) + h) := by abel
  rw [he, norm_neg, norm_add_sq_real, norm_sub_rev y p]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  ring

/-- Original label: `lem:squared-loss-gradient`.
The manuscript's Cauchy--Schwarz bound `|Ah| ≤ 2‖ŷ−y‖‖h‖` for the candidate
derivative `Ah = 2⟨ŷ−y,h⟩`, which shows that `A` is bounded. -/
theorem squared_loss_linear_bound {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y p h : H) :
    |(2 • innerSL ℝ (p - y)) h| ≤ 2 * ‖p - y‖ * ‖h‖ := by
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  rw [two_smul, ← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [abs_real_inner_le_norm (p - y) h]

/-- Original label: `lem:squared-loss-gradient`.
The manuscript's normalised remainder `|𝔣(ŷ+h) − 𝔣(ŷ) − Ah| / ‖h‖ = ‖h‖`
(including the harmless totalised value `0` at `h = 0`). -/
theorem squared_loss_remainder_ratio {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y p h : H) :
    |‖y - (p + h)‖ ^ 2 - ‖y - p‖ ^ 2 - (2 • innerSL ℝ (p - y)) h| / ‖h‖ = ‖h‖ := by
  rw [squared_loss_remainder, abs_of_nonneg (sq_nonneg _)]
  by_cases hh : ‖h‖ = 0
  · simp [hh]
  · field_simp

/-- Original label: `lem:squared-loss-gradient`.
The normalised remainder `‖h‖` tends to `0` as `h → 0`. -/
theorem squared_loss_remainder_ratio_tendsto {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y p : H) :
    Tendsto (fun h =>
      |‖y - (p + h)‖ ^ 2 - ‖y - p‖ ^ 2 - (2 • innerSL ℝ (p - y)) h| / ‖h‖)
      (𝓝 (0 : H)) (𝓝 0) := by
  simpa only [squared_loss_remainder_ratio, norm_zero] using continuous_norm.tendsto (0 : H)

/-- Original label: `lem:squared-loss-gradient`.
The manuscript's direct verification of the Fréchet-derivative definition: by
`squared_loss_remainder` the increment minus the bounded linear candidate
`Ah = 2⟨ŷ−y,h⟩` (`squared_loss_linear_bound`) is exactly `‖h‖²`, so the
normalised remainder `‖h‖⁻¹ · ‖h‖² = ‖h‖` tends to `0` as `h → 0`.  No chain
rule for `‖·‖²` is used, and no completeness is needed. -/
theorem squared_loss_hasFDerivAt {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y prediction : H) :
    HasFDerivAt (fun z : H => ‖y - z‖ ^ 2)
      (2 • innerSL ℝ (prediction - y)) prediction := by
  rw [hasFDerivAt_iff_tendsto]
  have hlim : Tendsto (fun z : H => ‖z - prediction‖) (𝓝 prediction) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp tendsto_id
  refine hlim.congr fun z => ?_
  change ‖z - prediction‖ = ‖z - prediction‖⁻¹ *
    ‖‖y - z‖ ^ 2 - ‖y - prediction‖ ^ 2 - (2 • innerSL ℝ (prediction - y)) (z - prediction)‖
  have he := squared_loss_remainder y prediction (z - prediction)
  simp only [add_sub_cancel] at he
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hz : ‖z - prediction‖ = 0
  · rw [hz]
    simp
  · rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

/-- Original label: `lem:squared-loss-gradient`.
The derivative is represented by the claimed gradient. -/
theorem squared_loss_gradient {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y prediction h : H) :
    (2 • innerSL ℝ (prediction - y)) h = ⟪(2 : ℝ) • (prediction - y), h⟫ := by
  simp [inner_smul_left, inner_sub_left]

/-- Original label: `defn:frechet-derivative`.
The bounded linear first-order approximation in the current source. -/
abbrev HasFrechetDerivative {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (f : H → G) (A : H →L[ℝ] G) (x : H) : Prop := HasFDerivAt f A x

/-- Original label: `defn:frechet-derivative`. -/
def frechetDerivative {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (f : H → G) (x : H) : H →L[ℝ] G :=
  fderiv ℝ f x

/-- Original label: `defn:frechet-derivative`.
Every existing approximation agrees with the named derivative, making the
operator-valued derivative function well-defined on differentiable inputs. -/
theorem frechetDerivative_eq {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {f : H → G} {A : H →L[ℝ] G} {x : H} (hA : HasFrechetDerivative f A x) :
    frechetDerivative f x = A := hA.fderiv

end Thesis.Foundations.Preliminary.DoctoralFunctionalAnalysis
