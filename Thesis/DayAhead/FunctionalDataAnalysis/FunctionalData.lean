import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Convex.Mul

/-!
# Day-ahead functional data analysis

Formal content for
`2 - day-ahead/3_functional_data_analysis.tex`.

The manuscript works with real separable Hilbert spaces.  Mathlib's
`HilbertBasis` is the exact infinite-dimensional basis object needed here: it
identifies the Hilbert space isometrically with an `ℓ²` space and supplies the
convergent coordinate expansion.
-/

namespace Thesis
namespace DayAhead
namespace FunctionalData

open Filter MeasureTheory
open symmDiff
open scoped ENNReal NNReal Topology BigOperators Matrix

universe u v

variable {ι : Type*}

/-! ## Expectation, rank-one operators, and covariance -/

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Definition `defn:expected-hilbert`.

Original label: `defn:expected-hilbert`.

Informal statement: the expectation of an integrable Hilbert-valued random
variable is its Bochner integral.

Lean strategy / thesis relation note: the Bochner integral is defined for every
function in mathlib and takes the expected value under the thesis' integrability
hypothesis.
-/
noncomputable def hilbertExpectation
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure Ω) (X : Ω → H) : H :=
  ∫ ω, X ω ∂μ

/-- The Bochner expectation has the expected scalar coordinates. -/
theorem inner_hilbertExpectation
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {μ : Measure Ω} {X : Ω → H} (hX : Integrable X μ) (u : H) :
    inner ℝ u (hilbertExpectation μ X) = ∫ ω, inner ℝ u (X ω) ∂μ := by
  exact (integral_inner hX u).symm

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Definition `defn:tensor-product`.

Original label: `defn:tensor-product`.

Informal statement: `(u ⊗ v)(w) = ⟪u,w⟫ v`.

Lean strategy / thesis relation note: mathlib's `rankOne ℝ x y` acts as
`z ↦ ⟪y,z⟫ x`, so the arguments appear in the reverse order from the thesis'
notation.
-/
noncomputable def tensorProduct
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) : H →L[ℝ] H :=
  InnerProductSpace.rankOne ℝ v u

@[simp]
theorem tensorProduct_apply
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v w : H) :
    tensorProduct u v w = inner ℝ u w • v := by
  simp [tensorProduct]

@[simp]
theorem norm_tensorProduct
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) :
    ‖tensorProduct u v‖ = ‖u‖ * ‖v‖ := by
  simp [tensorProduct, mul_comm]

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Definition `defn:covariance-operator`.

Original label: `defn:covariance-operator`.

Informal statement: the covariance operator is the Bochner expectation of
the rank-one operator formed from the centred random element.
-/
noncomputable def covarianceOperator
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : Ω → H) : H →L[ℝ] H :=
  let μX := hilbertExpectation μ X
  ∫ ω, tensorProduct (X ω - μX) (X ω - μX) ∂μ

/-! ## Scores and basis reconstruction -/

/-- The scalar score of `x` along the `n`th Hilbert-basis vector. -/
noncomputable def score {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (n : ι) (x : H) : ℝ :=
  inner ℝ (b n) x

@[simp]
theorem score_eq_repr
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (n : ι) (x : H) :
    score b n x = b.repr x n := by
  rw [score, b.repr_apply_apply]

/-- Every vector is the convergent sum of its score-weighted basis vectors. -/
theorem hasSum_score_smul_basis
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (x : H) :
    HasSum (fun n => score b n x • b n) x := by
  simpa only [score_eq_repr] using b.hasSum_repr x

/-- The full score sequence determines the Hilbert-space element. -/
theorem eq_of_scores_eq
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) {x y : H}
    (h : ∀ n, score b n x = score b n y) : x = y := by
  apply b.repr.injective
  apply lp.ext
  funext n
  simpa only [← score_eq_repr] using h n

/-! ## The sigma-algebra generated by all scores -/

/-- The measurable space on `H` generated by all scalar score maps. -/
@[reducible] noncomputable def scoreMeasurableSpace
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) : MeasurableSpace H :=
  ⨆ n, (inferInstance : MeasurableSpace ℝ).comap (score b n)

/-- A type copy used to distinguish the score-generated measurable structure
on the source from the Borel measurable structure on the target. -/
def ScoreDomain
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (_b : HilbertBasis ℕ ℝ H) := H

noncomputable instance scoreDomainMeasurableSpace
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) : MeasurableSpace (ScoreDomain b) :=
  @scoreMeasurableSpace H _ _ b

/-- Forget the score-generated source structure. -/
def ScoreDomain.toH
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {b : HilbertBasis ℕ ℝ H} (x : ScoreDomain b) : H := x

theorem scoreDomain_score_measurable
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    Measurable (fun x : ScoreDomain b => score b n x.toH) := by
  rw [measurable_iff_comap_le]
  change (inferInstance : MeasurableSpace ℝ).comap (score b n) ≤ scoreMeasurableSpace b
  exact le_iSup (fun k => (inferInstance : MeasurableSpace ℝ).comap (score b k)) n

noncomputable def scorePartialSum
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (x : ScoreDomain b) : H :=
  ∑ n ∈ Finset.range N, score b n x.toH • b n

theorem scorePartialSum_measurable
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) :
    Measurable (scorePartialSum b N) := by
  apply Finset.measurable_sum
  intro n hn
  exact (scoreDomain_score_measurable b n).smul_const (b n)

theorem scorePartialSum_tendsto
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (x : ScoreDomain b) :
    Tendsto (fun N => scorePartialSum b N x) atTop (𝓝 x.toH) := by
  exact (hasSum_score_smul_basis b x.toH).tendsto_sum_nat

/-- Alternative (vector-reconstruction) route to `σ(X) ⊆ G_∞`: the identity is the
pointwise limit of the measurable finite partial sums.  Not used by the mapped proof
of `thm:scores-sigma-algebra`, which goes through `scoreDomain_toH_measurable_from_balls`. -/
theorem scoreDomain_toH_measurable
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (b : HilbertBasis ℕ ℝ H) :
    Measurable (@ScoreDomain.toH H _ _ b) := by
  apply measurable_of_tendsto_metrizable (fun N => scorePartialSum_measurable b N)
  exact tendsto_pi_nhds.2 fun x => scorePartialSum_tendsto b x

/-! ### The thesis route to `σ(X) ⊆ G_∞`: Parseval, balls, and a countable base -/

/-- Parseval's identity applied to `x - c`, as in the thesis:
`‖x - c‖² = ∑ₙ (θₙ(x) - θₙ(c))²` with `θₙ(c) = ⟪c, eₙ⟫`. -/
theorem squaredDistance_hasSum
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (x c : H) :
    HasSum (fun n => (score b n x - score b n c) ^ 2) (‖x - c‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner (x - c) (x - c)
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  ext n
  simp only [score, inner_sub_right, inner_sub_left, real_inner_comm, pow_two]

/-- The squared distance to a fixed centre is measurable for the score-generated
sigma-algebra: each finite Parseval sum `S_N = ∑_{n<N} (θₙ - xₙ)²` is a measurable
function of the first `N` scores, and `S_N → ‖x - c‖²` pointwise. -/
theorem squaredDistance_measurable
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (c : H) :
    Measurable (fun x : ScoreDomain b => ‖x.toH - c‖ ^ 2) := by
  apply measurable_of_tendsto_metrizable
    (f := fun N x => ∑ n ∈ Finset.range N, (score b n x.toH - score b n c) ^ 2)
  · intro N
    exact Finset.measurable_sum _ fun n _ =>
      ((scoreDomain_score_measurable b n).sub_const _).pow_const 2
  · exact tendsto_pi_nhds.mpr fun x => (squaredDistance_hasSum b x.toH c).tendsto_sum_nat

/-- The preimage of an open ball, `X⁻¹(B_ε(c)) = {‖X - c‖² < ε²}`, is measurable for
the score sigma-algebra; no measurable vector reconstruction is evaluated. -/
theorem ball_preimage_measurable
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (c : H) (ε : ℝ) :
    MeasurableSet ((ScoreDomain.toH (b := b)) ⁻¹' Metric.ball c ε) := by
  by_cases hε : 0 < ε
  · have heq : (ScoreDomain.toH (b := b)) ⁻¹' Metric.ball c ε =
        {x : ScoreDomain b | ‖x.toH - c‖ ^ 2 < ε ^ 2} := by
      ext x
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, Set.mem_setOf_eq]
      exact (sq_lt_sq₀ (norm_nonneg _) hε.le).symm
    rw [heq]
    exact measurableSet_lt (squaredDistance_measurable b c) measurable_const
  · simp [Metric.ball_eq_empty.mpr (le_of_not_gt hε)]

/-- The thesis's countable family `𝒞 = {B_q(d) | d ∈ D, q ∈ ℚ_{>0}}` of balls with
centres in a dense set `D` and positive rational radii is a basis of the norm topology. -/
theorem dense_rational_ball_basis
    {H : Type u} [NormedAddCommGroup H] {D : Set H} (hD : Dense D) :
    TopologicalSpace.IsTopologicalBasis (Set.range (fun z : D × {r : ℚ // 0 < r} =>
      Metric.ball (z.1 : H) (z.2 : ℝ))) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨z, rfl⟩
    exact Metric.isOpen_ball
  · intro x U hx hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn (half_pos hε)
    have hr : 0 < (r : ℝ) := hr0
    obtain ⟨d, hd, hxd⟩ := hD.exists_dist_lt x hr
    refine ⟨Metric.ball d (r : ℝ), ⟨(⟨d, hd⟩, ⟨r, by exact_mod_cast hr⟩), rfl⟩,
      ?_, ?_⟩
    · exact hxd
    · intro y hy
      apply hball
      have htri := dist_triangle y d x
      have hdy : dist y d < (r : ℝ) := hy
      have hdx : dist d x < (r : ℝ) := by simpa only [dist_comm] using hxd
      change dist y x < ε
      linarith

/-- The reverse inclusion `σ(X) ⊆ G_∞` along the thesis route: fix a countable dense
`D ⊆ H`; every ball `B_q(d)` with `d ∈ D`, `q ∈ ℚ_{>0}` has a score-measurable
preimage by the Parseval argument (`ball_preimage_measurable`); these balls form a
countable base, so every open set is a countable union of them and the identity
`ScoreDomain b → H` is measurable for the Borel sigma-algebra.  (The index type
`D × ℚ_{>0}` is countable; mathlib's `IsTopologicalBasis.borel_eq_generateFrom`
performs the countable-union step.) -/
theorem scoreDomain_toH_measurable_from_balls
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [mH : MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (b : HilbertBasis ℕ ℝ H) :
    Measurable (@ScoreDomain.toH H _ _ b) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense H
  letI : Countable D := hDc.to_subtype
  have hC := dense_rational_ball_basis hDd
  rw [measurable_iff_comap_le]
  rw [show mH = borel H from BorelSpace.measurable_eq,
    hC.borel_eq_generateFrom]
  apply MeasurableSpace.comap_le_iff_le_map.mpr
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨z, rfl⟩
  exact ball_preimage_measurable b _ _

/-- The Borel sigma-algebra of a separable Hilbert space is generated by the
countable family of basis scores.  `G_∞ ⊆ σ(X)` because each score is a continuous
linear functional of `X`; `σ(X) ⊆ G_∞` by the Parseval/ball/countable-base argument
of `scoreDomain_toH_measurable_from_balls`. -/
theorem scoreMeasurableSpace_eq_borel
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (b : HilbertBasis ℕ ℝ H) :
    scoreMeasurableSpace b = (inferInstance : MeasurableSpace H) := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    change (inferInstance : MeasurableSpace ℝ).comap (score b n) ≤
      (inferInstance : MeasurableSpace H)
    have hc : Measurable[borel H, borel ℝ] (score b n) := (by
      unfold score
      fun_prop : Continuous (score b n)).borel_measurable
    have hm : Measurable (score b n) := by
      have hH : (inferInstance : MeasurableSpace H) = borel H :=
        BorelSpace.measurable_eq
      have hR : (inferInstance : MeasurableSpace ℝ) = borel ℝ :=
        BorelSpace.measurable_eq
      rw [← hH, ← hR] at hc
      exact hc
    exact measurable_iff_comap_le.mp hm
  · have h := scoreDomain_toH_measurable_from_balls b
    rw [measurable_iff_comap_le] at h
    change MeasurableSpace.comap (fun x : H => x)
      (inferInstance : MeasurableSpace H) ≤ scoreMeasurableSpace b at h
    simpa only [show (fun x : H => x) = id from rfl, MeasurableSpace.comap_id] using h

/-- Pulling the score-generated sigma-algebra back along a random element is
the same as pulling back its Borel sigma-algebra. -/
theorem comap_borel_eq_iSup_comap_scores
    {Ω : Type u} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) :
    (borel H).comap X =
      ⨆ n, (inferInstance : MeasurableSpace ℝ).comap
        (fun ω => score b n (X ω)) := by
  rw [← BorelSpace.measurable_eq]
  calc
    (inferInstance : MeasurableSpace H).comap X =
        (scoreMeasurableSpace b).comap X :=
      congrArg (fun m : MeasurableSpace H => m.comap X)
        (scoreMeasurableSpace_eq_borel b).symm
    _ = ⨆ n, (inferInstance : MeasurableSpace ℝ).comap
        (fun ω => score b n (X ω)) := by
      rw [scoreMeasurableSpace, MeasurableSpace.comap_iSup]
      congr 1
      funext n
      rw [MeasurableSpace.comap_comp]
      rfl

/-! ## The finite-score filtration -/

/-- The sigma-algebra generated by the first `N` scores of `X`. With Lean's
zero-based indexing, level `N` contains scores `0, ..., N - 1`. -/
noncomputable def scoreFiltration
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq N := ⨆ n : Fin N, (inferInstance : MeasurableSpace ℝ).comap
    (fun ω => score b n (X ω))
  mono' := by
    intro N M hNM
    refine iSup_le fun n => ?_
    exact le_iSup_of_le
      (⟨n, lt_of_lt_of_le n.isLt hNM⟩ : Fin M) le_rfl
  le' := by
    intro N
    refine iSup_le fun n => ?_
    rw [← measurable_iff_comap_le]
    exact (by
      fun_prop : Continuous (fun x : H => inner ℝ (b n) x)).measurable.comp hX

/-- The union of the finite-score filtration is the sigma-algebra generated by
the Hilbert-valued random element itself. -/
theorem iSup_scoreFiltration_eq_comap_borel
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X) :
    (⨆ N, scoreFiltration b X hX N) = (borel H).comap X := by
  rw [comap_borel_eq_iSup_comap_scores b X]
  apply le_antisymm
  · refine iSup_le fun N => iSup_le fun n => ?_
    exact le_iSup
      (fun k => (inferInstance : MeasurableSpace ℝ).comap
        (fun ω => score b k (X ω))) n
  · refine iSup_le fun n => ?_
    exact le_iSup_of_le (n + 1) <| le_iSup_of_le
      (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) le_rfl

/--
Thesis source: `2 - day-ahead/3_functional_data_analysis.tex`, first clause of
Theorem `thm:scores-sigma-algebra`.

Original label: `thm:scores-sigma-algebra`.

The manuscript states equality only up to null sets. In a separable Hilbert
space, the Borel sigma-algebra itself is generated by the countable score maps,
so Lean proves exact equality before a measure is chosen.

Lean strategy / thesis relation note: the inclusion `G_∞ ⊆ σ(X)` is the
continuity of each score functional; the inclusion `σ(X) ⊆ G_∞` follows the
thesis proof (Parseval `‖X - x‖² = ∑ (θₙ - xₙ)²` makes every ball preimage
`G_∞`-measurable, and a countable base of rational balls around a countable dense
set passes to all open sets), see `scoreDomain_toH_measurable_from_balls` and
`scoreMeasurableSpace_eq_borel`.  The pull-back along `X` and the identification of
`⨆ N, G_N` with `σ(θₙ, n ∈ ℕ)` are `comap_borel_eq_iSup_comap_scores` and
`iSup_scoreFiltration_eq_comap_borel`.
-/
theorem scores_generate_random_element
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X) :
    (⨆ N, scoreFiltration b X hX N) = (borel H).comap X :=
  iSup_scoreFiltration_eq_comap_borel b X hX

/--
Thesis source: `2 - day-ahead/3_functional_data_analysis.tex`, almost-sure
convergence clause of Theorem `thm:scores-sigma-algebra`.

Original label: `thm:scores-sigma-algebra`.

This is Levy's upward theorem from mathlib after identifying the supremum of
the finite-score filtration.
-/
theorem condExp_scoreFiltration_tendsto_ae
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X)
    (Y : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun N => μ[Y | scoreFiltration b X hX N] ω)
      atTop (𝓝 (μ[Y | (borel H).comap X] ω)) := by
  simpa only [iSup_scoreFiltration_eq_comap_borel b X hX] using
    (MeasureTheory.tendsto_ae_condExp
      (μ := μ) (ℱ := scoreFiltration b X hX) Y)

/--
Thesis source: `2 - day-ahead/3_functional_data_analysis.tex`, `L¹`
convergence clause of Theorem `thm:scores-sigma-algebra`.

Original label: `thm:scores-sigma-algebra`.

Lévy's upward theorem in `L¹` (mathlib's `tendsto_eLpNorm_condExp`) for the
increasing score filtration, after the Parseval identification
`⨆ N, G_N = σ(X)`.  The thesis assumes `Y ∈ L¹`; mathlib's statement holds for
every `Y` because conditional expectation vanishes on non-integrable inputs, so
the hypothesis is recorded but not needed.
-/
theorem condExp_scoreFiltration_tendsto_L1
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X)
    (Y : Ω → ℝ) (_hY : Integrable Y μ) :
    Tendsto (fun N => eLpNorm
      (μ[Y | scoreFiltration b X hX N] - μ[Y | (borel H).comap X]) 1 μ)
      atTop (𝓝 0) := by
  simpa only [iSup_scoreFiltration_eq_comap_borel b X hX] using
    (MeasureTheory.tendsto_eLpNorm_condExp
      (μ := μ) (ℱ := scoreFiltration b X hX) Y)

/--
Alternative route for `thm:scores-sigma-algebra` (not the mapped proof): the
Hilbert projection core.  Conditional expectations onto an increasing filtration
converge in `L²` once the closure of the union of its measurable subspaces is
identified with the target measurable subspace.  The mapped `L²` clause is
`condExp_scoreFiltration_tendsto_eLpNorm_two`, proved by Lévy's upward theorem. -/
theorem condExpL2_tendsto_of_lpMeas_closure
    {Ω : Type u} {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (ℱ : Filtration ℕ m₀) (hm : m ≤ m₀)
    (hclosure :
      (⨆ N, lpMeas ℝ ℝ (ℱ N) 2 μ).topologicalClosure =
        lpMeas ℝ ℝ m 2 μ)
    (f : Ω →₂[μ] ℝ) :
    Tendsto
      (fun N => (condExpL2 ℝ ℝ (ℱ.le' N) f : Ω →₂[μ] ℝ))
      atTop (𝓝 (condExpL2 ℝ ℝ hm f : Ω →₂[μ] ℝ)) := by
  let U : ℕ → Submodule ℝ (Ω →₂[μ] ℝ) :=
    fun N => lpMeas ℝ ℝ (ℱ N) 2 μ
  have hU : Monotone U := by
    intro N M hNM g hg
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hg ⊢
    obtain ⟨g', hg'meas, hgg'⟩ := hg
    exact ⟨g', hg'meas.mono (ℱ.mono' hNM), hgg'⟩
  letI (N : ℕ) : Fact (ℱ N ≤ m₀) := ⟨ℱ.le' N⟩
  have hprojection := Submodule.starProjection_tendsto_closure_iSup U hU f
  simpa only [U, condExpL2, Submodule.starProjection_apply, hclosure] using
    hprojection

/-- For a finite measure, the union of the `L²` subspaces measurable with
respect to an increasing filtration is dense in the subspace measurable with
respect to the supremum sigma-algebra. -/
theorem lpMeas_iSup_filtration_topologicalClosure
    {Ω : Type u} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m₀) :
    (⨆ N, lpMeas ℝ ℝ (ℱ N) 2 μ).topologicalClosure =
      lpMeas ℝ ℝ (⨆ N, ℱ N) 2 μ := by
  let U : Submodule ℝ (Ω →₂[μ] ℝ) := ⨆ N, lpMeas ℝ ℝ (ℱ N) 2 μ
  have hmInf : (⨆ N, ℱ N) ≤ m₀ := by
    exact iSup_le fun N => ℱ.le' N
  have hUle : U ≤ lpMeas ℝ ℝ (⨆ N, ℱ N) 2 μ := by
    refine iSup_le fun N f hf => ?_
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
    exact hf.mono (le_iSup (fun N => ℱ N) N)
  have htargetClosed : IsClosed
      (lpMeas ℝ ℝ (⨆ N, ℱ N) 2 μ : Set (Ω →₂[μ] ℝ)) := by
    simpa [lpMeas] using
      (isClosed_aestronglyMeasurable (F := ℝ) (p := (2 : ℝ≥0∞)) hmInf)
  apply le_antisymm
  · exact U.topologicalClosure_minimal hUle htargetClosed
  · intro f hf
    change f ∈ U.topologicalClosure
    let 𝒜 : Set (Set Ω) := {s | ∃ N, MeasurableSet[ℱ N] s}
    have h𝒜 : MeasureTheory.IsSetAlgebra 𝒜 := by
      refine ⟨?_, ?_, ?_⟩
      · exact ⟨0, @MeasurableSet.empty Ω (ℱ 0)⟩
      · rintro s ⟨N, hs⟩
        exact ⟨N, @MeasurableSet.compl Ω s (ℱ N) hs⟩
      · rintro s t ⟨N, hs⟩ ⟨M, ht⟩
        refine ⟨max N M, ?_⟩
        have hs' : MeasurableSet[ℱ (max N M)] s :=
          (ℱ.mono' (Nat.le_max_left N M)) s hs
        have ht' : MeasurableSet[ℱ (max N M)] t :=
          (ℱ.mono' (Nat.le_max_right N M)) t ht
        exact @MeasurableSet.union Ω (ℱ (max N M)) s t hs' ht'
    have hgen : (⨆ N, ℱ N) = MeasurableSpace.generateFrom 𝒜 := by
      simpa [𝒜] using
        (MeasurableSpace.measurableSpace_iSup_eq (fun N => ℱ N))
    let muInf : @Measure Ω (⨆ N, ℱ N) :=
      @Measure.trim Ω (⨆ N, ℱ N) m₀ μ hmInf
    letI : @IsFiniteMeasure Ω (⨆ N, ℱ N) muInf := by
      dsimp [muInf]
      infer_instance
    have h𝒜dense : @Measure.MeasureDense Ω (⨆ N, ℱ N) muInf 𝒜 := by
      exact @Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        Ω (⨆ N, ℱ N) muInf 𝒜 inferInstance h𝒜 hgen
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hf
    refine Lp.induction_stronglyMeasurable
      (F := ℝ) (p := (2 : ℝ≥0∞)) hmInf (by norm_num)
      (fun g => g ∈ U.topologicalClosure) ?_ ?_ ?_ f hf
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst]
      by_cases hc : c = 0
      · subst c
        have hz :
            indicatorConstLp (μ := μ) 2 (hmInf s hs) hμs.ne (0 : ℝ) = 0 := by
          simp [indicatorConstLp]
        rw [hz]
        exact U.topologicalClosure.zero_mem
      change indicatorConstLp 2 _ _ c ∈ closure (U : Set (Ω →₂[μ] ℝ))
      rw [SeminormedAddCommGroup.mem_closure_iff]
      intro ε hε
      have haux : 0 < (ε / ‖c‖) ^ (2 : ℝ≥0∞).toReal := by
        positivity
      obtain ⟨t, ⟨N, htN⟩, hst⟩ :=
        @Measure.MeasureDense.approx Ω (⨆ N, ℱ N) muInf 𝒜 h𝒜dense
          s hs (measure_ne_top muInf s) _ haux
      have htInf : MeasurableSet[(⨆ N, ℱ N)] t :=
        (le_iSup (fun N => ℱ N) N) t htN
      have hsymm : MeasurableSet[(⨆ N, ℱ N)] (s ∆ t) :=
        @MeasurableSet.symmDiff Ω (⨆ N, ℱ N) s t hs htInf
      change μ.trim hmInf (s ∆ t) < _ at hst
      rw [trim_measurableSet_eq hmInf hsymm] at hst
      let g : Ω →₂[μ] ℝ :=
        indicatorConstLp 2 ((ℱ.le' N) t htN) (measure_ne_top μ t) c
      have hgN : g ∈ lpMeas ℝ ℝ (ℱ N) 2 μ := by
        dsimp [g]
        exact mem_lpMeas_indicatorConstLp (ℱ.le' N) htN (measure_ne_top μ t)
      have hgU : g ∈ U := (le_iSup (fun N => lpMeas ℝ ℝ (ℱ N) 2 μ) N) hgN
      refine ⟨g, hgU, ?_⟩
      dsimp [g]
      rw [← dist_eq_norm]
      rw [dist_indicatorConstLp_eq_norm,
        norm_indicatorConstLp (by norm_num) (by norm_num)]
      calc
        ‖c‖ * μ.real (s ∆ t) ^ (1 / (2 : ℝ≥0∞).toReal)
            < ‖c‖ *
                (ENNReal.ofReal ((ε / ‖c‖) ^ (2 : ℝ≥0∞).toReal)).toReal ^
                  (1 / (2 : ℝ≥0∞).toReal) := by
              have hp : 0 < (2 : ℝ≥0∞).toReal :=
                ENNReal.toReal_pos (by norm_num) (by norm_num)
              rw [measureReal_def]
              gcongr
              exact ENNReal.ofReal_ne_top
        _ = ε := by
          rw [ENNReal.toReal_ofReal (by positivity), one_div,
            Real.rpow_rpow_inv (by positivity)
              (ENNReal.toReal_pos (by norm_num) (by norm_num)).ne',
            mul_div_cancel₀ _ (norm_ne_zero_iff.2 hc)]
    · intro f g _hf _hg _hfm _hgm _hdisj hPf hPg
      exact U.topologicalClosure.add_mem hPf hPg
    · change IsClosed
        ((fun g : lpMeas ℝ ℝ (⨆ N, ℱ N) 2 μ => (g : Ω →₂[μ] ℝ)) ⁻¹'
          (U.topologicalClosure : Set (Ω →₂[μ] ℝ)))
      exact U.isClosed_topologicalClosure.preimage continuous_subtype_val

/--
Alternative route for `thm:scores-sigma-algebra` (not the mapped proof): the
general finite-measure filtration density theorem above applies after
identifying the supremum of the score filtration with the sigma-algebra
generated by the random element.  The mapped `L²` clause is
`condExp_scoreFiltration_tendsto_eLpNorm_two`, proved by Lévy's upward theorem. -/
theorem scoreFiltration_lpMeas_closure
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X) :
    (⨆ N, lpMeas ℝ ℝ (scoreFiltration b X hX N) 2 μ).topologicalClosure =
      lpMeas ℝ ℝ ((borel H).comap X) 2 μ := by
  rw [← iSup_scoreFiltration_eq_comap_borel b X hX]
  exact lpMeas_iSup_filtration_topologicalClosure (scoreFiltration b X hX)

theorem scoreTarget_le
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X) :
    (borel H).comap X ≤ (inferInstance : MeasurableSpace Ω) := by
  rw [← iSup_scoreFiltration_eq_comap_borel b X hX]
  exact iSup_le fun N => (scoreFiltration b X hX).le' N

/-- The `L²` conditional-expectation classes converge in extended distance
once the isolated density statement is supplied. -/
theorem condExpL2_scoreFiltration_tendsto_edist
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    Tendsto
      (fun N => edist
        (condExpL2 ℝ ℝ ((scoreFiltration b X hX).le' N) (hY.toLp Y) :
          Ω →₂[μ] ℝ)
        (condExpL2 ℝ ℝ (scoreTarget_le b X hX)
          (hY.toLp Y) : Ω →₂[μ] ℝ))
      atTop (𝓝 0) := by
  have htarget := scoreTarget_le b X hX
  have hLp := condExpL2_tendsto_of_lpMeas_closure
    (m := (borel H).comap X)
    (scoreFiltration b X hX) htarget
    (scoreFiltration_lpMeas_closure b X hX) (hY.toLp Y)
  have hconst : Tendsto
      (fun _ : ℕ =>
        (condExpL2 ℝ ℝ htarget (hY.toLp Y) : Ω →₂[μ] ℝ))
      atTop (𝓝 (condExpL2 ℝ ℝ htarget (hY.toLp Y) : Ω →₂[μ] ℝ)) :=
    tendsto_const_nhds
  simpa only [edist_self] using hLp.edist hconst

/-! ### Lévy's upward theorem in `L²` -/

/-- The square identity transfers small-set `L¹` bounds for squared functions
into small-set `L²` bounds for the original functions. -/
theorem eLpNorm_square
    {Ω : Type u} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} (f : Ω → ℝ) :
    eLpNorm (fun ω => (f ω) ^ 2) 1 μ = (eLpNorm f 2 μ) ^ 2 := by
  have h := eLpNorm_norm_rpow (μ := μ) (p := 1) (q := 2) f (by norm_num)
  norm_num only [ENNReal.ofReal_ofNat, one_mul, Real.rpow_two,
    ENNReal.rpow_two, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- Conditional Jensen preserves a squared integrable majorant. -/
theorem conditional_square_le
    {Ω : Type u} {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    (fun ω => (μ[Y | m] ω) ^ 2) ≤ᵐ[μ] μ[(fun ω => (Y ω) ^ 2) | m] := by
  have hsquare : Integrable (fun ω => (Y ω) ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hY.norm.integrable_sq
  exact (even_two.convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ hm
    (by fun_prop : Continuous (fun y : ℝ => y ^ 2)).lowerSemicontinuous
    (hY.integrable (by norm_num)) hsquare

/-- The full family of scalar conditional expectations of a square-integrable
variable is uniformly integrable in `L²`. -/
theorem conditional_uniformIntegrable_two
    {Ω : Type u} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} [IsFiniteMeasure μ]
    {ι : Type*} (ℱ : ι → MeasurableSpace Ω) (hℱ : ∀ i, ℱ i ≤ m₀)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    UnifIntegrable (fun i => μ[Y | ℱ i]) 2 μ := by
  have hsquare : Integrable (fun ω => (Y ω) ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hY.norm.integrable_sq
  have hui := hsquare.uniformIntegrable_condExp hℱ
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hui.unifIntegrable (sq_pos_of_pos hε)
  refine ⟨δ, hδ, fun i s hs hμs => ?_⟩
  have hjensen := conditional_square_le (hℱ i) hY
  have hmono : eLpNorm (fun ω => ((s.indicator (μ[Y | ℱ i])) ω) ^ 2) 1 μ ≤
      eLpNorm (s.indicator (μ[(fun ω => (Y ω) ^ 2) | ℱ i])) 1 μ := by
    apply eLpNorm_mono_ae
    filter_upwards [hjensen] with ω hω
    by_cases hωs : ω ∈ s
    · simp only [Set.indicator_of_mem hωs]
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg ((sq_nonneg _).trans hω)]
      exact hω
    · simp [Set.indicator_of_notMem hωs]
  rw [eLpNorm_square] at hmono
  have hsq := hmono.trans (hsmall i s hs hμs)
  rw [ENNReal.ofReal_pow hε.le] at hsq
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
    (by simpa only [ENNReal.rpow_two] using hsq)

/-- Lévy's upward theorem in `L²`, along the martingale-convergence route: the
almost-everywhere Lévy theorem plus the uniform integrability of the conditional
means in `L²` (Vitali). -/
theorem levy_upward_L2
    {Ω : Type u} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m₀) (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    Tendsto (fun N => eLpNorm
      (μ[Y | ℱ N] - μ[Y | ⨆ n, ℱ n]) 2 μ) atTop (𝓝 0) := by
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun N => (stronglyMeasurable_condExp.mono (ℱ.le N)).aestronglyMeasurable)
    hY.condExp (conditional_uniformIntegrable_two ℱ ℱ.le hY)
  exact tendsto_ae_condExp (μ := μ) (ℱ := ℱ) Y

/-- Original label: `thm:scores-sigma-algebra`.
The `L²` convergence clause: `E[Y | G_N] → E[Y | σ(X)]` in `L²` for `Y ∈ L²`, by
Lévy's upward theorem (`levy_upward_L2`: almost-sure convergence plus uniform
integrability) for the increasing score filtration, after the Parseval
identification `⨆ N, G_N = σ(X)`. -/
theorem condExp_scoreFiltration_tendsto_eLpNorm_two
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (b : HilbertBasis ℕ ℝ H) (X : Ω → H) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    Tendsto
      (fun N => eLpNorm
        (μ[Y | scoreFiltration b X hX N] -
          μ[Y | (borel H).comap X]) 2 μ)
      atTop (𝓝 0) := by
  simpa only [iSup_scoreFiltration_eq_comap_borel b X hX] using
    levy_upward_L2 (scoreFiltration b X hX) Y hY

/-! ## Conditional expectations in a Hilbert basis -/

/-- Conditional expectation commutes with each scalar score functional. -/
theorem score_condExp_ae_eq
    {Ω : Type u} {H : Type v} {m m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m₀] Ω) (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (b : HilbertBasis ℕ ℝ H) {X : Ω → H} (hX : Integrable X μ) (n : ℕ) :
    (fun ω => score b n (μ[X | m] ω)) =ᵐ[μ]
      μ[(fun ω => score b n (X ω)) | m] := by
  simpa only [score, Function.comp_apply] using
    (innerSL ℝ (b n)).comp_condExp_comm hX

/-! ### The thesis partial sums `S_N` and conditional dominated convergence -/

/-- The thesis partial sum `S_N(x) = ∑_{n<N} θₙ(x) eₙ`, as the finite orthogonal
projection of `x` onto `span{e₀, …, e_{N-1}}`. -/
noncomputable def scoreProjection
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) : H →L[ℝ] H :=
  ∑ n ∈ Finset.range N, tensorProduct (b n) (b n)

theorem scoreProjection_apply
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (x : H) :
    scoreProjection b N x = ∑ n ∈ Finset.range N, score b n x • b n := by
  simp [scoreProjection, tensorProduct_apply, score]

/-- Bessel's inequality: the projection is a contraction, `‖S_N(x)‖ ≤ ‖x‖`. -/
theorem norm_scoreProjection_le
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (x : H) :
    ‖scoreProjection b N x‖ ≤ ‖x‖ := by
  have hsq : ‖scoreProjection b N x‖ ^ 2 =
      ∑ n ∈ Finset.range N, ‖inner ℝ (b n) x‖ ^ 2 := by
    rw [scoreProjection_apply, ← real_inner_self_eq_norm_sq, b.orthonormal.inner_sum]
    simp [score, Real.norm_eq_abs, pow_two]
  have hbound := b.orthonormal.sum_inner_products_le (s := Finset.range N) x
  nlinarith [norm_nonneg (scoreProjection b N x), norm_nonneg x]

/-- Orthogonality gives the exact squared residual `‖x - S_N(x)‖² = ‖x‖² - ∑_{n<N} θₙ(x)²`,
hence the decreasing error envelope used by conditional dominated convergence. -/
theorem scoreProjection_residual_sq
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (x : H) :
    ‖x - scoreProjection b N x‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ n ∈ Finset.range N, (score b n x) ^ 2 := by
  have hinner : inner ℝ x (scoreProjection b N x) =
      ∑ n ∈ Finset.range N, (score b n x) ^ 2 := by
    rw [scoreProjection_apply]
    simp only [inner_sum, inner_smul_right, score, pow_two, real_inner_comm]
  have hsq : ‖scoreProjection b N x‖ ^ 2 =
      ∑ n ∈ Finset.range N, (score b n x) ^ 2 := by
    rw [scoreProjection_apply, ← real_inner_self_eq_norm_sq, b.orthonormal.inner_sum]
    simp [score, pow_two]
  rw [norm_sub_sq_real, hinner, hsq]
  ring

theorem scoreProjection_residual_antitone
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (x : H) :
    Antitone (fun N => ‖x - scoreProjection b N x‖) := by
  intro N M hNM
  have hsum : (∑ n ∈ Finset.range N, (score b n x) ^ 2) ≤
      ∑ n ∈ Finset.range M, (score b n x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
      (fun _ _ _ => sq_nonneg _)
  have hN := scoreProjection_residual_sq b N x
  have hM := scoreProjection_residual_sq b M x
  nlinarith [norm_nonneg (x - scoreProjection b M x), norm_nonneg (x - scoreProjection b N x)]

/-- Conditional dominated convergence for a nonnegative decreasing envelope, in the
almost-sure form used by the thesis.  Mathlib's `L¹` dominated convergence theorem for
`condExpL1` gives convergence in measure, hence a subsequence converging almost
everywhere; monotonicity of conditional expectation upgrades that subsequence to the
full sequence. -/
theorem conditional_antitone_dominated_zero
    {Ω : Type u} {m m₀ : MeasurableSpace Ω} (μ : Measure[m₀] Ω)
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (r : ℕ → Ω → ℝ) (bound : Ω → ℝ)
    (hrmeas : ∀ n, AEStronglyMeasurable (r n) μ)
    (hbound : Integrable bound μ)
    (hrbound : ∀ n, ∀ᵐ ω ∂μ, ‖r n ω‖ ≤ bound ω)
    (hranti : ∀ᵐ ω ∂μ, Antitone (fun n => r n ω))
    (hrzero : ∀ᵐ ω ∂μ, Tendsto (fun n => r n ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[r n | m] ω) atTop (𝓝 0) := by
  have hrint : ∀ n, Integrable (r n) μ := fun n =>
    hbound.mono' (hrmeas n) (hrbound n)
  have hL1 := tendsto_condExpL1_of_dominated_convergence hm bound
    hrmeas hbound hrbound hrzero
  have hL1zero : Tendsto (fun n => condExpL1 hm μ (r n)) atTop (𝓝 0) := by
    change Tendsto (fun n => condExpL1 hm μ (r n)) atTop
      (𝓝 (condExpL1 hm μ (0 : Ω → ℝ))) at hL1
    rw [condExpL1_zero] at hL1
    exact hL1
  have hmeasure : TendstoInMeasure μ (fun n => μ[r n | m]) atTop (0 : Ω → ℝ) := by
    apply TendstoInMeasure.congr
      (fun n => (condExp_ae_eq_condExpL1 hm (r n)).symm) (Lp.coeFn_zero _ _ _)
    exact tendstoInMeasure_of_tendsto_Lp hL1zero
  obtain ⟨ns, hns, hsub⟩ := hmeasure.exists_seq_tendsto_ae
  have horder : ∀ᵐ ω ∂μ, Antitone (fun n => μ[r n | m] ω) := by
    have hpair : ∀ i j : ℕ, i ≤ j → μ[r j | m] ≤ᵐ[μ] μ[r i | m] := by
      intro i j hij
      exact condExp_mono (hrint j) (hrint i) (hranti.mono fun _ h => h hij)
    have hall : ∀ᵐ ω ∂μ, ∀ i j : ℕ, i ≤ j → μ[r j | m] ω ≤ μ[r i | m] ω := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro j
      by_cases hij : i ≤ j
      · exact (hpair i j hij).mono fun _ h _ => h
      · exact ae_of_all μ fun _ h => (hij h).elim
    exact hall
  filter_upwards [horder, hsub] with ω hanti hlim
  exact (tendsto_iff_tendsto_subseq_of_antitone hanti hns.tendsto_atTop).mpr hlim

/-- The thesis's conditional dominated convergence step: `S_N ∘ X → X` pointwise with
`‖S_N ∘ X‖ ≤ ‖X‖`, and `‖X‖` is integrable, so `E[S_N ∘ X | G] → E[X | G]` almost
surely.  The residual envelope `‖S_N ∘ X - X‖ ≤ 2‖X‖` is decreasing by
`scoreProjection_residual_antitone`. -/
theorem condExp_scoreProjection_tendsto
    {Ω : Type u} {H : Type v} {m m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m₀] Ω) (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (b : HilbertBasis ℕ ℝ H) {X : Ω → H} (hX : Integrable X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => μ[(fun u => scoreProjection b N (X u)) | m] ω)
      atTop (𝓝 (μ[X | m] ω)) := by
  let S (N : ℕ) (ω : Ω) := scoreProjection b N (X ω)
  have hS (N : ℕ) : Integrable (S N) μ := (scoreProjection b N).integrable_comp hX
  have hlim (ω : Ω) : Tendsto (fun N => S N ω) atTop (𝓝 (X ω)) := by
    simpa only [S, scoreProjection_apply] using
      (hasSum_score_smul_basis b (X ω)).tendsto_sum_nat
  let r (N : ℕ) (ω : Ω) := ‖S N ω - X ω‖
  have hbound (N : ℕ) (ω : Ω) : ‖r N ω‖ ≤ 2 * ‖X ω‖ := by
    have hSbound := norm_scoreProjection_le b N (X ω)
    have htriangle := norm_sub_le (S N ω) (X ω)
    simp only [r, Real.norm_of_nonneg (norm_nonneg _)]
    change ‖S N ω - X ω‖ ≤ 2 * ‖X ω‖
    change ‖S N ω‖ ≤ ‖X ω‖ at hSbound
    linarith
  have hres : ∀ᵐ ω ∂μ, Tendsto (fun N => μ[r N | m] ω) atTop (𝓝 0) := by
    apply conditional_antitone_dominated_zero μ hm r (fun ω => 2 * ‖X ω‖)
      (fun N => ((hS N).sub hX).aestronglyMeasurable.norm)
      (hX.norm.const_mul 2) (fun N => ae_of_all μ (hbound N))
    · exact ae_of_all μ fun ω => by
        simpa only [r, S, norm_sub_rev] using scoreProjection_residual_antitone b (X ω)
    · exact ae_of_all μ fun ω => by
        simpa only [r, sub_self, norm_zero] using ((hlim ω).sub_const (X ω)).norm
  have hdiff (N : ℕ) : μ[(fun ω => S N ω - X ω) | m] =ᵐ[μ]
      (fun ω => μ[S N | m] ω - μ[X | m] ω) := condExp_sub (hS N) hX m
  have hnorm (N : ℕ) : ∀ᵐ ω ∂μ,
      ‖μ[(fun u => S N u - X u) | m] ω‖ ≤ μ[r N | m] ω := norm_condExp_le
  filter_upwards [hres, ae_all_iff.mpr hdiff, ae_all_iff.mpr hnorm] with ω hr hd hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hr
  rw [← hd N]
  exact hn N

/-- The thesis's linearity step: `E[S_N | G] = ∑_{n<N} E[θₙ | G] eₙ` almost surely, by
linearity of conditional expectation and `E[θₙ eₙ | G] = E[θₙ | G] eₙ` for the fixed
deterministic basis vector `eₙ`. -/
theorem condExp_scoreProjection_eq_finite_scores
    {Ω : Type u} {H : Type v} {m m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m₀] Ω) (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (b : HilbertBasis ℕ ℝ H) {X : Ω → H} (hX : Integrable X μ) (N : ℕ) :
    μ[(fun u => scoreProjection b N (X u)) | m] =ᵐ[μ]
      (fun ω => ∑ n ∈ Finset.range N, μ[(fun u => score b n (X u)) | m] ω • b n) := by
  have hscore (n : ℕ) : Integrable (fun u => score b n (X u)) μ :=
    (innerSL ℝ (b n)).integrable_comp hX
  have hterm (n : ℕ) : Integrable (fun u => score b n (X u) • b n) μ :=
    (hscore n).smul_const _
  have hsum := condExp_finset_sum (s := Finset.range N)
    (f := fun n u => score b n (X u) • b n) (fun n _ => hterm n) m
  have hpull (n : ℕ) :
      μ[(fun u => score b n (X u) • b n) | m] =ᵐ[μ]
        (fun ω => μ[(fun u => score b n (X u)) | m] ω • b n) := by
    exact ((ContinuousLinearMap.toSpanSingleton ℝ (b n)).comp_condExp_comm
      (m := m) (hscore n)).symm
  have hinput : (fun u => scoreProjection b N (X u)) =
      ∑ n ∈ Finset.range N, (fun u => score b n (X u) • b n) := by
    funext u
    simp only [scoreProjection_apply, Finset.sum_apply]
  rw [hinput]
  filter_upwards [hsum, ae_all_iff.mpr hpull] with ω hs hp
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun n _ => hp n

/-- In a Hilbert basis, convergence of the partial sums `∑_{n<N} cₙ eₙ` to `z` identifies
each coefficient `cₙ` as the score `⟪eₙ, z⟫` (the scores of the partial sums are
eventually constant and continuous in the limit), so the series is the unconditionally
convergent basis expansion of `z`. -/
theorem hasSum_of_tendsto_partialSums_smul_basis
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (c : ℕ → ℝ) {z : H}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, c n • b n) atTop (𝓝 z)) :
    HasSum (fun n => c n • b n) z := by
  have hc : ∀ n, score b n z = c n := by
    intro n
    have hcont : Continuous (score b n) := by
      unfold score
      fun_prop
    have h1 : Tendsto (fun N => score b n (∑ k ∈ Finset.range N, c k • b k)) atTop
        (𝓝 (score b n z)) := (hcont.tendsto z).comp h
    have h2 : ∀ᶠ N in atTop, score b n (∑ k ∈ Finset.range N, c k • b k) = c n := by
      filter_upwards [eventually_gt_atTop n] with N hN
      simp [score, inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal, hN]
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h2.mono fun N hN => hN.symm))
  refine HasSum.congr_fun (hasSum_score_smul_basis b z) ?_
  intro n
  rw [hc n]

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Series-convergence clause of Theorem `thm:conditional-expect-Hilbert`.

Original label: `thm:conditional-expect-Hilbert`.

Informal statement: the finite score reconstructions converge almost surely
to the Hilbert-valued conditional expectation.

Lean strategy / thesis relation note: this is the thesis proof.  With
`S_N = ∑_{n<N} θₙ eₙ` (`scoreProjection`), linearity of conditional expectation and
pulling out the deterministic vectors give `E[S_N | G] = ∑_{n<N} E[θₙ | G] eₙ`
(`condExp_scoreProjection_eq_finite_scores`); `S_N → X` with `‖S_N‖ ≤ ‖X‖` and
`E‖X‖ < ∞`, so conditional dominated convergence gives `E[S_N | G] → E[X | G]`
almost surely (`condExp_scoreProjection_tendsto`).  The thesis assumes square
integrability on a probability space; the argument only needs Bochner
integrability, so the Lean theorem is slightly stronger.  Lean uses zero-based
natural-number indexing for the Hilbert basis.
-/
theorem condExp_partialSums_tendsto
    {Ω : Type u} {H : Type v} {m m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m₀] Ω) (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (b : HilbertBasis ℕ ℝ H) {X : Ω → H} (hX : Integrable X μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun N => ∑ n ∈ Finset.range N,
        μ[(fun η => score b n (X η)) | m] ω • b n)
      atTop (𝓝 (μ[X | m] ω)) := by
  filter_upwards [condExp_scoreProjection_tendsto μ hm b hX,
    ae_all_iff.mpr (fun N => condExp_scoreProjection_eq_finite_scores μ hm b hX N)]
    with ω hlim heq
  exact hlim.congr (fun N => heq N)

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Theorem `thm:conditional-expect-Hilbert`.

Original label: `thm:conditional-expect-Hilbert`.

Informal statement: the conditional expectation of a Hilbert-valued random
variable is almost surely the convergent sum of the conditional expectations
of its scalar basis scores.

Lean strategy / thesis relation note: the thesis proves the almost-sure
convergence of the partial sums `∑_{n<N} E[θₙ | G] eₙ` to `E[X | G]`
(`condExp_partialSums_tendsto`, by the `S_N` / conditional dominated convergence
argument).  The `HasSum` form recorded here is the unconditional-convergence
packaging of that limit: the partial-sum limit identifies the coefficients as the
scores of `E[X | G]`, whose basis expansion converges unconditionally
(`hasSum_of_tendsto_partialSums_smul_basis`).  Lean uses zero-based natural-number
indexing for the Hilbert basis.
-/
theorem condExp_hasSum_scores
    {Ω : Type u} {H : Type v} {m m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m₀] Ω) (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (b : HilbertBasis ℕ ℝ H) {X : Ω → H} (hX : Integrable X μ) :
    ∀ᵐ ω ∂μ, HasSum
      (fun n => μ[(fun η => score b n (X η)) | m] ω • b n)
      (μ[X | m] ω) := by
  filter_upwards [condExp_partialSums_tendsto μ hm b hX] with ω hω
  exact hasSum_of_tendsto_partialSums_smul_basis b _ hω

/-! ## Conditional expectation as the least-squares predictor -/

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Theorem `thm:regression-theorem`.

Original label: `thm:regression-theorem`.

Informal statement: conditional expectation is the least-squares predictor
among square-integrable random variables measurable with respect to the
conditioning sigma-algebra.

Lean strategy / thesis relation note: the current manuscript uses membership
in the argmin set. This theorem supplies the orthogonal-projection core: the
distance is the infimum over the measurable subspace. `RegressionMeanSquare`
connects it to the displayed expected squared error for actual random variables.
The Doob--Dynkin factorization through a predictor variable is a separate clause;
the corrected final sentence minimizes over that predictor's sigma-algebra.
-/
theorem condExpL2_minimizes
    {Ω : Type u} {H : Type v} {m m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {μ : Measure[m₀] Ω} (hm : m ≤ m₀) (f : Ω →₂[μ] H) :
    ‖f - (condExpL2 H ℝ hm f : Ω →₂[μ] H)‖ =
      ⨅ g : lpMeas H ℝ m 2 μ, ‖f - (g : Ω →₂[μ] H)‖ := by
  letI : Fact (m ≤ m₀) := ⟨hm⟩
  simpa only [condExpL2, Submodule.starProjection_apply] using
    (Submodule.starProjection_minimal
      (U := lpMeas H ℝ m 2 μ) f)

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`, predictor-factorisation clause
of Theorem `thm:regression-theorem`.

Original label: `thm:regression-theorem`.

Informal statement: conditioning on a random element `Y` produces a predictor
of the form `g(Y)` for a measurable function `g` on the state space of `Y`.

Lean strategy / thesis relation note: this is the Doob--Dynkin lemma. The
manuscript assumes the predictor state space is standard Borel; Mathlib's
strong-measurability form only needs the Hilbert-valued codomain to be complete.
The equality is pointwise for Mathlib's chosen conditional-expectation version,
and hence is stronger than the manuscript's almost-sure equality.
-/
theorem condExp_factorsThrough_predictor
    {Ω : Type u} {E : Type v} {H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (Y : Ω → E) (_hY : Measurable Y) (X : Ω → H) :
    ∃ g : E → H, StronglyMeasurable g ∧
      μ[X | (inferInstance : MeasurableSpace E).comap Y] = g ∘ Y := by
  have hcond : StronglyMeasurable[(inferInstance : MeasurableSpace E).comap Y]
      (μ[X | (inferInstance : MeasurableSpace E).comap Y]) :=
    stronglyMeasurable_condExp
  exact hcond.exists_eq_measurable_comp

/-! ## Weak stationarity in coordinates -/

/-- Matrix coefficients in a Hilbert basis determine a bounded linear operator. -/
theorem continuousLinearMap_eq_of_basis_matrix_eq
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) {A B : H →L[ℝ] H}
    (h : ∀ n m, score b m (A (b n)) = score b m (B (b n))) : A = B := by
  have hab : ∀ n, A (b n) = B (b n) := fun n =>
    eq_of_scores_eq b (fun m => h n m)
  ext x
  have hA := A.hasSum (b.hasSum_repr x)
  have hB := B.hasSum (b.hasSum_repr x)
  refine (HasSum.congr_fun hA ?_).unique hB
  intro n
  simp only [map_smul, hab n]

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Definition `defn:weak-stationarity`.

Original label: `defn:weak-stationarity`.

Informal statement: a process is weakly stationary when its Hilbert-valued
mean is constant and its cross-covariance operator depends only on the lag.

Lean strategy / thesis relation note: this definition isolates the moment
objects used in the thesis proposition.  Measurability and integrability are
the hypotheses that ensure the supplied `mean` and `crossCov` functions exist;
the coordinate characterization itself is deterministic once those moments
have been formed. `ProcessStationarity.WeaklyStationaryProcess` constructs them
from an actual process and includes the Hilbert--Schmidt lag condition.
-/
def WeaklyStationaryMoments
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (mean : ℕ → H) (crossCov : ℕ → ℕ → H →L[ℝ] H) : Prop :=
  (∃ μ : H, ∀ t, mean t = μ) ∧
    ∃ sigma : ℕ → H →L[ℝ] H, ∀ t h, crossCov (t + h) t = sigma h

/-- Coordinate version of weak stationarity, anchored at time zero. -/
def CoordinatewiseStationaryMoments
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H)
    (mean : ℕ → H) (crossCov : ℕ → ℕ → H →L[ℝ] H) : Prop :=
  (∀ t n, score b n (mean t) = score b n (mean 0)) ∧
    ∀ t h n m,
      score b m (crossCov (t + h) t (b n)) =
        score b m (crossCov h 0 (b n))

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`,
Proposition `prop:weak-stationarity`.

Original label: `prop:weak-stationarity`.

Informal statement: Hilbert-valued weak stationarity is equivalent to
constancy of every coordinate mean and dependence of every coordinate
cross-covariance only on the lag.

Lean strategy / thesis relation note: the reverse implication deliberately
defines the mean as `mean 0`, rather than first postulating a formal series
`∑ n, μ_n e_n`.  This is the corrected argument noted in `THESIS_ERRORS.md` and
automatically supplies the required square summability. The theorem
`ProcessStationarity.weaklyStationaryProcess_iff_scalar` applies this argument to
actual stochastic moments and discharges their analytic hypotheses.
-/
theorem weaklyStationaryMoments_iff_coordinates
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H)
    (mean : ℕ → H) (crossCov : ℕ → ℕ → H →L[ℝ] H) :
    WeaklyStationaryMoments mean crossCov ↔
      CoordinatewiseStationaryMoments b mean crossCov := by
  constructor
  · rintro ⟨⟨μ, hmean⟩, sigma, hcov⟩
    constructor
    · intro t n
      rw [hmean t, hmean 0]
    · intro t h n m
      rw [hcov t h]
      simpa using congrArg
        (fun A : H →L[ℝ] H => score b m (A (b n))) (hcov 0 h).symm
  · rintro ⟨hmean, hcov⟩
    constructor
    · refine ⟨mean 0, fun t => ?_⟩
      exact eq_of_scores_eq b (fun n => hmean t n)
    · refine ⟨fun h => crossCov h 0, fun t h => ?_⟩
      exact continuousLinearMap_eq_of_basis_matrix_eq b (fun n m => hcov t h n m)

end FunctionalData
end DayAhead
end Thesis
