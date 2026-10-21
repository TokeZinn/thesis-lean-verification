import Thesis.Intraday.Simulation.EnergyScore
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.StdSimplex

/-! # Negative type of the actual unsquared Euclidean distance

The analytic route uses one-dimensional cut kernels and Gaussian projections.
It never replaces the score's norm by a squared norm.
-/

noncomputable section
namespace Thesis.Intraday.EuclideanNegativeType

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

variable {ι : Type*} [Fintype ι]

def cut (L x t : ℝ) : ℝ := (Ioc L x).indicator (fun _ => 1) t

theorem cut_mul (L x y : ℝ) :
    (fun t => cut L x t * cut L y t) = (Ioc L (min x y)).indicator (fun _ => 1) := by
  classical
  funext t
  by_cases hl : L < t <;> by_cases hx : t ≤ x <;> by_cases hy : t ≤ y <;>
    simp [cut, Set.indicator, hl, hx, hy]

theorem cut_mul_integrable (L x y : ℝ) :
    Integrable (fun t => cut L x t * cut L y t) := by
  rw [cut_mul]
  exact (integrableOn_const (μ := volume) (by simp)).integrable_indicator measurableSet_Ioc

theorem integral_cut_mul (L x y : ℝ) (hx : L ≤ x) (hy : L ≤ y) :
    (∫ t, cut L x t * cut L y t) = min x y - L := by
  rw [cut_mul, integral_indicator_const 1 measurableSet_Ioc]
  simp only [smul_eq_mul, mul_one, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (le_min hx hy))]

theorem min_kernel_nonneg (x v : ι → ℝ) (L : ℝ) (hL : ∀ i, L ≤ x i) :
    0 ≤ ∑ i, ∑ j, v i * v j * (min (x i) (x j) - L) := by
  have hid : (fun t => (∑ i, v i * cut L (x i) t) ^ 2) =
      fun t => ∑ i, ∑ j, (v i * v j) * (cut L (x i) t * cut L (x j) t) := by
    funext t
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hint : (∫ t, (∑ i, v i * cut L (x i) t) ^ 2) =
      ∑ i, ∑ j, v i * v j * (min (x i) (x j) - L) := by
    rw [hid, integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul, integral_cut_mul L (x i) (x j) (hL i) (hL j)]
      · exact fun j _ => (cut_mul_integrable L (x i) (x j)).const_mul _
    · intro i _
      exact integrable_finset_sum _ fun j _ => (cut_mul_integrable L (x i) (x j)).const_mul _
  rw [← hint]
  exact integral_nonneg fun t => sq_nonneg _

theorem abs_sub_formula (x y L : ℝ) :
    |x - y| = (x - L) + (y - L) - 2 * (min x y - L) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The unsquared absolute-distance kernel is conditionally negative for
arbitrary finite real families, including empty index sets. -/
theorem real_distance_conditionallyNegative (x : ι → ℝ) :
    EnergyScore.ConditionallyNegative (fun i j => |x i - x j|) := by
  intro v hv
  obtain ⟨L, hL⟩ := (Set.finite_range x).bddBelow
  have hL' : ∀ i, L ≤ x i := fun i => hL (Set.mem_range_self i)
  have hpos := min_kernel_nonneg x v L hL'
  have hlinleft : (∑ i, ∑ j, v i * v j * (x i - L)) = 0 := by
    simp_rw [show ∀ i j, v i * v j * (x i - L) = (v i * (x i - L)) * v j by
      intro i j; ring, ← Finset.mul_sum]
    simp only [hv, mul_zero, Finset.sum_const_zero]
  have hlinright : (∑ i, ∑ j, v i * v j * (x j - L)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [show ∀ i j, v i * v j * (x j - L) = (v j * (x j - L)) * v i by
      intro i j; ring, ← Finset.mul_sum]
    simp only [hv, mul_zero, Finset.sum_const_zero]
  have hpair : EnergyScore.pair (fun i j => |x i - x j|) v v =
      -2 * ∑ i, ∑ j, v i * v j * (min (x i) (x j) - L) := by
    unfold EnergyScore.pair
    have he (i j : ι) : v i * v j * |x i - x j| =
        v i * v j * (x i - L) + v i * v j * (x j - L) -
          2 * (v i * v j * (min (x i) (x j) - L)) := by
      rw [abs_sub_formula (x i) (x j) L]
      ring
    simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hlinleft, hlinright]
    ring
  rw [hpair]
  linarith

def gaussianAbsMean : ℝ := ∫ r : ℝ, |r| ∂gaussianReal 0 1

theorem gaussianAbsMean_pos : 0 < gaussianAbsMean := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have hint : Integrable (fun r : ℝ => |r|) (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs] using
      (IsGaussian.integrable_fun_id (μ := gaussianReal 0 1)).norm
  have hnonneg : 0 ≤ gaussianAbsMean := integral_nonneg fun r => abs_nonneg r
  by_contra h
  have hz : gaussianAbsMean = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hae := (integral_eq_zero_iff_of_nonneg (fun r : ℝ => abs_nonneg r) hint).mp hz
  obtain ⟨r, hr, hne⟩ := (hae.and ((gaussianReal 0 1).ae_ne 0)).exists
  exact hne (abs_eq_zero.mp hr)

section GaussianProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_projection_abs_integrable (x : E) :
    Integrable (fun z => |inner ℝ x z|) (stdGaussian E) := by
  simpa only [Real.norm_eq_abs] using
    (IsGaussian.integrable_dual (stdGaussian E) (innerSL ℝ x)).norm

/-- Averaging absolute Gaussian projections is a positive constant times
the actual Euclidean norm. No formula for that constant is assumed. -/
theorem gaussian_projection_abs_mean (x : E) :
    (∫ z, |inner ℝ x z| ∂stdGaussian E) = ‖x‖ * gaussianAbsMean := by
  have hmap : (stdGaussian E).map (innerSL ℝ x) =
      (gaussianReal 0 1).map (fun r => ‖x‖ * r) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm, gaussianReal_map_const_mul]
    congr 1
    · simp only [mul_zero]
    · apply NNReal.coe_injective
      simp only [mul_one, Real.coe_toNNReal', NNReal.coe_mk, max_eq_left (sq_nonneg _)]
  calc
    _ = ∫ r : ℝ, |r| ∂(stdGaussian E).map (innerSL ℝ x) :=
      (integral_map (by fun_prop) (by fun_prop)).symm
    _ = ∫ r : ℝ, |r| ∂(gaussianReal 0 1).map (fun r => ‖x‖ * r) := by rw [hmap]
    _ = ∫ r : ℝ, |‖x‖ * r| ∂gaussianReal 0 1 := integral_map (by fun_prop) (by fun_prop)
    _ = ‖x‖ * gaussianAbsMean := by
      simp only [abs_mul, abs_of_nonneg (norm_nonneg x), integral_const_mul, gaussianAbsMean]

/-- Original label: `prop:aa-es-convex-simplex`.
Schoenberg's conditional negative-type inequality for the unsquared
Euclidean distance, proved from scalar cuts and Gaussian projections. -/
theorem euclidean_distance_conditionallyNegative (x : ι → E) :
    EnergyScore.ConditionallyNegative (fun i j => ‖x i - x j‖) := by
  intro v hv
  have hpoint (z : E) :
      EnergyScore.pair (fun i j => |inner ℝ (x i - x j) z|) v v ≤ 0 := by
    have h := real_distance_conditionallyNegative (fun i => inner ℝ (x i) z) v hv
    simpa only [inner_sub_left] using h
  have hid : (∫ z, EnergyScore.pair (fun i j => |inner ℝ (x i - x j) z|) v v
        ∂stdGaussian E) =
      gaussianAbsMean * EnergyScore.pair (fun i j => ‖x i - x j‖) v v := by
    unfold EnergyScore.pair
    rw [integral_finset_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul, gaussian_projection_abs_mean]
        ring
      · exact fun j _ => (gaussian_projection_abs_integrable (x i - x j)).const_mul _
    · intro i _
      exact integrable_finset_sum _ fun j _ =>
        (gaussian_projection_abs_integrable (x i - x j)).const_mul _
  have hnonpos : (∫ z, EnergyScore.pair (fun i j => |inner ℝ (x i - x j) z|) v v
      ∂stdGaussian E) ≤ 0 := integral_nonpos hpoint
  rw [hid] at hnonpos
  by_contra h
  exact (not_lt_of_ge hnonpos) (mul_pos gaussianAbsMean_pos (lt_of_not_ge h))

end GaussianProjection

/-- The standard simplex has exactly the pointwise `[0,1]` bounds and unit
mass required by the source definition. -/
theorem stdSimplex_eq_source : stdSimplex ℝ ι =
    {p : ι → ℝ | (∀ i, p i ∈ Icc (0 : ℝ) 1) ∧ ∑ i, p i = 1} := by
  ext p
  exact ⟨fun h => ⟨fun i => mem_Icc_of_mem_stdSimplex h i, h.2⟩,
    fun h => ⟨fun i => (h.1 i).1, h.2⟩⟩

/-- Original label: `prop:aa-es-convex-simplex`.
The actual unsquared-norm mixture energy score is convex on the probability
simplex. This discharges the analytic premise in the exact quadratic defect
identity, for every finite Euclidean dimension, including the source's 33. -/
theorem mixture_convexOn_simplex {d : ℕ} (outcomes : ι → AnalogueAttention.Vector d)
    (target : AnalogueAttention.Vector d) :
    ConvexOn ℝ (stdSimplex ℝ ι) (EnergyScore.mixture outcomes target) := by
  refine ⟨convex_stdSimplex ℝ ι, ?_⟩
  intro p hp q hq a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst b
  have ha1 : a ≤ 1 := by linarith
  simpa only [EnergyScore.mixture, smul_eq_mul] using
    EnergyScore.score_convex_on_normalised_weights
      (fun i j => ‖outcomes i - outcomes j‖) (fun i => ‖outcomes i - target‖)
      (euclidean_distance_conditionallyNegative outcomes) p q hp.2 hq.2 a ha ha1

end Thesis.Intraday.EuclideanNegativeType
