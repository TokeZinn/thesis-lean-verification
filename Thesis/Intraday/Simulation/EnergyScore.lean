import Thesis.Intraday.Simulation.AnalogueAttention
import Mathlib.Analysis.Convex.Function

/-! # Current mixture and finite-ensemble energy scores

Current labels: `defn:aa-training-energy-score`,
`defn:intraday-ensemble-energy-score`, `prop:aa-es-convex-simplex`.
The finite-sum convexity reduction below isolates conditional negative
definiteness as an explicit analytic premise. `EuclideanNegativeType` proves
this premise for the actual unsquared Euclidean distance by scalar cut kernels
and Gaussian projections, and supplies the unconditional simplex theorem.
-/

noncomputable section
namespace Thesis.Intraday.EnergyScore
open scoped BigOperators
open AnalogueAttention

variable {ι : Type*} [Fintype ι]

def pair (D : ι → ι → ℝ) (p q : ι → ℝ) : ℝ := ∑ i, ∑ j, p i * q j * D i j
def linear (d p : ι → ℝ) : ℝ := ∑ i, p i * d i
def score (D : ι → ι → ℝ) (d p : ι → ℝ) : ℝ := linear d p - pair D p p / 2

/-- Original label: `defn:aa-training-energy-score`. -/
def mixture {d : ℕ} (outcomes : ι → Vector d) (target : Vector d) (p : ι → ℝ) : ℝ :=
  score (fun i j => ‖outcomes i - outcomes j‖) (fun i => ‖outcomes i - target‖) p

/-- Original label: `defn:intraday-ensemble-energy-score`. -/
def ensemble {B d : ℕ} (observed : Vector d) (sample : Fin B → Vector d) : ℝ :=
  (∑ i, ‖sample i - observed‖) / B -
    if B < 2 then 0 else
      (∑ i, ∑ j, if i = j then 0 else ‖sample i - sample j‖) / (2 * B * (B - 1))

theorem ensemble_singleton {d : ℕ} (observed : Vector d) (sample : Fin 1 → Vector d) :
    ensemble observed sample = ‖sample 0 - observed‖ := by
  simp [ensemble]

theorem pair_add_left (D : ι → ι → ℝ) (p q r : ι → ℝ) :
    pair D (p + q) r = pair D p r + pair D q r := by
  simp [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pair_add_right (D : ι → ι → ℝ) (p q r : ι → ℝ) :
    pair D p (q + r) = pair D p q + pair D p r := by
  simp [pair, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem pair_smul_left (D : ι → ι → ℝ) (p q : ι → ℝ) (a : ℝ) :
    pair D (a • p) q = a * pair D p q := by
  simp [pair, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem pair_smul_right (D : ι → ι → ℝ) (p q : ι → ℝ) (a : ℝ) :
    pair D p (a • q) = a * pair D p q := by
  simp only [pair, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j, p i * (a * q j) * D i j = a * (p i * q j * D i j) by
    intro i j; ring]
  simp [Finset.mul_sum]

theorem linear_add (d p q : ι → ℝ) : linear d (p + q) = linear d p + linear d q := by
  simp [linear, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem linear_smul (d p : ι → ℝ) (a : ℝ) : linear d (a • p) = a * linear d p := by
  simp [linear, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem mixture_defect (D : ι → ι → ℝ) (d p q : ι → ℝ) (a : ℝ) :
    a * score D d p + (1 - a) * score D d q - score D d (a • p + (1 - a) • q) =
      -(a * (1 - a) / 2) * pair D (p - q) (p - q) := by
  have hsub : p - q = p + (-1 : ℝ) • q := by ext i; simp; ring
  rw [hsub]
  simp only [score, linear_add, linear_smul, pair_add_left, pair_add_right,
    pair_smul_left, pair_smul_right]
  ring

def ConditionallyNegative (D : ι → ι → ℝ) : Prop :=
  ∀ v : ι → ℝ, (∑ i, v i) = 0 → pair D v v ≤ 0

/-- Original label: `prop:aa-es-convex-simplex`.
The general finite-dimensional convexity calculation. The analytic premise
for the actual unsquared Euclidean norm is discharged in `EuclideanNegativeType`. -/
theorem score_convex_on_normalised_weights (D : ι → ι → ℝ) (d : ι → ℝ)
    (hD : ConditionallyNegative D) (p q : ι → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    score D d (a • p + (1 - a) • q) ≤ a * score D d p + (1 - a) * score D d q := by
  have hv : (∑ i, (p - q) i) = 0 := by simp [Pi.sub_apply, Finset.sum_sub_distrib, hp, hq]
  have hn := hD (p-q) hv
  have hc : 0 ≤ a * (1-a) / 2 :=
    div_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (by norm_num)
  have he := mixture_defect D d p q a
  have hprod : 0 ≤ -(a * (1-a) / 2) * pair D (p-q) (p-q) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hc) hn
  linarith

end Thesis.Intraday.EnergyScore
