import Mathlib.Analysis.InnerProductSpace.PiL2
import Thesis.Foundations.Stochastic.KernelHilbert

/-! # Unweighted isotonic fits supporting the current bounded price fit

The bounded price problem has uniform cell weights. The quantity problem
here has uniform weights and is only a supporting lemma: the current thesis
uses half weights at the two quantity endpoints.
-/

noncomputable section
namespace Thesis.DayAhead.GridFits

open Set
open Foundations.Stochastic.KernelHilbert
open scoped BigOperators

abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)

def quantitySet (n : ℕ) : Set (Vector n) := {x | Monotone x}
def priceSet (n : ℕ) (lo hi : ℝ) : Set (Vector n) :=
  {x | Monotone x ∧ ∀ i, x i ∈ Icc lo hi}

theorem quantitySet_closed (n : ℕ) : IsClosed (quantitySet n) :=
  isClosed_monotone.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))

theorem quantitySet_convex (n : ℕ) : Convex ℝ (quantitySet n) := by
  intro x hx y hy a b ha hb _ i j hij
  change a * x i + b * y i ≤ a * x j + b * y j
  exact add_le_add (mul_le_mul_of_nonneg_left (hx hij) ha)
    (mul_le_mul_of_nonneg_left (hy hij) hb)

theorem quantitySet_nonempty (n : ℕ) : (quantitySet n).Nonempty :=
  ⟨0, fun _ _ _ => le_rfl⟩

theorem priceSet_closed (n : ℕ) (lo hi : ℝ) : IsClosed (priceSet n lo hi) := by
  change IsClosed (quantitySet n ∩ {x : Vector n | ∀ i, x i ∈ Icc lo hi})
  apply (quantitySet_closed n).inter
  simp only [setOf_forall]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (PiLp.continuous_apply _ _ i)

theorem priceSet_convex (n : ℕ) (lo hi : ℝ) : Convex ℝ (priceSet n lo hi) := by
  intro x hx y hy a b ha hb hab
  refine ⟨quantitySet_convex n hx.1 hy.1 ha hb hab, ?_⟩
  intro i
  change a * x i + b * y i ∈ Icc lo hi
  constructor
  · have h1 := mul_le_mul_of_nonneg_left (hx.2 i).1 ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 i).1 hb
    calc
      lo = a * lo + b * lo := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x i + b * y i := add_le_add h1 h2
  · have h1 := mul_le_mul_of_nonneg_left (hx.2 i).2 ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 i).2 hb
    calc
      a * x i + b * y i ≤ a * hi + b * hi := add_le_add h1 h2
      _ = hi := by rw [← add_mul, hab, one_mul]

theorem priceSet_nonempty (n : ℕ) (lo hi : ℝ) (h : lo ≤ hi) :
    (priceSet n lo hi).Nonempty :=
  ⟨WithLp.toLp 2 (fun _ => lo), (fun _ _ _ => le_rfl), fun _ => ⟨le_rfl, h⟩⟩

theorem convex_projection_existsUnique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {C : Set H}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hne : C.Nonempty) (u : H) :
    ∃! p : H, p ∈ C ∧ ‖u - p‖ = ⨅ w : C, ‖u - (w : H)‖ := by
  obtain ⟨p, hp, he⟩ := exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv u
  refine ⟨p, ⟨hp, he⟩, ?_⟩
  intro q hq
  exact convexSet_metricProjection_minimizer_unique hconv hq.1 hp hq.2 he

/-- Unweighted supporting quantity fit; the current node fit is weighted. -/
theorem quantityFit_existsUnique (n : ℕ) (u : Vector n) :
    ∃! p : Vector n, p ∈ quantitySet n ∧ ‖u - p‖ = ⨅ w : quantitySet n, ‖u - (w : Vector n)‖ :=
  convex_projection_existsUnique (quantitySet_closed n) (quantitySet_convex n)
    (quantitySet_nonempty n) u

/-- Original label: `eq:price-pava`. -/
theorem priceFit_existsUnique (n : ℕ) (lo hi : ℝ) (h : lo ≤ hi) (u : Vector n) :
    ∃! p : Vector n, p ∈ priceSet n lo hi ∧
      ‖u - p‖ = ⨅ w : priceSet n lo hi, ‖u - (w : Vector n)‖ :=
  convex_projection_existsUnique (priceSet_closed n lo hi) (priceSet_convex n lo hi)
    (priceSet_nonempty n lo hi h) u

def quantityFit {n : ℕ} (u : Vector n) : Vector n := (quantityFit_existsUnique n u).choose
def priceFit {n : ℕ} (lo hi : ℝ) (h : lo ≤ hi) (u : Vector n) : Vector n :=
  (priceFit_existsUnique n lo hi h u).choose

theorem quantityFit_mem {n : ℕ} (u : Vector n) : quantityFit u ∈ quantitySet n :=
  (quantityFit_existsUnique n u).choose_spec.1.1

theorem priceFit_mem {n : ℕ} (lo hi : ℝ) (h : lo ≤ hi) (u : Vector n) :
    priceFit lo hi h u ∈ priceSet n lo hi :=
  (priceFit_existsUnique n lo hi h u).choose_spec.1.1

def squaredLoss {n : ℕ} (u v : Vector n) : ℝ := ∑ i, (u i - v i)^2

theorem squaredLoss_eq_norm_sq {n : ℕ} (u v : Vector n) : squaredLoss u v = ‖u - v‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, squaredLoss]

theorem squaredLoss_minimal {n : ℕ} {C : Set (Vector n)} {u p : Vector n}
    (hp : ‖u - p‖ = ⨅ w : C, ‖u - (w : Vector n)‖) {v : Vector n} (hv : v ∈ C) :
    squaredLoss u p ≤ squaredLoss u v := by
  rw [squaredLoss_eq_norm_sq, squaredLoss_eq_norm_sq]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [hp]
  exact ciInf_le_of_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ ⟨v, hv⟩ le_rfl

theorem quantityFit_minimal {n : ℕ} (u : Vector n) (v : Vector n) (hv : Monotone v) :
    squaredLoss u (quantityFit u) ≤ squaredLoss u v :=
  squaredLoss_minimal (quantityFit_existsUnique n u).choose_spec.1.2 hv

theorem priceFit_minimal {n : ℕ} (lo hi : ℝ) (h : lo ≤ hi) (u v : Vector n)
    (hv : v ∈ priceSet n lo hi) : squaredLoss u (priceFit lo hi h u) ≤ squaredLoss u v :=
  squaredLoss_minimal (priceFit_existsUnique n lo hi h u).choose_spec.1.2 hv

/-- A closest point in a convex Hilbert set cannot increase distance to any
point in that set. This proves the target-distance part of the current
coordinate decoding proposition directly from its variational inequality. -/
theorem projection_norm_sub_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {C : Set H} (hC : Convex ℝ C) {u p v : H}
    (hp : p ∈ C) (hmin : ‖u - p‖ = ⨅ w : C, ‖u - (w : H)‖)
    (hv : v ∈ C) : ‖p - v‖ ≤ ‖u - v‖ := by
  have hvar := ((norm_eq_iInf_iff_real_inner_le_zero hC hp).mp hmin) v hv
  have heq : u - v = (u - p) + (p - v) := by abel
  have hn := norm_add_sq_real (u - p) (p - v)
  have hinner : inner ℝ (u - p) (p - v) = -inner ℝ (u - p) (v - p) := by
    rw [← inner_neg_right]
    congr 2
    abel
  rw [hinner, ← heq] at hn
  have hsq : ‖p - v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by nlinarith [sq_nonneg ‖u - p‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Original label: `prop:app-isotonic-properties`, bounded price contraction. -/
theorem priceFit_norm_sub_le {n : ℕ} (lo hi : ℝ) (h : lo ≤ hi)
    (u v : Vector n) (hv : v ∈ priceSet n lo hi) :
    ‖priceFit lo hi h u - v‖ ≤ ‖u - v‖ :=
  projection_norm_sub_le (priceSet_convex n lo hi) (priceFit_mem lo hi h u)
    (priceFit_existsUnique n lo hi h u).choose_spec.1.2 hv

theorem priceFit_fixed {n : ℕ} (lo hi : ℝ) (h : lo ≤ hi) (u : Vector n)
    (hu : u ∈ priceSet n lo hi) : priceFit lo hi h u = u := by
  have hdist := priceFit_norm_sub_le lo hi h u u hu
  simpa only [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] using hdist

theorem priceFit_squaredLoss_to_target_le {n : ℕ} (lo hi : ℝ) (h : lo ≤ hi)
    (u v : Vector n) (hv : v ∈ priceSet n lo hi) :
    squaredLoss (priceFit lo hi h u) v ≤ squaredLoss u v := by
  rw [squaredLoss_eq_norm_sq, squaredLoss_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (priceFit_norm_sub_le lo hi h u v hv) 2

end Thesis.DayAhead.GridFits
