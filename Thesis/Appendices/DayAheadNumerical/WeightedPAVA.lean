import Thesis.Appendices.DayAheadNumerical.WeightedIsotonic
import Thesis.DayAhead.ForecastingImpact.EmpiricalGeometry
import Thesis.Appendices.DayAheadNumerical.NumericalRepresentation
import Thesis.Appendices.DayAheadNumerical.NumericalDecoding

/-! # Integer-weighted PAVA by ordered replication

Positive integer weights are represented by ordered repeated observations.
Ordinary PAVA is run once on that list, then each original group is averaged.
The variance decomposition proves that this averaging cannot increase the
objective. Thus this actual finite algorithm solves the weighted problem.
-/

noncomputable section
namespace Thesis.DayAhead.WeightedPAVA

open GridFits EmpiricalGeometry
open scoped BigOperators

variable {N n : ℕ}

def group (π : Fin N → Fin n) (i : Fin n) : Finset (Fin N) :=
  Finset.univ.filter fun j => π j = i

def countWeight (π : Fin N → Fin n) (i : Fin n) : ℝ := (group π i).card

def expand (π : Fin N → Fin n) (u : Vector n) : Vector N :=
  WithLp.toLp 2 (fun j => u (π j))

def collapse (π : Fin N → Fin n) (f : Vector N) : Vector n :=
  WithLp.toLp 2 (fun i => cellMean (group π i) f)

def fit (π : Fin N → Fin n) (u : Vector n) : Vector n :=
  collapse π (GridPAVA.quantityPAVA (expand π u))

theorem group_nonempty (π : Fin N → Fin n) (hπ : Function.Surjective π) (i : Fin n) :
    (group π i).Nonempty := by
  obtain ⟨j, hj⟩ := hπ i
  exact ⟨j, by simp [group, hj]⟩

theorem countWeight_pos (π : Fin N → Fin n) (hπ : Function.Surjective π) (i : Fin n) :
    0 < countWeight π i := by
  unfold countWeight
  exact_mod_cast (group_nonempty π hπ i).card_pos

theorem cellMean_le {s : Finset (Fin N)} (hs : s.Nonempty) (f : Fin N → ℝ) (c : ℝ)
    (hf : ∀ j ∈ s, f j ≤ c) : cellMean s f ≤ c := by
  have hn : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [cellMean, smul_eq_mul]
  calc
    (s.card : ℝ)⁻¹ * ∑ j ∈ s, f j ≤ (s.card : ℝ)⁻¹ * ∑ _j ∈ s, c :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hf) (inv_nonneg.mpr hn.le)
    _ = c := by simp [hn.ne']

theorem le_cellMean {s : Finset (Fin N)} (hs : s.Nonempty) (f : Fin N → ℝ) (c : ℝ)
    (hf : ∀ j ∈ s, c ≤ f j) : c ≤ cellMean s f := by
  have hn : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [cellMean, smul_eq_mul]
  calc
    c = (s.card : ℝ)⁻¹ * ∑ _j ∈ s, c := by simp [hn.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hf) (inv_nonneg.mpr hn.le)

theorem collapse_monotone (π : Fin N → Fin n) (hπ : Monotone π)
    (hsurj : Function.Surjective π) (f : Vector N) (hf : Monotone f) :
    Monotone (collapse π f) := by
  intro i k hik
  rcases hik.eq_or_lt with rfl | hik
  · exact le_rfl
  apply cellMean_le (group_nonempty π hsurj i)
  intro j hj
  apply le_cellMean (group_nonempty π hsurj k)
  intro l hl
  have hj' : π j = i := (Finset.mem_filter.mp hj).2
  have hl' : π l = k := (Finset.mem_filter.mp hl).2
  apply hf
  by_contra h
  have hlj : l ≤ j := le_of_lt (lt_of_not_ge h)
  have hki := hπ hlj
  rw [hj', hl'] at hki
  exact not_le.mpr hik hki

theorem sum_groups (π : Fin N → Fin n) (f : Fin N → ℝ) :
    (∑ i : Fin n, ∑ j ∈ group π i, f j) = ∑ j, f j := by
  simpa only [group] using
    (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := π) (fun _ _ => Finset.mem_univ _) f)

theorem expanded_loss (π : Fin N → Fin n) (u v : Vector n) :
    squaredLoss (expand π u) (expand π v) = WeightedIsotonic.weightedLoss (countWeight π) u v := by
  change (∑ j, (u (π j) - v (π j)) ^ 2) =
    ∑ i, countWeight π i * (u i - v i) ^ 2
  rw [← sum_groups π (fun j => (u (π j) - v (π j)) ^ 2)]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j ∈ group π i, (u (π j) - v (π j)) ^ 2) =
        ∑ _j ∈ group π i, (u i - v i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := by simp [countWeight]

theorem collapse_loss_le (π : Fin N → Fin n) (hsurj : Function.Surjective π)
    (u : Vector n) (f : Vector N) :
    WeightedIsotonic.weightedLoss (countWeight π) u (collapse π f) ≤
      squaredLoss (expand π u) f := by
  change (∑ i, countWeight π i * (u i - cellMean (group π i) f) ^ 2) ≤
    ∑ j, (u (π j) - f j) ^ 2
  rw [← sum_groups π (fun j => (u (π j) - f j) ^ 2)]
  apply Finset.sum_le_sum
  intro i _
  have hvar := cell_sum_squares (group π i) (group_nonempty π hsurj i) f (u i)
  simp only [Real.norm_eq_abs, sq_abs] at hvar
  have hnonneg : 0 ≤ ∑ j ∈ group π i, (f j - cellMean (group π i) f) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have heq : (∑ j ∈ group π i, (u (π j) - f j) ^ 2) =
      ∑ j ∈ group π i, (f j - u i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
    ring
  rw [heq]
  exact hvar ▸ le_add_of_nonneg_left hnonneg

theorem fit_monotone (π : Fin N → Fin n) (hπ : Monotone π)
    (hsurj : Function.Surjective π) (u : Vector n) : Monotone (fit π u) :=
  collapse_monotone π hπ hsurj _ (GridPAVA.quantityPAVA_monotone _)

theorem fit_minimal (π : Fin N → Fin n) (hπ : Monotone π)
    (hsurj : Function.Surjective π) (u v : Vector n) (hv : Monotone v) :
    WeightedIsotonic.weightedLoss (countWeight π) u (fit π u) ≤
      WeightedIsotonic.weightedLoss (countWeight π) u v := by
  calc
    _ ≤ squaredLoss (expand π u) (GridPAVA.quantityPAVA (expand π u)) :=
      collapse_loss_le π hsurj u _
    _ ≤ squaredLoss (expand π u) (expand π v) :=
      GridPAVA.quantityPAVA_minimal _ _ (hv.comp hπ)
    _ = _ := expanded_loss π u v

theorem fit_eq_weighted_quantityFit (π : Fin N → Fin n) (hπ : Monotone π)
    (hsurj : Function.Surjective π) (u : Vector n) :
    fit π u = WeightedIsotonic.quantityFit (countWeight π) u := by
  have hex := WeightedIsotonic.weighted_quantityFit_existsUnique
    (countWeight π) (countWeight_pos π hsurj) u
  exact hex.unique ⟨fit_monotone π hπ hsurj u, fun v hv => fit_minimal π hπ hsurj u v hv⟩
    ⟨WeightedIsotonic.quantityFit_monotone _ _,
      fun v hv => WeightedIsotonic.quantityFit_minimal _ (countWeight_pos π hsurj) u v hv⟩

theorem weightedLoss_scale (c : ℝ) (w : Fin n → ℝ) (u v : Vector n) :
    WeightedIsotonic.weightedLoss (fun i => c * w i) u v =
      c * WeightedIsotonic.weightedLoss w u v := by
  simp only [WeightedIsotonic.weightedLoss, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fit_eq_scaled_weighted_quantityFit (π : Fin N → Fin n) (hπ : Monotone π)
    (hsurj : Function.Surjective π) (c : ℝ) (hc : 0 < c) (u : Vector n) :
    fit π u = WeightedIsotonic.quantityFit (fun i => c * countWeight π i) u := by
  have hw : ∀ i, 0 < c * countWeight π i := fun i => mul_pos hc (countWeight_pos π hsurj i)
  have hex := WeightedIsotonic.weighted_quantityFit_existsUnique _ hw u
  apply hex.unique ⟨fit_monotone π hπ hsurj u, ?_⟩
    ⟨WeightedIsotonic.quantityFit_monotone _ _,
      fun v hv => WeightedIsotonic.quantityFit_minimal _ hw u v hv⟩
  intro v hv
  rw [weightedLoss_scale, weightedLoss_scale]
  exact mul_le_mul_of_nonneg_left (fit_minimal π hπ hsurj u v hv) hc.le

/-- Endpoints occur once and each interior current-grid observation occurs
twice: 1001 observations expand to 2000 for m=500. -/
def repetitionIndex (m : ℕ) (j : Fin (4 * m)) : Fin (2 * m + 1) :=
  ⟨(j.val + 1) / 2, by have := j.isLt; omega⟩

theorem repetitionIndex_monotone (m : ℕ) : Monotone (repetitionIndex m) := by
  intro i j hij
  change (i.val + 1) / 2 ≤ (j.val + 1) / 2
  exact Nat.div_le_div_right (Nat.add_le_add_right hij 1)

theorem repetitionIndex_surjective {m : ℕ} (hm : 0 < m) :
    Function.Surjective (repetitionIndex m) := by
  intro i
  by_cases hi : i.val = 0
  · exact ⟨⟨0, by omega⟩, Fin.ext (by simpa [repetitionIndex] using hi.symm)⟩
  · refine ⟨⟨2 * i.val - 1, by have := i.isLt; omega⟩, ?_⟩
    apply Fin.ext
    change (2 * i.val - 1 + 1) / 2 = i.val
    omega

theorem repetition_count {m : ℕ} (hm : 0 < m) (i : Fin (2 * m + 1)) :
    countWeight (repetitionIndex m) i = if i.val = 0 ∨ i.val = 2 * m then 1 else 2 := by
  classical
  by_cases hi0 : i.val = 0
  · have hg : group (repetitionIndex m) i = {⟨0, by omega⟩} := by
      ext j
      simp only [group, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Fin.ext_iff]
      change (j.val + 1) / 2 = i.val ↔ j.val = 0
      omega
    simp [countWeight, hg, hi0]
  by_cases hilast : i.val = 2 * m
  · have hg : group (repetitionIndex m) i = {⟨4 * m - 1, by omega⟩} := by
      ext j
      simp only [group, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Fin.ext_iff]
      change (j.val + 1) / 2 = i.val ↔ j.val = 4 * m - 1
      have := j.isLt
      omega
    simp [countWeight, hg, hilast]
  · let a : Fin (4 * m) := ⟨2 * i.val - 1, by have := i.isLt; omega⟩
    let b : Fin (4 * m) := ⟨2 * i.val, by have := i.isLt; omega⟩
    have hab : a ≠ b := by apply Fin.ne_of_val_ne; dsimp [a, b]; omega
    have hg : group (repetitionIndex m) i = {a, b} := by
      ext j
      simp only [group, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      change (j.val + 1) / 2 = i.val ↔ j.val = 2 * i.val - 1 ∨ j.val = 2 * i.val
      omega
    simp [countWeight, hg, hi0, hilast, hab]

theorem currentWeight_eq_scaled_count {m : ℕ} (hm : 0 < m) :
    NumericalRepresentation.nodeWeight m =
      fun i => (NumericalRepresentation.width m / 2) * countWeight (repetitionIndex m) i := by
  funext i
  rw [repetition_count hm i]
  unfold NumericalRepresentation.nodeWeight
  split_ifs <;> ring

/-- This is a finite PAVA procedure for the exact trapezoid-weighted quantity
problem. It uses replication to obtain the two half endpoint weights. -/
def quantityPAVA (m : ℕ) (u : Vector (2 * m + 1)) : Vector (2 * m + 1) :=
  fit (repetitionIndex m) u

theorem quantityPAVA_eq_current_fit {m : ℕ} (hm : 0 < m) (u : Vector (2 * m + 1)) :
    quantityPAVA m u = WeightedIsotonic.quantityFit (NumericalRepresentation.nodeWeight m) u := by
  rw [currentWeight_eq_scaled_count hm]
  exact fit_eq_scaled_weighted_quantityFit _ (repetitionIndex_monotone m)
    (repetitionIndex_surjective hm) _ (by positivity [NumericalRepresentation.width_pos hm]) u

/-- The current two-run numerical fitting algorithm: ordered-replication PAVA
for quantities and ordinary clipped PAVA for price cells. -/
def decodedByPAVA (lo hi : ℝ) (z : NumericalDecoding.GridValues) :
    NumericalDecoding.GridValues where
  quantity := quantityPAVA 500 (WithLp.toLp 2 z.quantity)
  price := GridPAVA.pricePAVA lo hi (WithLp.toLp 2 z.price)

theorem decodedByPAVA_eq (lo hi : ℝ) (h : lo ≤ hi) (z : NumericalDecoding.GridValues) :
    decodedByPAVA lo hi z = NumericalDecoding.decoded lo hi h z := by
  have hq := quantityPAVA_eq_current_fit (m := 500) (by norm_num)
    (WithLp.toLp 2 z.quantity)
  have hp := GridPAVA.pricePAVA_eq_priceFit h (WithLp.toLp 2 z.price)
  unfold decodedByPAVA NumericalDecoding.decoded NumericalDecoding.quantities
    NumericalDecoding.prices
  congr 1
  · exact congrArg (fun v : Vector 1001 => fun i => v i) hq
  · exact congrArg (fun v : Vector 1000 => fun i => v i) hp

end Thesis.DayAhead.WeightedPAVA
