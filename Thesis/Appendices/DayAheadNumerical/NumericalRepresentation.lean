import Thesis.Appendices.DayAheadNumerical.GridFits
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The current 1001-node / 1000-cell numerical representation

Quantity values are samples of a supplied pointwise representative. Price
values are cell integrals. The numerical quadratic form is the exact affine
finite-element mass form, and differs from the trapezoid-weighted node norm
used by quantity isotonic regression. No claim is made that node evaluation
is an operation on arbitrary L² equivalence classes.
-/

noncomputable section
namespace Thesis.DayAhead.NumericalRepresentation

open Set MeasureTheory
open scoped BigOperators

def node (m : ℕ) (i : Fin (2 * m + 1)) : ℝ := ((i.val : ℝ) - m) / m

def width (m : ℕ) : ℝ := (m : ℝ)⁻¹

def cell (m : ℕ) (i : Fin (2 * m)) : Set ℝ := Icc (node m i.castSucc) (node m i.succ)

/-- Original label: `defn:fixed-grid-representative`. -/
structure Values (m : ℕ) where
  quantity : Fin (2 * m + 1) → ℝ
  price : Fin (2 * m) → ℝ

def representative (m : ℕ) (ψ φ : ℝ → ℝ) : Values m where
  quantity i := ψ (node m i)
  price i := (width m)⁻¹ * ∫ u in cell m i, φ u

theorem node_succ_sub (m : ℕ) (i : Fin (2 * m)) :
    node m i.succ - node m i.castSucc = width m := by
  simp only [node, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, width]
  ring

theorem width_pos {m : ℕ} (hm : 0 < m) : 0 < width m := by
  exact inv_pos.mpr (by exact_mod_cast hm)

theorem node_strictMono {m : ℕ} (hm : 0 < m) : StrictMono (node m) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (show (0 : ℝ) < m by exact_mod_cast hm)).mpr
  exact sub_lt_sub_right (by exact_mod_cast hij) _

theorem node_zero {m : ℕ} (hm : 0 < m) : node m 0 = -1 := by
  simp only [node, Fin.val_zero, Nat.cast_zero, zero_sub, neg_div]
  rw [div_self (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)]

theorem node_last {m : ℕ} (hm : 0 < m) : node m (Fin.last (2 * m)) = 1 := by
  simp only [node, Fin.val_last, Nat.cast_mul, Nat.cast_ofNat]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

theorem node_mem_interval {m : ℕ} (hm : 0 < m) (i : Fin (2 * m + 1)) :
    node m i ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · simpa only [node_zero hm] using (node_strictMono hm).monotone (Fin.zero_le i)
  · simpa only [node_last hm] using (node_strictMono hm).monotone (Fin.le_last i)

theorem cell_subset_interval {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) :
    cell m i ⊆ Icc (-1 : ℝ) 1 :=
  fun _ hx => ⟨(node_mem_interval hm i.castSucc).1.trans hx.1,
    hx.2.trans (node_mem_interval hm i.succ).2⟩

/-- Cell averages of a monotone price function lie between its endpoint
values. This uses actual Lebesgue integrals, rather than assuming that the
resulting price array is monotone. -/
theorem representative_price_between {m : ℕ} (hm : 0 < m) (ψ φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Icc (-1 : ℝ) 1)) (i : Fin (2 * m)) :
    (representative m ψ φ).price i ∈
      Icc (φ (node m i.castSucc)) (φ (node m i.succ)) := by
  letI : IsFiniteMeasure (volume.restrict (cell m i)) := by
    dsimp [cell]
    infer_instance
  have hsub := cell_subset_interval hm i
  have hmono : MonotoneOn φ (cell m i) := hφ.mono hsub
  have hint : IntegrableOn φ (cell m i) volume := hmono.integrableOn_isCompact isCompact_Icc
  have hnodes : node m i.castSucc ≤ node m i.succ :=
    (node_strictMono hm).monotone (Fin.castSucc_le_succ i)
  have hl := setIntegral_mono_on (integrable_const (φ (node m i.castSucc))) hint
    measurableSet_Icc (fun x hx => hφ (node_mem_interval hm _) (hsub hx) hx.1)
  have hr := setIntegral_mono_on hint (integrable_const (φ (node m i.succ)))
    measurableSet_Icc (fun x hx => hφ (hsub hx) (node_mem_interval hm _) hx.2)
  have hw : 0 < width m := width_pos hm
  have hmeasure : volume.real (cell m i) = width m := by
    rw [cell, Real.volume_real_Icc_of_le hnodes, node_succ_sub]
  rw [setIntegral_const, hmeasure, smul_eq_mul] at hl hr
  constructor
  · calc
      φ (node m i.castSucc) = (width m)⁻¹ * (width m * φ (node m i.castSucc)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hw.le)
  · calc
      _ ≤ (width m)⁻¹ * (width m * φ (node m i.succ)) :=
        mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hw.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]

theorem representative_quantity_monotone {m : ℕ} (hm : 0 < m) (ψ φ : ℝ → ℝ)
    (hψ : MonotoneOn ψ (Icc (-1 : ℝ) 1)) : Monotone (representative m ψ φ).quantity :=
  fun _ _ hij => hψ (node_mem_interval hm _) (node_mem_interval hm _)
    ((node_strictMono hm).monotone hij)

theorem representative_price_monotone {m : ℕ} (hm : 0 < m) (ψ φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Icc (-1 : ℝ) 1)) : Monotone (representative m ψ φ).price := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  have hidx : i.succ ≤ j.castSucc := by exact_mod_cast hij
  exact (representative_price_between hm ψ φ hφ i).2.trans
    ((hφ (node_mem_interval hm _) (node_mem_interval hm _)
      ((node_strictMono hm).monotone hidx)).trans
        (representative_price_between hm ψ φ hφ j).1)

theorem representative_price_bounds {m : ℕ} (hm : 0 < m) (ψ φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Icc (-1 : ℝ) 1)) (lo hi : ℝ)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, φ x ∈ Icc lo hi) (i : Fin (2 * m)) :
    (representative m ψ φ).price i ∈ Icc lo hi :=
  ⟨(hb _ (node_mem_interval hm _)).1.trans (representative_price_between hm ψ φ hφ i).1,
    (representative_price_between hm ψ φ hφ i).2.trans (hb _ (node_mem_interval hm _)).2⟩

/-- The current dimensions are 2001, with 1001 quantity and 1000 price values. -/
theorem current_dimensions : 2 * 500 + 1 = 1001 ∧ 2 * 500 = 1000 := by norm_num

/-- The closed-cell convention is harmless for price integrals: changing a
price function on a null set does not change any price entry. -/
theorem price_representative_congr_ae (m : ℕ) (ψ φ χ : ℝ → ℝ)
    (h : φ =ᵐ[volume] χ) :
    (representative m ψ φ).price = (representative m ψ χ).price := by
  funext i
  exact congrArg (fun r => (width m)⁻¹ * r)
    (integral_congr_ae (ae_restrict_of_ae h))

/-- Original label: `defn:numerical-inner-product`, one affine cell. -/
def affineMass (h a b c d : ℝ) : ℝ := h / 6 * (2 * a * c + a * d + b * c + 2 * b * d)

def numericalInner {m : ℕ} (z w : Values m) : ℝ :=
  ∑ i : Fin (2 * m),
    (affineMass (width m) (z.quantity i.castSucc) (z.quantity i.succ)
      (w.quantity i.castSucc) (w.quantity i.succ) + width m * z.price i * w.price i)

/-- Original label: `prop:app-numerical-inner-product-exact`, the exact local
integral identity from which the finite-cell sum follows. -/
theorem affineMass_exact (h a b c d : ℝ) :
    h * (∫ s in (0 : ℝ)..1, ((1 - s) * a + s * b) * ((1 - s) * c + s * d)) =
      affineMass h a b c d := by
  have hpoly : (fun s : ℝ => ((1 - s) * a + s * b) * ((1 - s) * c + s * d)) =
      (fun s => a * c + (a * d + b * c - 2 * a * c) * s +
        (a * c - a * d - b * c + b * d) * s ^ 2) := by
    funext s
    ring
  rw [hpoly]
  have hi₁ : IntervalIntegrable (fun s : ℝ => a * c + (a * d + b * c - 2 * a * c) * s)
      volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun s : ℝ => (a * c - a * d - b * c + b * d) * s ^ 2)
      volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi₀ : IntervalIntegrable (fun s : ℝ => (a * d + b * c - 2 * a * c) * s)
      volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi₁ hi₂,
    intervalIntegral.integral_add (intervalIntegrable_const) hi₀,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  simp only [integral_id, integral_pow]
  norm_num [affineMass]
  ring

def localInterpolantInner {m : ℕ} (z w : Values m) : ℝ :=
  ∑ i : Fin (2 * m), (width m *
    (∫ s in (0 : ℝ)..1,
      ((1 - s) * z.quantity i.castSucc + s * z.quantity i.succ) *
      ((1 - s) * w.quantity i.castSucc + s * w.quantity i.succ)) +
    width m * z.price i * w.price i)

/-- Exactness summed over every cell, including the two coordinate parts. -/
theorem numericalInner_eq_localInterpolantInner {m : ℕ} (z w : Values m) :
    numericalInner z w = localInterpolantInner z w := by
  simp only [numericalInner, localInterpolantInner, affineMass_exact]

theorem affineMass_self (h a b : ℝ) :
    affineMass h a b a b = h / 6 * (a ^ 2 + b ^ 2 + (a + b) ^ 2) := by
  unfold affineMass
  ring

theorem numericalInner_self_nonneg {m : ℕ} (z : Values m) : 0 ≤ numericalInner z z := by
  unfold numericalInner
  apply Finset.sum_nonneg
  intro i _
  rw [affineMass_self]
  have hw : 0 ≤ width m := inv_nonneg.mpr (Nat.cast_nonneg m)
  have hs : 0 ≤ z.quantity i.castSucc ^ 2 + z.quantity i.succ ^ 2 +
      (z.quantity i.castSucc + z.quantity i.succ) ^ 2 := by positivity
  have hp : 0 ≤ width m * z.price i * z.price i := by
    nlinarith [sq_nonneg (z.price i)]
  exact add_nonneg (mul_nonneg (div_nonneg hw (by norm_num)) hs) hp

/-- Trapezoidal node weights of `eq:quantity-pava`; these are not the mass
matrix used by `numericalInner`. -/
def nodeWeight (m : ℕ) (i : Fin (2 * m + 1)) : ℝ :=
  if i.val = 0 ∨ i.val = 2 * m then width m / 2 else width m

theorem nodeWeight_pos {m : ℕ} (hm : 0 < m) (i : Fin (2 * m + 1)) :
    0 < nodeWeight m i := by
  unfold nodeWeight
  split <;> positivity [width_pos hm]

def quantityNodeLoss {m : ℕ} (a b : Fin (2 * m + 1) → ℝ) : ℝ :=
  ∑ i, nodeWeight m i * (a i - b i) ^ 2

def priceCellLoss {m : ℕ} (a b : Fin (2 * m) → ℝ) : ℝ :=
  ∑ i, width m * (a i - b i) ^ 2

/-- Already for one affine cell, the trapezoidal node norm and the exact
L² mass norm differ. Thus separate isotonic fitting is not a joint projection
for the thesis's numerical inner product. -/
theorem node_and_mass_geometry_differ :
    (1 / 2 : ℝ) * (0 ^ 2 + 1 ^ 2) ≠ affineMass 1 0 1 0 1 := by
  norm_num [affineMass]

end Thesis.DayAhead.NumericalRepresentation
