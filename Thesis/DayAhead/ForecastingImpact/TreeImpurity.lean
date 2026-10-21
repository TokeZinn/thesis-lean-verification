import Thesis.DayAhead.ForecastingImpact.EmpiricalGeometry
import Mathlib.Tactic.FieldSimp

/-! # Hilbert tree impurity and Gram formulas in current Chapter 5 -/

noncomputable section
namespace Thesis.DayAhead.TreeImpurity

open EmpiricalGeometry
open scoped BigOperators

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Original label: `defn:cell-impurity-split`. -/
def lossImpurity (loss : H → H → ℝ) (s : Finset ι) (y : ι → H) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ i ∈ s, loss (y i) (cellMean s y)

/-- Original label: `defn:cell-impurity-split`.
The definition permits a general loss; squared Hilbert loss is used later. -/
def lossSplitReduction (loss : H → H → ℝ) (s left right : Finset ι) (y : ι → H) : ℝ :=
  lossImpurity loss s y - (left.card : ℝ) / s.card * lossImpurity loss left y -
    (right.card : ℝ) / s.card * lossImpurity loss right y

/-- The squared-Hilbert-loss specialization. -/
def impurity (s : Finset ι) (y : ι → H) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ i ∈ s, ‖y i - cellMean s y‖ ^ 2

def gramBlock (s t : Finset ι) (y : ι → H) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ t, inner ℝ (y i) (y j)

theorem gramBlock_eq_inner (s t : Finset ι) (y : ι → H) :
    gramBlock s t y = inner ℝ (∑ i ∈ s, y i) (∑ j ∈ t, y j) := by
  simp only [gramBlock, sum_inner, inner_sum]
  exact Finset.sum_comm

theorem gramBlock_symm (s t : Finset ι) (y : ι → H) : gramBlock s t y = gramBlock t s y := by
  rw [gramBlock_eq_inner, gramBlock_eq_inner, real_inner_comm]

theorem norm_cellMean_sq (s : Finset ι) (y : ι → H) :
    ‖cellMean s y‖ ^ 2 = (s.card : ℝ)⁻¹ ^ 2 * gramBlock s s y := by
  rw [cellMean, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, gramBlock_eq_inner,
    real_inner_self_eq_norm_sq]

/-- Chapter 5, lines 344–348. -/
theorem impurity_eq_secondMoment_sub_mean (s : Finset ι) (hs : s.Nonempty) (y : ι → H) :
    impurity s y = (s.card : ℝ)⁻¹ * (∑ i ∈ s, ‖y i‖ ^ 2) - ‖cellMean s y‖ ^ 2 := by
  have h := cell_sum_squares s hs y 0
  simp only [sub_zero, zero_sub, norm_neg] at h
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  rw [h, mul_add, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, add_sub_cancel_right]
  rfl

theorem pairwise_sum_sq (s : Finset ι) (hs : s.Nonempty) (y : ι → H) :
    (∑ i ∈ s, ∑ j ∈ s, ‖y i - y j‖ ^ 2) =
      2 * (s.card : ℝ) * ∑ i ∈ s, ‖y i - cellMean s y‖ ^ 2 := by
  have h (i : ι) : (∑ j ∈ s, ‖y i - y j‖ ^ 2) =
      (∑ j ∈ s, ‖y j - cellMean s y‖ ^ 2) +
        (s.card : ℝ) * ‖y i - cellMean s y‖ ^ 2 := by
    simpa only [norm_sub_rev] using cell_sum_squares s hs y (y i)
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- Original label: `eq:compute-split-1`. -/
theorem impurity_eq_pairwise (s : Finset ι) (hs : s.Nonempty) (y : ι → H) :
    impurity s y = (2 * (s.card : ℝ)^2)⁻¹ *
      ∑ i ∈ s, ∑ j ∈ s, ‖y i - y j‖ ^ 2 := by
  rw [pairwise_sum_sq s hs y, impurity]
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  field_simp

/-- Chapter 5, line 365: the complete Gram-block formula for impurity. -/
theorem impurity_eq_gram (s : Finset ι) (hs : s.Nonempty) (y : ι → H) :
    impurity s y = (s.card : ℝ)⁻¹ * (∑ i ∈ s, inner ℝ (y i) (y i)) -
      (s.card : ℝ)⁻¹ ^ 2 * gramBlock s s y := by
  rw [impurity_eq_secondMoment_sub_mean s hs y, norm_cellMean_sq]
  simp only [real_inner_self_eq_norm_sq]

theorem inner_cellMeans (s t : Finset ι) (y : ι → H) :
    inner ℝ (cellMean s y) (cellMean t y) =
      ((s.card : ℝ)⁻¹ * (t.card : ℝ)⁻¹) * gramBlock s t y := by
  simp only [cellMean, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    gramBlock_eq_inner]
  ring

theorem mean_distance_eq_gram (s t : Finset ι) (y : ι → H) :
    ‖cellMean s y - cellMean t y‖ ^ 2 =
      (s.card : ℝ)⁻¹ ^ 2 * gramBlock s s y +
      (t.card : ℝ)⁻¹ ^ 2 * gramBlock t t y -
      2 * ((s.card : ℝ)⁻¹ * (t.card : ℝ)⁻¹) * gramBlock s t y := by
  rw [norm_sub_sq_real, norm_cellMean_sq, norm_cellMean_sq, inner_cellMeans]
  ring

variable [DecidableEq ι]

/-- Original label: `defn:cell-impurity-split`. -/
def impurityGain (s t : Finset ι) (y : ι → H) : ℝ :=
  impurity (s ∪ t) y - (s.card : ℝ) / (s ∪ t).card * impurity s y -
    (t.card : ℝ) / (s ∪ t).card * impurity t y

theorem gramBlock_union (s t : Finset ι) (hd : Disjoint s t) (y : ι → H) :
    gramBlock (s ∪ t) (s ∪ t) y = gramBlock s s y + gramBlock t t y + 2 * gramBlock s t y := by
  simp only [gramBlock, Finset.sum_union hd, Finset.sum_add_distrib]
  have h := gramBlock_symm s t y
  dsimp only [gramBlock] at h
  linarith

/-- Original label: `eq:compute-split-2`.
The displayed gain identity holds for disjoint, nonempty daughter cells. -/
theorem impurityGain_eq_mean_distance (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : Disjoint s t) (y : ι → H) :
    impurityGain s t y = ((s.card : ℝ) * (t.card : ℝ)) / (s ∪ t).card ^ 2 *
      ‖cellMean s y - cellMean t y‖ ^ 2 := by
  have hst : (s ∪ t).Nonempty := hs.mono Finset.subset_union_left
  have hns : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hnt : (t.card : ℝ) ≠ 0 := by exact_mod_cast ht.card_ne_zero
  have hn : (s.card : ℝ) + (t.card : ℝ) ≠ 0 := by
    have : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
    positivity
  rw [impurityGain, impurity_eq_gram _ hst, impurity_eq_gram _ hs,
    impurity_eq_gram _ ht, mean_distance_eq_gram, gramBlock_union s t hd y,
    Finset.sum_union hd, Finset.card_union_of_disjoint hd, Nat.cast_add]
  field_simp
  ring

theorem impurityGain_nonneg (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : Disjoint s t) (y : ι → H) : 0 ≤ impurityGain s t y := by
  rw [impurityGain_eq_mean_distance s t hs ht hd y]
  positivity

/-- Original label: `prop:gram-split-gain-bound`.
Supporting exact identity for the gain. The proposition's spectral tail error
bound requires a separate perturbation argument. -/
theorem impurityGain_eq_gram (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : Disjoint s t) (y : ι → H) :
    impurityGain s t y = ((s.card : ℝ) * (t.card : ℝ)) / (s ∪ t).card ^ 2 *
      (gramBlock s s y / (s.card : ℝ)^2 + gramBlock t t y / (t.card : ℝ)^2 -
        2 / ((s.card : ℝ) * (t.card : ℝ)) * gramBlock s t y) := by
  rw [impurityGain_eq_mean_distance s t hs ht hd y, mean_distance_eq_gram]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

def leftCell {p : ℕ} (s : Finset ι) (x : ι → Fin p → ℝ) (j : Fin p) (cut : ℝ) : Finset ι :=
  s.filter fun i => x i j ≤ cut

def rightCell {p : ℕ} (s : Finset ι) (x : ι → Fin p → ℝ) (j : Fin p) (cut : ℝ) : Finset ι :=
  s.filter fun i => cut < x i j

omit [DecidableEq ι] in
theorem split_disjoint {p : ℕ} (s : Finset ι) (x : ι → Fin p → ℝ) (j : Fin p) (cut : ℝ) :
    Disjoint (leftCell s x j cut) (rightCell s x j cut) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact not_lt_of_ge (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem split_union {p : ℕ} (s : Finset ι) (x : ι → Fin p → ℝ) (j : Fin p) (cut : ℝ) :
    leftCell s x j cut ∪ rightCell s x j cut = s := by
  ext i
  simp only [leftCell, rightCell, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  · intro hi
    rcases le_or_gt (x i j) cut with h | h
    · exact Or.inl ⟨hi, h⟩
    · exact Or.inr ⟨hi, h⟩

end Thesis.DayAhead.TreeImpurity
