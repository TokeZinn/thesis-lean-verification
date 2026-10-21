import Thesis.Appendices.DayAheadNumerical.GridPAVA

/-! # Positive weighted quantity isotonic regression

The current quantity fit uses trapezoidal node weights, including half weights
at its endpoints. Rescaling each coordinate by the square root of its weight
transports the problem to an ordinary Euclidean closed convex projection.
-/

noncomputable section
namespace Thesis.DayAhead.WeightedIsotonic

open Set GridFits
open scoped BigOperators

variable {n : ℕ}

def scale (w : Fin n → ℝ) (u : Vector n) : Vector n :=
  WithLp.toLp 2 (fun i => Real.sqrt (w i) * u i)

def unscale (w : Fin n → ℝ) (u : Vector n) : Vector n :=
  WithLp.toLp 2 (fun i => u i / Real.sqrt (w i))

theorem unscale_scale (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (u : Vector n) :
    unscale w (scale w u) = u := by
  apply PiLp.ext
  intro i
  simp [unscale, scale, ne_of_gt (Real.sqrt_pos.mpr (hw i))]

theorem scale_unscale (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (u : Vector n) :
    scale w (unscale w u) = u := by
  apply PiLp.ext
  intro i
  change Real.sqrt (w i) * (u i / Real.sqrt (w i)) = u i
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (hw i))]

def constraint (w : Fin n → ℝ) : Set (Vector n) :=
  {u | Monotone (unscale w u)}

theorem constraint_closed (w : Fin n → ℝ) : IsClosed (constraint w) := by
  apply isClosed_monotone.preimage
  exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i).div_const _

theorem constraint_convex (w : Fin n → ℝ) : Convex ℝ (constraint w) := by
  intro u hu v hv a b ha hb _ i j hij
  change (a * u i + b * v i) / Real.sqrt (w i) ≤
    (a * u j + b * v j) / Real.sqrt (w j)
  have hui := mul_le_mul_of_nonneg_left (hu hij) ha
  have hvi := mul_le_mul_of_nonneg_left (hv hij) hb
  change a * (u i / Real.sqrt (w i)) ≤ a * (u j / Real.sqrt (w j)) at hui
  change b * (v i / Real.sqrt (w i)) ≤ b * (v j / Real.sqrt (w j)) at hvi
  calc
    _ = a * (u i / Real.sqrt (w i)) + b * (v i / Real.sqrt (w i)) := by ring
    _ ≤ a * (u j / Real.sqrt (w j)) + b * (v j / Real.sqrt (w j)) := add_le_add hui hvi
    _ = _ := by ring

theorem constraint_nonempty (w : Fin n → ℝ) : (constraint w).Nonempty := by
  refine ⟨0, ?_⟩
  intro i j _
  simp [unscale]

def weightedLoss (w : Fin n → ℝ) (u v : Vector n) : ℝ :=
  ∑ i, w i * (u i - v i) ^ 2

theorem weightedLoss_eq_squaredLoss (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (u v : Vector n) : weightedLoss w u v = squaredLoss (scale w u) (scale w v) := by
  unfold weightedLoss squaredLoss
  apply Finset.sum_congr rfl
  intro i _
  change w i * (u i - v i) ^ 2 = (Real.sqrt (w i) * u i - Real.sqrt (w i) * v i) ^ 2
  rw [← mul_sub, mul_pow, Real.sq_sqrt (hw i).le]

def projected (w : Fin n → ℝ) (u : Vector n) : Vector n :=
  (convex_projection_existsUnique (constraint_closed w) (constraint_convex w)
    (constraint_nonempty w) (scale w u)).choose

/-- Original label: `eq:quantity-pava`. -/
def quantityFit (w : Fin n → ℝ) (u : Vector n) : Vector n := unscale w (projected w u)

theorem quantityFit_monotone (w : Fin n → ℝ) (u : Vector n) : Monotone (quantityFit w u) :=
  (convex_projection_existsUnique (constraint_closed w) (constraint_convex w)
    (constraint_nonempty w) (scale w u)).choose_spec.1.1

theorem quantityFit_minimal (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (u v : Vector n) (hv : Monotone v) :
    weightedLoss w u (quantityFit w u) ≤ weightedLoss w u v := by
  rw [weightedLoss_eq_squaredLoss w hw, weightedLoss_eq_squaredLoss w hw]
  have hp := (convex_projection_existsUnique (constraint_closed w) (constraint_convex w)
    (constraint_nonempty w) (scale w u)).choose_spec.1.2
  rw [quantityFit, scale_unscale w hw]
  apply squaredLoss_minimal hp
  change Monotone (unscale w (scale w v))
  simpa [unscale_scale w hw] using hv

/-- Original label: `prop:app-isotonic-properties`, existence and uniqueness
for every strictly positive set of node weights. -/
theorem weighted_quantityFit_existsUnique (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (u : Vector n) :
    ∃! p : Vector n, Monotone p ∧
      ∀ v : Vector n, Monotone v → weightedLoss w u p ≤ weightedLoss w u v := by
  refine ⟨quantityFit w u, ⟨quantityFit_monotone w u,
    fun v hv => quantityFit_minimal w hw u v hv⟩, ?_⟩
  intro p hp
  let hex := convex_projection_existsUnique (constraint_closed w) (constraint_convex w)
    (constraint_nonempty w) (scale w u)
  have hscaled : scale w p = hex.choose := by
    apply GridPAVA.minimizer_eq_choice (scale w u) (scale w p) (constraint w) hex
    · change Monotone (unscale w (scale w p))
      simpa [unscale_scale w hw] using hp.1
    · intro v hv
      have hmin := hp.2 (unscale w v) hv
      rw [weightedLoss_eq_squaredLoss w hw, weightedLoss_eq_squaredLoss w hw,
        scale_unscale w hw] at hmin
      exact hmin
  have heq := congrArg (unscale w) hscaled
  simpa only [unscale_scale w hw, quantityFit, projected] using heq

/-- Current coordinate decoding does not increase weighted node distance to
any monotone target. Its geometry is the node norm, not the affine mass norm. -/
theorem weighted_quantityFit_to_target_le (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (u v : Vector n) (hv : Monotone v) :
    weightedLoss w (quantityFit w u) v ≤ weightedLoss w u v := by
  rw [weightedLoss_eq_squaredLoss w hw, weightedLoss_eq_squaredLoss w hw,
    squaredLoss_eq_norm_sq, squaredLoss_eq_norm_sq]
  have hp := (convex_projection_existsUnique (constraint_closed w) (constraint_convex w)
    (constraint_nonempty w) (scale w u)).choose_spec.1
  rw [quantityFit, scale_unscale w hw]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply projection_norm_sub_le (constraint_convex w) hp.1 hp.2
  change Monotone (unscale w (scale w v))
  simpa only [unscale_scale w hw] using hv

theorem weighted_quantityFit_fixed (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (u : Vector n) (hu : Monotone u) : quantityFit w u = u := by
  have hdist := weighted_quantityFit_to_target_le w hw u u hu
  rw [weightedLoss_eq_squaredLoss w hw, weightedLoss_eq_squaredLoss w hw,
    squaredLoss_eq_norm_sq, squaredLoss_eq_norm_sq, sub_self, norm_zero,
    zero_pow (by decide)] at hdist
  have hs : scale w (quantityFit w u) = scale w u := by
    apply sub_eq_zero.mp
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (scale w (quantityFit w u) - scale w u)])
  have h := congrArg (unscale w) hs
  simpa only [unscale_scale w hw] using h

end Thesis.DayAhead.WeightedIsotonic
