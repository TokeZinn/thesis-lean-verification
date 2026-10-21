import Thesis.Appendices.DayAheadNumerical.NumericalRepresentation
import Thesis.Appendices.DayAheadNumerical.WeightedIsotonic

/-! # Current coordinate decoding of the 2001-dimensional numerical carrier

The quantity fit has 1001 nodes and half endpoint weights. The price fit has
1000 cells and uniform weights. The assertions concern the exact minimizers;
the separately specified collapsed-point price reader is a further operation.
-/

noncomputable section
namespace Thesis.DayAhead.NumericalDecoding

set_option maxRecDepth 4096

open NumericalRepresentation
open scoped BigOperators

abbrev GridValues := Values 500

def quantities (z : GridValues) : GridFits.Vector 1001 :=
  WeightedIsotonic.quantityFit (nodeWeight 500) (WithLp.toLp 2 z.quantity)

def prices (lo hi : ℝ) (h : lo ≤ hi) (z : GridValues) : GridFits.Vector 1000 :=
  GridFits.priceFit lo hi h (WithLp.toLp 2 z.price)

/-- Original label: `defn:isotonic-decoding-grid`. -/
def decoded (lo hi : ℝ) (h : lo ≤ hi) (z : GridValues) : GridValues where
  quantity := quantities z
  price := prices lo hi h z

def admissible (z : GridValues) : Prop :=
  quantities z 0 ≤ 0 ∧ 0 ≤ quantities z (Fin.last 1000)

theorem quantity_minimizer_existsUnique (z : GridValues) :
    ∃! p : GridFits.Vector 1001, Monotone p ∧
      ∀ v : GridFits.Vector 1001, Monotone v →
        WeightedIsotonic.weightedLoss (nodeWeight 500) (WithLp.toLp 2 z.quantity) p ≤
          WeightedIsotonic.weightedLoss (nodeWeight 500) (WithLp.toLp 2 z.quantity) v :=
  WeightedIsotonic.weighted_quantityFit_existsUnique _
    (nodeWeight_pos (m := 500) (by norm_num)) _

theorem quantities_monotone (z : GridValues) : Monotone (quantities z) :=
  WeightedIsotonic.quantityFit_monotone _ _

theorem prices_monotone (lo hi : ℝ) (h : lo ≤ hi) (z : GridValues) :
    Monotone (prices lo hi h z) := (GridFits.priceFit_mem lo hi h _).1

theorem prices_bounded (lo hi : ℝ) (h : lo ≤ hi) (z : GridValues) (i : Fin 1000) :
    prices lo hi h z i ∈ Set.Icc lo hi := (GridFits.priceFit_mem lo hi h _).2 i

/-- Original label: `prop:app-isotonic-properties`, exact invariance of an
admissible numerical representative under the two coordinate fits. -/
theorem decoded_fixed (lo hi : ℝ) (h : lo ≤ hi) (z : GridValues)
    (hq : Monotone z.quantity) (hp : Monotone z.price)
    (hb : ∀ i, z.price i ∈ Set.Icc lo hi) : decoded lo hi h z = z := by
  have hqfit : quantities z = WithLp.toLp 2 z.quantity :=
    WeightedIsotonic.weighted_quantityFit_fixed _ (nodeWeight_pos (m := 500) (by norm_num)) _ hq
  have hpfit : prices lo hi h z = WithLp.toLp 2 z.price :=
    GridFits.priceFit_fixed lo hi h _ ⟨hp, hb⟩
  cases z
  simp only [decoded]
  congr 1
  · exact congrArg (fun v : GridFits.Vector 1001 => fun i => v i) hqfit
  · exact congrArg (fun v : GridFits.Vector 1000 => fun i => v i) hpfit

theorem priceCellLoss_eq_scaled_squaredLoss (a b : Fin 1000 → ℝ) :
    priceCellLoss (m := 500) a b = width 500 *
      GridFits.squaredLoss (WithLp.toLp 2 a) (WithLp.toLp 2 b) := by
  simp only [priceCellLoss, GridFits.squaredLoss, Finset.mul_sum]

/-- Original label: `prop:app-isotonic-properties`, price-coordinate
non-expansiveness in the exact current cell geometry. -/
theorem decoded_price_loss_le (lo hi : ℝ) (h : lo ≤ hi) (forecast target : GridValues)
    (hp : Monotone target.price) (hb : ∀ i, target.price i ∈ Set.Icc lo hi) :
    priceCellLoss (m := 500) (decoded lo hi h forecast).price target.price ≤
      priceCellLoss (m := 500) forecast.price target.price := by
  rw [priceCellLoss_eq_scaled_squaredLoss, priceCellLoss_eq_scaled_squaredLoss]
  exact mul_le_mul_of_nonneg_left
    (GridFits.priceFit_squaredLoss_to_target_le lo hi h _ _ ⟨hp, hb⟩)
    (width_pos (m := 500) (by norm_num)).le

/-- Original label: `prop:monotone-decoding-nonexpansive`.
Deterministic contraction; the corrected integrable conditional-expectation
clause is proved by coordinate order preservation in `ConditionalDecoding`.
The analogous quantity guarantee is in the trapezoid-weighted node
geometry, as required by the current proposition, not the affine mass form. -/
theorem decoded_quantity_loss_le (lo hi : ℝ) (h : lo ≤ hi)
    (forecast target : GridValues) (hq : Monotone target.quantity) :
    quantityNodeLoss (m := 500) (decoded lo hi h forecast).quantity target.quantity ≤
      quantityNodeLoss (m := 500) forecast.quantity target.quantity := by
  exact WeightedIsotonic.weighted_quantityFit_to_target_le (n := 1001)
    (nodeWeight 500) (nodeWeight_pos (m := 500) (by norm_num))
    (WithLp.toLp 2 forecast.quantity) (WithLp.toLp 2 target.quantity) hq

/-- Original label: `prop:app-isotonic-properties`.
The actual current node samples and cell integrals of a monotone bounded
pointwise pair are fixed by decoding. -/
theorem decoded_representative_fixed (lo hi : ℝ) (h : lo ≤ hi) (ψ φ : ℝ → ℝ)
    (hψ : MonotoneOn ψ (Set.Icc (-1 : ℝ) 1))
    (hφ : MonotoneOn φ (Set.Icc (-1 : ℝ) 1))
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, φ x ∈ Set.Icc lo hi) :
    decoded lo hi h (representative 500 ψ φ) = representative 500 ψ φ :=
  decoded_fixed lo hi h _ (representative_quantity_monotone (by norm_num) ψ φ hψ)
    (representative_price_monotone (by norm_num) ψ φ hφ)
    (representative_price_bounds (by norm_num) ψ φ hφ lo hi hb)

theorem decoded_price_loss_to_representative_le (lo hi : ℝ) (h : lo ≤ hi)
    (forecast : GridValues) (ψ φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Set.Icc (-1 : ℝ) 1))
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, φ x ∈ Set.Icc lo hi) :
    priceCellLoss (m := 500) (decoded lo hi h forecast).price
      (representative 500 ψ φ).price ≤
      priceCellLoss (m := 500) forecast.price (representative 500 ψ φ).price :=
  decoded_price_loss_le lo hi h _ _ (representative_price_monotone (by norm_num) ψ φ hφ)
    (representative_price_bounds (by norm_num) ψ φ hφ lo hi hb)

end Thesis.DayAhead.NumericalDecoding
