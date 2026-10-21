import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLCanonicalNodes
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalPieceAffinity

/-! # Actual canonical piece formulas on the vendor count cells -/
noncomputable section
namespace Thesis.DayAhead.VendorPLCanonicalPieces

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLPriceCells
open VendorPLQuantityCells VendorPLQuantityAffinity VendorPLBreakpoints VendorPLCanonicalNodes
open PiecewiseAffinePriceCurves PLCanonicalEncoding

variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

theorem actual_canonical_left_affine (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r)
    (j : Fin (leftCount (actualCurve hlohi p r x))) :
    ∃ A B : ℝ, ∀ q ∈ Ioo (leftKnot (actualCurve hlohi p r x) j.castSucc)
      (leftKnot (actualCurve hlohi p r x) j.succ), (actualCurve hlohi p r x).price q = A*q+B := by
  apply PLCanonicalPieceAffinity.canonical_left_piece_affine (actualCurve hlohi p r x)
    (fun i => quantity hlohi p r i x) (selectedQuantity_strictMono hlohi p r x)
    (quantity_first hlohi p r x) (quantity_last hlohi p r x) _ _ j
  · obtain ⟨i, hi⟩ := origin_covered hlohi p r x
    exact ⟨i, hi⟩
  · exact actual_price_affine hlohi p r x

theorem actual_canonical_right_affine (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r)
    (j : Fin (rightCount (actualCurve hlohi p r x))) :
    ∃ A B : ℝ, ∀ q ∈ Ioo (rightKnot (actualCurve hlohi p r x) j.castSucc)
      (rightKnot (actualCurve hlohi p r x) j.succ), (actualCurve hlohi p r x).price q = A*q+B := by
  apply PLCanonicalPieceAffinity.canonical_right_piece_affine (actualCurve hlohi p r x)
    (fun i => quantity hlohi p r i x) (selectedQuantity_strictMono hlohi p r x)
    (quantity_first hlohi p r x) (quantity_last hlohi p r x) _ _ j
  · obtain ⟨i, hi⟩ := origin_covered hlohi p r x
    exact ⟨i, hi⟩
  · exact actual_price_affine hlohi p r x

theorem fixed_left_piece_affine (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : VendorPLCanonicalNodes.cell hlohi p r L R) (j : Fin L.1.val) :
    ∃ A B : ℝ, ∀ q ∈ Ioo (leftKnots hlohi p r L x.val j.castSucc)
      (leftKnots hlohi p r L x.val j.succ), (actualCurve hlohi p r x.val).price q = A*q+B := by
  let f := actualCurve hlohi p r x.val
  let j' : Fin (leftCount f) := Fin.cast (leftCount_on_cell hlohi p r L R x).symm j
  have h1 : leftKnot f j'.castSucc = leftKnots hlohi p r L x.val j.castSucc :=
    leftKnot_on_cell hlohi p r L R x j.castSucc
  have h2 : leftKnot f j'.succ = leftKnots hlohi p r L x.val j.succ :=
    leftKnot_on_cell hlohi p r L R x j.succ
  dsimp only [f] at h1 h2
  simpa only [h1, h2] using actual_canonical_left_affine hlohi p r x.val j'

theorem fixed_right_piece_affine (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : VendorPLCanonicalNodes.cell hlohi p r L R) (j : Fin R.1.val) :
    ∃ A B : ℝ, ∀ q ∈ Ioo (rightKnots hlohi p r R x.val j.castSucc)
      (rightKnots hlohi p r R x.val j.succ), (actualCurve hlohi p r x.val).price q = A*q+B := by
  let f := actualCurve hlohi p r x.val
  let j' : Fin (rightCount f) := Fin.cast (rightCount_on_cell hlohi p r L R x).symm j
  have h1 : rightKnot f j'.castSucc = rightKnots hlohi p r R x.val j.castSucc :=
    rightKnot_on_cell hlohi p r L R x j.castSucc
  have h2 : rightKnot f j'.succ = rightKnots hlohi p r R x.val j.succ :=
    rightKnot_on_cell hlohi p r L R x j.succ
  dsimp only [f] at h1 h2
  simpa only [h1, h2] using actual_canonical_right_affine hlohi p r x.val j'

theorem leftCount_pos_of_left_neg (f : Curve) (hf : f.leftEndpoint < 0) : 0 < leftCount f := by
  by_contra h
  have hc : leftCount f = 0 := Nat.eq_zero_of_not_pos h
  have hi : Fin.last (leftCount f) = 0 := Fin.ext (by simp [hc])
  have heq := leftKnot_last f
  rw [hi, leftKnot_first] at heq
  linarith

theorem rightCount_pos_of_right_pos (f : Curve) (hf : 0 < f.rightEndpoint) : 0 < rightCount f := by
  by_contra h
  have hc : rightCount f = 0 := Nat.eq_zero_of_not_pos h
  have hi : Fin.last (rightCount f) = 0 := Fin.ext (by simp [hc])
  have heq := rightKnot_last f
  rw [hi, rightKnot_first] at heq
  linarith

end Thesis.DayAhead.VendorPLCanonicalPieces
