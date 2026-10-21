import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLQuantityAffinity
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLJoinComparison
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLBreakpointGrid

/-! # Source breakpoint decisions on actual vendor comparison cells

At every interior candidate quantity, two fixed interior samples recover
the actual adjacent affine prices. Point-value equality, the two one-sided
limits and collinearity decide the actual AffineNear predicate by finitely
many Borel comparisons; a jump is never silently discarded.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLBreakpoints

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLPriceCells
open VendorPLQuantityCells VendorPLQuantityAffinity VendorPLMidpoint
open InterpolatedImpactCurve PLJoinComparison PiecewiseAffinePriceCurves

variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

abbrev Interior (n : ℕ) := {i : Fin (n + 1) // 0 < i.val ∧ i.val < n}

def leftGap {n : ℕ} (i : Interior n) : Fin n := ⟨i.val.val - 1, by have := i.property; omega⟩
def rightGap {n : ℕ} (i : Interior n) : Fin n := ⟨i.val.val, i.property.2⟩

@[simp] theorem leftGap_succ {n : ℕ} (i : Interior n) : (leftGap i).succ = i.val := by
  apply Fin.ext
  have := i.property
  simp only [leftGap, Fin.val_succ]
  omega

@[simp] theorem rightGap_castSucc {n : ℕ} (i : Interior n) : (rightGap i).castSucc = i.val := rfl

def actualCurve (p : VendorPLPriceCells.Pattern ns nb) (r : VendorPLQuantityCells.Pattern p)
    (x : VendorPLQuantityCells.cell hlohi p r) : Curve := Book.impactCurve (book hlohi x.val)

def quantity (p : VendorPLPriceCells.Pattern ns nb) (r : VendorPLQuantityCells.Pattern p)
    (i : Fin (r.1.val + 1)) (x : VendorPLQuantityCells.cell hlohi p r) : ℝ :=
  selectedQuantity hlohi p r x.val i

theorem measurable_quantity (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (i : Fin (r.1.val + 1)) :
    Measurable (quantity hlohi p r i) :=
  (measurable_selectedQuantity hlohi p r i).comp measurable_subtype_coe

theorem measurable_price_at_quantity (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (i : Fin (r.1.val + 1)) :
    Measurable (fun x : VendorPLQuantityCells.cell hlohi p r =>
      (actualCurve hlohi p r x).price (quantity hlohi p r i x)) := by
  have h := measurable_actual_price hlohi (fun x => selectedQuantity hlohi p r x i)
    (measurable_selectedQuantity hlohi p r i) (fun x => selectedQuantity_bounds hlohi p r x i)
  exact h.comp measurable_subtype_coe

theorem measurable_price_at_firstSample (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (i j : Fin (r.1.val + 1)) :
    Measurable (fun x : VendorPLQuantityCells.cell hlohi p r =>
      (actualCurve hlohi p r x).price
        (firstSample (quantity hlohi p r i x) (quantity hlohi p r j x))) := by
  let q (x : BoundedLayer lo hi ns nb) :=
    firstSample (selectedQuantity hlohi p r x i) (selectedQuantity hlohi p r x j)
  have hq : Measurable q := by
    dsimp [q, firstSample]
    exact (((measurable_selectedQuantity hlohi p r i).const_mul 2).add
      (measurable_selectedQuantity hlohi p r j)).div_const 3
  have hdom (x : BoundedLayer lo hi ns nb) : q x ∈ (book hlohi x).domain := by
    have hi := selectedQuantity_bounds hlohi p r x i
    have hj := selectedQuantity_bounds hlohi p r x j
    dsimp [q, firstSample]
    constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]
  exact (measurable_actual_price hlohi q hq hdom).comp measurable_subtype_coe

theorem measurable_price_at_secondSample (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (i j : Fin (r.1.val + 1)) :
    Measurable (fun x : VendorPLQuantityCells.cell hlohi p r =>
      (actualCurve hlohi p r x).price
        (secondSample (quantity hlohi p r i x) (quantity hlohi p r j x))) := by
  let q (x : BoundedLayer lo hi ns nb) :=
    secondSample (selectedQuantity hlohi p r x i) (selectedQuantity hlohi p r x j)
  have hq : Measurable q := by
    dsimp [q, secondSample]
    exact ((measurable_selectedQuantity hlohi p r i).add
      ((measurable_selectedQuantity hlohi p r j).const_mul 2)).div_const 3
  have hdom (x : BoundedLayer lo hi ns nb) : q x ∈ (book hlohi x).domain := by
    have hi := selectedQuantity_bounds hlohi p r x i
    have hj := selectedQuantity_bounds hlohi p r x j
    dsimp [q, secondSample]
    constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]
  exact (measurable_actual_price hlohi q hq hdom).comp measurable_subtype_coe

/-- Actual local affinity at each interior transposed vertex is Borel by
source finite collinearity/point-value comparisons, with no oracle premise. -/
theorem measurableSet_affineNear_at_interior (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (i : Interior r.1.val) :
    MeasurableSet {x : VendorPLQuantityCells.cell hlohi p r |
      PLCanonicalEncoding.AffineNear (actualCurve hlohi p r x) (quantity hlohi p r i.val x)} := by
  let l := (leftGap i).castSucc
  let j := i.val
  let k := (rightGap i).succ
  have hlj : l < j := by
    change i.val.val - 1 < i.val.val
    have := i.property.1
    omega
  have hjk : j < k := by
    change i.val.val < i.val.val + 1
    omega
  apply measurableSet_affineNear_of_gaps (actualCurve hlohi p r)
    (quantity hlohi p r l) (quantity hlohi p r j) (quantity hlohi p r k)
    (fun x => selectedQuantity_strictMono hlohi p r x hlj)
    (fun x => selectedQuantity_strictMono hlohi p r x hjk)
  · intro x
    simpa only [l, j, leftGap_succ] using actual_price_affine hlohi p r x (leftGap i)
  · intro x
    simpa only [j, k, rightGap_castSucc] using actual_price_affine hlohi p r x (rightGap i)
  · exact measurable_quantity hlohi p r l
  · exact measurable_quantity hlohi p r j
  · exact measurable_quantity hlohi p r k
  · exact measurable_price_at_firstSample hlohi p r l j
  · exact measurable_price_at_secondSample hlohi p r l j
  · exact measurable_price_at_firstSample hlohi p r j k
  · exact measurable_price_at_secondSample hlohi p r j k
  · exact measurable_price_at_quantity hlohi p r j


theorem quantity_first (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    quantity hlohi p r 0 x = (actualCurve hlohi p r x).leftEndpoint :=
  selectedQuantity_first hlohi p r x

theorem quantity_last (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    quantity hlohi p r (Fin.last r.1.val) x = (actualCurve hlohi p r x).rightEndpoint :=
  selectedQuantity_last hlohi p r x

/-- The exact intrinsic-breakpoint decision is Borel at every candidate,
including both physical endpoints and the separately handled origin. -/
theorem measurableSet_breakpoint_at (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (i : Fin (r.1.val + 1)) :
    MeasurableSet {x : VendorPLQuantityCells.cell hlohi p r |
      quantity hlohi p r i x ∈ PLCanonicalEncoding.breakpoints (actualCurve hlohi p r x)} := by
  by_cases hi0 : i = 0
  · subst i
    convert MeasurableSet.empty using 1
    ext x
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    intro h
    have hh := h.1.1
    rw [quantity_first hlohi p r x] at hh
    exact lt_irrefl _ hh
  by_cases hilast : i = Fin.last r.1.val
  · subst i
    convert MeasurableSet.empty using 1
    ext x
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    intro h
    have hh := h.1.2
    rw [quantity_last hlohi p r x] at hh
    exact lt_irrefl _ hh
  have hi : 0 < i.val ∧ i.val < r.1.val := by
    have hi0' : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have hilast' : i.val ≠ r.1.val := fun h => hilast (Fin.ext h)
    have := i.isLt
    omega
  let j : Interior r.1.val := ⟨i, hi⟩
  have haff := measurableSet_affineNear_at_interior hlohi p r j
  have hnonzero : MeasurableSet {x : VendorPLQuantityCells.cell hlohi p r |
      quantity hlohi p r i x ≠ 0} :=
    (measurableSet_eq_fun (measurable_quantity hlohi p r i) measurable_const).compl
  convert hnonzero.inter haff.compl using 1
  ext x
  have hdom : quantity hlohi p r i x ∈
      Ioo (actualCurve hlohi p r x).leftEndpoint (actualCurve hlohi p r x).rightEndpoint := by
    rw [← quantity_first hlohi p r x, ← quantity_last hlohi p r x]
    exact ⟨selectedQuantity_strictMono hlohi p r x (show (0 : Fin (r.1.val + 1)) < i from hi.1),
      selectedQuantity_strictMono hlohi p r x (show i < Fin.last r.1.val from hi.2)⟩
  simp only [PLCanonicalEncoding.breakpoints, mem_setOf_eq, mem_inter_iff, mem_compl_iff,
    j, hdom, true_and]

def leftNodeCoordinates (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    Fin (r.1.val + 2) → ℝ := by
  classical
  exact Fin.cases (actualCurve hlohi p r x).leftEndpoint (fun i =>
    if quantity hlohi p r i x ∈ PLCanonicalEncoding.breakpoints (actualCurve hlohi p r x) ∧
      quantity hlohi p r i x < 0 then quantity hlohi p r i x else 0)

def rightNodeCoordinates (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    Fin (r.1.val + 2) → ℝ := by
  classical
  exact Fin.cases (actualCurve hlohi p r x).rightEndpoint (fun i =>
    if quantity hlohi p r i x ∈ PLCanonicalEncoding.breakpoints (actualCurve hlohi p r x) ∧
      0 < quantity hlohi p r i x then quantity hlohi p r i x else 0)

theorem measurable_leftNodeCoordinates (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) : Measurable (leftNodeCoordinates hlohi p r) := by
  classical
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (measurable_buyDepth hlohi).neg.comp measurable_subtype_coe
  · change Measurable (fun x =>
      if quantity hlohi p r j x ∈ PLCanonicalEncoding.breakpoints (actualCurve hlohi p r x) ∧
        quantity hlohi p r j x < 0 then quantity hlohi p r j x else 0)
    exact (measurable_quantity hlohi p r j).ite
      ((measurableSet_breakpoint_at hlohi p r j).inter
        (measurableSet_lt (measurable_quantity hlohi p r j) measurable_const)) measurable_const

theorem measurable_rightNodeCoordinates (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) : Measurable (rightNodeCoordinates hlohi p r) := by
  classical
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (measurable_sellDepth hlohi).comp measurable_subtype_coe
  · change Measurable (fun x =>
      if quantity hlohi p r j x ∈ PLCanonicalEncoding.breakpoints (actualCurve hlohi p r x) ∧
        0 < quantity hlohi p r j x then quantity hlohi p r j x else 0)
    exact (measurable_quantity hlohi p r j).ite
      ((measurableSet_breakpoint_at hlohi p r j).inter
        (measurableSet_lt measurable_const (measurable_quantity hlohi p r j))) measurable_const

end Thesis.DayAhead.VendorPLBreakpoints

