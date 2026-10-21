import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLCanonicalPieces
import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLPriceEvaluation
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalEndpointAssembly

/-! # Actual full-affine vendor encoding: Borel endpoint assembly and pasting

Every branch used here is an explicit finite comparison cell constructed
from the literal paired cumulative lists. The exact canonical knots are
selected measurable coordinates, and the actual midpoint price is evaluated
at the source's two interior samples on each physical piece. The resulting
two one-sided endpoint vectors reconstruct the actual canonical L² class.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLBorel

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLPriceCells
open VendorPLQuantityCells VendorPLQuantityAffinity VendorPLBreakpoints VendorPLCanonicalNodes
open VendorPLCanonicalPieces VendorPLPriceEvaluation PLCanonicalEncoding PLJoinComparison
open PLCanonicalEndpointAssembly PLCellEndpointEncoding PriceCurves PriceCurveHilbert

variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

theorem measurable_firstSample_price {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → BoundedLayer lo hi ns nb) (hin : Measurable input)
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hda : ∀ w, a w ∈ (book hlohi (input w)).domain)
    (hdb : ∀ w, b w ∈ (book hlohi (input w)).domain) :
    Measurable (fun w => (book hlohi (input w)).price (firstSample (a w) (b w))) := by
  apply measurable_actual_price_family hlohi input hin _
    (((ha.const_mul 2).add hb).div_const 3)
  intro w
  have hA := hda w
  have hB := hdb w
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]

theorem measurable_secondSample_price {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → BoundedLayer lo hi ns nb) (hin : Measurable input)
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hda : ∀ w, a w ∈ (book hlohi (input w)).domain)
    (hdb : ∀ w, b w ∈ (book hlohi (input w)).domain) :
    Measurable (fun w => (book hlohi (input w)).price (secondSample (a w) (b w))) := by
  apply measurable_actual_price_family hlohi input hin _
    ((ha.add (hb.const_mul 2)).div_const 3)
  intro w
  have hA := hda w
  have hB := hdb w
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]

def data (p : VendorPLPriceCells.Pattern ns nb) (r : VendorPLQuantityCells.Pattern p)
    (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : VendorPLCanonicalNodes.cell hlohi p r L R) : Endpoints (L.1.val + R.1.val) :=
  endpointData (actualCurve hlohi p r x.val).price
    (leftKnots hlohi p r L x.val) (rightKnots hlohi p r R x.val)

theorem measurable_data (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2)) :
    Measurable (data hlohi p r L R) := by
  let input (x : VendorPLCanonicalNodes.cell hlohi p r L R) := x.val.val
  have hin : Measurable input := measurable_subtype_coe.comp measurable_subtype_coe
  have hkl (j : Fin (L.1.val + 1)) :
      Measurable (fun x : VendorPLCanonicalNodes.cell hlohi p r L R =>
      leftKnots hlohi p r L x.val j) :=
    ((measurable_pi_apply j).comp (measurable_leftKnots hlohi p r L)).comp measurable_subtype_coe
  have hkr (j : Fin (R.1.val + 1)) :
      Measurable (fun x : VendorPLCanonicalNodes.cell hlohi p r L R =>
      rightKnots hlohi p r R x.val j) :=
    ((measurable_pi_apply j).comp (measurable_rightKnots hlohi p r R)).comp measurable_subtype_coe
  have hdl (j : Fin (L.1.val + 1)) (x : VendorPLCanonicalNodes.cell hlohi p r L R) :
      leftKnots hlohi p r L x.val j ∈ (book hlohi (input x)).domain :=
    leftCoordinate_bounds hlohi p r x.val (L.2 j)
  have hdr (j : Fin (R.1.val + 1)) (x : VendorPLCanonicalNodes.cell hlohi p r L R) :
      rightKnots hlohi p r R x.val j ∈ (book hlohi (input x)).domain :=
    rightCoordinate_bounds hlohi p r x.val (R.2 j)
  apply measurable_endpointData _ _ _ hkl hkr
  · intro j
    exact measurable_firstSample_price hlohi input hin _ _ (hkl j.castSucc) (hkl j.succ)
      (hdl j.castSucc) (hdl j.succ)
  · intro j
    exact measurable_secondSample_price hlohi input hin _ _ (hkl j.castSucc) (hkl j.succ)
      (hdl j.castSucc) (hdl j.succ)
  · intro j
    exact measurable_firstSample_price hlohi input hin _ _ (hkr j.castSucc) (hkr j.succ)
      (hdr j.castSucc) (hdr j.succ)
  · intro j
    exact measurable_secondSample_price hlohi input hin _ _ (hkr j.castSucc) (hkr j.succ)
      (hdr j.castSucc) (hdr j.succ)

theorem actual_canonical_eq_endpoint (μ : Measure Parameter) [IsFiniteMeasure μ] [NoAtoms μ]
    (p : VendorPLPriceCells.Pattern ns nb) (r : VendorPLQuantityCells.Pattern p)
    (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : VendorPLCanonicalNodes.cell hlohi p r L R)
    (hpos : 0 < (book hlohi x.val.val).buyDepth ∧ 0 < (book hlohi x.val.val).sellDepth) :
    PLCanonicalEncoding.encodingLp μ (actualCurve hlohi p r x.val) =
      endpointContinuousLinearMap μ (leftBoundary L.1.val R.1.val)
        (rightBoundary L.1.val R.1.val) (data hlohi p r L R x) := by
  let f := actualCurve hlohi p r x.val
  have hL : leftCount f = L.1.val := leftCount_on_cell hlohi p r L R x
  have hR : rightCount f = R.1.val := rightCount_on_cell hlohi p r L R x
  have hLpos : 0 < L.1.val := hL ▸ leftCount_pos_of_left_neg f (neg_lt_zero.mpr hpos.1)
  have hRpos : 0 < R.1.val := hR ▸ rightCount_pos_of_right_pos f hpos.2
  have hkl (j : Fin (leftCount f + 1)) : leftKnot f j =
      leftKnots hlohi p r L x.val (Fin.cast (congrArg (fun n => n + 1) hL) j) :=
    leftKnot_on_cell hlohi p r L R x (Fin.cast (congrArg (fun n => n + 1) hL) j)
  have hkr (j : Fin (rightCount f + 1)) : rightKnot f j =
      rightKnots hlohi p r R x.val (Fin.cast (congrArg (fun n => n + 1) hR) j) :=
    rightKnot_on_cell hlohi p r L R x (Fin.cast (congrArg (fun n => n + 1) hR) j)
  exact canonical_eq_endpoint_fixed_counts μ f _ _ hL hR hLpos hRpos hkl hkr
    (fixed_left_piece_affine hlohi p r L R x) (fixed_right_piece_affine hlohi p r L R x)


/-- Pasting the explicit canonical-count comparison cells gives Borel
encoding for every measurable family inside a fixed price/quantity cell. -/
theorem measurable_encoding_on_quantity_family
    (μ : Measure Parameter) [IsFiniteMeasure μ] [NoAtoms μ]
    {Ω : Type*} [MeasurableSpace Ω]
    (p : VendorPLPriceCells.Pattern ns nb) (r : VendorPLQuantityCells.Pattern p)
    (input : Ω → VendorPLQuantityCells.cell hlohi p r) (hin : Measurable input)
    (hpos : ∀ w, 0 < (book hlohi (input w).val).buyDepth ∧
      0 < (book hlohi (input w).val).sellDepth) :
    @Measurable Ω (PriceHilbertSpace μ) _ (borel (PriceHilbertSpace μ))
      (fun w => PLCanonicalEncoding.encodingLp μ (actualCurve hlohi p r (input w))) := by
  letI : MeasurableSpace (PriceHilbertSpace μ) := borel (PriceHilbertSpace μ)
  let cells (i : FiniteNodeEnumeration.Pattern (r.1.val + 2) ×
      FiniteNodeEnumeration.Pattern (r.1.val + 2)) :=
    input ⁻¹' VendorPLCanonicalNodes.cell hlohi p r i.1 i.2
  apply measurable_of_countable_cells cells
    (fun i => (VendorPLCanonicalNodes.measurableSet_cell hlohi p r i.1 i.2).preimage hin)
    (fun w => by
      obtain ⟨L, R, h⟩ := VendorPLCanonicalNodes.cell_cover hlohi p r (input w)
      exact ⟨(L,R), h⟩)
  intro i
  let xin (w : cells i) : VendorPLCanonicalNodes.cell hlohi p r i.1 i.2 :=
    ⟨input w.val, w.property⟩
  have hxin : Measurable xin := (hin.comp measurable_subtype_coe).subtype_mk
  have hd : Measurable (fun w : cells i => data hlohi p r i.1 i.2 (xin w)) :=
    (measurable_data hlohi p r i.1 i.2).comp hxin
  convert measurable_endpoint_assembly μ (leftBoundary i.1.1.val i.2.1.val)
    (rightBoundary i.1.1.val i.2.1.val) _ hd using 1
  funext w
  exact actual_canonical_eq_endpoint hlohi μ p r i.1 i.2 (xin w) (hpos w.val)

/-- Full fixed-length paired-list theorem. Price and quantity weak-order
cells, exact breakpoint decisions and canonical-count cells are all derived
from the literal input; no step-input reduction or affine certificate occurs. -/
theorem measurable_encoding_family
    (μ : Measure Parameter) [IsFiniteMeasure μ] [NoAtoms μ]
    {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → BoundedLayer lo hi ns nb) (hin : Measurable input)
    (hpos : ∀ w, 0 < (book hlohi (input w)).buyDepth ∧
      0 < (book hlohi (input w)).sellDepth) :
    @Measurable Ω (PriceHilbertSpace μ) _ (borel (PriceHilbertSpace μ))
      (fun w => PLCanonicalEncoding.encodingLp μ
        (InterpolatedImpactCurve.Book.impactCurve (book hlohi (input w)))) := by
  letI : MeasurableSpace (PriceHilbertSpace μ) := borel (PriceHilbertSpace μ)
  let cells (i : Σ p : VendorPLPriceCells.Pattern ns nb, VendorPLQuantityCells.Pattern p) :=
    input ⁻¹' VendorPLQuantityCells.cell hlohi i.1 i.2
  apply measurable_of_countable_cells cells
    (fun i => (VendorPLQuantityCells.measurableSet_cell hlohi i.1 i.2).preimage hin)
    (fun w => by
      obtain ⟨p, r, h⟩ := VendorPLQuantityCells.cell_cover hlohi (input w)
      exact ⟨⟨p,r⟩, h⟩)
  intro i
  let xin (w : cells i) : VendorPLQuantityCells.cell hlohi i.1 i.2 :=
    ⟨input w.val, w.property⟩
  have hxin : Measurable xin := (hin.comp measurable_subtype_coe).subtype_mk
  exact measurable_encoding_on_quantity_family hlohi μ i.1 i.2 xin hxin
    (fun w => hpos w.val)

def positiveDepths (x : BoundedLayer lo hi ns nb) : Prop :=
  0 < (book hlohi x).buyDepth ∧ 0 < (book hlohi x).sellDepth

abbrev PositiveLayer (lo hi : ℝ) (hlohi : lo ≤ hi) (ns nb : ℕ) :=
  {x : BoundedLayer lo hi ns nb // positiveDepths hlohi x}

/-- Original label: `prop:pl-encoding-measurable`, full fixed-list-length
Hilbert-valued clause, before the separate countable tuple-layer transport. -/
theorem measurable_encoding_positive_layer
    (μ : Measure Parameter) [IsFiniteMeasure μ] [NoAtoms μ] :
    @Measurable (PositiveLayer lo hi hlohi ns nb) (PriceHilbertSpace μ) _
      (borel (PriceHilbertSpace μ))
      (fun x => PLCanonicalEncoding.encodingLp μ
        (InterpolatedImpactCurve.Book.impactCurve (book hlohi x.val))) :=
  measurable_encoding_family hlohi μ _ measurable_subtype_coe (fun x => x.property)

end Thesis.DayAhead.VendorPLBorel

