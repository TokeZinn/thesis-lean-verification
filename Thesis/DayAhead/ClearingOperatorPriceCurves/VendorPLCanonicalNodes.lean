import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLBreakpoints

/-! # Literal canonical-node arrays from the vendor comparison cells

Every intrinsic breakpoint is an actual transposed-polygon candidate. The
Borel local-affinity decision filters that finite array, retaining the sided
origin and physical endpoints. The resulting finite value sets are exactly
the canonical leftNodes and rightNodes; redundant affine joins are removed.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLCanonicalNodes

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLPriceCells
open VendorPLQuantityCells VendorPLQuantityAffinity VendorPLBreakpoints PLCanonicalEncoding

variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

theorem breakpoints_covered (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    breakpoints (actualCurve hlohi p r x) ⊆ Set.range (fun i => quantity hlohi p r i x) := by
  apply PLBreakpointGrid.breakpoints_subset_grid (actualCurve hlohi p r x)
    (fun i => quantity hlohi p r i x) (quantity_first hlohi p r x) (quantity_last hlohi p r x)
  intro j
  exact actual_price_affine hlohi p r x j

theorem left_coordinates_values (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    FiniteNodeEnumeration.values (leftNodeCoordinates hlohi p r x) =
      leftNodes (actualCurve hlohi p r x) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [leftNodeCoordinates, leftNodes]
    · change (if quantity hlohi p r j x ∈ breakpoints (actualCurve hlohi p r x) ∧
        quantity hlohi p r j x < 0 then quantity hlohi p r j x else 0) ∈ _
      split_ifs with h
      · simp only [leftNodes, Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact Or.inr (Or.inr h)
      · simp [leftNodes]
  · intro hq
    simp only [leftNodes, Finset.mem_insert, Finset.mem_filter,
      Set.Finite.mem_toFinset] at hq
    rcases hq with rfl | rfl | hq
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · obtain ⟨j, hj⟩ := origin_covered hlohi p r x
      refine Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, ?_⟩
      simp only [leftNodeCoordinates, Fin.cases_succ]
      have hj' : quantity hlohi p r j x = 0 := hj
      rw [hj']
      simp
    · obtain ⟨j, hj⟩ := breakpoints_covered hlohi p r x hq.1
      change quantity hlohi p r j x = q at hj
      refine Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, ?_⟩
      simp only [leftNodeCoordinates, Fin.cases_succ]
      rw [hj, if_pos hq]

theorem right_coordinates_values (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    FiniteNodeEnumeration.values (rightNodeCoordinates hlohi p r x) =
      rightNodes (actualCurve hlohi p r x) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rightNodeCoordinates, rightNodes]
    · change (if quantity hlohi p r j x ∈ breakpoints (actualCurve hlohi p r x) ∧
        0 < quantity hlohi p r j x then quantity hlohi p r j x else 0) ∈ _
      split_ifs with h
      · simp only [rightNodes, Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact Or.inr (Or.inr h)
      · simp [rightNodes]
  · intro hq
    simp only [rightNodes, Finset.mem_insert, Finset.mem_filter,
      Set.Finite.mem_toFinset] at hq
    rcases hq with rfl | rfl | hq
    · obtain ⟨j, hj⟩ := origin_covered hlohi p r x
      refine Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, ?_⟩
      simp only [rightNodeCoordinates, Fin.cases_succ]
      have hj' : quantity hlohi p r j x = 0 := hj
      rw [hj']
      simp
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · obtain ⟨j, hj⟩ := breakpoints_covered hlohi p r x hq.1
      change quantity hlohi p r j x = q at hj
      refine Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, ?_⟩
      simp only [rightNodeCoordinates, Fin.cases_succ]
      rw [hj, if_pos hq]

/-- The final source refinement fixes the canonical negative and positive
piece counts by explicit finite order/equality cells of the filtered arrays. -/
def cell (p : VendorPLPriceCells.Pattern ns nb) (r : VendorPLQuantityCells.Pattern p)
    (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2)) :
    Set (VendorPLQuantityCells.cell hlohi p r) :=
  FiniteNodeEnumeration.cell (leftNodeCoordinates hlohi p r) L ∩
    FiniteNodeEnumeration.cell (rightNodeCoordinates hlohi p r) R

theorem measurableSet_cell (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2)) :
    MeasurableSet (cell hlohi p r L R) :=
  (FiniteNodeEnumeration.measurableSet_cell _ (measurable_leftNodeCoordinates hlohi p r) L).inter
    (FiniteNodeEnumeration.measurableSet_cell _ (measurable_rightNodeCoordinates hlohi p r) R)

theorem cell_cover (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    ∃ L R, x ∈ cell hlohi p r L R := by
  obtain ⟨L, hL⟩ := FiniteNodeEnumeration.cell_cover (by omega) (leftNodeCoordinates hlohi p r) x
  obtain ⟨R, hR⟩ := FiniteNodeEnumeration.cell_cover (by omega) (rightNodeCoordinates hlohi p r) x
  exact ⟨L, R, hL, hR⟩


def leftKnots (p : VendorPLPriceCells.Pattern ns nb) (r : VendorPLQuantityCells.Pattern p)
    (L : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : VendorPLQuantityCells.cell hlohi p r) : Fin (L.1.val + 1) → ℝ :=
  fun i => leftNodeCoordinates hlohi p r x (L.2 i)

def rightKnots (p : VendorPLPriceCells.Pattern ns nb) (r : VendorPLQuantityCells.Pattern p)
    (R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : VendorPLQuantityCells.cell hlohi p r) : Fin (R.1.val + 1) → ℝ :=
  fun i => rightNodeCoordinates hlohi p r x (R.2 i)

theorem measurable_leftKnots (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L : FiniteNodeEnumeration.Pattern (r.1.val + 2)) :
    Measurable (leftKnots hlohi p r L) :=
  measurable_pi_lambda _ fun i =>
    (measurable_pi_apply (L.2 i)).comp (measurable_leftNodeCoordinates hlohi p r)

theorem measurable_rightKnots (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (R : FiniteNodeEnumeration.Pattern (r.1.val + 2)) :
    Measurable (rightKnots hlohi p r R) :=
  measurable_pi_lambda _ fun i =>
    (measurable_pi_apply (R.2 i)).comp (measurable_rightNodeCoordinates hlohi p r)

theorem leftCount_on_cell (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : cell hlohi p r L R) : leftCount (actualCurve hlohi p r x.val) = L.1.val := by
  have hc : (leftNodes (actualCurve hlohi p r x.val)).card = L.1.val + 1 := by
    rw [← left_coordinates_values]
    exact FiniteNodeEnumeration.cardinal_on_cell _ L x.property.1
  dsimp [leftCount, count]
  omega

theorem rightCount_on_cell (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : cell hlohi p r L R) : rightCount (actualCurve hlohi p r x.val) = R.1.val := by
  have hc : (rightNodes (actualCurve hlohi p r x.val)).card = R.1.val + 1 := by
    rw [← right_coordinates_values]
    exact FiniteNodeEnumeration.cardinal_on_cell _ R x.property.2
  dsimp [rightCount, count]
  omega

theorem leftKnot_on_cell (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : cell hlohi p r L R) (j : Fin (L.1.val + 1)) :
    leftKnot (actualCurve hlohi p r x.val)
      (Fin.cast (by rw [leftCount_on_cell hlohi p r L R x]) j) = leftKnots hlohi p r L x.val j := by
  have hc : (leftNodes (actualCurve hlohi p r x.val)).card = L.1.val + 1 := by
    rw [← left_coordinates_values]
    exact FiniteNodeEnumeration.cardinal_on_cell _ L x.property.1
  have hm (i : Fin (L.1.val + 1)) :
      leftKnots hlohi p r L x.val i ∈ leftNodes (actualCurve hlohi p r x.val) := by
    rw [← left_coordinates_values]
    exact Finset.mem_image.mpr ⟨L.2 i, Finset.mem_univ _, rfl⟩
  have heq : leftKnots hlohi p r L x.val =
      (leftNodes (actualCurve hlohi p r x.val)).orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc hm x.property.1.1
  rw [congrFun heq j]
  exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl

theorem rightKnot_on_cell (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (L R : FiniteNodeEnumeration.Pattern (r.1.val + 2))
    (x : cell hlohi p r L R) (j : Fin (R.1.val + 1)) :
    rightKnot (actualCurve hlohi p r x.val)
      (Fin.cast (by rw [rightCount_on_cell hlohi p r L R x]) j) =
      rightKnots hlohi p r R x.val j := by
  have hc : (rightNodes (actualCurve hlohi p r x.val)).card = R.1.val + 1 := by
    rw [← right_coordinates_values]
    exact FiniteNodeEnumeration.cardinal_on_cell _ R x.property.2
  have hm (i : Fin (R.1.val + 1)) :
      rightKnots hlohi p r R x.val i ∈ rightNodes (actualCurve hlohi p r x.val) := by
    rw [← right_coordinates_values]
    exact Finset.mem_image.mpr ⟨R.2 i, Finset.mem_univ _, rfl⟩
  have heq : rightKnots hlohi p r R x.val =
      (rightNodes (actualCurve hlohi p r x.val)).orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc hm x.property.2.1
  rw [congrFun heq j]
  exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl

theorem leftCoordinate_bounds (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r)
    (i : Fin (r.1.val + 2)) : leftNodeCoordinates hlohi p r x i ∈ (book hlohi x.val).domain := by
  classical
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨le_rfl, (neg_nonpos.mpr (book hlohi x.val).buyDepth_nonneg).trans
      (book hlohi x.val).sellDepth_nonneg⟩
  · change (if quantity hlohi p r j x ∈ breakpoints (actualCurve hlohi p r x) ∧
        quantity hlohi p r j x < 0 then quantity hlohi p r j x else 0) ∈ _
    split_ifs
    · exact selectedQuantity_bounds hlohi p r x.val j
    · exact (book hlohi x.val).zero_mem_domain

theorem rightCoordinate_bounds (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r)
    (i : Fin (r.1.val + 2)) : rightNodeCoordinates hlohi p r x i ∈ (book hlohi x.val).domain := by
  classical
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨(neg_nonpos.mpr (book hlohi x.val).buyDepth_nonneg).trans
      (book hlohi x.val).sellDepth_nonneg, le_rfl⟩
  · change (if quantity hlohi p r j x ∈ breakpoints (actualCurve hlohi p r x) ∧
        0 < quantity hlohi p r j x then quantity hlohi p r j x else 0) ∈ _
    split_ifs
    · exact selectedQuantity_bounds hlohi p r x.val j
    · exact (book hlohi x.val).zero_mem_domain

end Thesis.DayAhead.VendorPLCanonicalNodes

