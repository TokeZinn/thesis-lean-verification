import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLPriceCells

/-! # Explicit Borel quantity-order cells of the actual vendor polygon

The candidate array contains both one-sided excess values at every original
price node, both depth endpoints, and the source-sided origin. Distinct-value
enumeration is by explicit finite equality/order cells, ready for jump and
collinearity comparisons. No canonical-breakpoint identification is assumed.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLQuantityCells

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLPriceCells

variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

def quantities (p : VendorPLPriceCells.Pattern ns nb) (x : BoundedLayer lo hi ns nb) :
    Fin ((3 + (p.1.val + 1)) + (p.1.val + 1)) → ℝ :=
  Fin.addCases
    (Fin.addCases ![-(book hlohi x).buyDepth, 0, (book hlohi x).sellDepth]
      (lowerQuantity hlohi p x))
    (upperQuantity hlohi p x)

theorem measurable_buyDepth :
    Measurable (fun x : BoundedLayer lo hi ns nb => (book hlohi x).buyDepth) :=
  measurable_parsed_buyCumulative hlohi ns nb (Fin.last _)

theorem measurable_sellDepth :
    Measurable (fun x : BoundedLayer lo hi ns nb => (book hlohi x).sellDepth) :=
  measurable_parsed_sellCumulative hlohi ns nb (Fin.last _)

theorem measurable_quantities (p : VendorPLPriceCells.Pattern ns nb) :
    Measurable (quantities hlohi p) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · fin_cases j
      · simpa only [quantities, Fin.addCases_left, Matrix.cons_val_zero] using
          (measurable_buyDepth hlohi).neg
      · simpa only [quantities, Fin.addCases_left, Matrix.cons_val_succ,
          Matrix.cons_val_zero] using
          (measurable_const : Measurable (fun _ : BoundedLayer lo hi ns nb => (0 : ℝ)))
      · simpa only [quantities, Fin.addCases_left, Matrix.cons_val_succ,
          Matrix.cons_val_zero] using measurable_sellDepth hlohi
    · simpa only [quantities, Fin.addCases_left, Fin.addCases_right] using
        measurable_lowerQuantity hlohi p j
  · simpa only [quantities, Fin.addCases_right] using
      measurable_upperQuantity hlohi p j

abbrev Pattern (p : VendorPLPriceCells.Pattern ns nb) :=
  FiniteNodeEnumeration.Pattern ((3 + (p.1.val + 1)) + (p.1.val + 1))

def cell (p : VendorPLPriceCells.Pattern ns nb) (r : Pattern p) :
    Set (BoundedLayer lo hi ns nb) :=
  VendorPLPriceCells.cell hlohi p ∩ FiniteNodeEnumeration.cell (quantities hlohi p) r

theorem measurableSet_cell (p : VendorPLPriceCells.Pattern ns nb) (r : Pattern p) :
    MeasurableSet (cell hlohi p r) :=
  (VendorPLPriceCells.measurableSet_cell hlohi p).inter
    (FiniteNodeEnumeration.measurableSet_cell _ (measurable_quantities hlohi p) r)

/-- Every literal vendor list lies in a finite price comparison cell and a
finite quantity comparison cell constructed from its actual one-sided excess
vertices. The finite branch data depend only on exact comparisons. -/
theorem cell_cover (x : BoundedLayer lo hi ns nb) :
    ∃ p : VendorPLPriceCells.Pattern ns nb, ∃ r : Pattern p, x ∈ cell hlohi p r := by
  obtain ⟨p, hp⟩ := VendorPLPriceCells.cell_cover hlohi x
  obtain ⟨r, hr⟩ := FiniteNodeEnumeration.cell_cover (by omega) (quantities hlohi p) x
  exact ⟨p, r, hp, hr⟩

def selectedQuantity (p : VendorPLPriceCells.Pattern ns nb) (r : Pattern p)
    (x : BoundedLayer lo hi ns nb) (j : Fin (r.1.val + 1)) : ℝ :=
  quantities hlohi p x (r.2 j)

theorem measurable_selectedQuantity (p : VendorPLPriceCells.Pattern ns nb)
    (r : Pattern p) (j : Fin (r.1.val + 1)) :
    Measurable (fun x : BoundedLayer lo hi ns nb => selectedQuantity hlohi p r x j) :=
  (measurable_pi_apply _).comp (measurable_quantities hlohi p)

theorem selectedQuantity_strictMono (p : VendorPLPriceCells.Pattern ns nb)
    (r : Pattern p) (x : cell hlohi p r) :
    StrictMono (selectedQuantity hlohi p r x.val) := x.property.2.1


theorem vertex_bounds (m : ExcessSupply.Book lo hi) (price : ℝ) :
    lowerVertex m price ∈ m.domain ∧ upperVertex m price ∈ m.domain := by
  have hb : ∀ t, m.excess t ∈ Icc (-m.buyDepth) m.sellDepth := fun t =>
    ExcessSupply.excess_bounds _ _ m.sellDepth_nonneg m.buyDepth_nonneg _ _ t
  exact ⟨isClosed_Icc.mem_of_tendsto (excess_tendsto_left m price)
    (Filter.Eventually.of_forall hb),
    isClosed_Icc.mem_of_tendsto (excess_tendsto_right m price)
      (Filter.Eventually.of_forall hb)⟩

theorem quantities_bounds (p : VendorPLPriceCells.Pattern ns nb)
    (x : BoundedLayer lo hi ns nb)
    (i : Fin ((3 + (p.1.val + 1)) + (p.1.val + 1))) :
    quantities hlohi p x i ∈ (book hlohi x).domain := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · fin_cases j
      · have hb : -(book hlohi x).buyDepth ∈ (book hlohi x).domain :=
          ⟨le_rfl, (neg_nonpos.mpr (book hlohi x).buyDepth_nonneg).trans
            (book hlohi x).sellDepth_nonneg⟩
        simpa [quantities] using hb
      · simpa [quantities] using (book hlohi x).zero_mem_domain
      · have hb : (book hlohi x).sellDepth ∈ (book hlohi x).domain :=
          ⟨(neg_nonpos.mpr (book hlohi x).buyDepth_nonneg).trans
            (book hlohi x).sellDepth_nonneg, le_rfl⟩
        simpa [quantities] using hb
    · simpa only [quantities, Fin.addCases_left, Fin.addCases_right,
        lowerQuantity] using (vertex_bounds (book hlohi x) (selectedPrice hlohi p x j)).1
  · simpa only [quantities, Fin.addCases_right, upperQuantity] using
      (vertex_bounds (book hlohi x) (selectedPrice hlohi p x j)).2

theorem selectedQuantity_bounds (p : VendorPLPriceCells.Pattern ns nb)
    (r : Pattern p) (x : BoundedLayer lo hi ns nb) (j : Fin (r.1.val + 1)) :
    selectedQuantity hlohi p r x j ∈ (book hlohi x).domain :=
  quantities_bounds hlohi p x _

theorem lower_vertices_covered (p : VendorPLPriceCells.Pattern ns nb)
    (r : Pattern p) (x : cell hlohi p r) (i : Fin (p.1.val + 1)) :
    ∃ j, selectedQuantity hlohi p r x.val j =
      (book hlohi x.val).excess.leftLim (selectedPrice hlohi p x.val i) := by
  obtain ⟨j, hj⟩ := x.property.2.2
    (Fin.castAdd (p.1.val + 1) (Fin.natAdd 3 i))
  refine ⟨j, ?_⟩
  simpa only [quantities, Fin.addCases_left, Fin.addCases_right, selectedQuantity,
    lowerQuantity, ← excess_leftLim_eq] using hj.symm

theorem upper_vertices_covered (p : VendorPLPriceCells.Pattern ns nb)
    (r : Pattern p) (x : cell hlohi p r) (i : Fin (p.1.val + 1)) :
    ∃ j, selectedQuantity hlohi p r x.val j =
      (book hlohi x.val).excess.rightLim (selectedPrice hlohi p x.val i) := by
  obtain ⟨j, hj⟩ := x.property.2.2 (Fin.natAdd (3 + (p.1.val + 1)) i)
  refine ⟨j, ?_⟩
  simpa only [quantities, Fin.addCases_right, selectedQuantity,
    upperQuantity, ← excess_rightLim_eq] using hj.symm


theorem selectedQuantity_first (p : VendorPLPriceCells.Pattern ns nb)
    (r : Pattern p) (x : cell hlohi p r) :
    selectedQuantity hlohi p r x.val 0 = -(book hlohi x.val).buyDepth := by
  let i := Fin.castAdd (p.1.val + 1) (Fin.castAdd (p.1.val + 1) (0 : Fin 3))
  have hstart : quantities hlohi p x.val i = -(book hlohi x.val).buyDepth := by
    simp [quantities, i]
  obtain ⟨j, hj⟩ := x.property.2.2 i
  rw [hstart] at hj
  change -(book hlohi x.val).buyDepth = selectedQuantity hlohi p r x.val j at hj
  exact le_antisymm
    (((selectedQuantity_strictMono hlohi p r x).monotone (Fin.zero_le j)).trans_eq hj.symm)
    (selectedQuantity_bounds hlohi p r x.val 0).1

theorem selectedQuantity_last (p : VendorPLPriceCells.Pattern ns nb)
    (r : Pattern p) (x : cell hlohi p r) :
    selectedQuantity hlohi p r x.val (Fin.last r.1.val) = (book hlohi x.val).sellDepth := by
  let i := Fin.castAdd (p.1.val + 1) (Fin.castAdd (p.1.val + 1) (2 : Fin 3))
  have hstart : quantities hlohi p x.val i = (book hlohi x.val).sellDepth := by
    simp [quantities, i]
  obtain ⟨j, hj⟩ := x.property.2.2 i
  rw [hstart] at hj
  change (book hlohi x.val).sellDepth = selectedQuantity hlohi p r x.val j at hj
  exact le_antisymm (selectedQuantity_bounds hlohi p r x.val _).2
    (hj.trans_le ((selectedQuantity_strictMono hlohi p r x).monotone (Fin.le_last j)))

theorem origin_covered (p : VendorPLPriceCells.Pattern ns nb)
    (r : Pattern p) (x : cell hlohi p r) :
    ∃ j, selectedQuantity hlohi p r x.val j = 0 := by
  let i := Fin.castAdd (p.1.val + 1) (Fin.castAdd (p.1.val + 1) (1 : Fin 3))
  have hstart : quantities hlohi p x.val i = 0 := by simp [quantities, i]
  obtain ⟨j, hj⟩ := x.property.2.2 i
  exact ⟨j, hj.symm.trans hstart⟩

end Thesis.DayAhead.VendorPLQuantityCells


