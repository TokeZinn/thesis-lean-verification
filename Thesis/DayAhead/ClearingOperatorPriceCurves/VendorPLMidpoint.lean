import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLPriceCells
import Thesis.DayAhead.ClearingOperatorPriceCurves.FinitePolygonInverse
import Thesis.DayAhead.ClearingOperatorPriceCurves.FinitePricePathSource

/-! # Borel midpoint prices of the actual paired-list polygon

The completed excess graph is the source finite polygon. Horizontal fibers
are finite unions of singleton/interval slices; finite arithmetic minima
and maxima give their actual midpoint. The source comparison-cell formulas
therefore prove joint Borel dependence without replacing PL input by steps.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLMidpoint

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLPriceCells
open FinitePolygonInverse
open Foundations.MarketRepresentation TuplesMeasurableSorting

variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

abbrev Index (p : VendorPLPriceCells.Pattern ns nb) := Fin (p.1.val + 1) ⊕ Fin p.1.val

def sourceA (p : VendorPLPriceCells.Pattern ns nb) (x : BoundedLayer lo hi ns nb) :
    Index p → ℝ × ℝ
  | .inl i => (selectedPrice hlohi p x i, lowerQuantity hlohi p x i)
  | .inr j => (selectedPrice hlohi p x j.castSucc, upperQuantity hlohi p x j.castSucc)

def sourceB (p : VendorPLPriceCells.Pattern ns nb) (x : BoundedLayer lo hi ns nb) :
    Index p → ℝ × ℝ
  | .inl i => (selectedPrice hlohi p x i, upperQuantity hlohi p x i)
  | .inr j => (selectedPrice hlohi p x j.succ, lowerQuantity hlohi p x j.succ)

def endpointA (p : VendorPLPriceCells.Pattern ns nb) (x : BoundedLayer lo hi ns nb) :
    Fin (Fintype.card (Index p)) → ℝ × ℝ :=
  fun i => sourceA hlohi p x ((Fintype.equivFin (Index p)).symm i)

def endpointB (p : VendorPLPriceCells.Pattern ns nb) (x : BoundedLayer lo hi ns nb) :
    Fin (Fintype.card (Index p)) → ℝ × ℝ :=
  fun i => sourceB hlohi p x ((Fintype.equivFin (Index p)).symm i)

theorem measurable_endpointA (p : VendorPLPriceCells.Pattern ns nb) :
    Measurable (endpointA hlohi p) := by
  apply measurable_pi_lambda
  intro i
  simp only [endpointA]
  generalize (Fintype.equivFin (Index p)).symm i = k
  cases k with
  | inl j =>
    exact (measurable_selectedPrice hlohi p j).prodMk
      (measurable_lowerQuantity hlohi p j)
  | inr j =>
    exact (measurable_selectedPrice hlohi p j.castSucc).prodMk
      (measurable_upperQuantity hlohi p j.castSucc)

theorem measurable_endpointB (p : VendorPLPriceCells.Pattern ns nb) :
    Measurable (endpointB hlohi p) := by
  apply measurable_pi_lambda
  intro i
  simp only [endpointB]
  generalize (Fintype.equivFin (Index p)).symm i = k
  cases k with
  | inl j =>
    exact (measurable_selectedPrice hlohi p j).prodMk
      (measurable_upperQuantity hlohi p j)
  | inr j =>
    exact (measurable_selectedPrice hlohi p j.succ).prodMk
      (measurable_lowerQuantity hlohi p j.succ)

/-- The actual completed inverse fiber is the finite union of the literal
source polygon's segment slices on every fixed price-order cell. -/
theorem actual_levelSet_eq_finite_fiber (p : VendorPLPriceCells.Pattern ns nb)
    (x : VendorPLPriceCells.cell hlohi p) (q : ℝ) :
    CompletedInverse.levelSet lo hi (book hlohi x.val).excess q =
      FinitePolygonInverse.fiber (endpointA hlohi p x.val) (endpointB hlohi p x.val) q := by
  have hpoly := FinitePricePathSource.completedGraph_eq_polygon
    (selectedPrice hlohi p x.val) x.property.1 (book hlohi x.val).excess
    (FinitePricePathSource.book_excess_monotone _) (selectedPrice_excess_affine hlohi p x)
  rw [selectedPrice_first hlohi p x, selectedPrice_last hlohi p x] at hpoly
  ext t
  change (t,q) ∈ FinitePricePathSource.completedGraph lo hi (book hlohi x.val).excess ↔ _
  rw [hpoly, FinitePricePathSource.polygon_eq_iUnion]
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · refine ⟨Fintype.equivFin (Index p) (.inl i), ?_⟩
      simpa only [endpointA, endpointB, Equiv.symm_apply_apply, sourceA, sourceB,
        lowerQuantity, upperQuantity, ← excess_leftLim_eq, ← excess_rightLim_eq,
        FinitePricePathSource.lower, FinitePricePathSource.upper] using hi
    · refine ⟨Fintype.equivFin (Index p) (.inr j), ?_⟩
      simpa only [endpointA, endpointB, Equiv.symm_apply_apply, sourceA, sourceB,
        lowerQuantity, upperQuantity, ← excess_leftLim_eq, ← excess_rightLim_eq,
        FinitePricePathSource.lower, FinitePricePathSource.upper] using hj
  · rintro ⟨i, hi⟩
    generalize he : (Fintype.equivFin (Index p)).symm i = k at hi
    cases k with
    | inl j =>
      left
      refine ⟨j, ?_⟩
      simpa only [endpointA, endpointB, he, sourceA, sourceB,
        lowerQuantity, upperQuantity, ← excess_leftLim_eq, ← excess_rightLim_eq,
        FinitePricePathSource.lower, FinitePricePathSource.upper] using hi
    | inr j =>
      right
      refine ⟨j, ?_⟩
      simpa only [endpointA, endpointB, he, sourceA, sourceB,
        lowerQuantity, upperQuantity, ← excess_leftLim_eq, ← excess_rightLim_eq,
        FinitePricePathSource.lower, FinitePricePathSource.upper] using hi

theorem endpoints_order_bounds (p : VendorPLPriceCells.Pattern ns nb)
    (x : VendorPLPriceCells.cell hlohi p) :
    (∀ i, (endpointA hlohi p x.val i).1 ≤ (endpointB hlohi p x.val i).1) ∧
    (∀ i, (endpointA hlohi p x.val i).2 ≤ (endpointB hlohi p x.val i).2) ∧
    (∀ i, lo ≤ (endpointA hlohi p x.val i).1) ∧
    (∀ i, (endpointB hlohi p x.val i).1 ≤ hi) := by
  have hE := FinitePricePathSource.book_excess_monotone (book hlohi x.val)
  have hpair (i) :
      (endpointA hlohi p x.val i).1 ≤ (endpointB hlohi p x.val i).1 ∧
      (endpointA hlohi p x.val i).2 ≤ (endpointB hlohi p x.val i).2 ∧
      lo ≤ (endpointA hlohi p x.val i).1 ∧ (endpointB hlohi p x.val i).1 ≤ hi := by
    simp only [endpointA, endpointB]
    generalize (Fintype.equivFin (Index p)).symm i = k
    cases k with
    | inl j =>
      change selectedPrice hlohi p x.val j ≤ selectedPrice hlohi p x.val j ∧ _
      refine ⟨le_rfl, ?_, (selectedPrice_bounds hlohi p x.val j).1,
        (selectedPrice_bounds hlohi p x.val j).2⟩
      simpa only [sourceA, sourceB, lowerQuantity, upperQuantity, ← excess_leftLim_eq,
        ← excess_rightLim_eq] using hE.leftLim_le_rightLim (x := selectedPrice hlohi p x.val j)
          (y := selectedPrice hlohi p x.val j) le_rfl
    | inr j =>
      change selectedPrice hlohi p x.val j.castSucc ≤ selectedPrice hlohi p x.val j.succ ∧ _
      refine ⟨x.property.1.monotone (Fin.castSucc_le_succ j), ?_,
        (selectedPrice_bounds hlohi p x.val j.castSucc).1,
        (selectedPrice_bounds hlohi p x.val j.succ).2⟩
      simpa only [sourceA, sourceB, lowerQuantity, upperQuantity, ← excess_leftLim_eq,
        ← excess_rightLim_eq] using hE.rightLim_le_leftLim
          (x.property.1 (Fin.castSucc_lt_succ (i := j)))
  exact ⟨fun i => (hpair i).1, fun i => (hpair i).2.1,
    fun i => (hpair i).2.2.1, fun i => (hpair i).2.2.2⟩

/-- The actual midpoint-selected price equals the finite source arithmetic
formula, including a full price interval at a flat quantity. -/
theorem actual_midpoint_eq (p : VendorPLPriceCells.Pattern ns nb)
    (x : VendorPLPriceCells.cell hlohi p) (q : ℝ) (hq : q ∈ (book hlohi x.val).domain) :
    (book hlohi x.val).price q =
      (finiteLower hi (endpointA hlohi p x.val) (endpointB hlohi p x.val) q +
        finiteUpper lo (endpointA hlohi p x.val) (endpointB hlohi p x.val) q)/2 := by
  have hne := FinitePricePathSource.actual_levelSet_nonempty (book hlohi x.val) q hq
  rw [actual_levelSet_eq_finite_fiber hlohi p x] at hne
  have hb := endpoints_order_bounds hlohi p x
  change (sInf (CompletedInverse.levelSet lo hi (book hlohi x.val).excess q) +
    sSup (CompletedInverse.levelSet lo hi (book hlohi x.val).excess q))/2 = _
  rw [actual_levelSet_eq_finite_fiber hlohi p x,
    sInf_fiber_eq _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 q hne,
    sSup_fiber_eq _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 q hne]

/-- Joint Borel dependence of actual midpoint prices, with a measurable
quantity argument anywhere in the actual available-depth interval. -/
theorem measurable_actual_price_on_cell (p : VendorPLPriceCells.Pattern ns nb)
    (q : VendorPLPriceCells.cell hlohi p → ℝ) (hq : Measurable q)
    (hdom : ∀ x, q x ∈ (book hlohi x.val).domain) :
    Measurable (fun x => (book hlohi x.val).price (q x)) := by
  have ha : Measurable (fun x : VendorPLPriceCells.cell hlohi p =>
      endpointA hlohi p x.val) :=
    (measurable_endpointA hlohi p).comp measurable_subtype_coe
  have hb : Measurable (fun x : VendorPLPriceCells.cell hlohi p =>
      endpointB hlohi p x.val) :=
    (measurable_endpointB hlohi p).comp measurable_subtype_coe
  convert measurable_finiteMidpoint lo hi _ _ q ha hb hq using 1
  funext x
  exact actual_midpoint_eq hlohi p x (q x) (hdom x)


/-- Actual midpoint price evaluation is Borel on an entire fixed raw-list
length layer. The finite price-cell formulas are pasted using their literal
weak-order comparison cover, including duplicate price entries. -/
theorem measurable_actual_price
    (q : BoundedLayer lo hi ns nb → ℝ) (hq : Measurable q)
    (hdom : ∀ x, q x ∈ (book hlohi x).domain) :
    Measurable (fun x => (book hlohi x).price (q x)) := by
  apply measurable_of_measurable_restrict_countable_cover
    (S := fun p : VendorPLPriceCells.Pattern ns nb => VendorPLPriceCells.cell hlohi p)
    (VendorPLPriceCells.measurableSet_cell hlohi) (by
      ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      exact VendorPLPriceCells.cell_cover hlohi x)
  intro p
  exact measurable_actual_price_on_cell hlohi p (fun x => q x.val)
    (hq.comp measurable_subtype_coe) (fun x => hdom x.val)

end Thesis.DayAhead.VendorPLMidpoint

