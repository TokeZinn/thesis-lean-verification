import Thesis.DayAhead.ClearingOperatorPriceCurves.MergedPriceNodes
import Thesis.DayAhead.ClearingOperatorPriceCurves.FiniteNodeEnumeration

/-! # Actual vendor price-grid comparison cells

The source finite weak-order/equality decomposition is instantiated on every
original parsed price coordinate. On each explicit measurable cell, the
intrinsic distinct merged grid is a fixed selection of those coordinates.
Its completed-excess lower/upper vertex coordinates are jointly Borel.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLPriceCells

open Set MeasureTheory VendorPLParser VendorPLVertices

variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

def coordinates (x : BoundedLayer lo hi ns nb) : Fin ((ns + 2) + (nb + 2)) → ℝ :=
  Fin.addCases (book hlohi x).sellPrice (book hlohi x).buyPrice

theorem measurable_coordinates : Measurable (coordinates hlohi (ns := ns) (nb := nb)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [coordinates, Fin.addCases_left] using
      measurable_parsed_sellPrice hlohi ns nb j
  · simpa only [coordinates, Fin.addCases_right] using
      measurable_parsed_buyPrice hlohi ns nb j

theorem coordinate_values_eq (x : BoundedLayer lo hi ns nb) :
    FiniteNodeEnumeration.values (coordinates hlohi x) = MergedPriceNodes.nodes (book hlohi x) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [coordinates, Fin.addCases_left] using
        MergedPriceNodes.sell_mem_nodes (book hlohi x) j
    · simpa only [coordinates, Fin.addCases_right] using
        MergedPriceNodes.buy_mem_nodes (book hlohi x) j
  · intro hp
    rcases Finset.mem_union.mp hp with hs | hb
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_image.mpr
        ⟨Fin.castAdd (nb + 2) j, Finset.mem_univ _, by simp [coordinates]⟩
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr
        ⟨Fin.natAdd (ns + 2) j, Finset.mem_univ _, by simp [coordinates]⟩

abbrev Pattern (ns nb : ℕ) := FiniteNodeEnumeration.Pattern ((ns + 2) + (nb + 2))

def cell (p : Pattern ns nb) : Set (BoundedLayer lo hi ns nb) :=
  FiniteNodeEnumeration.cell (coordinates hlohi) p

theorem measurableSet_cell (p : Pattern ns nb) : MeasurableSet (cell hlohi p) :=
  FiniteNodeEnumeration.measurableSet_cell _ (measurable_coordinates hlohi) p

theorem cell_cover (x : BoundedLayer lo hi ns nb) : ∃ p : Pattern ns nb, x ∈ cell hlohi p :=
  FiniteNodeEnumeration.cell_cover (by omega) (coordinates hlohi) x

def selectedPrice (p : Pattern ns nb) (x : BoundedLayer lo hi ns nb)
    (j : Fin (p.1.val + 1)) : ℝ := coordinates hlohi x (p.2 j)

theorem measurable_selectedPrice (p : Pattern ns nb) (j : Fin (p.1.val + 1)) :
    Measurable (fun x : BoundedLayer lo hi ns nb => selectedPrice hlohi p x j) :=
  (measurable_pi_apply _).comp (measurable_coordinates hlohi)

/-- The source comparison cell determines the exact intrinsic merged-grid
cardinality and the literal coordinate formula at every node. -/
theorem actual_grid_on_cell (p : Pattern ns nb) (x : cell hlohi p) :
    ∃ h : MergedPriceNodes.gapCount (book hlohi x.val) = p.1.val,
      ∀ j : Fin (p.1.val + 1),
        MergedPriceNodes.grid (book hlohi x.val) (Fin.cast (by omega) j) =
          selectedPrice hlohi p x.val j := by
  have hc : (MergedPriceNodes.nodes (book hlohi x.val)).card = p.1.val + 1 := by
    rw [← coordinate_values_eq]
    exact FiniteNodeEnumeration.cardinal_on_cell (coordinates hlohi) p x.property
  have hk : MergedPriceNodes.gapCount (book hlohi x.val) = p.1.val := by
    dsimp [MergedPriceNodes.gapCount, PLCanonicalEncoding.count]
    omega
  refine ⟨hk, fun j => ?_⟩
  have hfs (j : Fin (p.1.val + 1)) :
      selectedPrice hlohi p x.val j ∈ MergedPriceNodes.nodes (book hlohi x.val) := by
    rw [← coordinate_values_eq]
    exact Finset.mem_image.mpr ⟨p.2 j, Finset.mem_univ _, rfl⟩
  have heq : selectedPrice hlohi p x.val =
      (MergedPriceNodes.nodes (book hlohi x.val)).orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc hfs x.property.1
  rw [congrFun heq j]
  exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl

def lowerQuantity (p : Pattern ns nb) (x : BoundedLayer lo hi ns nb)
    (j : Fin (p.1.val + 1)) : ℝ :=
  lowerVertex (book hlohi x) (selectedPrice hlohi p x j)

def upperQuantity (p : Pattern ns nb) (x : BoundedLayer lo hi ns nb)
    (j : Fin (p.1.val + 1)) : ℝ :=
  upperVertex (book hlohi x) (selectedPrice hlohi p x j)

theorem measurable_lowerQuantity (p : Pattern ns nb) (j : Fin (p.1.val + 1)) :
    Measurable (fun x : BoundedLayer lo hi ns nb => lowerQuantity hlohi p x j) :=
  (measurable_vertices hlohi _ (measurable_selectedPrice hlohi p j)).1

theorem measurable_upperQuantity (p : Pattern ns nb) (j : Fin (p.1.val + 1)) :
    Measurable (fun x : BoundedLayer lo hi ns nb => upperQuantity hlohi p x j) :=
  (measurable_vertices hlohi _ (measurable_selectedPrice hlohi p j)).2

/-- The literal completed-graph vertex arrays, including both sides at
price jumps, are finite families of Borel data on every price-order cell. -/
theorem measurable_vertex_arrays (p : Pattern ns nb) :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      (selectedPrice hlohi p x, lowerQuantity hlohi p x, upperQuantity hlohi p x)) :=
  (measurable_pi_lambda _ (measurable_selectedPrice hlohi p)).prodMk
    ((measurable_pi_lambda _ (measurable_lowerQuantity hlohi p)).prodMk
      (measurable_pi_lambda _ (measurable_upperQuantity hlohi p)))


theorem coordinates_bounds (x : BoundedLayer lo hi ns nb)
    (i : Fin ((ns + 2) + (nb + 2))) : coordinates hlohi x i ∈ Icc lo hi := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [coordinates, Fin.addCases_left] using (book hlohi x).sellPrice_bounds j
  · simpa only [coordinates, Fin.addCases_right] using (book hlohi x).buyPrice_bounds j

theorem selectedPrice_bounds (p : Pattern ns nb) (x : BoundedLayer lo hi ns nb)
    (j : Fin (p.1.val + 1)) : selectedPrice hlohi p x j ∈ Icc lo hi :=
  coordinates_bounds hlohi x _

theorem selectedPrice_first (p : Pattern ns nb) (x : cell hlohi p) :
    selectedPrice hlohi p x.val 0 = lo := by
  obtain ⟨j, hj⟩ := x.property.2 (Fin.castAdd (nb+2) (0 : Fin (ns+2)))
  have hzero : coordinates hlohi x.val (Fin.castAdd (nb+2) (0 : Fin (ns+2))) = lo :=
    by simpa only [coordinates, Fin.addCases_left] using (book hlohi x.val).sellPrice_zero
  rw [hzero] at hj
  change lo = selectedPrice hlohi p x.val j at hj
  exact le_antisymm ((x.property.1.monotone (Fin.zero_le j)).trans_eq hj.symm)
    (selectedPrice_bounds hlohi p x.val 0).1

theorem selectedPrice_last (p : Pattern ns nb) (x : cell hlohi p) :
    selectedPrice hlohi p x.val (Fin.last p.1.val) = hi := by
  obtain ⟨j, hj⟩ := x.property.2 (Fin.natAdd (ns+2) (0 : Fin (nb+2)))
  have hzero : coordinates hlohi x.val (Fin.natAdd (ns+2) (0 : Fin (nb+2))) = hi :=
    by simpa only [coordinates, Fin.addCases_right] using (book hlohi x.val).buyPrice_zero
  rw [hzero] at hj
  change hi = selectedPrice hlohi p x.val j at hj
  exact le_antisymm (selectedPrice_bounds hlohi p x.val _).2
    (hj.trans_le (x.property.1.monotone (Fin.le_last j)))

/-- The same literal affine-gap proof applies directly to the fixed selected
coordinates on a comparison cell; no dependent grid cast is required. -/
theorem selectedPrice_excess_affine (p : Pattern ns nb) (x : cell hlohi p)
    (j : Fin p.1.val) :
    ∃ A B : ℝ, ∀ t ∈ Ioo (selectedPrice hlohi p x.val j.castSucc)
      (selectedPrice hlohi p x.val j.succ), (book hlohi x.val).excess t = A*t+B := by
  apply PriceNodeGaps.excess_affine_on_gap (book hlohi x.val)
    (x.property.1 (Fin.castSucc_lt_succ (i := j)))
  · intro i hi
    obtain ⟨k, hk⟩ := x.property.2 (Fin.castAdd (nb+2) i)
    have heq : (book hlohi x.val).sellPrice i = selectedPrice hlohi p x.val k := by
      simpa only [coordinates, selectedPrice, Fin.addCases_left, Fin.addCases_right] using hk
    rw [heq] at hi
    exact OfferedPartition.node_not_open (selectedPrice hlohi p x.val)
      x.property.1.monotone k j hi
  · intro i hi
    obtain ⟨k, hk⟩ := x.property.2 (Fin.natAdd (ns+2) i)
    have heq : (book hlohi x.val).buyPrice i = selectedPrice hlohi p x.val k := by
      simpa only [coordinates, selectedPrice, Fin.addCases_left, Fin.addCases_right] using hk
    rw [heq] at hi
    exact OfferedPartition.node_not_open (selectedPrice hlohi p x.val)
      x.property.1.monotone k j hi

end Thesis.DayAhead.VendorPLPriceCells

