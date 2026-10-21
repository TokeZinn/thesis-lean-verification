import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLQuantityCells
import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLMidpoint
import Thesis.DayAhead.ClearingOperatorPriceCurves.FinitePolygonInverseAffinity

/-! # Actual vendor midpoint affinity on the source quantity grid

Every genuine polygon-vertex quantity occurs in the explicitly compared
quantity array. A consecutive distinct quantity gap therefore contains no
vertex; transposition of the actual completed polygon gives one affine
price formula throughout that gap.
-/

noncomputable section
namespace Thesis.DayAhead.VendorPLQuantityAffinity

open Set VendorPLParser VendorPLPriceCells VendorPLQuantityCells VendorPLMidpoint
open VendorPLVertices
open FinitePricePathSource FinitePolygonInverseAffinity

variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

theorem endpoint_quantities_covered (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r) :
    (∀ i, ∃ k, selectedQuantity hlohi p r x.val k = (endpointA hlohi p x.val i).2) ∧
    (∀ i, ∃ k, selectedQuantity hlohi p r x.val k = (endpointB hlohi p x.val i).2) := by
  constructor <;> intro i
  · simp only [endpointA]
    generalize (Fintype.equivFin (Index p)).symm i = k
    cases k with
    | inl j =>
      simpa only [sourceA, lowerQuantity, ← excess_leftLim_eq] using
        lower_vertices_covered hlohi p r x j
    | inr j =>
      simpa only [sourceA, upperQuantity, ← excess_rightLim_eq] using
        upper_vertices_covered hlohi p r x j.castSucc
  · simp only [endpointB]
    generalize (Fintype.equivFin (Index p)).symm i = k
    cases k with
    | inl j =>
      simpa only [sourceB, upperQuantity, ← excess_rightLim_eq] using
        upper_vertices_covered hlohi p r x j
    | inr j =>
      simpa only [sourceB, lowerQuantity, ← excess_leftLim_eq] using
        lower_vertices_covered hlohi p r x j.succ

theorem actual_price_affine (p : VendorPLPriceCells.Pattern ns nb)
    (r : VendorPLQuantityCells.Pattern p) (x : VendorPLQuantityCells.cell hlohi p r)
    (j : Fin r.1.val) :
    ∃ A B : ℝ, ∀ q ∈ Ioo (selectedQuantity hlohi p r x.val j.castSucc)
      (selectedQuantity hlohi p r x.val j.succ), (book hlohi x.val).price q = A * q + B := by
  let xp : VendorPLPriceCells.cell hlohi p := ⟨x.val, x.property.1⟩
  have hbound := endpoints_order_bounds hlohi p xp
  have hgraph : completedGraph lo hi (book hlohi x.val).excess =
      ⋃ i, segment ℝ (endpointA hlohi p x.val i) (endpointB hlohi p x.val i) := by
    ext ⟨price, quantity⟩
    change price ∈ CompletedInverse.levelSet lo hi (book hlohi x.val).excess quantity ↔ _
    rw [actual_levelSet_eq_finite_fiber hlohi p xp]
    simp only [FinitePolygonInverse.fiber, mem_setOf_eq, mem_iUnion]
    rfl
  have hstrict := selectedQuantity_strictMono hlohi p r x
  have hgap := hstrict (Fin.castSucc_lt_succ (i := j))
  have hvertices : ∀ i,
      (endpointA hlohi p x.val i).2 ∉ Ioo (selectedQuantity hlohi p r x.val j.castSucc)
        (selectedQuantity hlohi p r x.val j.succ) ∧
      (endpointB hlohi p x.val i).2 ∉ Ioo (selectedQuantity hlohi p r x.val j.castSucc)
        (selectedQuantity hlohi p r x.val j.succ) := by
    intro i
    obtain ⟨ka, hka⟩ := (endpoint_quantities_covered hlohi p r x).1 i
    obtain ⟨kb, hkb⟩ := (endpoint_quantities_covered hlohi p r x).2 i
    constructor
    · rw [← hka]
      exact OfferedPartition.node_not_open _ hstrict.monotone ka j
    · rw [← hkb]
      exact OfferedPartition.node_not_open _ hstrict.monotone kb j
  have hleft := selectedQuantity_bounds hlohi p r x.val j.castSucc
  have hright := selectedQuantity_bounds hlohi p r x.val j.succ
  have hmid : (selectedQuantity hlohi p r x.val j.castSucc +
      selectedQuantity hlohi p r x.val j.succ) / 2 ∈ (book hlohi x.val).domain := by
    constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]
  exact midpoint_affine_on_vertex_gap (book_excess_monotone (book hlohi x.val))
    (endpointA hlohi p x.val) (endpointB hlohi p x.val) hbound.1 hbound.2.1 hgraph hgap
    hvertices (actual_levelSet_nonempty (book hlohi x.val) _ hmid)

end Thesis.DayAhead.VendorPLQuantityAffinity
