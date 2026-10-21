import Thesis.DayAhead.ClearingOperatorPriceCurves.EquilibriumQuantity
import Mathlib.MeasureTheory.Order.Lattice

/-! # Finite arithmetic formula for actual interpolated acceptance

Each positive-width quantity cell contributes its largest accepted point,
when nonempty. The accepted-volume supremum is the maximum of these finitely
many candidates and zero. This is the local affine/constant formula used by
the source finite comparison-cell proof, derived for the actual accepted set.
-/
noncomputable section
namespace Thesis.DayAhead.InterpolatedAcceptanceFormula

open Set MeasureTheory InterpolatedSide InterpolatedOffered ExcessSupply EquilibriumQuantity

/-- The right-selected accepted endpoint of one quantity cell. -/
def cellEndpoint (l r a b level : ℝ) : ℝ :=
  if l < r ∧ a ≤ level then
    if b ≤ level then r else interpolate a b l r level
  else 0

theorem cellEndpoint_nonneg {l r a b level : ℝ} (hl : 0 ≤ l) (_hab : a ≤ b) :
    0 ≤ cellEndpoint l r a b level := by
  unfold cellEndpoint
  split_ifs with hw hb
  · exact hl.trans hw.1.le
  · have ha : a < b := hw.2.trans_lt (lt_of_not_ge hb)
    exact hl.trans (interpolate_mem_Icc ha ⟨hw.2, (lt_of_not_ge hb).le⟩ hw.1.le).1
  · exact le_rfl

/-- A nonzero cell endpoint is an actual point of the closed accepted cell. -/
theorem cellEndpoint_mem {n : ℕ} (p Q : Fin (n + 1) → ℝ) (level : ℝ) (j : Fin n)
    (_hp : Monotone p) :
    cellEndpoint (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) level = 0 ∨
      cellEndpoint (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) level ∈
        closedAcceptedCell p Q level j := by
  unfold cellEndpoint
  split_ifs with h hpmax
  · right
    rw [closedAcceptedCell, if_pos h.1]
    refine ⟨⟨h.1.le, le_rfl⟩, ?_⟩
    have he : interpolate (Q j.castSucc) (Q j.succ)
        (p j.castSucc) (p j.succ) (Q j.succ) = p j.succ := by
      unfold interpolate
      field_simp [sub_ne_zero.mpr h.1.ne']
      ring
    change interpolate (Q j.castSucc) (Q j.succ)
      (p j.castSucc) (p j.succ) (Q j.succ) ≤ level
    rw [he]
    exact hpmax
  · right
    rw [closedAcceptedCell, if_pos h.1]
    have hprice : p j.castSucc < p j.succ := h.2.trans_lt (lt_of_not_ge hpmax)
    exact ⟨interpolate_mem_Icc hprice ⟨h.2, (lt_of_not_ge hpmax).le⟩ h.1.le,
      (interpolate_inverse h.1.ne hprice.ne level).le⟩
  · exact Or.inl rfl

/-- Every accepted point of a quantity cell lies below its arithmetic endpoint. -/
theorem closedCell_le_endpoint {n : ℕ} (p Q : Fin (n + 1) → ℝ) (level : ℝ) (j : Fin n)
    (hp : Monotone p) {q : ℝ} (hq : q ∈ closedAcceptedCell p Q level j) :
    q ≤ cellEndpoint (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) level := by
  by_cases hw : Q j.castSucc < Q j.succ
  · rw [closedAcceptedCell, if_pos hw] at hq
    have hpl : p j.castSucc ≤ level :=
      (interpolate_mem_Icc hw hq.1 (hp (Fin.castSucc_le_succ j))).1.trans hq.2
    rw [cellEndpoint, if_pos ⟨hw, hpl⟩]
    split_ifs with hpr
    · exact hq.1.2
    · have hprice : p j.castSucc < p j.succ := hpl.trans_lt (lt_of_not_ge hpr)
      apply (interpolate_strictMono hw hprice).le_iff_le.mp
      rw [interpolate_inverse hw.ne hprice.ne level]
      exact hq.2
  · simp [closedAcceptedCell, hw] at hq

def finiteAccepted {n : ℕ} (p Q : Fin (n + 1) → ℝ) (level : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1))).sup' (by simp)
    (Fin.cases 0 (fun j =>
      cellEndpoint (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) level))

theorem zero_le_finiteAccepted {n : ℕ} (p Q : Fin (n + 1) → ℝ) (level : ℝ) :
    0 ≤ finiteAccepted p Q level :=
  by
    simpa only [finiteAccepted, Fin.cases_zero] using
      (Finset.le_sup' (Fin.cases 0 (fun j =>
        cellEndpoint (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) level))
        (Finset.mem_univ (0 : Fin (n + 1))))

theorem endpoint_le_finiteAccepted {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (level : ℝ) (j : Fin n) :
    cellEndpoint (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) level ≤
      finiteAccepted p Q level :=
  by
    simpa only [finiteAccepted, Fin.cases_succ] using
      (Finset.le_sup' (Fin.cases 0 (fun j =>
        cellEndpoint (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) level))
        (Finset.mem_univ j.succ))

/-- The actual supremum-defined accepted volume equals the finite maximum
used by the source algebraic comparison cells; zero-volume cells contribute0. -/
theorem offered_eq_finiteAccepted {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (level : ℝ) :
    offered (Q (Fin.last n)) (curve p Q) level = finiteAccepted p Q level := by
  have hdepth : 0 ≤ Q (Fin.last n) := hz ▸ hQ (Fin.zero_le _)
  apply le_antisymm
  · apply csSup_le (offeredSet_nonempty _ _ _)
    intro q hq
    rw [offeredSet_eq_closed_cells p Q hp hQ hz] at hq
    rcases hq with rfl | hq
    · exact zero_le_finiteAccepted p Q level
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hq
      exact (closedCell_le_endpoint p Q level j hp hj).trans
        (endpoint_le_finiteAccepted p Q level j)
  · apply Finset.sup'_le
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_csSup (offeredSet_bddAbove _ hdepth _ _) (Or.inl rfl)
    · apply le_csSup (offeredSet_bddAbove _ hdepth _ _)
      rw [offeredSet_eq_closed_cells p Q hp hQ hz]
      rcases cellEndpoint_mem p Q level j hp with hzero | hmem
      · exact Or.inl hzero
      · exact Or.inr (mem_iUnion.mpr ⟨j, hmem⟩)

/-- All arithmetic operations in a fixed cell are Borel, including its zero
and full acceptance branches. -/
theorem measurable_cellEndpoint :
    Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) =>
      cellEndpoint x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold cellEndpoint interpolate
  have hin : Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) =>
      if x.2.2.2.1 ≤ x.2.2.2.2 then x.2.1 else
        ((x.2.2.2.1-x.2.2.2.2)*x.1+(x.2.2.2.2-x.2.2.1)*x.2.1) /
          (x.2.2.2.1-x.2.2.1)) :=
    (show Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) => x.2.1) by fun_prop).ite
      (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
  have hcond : MeasurableSet {x : (ℝ × ℝ × ℝ × ℝ × ℝ) |
      x.1 < x.2.1 ∧ x.2.2.1 ≤ x.2.2.2.2} :=
    (measurableSet_lt (show Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) => x.1) by fun_prop)
      (by fun_prop)).inter (measurableSet_le
        (show Measurable (fun x : (ℝ × ℝ × ℝ × ℝ × ℝ) => x.2.2.1) by fun_prop)
        (by fun_prop))
  exact hin.ite hcond measurable_const

/-- Borel finite maximum assembly of the actual local acceptance formulas. -/
theorem measurable_finiteAccepted {n : ℕ} :
    Measurable (fun x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ =>
      finiteAccepted x.1 x.2.1 x.2.2) := by
  let f : Fin (n + 1) → ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ) → ℝ :=
    fun i x => Fin.cases (0 : ℝ) (fun j : Fin n =>
      cellEndpoint (x.2.1 j.castSucc) (x.2.1 j.succ)
        (x.1 j.castSucc) (x.1 j.succ) x.2.2) i
  have hsup : Measurable ((Finset.univ : Finset (Fin (n + 1))).sup' (by simp) f) := by
    apply Finset.measurable_sup'
    intro i _
    refine Fin.cases measurable_const (fun j => ?_) i
    change Measurable (fun x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ =>
      cellEndpoint (x.2.1 j.castSucc) (x.2.1 j.succ)
        (x.1 j.castSucc) (x.1 j.succ) x.2.2)
    have hdata : Measurable (fun x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ =>
      (x.2.1 j.castSucc, x.2.1 j.succ, x.1 j.castSucc, x.1 j.succ, x.2.2)) := by
      fun_prop
    exact measurable_cellEndpoint.comp hdata
  convert hsup using 1
  funext x
  exact (Finset.sup'_apply _ f x).symm

/-- Actual accepted-volume evaluation is jointly Borel in every measurable
sorted nodal-price/cumulative-quantity family and the queried price. -/
theorem measurable_actual_offered
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (p Q : Ω → Fin (n + 1) → ℝ) (level : Ω → ℝ)
    (hp : Measurable p) (hQ : Measurable Q) (hlevel : Measurable level)
    (hpm : ∀ ω, Monotone (p ω)) (hQm : ∀ ω, Monotone (Q ω))
    (hzero : ∀ ω, Q ω 0 = 0) :
    Measurable (fun ω => offered (Q ω (Fin.last n)) (curve (p ω) (Q ω)) (level ω)) := by
  have hdata := hp.prodMk (hQ.prodMk hlevel)
  convert measurable_finiteAccepted.comp hdata using 1
  funext ω
  exact offered_eq_finiteAccepted (p ω) (Q ω) (hpm ω) (hQm ω) (hzero ω) (level ω)

end Thesis.DayAhead.InterpolatedAcceptanceFormula
