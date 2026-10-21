import Thesis.Intraday.Simulation.Conservation
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

/-! # Partial-depth geometry from actual visible orders

Current source: `eq:aa-sweep-geometry` and `sec:intraday-geometry-gauge`.
The list order is the supplied visible priority order. Positive quantities are
those of the actual logarithmic order representation; the final level is
partly consumed and the unused tail receives zero allocation.
-/

noncomputable section
namespace Thesis.Intraday.GeometrySweep

open Execution Conservation Set
open scoped BigOperators
open Filter Topology

def depth (orders : List Order) : ℝ := (orders.map quantity).sum

def allocations : List Order → ℝ → List ℝ
  | [], _ => []
  | o :: os, v => min (quantity o) (max 0 v) :: allocations os (max 0 (v - quantity o))

def notional : List Order → ℝ → ℝ
  | [], _ => 0
  | o :: os, v => price o * min (quantity o) (max 0 v) +
      notional os (max 0 (v - quantity o))

theorem depth_nonneg (orders : List Order) : 0 ≤ depth orders := by
  induction orders with
  | nil => simp [depth]
  | cons o os ih => simpa [depth] using add_nonneg (quantity_pos o).le ih

theorem allocations_length (orders : List Order) (v : ℝ) :
    (allocations orders v).length = orders.length := by
  induction orders generalizing v with
  | nil => rfl
  | cons o os ih => simp [allocations, ih]

theorem allocations_bounds (orders : List Order) (v : ℝ) :
    List.Forall₂ (fun q o => 0 ≤ q ∧ q ≤ quantity o) (allocations orders v) orders := by
  induction orders generalizing v with
  | nil => exact List.Forall₂.nil
  | cons o os ih =>
    exact List.Forall₂.cons ⟨le_min (quantity_pos o).le (le_max_left _ _), min_le_left _ _⟩
      (ih _)

theorem notional_eq_allocations (orders : List Order) (v : ℝ) :
    notional orders v = (List.zipWith (fun o q => price o * q) orders
      (allocations orders v)).sum := by
  induction orders generalizing v with
  | nil => rfl
  | cons o os ih => simp [notional, allocations, ih]

theorem split_volume {q d v : ℝ} (hq : 0 ≤ q) (hd : 0 ≤ d) :
    min q (max 0 v) + min (max 0 (v - q)) d = min (max 0 v) (q + d) := by
  by_cases hv : v ≤ 0
  · simp [max_eq_left hv, max_eq_left (show v - q ≤ 0 by linarith),
      min_eq_right hq, min_eq_left hd, min_eq_left (add_nonneg hq hd)]
  by_cases hvq : v ≤ q
  · simp [max_eq_right (le_of_not_ge hv), max_eq_left (sub_nonpos.mpr hvq),
      min_eq_right hvq, min_eq_left hd, min_eq_left (show v ≤ q + d by linarith)]
  have hqv : q ≤ v := le_of_not_ge hvq
  by_cases hrem : v - q ≤ d
  · simp [max_eq_right (le_of_not_ge hv), max_eq_right (sub_nonneg.mpr hqv),
      min_eq_left hqv, min_eq_left hrem, min_eq_left (show v ≤ q + d by linarith)]
  · simp [max_eq_right (le_of_not_ge hv), max_eq_right (sub_nonneg.mpr hqv),
      min_eq_left hqv, min_eq_right (le_of_not_ge hrem),
      min_eq_right (show q + d ≤ v by linarith)]

theorem allocations_sum (orders : List Order) (v : ℝ) :
    (allocations orders v).sum = min (max 0 v) (depth orders) := by
  induction orders generalizing v with
  | nil => simp [allocations, depth]
  | cons o os ih =>
    simp only [allocations, List.sum_cons, ih]
    simpa [depth, max_assoc] using
      (split_volume (v := v) (quantity_pos o).le (depth_nonneg os))

theorem allocations_sum_of_within_depth (orders : List Order) {v : ℝ}
    (hv : 0 ≤ v) (hd : v ≤ depth orders) : (allocations orders v).sum = v := by
  rw [allocations_sum, max_eq_right hv, min_eq_left hd]

@[simp] theorem notional_zero (orders : List Order) : notional orders 0 = 0 := by
  induction orders with
  | nil => rfl
  | cons o os ih =>
    simp [notional, (quantity_pos o).le, ih]

theorem notional_first {o : Order} {os : List Order} {v : ℝ}
    (hv : 0 ≤ v) (hq : v ≤ quantity o) : notional (o :: os) v = price o * v := by
  simp [notional, max_eq_right hv, min_eq_right hq, max_eq_left (sub_nonpos.mpr hq)]

theorem continuous_notional (orders : List Order) : Continuous (notional orders) := by
  induction orders with
  | nil => exact continuous_const
  | cons o os ih =>
    exact (continuous_const.mul (continuous_const.min (continuous_const.max continuous_id))).add
      (ih.comp (continuous_const.max (continuous_id.sub continuous_const)))

def bookOrders (b : Book) : List Order := List.ofFn b.2

theorem depth_bookOrders (b : Book) : depth (bookOrders b) = bookQuantity b := by
  simp [depth, bookOrders, bookQuantity, List.map_ofFn, List.sum_ofFn]

theorem bookQuantity_pos {b : Book} (hb : 0 < b.1) : 0 < bookQuantity b := by
  rcases b with ⟨n, b⟩
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hb)
  | succ n =>
    rw [bookQuantity_head_tail]
    exact add_pos_of_pos_of_nonneg (quantity_pos (b 0)) (bookQuantity_nonneg _)

def selectedSide (b : State) (u : ℝ) : Book := if u ≤ 0 then b.1 else b.2

def requestedVolume (b : State) (u : ℝ) : ℝ := |u| * bookQuantity (selectedSide b u)

theorem requestedVolume_bounds (b : State) {u : ℝ} (hu : |u| ≤ 1) :
    0 ≤ requestedVolume b u ∧
      requestedVolume b u ≤ bookQuantity (selectedSide b u) := by
  have h := mul_le_mul_of_nonneg_right hu (bookQuantity_nonneg (selectedSide b u))
  simp only [one_mul] at h
  exact ⟨mul_nonneg (abs_nonneg _) (bookQuantity_nonneg _), h⟩

theorem requestedVolume_fully_allocated (b : State) {u : ℝ} (hu : |u| ≤ 1) :
    (allocations (bookOrders (selectedSide b u)) (requestedVolume b u)).sum =
      requestedVolume b u := by
  have h := requestedVolume_bounds b hu
  exact allocations_sum_of_within_depth _ h.1 (by simpa [depth_bookOrders] using h.2)

def midpoint (b : State) : ℝ := (best 0 b.1 + best 0 b.2) / 2

def signedCost (b : State) (u : ℝ) : ℝ :=
  if u ≤ 0 then -notional (bookOrders b.1) (-u * bookQuantity b.1)
  else notional (bookOrders b.2) (u * bookQuantity b.2)

def displacement (b : State) (u : ℝ) : ℝ :=
  if u = 0 then 0 else
    (if u ≤ 0 then notional (bookOrders b.1) (-u * bookQuantity b.1)
     else notional (bookOrders b.2) (u * bookQuantity b.2)) /
       requestedVolume b u - midpoint b

@[simp] theorem signedCost_zero (b : State) : signedCost b 0 = 0 := by simp [signedCost]
@[simp] theorem displacement_zero (b : State) : displacement b 0 = 0 := by simp [displacement]

theorem signedCost_negative (b : State) {u : ℝ} (hu : u < 0) :
    signedCost b u = -notional (bookOrders b.1) (requestedVolume b u) := by
  simp [signedCost, hu.le, requestedVolume, selectedSide, abs_of_neg hu]

theorem signedCost_positive (b : State) {u : ℝ} (hu : 0 < u) :
    signedCost b u = notional (bookOrders b.2) (requestedVolume b u) := by
  simp [signedCost, not_le.mpr hu, requestedVolume, selectedSide, abs_of_pos hu]

theorem continuous_signedCost (b : State) : Continuous (signedCost b) := by
  apply Continuous.if_le
    ((continuous_notional _).comp (continuous_id.neg.mul continuous_const)).neg
    ((continuous_notional _).comp (continuous_id.mul continuous_const))
    continuous_id continuous_const
  intro u hu
  change u = 0 at hu
  simp [hu]

theorem displacement_negative (b : State) {u : ℝ} (hu : u < 0) :
    displacement b u = notional (bookOrders b.1) (-u * bookQuantity b.1) /
      (-u * bookQuantity b.1) - midpoint b := by
  simp [displacement, ne_of_lt hu, hu.le, requestedVolume, selectedSide, abs_of_neg hu]

theorem displacement_positive (b : State) {u : ℝ} (hu : 0 < u) :
    displacement b u = notional (bookOrders b.2) (u * bookQuantity b.2) /
      (u * bookQuantity b.2) - midpoint b := by
  simp [displacement, ne_of_gt hu, not_le.mpr hu, requestedVolume, selectedSide, abs_of_pos hu]

theorem continuousOn_displacement_negative {b : State}
    (hb : 0 < b.1.1) (_hs : 0 < b.2.1) : ContinuousOn (displacement b) (Iio 0) := by
  have hc : Continuous (fun u : ℝ => -u * bookQuantity b.1) :=
    continuous_id.neg.mul continuous_const
  have h := ((continuous_notional (bookOrders b.1)).comp hc).continuousOn.div
    hc.continuousOn (fun u (hu : u < 0) =>
      mul_ne_zero (neg_ne_zero.mpr (ne_of_lt hu)) (ne_of_gt (bookQuantity_pos hb)))
  exact (h.sub (continuousOn_const (c := midpoint b))).congr
    fun u hu => displacement_negative b hu

theorem continuousOn_displacement_positive {b : State}
    (_hb : 0 < b.1.1) (hs : 0 < b.2.1) : ContinuousOn (displacement b) (Ioi 0) := by
  have hc : Continuous (fun u : ℝ => u * bookQuantity b.2) :=
    continuous_id.mul continuous_const
  have h := ((continuous_notional (bookOrders b.2)).comp hc).continuousOn.div
    hc.continuousOn (fun u (hu : 0 < u) =>
      mul_ne_zero (ne_of_gt hu) (ne_of_gt (bookQuantity_pos hs)))
  exact (h.sub (continuousOn_const (c := midpoint b))).congr
    fun u hu => displacement_positive b hu

theorem notional_book_first {n : ℕ} (x : Fin (n + 1) → Order) {v : ℝ}
    (hv : 0 ≤ v) (hq : v ≤ quantity (x 0)) :
    notional (bookOrders ⟨n + 1, x⟩) v = price (x 0) * v := by
  simpa [bookOrders, List.ofFn_succ] using
    (notional_first (os := List.ofFn (fun i : Fin n => x i.succ)) hv hq)

/-- Close to zero the first ask alone supplies the requested positive volume. -/
theorem displacement_right_eventually {b : State}
    (hb : 0 < b.1.1) (hs : 0 < b.2.1) :
    displacement b =ᶠ[𝓝[>] 0] fun _ => best 0 b.2 - midpoint b := by
  rcases b with ⟨buy, ⟨m, sell⟩⟩
  cases m with
  | zero => exact False.elim (Nat.not_lt_zero _ hs)
  | succ m =>
    let b : State := (buy, ⟨m + 1, sell⟩)
    have hV : 0 < bookQuantity b.2 := bookQuantity_pos hs
    have hc : Continuous (fun u : ℝ => u * bookQuantity b.2) :=
      continuous_id.mul continuous_const
    have hsmall : ∀ᶠ u in 𝓝 (0 : ℝ), u * bookQuantity b.2 < quantity (sell 0) :=
      hc.continuousAt.eventually_lt continuousAt_const (by simpa using quantity_pos (sell 0))
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with u hq hu
    change 0 < u at hu
    change displacement b u = price (sell 0) - midpoint b
    rw [displacement_positive b hu, notional_book_first sell (mul_pos hu hV).le hq.le]
    rw [mul_div_cancel_right₀ _ (ne_of_gt (mul_pos hu hV))]

/-- The left limit uses the first bid, irrespective of deeper visible levels. -/
theorem displacement_left_eventually {b : State}
    (hb : 0 < b.1.1) (hs : 0 < b.2.1) :
    displacement b =ᶠ[𝓝[<] 0] fun _ => best 0 b.1 - midpoint b := by
  rcases b with ⟨⟨n, buy⟩, sell⟩
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hb)
  | succ n =>
    let b : State := (⟨n + 1, buy⟩, sell)
    have hV : 0 < bookQuantity b.1 := bookQuantity_pos hb
    have hc : Continuous (fun u : ℝ => -u * bookQuantity b.1) :=
      continuous_id.neg.mul continuous_const
    have hsmall : ∀ᶠ u in 𝓝 (0 : ℝ), -u * bookQuantity b.1 < quantity (buy 0) :=
      hc.continuousAt.eventually_lt continuousAt_const (by simpa using quantity_pos (buy 0))
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with u hq hu
    change u < 0 at hu
    change displacement b u = price (buy 0) - midpoint b
    rw [displacement_negative b hu,
      notional_book_first buy (mul_pos (neg_pos.mpr hu) hV).le hq.le]
    rw [mul_div_cancel_right₀ _ (ne_of_gt (mul_pos (neg_pos.mpr hu) hV))]

theorem displacement_right_limit {b : State}
    (hb : 0 < b.1.1) (hs : 0 < b.2.1) :
    Tendsto (displacement b) (𝓝[>] 0) (𝓝 (best 0 b.2 - midpoint b)) :=
  tendsto_const_nhds.congr' (displacement_right_eventually hb hs).symm

theorem displacement_left_limit {b : State}
    (hb : 0 < b.1.1) (hs : 0 < b.2.1) :
    Tendsto (displacement b) (𝓝[<] 0) (𝓝 (best 0 b.1 - midpoint b)) :=
  tendsto_const_nhds.congr' (displacement_left_eventually hb hs).symm

/-- The thesis's warning is substantive whenever the two best quotes differ. -/
theorem displacement_not_continuousAt_zero {b : State}
    (hb : 0 < b.1.1) (hs : 0 < b.2.1) (hspread : best 0 b.1 ≠ best 0 b.2) :
    ¬ ContinuousAt (displacement b) 0 := by
  intro hc
  have hr := tendsto_nhds_unique (displacement_right_limit hb hs)
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hl := tendsto_nhds_unique (displacement_left_limit hb hs)
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  exact hspread (by linarith)

end Thesis.Intraday.GeometrySweep
