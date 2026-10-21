import Thesis.Intraday.LOBsAndTuples.Execution

/-! # Executed quantity and conservation for the literal four-branch update -/

noncomputable section
namespace Thesis.Intraday.Conservation

open Execution
open scoped BigOperators

def bookQuantity (b : Book) : ℝ := ∑ i : Fin b.1, quantity (b.2 i)

theorem bookQuantity_nonneg (b : Book) : 0 ≤ bookQuantity b :=
  Finset.sum_nonneg fun i _ => (quantity_pos (b.2 i)).le

def matchedQuantity : State → ℝ
  | (⟨0, _⟩, _) => 0
  | (⟨_ + 1, _⟩, ⟨0, _⟩) => 0
  | (⟨_ + 1, b⟩, ⟨_ + 1, s⟩) =>
    if price (b 0) < price (s 0) then 0 else min (quantity (b 0)) (quantity (s 0))

theorem matchedQuantity_nonneg (x : State) : 0 ≤ matchedQuantity x := by
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero => exact le_rfl
  | succ n =>
    cases m with
    | zero => exact le_rfl
    | succ m =>
      dsimp only [matchedQuantity]
      split
      · exact le_rfl
      · exact le_min (quantity_pos _).le (quantity_pos _).le

theorem bookQuantity_head_tail {n : ℕ} (x : Fin (n + 1) → Order) :
    bookQuantity ⟨n + 1, x⟩ = quantity (x 0) + bookQuantity (tail x) := by
  exact Fin.sum_univ_succ (fun i => quantity (x i))

theorem bookQuantity_changeHead {n : ℕ} (x : Fin (n + 1) → Order) {q : ℝ} (hq : 0 < q) :
    bookQuantity (changeHead x q) = q + bookQuantity (tail x) := by
  rw [changeHead, bookQuantity_head_tail]
  simp only [Function.update_self, withQuantity_quantity _ hq]
  congr 1

/-- Both sides lose exactly the same executed volume, including exact fills. -/
theorem step_quantity_conservation (x : State) :
    bookQuantity (step x).1 + matchedQuantity x = bookQuantity x.1 ∧
      bookQuantity (step x).2 + matchedQuantity x = bookQuantity x.2 := by
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero => simp [step, matchedQuantity]
  | succ n =>
    cases m with
    | zero => simp [step, matchedQuantity]
    | succ m =>
      by_cases hp : price (b 0) < price (s 0)
      · simp [step, matchedQuantity, hp]
      by_cases hb : quantity (b 0) < quantity (s 0)
      · simp only [step, matchedQuantity, if_neg hp, if_pos hb, min_eq_left hb.le,
          bookQuantity_changeHead s (sub_pos.mpr hb), bookQuantity_head_tail]
        constructor <;> ring
      by_cases hs : quantity (s 0) < quantity (b 0)
      · simp only [step, matchedQuantity, if_neg hp, if_neg hb, if_pos hs,
          min_eq_right hs.le, bookQuantity_changeHead b (sub_pos.mpr hs), bookQuantity_head_tail]
        constructor <;> ring
      · have he : quantity (b 0) = quantity (s 0) := le_antisymm (le_of_not_gt hs) (le_of_not_gt hb)
        simp only [step, matchedQuantity, if_neg hp, he, lt_self_iff_false, if_false,
          min_self, bookQuantity_head_tail]
        constructor <;> ring

def executedThrough (n : ℕ) (x : State) : ℝ :=
  ∑ k ∈ Finset.range n, matchedQuantity (step^[k] x)

theorem executedThrough_nonneg (n : ℕ) (x : State) : 0 ≤ executedThrough n x :=
  Finset.sum_nonneg fun _ _ => matchedQuantity_nonneg _

theorem iterate_quantity_conservation (n : ℕ) (x : State) :
    bookQuantity (step^[n] x).1 + executedThrough n x = bookQuantity x.1 ∧
      bookQuantity (step^[n] x).2 + executedThrough n x = bookQuantity x.2 := by
  induction n with
  | zero => simp [executedThrough]
  | succ n ih =>
    have h := step_quantity_conservation (step^[n] x)
    simp only [executedThrough, Finset.sum_range_succ, Function.iterate_succ_apply'] at *
    constructor <;> linarith [h.1, h.2, ih.1, ih.2]

theorem executedThrough_le_depth (n : ℕ) (x : State) :
    executedThrough n x ≤ min (bookQuantity x.1) (bookQuantity x.2) := by
  have h := iterate_quantity_conservation n x
  have hb := bookQuantity_nonneg (step^[n] x).1
  have hs := bookQuantity_nonneg (step^[n] x).2
  exact le_min (by linarith [h.1]) (by linarith [h.2])

theorem iterate_netQuantity (n : ℕ) (x : State) :
    bookQuantity (step^[n] x).1 - bookQuantity (step^[n] x).2 =
      bookQuantity x.1 - bookQuantity x.2 := by
  have h := iterate_quantity_conservation n x
  linarith [h.1, h.2]

end Thesis.Intraday.Conservation
