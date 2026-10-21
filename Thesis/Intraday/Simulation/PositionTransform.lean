import Thesis.Intraday.Simulation.PriceTranslation
import Thesis.Intraday.LOBsAndTuples.Clearing
import Mathlib.Algebra.Order.Round

/-! # Same-side and relative-position block transformation

Inference chapter, Action Transformations. The concrete Analogue-Attention
simulator uses the opposite-side anchor described in its own chapter.
Indices below are zero-based `Fin` values; `oneBased` is exactly the displayed
one-based round-and-clamp formula, with the specified nearest-even half ties.

An empty current side drops a positional action. On a nonempty side the
selection always returns the order currently at that position, independently
of its historical identifier. Additions use the actual same-side best quotes;
their bounded-price certificate is explicit. A tick/rejection/repair policy
and integration into the concrete simulator are separate.
-/

noncomputable section
namespace Thesis.Intraday.PositionTransform

open Execution Clearing PriceTranslation

/-- IEEE-style nearest-integer rounding: exact half ties select the even
integer. Mathlib's `round` alone selects the larger integer at a half tie. -/
def roundEven (x : ℝ) : ℤ :=
  if x - (Int.floor x : ℝ) = 1 / 2 ∧ Even (Int.floor x) then Int.floor x else round x

@[simp] theorem roundEven_int (n : ℤ) : roundEven (n : ℝ) = n := by
  simp [roundEven]

@[simp] theorem roundEven_nat (n : ℕ) : roundEven (n : ℝ) = n := by
  simpa using roundEven_int (n : ℤ)

theorem roundEven_half : roundEven (1 / 2 : ℝ) = 0 := by
  norm_num [roundEven, Int.floor_eq_iff]

def fraction {n : ℕ} (i : Fin n) : ℝ :=
  if n ≤ 1 then 0 else (i.val : ℝ) / ((n : ℝ) - 1)

theorem fraction_short {n : ℕ} (i : Fin n) (hn : n ≤ 1) : fraction i = 0 := by
  simp [fraction, hn]

theorem fraction_nonneg {n : ℕ} (i : Fin n) : 0 ≤ fraction i := by
  unfold fraction
  split_ifs with hn
  · exact le_rfl
  · have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)

theorem fraction_le_one {n : ℕ} (i : Fin n) : fraction i ≤ 1 := by
  unfold fraction
  split_ifs with hn
  · norm_num
  · have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    apply (div_le_one (by linarith : 0 < (n : ℝ) - 1)).mpr
    linarith

theorem fraction_touch (n : ℕ) : fraction (0 : Fin (n + 1)) = 0 := by
  simp [fraction]

theorem fraction_deepest (n : ℕ) (hn : 0 < n) : fraction (Fin.last n) = 1 := by
  have h : ¬n + 1 ≤ 1 := by omega
  have hr : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [fraction, h, hr]

def oneBased (n : ℕ) (u : ℝ) : ℤ :=
  min (max (roundEven (u * ((n : ℝ) - 1)) + 1) 1) n

theorem oneBased_bounds (n : ℕ) (hn : 0 < n) (u : ℝ) :
    1 ≤ oneBased n u ∧ oneBased n u ≤ n := by
  constructor
  · exact le_min (le_max_right _ _) (by exact_mod_cast hn)
  · exact min_le_right _ _

def targetIndex (n : ℕ) (u : ℝ) : Option (Fin n) :=
  if hn : 0 < n then
    some ⟨(oneBased n u).toNat - 1, by
      have := oneBased_bounds n hn u
      omega⟩
  else none

theorem targetIndex_none_iff (n : ℕ) (u : ℝ) : targetIndex n u = none ↔ n = 0 := by
  simp [targetIndex]

theorem targetIndex_exists (n : ℕ) (hn : 0 < n) (u : ℝ) :
    ∃ i, targetIndex n u = some i := by
  simp [targetIndex, hn]

theorem targetIndex_formula {n : ℕ} {u : ℝ} {i : Fin n}
    (hi : targetIndex n u = some i) : (i.val : ℤ) + 1 = oneBased n u := by
  unfold targetIndex at hi
  split at hi
  · rename_i hn
    cases hi
    have := oneBased_bounds n hn u
    dsimp only
    omega
  · contradiction

theorem oneBased_touch (n : ℕ) (hn : 0 < n) : oneBased n 0 = 1 := by
  have h : (1 : ℤ) ≤ n := by exact_mod_cast hn
  simp [oneBased, roundEven, min_eq_left h]

theorem oneBased_deepest (n : ℕ) (hn : 0 < n) : oneBased n 1 = n := by
  have h : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have he : (n : ℝ) - 1 = ((n : ℤ) - 1 : ℤ) := by simp
  rw [oneBased, one_mul, he, roundEven_int]
  simp [max_eq_left h]

theorem targetIndex_touch (n : ℕ) : targetIndex (n + 1) 0 = some 0 := by
  simp [targetIndex, oneBased_touch]

theorem targetIndex_deepest (n : ℕ) : targetIndex (n + 1) 1 = some (Fin.last n) := by
  simp [targetIndex, oneBased_deepest]
  rfl

theorem targetIndex_singleton (u : ℝ) : targetIndex 1 u = some 0 := by
  simp [targetIndex, oneBased, roundEven]

theorem fraction_reconstruct {n : ℕ} (i : Fin n) :
    fraction i * ((n : ℝ) - 1) = i.val := by
  by_cases hn : n ≤ 1
  · have hi : i.val = 0 := by have := i.isLt; omega
    simp [fraction, hn, hi]
  · have h : (n : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      linarith
    simp [fraction, hn, h]

theorem targetIndex_same_depth {n : ℕ} (i : Fin n) : targetIndex n (fraction i) = some i := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have he : oneBased n (fraction i) = (i.val : ℤ) + 1 := by
    have hi : (i.val : ℤ) + 1 ≤ n := by exact_mod_cast i.isLt
    simp only [oneBased, fraction_reconstruct, roundEven_nat]
    rw [max_eq_left (by omega), min_eq_left hi]
  simp only [targetIndex, dif_pos hn, he]
  congr 1

/-- Regression for the source's half-tie convention: at depth two the
midpoint maps to the first order. -/
theorem half_tie_selects_even : oneBased 2 (1 / 2) = 1 := by
  norm_num [oneBased, roundEven_half]

/-- Resolve against the actual current separated tuple, not a historical key. -/
def resolve (buy : Bool) (m : Market) (u : ℝ) : Option Order :=
  (targetIndex (side buy m).1 u).map (side buy m).2

theorem resolve_none_iff (buy : Bool) (m : Market) (u : ℝ) :
    resolve buy m u = none ↔ (side buy m).1 = 0 := by
  simp [resolve, targetIndex_none_iff]

theorem resolve_actual_side (buy : Bool) (m : Market) (u : ℝ) (o : Order)
    (ho : resolve buy m u = some o) :
    ∃ i : Fin (side buy m).1, targetIndex (side buy m).1 u = some i ∧
      o = (side buy m).2 i ∧ m.2 (sideIndex buy m i) = ⟨buy, o⟩ := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp ho
  exact ⟨i, hi, rfl, (side_entry buy m i).symm⟩

theorem resolve_same_depth (buy : Bool) (m : Market) (i : Fin (side buy m).1) :
    resolve buy m (fraction i) = some ((side buy m).2 i) := by
  simp [resolve, targetIndex_same_depth]

/-- `best 0` is used only with the nonempty-side guard below. -/
def shift (buy : Bool) (sim lib : Market) : ℝ :=
  best 0 (side buy sim) - best 0 (side buy lib)

def addition (buy : Bool) (sim lib : Market) (o : Order)
    (_hs : 0 < (side buy sim).1) (_hl : 0 < (side buy lib).1)
    (hp : price o + shift buy sim lib ∈ Set.Icc (-9999 : ℝ) 9999) : Order :=
  shiftOrder o (shift buy sim lib) hp

theorem addition_distance (buy : Bool) (sim lib : Market) (o : Order) (hs hl hp) :
    price (addition buy sim lib o hs hl hp) - best 0 (side buy sim) =
      price o - best 0 (side buy lib) := by
  simp only [addition, shiftOrder_price, shift]
  ring

theorem addition_quantity (buy : Bool) (sim lib : Market) (o : Order) (hs hl hp) :
    quantity (addition buy sim lib o hs hl hp) = quantity o := rfl

theorem addition_time (buy : Bool) (sim lib : Market) (o : Order) (hs hl hp) :
    Thesis.Intraday.time (addition buy sim lib o hs hl hp) = Thesis.Intraday.time o := rfl

def spread (m : Market) : ℝ := best 0 (side false m) - best 0 (side true m)

theorem same_shift_iff_same_spread (sim lib : Market) :
    shift true sim lib = shift false sim lib ↔ spread sim = spread lib := by
  unfold shift spread
  constructor <;> intro h <;> linarith

theorem midpoint_shift_iff_same_spread (buy : Bool) (sim lib : Market) :
    shift buy sim lib = GeometrySweep.midpoint (splitMarket sim) -
      GeometrySweep.midpoint (splitMarket lib) ↔ spread sim = spread lib := by
  unfold shift GeometrySweep.midpoint splitMarket spread
  cases buy <;> dsimp only <;> constructor <;> intro h <;> linarith

end Thesis.Intraday.PositionTransform
