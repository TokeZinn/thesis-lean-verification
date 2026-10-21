import Thesis.Intraday.Simulation.GeometrySweep
import Thesis.Intraday.Simulation.AnalogueAttention
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! # Current depth-profile features and outcome grids

This uses each side's own total volume, as in `eq:aa-sweep-geometry`, rather
than the obsolete common-volume geometry gauge. Feature/output dimensions
match `eq:aa-tokens` and `eq:aa-outcome` exactly.
-/

noncomputable section
namespace Thesis.Intraday.DepthProfile
open Execution GeometrySweep AnalogueAttention

def inputNode (i : Fin 41) : ℝ := -1 + (i.val : ℝ) / 20
def outputNode (i : Fin 33) : ℝ := -1 + (i.val : ℝ) / 16

theorem inputNode_bounds (i : Fin 41) : -1 ≤ inputNode i ∧ inputNode i ≤ 1 := by
  have hi : (i.val : ℝ) ≤ 40 := by exact_mod_cast (show i.val ≤ 40 by omega)
  have hz : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  dsimp [inputNode]; constructor <;> linarith

theorem outputNode_bounds (i : Fin 33) : -1 ≤ outputNode i ∧ outputNode i ≤ 1 := by
  have hi : (i.val : ℝ) ≤ 32 := by exact_mod_cast (show i.val ≤ 32 by omega)
  have hz : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  dsimp [outputNode]; constructor <;> linarith

def features (b : State) (i : Fin 41) : Vector 4 :=
  let u := inputNode i
  WithLp.toLp 2 ![u, Real.log (1 + requestedVolume b u),
    Real.arsinh (displacement b u / 10), SignType.sign u]

def outcome (start finish : State) : Vector 33 :=
  WithLp.toLp 2 fun i => displacement finish (outputNode i) - displacement start (outputNode i)

theorem feature_sweep_fully_allocated (b : State) (i : Fin 41) :
    (allocations (bookOrders (selectedSide b (inputNode i)))
      (requestedVolume b (inputNode i))).sum = requestedVolume b (inputNode i) :=
  requestedVolume_fully_allocated b (abs_le.mpr (inputNode_bounds i))

theorem logarithm_argument_positive (b : State) (i : Fin 41) :
    0 < 1 + requestedVolume b (inputNode i) := by
  have h := (requestedVolume_bounds b (abs_le.mpr (inputNode_bounds i))).1
  linarith

theorem input_grid_endpoints : inputNode 0 = -1 ∧ inputNode 20 = 0 ∧ inputNode 40 = 1 := by
  norm_num [inputNode]

theorem output_grid_endpoints : outputNode 0 = -1 ∧ outputNode 16 = 0 ∧ outputNode 32 = 1 := by
  norm_num [outputNode]

/-- On a one-order ask side every positive relative-depth sweep returns the
same execution price, regardless of that side's total quantity. This is a
literal witness to the current score's loss of total-depth information. -/
theorem singleton_displacement_positive (bid ask : Order) (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ 1) :
    displacement ((⟨1, fun _ => bid⟩, ⟨1, fun _ => ask⟩) : State) u =
      price ask - (price bid + price ask) / 2 := by
  let b : State := (⟨1, fun _ => bid⟩, ⟨1, fun _ => ask⟩)
  have hq : Conservation.bookQuantity b.2 = quantity ask := by
    simp [b, Conservation.bookQuantity]
  change displacement b u = _
  rw [displacement_positive b hu, hq]
  have hp : 0 < u * quantity ask := mul_pos hu (quantity_pos ask)
  have hb : u * quantity ask ≤ quantity ask := by
    simpa using mul_le_mul_of_nonneg_right hu1 (quantity_pos ask).le
  rw [notional_book_first (fun _ : Fin 1 => ask) hp.le hb,
    mul_div_cancel_right₀ _ (ne_of_gt hp)]
  rfl

/-- The bid-side counterpart establishes that independent buy/sell depth
changes can be invisible to displacement on the entire nonzero grid. -/
theorem singleton_displacement_negative (bid ask : Order) (u : ℝ) (hu : u < 0)
    (hu1 : -1 ≤ u) :
    displacement ((⟨1, fun _ => bid⟩, ⟨1, fun _ => ask⟩) : State) u =
      price bid - (price bid + price ask) / 2 := by
  let b : State := (⟨1, fun _ => bid⟩, ⟨1, fun _ => ask⟩)
  have hq : Conservation.bookQuantity b.1 = quantity bid := by
    simp [b, Conservation.bookQuantity]
  change displacement b u = _
  rw [displacement_negative b hu, hq]
  have hp : 0 < -u * quantity bid := mul_pos (neg_pos.mpr hu) (quantity_pos bid)
  have hb : -u * quantity bid ≤ quantity bid := by
    have hu' : -u ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right hu' (quantity_pos bid).le
  rw [notional_book_first (fun _ : Fin 1 => bid) hp.le hb,
    mul_div_cancel_right₀ _ (ne_of_gt hp)]
  rfl

end Thesis.Intraday.DepthProfile
