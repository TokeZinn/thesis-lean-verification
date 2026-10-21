import Thesis.Intraday.InferencePointProcesses.ExchangeableRanks
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Limits of the exact finite-ensemble coverage expectations

The final asymptotic clauses of `prop:midrank-coverage-expectations`, using the
actual floor/ceiling counts, not a continuous-uniform replacement at finite B.
-/

noncomputable section
namespace Thesis.Intraday.RankLimits
open Filter ExchangeableRanks
open scoped Topology

theorem floor_div_succ_limit (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun B : ℕ => (Nat.floor ((B : ℝ) * a) : ℝ) / (B+1)) atTop (𝓝 a) := by
  have hf : Tendsto (fun B : ℕ => (Nat.floor ((B : ℝ) * a) : ℝ) / B) atTop (𝓝 a) := by
    simpa only [mul_comm] using
      (tendsto_nat_floor_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop
  have h := hf.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with B hB
  have hn : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  field_simp

theorem ceil_div_succ_limit (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun B : ℕ => (Nat.ceil ((B : ℝ) * a) : ℝ) / (B+1)) atTop (𝓝 a) := by
  have hf : Tendsto (fun B : ℕ => (Nat.ceil ((B : ℝ) * a) : ℝ) / B) atTop (𝓝 a) := by
    simpa only [mul_comm] using
      (tendsto_nat_ceil_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop
  have h := hf.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with B hB
  have hn : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  field_simp

theorem upper_reference_limit (alpha : ℝ) (ha1 : alpha ≤ 1) :
    Tendsto (fun B : ℕ => ((Nat.floor ((B : ℝ) * (1-alpha)) : ℝ) + 1) / (B+1))
      atTop (𝓝 (1-alpha)) := by
  have h := (floor_div_succ_limit (1-alpha) (by linarith)).add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [add_zero, ← add_div] using h

/-- Original label: `prop:midrank-coverage-expectations`. -/
theorem central_reference_limit (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    Tendsto (fun B : ℕ => EnsembleCalibration.centralReference B alpha)
      atTop (𝓝 (1-alpha)) := by
  have hf := floor_div_succ_limit (1-alpha/2) (by linarith : 0 ≤ 1-alpha/2)
  have hc := ceil_div_succ_limit (alpha/2) (by linarith : 0 ≤ alpha/2)
  have h := (hf.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).sub hc
  have he : (1-alpha/2)+0-alpha/2 = 1-alpha := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with B hB
  rw [central_reference_formula B hB alpha ha0 ha1]
  ring

end Thesis.Intraday.RankLimits
