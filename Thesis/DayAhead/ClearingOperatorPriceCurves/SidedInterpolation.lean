import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedParametrisation
import Mathlib.Algebra.BigOperators.Intervals

/-! # General parameter-block laws for equal-block interpolation -/

noncomputable section

namespace Thesis.DayAhead.SidedParametrisation

open scoped BigOperators

theorem sum_adjacent_knot_differences_before {n : ℕ} (knot : Fin (n + 1) → ℝ)
    (j : Fin n) :
    (∑ i ∈ Finset.Iio j, (knot i.succ - knot i.castSucc)) = knot j.castSucc - knot 0 := by
  have h := Fin.sum_Iic_sub j knot
  rw [← Finset.Iio_insert, Finset.sum_insert (by simp)] at h
  linarith

theorem uniformInterpolation_on_block {n : ℕ} (knot : Fin (n + 1) → ℝ)
    (j : Fin n) {t : ℝ} (hleft : (j : ℝ) / n ≤ t)
    (hright : t ≤ ((j : ℝ) + 1) / n) :
    uniformInterpolation knot t = knot j.castSucc +
      (knot j.succ - knot j.castSucc) * ((n : ℝ) * t - j) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hlo : (j : ℝ) ≤ (n : ℝ) * t := by
    have := (div_le_iff₀ hn).mp hleft
    linarith
  have hhi : (n : ℝ) * t ≤ (j : ℝ) + 1 := by
    have := (le_div_iff₀ hn).mp hright
    linarith
  have hterm (i : Fin n) :
      (knot i.succ - knot i.castSucc) * clampUnit ((n : ℝ) * t - i) =
        (if i < j then knot i.succ - knot i.castSucc else 0) +
        (if i = j then (knot j.succ - knot j.castSucc) * ((n : ℝ) * t - j) else 0) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      rw [clampUnit_of_one_le (by linarith), if_pos hij, if_neg hij.ne]
      ring
    · rw [clampUnit_eq_self (by linarith) (by linarith), if_neg (lt_irrefl _), if_pos rfl]
      ring
    · have hji' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
      rw [clampUnit_of_nonpos (by linarith), if_neg (not_lt.mpr hji.le), if_neg hji.ne']
      ring
  have hfilter : Finset.univ.filter (fun i : Fin n => i < j) = Finset.Iio j := by
    ext i
    simp
  unfold uniformInterpolation
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter, hfilter, sum_adjacent_knot_differences_before]
  ring

theorem uniformInterpolation_block_interior {n : ℕ} (knot : Fin (n + 1) → ℝ)
    (hknot : StrictMono knot) (j : Fin n) {t : ℝ}
    (hleft : (j : ℝ) / n < t) (hright : t < ((j : ℝ) + 1) / n) :
    knot j.castSucc < uniformInterpolation knot t ∧
      uniformInterpolation knot t < knot j.succ := by
  rw [uniformInterpolation_on_block knot j hleft.le hright.le]
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hlo : 0 < (n : ℝ) * t - j := by
    have := (div_lt_iff₀ hn).mp hleft
    linarith
  have hhi : (n : ℝ) * t - j < 1 := by
    have := (lt_div_iff₀ hn).mp hright
    linarith
  have hk : 0 < knot j.succ - knot j.castSucc :=
    sub_pos.mpr (hknot Fin.castSucc_lt_succ)
  constructor <;> nlinarith

end Thesis.DayAhead.SidedParametrisation
