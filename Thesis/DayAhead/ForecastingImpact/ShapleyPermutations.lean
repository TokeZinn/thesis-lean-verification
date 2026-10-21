import Thesis.DayAhead.ForecastingImpact.Shapley
import Mathlib.Data.Fintype.Perm

/-! # The actual predecessor coalitions in permutation attribution

Forecasting chapter, lines 500–513. Each permutation orders all features;
its marginal contributions telescope exactly. The connection between uniform
permutation frequencies and the factorial formula is recorded separately.
-/

noncomputable section
namespace Thesis.DayAhead.ShapleyPermutations

open Finset
open scoped BigOperators

variable {n : ℕ} {H : Type*} [AddCommGroup H]

def stage (π : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  univ.filter fun i => (π i).val < k

def predecessors (π : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => π j < π i

theorem stage_zero (π : Equiv.Perm (Fin n)) : stage π 0 = ∅ := by simp [stage]

theorem stage_full (π : Equiv.Perm (Fin n)) : stage π n = univ := by simp [stage]

theorem stage_succ (π : Equiv.Perm (Fin n)) (k : Fin n) :
    stage π (k.val + 1) = insert (π.symm k) (stage π k.val) := by
  ext i
  simp only [stage, mem_filter, mem_univ, true_and, mem_insert]
  rw [← π.apply_eq_iff_eq_symm_apply, ← Fin.val_inj]
  omega

theorem predecessors_eq_stage (π : Equiv.Perm (Fin n)) (i : Fin n) :
    predecessors π i = stage π (π i).val := rfl

def contribution (V : Finset (Fin n) → H) (π : Equiv.Perm (Fin n)) (i : Fin n) : H :=
  Shapley.marginal V (predecessors π i) i

theorem efficiency (V : Finset (Fin n) → H) (π : Equiv.Perm (Fin n)) :
    ∑ i, contribution V π i = V univ - V ∅ := by
  calc
    _ = ∑ k : Fin n, (V (stage π (k.val + 1)) - V (stage π k.val)) := by
      apply Fintype.sum_equiv π
      intro i
      rw [stage_succ, π.symm_apply_apply]
      rfl
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun k => V (stage π (k + 1)) - V (stage π k)),
        sum_range_sub (fun k => V (stage π k)) n, stage_full, stage_zero]

variable [Module ℝ H]

def sampleValue (B : ℕ) (V : Finset (Fin n) → H)
    (permutations : Fin B → Equiv.Perm (Fin n)) (i : Fin n) : H :=
  (B : ℝ)⁻¹ • ∑ b, contribution V (permutations b) i

/-- Exact marginal evaluations retain efficiency for every nonempty sample of permutations. -/
theorem sample_efficiency {B : ℕ} (hB : 0 < B) (V : Finset (Fin n) → H)
    (permutations : Fin B → Equiv.Perm (Fin n)) :
    ∑ i, sampleValue B V permutations i = V univ - V ∅ := by
  simp only [sampleValue, ← smul_sum]
  rw [sum_comm]
  simp only [efficiency, sum_const, card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by positivity : (B : ℝ) ≠ 0), one_smul]

end Thesis.DayAhead.ShapleyPermutations
