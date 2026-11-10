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

variable [Module ℝ H]

end Thesis.DayAhead.ShapleyPermutations
