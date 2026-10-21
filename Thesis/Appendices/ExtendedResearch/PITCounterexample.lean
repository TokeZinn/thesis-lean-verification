import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-! # The finite-count core of the multi-step PIT dependence counterexample

Take a persistent fair regime S known at time zero and iid innovations εₙ,
uniform on {0,1,2,3}. In regime false use εₙ₊₁ < 2. In regime true use
εₙ₊₁ = 0 or εₙ₊₂ = 0 or both equal 1. Each event has probability 1/2, so
the corresponding binary outcome has the ideal two-step Bernoulli(1/2)
forecast. Independent auxiliary uniforms give ideal randomized PITs; a PIT
lies in its lower half precisely on the displayed event.

Two adjacent lower-half events have regime-dependent probabilities. Two
distant adjacent pairs therefore remain dependent through S, even though
each single ideal PIT is uniform conditional on its forecast information.
The finite counts and the resulting strictly positive dependence below are
kernel checked. The construction of the infinite product probability space
and the continuous auxiliary randomizations are explained in the audit and
are not claimed as formalized by these finite identities.
-/

namespace Thesis.Foundations.Research.PITCounterexample

def lowerHalf (regime : Bool) (x y : Fin 4) : Prop :=
  if regime then x = 0 ∨ y = 0 ∨ (x = 1 ∧ y = 1) else x < 2

instance (regime : Bool) (x y : Fin 4) : Decidable (lowerHalf regime x y) := by
  unfold lowerHalf
  infer_instance

def singleCount (regime : Bool) : ℕ :=
  ((Finset.univ : Finset (Fin 4 × Fin 4)).filter fun t ↦ lowerHalf regime t.1 t.2).card

def pairCount (regime : Bool) : ℕ :=
  ((Finset.univ : Finset (Fin 4 × (Fin 4 × Fin 4))).filter fun t ↦
    lowerHalf regime t.1 t.2.1 ∧ lowerHalf regime t.2.1 t.2.2).card

theorem singleCount_false : singleCount false = 8 := by decide
theorem singleCount_true : singleCount true = 8 := by decide
theorem pairCount_false : pairCount false = 16 := by decide
theorem pairCount_true : pairCount true = 22 := by decide

def pairProbability (regime : Bool) : ℚ := (pairCount regime : ℚ) / 64

/-- The two separated adjacent-pair events have probability of intersection
strictly greater than the product of their probabilities: difference 9/4096.
This disproves 1-dependence in the accompanying ideal two-step PIT example. -/
theorem distant_blocks_depend :
    (pairProbability false ^ 2 + pairProbability true ^ 2) / 2 -
      ((pairProbability false + pairProbability true) / 2) ^ 2 = 9 / 4096 := by
  norm_num [pairProbability, pairCount_false, pairCount_true]

theorem distant_blocks_not_independent :
    ((pairProbability false + pairProbability true) / 2) ^ 2 <
      (pairProbability false ^ 2 + pairProbability true ^ 2) / 2 := by
  norm_num [pairProbability, pairCount_false, pairCount_true]

end Thesis.Foundations.Research.PITCounterexample
