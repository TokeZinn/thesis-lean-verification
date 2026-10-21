import Thesis.DayAhead.ForecastingImpact.BoostingLoss
import Mathlib.Tactic

/-! # Validation checkpointing and patience stopping

Chapter 5, lines 404 and 421. Scores are evaluated on the reserved validation
set. Index zero is the initial model; a strictly smaller validation error
replaces the cache, and ties retain the earlier model. Patience is the number
of completed rounds since that replacement. A maximum round count always
terminates the procedure. These are exact selection rules, not a claim that
the selected model generalizes or reproduces an archived training run.
-/

noncomputable section
namespace Thesis.DayAhead.ValidationCheckpoint

def bestIndex (score : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if score (n + 1) < score (bestIndex score n) then n + 1 else bestIndex score n

theorem bestIndex_le (score : ℕ → ℝ) (n : ℕ) : bestIndex score n ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [bestIndex]
    split_ifs <;> omega

theorem bestIndex_minimal (score : ℕ → ℝ) (n : ℕ) :
    ∀ i ≤ n, score (bestIndex score n) ≤ score i := by
  induction n with
  | zero =>
    intro i hi
    have he : i = 0 := by omega
    subst i
    exact le_rfl
  | succ n ih =>
    intro i hi
    simp only [bestIndex]
    split_ifs with h
    · by_cases heq : i = n + 1
      · subst i; exact le_rfl
      · exact h.le.trans (ih i (by omega))
    · by_cases heq : i = n + 1
      · subst i; exact le_of_not_gt h
      · exact ih i (by omega)

theorem bestIndex_earliest (score : ℕ → ℝ) (n : ℕ) {i : ℕ} (hi : i ≤ n)
    (hscore : score i = score (bestIndex score n)) : bestIndex score n ≤ i := by
  induction n with
  | zero => simp only [bestIndex]; omega
  | succ n ih =>
    simp only [bestIndex] at hscore ⊢
    split_ifs at hscore ⊢ with h
    · by_contra hlt
      have himin := bestIndex_minimal score n i (by omega)
      linarith
    · by_cases hin : i ≤ n
      · exact ih hin hscore
      · have hb := bestIndex_le score n; omega

theorem bestScore_antitone (score : ℕ → ℝ) : Antitone (fun n => score (bestIndex score n)) := by
  apply antitone_nat_of_succ_le
  intro n
  exact bestIndex_minimal score (n + 1) (bestIndex score n) (by have := bestIndex_le score n; omega)

def waitRounds (score : ℕ → ℝ) (n : ℕ) : ℕ := n - bestIndex score n

theorem waitRounds_zero_of_improved (score : ℕ → ℝ) (n : ℕ)
    (h : score (n + 1) < score (bestIndex score n)) : waitRounds score (n + 1) = 0 := by
  simp [waitRounds, bestIndex, h]

theorem waitRounds_succ_of_not_improved (score : ℕ → ℝ) (n : ℕ)
    (h : score (bestIndex score n) ≤ score (n + 1)) :
    waitRounds score (n + 1) = waitRounds score n + 1 := by
  simp only [waitRounds, bestIndex, if_neg (not_lt_of_ge h)]
  have := bestIndex_le score n
  omega

def stopLoop (score : ℕ → ℝ) (patience : ℕ) : ℕ → ℕ → ℕ
  | 0, current => current
  | fuel + 1, current => if patience ≤ waitRounds score current then current
      else stopLoop score patience fuel (current + 1)

theorem stopLoop_spec (score : ℕ → ℝ) (patience fuel current : ℕ) :
    let stop := stopLoop score patience fuel current
    current ≤ stop ∧ stop ≤ current + fuel ∧
      (stop = current + fuel ∨ patience ≤ waitRounds score stop) := by
  induction fuel generalizing current with
  | zero => simp [stopLoop]
  | succ fuel ih =>
    simp only [stopLoop]
    split_ifs with h
    · exact ⟨le_rfl, by omega, Or.inr h⟩
    · have hs := ih (current + 1)
      refine ⟨by omega, by omega, ?_⟩
      rcases hs.2.2 with heq | hstop
      · exact Or.inl (by omega)
      · exact Or.inr hstop

def stopRound (score : ℕ → ℝ) (maxRounds patience : ℕ) : ℕ :=
  stopLoop score patience maxRounds 0

theorem stopLoop_before (score : ℕ → ℝ) (patience fuel current k : ℕ)
    (hcurrent : current ≤ k) (hk : k < stopLoop score patience fuel current) :
    waitRounds score k < patience := by
  induction fuel generalizing current with
  | zero => simp only [stopLoop] at hk; omega
  | succ fuel ih =>
    simp only [stopLoop] at hk
    split_ifs at hk with h
    · omega
    · by_cases heq : k = current
      · subst k; omega
      · exact ih (current + 1) (by omega) hk

theorem stopRound_spec (score : ℕ → ℝ) (maxRounds patience : ℕ) :
    stopRound score maxRounds patience ≤ maxRounds ∧
      (stopRound score maxRounds patience = maxRounds ∨
        patience ≤ waitRounds score (stopRound score maxRounds patience)) := by
  have h := (stopLoop_spec score patience maxRounds 0).2
  simpa only [stopRound, zero_add] using h

theorem stopRound_before (score : ℕ → ℝ) (maxRounds patience k : ℕ)
    (hk : k < stopRound score maxRounds patience) : waitRounds score k < patience :=
  stopLoop_before score patience maxRounds 0 k (Nat.zero_le _) hk

def checkpoint (score : ℕ → ℝ) (maxRounds patience : ℕ) : ℕ :=
  bestIndex score (stopRound score maxRounds patience)

/-- The returned checkpoint is the earliest validation minimizer among all
visited models, even when the final visited model is worse. -/
theorem checkpoint_spec (score : ℕ → ℝ) (maxRounds patience : ℕ) :
    checkpoint score maxRounds patience ≤ stopRound score maxRounds patience ∧
    (∀ i ≤ stopRound score maxRounds patience,
      score (checkpoint score maxRounds patience) ≤ score i) ∧
    (∀ i ≤ stopRound score maxRounds patience,
      score i = score (checkpoint score maxRounds patience) →
        checkpoint score maxRounds patience ≤ i) :=
  ⟨bestIndex_le score _, bestIndex_minimal score _,
    fun _ hi hs => bestIndex_earliest score _ hi hs⟩

def validationScore {ι X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (validationRows : Finset ι) (x : ι → X) (y : ι → H) (models : ℕ → X → H) : ℕ → ℝ :=
  fun n => BoostingLoss.empiricalRisk validationRows x y (models n)

theorem validationScore_congr {ι X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (validationRows : Finset ι) (x : ι → X) (y y' : ι → H) (models : ℕ → X → H)
    (h : ∀ i ∈ validationRows, y i = y' i) :
    validationScore validationRows x y models = validationScore validationRows x y' models := by
  funext n
  unfold validationScore BoostingLoss.empiricalRisk
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

/-- For a fixed candidate-model sequence, changing outcomes outside validation
cannot change the checkpoint. This is not a claim that prior preprocessing or
training was independent of test data. -/
theorem checkpoint_ignores_other_outcomes {ι X H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (validationRows : Finset ι) (x : ι → X) (y y' : ι → H) (models : ℕ → X → H)
    (h : ∀ i ∈ validationRows, y i = y' i) (maxRounds patience : ℕ) :
    checkpoint (validationScore validationRows x y models) maxRounds patience =
      checkpoint (validationScore validationRows x y' models) maxRounds patience := by
  rw [validationScore_congr validationRows x y y' models h]

end Thesis.DayAhead.ValidationCheckpoint
