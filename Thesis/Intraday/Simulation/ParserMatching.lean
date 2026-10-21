import Mathlib.Tactic

/-! # Current reconstruction matching programme

Binary-channel equivalence and the outer Bellman programme's optimum over
order-preserving linked block pairs. `ParserPrograms` gives the literal
finite MILPs and attained inner maxima; `ParserLinks`, `ParserDecomposition`
and `ParserAssembly` prove the complete two-level exactness proposition.
-/

namespace Thesis.Intraday.ParserMatching

theorem channel_constraints (reductions additions : ℕ) :
    (∃ beta : ℕ, beta ≤ 1 ∧ reductions ≤ beta ∧ additions ≤ 1 - beta) ↔
      reductions + additions ≤ 1 := by
  constructor
  · rintro ⟨beta, hb, hr, ha⟩; omega
  · intro h; exact ⟨reductions, by omega, le_rfl, by omega⟩

/-- Original label: `defn:parser-inner-outer-programs`.
Generic outer recursion, instantiated by the actual finite inner optimum in
`ParserPrograms.terminalValue`. -/
noncomputable def value (score : ℕ → ℕ → ℝ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | n + 1, m + 1 =>
      if allowed n m then
        max (max (value score allowed n (m + 1)) (value score allowed (n + 1) m))
          (value score allowed n m + score n m)
      else max (value score allowed n (m + 1)) (value score allowed (n + 1) m)

/-- A path through the Bellman lattice describes exactly a strictly increasing
sequence of linked indices; skipped rows and columns carry no volume. -/
inductive Feasible (score : ℕ → ℕ → ℝ) (allowed : ℕ → ℕ → Prop) : ℕ → ℕ → ℝ → Prop
  | empty (n m : ℕ) : Feasible score allowed n m 0
  | skipRow {n m v} : Feasible score allowed n m v → Feasible score allowed (n + 1) m v
  | skipCol {n m v} : Feasible score allowed n m v → Feasible score allowed n (m + 1) v
  | link {n m v} : Feasible score allowed n m v → allowed n m →
      Feasible score allowed (n + 1) (m + 1) (v + score n m)

theorem value_nonneg (score : ℕ → ℕ → ℝ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] (n m : ℕ) : 0 ≤ value score allowed n m := by
  induction n generalizing m with
  | zero => simp [value]
  | succ n ih =>
    cases m with
    | zero => simp [value]
    | succ m =>
      simp only [value]
      split
      · exact (ih _).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (ih _).trans (le_max_left _ _)

theorem value_skipRow (score : ℕ → ℕ → ℝ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] (n m : ℕ) :
    value score allowed n m ≤ value score allowed (n + 1) m := by
  cases m with
  | zero => cases n <;> simp [value]
  | succ m =>
    simp only [value]
    split
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact le_max_left _ _

theorem value_skipCol (score : ℕ → ℕ → ℝ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] (n m : ℕ) :
    value score allowed n m ≤ value score allowed n (m + 1) := by
  cases n with
  | zero => simp [value]
  | succ n =>
    simp only [value]
    split
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _

theorem feasible_le_value (score : ℕ → ℕ → ℝ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] {n m : ℕ} {v : ℝ} (h : Feasible score allowed n m v) :
    v ≤ value score allowed n m := by
  induction h with
  | empty n m => exact value_nonneg _ _ _ _
  | skipRow h ih => exact ih.trans (value_skipRow _ _ _ _)
  | skipCol h ih => exact ih.trans (value_skipCol _ _ _ _)
  | link h ha ih =>
    rw [value, if_pos ha]
    exact (by linarith : _ ≤ _ + score _ _).trans (le_max_right _ _)

theorem value_attained (score : ℕ → ℕ → ℝ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] (n m : ℕ) :
    Feasible score allowed n m (value score allowed n m) := by
  induction n generalizing m with
  | zero => simpa only [value] using (Feasible.empty (score := score) (allowed := allowed) 0 m)
  | succ n ih =>
    induction m with
    | zero =>
      simpa only [value] using (Feasible.empty (score := score) (allowed := allowed) (n+1) 0)
    | succ m ihm =>
      rw [value]
      have hr := Feasible.skipRow (ih (m + 1))
      have hc := Feasible.skipCol ihm
      have hmax : Feasible score allowed (n + 1) (m + 1)
          (max (value score allowed n (m + 1)) (value score allowed (n + 1) m)) := by
        rcases le_total (value score allowed n (m + 1)) (value score allowed (n + 1) m) with h | h
        · simpa only [max_eq_right h] using hc
        · simpa only [max_eq_left h] using hr
      split
      · rename_i ha
        have hl := Feasible.link (ih m) ha
        rcases le_total (max (value score allowed n (m + 1)) (value score allowed (n + 1) m))
            (value score allowed n m + score n m) with h | h
        · simpa only [max_eq_right h] using hl
        · simpa only [max_eq_left h] using hmax
      · exact hmax

/-- Original label: `prop:parser-two-level-exactness`.
The generic outer optimum; the complete literal-MILP proposition is
`ParserAssembly.twoLevelBlockMatching_exactness`. -/
theorem exact_outer_optimum (score : ℕ → ℕ → ℝ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] (n m : ℕ) :
    Feasible score allowed n m (value score allowed n m) ∧
      ∀ v, Feasible score allowed n m v → v ≤ value score allowed n m :=
  ⟨value_attained _ _ _ _, fun _ h => feasible_le_value _ _ h⟩

end Thesis.Intraday.ParserMatching
