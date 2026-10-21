import Thesis.Appendices.DayAheadNumerical.PAVA.Blocks

/-! # Terminating pool-adjacent-violators algorithm

Each pass merges the first adjacent pair whose means are in decreasing order.
Every merge reduces the number of blocks by one. The original observations are
preserved in order, and the final block means are nondecreasing.
-/

noncomputable section
namespace Thesis.DayAhead.PAVA

def observations (blocks : List Block) : List ℝ := blocks.flatMap Block.data

def step : List Block → Option (List Block)
  | [] => none
  | [_] => none
  | a :: b :: rest =>
    if hab : mean a.data ≤ mean b.data then
      (step (b :: rest)).map (fun tail => a :: tail)
    else some (merge a b (le_of_not_ge hab) :: rest)

theorem step_length {xs ys : List Block} (h : step xs = some ys) :
    ys.length + 1 = xs.length := by
  induction xs generalizing ys with
  | nil => simp [step] at h
  | cons a xs ih =>
    cases xs with
    | nil => simp [step] at h
    | cons b rest =>
      rw [step] at h
      split at h
      · cases ht : step (b :: rest) with
        | none => simp [ht] at h
        | some tail =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst ys
          have := ih ht
          simp only [List.length_cons] at *
          omega
      · simp only [Option.some.injEq] at h
        subst ys
        simp

theorem step_observations {xs ys : List Block} (h : step xs = some ys) :
    observations ys = observations xs := by
  induction xs generalizing ys with
  | nil => simp [step] at h
  | cons a xs ih =>
    cases xs with
    | nil => simp [step] at h
    | cons b rest =>
      rw [step] at h
      split at h
      · cases ht : step (b :: rest) with
        | none => simp [ht] at h
        | some tail =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst ys
          change a.data ++ observations tail = a.data ++ observations (b :: rest)
          rw [ih ht]
      · simp only [Option.some.injEq] at h
        subst ys
        simp [observations, List.append_assoc]

theorem step_none_sorted {xs : List Block} (h : step xs = none) :
    xs.Pairwise (fun a b => mean a.data ≤ mean b.data) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b rest =>
      rw [step] at h
      split at h
      next hab =>
        have ht : step (b :: rest) = none := by simpa using h
        have hs := ih ht
        rw [List.pairwise_cons] at hs ⊢
        refine ⟨?_, List.pairwise_cons.mpr hs⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hab
        · exact hab.trans (hs.1 c hc)
      next => simp at h

def pool (xs : List Block) : List Block :=
  match _h : step xs with
  | none => xs
  | some ys => pool ys
termination_by xs.length
decreasing_by have := step_length _h; omega

theorem pool_spec (xs : List Block) :
    observations (pool xs) = observations xs ∧
      (pool xs).Pairwise (fun a b => mean a.data ≤ mean b.data) := by
  induction xs using pool.induct with
  | case1 xs h =>
    rw [pool, h]
    exact ⟨rfl, step_none_sorted h⟩
  | case2 xs ys h ih =>
    rw [pool, h]
    exact ⟨ih.1.trans (step_observations h), ih.2⟩

def fittedBlocks (xs : List ℝ) : List Block := pool (xs.map singleton)

theorem fittedBlocks_observations (xs : List ℝ) : observations (fittedBlocks xs) = xs := by
  rw [fittedBlocks, (pool_spec _).1]
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.map_cons, observations, List.flatMap_cons,
      singleton, List.singleton_append] using congrArg (List.cons x) ih

theorem fittedBlocks_sorted (xs : List ℝ) :
    (fittedBlocks xs).Pairwise (fun a b => mean a.data ≤ mean b.data) := (pool_spec _).2

end Thesis.DayAhead.PAVA
