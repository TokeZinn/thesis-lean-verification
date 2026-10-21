import Thesis.Intraday.Simulation.ParserMatching

/-! # Exact constrained link sets and the Bellman lattice

Finite noncrossing block links with unique rows are exactly the skip/link
paths of the parser's dynamic programme. The increasing-column property
also forces unique columns. This is the combinatorial decomposition bridge;
the separate `ParserPrograms` file contains the literal assignment MILPs.
-/

namespace Thesis.Intraday.ParserLinks
open scoped BigOperators
open ParserMatching

structure Valid (gate : ℕ → ℕ → Prop) (n m : ℕ) (s : Finset (ℕ × ℕ)) : Prop where
  bounded : ∀ a ∈ s, a.1 < n ∧ a.2 < m
  row_unique : ∀ a ∈ s, ∀ b ∈ s, a.1 = b.1 → a = b
  increasing : ∀ a ∈ s, ∀ b ∈ s, a.1 < b.1 → a.2 < b.2
  admissible : ∀ a ∈ s, gate a.1 a.2

theorem Valid.empty (gate : ℕ → ℕ → Prop) (n m : ℕ) : Valid gate n m ∅ := by
  constructor <;> simp

theorem Valid.subset {gate : ℕ → ℕ → Prop} {n m : ℕ} {s t : Finset (ℕ × ℕ)}
    (h : Valid gate n m s) (ht : t ⊆ s) : Valid gate n m t :=
  ⟨fun a ha => h.bounded a (ht ha),
    fun a ha b hb => h.row_unique a (ht ha) b (ht hb),
    fun a ha b hb => h.increasing a (ht ha) b (ht hb),
    fun a ha => h.admissible a (ht ha)⟩

theorem Valid.mono {gate : ℕ → ℕ → Prop} {n m n' m' : ℕ}
    {s : Finset (ℕ × ℕ)} (h : Valid gate n m s) (hn : n ≤ n') (hm : m ≤ m') :
    Valid gate n' m' s :=
  { h with bounded := fun a ha =>
      ⟨(h.bounded a ha).1.trans_le hn, (h.bounded a ha).2.trans_le hm⟩ }

theorem Valid.column_unique {gate : ℕ → ℕ → Prop} {n m : ℕ}
    {s : Finset (ℕ × ℕ)} (h : Valid gate n m s) (a : ℕ × ℕ) (ha : a ∈ s)
    (b : ℕ × ℕ) (hb : b ∈ s) (he : a.2 = b.2) : a = b := by
  rcases lt_trichotomy a.1 b.1 with hab | hab | hab
  · exact (Nat.ne_of_lt (h.increasing a ha b hb hab) he).elim
  · exact h.row_unique a ha b hb hab
  · exact (Nat.ne_of_lt (h.increasing b hb a ha hab) he.symm).elim

theorem Valid.corner_not_mem {gate : ℕ → ℕ → Prop} {n m : ℕ}
    {s : Finset (ℕ × ℕ)} (h : Valid gate n m s) : (n, m) ∉ s := by
  intro hc
  have := (h.bounded (n, m) hc).1
  omega

theorem Valid.insert_corner {gate : ℕ → ℕ → Prop} {n m : ℕ}
    {s : Finset (ℕ × ℕ)} (h : Valid gate n m s) (hg : gate n m) :
    Valid gate (n + 1) (m + 1) (insert (n, m) s) := by
  constructor
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨Nat.lt_succ_self _, Nat.lt_succ_self _⟩
    · exact ⟨(h.bounded a ha).1.trans (Nat.lt_succ_self _),
        (h.bounded a ha).2.trans (Nat.lt_succ_self _)⟩
  · intro a ha b hb he
    rcases Finset.mem_insert.mp ha with rfl | ha <;>
      rcases Finset.mem_insert.mp hb with rfl | hb
    · rfl
    · have := (h.bounded b hb).1
      omega
    · have := (h.bounded a ha).1
      omega
    · exact h.row_unique a ha b hb he
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha <;>
      rcases Finset.mem_insert.mp hb with rfl | hb
    · exact (Nat.lt_irrefl _ hab).elim
    · have := (h.bounded b hb).1
      omega
    · exact (h.bounded a ha).2
    · exact h.increasing a ha b hb hab
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hg
    · exact h.admissible a ha

theorem Valid.erase_corner {gate : ℕ → ℕ → Prop} {n m : ℕ}
    {s : Finset (ℕ × ℕ)} (h : Valid gate (n + 1) (m + 1) s) (hc : (n, m) ∈ s) :
    Valid gate n m (s.erase (n, m)) := by
  have ht := h.subset (Finset.erase_subset (n, m) s)
  refine { ht with bounded := ?_ }
  intro a ha
  have ha' := Finset.mem_of_mem_erase ha
  have hne := (Finset.mem_erase.mp ha).1
  have haN := (h.bounded a ha').1
  have han : a.1 < n := by
    by_contra hnot
    have he : a.1 = n := by omega
    exact hne (h.row_unique a ha' (n, m) hc he)
  exact ⟨han, h.increasing a ha' (n, m) hc han⟩

theorem Valid.empty_boundary {gate : ℕ → ℕ → Prop} {n m : ℕ}
    {s : Finset (ℕ × ℕ)} (h : Valid gate n m s) (hz : n = 0 ∨ m = 0) : s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have := h.bounded a ha
  omega

theorem Valid.peel {gate : ℕ → ℕ → Prop} {n m : ℕ} {s : Finset (ℕ × ℕ)}
    (h : Valid gate (n + 1) (m + 1) s) (hc : (n, m) ∉ s) :
    Valid gate n (m + 1) s ∨ Valid gate (n + 1) m s := by
  by_cases hr : ∃ l, (n, l) ∈ s
  · right
    obtain ⟨l, hl⟩ := hr
    refine { h with bounded := ?_ }
    intro a ha
    have haBound := h.bounded a ha
    refine ⟨haBound.1, ?_⟩
    by_contra hnot
    have ham : a.2 = m := by omega
    have han : a.1 < n := by
      by_contra hnot'
      have han' : a.1 = n := by omega
      have he : a = (n, m) := Prod.ext han' ham
      exact hc (he ▸ ha)
    have hinc := h.increasing a ha (n, l) hl han
    have hlBound := (h.bounded (n, l) hl).2
    omega
  · left
    refine { h with bounded := ?_ }
    intro a ha
    have hb := h.bounded a ha
    refine ⟨?_, hb.2⟩
    by_contra hnot
    have he : a.1 = n := by omega
    exact hr ⟨a.2, (Prod.eta a).symm ▸ (he ▸ ha)⟩

/-- A literal constrained finite link set produces a Bellman path with exactly
its summed inner scores, including zero-score links. -/
theorem Valid.feasible {gate : ℕ → ℕ → Prop} {n m : ℕ} {s : Finset (ℕ × ℕ)}
    (h : Valid gate n m s) (score : ℕ → ℕ → ℝ) :
    Feasible score gate n m (∑ a ∈ s, score a.1 a.2) := by
  induction n generalizing m s with
  | zero =>
    rw [h.empty_boundary (Or.inl rfl)]
    simpa using (Feasible.empty (score := score) (allowed := gate) 0 m)
  | succ n ihn =>
    induction m with
    | zero =>
      rw [h.empty_boundary (Or.inr rfl)]
      simpa using (Feasible.empty (score := score) (allowed := gate) (n + 1) 0)
    | succ m ihm =>
      by_cases hc : (n, m) ∈ s
      · have hp := Feasible.link (ihn (h.erase_corner hc)) (h.admissible (n, m) hc)
        have he : (∑ a ∈ s.erase (n, m), score a.1 a.2) + score n m =
            ∑ a ∈ s, score a.1 a.2 := Finset.sum_erase_add _ _ hc
        exact he ▸ hp
      · rcases h.peel hc with hr | hcol
        · exact Feasible.skipRow (ihn hr)
        · exact Feasible.skipCol (ihm hcol)

theorem feasible_exists_links {gate : ℕ → ℕ → Prop} {score : ℕ → ℕ → ℝ}
    {n m : ℕ} {v : ℝ} (h : Feasible score gate n m v) :
    ∃ s : Finset (ℕ × ℕ), Valid gate n m s ∧ (∑ a ∈ s, score a.1 a.2) = v := by
  induction h with
  | empty n m => exact ⟨∅, Valid.empty _ _ _, by simp⟩
  | skipRow h ih =>
    obtain ⟨s, hs, he⟩ := ih
    exact ⟨s, hs.mono (Nat.le_succ _) le_rfl, he⟩
  | skipCol h ih =>
    obtain ⟨s, hs, he⟩ := ih
    exact ⟨s, hs.mono le_rfl (Nat.le_succ _), he⟩
  | @link n m v h hg ih =>
    obtain ⟨s, hs, he⟩ := ih
    refine ⟨insert (n, m) s, hs.insert_corner hg, ?_⟩
    rw [Finset.sum_insert hs.corner_not_mem, he]
    exact add_comm _ _

/-- Exact weighted noncrossing-matching optimum, independently of the MILP
assignment decomposition. Both directions are actual constructions. -/
theorem value_isGreatest_link_sum (score : ℕ → ℕ → ℝ) (gate : ℕ → ℕ → Prop)
    [DecidableRel gate] (n m : ℕ) :
    (∃ s : Finset (ℕ × ℕ), Valid gate n m s ∧
      (∑ a ∈ s, score a.1 a.2) = value score gate n m) ∧
    (∀ s : Finset (ℕ × ℕ), Valid gate n m s →
      (∑ a ∈ s, score a.1 a.2) ≤ value score gate n m) :=
  ⟨feasible_exists_links (value_attained _ _ _ _),
    fun _ hs => feasible_le_value _ _ (hs.feasible score)⟩

end Thesis.Intraday.ParserLinks
