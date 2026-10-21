import Thesis.Intraday.Simulation.ParserPrograms
import Thesis.Intraday.Simulation.ParserLinks

/-! # Global assignment-to-link decomposition

The actual global MILP is bounded by the actual Bellman terminal value.
The proof constructs its constrained block-link set and bounds every block's
literal assignment objective by its attained inner optimum. `ParserAssembly`
proves the converse and the final equality for the literal finite MILPs.
-/

noncomputable section
namespace Thesis.Intraday.ParserDecomposition
open scoped BigOperators
open ParserPrograms

theorem true_unique_of_degree {ι : Type*} [Fintype ι] (f : ι → Bool)
    (hdegree : ∑ i, bit (f i) ≤ 1) {i j : ι} (hi : f i = true) (hj : f j = true) :
    i = j := by
  classical
  by_contra hne
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun i => bit (f i)) (Finset.subset_univ ({i, j} : Finset ι))
    (fun _ _ _ => Nat.zero_le _)
  have hpair : (∑ a ∈ ({i, j} : Finset ι), bit (f a)) = 2 := by
    rw [Finset.sum_pair hne, hi, hj]
    rfl
  rw [hpair] at hsub
  have htwo : 2 ≤ ∑ i, bit (f i) := hsub
  omega

def selectedLinks {n m N M : ℕ} (v : GlobalVariables n m N M) : Finset (ℕ × ℕ) :=
  (Finset.univ.filter fun a : Fin N × Fin M => v.z a.1 a.2).image
    (fun a => (a.1.val, a.2.val))

theorem mem_selectedLinks {n m N M : ℕ} (v : GlobalVariables n m N M) (a : ℕ × ℕ) :
    a ∈ selectedLinks v ↔ ∃ k : Fin N, ∃ l : Fin M,
      v.z k l = true ∧ (k.val, l.val) = a := by
  simp only [selectedLinks, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, l⟩, hz, he⟩
    exact ⟨k, l, hz, he⟩
  · rintro ⟨k, l, hz, he⟩
    exact ⟨(k, l), hz, he⟩

theorem selectedLinks_mk {n m N M : ℕ} (v : GlobalVariables n m N M)
    (k : Fin N) (l : Fin M) : (k.val, l.val) ∈ selectedLinks v ↔ v.z k l = true := by
  rw [mem_selectedLinks]
  constructor
  · rintro ⟨k', l', hz, he⟩
    have hk : k' = k := Fin.ext (congrArg Prod.fst he)
    have hl : l' = l := Fin.ext (congrArg Prod.snd he)
    simpa only [hk, hl] using hz
  · intro hz
    exact ⟨k, l, hz, rfl⟩

theorem selectedLinks_valid {n m N M : ℕ} (p : Problem n m N M)
    (v : GlobalVariables n m N M) (hv : globalFeasible p v) :
    ParserLinks.Valid (natGate p) N M (selectedLinks v) := by
  rcases hv with ⟨_, _, _, _, hcol, hrow, hcross, hgate⟩
  constructor
  · intro a ha
    obtain ⟨k, l, _, rfl⟩ := (mem_selectedLinks v a).1 ha
    exact ⟨k.isLt, l.isLt⟩
  · intro a ha b hb he
    obtain ⟨k, l, hz, rfl⟩ := (mem_selectedLinks v a).1 ha
    obtain ⟨k', l', hz', rfl⟩ := (mem_selectedLinks v b).1 hb
    have hk : k = k' := Fin.ext he
    subst k'
    have hl := true_unique_of_degree (v.z k) (hrow k) hz hz'
    exact Prod.ext rfl (congrArg Fin.val hl)
  · intro a ha b hb hlt
    obtain ⟨k, l, hz, rfl⟩ := (mem_selectedLinks v a).1 ha
    obtain ⟨k', l', hz', rfl⟩ := (mem_selectedLinks v b).1 hb
    by_contra hnot
    have hle : l' ≤ l := Nat.le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hl | hl
    · have hbad := hcross k k' l l' hlt hl
      simp only [hz, hz', bit, ↓reduceIte] at hbad
      omega
    · subst l'
      have hk := true_unique_of_degree (fun k => v.z k l) (hcol l) hz hz'
      have := congrArg Fin.val hk
      omega
  · intro a ha
    obtain ⟨k, l, hz, rfl⟩ := (mem_selectedLinks v a).1 ha
    refine ⟨k.isLt, l.isLt, ?_⟩
    by_contra hnot
    have hf := hgate k l hnot
    simp [hf] at hz

theorem restricted_objective_zero_unlinked {n m N M : ℕ} (p : Problem n m N M)
    (v : GlobalVariables n m N M) (hv : globalFeasible p v) (k : Fin N) (l : Fin M)
    (hz : v.z k l = false) : objective p (restrictAssignment p k l v.assignment) = 0 := by
  have hx (i : Fin n) (j : Fin m) :
      (restrictAssignment p k l v.assignment).x i j = false := by
    dsimp only [restrictAssignment]
    split_ifs with h
    · have he := hv.2.1 i j
      rw [h.1, h.2, hz] at he
      cases hb : v.assignment.x i j <;> simp_all [bit]
    · rfl
  have hy (i : Fin n) (j : Fin m) :
      (restrictAssignment p k l v.assignment).y i j = false := by
    dsimp only [restrictAssignment]
    split_ifs with h
    · have he := hv.2.2.1 i j
      rw [h.1, h.2, hz] at he
      cases hb : v.assignment.y i j <;> simp_all [bit]
    · rfl
  simp [objective, hx, hy, bit]

theorem blockObjective_le_link_score {n m N M : ℕ} (p : Problem n m N M)
    (v : GlobalVariables n m N M) (hv : globalFeasible p v) (k : Fin N) (l : Fin M) :
    blockObjective p v.assignment k l ≤ if v.z k l then innerMaximum p k l else 0 := by
  rw [← restricted_objective_eq_blockObjective]
  cases hz : v.z k l
  · simpa only [hz, Bool.false_eq_true, ↓reduceIte] using
      (restricted_objective_zero_unlinked p v hv k l hz).le
  · simpa only [hz, ↓reduceIte] using
      restricted_objective_le_innerMaximum p k l v.assignment hv.1

theorem finPairValues_injective {N M : ℕ} :
    Function.Injective (fun a : Fin N × Fin M => (a.1.val, a.2.val)) := by
  intro a b he
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

theorem sum_selectedLinks {n m N M : ℕ} (p : Problem n m N M)
    (v : GlobalVariables n m N M) :
    (∑ a ∈ selectedLinks v, natScore p a.1 a.2) =
      ∑ k, ∑ l, if v.z k l then innerMaximum p k l else 0 := by
  rw [selectedLinks, Finset.sum_image (fun _ _ _ _ h => finPairValues_injective h),
    Finset.sum_filter]
  simp only [natScore, Fin.isLt, and_self, ↓reduceDIte]
  exact Fintype.sum_prod_type _

theorem globalObjective_le_terminalValue {n m N M : ℕ} (p : Problem n m N M)
    (v : GlobalVariables n m N M) (hv : globalFeasible p v) :
    objective p v.assignment ≤ terminalValue p := by
  calc
    _ = ∑ k, ∑ l, blockObjective p v.assignment k l := objective_eq_sum_blockObjective p _
    _ ≤ ∑ k, ∑ l, if v.z k l then innerMaximum p k l else 0 :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
        blockObjective_le_link_score p v hv k l
    _ = ∑ a ∈ selectedLinks v, natScore p a.1 a.2 := (sum_selectedLinks p v).symm
    _ ≤ terminalValue p :=
      ParserMatching.feasible_le_value _ _ ((selectedLinks_valid p v hv).feasible (natScore p))

theorem globalMaximum_le_terminalValue {n m N M : ℕ} (p : Problem n m N M) :
    globalMaximum p ≤ terminalValue p := by
  obtain ⟨v, hv, he⟩ := (globalMaximum_isGreatest p).1
  rw [← he]
  exact globalObjective_le_terminalValue p v hv

end Thesis.Intraday.ParserDecomposition
