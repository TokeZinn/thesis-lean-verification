import Thesis.Intraday.Simulation.ParserDecomposition

/-! # Assembly of attained inner matching optimisers

Selected block pairs use disjoint update and trade blocks. Their inner
solutions can therefore be assembled without violating either capacities or
single-trade assignment. Zero-score links are discarded before imposing the
source's nonempty-link constraint.
-/

noncomputable section
namespace Thesis.Intraday.ParserAssembly
open scoped BigOperators
open ParserPrograms ParserDecomposition

def innerChoice {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) : Assignment n m :=
  Classical.choose (innerMaximum_isGreatest p k l).1

theorem innerChoice_feasible {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) :
    innerFeasible p k l (innerChoice p k l) :=
  (Classical.choose_spec (innerMaximum_isGreatest p k l).1).1

theorem innerChoice_objective {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) :
    objective p (innerChoice p k l) = innerMaximum p k l :=
  (Classical.choose_spec (innerMaximum_isGreatest p k l).1).2

def matrix {n m : ℕ} (channel : Bool) (a : Assignment n m) : Fin n → Fin m → Bool :=
  if channel then a.x else a.y

theorem innerChoice_outside {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M)
    (channel : Bool) (i : Fin n) (j : Fin m)
    (h : p.orderBlock i ≠ k ∨ p.tradeBlock j ≠ l) :
    matrix channel (innerChoice p k l) i j = false := by
  cases channel
  · exact (innerChoice_feasible p k l).2.2 i j h
  · exact (innerChoice_feasible p k l).2.1 i j h

def joinedMatrix {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ))
    (channel : Bool) (i : Fin n) (j : Fin m) : Bool :=
  if ((p.orderBlock i).val, (p.tradeBlock j).val) ∈ s then
    matrix channel (innerChoice p (p.orderBlock i) (p.tradeBlock j)) i j else false

theorem joinedMatrix_column {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ))
    (hs : ParserLinks.Valid (natGate p) N M s) (k : Fin N) (l : Fin M)
    (hkl : (k.val, l.val) ∈ s) (channel : Bool) (i : Fin n) (j : Fin m)
    (hj : p.tradeBlock j = l) :
    joinedMatrix p s channel i j = matrix channel (innerChoice p k l) i j := by
  by_cases hi : p.orderBlock i = k
  · simp only [joinedMatrix, hi, hj, hkl, ↓reduceIte]
  · have hnot : ((p.orderBlock i).val, l.val) ∉ s := by
      intro hm
      have he := hs.column_unique _ hm _ hkl rfl
      exact hi (Fin.ext (congrArg Prod.fst he))
    rw [joinedMatrix, hj, if_neg hnot, innerChoice_outside p k l channel i j (Or.inl hi)]

theorem joinedMatrix_row {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ))
    (hs : ParserLinks.Valid (natGate p) N M s) (k : Fin N) (l : Fin M)
    (hkl : (k.val, l.val) ∈ s) (channel : Bool) (i : Fin n) (j : Fin m)
    (hi : p.orderBlock i = k) :
    joinedMatrix p s channel i j = matrix channel (innerChoice p k l) i j := by
  by_cases hj : p.tradeBlock j = l
  · simp only [joinedMatrix, hi, hj, hkl, ↓reduceIte]
  · have hnot : (k.val, (p.tradeBlock j).val) ∉ s := by
      intro hm
      have he := hs.row_unique _ hm _ hkl rfl
      exact hj (Fin.ext (congrArg Prod.snd he))
    rw [joinedMatrix, hi, if_neg hnot, innerChoice_outside p k l channel i j (Or.inr hj)]

theorem joinedMatrix_empty_column {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (l : Fin M) (hn : ¬∃ k : Fin N, (k.val, l.val) ∈ s)
    (channel : Bool) (i : Fin n) (j : Fin m) (hj : p.tradeBlock j = l) :
    joinedMatrix p s channel i j = false := by
  have hnot : ((p.orderBlock i).val, l.val) ∉ s := fun h => hn ⟨p.orderBlock i, h⟩
  simp only [joinedMatrix, hj, hnot, ↓reduceIte]

theorem joinedMatrix_empty_row {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (k : Fin N) (hn : ¬∃ l : Fin M, (k.val, l.val) ∈ s)
    (channel : Bool) (i : Fin n) (j : Fin m) (hi : p.orderBlock i = k) :
    joinedMatrix p s channel i j = false := by
  have hnot : (k.val, (p.tradeBlock j).val) ∉ s := fun h => hn ⟨p.tradeBlock j, h⟩
  simp only [joinedMatrix, hi, hnot, ↓reduceIte]

theorem joinedCounts_le_one {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ))
    (hs : ParserLinks.Valid (natGate p) N M s) :
    ∀ j, (∑ i, bit (joinedMatrix p s true i j)) +
      (∑ i, bit (joinedMatrix p s false i j)) ≤ 1 := by
  intro j
  by_cases hm : ∃ k : Fin N, (k.val, (p.tradeBlock j).val) ∈ s
  · obtain ⟨k, hk⟩ := hm
    simp_rw [joinedMatrix_column p s hs k (p.tradeBlock j) hk _ _ j rfl]
    exact (channel_constraints_bool _ _).1
      ⟨(innerChoice p k (p.tradeBlock j)).beta j,
        (innerChoice_feasible p k (p.tradeBlock j)).1.2.2.1 j⟩
  · simp only [joinedMatrix_empty_column p s (p.tradeBlock j) hm _ _ j rfl, bit,
      Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero, zero_add, Nat.zero_le]

def assembledAssignment {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ))
    (hs : ParserLinks.Valid (natGate p) N M s) : Assignment n m :=
  ⟨joinedMatrix p s true, joinedMatrix p s false,
    Classical.choose ((exists_channels_iff _ _).2 (joinedCounts_le_one p s hs))⟩

theorem assembledAssignment_channels {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s) :
    channels (assembledAssignment p s hs) :=
  Classical.choose_spec ((exists_channels_iff _ _).2 (joinedCounts_le_one p s hs))

theorem assembledAssignment_commonFeasible {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s) :
    commonFeasible p (assembledAssignment p s hs) := by
  refine ⟨?_, ?_, assembledAssignment_channels p s hs, ?_, ?_, ?_, ?_⟩
  · intro i hi j
    change joinedMatrix p s true i j = false
    unfold joinedMatrix
    split_ifs
    · exact (innerChoice_feasible p _ _).1.1 i hi j
    · rfl
  · intro i hi j
    change joinedMatrix p s false i j = false
    unfold joinedMatrix
    split_ifs
    · exact (innerChoice_feasible p _ _).1.2.1 i hi j
    · rfl
  · intro i hi
    change (∑ j, (bit (joinedMatrix p s true i j) : ℝ) * p.tradeQuantity j) ≤ p.capacity i
    by_cases hm : ∃ l : Fin M, ((p.orderBlock i).val, l.val) ∈ s
    · obtain ⟨l, hl⟩ := hm
      simp_rw [joinedMatrix_row p s hs (p.orderBlock i) l hl true i _ rfl]
      exact (innerChoice_feasible p (p.orderBlock i) l).1.2.2.2.1 i hi
    · simp only [joinedMatrix_empty_row p s (p.orderBlock i) hm true i _ rfl, bit,
        Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_mul, Finset.sum_const_zero]
      exact p.capacity_nonneg i
  · intro i j hb hp
    change joinedMatrix p s true i j = false
    unfold joinedMatrix
    split_ifs
    · exact (innerChoice_feasible p _ _).1.2.2.2.2.1 i j hb hp
    · rfl
  · intro i j hb hp
    change joinedMatrix p s true i j = false
    unfold joinedMatrix
    split_ifs
    · exact (innerChoice_feasible p _ _).1.2.2.2.2.2.1 i j hb hp
    · rfl
  · intro i j hp
    change joinedMatrix p s false i j = false
    unfold joinedMatrix
    split_ifs
    · exact (innerChoice_feasible p _ _).1.2.2.2.2.2.2 i j hp
    · rfl

def assembledGlobal {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ))
    (hs : ParserLinks.Valid (natGate p) N M s) : GlobalVariables n m N M :=
  ⟨assembledAssignment p s hs, fun k l => decide ((k.val, l.val) ∈ s)⟩

theorem assembledGlobal_z_true {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s)
    (k : Fin N) (l : Fin M) :
    (assembledGlobal p s hs).z k l = true ↔ (k.val, l.val) ∈ s := by
  simp only [assembledGlobal, decide_eq_true_eq]

theorem degree_le_one_of_true_unique {ι : Type*} [Fintype ι] (f : ι → Bool)
    (hu : ∀ i j, f i = true → f j = true → i = j) : ∑ i, bit (f i) ≤ 1 := by
  classical
  by_cases he : ∃ i, f i = true
  · obtain ⟨i, hi⟩ := he
    have hother (j : ι) (hj : j ≠ i) : f j = false := by
      cases h : f j
      · rfl
      · exact (hj (hu j i h hi)).elim
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [hother j hji, bit]) (by simp)]
    exact bit_le_one _
  · have hf (i : ι) : f i = false := by
      cases h : f i
      · rfl
      · exact (he ⟨i, h⟩).elim
    simp [hf, bit]

theorem objective_positive_edge {n m N M : ℕ} (p : Problem n m N M)
    (a : Assignment n m) (ha : 0 < objective p a) :
    ∃ i j, a.x i j = true ∨ a.y i j = true := by
  by_contra hnone
  have hx (i : Fin n) (j : Fin m) : a.x i j = false := by
    cases h : a.x i j
    · rfl
    · exact (hnone ⟨i, j, Or.inl h⟩).elim
  have hy (i : Fin n) (j : Fin m) : a.y i j = false := by
    cases h : a.y i j
    · rfl
    · exact (hnone ⟨i, j, Or.inr h⟩).elim
  simp [objective, hx, hy, bit] at ha

theorem innerChoice_true_blocks {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) (channel : Bool) (i : Fin n) (j : Fin m)
    (he : matrix channel (innerChoice p k l) i j = true) :
    p.orderBlock i = k ∧ p.tradeBlock j = l := by
  by_contra h
  have hf := innerChoice_outside p k l channel i j (not_and_or.mp h)
  rw [hf] at he
  cases he

def blockCount {n m N M : ℕ} (p : Problem n m N M) (a : Assignment n m)
    (k : Fin N) (l : Fin M) : ℕ :=
  (∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
    ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), bit (a.x i j)) +
  ∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
    ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), bit (a.y i j)

theorem blockCount_ge_one_of_edge {n m N M : ℕ} (p : Problem n m N M)
    (a : Assignment n m) (k : Fin N) (l : Fin M) (channel : Bool) (i : Fin n) (j : Fin m)
    (hi : p.orderBlock i = k) (hj : p.tradeBlock j = l)
    (he : matrix channel a i j = true) : 1 ≤ blockCount p a k l := by
  have hi' : i ∈ Finset.univ.filter (fun i => p.orderBlock i = k) := by simp [hi]
  have hj' : j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l) := by simp [hj]
  cases channel
  · have h₁ := Finset.single_le_sum (f := fun j => bit (a.y i j)) (fun _ _ => Nat.zero_le _) hj'
    have h₂ := Finset.single_le_sum
      (f := fun i => ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), bit (a.y i j))
      (fun _ _ => Nat.zero_le _) hi'
    have hbit : bit (a.y i j) = 1 := by rw [show a.y i j = true from he]; rfl
    change 1 ≤ _ + _
    have hcount : 1 ≤ ∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
        ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), bit (a.y i j) := by
      exact hbit ▸ h₁.trans h₂
    omega
  · have h₁ := Finset.single_le_sum (f := fun j => bit (a.x i j)) (fun _ _ => Nat.zero_le _) hj'
    have h₂ := Finset.single_le_sum
      (f := fun i => ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), bit (a.x i j))
      (fun _ _ => Nat.zero_le _) hi'
    have hbit : bit (a.x i j) = 1 := by rw [show a.x i j = true from he]; rfl
    change 1 ≤ _ + _
    have hcount : 1 ≤ ∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
        ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), bit (a.x i j) := by
      exact hbit ▸ h₁.trans h₂
    omega

theorem assembledGlobal_positive_link_nonempty {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s)
    (hpos : ∀ a ∈ s, 0 < natScore p a.1 a.2) (k : Fin N) (l : Fin M)
    (hkl : (k.val, l.val) ∈ s) :
    1 ≤ blockCount p (assembledGlobal p s hs).assignment k l := by
  have hp : 0 < innerMaximum p k l := by simpa only [natScore_eq] using hpos (k.val, l.val) hkl
  obtain ⟨i, j, he | he⟩ := objective_positive_edge p (innerChoice p k l)
    (by rwa [innerChoice_objective])
  · have hb := innerChoice_true_blocks p k l true i j he
    apply blockCount_ge_one_of_edge p _ k l true i j hb.1 hb.2
    exact (joinedMatrix_column p s hs k l hkl true i j hb.2).trans he
  · have hb := innerChoice_true_blocks p k l false i j he
    apply blockCount_ge_one_of_edge p _ k l false i j hb.1 hb.2
    exact (joinedMatrix_column p s hs k l hkl false i j hb.2).trans he

theorem assembledGlobal_feasible {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s)
    (hpos : ∀ a ∈ s, 0 < natScore p a.1 a.2) : globalFeasible p (assembledGlobal p s hs) := by
  refine ⟨assembledAssignment_commonFeasible p s hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change bit (joinedMatrix p s true i j) ≤ bit (decide _)
    by_cases hm : ((p.orderBlock i).val, (p.tradeBlock j).val) ∈ s
    · simpa only [hm, decide_true, bit, ↓reduceIte] using bit_le_one (joinedMatrix p s true i j)
    · simp [joinedMatrix, hm, bit]
  · intro i j
    change bit (joinedMatrix p s false i j) ≤ bit (decide _)
    by_cases hm : ((p.orderBlock i).val, (p.tradeBlock j).val) ∈ s
    · simpa only [hm, decide_true, bit, ↓reduceIte] using bit_le_one (joinedMatrix p s false i j)
    · simp [joinedMatrix, hm, bit]
  · intro k l
    change bit ((assembledGlobal p s hs).z k l) ≤ blockCount p _ k l
    cases hz : (assembledGlobal p s hs).z k l
    · simp only [bit, Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
    · exact assembledGlobal_positive_link_nonempty p s hs hpos k l
        ((assembledGlobal_z_true p s hs k l).1 hz)
  · intro l
    apply degree_le_one_of_true_unique
    intro k k' hk hk'
    exact Fin.ext (congrArg Prod.fst (hs.column_unique _
      ((assembledGlobal_z_true p s hs k l).1 hk) _
      ((assembledGlobal_z_true p s hs k' l).1 hk') rfl))
  · intro k
    apply degree_le_one_of_true_unique
    intro l l' hl hl'
    exact Fin.ext (congrArg Prod.snd (hs.row_unique _
      ((assembledGlobal_z_true p s hs k l).1 hl) _
      ((assembledGlobal_z_true p s hs k l').1 hl') rfl))
  · intro k k' l l' hk hl
    by_cases h₁ : (assembledGlobal p s hs).z k l = true
    · by_cases h₂ : (assembledGlobal p s hs).z k' l' = true
      · have hi := hs.increasing _ ((assembledGlobal_z_true p s hs k l).1 h₁) _
          ((assembledGlobal_z_true p s hs k' l').1 h₂) hk
        omega
      · have hf : (assembledGlobal p s hs).z k' l' = false := by
          cases hz : (assembledGlobal p s hs).z k' l' <;> simp_all
        simp [h₁, hf, bit]
    · have hf : (assembledGlobal p s hs).z k l = false := by
        cases hz : (assembledGlobal p s hs).z k l <;> simp_all
      simpa only [hf, bit, Bool.false_eq_true, ↓reduceIte, zero_add] using
        bit_le_one ((assembledGlobal p s hs).z k' l')
  · intro k l hnot
    have hm : (k.val, l.val) ∉ s := by
      intro hm
      exact hnot ((natGate_iff p k l).1 (hs.admissible _ hm))
    simp [assembledGlobal, hm]

theorem matrix_restrict {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M)
    (a : Assignment n m) (channel : Bool) (i : Fin n) (j : Fin m) :
    matrix channel (restrictAssignment p k l a) i j =
      if p.orderBlock i = k ∧ p.tradeBlock j = l then matrix channel a i j else false := by
  cases channel <;> rfl

theorem matrix_assembled {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ))
    (hs : ParserLinks.Valid (natGate p) N M s) (channel : Bool) (i : Fin n) (j : Fin m) :
    matrix channel (assembledGlobal p s hs).assignment i j = joinedMatrix p s channel i j := by
  cases channel <;> rfl

theorem restricted_matrix_selected {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s)
    (k : Fin N) (l : Fin M) (hkl : (k.val, l.val) ∈ s)
    (channel : Bool) (i : Fin n) (j : Fin m) :
    matrix channel (restrictAssignment p k l (assembledGlobal p s hs).assignment) i j =
      matrix channel (innerChoice p k l) i j := by
  rw [matrix_restrict]
  split_ifs with h
  · rw [matrix_assembled]
    exact joinedMatrix_column p s hs k l hkl channel i j h.2
  · exact (innerChoice_outside p k l channel i j (not_and_or.mp h)).symm

theorem assembled_blockObjective_selected {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s)
    (k : Fin N) (l : Fin M) (hkl : (k.val, l.val) ∈ s) :
    blockObjective p (assembledGlobal p s hs).assignment k l = innerMaximum p k l := by
  rw [← restricted_objective_eq_blockObjective]
  have hx (i : Fin n) (j : Fin m) :
      (restrictAssignment p k l (assembledGlobal p s hs).assignment).x i j =
        (innerChoice p k l).x i j := restricted_matrix_selected p s hs k l hkl true i j
  have hy (i : Fin n) (j : Fin m) :
      (restrictAssignment p k l (assembledGlobal p s hs).assignment).y i j =
        (innerChoice p k l).y i j := restricted_matrix_selected p s hs k l hkl false i j
  have he : objective p (restrictAssignment p k l (assembledGlobal p s hs).assignment) =
      objective p (innerChoice p k l) := by simp only [objective, hx, hy]
  exact he.trans (innerChoice_objective p k l)

theorem selectedLinks_assembled {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s) :
    selectedLinks (assembledGlobal p s hs) = s := by
  ext a
  constructor
  · intro ha
    obtain ⟨k, l, hz, rfl⟩ := (mem_selectedLinks _ a).1 ha
    exact (assembledGlobal_z_true p s hs k l).1 hz
  · intro ha
    have hb := hs.bounded a ha
    let k : Fin N := ⟨a.1, hb.1⟩
    let l : Fin M := ⟨a.2, hb.2⟩
    exact (mem_selectedLinks _ a).2
      ⟨k, l, (assembledGlobal_z_true p s hs k l).2 ha, Prod.eta a⟩

theorem assembledGlobal_objective {n m N M : ℕ} (p : Problem n m N M)
    (s : Finset (ℕ × ℕ)) (hs : ParserLinks.Valid (natGate p) N M s)
    (hpos : ∀ a ∈ s, 0 < natScore p a.1 a.2) :
    objective p (assembledGlobal p s hs).assignment = ∑ a ∈ s, natScore p a.1 a.2 := by
  have hv := assembledGlobal_feasible p s hs hpos
  calc
    _ = ∑ k, ∑ l, blockObjective p (assembledGlobal p s hs).assignment k l :=
      objective_eq_sum_blockObjective p _
    _ = ∑ k, ∑ l, if (assembledGlobal p s hs).z k l then innerMaximum p k l else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      cases hz : (assembledGlobal p s hs).z k l
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← restricted_objective_eq_blockObjective]
        exact restricted_objective_zero_unlinked p _ hv k l hz
      · exact assembled_blockObjective_selected p s hs k l
          ((assembledGlobal_z_true p s hs k l).1 hz)
    _ = ∑ a ∈ selectedLinks (assembledGlobal p s hs), natScore p a.1 a.2 :=
      (sum_selectedLinks p _).symm
    _ = _ := by rw [selectedLinks_assembled]

theorem natScore_nonneg {n m N M : ℕ} (p : Problem n m N M) (k l : ℕ) :
    0 ≤ natScore p k l := by
  unfold natScore
  split_ifs
  · exact innerMaximum_nonneg p _ _
  · exact le_rfl

def positiveLinks {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) := by
  classical
  exact s.filter fun a => 0 < natScore p a.1 a.2

theorem positiveLinks_valid {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ))
    (hs : ParserLinks.Valid (natGate p) N M s) :
    ParserLinks.Valid (natGate p) N M (positiveLinks p s) :=
  hs.subset (Finset.filter_subset _ _)

theorem positiveLinks_positive {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ)) :
    ∀ a ∈ positiveLinks p s, 0 < natScore p a.1 a.2 := by
  classical
  exact fun _ ha => (Finset.mem_filter.mp ha).2

theorem sum_positiveLinks {n m N M : ℕ} (p : Problem n m N M) (s : Finset (ℕ × ℕ)) :
    (∑ a ∈ positiveLinks p s, natScore p a.1 a.2) = ∑ a ∈ s, natScore p a.1 a.2 := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hnot
  have hn : ¬0 < natScore p a.1 a.2 := by
    intro hp
    exact hnot (Finset.mem_filter.mpr ⟨ha, hp⟩)
  exact le_antisymm (le_of_not_gt hn) (natScore_nonneg p _ _)

theorem terminalValue_le_globalMaximum {n m N M : ℕ} (p : Problem n m N M) :
    terminalValue p ≤ globalMaximum p := by
  obtain ⟨s, hs, he⟩ :=
    (ParserLinks.value_isGreatest_link_sum (natScore p) (natGate p) N M).1
  have ht := positiveLinks_valid p s hs
  have hp := positiveLinks_positive p s
  have hv := assembledGlobal_feasible p (positiveLinks p s) ht hp
  have ho := assembledGlobal_objective p (positiveLinks p s) ht hp
  have hvalue : objective p (assembledGlobal p (positiveLinks p s) ht).assignment =
      terminalValue p := ho.trans ((sum_positiveLinks p s).trans he)
  rw [← hvalue]
  exact (globalMaximum_isGreatest p).2 _ hv

/-- Original label: `prop:parser-two-level-exactness`.
The actual finite global integer-program maximum equals the actual terminal
Bellman value. Inner optimisers are assembled, and zero-volume links dropped,
so the source's reverse/nonempty-link constraint is preserved. -/
theorem twoLevelExact {n m N M : ℕ} (p : Problem n m N M) : TwoLevelExact p :=
  le_antisymm (terminalValue_le_globalMaximum p) (globalMaximum_le_terminalValue p)

/-- Both clauses of the source proposition, for the literal Boolean variables
and actual finite optimisation programmes. -/
theorem twoLevelBlockMatching_exactness {n m N M : ℕ} (p : Problem n m N M) :
    (∀ x y : Fin n → Fin m → Bool,
      (∃ beta, channels (⟨x, y, beta⟩ : Assignment n m)) ↔
        ∀ j, (∑ i, bit (x i j)) + (∑ i, bit (y i j)) ≤ 1) ∧
    terminalValue p = globalMaximum p :=
  ⟨exists_channels_iff, twoLevelExact p⟩

end Thesis.Intraday.ParserAssembly
