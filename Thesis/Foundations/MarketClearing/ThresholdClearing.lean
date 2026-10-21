import Thesis.Foundations.MarketClearing.QuantityPerturbation

/-! # Price-level characterization of the existing clearing formula

Grouping all equal-price orders removes dependence on their internal ordering.
This is a proof device for the actual cumulative compatible-volume rule.
-/

noncomputable section
namespace Thesis.Foundations.MarketClearing.ThresholdClearing

open MarketRepresentation TuplesBasic FiniteSets
open Sorting Equilibrium

def prefixQuantity {n : ℕ} (q : Fin n → Quantity) (i : Fin n) : Quantity :=
  ∑ j, if j ≤ i then q j else 0

def below {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity) (r : ℝ) : Quantity :=
  ∑ j, if p j ≤ r then q j else 0

def above {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity) (r : ℝ) : Quantity :=
  ∑ j, if r ≤ p j then q j else 0

theorem prefix_le_below {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (hp : Monotone p) (i : Fin n) : prefixQuantity q i ≤ below p q (p i) := by
  apply Finset.sum_le_sum
  intro j _
  by_cases h : j ≤ i
  · simp only [if_pos h, if_pos (hp h)]
    exact le_rfl
  · simp only [if_neg h]
    exact zero_le _

theorem prefix_le_above {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (hp : Antitone p) (i : Fin n) : prefixQuantity q i ≤ above p q (p i) := by
  apply Finset.sum_le_sum
  intro j _
  by_cases h : j ≤ i
  · simp only [if_pos h, if_pos (hp h)]
    exact le_rfl
  · simp only [if_neg h]
    exact zero_le _

theorem exists_prefix_below {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (hp : Monotone p) (i : Fin n) : ∃ k, p k = p i ∧ prefixQuantity q k = below p q (p i) := by
  let s := Finset.univ.filter (fun j => p j ≤ p i)
  have hi : i ∈ s := by simp [s]
  let k := s.max' ⟨i, hi⟩
  have hk : k ∈ s := Finset.max'_mem _ _
  have hik : i ≤ k := Finset.le_max' _ _ hi
  have hpk : p k = p i := le_antisymm (Finset.mem_filter.mp hk).2 (hp hik)
  refine ⟨k, hpk, ?_⟩
  apply Finset.sum_congr rfl
  intro j _
  have hj : j ≤ k ↔ p j ≤ p i := by
    constructor
    · intro h
      exact (hp h).trans_eq hpk
    · intro h
      exact Finset.le_max' _ _ (by simp [s, h])
  simp only [hj]

theorem exists_prefix_above {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (hp : Antitone p) (i : Fin n) : ∃ k, p k = p i ∧ prefixQuantity q k = above p q (p i) := by
  let s := Finset.univ.filter (fun j => p i ≤ p j)
  have hi : i ∈ s := by simp [s]
  let k := s.max' ⟨i, hi⟩
  have hk : k ∈ s := Finset.max'_mem _ _
  have hik : i ≤ k := Finset.le_max' _ _ hi
  have hpk : p k = p i := le_antisymm (hp hik) (Finset.mem_filter.mp hk).2
  refine ⟨k, hpk, ?_⟩
  apply Finset.sum_congr rfl
  intro j _
  have hj : j ≤ k ↔ p i ≤ p j := by
    constructor
    · intro h
      exact hpk ▸ hp h
    · intro h
      exact Finset.le_max' _ _ (by simp [s, h])
  simp only [hj]

def cumulativeVolume {n m : ℕ} (ps : Fin n → ℝ) (qs : Fin n → Quantity)
    (pb : Fin m → ℝ) (qb : Fin m → Quantity) : Quantity :=
  Finset.univ.sup fun ij : Fin n × Fin m =>
    if ps ij.1 ≤ pb ij.2 then min (prefixQuantity qs ij.1) (prefixQuantity qb ij.2) else 0

def thresholdVolume {n m : ℕ} (ps : Fin n → ℝ) (qs : Fin n → Quantity)
    (pb : Fin m → ℝ) (qb : Fin m → Quantity) : Quantity :=
  Finset.univ.sup fun ij : Fin n × Fin m =>
    if ps ij.1 ≤ pb ij.2 then min (below ps qs (ps ij.1)) (above pb qb (pb ij.2)) else 0

theorem cumulativeVolume_eq_thresholdVolume {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (hs : Monotone ps) (hb : Antitone pb) :
    cumulativeVolume ps qs pb qb = thresholdVolume ps qs pb qb := by
  apply le_antisymm
  · apply Finset.sup_mono_fun
    intro ij _
    split_ifs
    · exact min_le_min (prefix_le_below ps qs hs ij.1) (prefix_le_above pb qb hb ij.2)
    · exact le_rfl
  · apply Finset.sup_le
    intro ij _
    by_cases h : ps ij.1 ≤ pb ij.2
    · simp only [if_pos h]
      obtain ⟨i, hi, hqs⟩ := exists_prefix_below ps qs hs ij.1
      obtain ⟨j, hj, hqb⟩ := exists_prefix_above pb qb hb ij.2
      have hij : ps i ≤ pb j := by rwa [hi, hj]
      have hle := Finset.le_sup (f := fun ij : Fin n × Fin m =>
        if ps ij.1 ≤ pb ij.2 then min (prefixQuantity qs ij.1) (prefixQuantity qb ij.2) else 0)
        (Finset.mem_univ (i, j))
      simpa only [if_pos hij, hqs, hqb] using hle
    · simp only [if_neg h]
      exact zero_le _

theorem eval_cumulative {n : ℕ} (q : Fin n → Quantity) (i : Fin n) :
    tupleQuantityEval i.val (cumulativeQuantityTuple ⟨n, q⟩) = prefixQuantity q i :=
  dif_pos i.isLt

theorem equilibrium_eq_cumulativeVolume {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity) :
    equilibriumQuantity ((cumulativeQuantityTuple ⟨n, qs⟩, ⟨n, ps⟩),
      (cumulativeQuantityTuple ⟨m, qb⟩, ⟨m, pb⟩)) = cumulativeVolume ps qs pb qb := by
  dsimp only [equilibriumQuantity, maxClearedQuantityForIndexSet, cumulativeVolume]
  apply le_antisymm
  · apply Finset.sup_le
    intro ij hij
    have hmem := (FiniteSubsets.mem_toFinset _).mp hij
    obtain ⟨hi, hj, hp⟩ := (mem_feasibleEquilibriumIndexSet ⟨n, ps⟩ ⟨m, pb⟩).mp hmem
    change ps ⟨ij.1, hi⟩ ≤ pb ⟨ij.2, hj⟩ at hp
    have he : clearedQuantityAt (cumulativeQuantityTuple ⟨n, qs⟩)
        (cumulativeQuantityTuple ⟨m, qb⟩) ij =
        min (prefixQuantity qs ⟨ij.1, hi⟩) (prefixQuantity qb ⟨ij.2, hj⟩) := by
      dsimp only [clearedQuantityAt]
      rw [eval_cumulative qs ⟨ij.1, hi⟩, eval_cumulative qb ⟨ij.2, hj⟩]
    rw [he]
    have h := Finset.le_sup (f := fun ij : Fin n × Fin m =>
      if ps ij.1 ≤ pb ij.2 then min (prefixQuantity qs ij.1) (prefixQuantity qb ij.2) else 0)
      (Finset.mem_univ (⟨ij.1, hi⟩, ⟨ij.2, hj⟩))
    simpa only [if_pos hp] using h
  · apply Finset.sup_le
    intro ij _
    by_cases hp : ps ij.1 ≤ pb ij.2
    · simp only [if_pos hp]
      have hmem : (ij.1.val, ij.2.val) ∈ FiniteSubsets.toFinset
          (feasibleEquilibriumIndexSet ⟨n, ps⟩ ⟨m, pb⟩) :=
        (FiniteSubsets.mem_toFinset _).mpr ⟨ij.1.isLt, ij.2.isLt, hp⟩
      have h := Finset.le_sup
        (f := clearedQuantityAt (cumulativeQuantityTuple ⟨n, qs⟩) (cumulativeQuantityTuple ⟨m, qb⟩))
        hmem
      simpa only [clearedQuantityAt, eval_cumulative] using h
    · simp only [if_neg hp]
      exact zero_le _

theorem equilibrium_eq_thresholdVolume {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (hs : Monotone ps) (hb : Antitone pb) :
    equilibriumQuantity ((cumulativeQuantityTuple ⟨n, qs⟩, ⟨n, ps⟩),
      (cumulativeQuantityTuple ⟨m, qb⟩, ⟨m, pb⟩)) = thresholdVolume ps qs pb qb := by
  rw [equilibrium_eq_cumulativeVolume, cumulativeVolume_eq_thresholdVolume ps qs pb qb hs hb]

theorem below_permutation {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (π : FinitePermutation n) (r : ℝ) :
    below (fun i => p (π i)) (fun i => q (π i)) r = below p q r :=
  Equiv.sum_comp π (fun i => if p i ≤ r then q i else 0)

theorem above_permutation {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity)
    (π : FinitePermutation n) (r : ℝ) :
    above (fun i => p (π i)) (fun i => q (π i)) r = above p q r :=
  Equiv.sum_comp π (fun i => if r ≤ p i then q i else 0)

theorem thresholdVolume_permutation_le {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (π : FinitePermutation n) (ρ : FinitePermutation m) :
    thresholdVolume (fun i => ps (π i)) (fun i => qs (π i))
      (fun j => pb (ρ j)) (fun j => qb (ρ j)) ≤ thresholdVolume ps qs pb qb := by
  apply Finset.sup_le
  intro ij _
  simp only [below_permutation, above_permutation]
  exact Finset.le_sup (f := fun ij : Fin n × Fin m =>
    if ps ij.1 ≤ pb ij.2 then min (below ps qs (ps ij.1)) (above pb qb (pb ij.2)) else 0)
    (Finset.mem_univ (π ij.1, ρ ij.2))

theorem thresholdVolume_permutation {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (π : FinitePermutation n) (ρ : FinitePermutation m) :
    thresholdVolume (fun i => ps (π i)) (fun i => qs (π i))
      (fun j => pb (ρ j)) (fun j => qb (ρ j)) = thresholdVolume ps qs pb qb := by
  apply le_antisymm (thresholdVolume_permutation_le ps qs pb qb π ρ)
  simpa only [Equiv.apply_symm_apply] using thresholdVolume_permutation_le
    (fun i => ps (π i)) (fun i => qs (π i))
    (fun j => pb (ρ j)) (fun j => qb (ρ j)) π.symm ρ.symm

/-- A price cut need not occur among the order prices. Its feasible quantity
is still bounded by the existing finite candidate maximum. -/
theorem arbitrary_threshold_le {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (r t : ℝ) (hrt : r ≤ t) :
    min (below ps qs r) (above pb qb t) ≤ thresholdVolume ps qs pb qb := by
  let s := Finset.univ.filter (fun i => ps i ≤ r)
  let b := Finset.univ.filter (fun j => t ≤ pb j)
  by_cases hs : s.Nonempty
  · by_cases hb : b.Nonempty
    · obtain ⟨i, hi, himax⟩ := Finset.exists_max_image s ps hs
      obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image b pb hb
      have hir : ps i ≤ r := (Finset.mem_filter.mp hi).2
      have htj : t ≤ pb j := (Finset.mem_filter.mp hj).2
      have hs' : below ps qs r = below ps qs (ps i) := by
        apply Finset.sum_congr rfl
        intro k _
        have h : ps k ≤ r ↔ ps k ≤ ps i :=
          ⟨fun h => himax k (by simp [s, h]), fun h => h.trans hir⟩
        simp only [h]
      have hb' : above pb qb t = above pb qb (pb j) := by
        apply Finset.sum_congr rfl
        intro k _
        have h : t ≤ pb k ↔ pb j ≤ pb k :=
          ⟨fun h => hjmin k (by simp [b, h]), fun h => htj.trans h⟩
        simp only [h]
      rw [hs', hb']
      have hp := hir.trans (hrt.trans htj)
      have h := Finset.le_sup (f := fun ij : Fin n × Fin m =>
        if ps ij.1 ≤ pb ij.2 then min (below ps qs (ps ij.1)) (above pb qb (pb ij.2)) else 0)
        (Finset.mem_univ (i, j))
      simpa only [if_pos hp] using h
    · have he : above pb qb t = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have h : ¬t ≤ pb j := fun h => hb ⟨j, by simp [b, h]⟩
        exact if_neg h
      rw [he, min_eq_right (zero_le _)]
      exact zero_le _
  · have he : below ps qs r = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have h : ¬ps i ≤ r := fun h => hs ⟨i, by simp [s, h]⟩
      exact if_neg h
    rw [he, min_eq_left (zero_le _)]
    exact zero_le _

theorem below_prepend {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity) (p₀ r : ℝ) (q₀ : Quantity) :
    below (Fin.append (fun _ : Fin 1 => p₀) p) (Fin.append (fun _ : Fin 1 => q₀) q) r =
      (if p₀ ≤ r then q₀ else 0) + below p q r := by
  dsimp only [below]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_one]

theorem above_prepend {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity) (p₀ r : ℝ) (q₀ : Quantity) :
    above (Fin.append (fun _ : Fin 1 => p₀) p) (Fin.append (fun _ : Fin 1 => q₀) q) r =
      (if r ≤ p₀ then q₀ else 0) + above p q r := by
  dsimp only [above]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_one]

theorem thresholdVolume_le_prepend_buy {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (p₀ : ℝ) (q₀ : Quantity) :
    thresholdVolume ps qs pb qb ≤ thresholdVolume ps qs
      (Fin.append (fun _ : Fin 1 => p₀) pb) (Fin.append (fun _ : Fin 1 => q₀) qb) := by
  apply Finset.sup_le
  intro ij _
  by_cases hp : ps ij.1 ≤ pb ij.2
  · simp only [if_pos hp]
    have h := Finset.le_sup (f := fun ij : Fin n × Fin (1 + m) =>
      if ps ij.1 ≤ (Fin.append (fun _ : Fin 1 => p₀) pb) ij.2 then
        min (below ps qs (ps ij.1))
          (above (Fin.append (fun _ : Fin 1 => p₀) pb) (Fin.append (fun _ : Fin 1 => q₀) qb)
            ((Fin.append (fun _ : Fin 1 => p₀) pb) ij.2)) else 0)
      (Finset.mem_univ (ij.1, Fin.natAdd 1 ij.2))
    conv at h => lhs; simp only [Fin.append_right, if_pos hp, above_prepend]
    exact (min_le_min_left _ (le_add_of_nonneg_left (zero_le _))).trans h
  · simp only [if_neg hp]
    exact zero_le _

theorem thresholdVolume_prepend_zero_buy {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (p₀ : ℝ) :
    thresholdVolume ps qs (Fin.append (fun _ : Fin 1 => p₀) pb)
      (Fin.append (fun _ : Fin 1 => 0) qb) = thresholdVolume ps qs pb qb := by
  apply le_antisymm
  · apply Finset.sup_le
    intro ij _
    split_ifs with hp
    · rw [above_prepend]
      simp only [ite_self, zero_add]
      exact arbitrary_threshold_le ps qs pb qb _ _ hp
    · exact zero_le _
  · exact thresholdVolume_le_prepend_buy ps qs pb qb p₀ 0

theorem thresholdVolume_le_prepend_sell {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (p₀ : ℝ) (q₀ : Quantity) :
    thresholdVolume ps qs pb qb ≤ thresholdVolume
      (Fin.append (fun _ : Fin 1 => p₀) ps) (Fin.append (fun _ : Fin 1 => q₀) qs) pb qb := by
  apply Finset.sup_le
  intro ij _
  by_cases hp : ps ij.1 ≤ pb ij.2
  · simp only [if_pos hp]
    have h := Finset.le_sup (f := fun ij : Fin (1 + n) × Fin m =>
      if (Fin.append (fun _ : Fin 1 => p₀) ps) ij.1 ≤ pb ij.2 then
        min (below (Fin.append (fun _ : Fin 1 => p₀) ps) (Fin.append (fun _ : Fin 1 => q₀) qs)
          ((Fin.append (fun _ : Fin 1 => p₀) ps) ij.1)) (above pb qb (pb ij.2)) else 0)
      (Finset.mem_univ (Fin.natAdd 1 ij.1, ij.2))
    conv at h => lhs; simp only [Fin.append_right, if_pos hp, below_prepend]
    exact (min_le_min_right _ (le_add_of_nonneg_left (zero_le _))).trans h
  · simp only [if_neg hp]
    exact zero_le _

theorem thresholdVolume_prepend_zero_sell {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (p₀ : ℝ) :
    thresholdVolume (Fin.append (fun _ : Fin 1 => p₀) ps)
      (Fin.append (fun _ : Fin 1 => 0) qs) pb qb = thresholdVolume ps qs pb qb := by
  apply le_antisymm
  · apply Finset.sup_le
    intro ij _
    split_ifs with hp
    · rw [below_prepend]
      simp only [ite_self, zero_add]
      exact arbitrary_threshold_le ps qs pb qb _ _ hp
    · exact zero_le _
  · exact thresholdVolume_le_prepend_sell ps qs pb qb p₀ 0

theorem thresholdVolume_prepend_buy_le {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (p₀ : ℝ) (q₀ : Quantity) :
    thresholdVolume ps qs (Fin.append (fun _ : Fin 1 => p₀) pb)
      (Fin.append (fun _ : Fin 1 => q₀) qb) ≤ thresholdVolume ps qs pb qb + q₀ := by
  apply Finset.sup_le
  intro ij _
  split_ifs with hp
  · rw [above_prepend]
    apply le_trans _ (add_le_add (arbitrary_threshold_le ps qs pb qb _ _ hp) le_rfl)
    rw [← min_add_add_right]
    apply min_le_min (le_add_of_nonneg_right q₀.coe_nonneg)
    split_ifs <;> simp [add_comm]
  · exact zero_le _

theorem thresholdVolume_prepend_sell_le {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (p₀ : ℝ) (q₀ : Quantity) :
    thresholdVolume (Fin.append (fun _ : Fin 1 => p₀) ps)
      (Fin.append (fun _ : Fin 1 => q₀) qs) pb qb ≤ thresholdVolume ps qs pb qb + q₀ := by
  apply Finset.sup_le
  intro ij _
  split_ifs with hp
  · rw [below_prepend]
    apply le_trans _ (add_le_add (arbitrary_threshold_le ps qs pb qb _ _ hp) le_rfl)
    rw [← min_add_add_right]
    apply min_le_min _ (le_add_of_nonneg_right q₀.coe_nonneg)
    split_ifs <;> simp [add_comm]
  · exact zero_le _

end Thesis.Foundations.MarketClearing.ThresholdClearing
