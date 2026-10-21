import Thesis.Foundations.MarketClearing.Equilibrium

/-! # Quantity perturbations through sorting, aggregation and clearing

A common permutation preserves a nonnegative perturbation's total mass.
Every cumulative entry changes by at most that mass, and the finite compatible
maximum has the same bound. No distinct-price or strictly-positive-order
assumption is used.
-/

noncomputable section
namespace Thesis.Foundations.MarketClearing.QuantityPerturbation

open MarketRepresentation TuplesBasic TuplesMeasurableSorting FiniteSets
open MarketActions.Primitive Sorting Equilibrium

def IncreasesWithin (x y : Tuple Quantity) (δ : Quantity) : Prop :=
  ∃ (n : ℕ) (a d : Fin n → Quantity), x = ⟨n, a⟩ ∧ y = ⟨n, fun i => a i + d i⟩ ∧
    ∑ i, d i ≤ δ

theorem increasesWithin_refl (x : Tuple Quantity) (δ : Quantity) : IncreasesWithin x x δ := by
  rcases x with ⟨n, a⟩
  exact ⟨n, a, fun _ => 0, rfl, by simp, by simp⟩

theorem increasesWithin_prepend (x : Tuple Quantity) (q δ : Quantity) :
    IncreasesWithin (concat ⟨1, fun _ => q⟩ x) (concat ⟨1, fun _ => q + δ⟩ x) δ := by
  refine ⟨1 + x.1, Fin.append (fun _ : Fin 1 => q) x.2,
    Fin.append (fun _ : Fin 1 => δ) (fun _ : Fin x.1 => 0), rfl, ?_, ?_⟩
  · refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;>
      simp [concat, Tuple.entry, Tuple.length]
  · rw [Fin.sum_univ_add]
    simp

theorem IncreasesWithin.permutationMap {x y : Tuple Quantity} {δ : Quantity}
    (h : IncreasesWithin x y δ) (π : FinitePermutations) :
    IncreasesWithin (permutationMap x π) (permutationMap y π) δ := by
  rcases h with ⟨n, a, d, rfl, rfl, hd⟩
  rcases π with ⟨m, π⟩
  by_cases hn : n = m
  · subst m
    simp only [permutationMap_same_length, permute, Tuple.length, Tuple.entry]
    refine ⟨n, fun i => a (π i), fun i => d (π i), rfl, rfl, ?_⟩
    rwa [Equiv.sum_comp π]
  · rw [permutationMap_ne_length hn, permutationMap_ne_length hn]
    exact increasesWithin_refl _ _

theorem IncreasesWithin.cumulative_bounds {x y : Tuple Quantity} {δ : Quantity}
    (h : IncreasesWithin x y δ) (k : ℕ) :
    tupleQuantityEval k (cumulativeQuantityTuple x) ≤
      tupleQuantityEval k (cumulativeQuantityTuple y) ∧
    tupleQuantityEval k (cumulativeQuantityTuple y) ≤
      tupleQuantityEval k (cumulativeQuantityTuple x) + δ := by
  rcases h with ⟨n, a, d, rfl, rfl, hd⟩
  by_cases hk : k < n
  · simp only [cumulativeQuantityTuple, tupleQuantityEval, Tuple.length, Tuple.entry, dif_pos hk]
    change ((∑ j : Fin n, if j ≤ ⟨k, hk⟩ then a j else 0) ≤
        ∑ j : Fin n, if j ≤ ⟨k, hk⟩ then a j + d j else 0) ∧
      (∑ j : Fin n, if j ≤ ⟨k, hk⟩ then a j + d j else 0) ≤
        (∑ j : Fin n, if j ≤ ⟨k, hk⟩ then a j else 0) + δ
    have he : (∑ j : Fin n, if j ≤ ⟨k, hk⟩ then a j + d j else 0) =
        (∑ j : Fin n, if j ≤ ⟨k, hk⟩ then a j else 0) +
          ∑ j : Fin n, if j ≤ ⟨k, hk⟩ then d j else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [he]
    refine ⟨le_add_of_nonneg_right (zero_le _), add_le_add le_rfl ?_⟩
    apply le_trans _ hd
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> simp
  · simp [cumulativeQuantityTuple, tupleQuantityEval, Tuple.length, hk]

theorem maxCleared_bounds (η : FiniteSubsets (ℕ × ℕ))
    (s b s' b' : Tuple Quantity) (δ : Quantity)
    (hs : ∀ k, tupleQuantityEval k s ≤ tupleQuantityEval k s' ∧
      tupleQuantityEval k s' ≤ tupleQuantityEval k s + δ)
    (hb : ∀ k, tupleQuantityEval k b ≤ tupleQuantityEval k b' ∧
      tupleQuantityEval k b' ≤ tupleQuantityEval k b + δ) :
    maxClearedQuantityForIndexSet η s b ≤ maxClearedQuantityForIndexSet η s' b' ∧
    maxClearedQuantityForIndexSet η s' b' ≤ maxClearedQuantityForIndexSet η s b + δ := by
  constructor
  · apply Finset.sup_mono_fun
    intro ij _
    exact min_le_min (hs ij.1).1 (hb ij.2).1
  · apply Finset.sup_le
    intro ij hij
    calc
      clearedQuantityAt s' b' ij ≤ clearedQuantityAt s b ij + δ := by
        dsimp only [clearedQuantityAt]
        rw [← min_add_add_right]
        exact min_le_min (hs ij.1).2 (hb ij.2).2
      _ ≤ maxClearedQuantityForIndexSet η s b + δ :=
        add_le_add (Finset.le_sup (f := clearedQuantityAt s b) hij) le_rfl

def addAt (x : Tuple Quantity) (t : Fin x.1) (δ : Quantity) : Tuple Quantity :=
  ⟨x.1, fun i => x.2 i + if i = t then δ else 0⟩

theorem cumulative_monotone (x : Tuple Quantity) : Monotone (cumulativeQuantityTuple x).2 := by
  intro i j hij
  change (∑ k : Fin x.1, if k ≤ i then x.2 k else 0) ≤
    ∑ k : Fin x.1, if k ≤ j then x.2 k else 0
  apply Finset.sum_le_sum
  intro k _
  by_cases hki : k ≤ i
  · simp only [if_pos hki, if_pos (hki.trans hij)]
    exact le_rfl
  · simp only [if_neg hki]
    exact zero_le _

theorem cumulative_addAt (x : Tuple Quantity) (t k : Fin x.1) (δ : Quantity) :
    (cumulativeQuantityTuple (addAt x t δ)).2 k =
      (cumulativeQuantityTuple x).2 k + if t ≤ k then δ else 0 := by
  change (∑ j : Fin x.1, if j ≤ k then x.2 j + (if j = t then δ else 0) else 0) =
    (∑ j : Fin x.1, if j ≤ k then x.2 j else 0) + if t ≤ k then δ else 0
  have he (j : Fin x.1) :
      (if j ≤ k then x.2 j + (if j = t then δ else 0) else 0) =
        (if j ≤ k then x.2 j else 0) + (if j = t then (if t ≤ k then δ else 0) else 0) := by
    by_cases h : j = t
    · subst j
      split_ifs <;> simp_all
    · simp only [h, if_false, add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem permutationMap_addAt {n : ℕ} (a : Fin n → Quantity) (t : Fin n)
    (δ : Quantity) (π : FinitePermutation n) :
    permutationMap (addAt ⟨n, a⟩ t δ) ⟨n, π⟩ =
      addAt (permute ⟨n, a⟩ π) (π.symm t) δ := by
  simp only [addAt, permutationMap_same_length, permute, Tuple.length, Tuple.entry]
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext i
  change a (π i) + (if π i = t then δ else 0) =
    a (π i) + (if i = π.symm t then δ else 0)
  simp only [π.apply_eq_iff_eq_symm_apply]

theorem prepend_addAt (x : Tuple Quantity) (q δ : Quantity) :
    concat ⟨1, fun _ => q + δ⟩ x =
      addAt (concat ⟨1, fun _ => q⟩ x) (Fin.castAdd x.1 (0 : Fin 1)) δ := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext i
  change Fin (1 + x.1) at i
  refine Fin.addCases ?_ ?_ i
  · intro i
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [concat, addAt, Tuple.entry, Tuple.length]
  · intro i
    have hi : Fin.natAdd 1 i ≠ Fin.castAdd x.1 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    simp [concat, addAt, Tuple.entry, Tuple.length, hi]

end Thesis.Foundations.MarketClearing.QuantityPerturbation
