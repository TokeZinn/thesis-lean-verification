import Thesis.DayAhead.ForecastingImpact.ShapleyPermutations
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Order.Interval.Finset.Fin

/-! # Exact uniform-permutation weights

Forecasting chapter, lines 500–513. Counting the permutations with a specified
predecessor coalition proves that the uniform permutation average is exactly
the factorial-weighted Shapley value, also for real-module-valued games.
-/

noncomputable section
namespace Thesis.DayAhead.ShapleyPermutations

open Finset
open scoped BigOperators

variable {n : ℕ}

theorem notMem_predecessors (π : Equiv.Perm (Fin n)) (i : Fin n) :
    i ∉ predecessors π i := by simp [predecessors]

theorem card_predecessors (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (predecessors π i).card = (π i).val := by
  have himage : (predecessors π i).image π = Iio (π i) := by
    ext j
    simp only [mem_image, predecessors, mem_filter, mem_univ, true_and, mem_Iio]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hj
      exact ⟨π.symm j, by simpa using hj, π.apply_symm_apply j⟩
  rw [← card_image_of_injective _ π.injective, himage, Fin.card_Iio]

/-- The three fibers are the predecessors, the feature itself, and its successors. -/
def coalitionTag (i : Fin n) (S : Finset (Fin n)) (j : Fin n) : Fin 3 :=
  if j = i then 1 else if j ∈ S then 0 else 2

def positionTag (k j : Fin n) : Fin 3 :=
  if j < k then 0 else if j = k then 1 else 2

theorem coalitionTag_zero {i j : Fin n} {S : Finset (Fin n)} (hi : i ∉ S) :
    coalitionTag i S j = 0 ↔ j ∈ S := by
  by_cases hji : j = i <;> by_cases hj : j ∈ S <;> simp_all [coalitionTag]

theorem coalitionTag_one (i j : Fin n) (S : Finset (Fin n)) :
    coalitionTag i S j = 1 ↔ j = i := by
  by_cases hji : j = i <;> by_cases hj : j ∈ S <;> simp [coalitionTag, hji, hj]

theorem coalitionTag_two (i j : Fin n) (S : Finset (Fin n)) :
    coalitionTag i S j = 2 ↔ j ∉ insert i S := by
  by_cases hji : j = i <;> by_cases hj : j ∈ S <;> simp [coalitionTag, hji, hj]

theorem positionTag_zero (k j : Fin n) : positionTag k j = 0 ↔ j < k := by
  by_cases hj : j < k <;> by_cases he : j = k <;> simp [positionTag, hj, he]

theorem positionTag_one (k j : Fin n) : positionTag k j = 1 ↔ j = k := by
  by_cases he : j = k
  · subst j; simp [positionTag]
  · by_cases hj : j < k <;> simp [positionTag, hj, he]

theorem positionTag_two (k j : Fin n) : positionTag k j = 2 ↔ k < j := by
  by_cases hj : j < k <;> by_cases he : j = k <;> simp_all [positionTag] <;> omega

theorem card_coalitionTag {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S) (c : Fin 3) :
    Fintype.card {j // coalitionTag i S j = c} =
      if c = 0 then S.card else if c = 1 then 1 else n - S.card - 1 := by
  fin_cases c
  · change Fintype.card {j // coalitionTag i S j = 0} = S.card
    simp only [Fintype.card_subtype, coalitionTag_zero hi]
    simp
  · change Fintype.card {j // coalitionTag i S j = 1} = 1
    simp only [Fintype.card_subtype, coalitionTag_one]
    have hfilter : (univ.filter fun j : Fin n => j = i) = {i} := by ext; simp
    rw [hfilter, card_singleton]
  · change Fintype.card {j // coalitionTag i S j = 2} = n - S.card - 1
    simp only [Fintype.card_subtype, coalitionTag_two]
    have hfilter : (univ.filter fun j => j ∉ insert i S) = (insert i S)ᶜ := by
      ext; simp
    rw [hfilter, card_compl, card_insert_of_notMem hi, Fintype.card_fin]
    omega

theorem card_positionTag (k : Fin n) (c : Fin 3) :
    Fintype.card {j // positionTag k j = c} =
      if c = 0 then k.val else if c = 1 then 1 else n - k.val - 1 := by
  fin_cases c
  · change Fintype.card {j // positionTag k j = 0} = k.val
    simp only [Fintype.card_subtype, positionTag_zero]
    have hfilter : (univ.filter fun j => j < k) = Iio k := by ext; simp
    rw [hfilter, Fin.card_Iio]
  · change Fintype.card {j // positionTag k j = 1} = 1
    simp only [Fintype.card_subtype, positionTag_one]
    have hfilter : (univ.filter fun j : Fin n => j = k) = {k} := by ext; simp
    rw [hfilter, card_singleton]
  · change Fintype.card {j // positionTag k j = 2} = n - k.val - 1
    simp only [Fintype.card_subtype, positionTag_two]
    have hfilter : (univ.filter fun j => k < j) = Ioi k := by ext; simp
    rw [hfilter, Fin.card_Ioi]
    omega

theorem tag_composition_iff {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S)
    (k : Fin n) (π : Equiv.Perm (Fin n)) :
    positionTag k ∘ π = coalitionTag i S ↔ predecessors π i = S ∧ π i = k := by
  constructor
  · intro h
    have hik : π i = k := (positionTag_one k _).mp (by
      simpa [coalitionTag] using congrFun h i)
    refine ⟨?_, hik⟩
    ext j
    change (j ∈ univ.filter fun j => π j < π i) ↔ j ∈ S
    simp only [mem_filter, mem_univ, true_and, hik]
    rw [← positionTag_zero, ← coalitionTag_zero hi]
    exact (congrArg (· = 0) (congrFun h j)).to_iff
  · rintro ⟨hS, hik⟩
    funext j
    have hj : j ∈ S ↔ π j < k := by
      rw [← hS]
      simp [predecessors, hik]
    have he : j = i ↔ π j = k := by rw [← hik, π.injective.eq_iff]
    by_cases hji : j = i
    · subst j
      simp [positionTag, coalitionTag, hik]
    by_cases hjS : j ∈ S
    · simp [positionTag, coalitionTag, hji, hjS, hj.mp hjS]
    · simp [positionTag, coalitionTag, hji, hjS,
        mt hj.mpr hjS, mt he.mpr hji]

theorem exists_tag_permutation {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S)
    (k : Fin n) (hk : k.val = S.card) :
    ∃ π : Equiv.Perm (Fin n), positionTag k ∘ π = coalitionTag i S := by
  have hc (c : Fin 3) : Fintype.card {j // coalitionTag i S j = c} =
      Fintype.card {j // positionTag k j = c} := by
    rw [card_coalitionTag hi, card_positionTag, hk]
  let e (c : Fin 3) := Classical.choice (Fintype.card_eq.mp (hc c))
  exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩

/-- Exact multiplicity, including the empty and full predecessor coalitions. -/
theorem card_predecessor_fiber {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S) :
    Fintype.card {π : Equiv.Perm (Fin n) // predecessors π i = S} =
      S.card.factorial * (n - S.card - 1).factorial := by
  have hSn : S.card < n := by
    have := card_lt_card (ssubset_insert hi)
    have := (insert i S).card_le_univ
    simp only [Fintype.card_fin] at this
    omega
  let k : Fin n := ⟨S.card, hSn⟩
  have heq (π : Equiv.Perm (Fin n)) :
      predecessors π i = S ↔ positionTag k ∘ π = coalitionTag i S := by
    rw [tag_composition_iff hi]
    constructor
    · intro h
      refine ⟨h, Fin.ext ?_⟩
      change (π i).val = S.card
      rw [← card_predecessors, h]
    · exact And.left
  obtain ⟨σ, hσ⟩ := exists_tag_permutation hi k rfl
  have hcompose (τ : Equiv.Perm (Fin n)) :
      coalitionTag i S ∘ τ = coalitionTag i S ↔
        positionTag k ∘ (σ * τ) = coalitionTag i S := by
    have hc : positionTag k ∘ (σ * τ) = coalitionTag i S ∘ τ := by
      funext j
      exact congrFun hσ (τ j)
    rw [hc]
  calc
    _ = Fintype.card {π : Equiv.Perm (Fin n) // positionTag k ∘ π = coalitionTag i S} :=
      Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) heq)
    _ = Fintype.card {τ : Equiv.Perm (Fin n) // coalitionTag i S ∘ τ = coalitionTag i S} :=
      (Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft σ) hcompose)).symm
    _ = _ := by
      rw [DomMulAct.stabilizer_card]
      simp_rw [card_coalitionTag hi]
      simp [Fin.prod_univ_succ]

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

omit [Module ℝ H] in
theorem sum_contributions_by_coalition (V : Finset (Fin n) → H) (i : Fin n) :
    ∑ π : Equiv.Perm (Fin n), contribution V π i =
      ∑ S ∈ (univ.erase i).powerset,
        (S.card.factorial * (n - S.card - 1).factorial) • Shapley.marginal V S i := by
  have hmem (π : Equiv.Perm (Fin n)) (_ : π ∈ univ) :
      predecessors π i ∈ (univ.erase i).powerset := by
    rw [mem_powerset, subset_erase]
    exact ⟨subset_univ _, notMem_predecessors π i⟩
  simp only [contribution]
  rw [← sum_fiberwise_of_maps_to' hmem (fun S => Shapley.marginal V S i)]
  apply sum_congr rfl
  intro S hS
  have hi : i ∉ S := notMem_mono (mem_powerset.mp hS) (notMem_erase i univ)
  rw [sum_const, ← Fintype.card_subtype, card_predecessor_fiber hi]

/-- Enumerating all permutations gives the actual factorial-weighted formula. -/
theorem uniform_average_eq_value (V : Finset (Fin n) → H) (i : Fin n) :
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ •
      ∑ π : Equiv.Perm (Fin n), contribution V π i = Shapley.value V i := by
  rw [sum_contributions_by_coalition, smul_sum]
  simp only [Shapley.value, Fintype.card_perm, Fintype.card_fin]
  apply sum_congr rfl
  intro S _
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  simp only [Shapley.weight, Nat.cast_mul, div_eq_mul_inv]
  ring

end Thesis.DayAhead.ShapleyPermutations
