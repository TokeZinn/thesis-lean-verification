import Thesis.Foundations.Stochastic.PermutedTuples
import Thesis.Appendices.Analysis.BoundedMetric

/-!
# The current thesis's bounded matching metric

`defn:permuted-tuple-hausdorff-distance` defines the permuted-tuple matching
distance `d_π(x^π, y^π)` as the minimum over permutations `σ ∈ P_n` of
`max_i min(d(x(i), y(σ(i))), 1)` when both representatives have length `n`
(for `n = 0` this is the empty maximum `0`), and as `1` when the lengths
differ. This module takes that formula as the *definition* of
`matchingEDistance`: it is first defined on representatives
(`tupleMatchingEDistance`), shown to be independent of the representatives by
the manuscript's relabelling argument, and then descended to the quotient.
The metric axioms are proved by the manuscript's verifications (attained
finite minimum, the bijection `σ ↦ σ⁻¹`, the composition `σ' ∘ σ`), and the
metric instance `matchingMetricSpace` is built from them.

The older orbit-Hausdorff construction of `PermutedTuples` is used only at the
end: the matching distance is identified with the truncation at `1` of that
distance (`matchingEDistance_eq_min_edist`), so both induce the same
uniformity, and completeness and separability are inherited from the
Cauchy-lifting and dense-image proofs of `PermutedTuples`.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Stochastic.MatchingTuples

open MarketRepresentation MarketRepresentation.TuplesBasic
open MarketRepresentation.TuplesMetricTopology PermutedTuples

universe u

/-! ## The fixed-length matching cost -/

/-- The cost of matching two fixed-length representatives, including the empty
tuple. The infimum is a minimum because the permutation type is finite. -/
def fixedMatchingCost {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) : ℝ≥0∞ :=
  ⨅ σ : Equiv.Perm (Fin n), min (coordinateEDistSup x (y ∘ σ)) 1

theorem fixedMatchingCost_le_one {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) : fixedMatchingCost x y ≤ 1 :=
  (iInf_le _ (Equiv.refl _)).trans (min_le_right _ _)

theorem fixedMatchingCost_lt_iff {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) {ε : ℝ≥0∞} (hε : ε ≤ 1) :
    fixedMatchingCost x y < ε ↔
      ∃ σ : Equiv.Perm (Fin n), coordinateEDistSup x (y ∘ σ) < ε := by
  simp only [fixedMatchingCost, iInf_lt_iff, min_lt_iff]
  simp only [not_lt_of_ge hε, or_false]

/-- The orbit-Hausdorff distance of `PermutedTuples` below radius one is the
existence of a matching with small coordinate cost. Used only to identify the
matching distance with the truncated orbit distance. -/
theorem quotient_edist_lt_iff_matching {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) {ε : ℝ≥0∞} (hε : ε ≤ 1) :
    edist (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X))
      (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X)) < ε ↔
      ∃ σ : Equiv.Perm (Fin n), coordinateEDistSup x (y ∘ σ) < ε := by
  constructor
  · intro h
    have hx := self_mem_permutativeClass (Sigma.mk n x : Tuple X)
    rcases Metric.exists_edist_lt_of_hausdorffEDist_lt hx h with ⟨z, hz, hxz⟩
    rcases hz with ⟨σ, rfl⟩
    refine ⟨σ, ?_⟩
    change edist (Sigma.mk n x : Tuple X) (Sigma.mk n (y ∘ σ) : Tuple X) < ε at hxz
    have heq := fixedLength_edist_eq_coordinateEDistSup_of_lt_one
      (lt_of_lt_of_le hxz hε)
    rw [heq] at hxz
    exact hxz
  · rintro ⟨σ, hσ⟩
    have hclass :
        Quot.mk (permutativeSetoid X) (Sigma.mk n (y ∘ σ) : Tuple X) =
          Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X) :=
      (Quot.sound (show PermutativeEquality (Sigma.mk n y : Tuple X)
        (Sigma.mk n (y ∘ σ) : Tuple X) from ⟨σ, rfl⟩)).symm
    rw [← hclass]
    exact lt_of_le_of_lt
      (permutedTupleHausdorffEDistance_mk_mk_le_coordinateEDistSup x (y ∘ σ)) hσ

/-- Truncation commutes with the finite coordinate maximum, including length zero. -/
theorem truncated_coordinateEDistSup {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) :
    min (coordinateEDistSup x y) 1 =
      Finset.univ.sup (fun i => min (edist (x i) (y i)) 1) := by
  classical
  unfold coordinateEDistSup
  exact Finset.sup_inf_distrib_right _ _ _

/-! ## The manuscript's verifications for one candidate matching -/

/-- Original label: `defn:permuted-tuple-hausdorff-distance`.
The cost `max_i min(d(x(i), y(σ(i))), 1)` of one candidate matching `σ`. -/
def matchingCost {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) (σ : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  Finset.univ.sup (fun i => min (edist (x i) (y (σ i))) 1)

/-- Reindexing `j = σ(i)` does not change a finite maximum. -/
theorem sup_comp_perm {n : ℕ} (f : Fin n → ℝ≥0∞) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.sup (fun i => f (σ i)) = Finset.univ.sup f := by
  apply le_antisymm
  · exact Finset.sup_le fun i _ => Finset.le_sup (f := f) (Finset.mem_univ (σ i))
  · apply Finset.sup_le
    intro i _
    simpa using (Finset.le_sup (f := fun j => f (σ j)) (Finset.mem_univ (σ.symm i)))

/-- The triangle inequality for the truncated ground distance `d̄ = min(d, 1)`. -/
theorem truncated_edist_triangle {X : Type u} [EMetricSpace X] (x y z : X) :
    min (edist x z) 1 ≤ min (edist x y) 1 + min (edist y z) 1 := by
  by_cases hxy : edist x y ≤ 1
  · by_cases hyz : edist y z ≤ 1
    · rw [min_eq_left hxy, min_eq_left hyz]
      exact (min_le_left _ _).trans (edist_triangle x y z)
    · rw [min_eq_right (le_of_not_ge hyz)]
      exact (min_le_right _ _).trans (le_add_left le_rfl)
  · rw [min_eq_right (le_of_not_ge hxy)]
    exact (min_le_right _ _).trans (le_add_right le_rfl)

/-- Symmetry step: the cost of `σ` for `(x, y)` is the cost of `σ⁻¹` for `(y, x)`. -/
theorem matchingCost_symm {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) (σ : Equiv.Perm (Fin n)) :
    matchingCost x y σ = matchingCost y x σ.symm := by
  unfold matchingCost
  rw [← sup_comp_perm (fun j => min (edist (y j) (x (σ.symm j))) 1) σ]
  simp only [Equiv.symm_apply_apply, edist_comm]

/-- Triangle step: the composed matching `σ' ∘ σ` costs at most the sum. -/
theorem matchingCost_trans_le {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y z : Fin n → X) (σ τ : Equiv.Perm (Fin n)) :
    matchingCost x z (σ.trans τ) ≤ matchingCost x y σ + matchingCost y z τ := by
  apply Finset.sup_le
  intro i _
  have h₁ := Finset.le_sup (f := fun j => min (edist (x j) (y (σ j))) 1)
    (Finset.mem_univ i)
  have h₂ := Finset.le_sup (f := fun j => min (edist (y j) (z (τ j))) 1)
    (Finset.mem_univ (σ i))
  exact (truncated_edist_triangle (x i) (y (σ i)) (z (τ (σ i)))).trans (add_le_add h₁ h₂)

/-- The manuscript's representative-change calculation before taking minima:
relabelling `x' = x ∘ α`, `y' = y ∘ β` turns the candidate `σ` into
`β ∘ σ ∘ α⁻¹`. -/
theorem matchingCost_comp_perm {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) (α β σ : Equiv.Perm (Fin n)) :
    matchingCost (x ∘ α) (y ∘ β) σ = matchingCost x y ((α.symm.trans σ).trans β) := by
  unfold matchingCost
  rw [← sup_comp_perm (fun j =>
    min (edist (x j) (y (((α.symm.trans σ).trans β) j))) 1) α]
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem fixedMatchingCost_eq_iInf_matchingCost {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) : fixedMatchingCost x y = ⨅ σ, matchingCost x y σ := by
  simp only [fixedMatchingCost, matchingCost, truncated_coordinateEDistSup,
    Function.comp_apply]

/-- The minimum over the finite set `P_n` is attained. -/
theorem exists_matchingCost_eq_fixedMatchingCost {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) : ∃ σ, matchingCost x y σ = fixedMatchingCost x y := by
  rw [fixedMatchingCost_eq_iInf_matchingCost]
  exact exists_eq_ciInf_of_finite

theorem fixedMatchingCost_le_matchingCost {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) (σ : Equiv.Perm (Fin n)) : fixedMatchingCost x y ≤ matchingCost x y σ := by
  rw [fixedMatchingCost_eq_iInf_matchingCost]
  exact iInf_le _ σ

/-- Taking `σ = id` for two equal representatives gives cost zero. -/
theorem fixedMatchingCost_self {X : Type u} [EMetricSpace X] {n : ℕ}
    (x : Fin n → X) : fixedMatchingCost x x = 0 := by
  have hz : matchingCost x x (Equiv.refl (Fin n)) = 0 := by
    unfold matchingCost
    refine le_antisymm ?_ bot_le
    exact Finset.sup_le fun i _ => by simp
  exact le_antisymm ((fixedMatchingCost_le_matchingCost x x (Equiv.refl _)).trans_eq hz) bot_le

/-- A zero attained minimum forces `x(i) = y(σ(i))` for every `i`, i.e.
`x = y ∘ σ`, for the minimising matching `σ`; conversely `x = y ∘ σ` gives
cost zero at `σ`. This includes the empty layer without a nonempty-index
assumption. -/
theorem fixedMatchingCost_eq_zero_iff {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) : fixedMatchingCost x y = 0 ↔
      ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  constructor
  · intro hzero
    obtain ⟨σ, hσ⟩ := exists_matchingCost_eq_fixedMatchingCost x y
    refine ⟨σ, funext fun i => ?_⟩
    have hle : min (edist (x i) (y (σ i))) 1 ≤ 0 := by
      have := Finset.le_sup (f := fun j => min (edist (x j) (y (σ j))) 1)
        (Finset.mem_univ i)
      exact this.trans_eq (hσ.trans hzero)
    have hz : min (edist (x i) (y (σ i))) 1 = 0 := le_antisymm hle bot_le
    exact edist_eq_zero.mp (by simpa using hz)
  · rintro ⟨σ, rfl⟩
    have hz : matchingCost (y ∘ σ) y σ = 0 := by
      unfold matchingCost
      refine le_antisymm ?_ bot_le
      exact Finset.sup_le fun i _ => by simp
    exact le_antisymm ((fixedMatchingCost_le_matchingCost (y ∘ σ) y σ).trans_eq hz) bot_le

/-- Symmetry via the bijection `σ ↦ σ⁻¹` of `P_n`. -/
theorem fixedMatchingCost_comm {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) : fixedMatchingCost x y = fixedMatchingCost y x := by
  have aux (x y : Fin n → X) : fixedMatchingCost x y ≤ fixedMatchingCost y x := by
    obtain ⟨σ, hσ⟩ := exists_matchingCost_eq_fixedMatchingCost y x
    calc
      fixedMatchingCost x y ≤ matchingCost x y σ.symm := fixedMatchingCost_le_matchingCost _ _ _
      _ = matchingCost y x σ := (matchingCost_symm y x σ).symm
      _ = fixedMatchingCost y x := hσ
  exact le_antisymm (aux x y) (aux y x)

/-- The triangle inequality via the composed matching `σ' ∘ σ` of two
minimisers. -/
theorem fixedMatchingCost_triangle {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y z : Fin n → X) :
    fixedMatchingCost x z ≤ fixedMatchingCost x y + fixedMatchingCost y z := by
  obtain ⟨σ, hσ⟩ := exists_matchingCost_eq_fixedMatchingCost x y
  obtain ⟨τ, hτ⟩ := exists_matchingCost_eq_fixedMatchingCost y z
  calc
    fixedMatchingCost x z ≤ matchingCost x z (σ.trans τ) := fixedMatchingCost_le_matchingCost _ _ _
    _ ≤ matchingCost x y σ + matchingCost y z τ := matchingCost_trans_le x y z σ τ
    _ = fixedMatchingCost x y + fixedMatchingCost y z := by rw [hσ, hτ]

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
Well-definedness on fixed-length representatives: relabelling either
representative merely relabels the candidate matchings through the bijection
`σ ↦ β ∘ σ ∘ α⁻¹` of `P_n`, so the minimum is unchanged. -/
theorem fixedMatchingCost_representatives {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) (α β : Equiv.Perm (Fin n)) :
    fixedMatchingCost (x ∘ α) (y ∘ β) = fixedMatchingCost x y := by
  have aux (x y : Fin n → X) (α β : Equiv.Perm (Fin n)) :
      fixedMatchingCost (x ∘ α) (y ∘ β) ≤ fixedMatchingCost x y := by
    obtain ⟨σ, hσ⟩ := exists_matchingCost_eq_fixedMatchingCost x y
    let τ := (α.trans σ).trans β.symm
    have hτ : (α.symm.trans τ).trans β = σ := by
      ext i
      simp [τ]
    calc
      fixedMatchingCost (x ∘ α) (y ∘ β) ≤ matchingCost (x ∘ α) (y ∘ β) τ :=
        fixedMatchingCost_le_matchingCost _ _ _
      _ = matchingCost x y σ := by rw [matchingCost_comp_perm, hτ]
      _ = fixedMatchingCost x y := hσ
  refine le_antisymm (aux x y α β) ?_
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using
    aux (x ∘ α) (y ∘ β) α.symm β.symm

/-! ## The matching distance on representatives and on the quotient -/

/-- Original label: `defn:permuted-tuple-hausdorff-distance`.
The matching distance on representatives: `1` for different lengths and the
minimal matching cost for equal lengths (for length `0` the empty maximum,
i.e. `0`). -/
def tupleMatchingEDistance {X : Type u} [EMetricSpace X] (x y : Tuple X) : ℝ≥0∞ :=
  if h : x.1 = y.1 then fixedMatchingCost x.2 (y.2 ∘ Fin.cast h) else 1

theorem tupleMatchingEDistance_mk_mk {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) :
    tupleMatchingEDistance (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) =
      fixedMatchingCost x y := by
  unfold tupleMatchingEDistance
  exact dif_pos rfl

theorem tupleMatchingEDistance_of_length_ne {X : Type u} [EMetricSpace X]
    {x y : Tuple X} (h : x.1 ≠ y.1) : tupleMatchingEDistance x y = 1 :=
  dif_neg h

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
Well-definedness on the quotient, as in the manuscript: if the lengths differ,
so do the lengths of any other representatives and both values are `1`; for
equal lengths `n`, representatives `x ∘ α` and `y ∘ β` give the same minimum
by `fixedMatchingCost_representatives`. -/
theorem tupleMatchingEDistance_permute {X : Type u} [EMetricSpace X]
    (x y : Tuple X) (α : FinitePermutation x.length) (β : FinitePermutation y.length) :
    tupleMatchingEDistance (permute x α) (permute y β) = tupleMatchingEDistance x y := by
  rcases x with ⟨n, x⟩
  rcases y with ⟨m, y⟩
  by_cases h : n = m
  · subst h
    change tupleMatchingEDistance (Sigma.mk n (x ∘ α) : Tuple X) (Sigma.mk n (y ∘ β) : Tuple X) =
      tupleMatchingEDistance (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X)
    rw [tupleMatchingEDistance_mk_mk, tupleMatchingEDistance_mk_mk]
    exact fixedMatchingCost_representatives x y α β
  · exact (tupleMatchingEDistance_of_length_ne
      (x := permute (Sigma.mk n x : Tuple X) α) (y := permute (Sigma.mk m y : Tuple X) β) h).trans
      (tupleMatchingEDistance_of_length_ne
        (x := (Sigma.mk n x : Tuple X)) (y := (Sigma.mk m y : Tuple X)) h).symm

theorem tupleMatchingEDistance_permute_left {X : Type u} [EMetricSpace X]
    (x y : Tuple X) (α : FinitePermutation x.length) :
    tupleMatchingEDistance (permute x α) y = tupleMatchingEDistance x y := by
  have h := tupleMatchingEDistance_permute x y α (Equiv.refl _)
  rwa [permute_refl] at h

theorem tupleMatchingEDistance_permute_right {X : Type u} [EMetricSpace X]
    (x y : Tuple X) (β : FinitePermutation y.length) :
    tupleMatchingEDistance x (permute y β) = tupleMatchingEDistance x y := by
  have h := tupleMatchingEDistance_permute x y (Equiv.refl _) β
  rwa [permute_refl] at h

/-- Original label: `defn:permuted-tuple-hausdorff-distance`.
The permuted-tuple matching distance `d_π` on the quotient: the minimum over
permutations of the truncated maximal coordinate distance for representatives
of equal length, and `1` for different lengths. It is well defined on the
quotient by `tupleMatchingEDistance_permute`. -/
def matchingEDistance {X : Type u} [EMetricSpace X]
    (q r : PermutedTupleQuotientSpace X) : ℝ≥0∞ :=
  Quot.lift₂ tupleMatchingEDistance
    (fun x _ _ hy => by
      obtain ⟨β, rfl⟩ := hy
      exact (tupleMatchingEDistance_permute_right x _ β).symm)
    (fun _ _ y hx => by
      obtain ⟨α, rfl⟩ := hx
      exact (tupleMatchingEDistance_permute_left _ y α).symm)
    q r

theorem matchingEDistance_mk {X : Type u} [EMetricSpace X] (x y : Tuple X) :
    matchingEDistance (Quot.mk (permutativeSetoid X) x) (Quot.mk (permutativeSetoid X) y) =
      tupleMatchingEDistance x y :=
  rfl

/-- Original label: `defn:permuted-tuple-hausdorff-distance`.
On two representatives of the same length the matching distance is the
minimum over all permutations of the truncated maximum coordinate cost. -/
theorem matchingEDistance_mk_mk {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) :
    matchingEDistance
      (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X))
      (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X)) =
        fixedMatchingCost x y :=
  tupleMatchingEDistance_mk_mk x y

/-- Original label: `defn:permuted-tuple-hausdorff-distance`.
Distinct length layers have matching distance exactly one. -/
theorem matchingEDistance_of_length_ne {X : Type u} [EMetricSpace X]
    {q r : PermutedTupleQuotientSpace X} (h : quotientLength q ≠ quotientLength r) :
    matchingEDistance q r = 1 := by
  revert h
  refine Quot.induction_on₂ q r ?_
  intro x y h
  exact tupleMatchingEDistance_of_length_ne (x := x) (y := y) h

theorem matchingEDistance_le_one {X : Type u} [EMetricSpace X]
    (q r : PermutedTupleQuotientSpace X) : matchingEDistance q r ≤ 1 := by
  refine Quot.induction_on₂ q r ?_
  intro x y
  change tupleMatchingEDistance x y ≤ 1
  unfold tupleMatchingEDistance
  split_ifs
  · exact fixedMatchingCost_le_one _ _
  · exact le_rfl

/-- Original label: `defn:permuted-tuple-hausdorff-distance`.
The minimum is attained, so the infimum formulation gives the literal finite
minimum of maximum truncated coordinate distances in the manuscript. -/
theorem matchingEDistance_attained {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) :
    ∃ σ : Equiv.Perm (Fin n),
      matchingEDistance
        (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X))
        (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X)) =
          Finset.univ.sup (fun i => min (edist (x i) (y (σ i))) 1) := by
  obtain ⟨σ, hσ⟩ := exists_matchingCost_eq_fixedMatchingCost x y
  exact ⟨σ, (matchingEDistance_mk_mk x y).trans hσ.symm⟩

/-! ## The metric axioms, by the manuscript's route -/

theorem matchingEDistance_self {X : Type u} [EMetricSpace X]
    (q : PermutedTupleQuotientSpace X) : matchingEDistance q q = 0 := by
  refine Quot.inductionOn q ?_
  rintro ⟨n, x⟩
  rw [matchingEDistance_mk_mk, fixedMatchingCost_self]

/-- Original label: `defn:permuted-tuple-hausdorff-distance`.
The distance between the empty classes is zero. -/
theorem matchingEDistance_empty {X : Type u} [EMetricSpace X] :
    matchingEDistance (Quot.mk (permutativeSetoid X) (Tuple.empty X))
      (Quot.mk (permutativeSetoid X) (Tuple.empty X)) = 0 :=
  matchingEDistance_self _

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
Identity of indiscernibles: distance `0` forces equal lengths, and then the
attained minimising matching `σ` gives `x = y ∘ σ`, so the classes coincide. -/
theorem matchingEDistance_eq_zero {X : Type u} [EMetricSpace X]
    (q r : PermutedTupleQuotientSpace X) (hz : matchingEDistance q r = 0) : q = r := by
  revert hz
  refine Quot.induction_on₂ q r ?_
  rintro ⟨n, x⟩ ⟨m, y⟩ hz
  by_cases hnm : n = m
  · subst m
    rw [matchingEDistance_mk_mk] at hz
    obtain ⟨σ, hσ⟩ := (fixedMatchingCost_eq_zero_iff x y).mp hz
    apply Eq.symm
    apply Quot.sound
    exact ⟨σ, by cases hσ; rfl⟩
  · have hlen : quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk n x)) ≠
        quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk m y)) := hnm
    rw [matchingEDistance_of_length_ne hlen] at hz
    exact False.elim (one_ne_zero hz)

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
Symmetry: immediate for different lengths, and by `σ ↦ σ⁻¹` otherwise. -/
theorem matchingEDistance_comm {X : Type u} [EMetricSpace X]
    (q r : PermutedTupleQuotientSpace X) : matchingEDistance q r = matchingEDistance r q := by
  refine Quot.induction_on₂ q r ?_
  rintro ⟨n, x⟩ ⟨m, y⟩
  by_cases hnm : n = m
  · subst m
    rw [matchingEDistance_mk_mk, matchingEDistance_mk_mk, fixedMatchingCost_comm]
  · have hlen : quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk n x)) ≠
        quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk m y)) := hnm
    rw [matchingEDistance_of_length_ne hlen, matchingEDistance_of_length_ne hlen.symm]

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
Triangle inequality: by the composed matching `σ' ∘ σ` for three equal
lengths; otherwise the right-hand side contains a term equal to `1`, which
bounds every matching distance. -/
theorem matchingEDistance_triangle {X : Type u} [EMetricSpace X]
    (q r s : PermutedTupleQuotientSpace X) :
    matchingEDistance q s ≤ matchingEDistance q r + matchingEDistance r s := by
  refine Quot.inductionOn q ?_
  rintro ⟨n, x⟩
  refine Quot.inductionOn r ?_
  rintro ⟨m, y⟩
  refine Quot.inductionOn s ?_
  rintro ⟨k, z⟩
  by_cases hnm : n = m
  · subst m
    by_cases hnk : n = k
    · subst k
      rw [matchingEDistance_mk_mk, matchingEDistance_mk_mk, matchingEDistance_mk_mk]
      exact fixedMatchingCost_triangle x y z
    · have hlen : quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk n y)) ≠
          quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk k z)) := hnk
      rw [matchingEDistance_of_length_ne hlen]
      exact (matchingEDistance_le_one _ _).trans (le_add_left le_rfl)
  · have hlen : quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk n x)) ≠
        quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk m y)) := hnm
    rw [matchingEDistance_of_length_ne hlen]
    exact (matchingEDistance_le_one _ _).trans (le_add_right le_rfl)

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
`(T^π(X), d_π)` is an (extended) metric space, with every axiom proved by the
manuscript's verification above. The uniformity carried by this structure is
the one generated by `d_π` itself; `matchingMetricSpace` below replaces it by
the orbit uniformity of `PermutedTuples`, which is the same filter
(`matching_uniformity`), in order to inherit completeness and separability. -/
@[implicit_reducible]
def matchingEMetricSpace (X : Type u) [EMetricSpace X] :
    EMetricSpace (PermutedTupleQuotientSpace X) where
  edist := matchingEDistance
  edist_self := matchingEDistance_self
  edist_comm := matchingEDistance_comm
  edist_triangle := matchingEDistance_triangle
  eq_of_edist_eq_zero := matchingEDistance_eq_zero _ _

/-! ## Identification with the truncated orbit-Hausdorff distance -/

/-- The fixed-length matching cost equals the truncation at `1` of the
orbit-Hausdorff distance of `PermutedTuples` between the two classes. -/
theorem fixedMatchingCost_eq_min_edist {X : Type u} [EMetricSpace X] {n : ℕ}
    (x y : Fin n → X) :
    fixedMatchingCost x y =
      min (edist (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X))
        (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X))) 1 := by
  apply le_antisymm
  · by_contra h
    have hlt := lt_of_not_ge h
    have hsmall := fixedMatchingCost_le_one x y
    have hd := (min_lt_iff.mp hlt).resolve_right (not_lt_of_ge hsmall)
    have hc := (quotient_edist_lt_iff_matching x y hsmall).mp hd
    exact lt_irrefl _ ((fixedMatchingCost_lt_iff x y hsmall).mpr hc)
  · by_contra h
    have hlt := lt_of_not_ge h
    have hsmall : min (edist (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X))
        (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X))) 1 ≤ 1 := min_le_right _ _
    have hc := (fixedMatchingCost_lt_iff x y hsmall).mp hlt
    have hd := (quotient_edist_lt_iff_matching x y hsmall).mpr hc
    exact lt_irrefl _ (lt_of_le_of_lt (min_le_left _ _) hd)

/-- The matching distance is the truncation at `1` of the orbit-Hausdorff
distance of `PermutedTuples`; in particular both induce the same uniformity. -/
theorem matchingEDistance_eq_min_edist {X : Type u} [EMetricSpace X]
    (q r : PermutedTupleQuotientSpace X) :
    matchingEDistance q r = min (edist q r) 1 := by
  refine Quot.induction_on₂ q r ?_
  rintro ⟨n, x⟩ ⟨m, y⟩
  by_cases hnm : n = m
  · subst m
    rw [matchingEDistance_mk_mk]
    exact fixedMatchingCost_eq_min_edist x y
  · have hlen : quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk n x)) ≠
        quotientLength (Quot.mk (permutativeSetoid X) (Sigma.mk m y)) := hnm
    rw [matchingEDistance_of_length_ne hlen]
    refine (min_eq_right ?_).symm
    exact le_of_not_gt (fun hlt => hlen (quotientLength_eq_of_edist_lt_one hlt))

theorem matchingEDistance_lt_iff {X : Type u} [EMetricSpace X]
    {q r : PermutedTupleQuotientSpace X} {ε : ℝ≥0∞} (hε : ε ≤ 1) :
    matchingEDistance q r < ε ↔ edist q r < ε := by
  rw [matchingEDistance_eq_min_edist, min_lt_iff]
  exact or_iff_left (not_lt_of_ge hε)

private theorem matching_uniformity (X : Type u) [EMetricSpace X] :
    (inferInstance : UniformSpace (PermutedTupleQuotientSpace X)).uniformity =
      (matchingEMetricSpace X).toUniformSpace.uniformity := by
  apply (uniformity_basis_edist' (α := PermutedTupleQuotientSpace X) 1 zero_lt_one).ext
    (@uniformity_basis_edist' _ (matchingEMetricSpace X).toPseudoEMetricSpace 1 zero_lt_one)
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro p hp
    change matchingEDistance p.1 p.2 < ε at hp
    rw [matchingEDistance_eq_min_edist] at hp
    exact (min_lt_iff.mp hp).resolve_right (not_lt_of_ge hε.2.le)
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro p hp
    change edist p.1 p.2 < ε at hp
    change matchingEDistance p.1 p.2 < ε
    rw [matchingEDistance_eq_min_edist]
    exact lt_of_le_of_lt (min_le_left _ _) hp

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
The metric space `(T^π(X), d_π)` of the manuscript: its distance is
`matchingEDistance`, the minimum-over-permutations formula of
`defn:permuted-tuple-hausdorff-distance`, and its axioms are those of
`matchingEMetricSpace`, proved by the manuscript's verifications. The
uniformity is taken to be the orbit uniformity of `PermutedTuples`, which
`matching_uniformity` shows to coincide with the one generated by `d_π`
(because `d_π` is the truncation at `1` of the orbit distance), so that the
completeness and separability clauses below are inherited. -/
@[implicit_reducible]
def matchingMetricSpace (X : Type u) [EMetricSpace X] :
    MetricSpace (PermutedTupleQuotientSpace X) := by
  letI : EMetricSpace (PermutedTupleQuotientSpace X) :=
    (matchingEMetricSpace X).replaceUniformity (matching_uniformity X)
  apply EMetricSpace.toMetricSpace
  intro q r
  change matchingEDistance q r ≠ ⊤
  exact ne_top_of_le_ne_top (by simp) (matchingEDistance_le_one q r)

theorem matchingMetricSpace_edist (X : Type u) [EMetricSpace X]
    (q r : PermutedTupleQuotientSpace X) :
    @edist _ (matchingMetricSpace X).toEDist q r = matchingEDistance q r := rfl

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
Completeness of `(T^π(X), d_π)` for complete `X`. The uniformity of
`matchingMetricSpace` is the orbit uniformity, so this is the Cauchy-lifting
argument of `PermutedTuples.cauchySeq_tendsto_of_complete`: a Cauchy sequence
of classes eventually has constant length, close tuple representatives are
chosen recursively, their limit in the complete tuple space represents the
limit class. -/
theorem matching_completeSpace (X : Type u) [EMetricSpace X] [CompleteSpace X] :
    @CompleteSpace (PermutedTupleQuotientSpace X) (matchingMetricSpace X).toUniformSpace :=
  PermutedTuples.completeSpace

/-- Original label: `thm:permuted-tuple-hausdorff-metric-complete-separable`.
Separability of `(T^π(X), d_π)` for separable `X`: the classes of a countable
dense set of tuples are dense, as in `PermutedTuples.separableSpace`, whose
topology is that of `matchingMetricSpace`. -/
theorem matching_separableSpace (X : Type u) [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] :
    @TopologicalSpace.SeparableSpace (PermutedTupleQuotientSpace X)
      (matchingMetricSpace X).toUniformSpace.toTopologicalSpace :=
  PermutedTuples.separableSpace

end Thesis.Foundations.Stochastic.MatchingTuples
