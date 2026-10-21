import Thesis.Foundations.MarketClearing.ThresholdMarginals
import Mathlib.Topology.Semicontinuity.Basic

/-! # Current executable-volume characterizations

The finite price-cut formula is identified with the original cumulative-volume
operator. Its maximum over every real price is attained, including empty books.
-/

noncomputable section
namespace Thesis.Foundations.MarketClearing.DoctoralResults

open MarketRepresentation TuplesBasic Sorting Equilibrium MidpointPrice
open ThresholdClearing ThresholdMarginals

theorem below_mono {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity) :
    Monotone (below p q) := by
  intro r t h
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : p i ≤ r
  · simp only [if_pos hi, if_pos (hi.trans h)]
    exact le_rfl
  · simp only [if_neg hi]
    exact zero_le _

theorem above_anti {n : ℕ} (p : Fin n → ℝ) (q : Fin n → Quantity) :
    Antitone (above p q) := by
  intro r t h
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : t ≤ p i
  · simp only [if_pos hi, if_pos (h.trans hi)]
    exact le_rfl
  · simp only [if_neg hi]
    exact zero_le _

/-- The finite maximum is achieved by a common price, even if either book is empty. -/
theorem thresholdVolume_attained {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity) :
    ∃ r : ℝ, thresholdVolume ps qs pb qb = min (below ps qs r) (above pb qb r) := by
  by_cases hz : thresholdVolume ps qs pb qb = 0
  · refine ⟨0, le_antisymm (by rw [hz]; exact zero_le _) ?_⟩
    exact arbitrary_threshold_le ps qs pb qb 0 0 le_rfl
  · have hne : (Finset.univ : Finset (Fin n × Fin m)).Nonempty := by
      by_contra h
      have he : (Finset.univ : Finset (Fin n × Fin m)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      exact hz (by simp [thresholdVolume, he])
    obtain ⟨ij, _, hij⟩ := Finset.exists_mem_eq_sup Finset.univ hne
      (fun ij : Fin n × Fin m ↦ if ps ij.1 ≤ pb ij.2 then
        min (below ps qs (ps ij.1)) (above pb qb (pb ij.2)) else 0)
    have hp : ps ij.1 ≤ pb ij.2 := by
      by_contra hp
      exact hz (hij.trans (if_neg hp))
    refine ⟨ps ij.1, le_antisymm ?_ (arbitrary_threshold_le ps qs pb qb _ _ le_rfl)⟩
    change thresholdVolume ps qs pb qb = _ at hij
    rw [hij, if_pos hp]
    exact min_le_min le_rfl (above_anti pb qb hp)

/-- Original label: `prop:executable-volume-uniform-price`.
The manuscript's maximum is an attained greatest element, rather than merely
a supremum. `Quantity` is the nonnegative real type. -/
theorem executableVolume_uniformPrice {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (hs : Monotone ps) (hb : Antitone pb) :
    IsGreatest (Set.range (fun r : ℝ ↦ min (below ps qs r) (above pb qb r)))
      (equilibriumQuantity ((cumulativeQuantityTuple ⟨n, qs⟩, ⟨n, ps⟩),
        (cumulativeQuantityTuple ⟨m, qb⟩, ⟨m, pb⟩))) := by
  rw [equilibrium_eq_thresholdVolume ps qs pb qb hs hb]
  obtain ⟨r, hr⟩ := thresholdVolume_attained ps qs pb qb
  refine ⟨⟨r, hr.symm⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact arbitrary_threshold_le ps qs pb qb t t le_rfl

/-- Original label: `lem:state-functionals-permutation-invariant`.
The volume part, for the actual sorted cumulative quantity formula. The two
sort permutations may reorder all entries, including ties and zero quantities. -/
theorem sorted_volume_permutation {n m : ℕ}
    (ps : Fin n → ℝ) (qs : Fin n → Quantity) (pb : Fin m → ℝ) (qb : Fin m → Quantity)
    (π : FinitePermutation n) (ρ : FinitePermutation m)
    (hs : Monotone ps) (hb : Antitone pb)
    (hs' : Monotone (fun i ↦ ps (π i))) (hb' : Antitone (fun j ↦ pb (ρ j))) :
    equilibriumQuantity ((cumulativeQuantityTuple ⟨n, fun i ↦ qs (π i)⟩, ⟨n, fun i ↦ ps (π i)⟩),
      (cumulativeQuantityTuple ⟨m, fun j ↦ qb (ρ j)⟩, ⟨m, fun j ↦ pb (ρ j)⟩)) =
    equilibriumQuantity ((cumulativeQuantityTuple ⟨n, qs⟩, ⟨n, ps⟩),
      (cumulativeQuantityTuple ⟨m, qb⟩, ⟨m, pb⟩)) := by
  rw [equilibrium_eq_thresholdVolume _ _ _ _ hs' hb',
    equilibrium_eq_thresholdVolume _ _ _ _ hs hb]
  exact thresholdVolume_permutation ps qs pb qb π ρ

/-- Equal cumulative price cuts determine the same sell marginal price. -/
theorem sell_marginal_permutation {n : ℕ}
    (p : Fin n → ℝ) (q : Fin n → Quantity) (π : FinitePermutation n)
    (hp : Monotone p) (hp' : Monotone (fun i ↦ p (π i))) (v : Quantity)
    {i j : ℕ}
    (hi : ReachesFirst ((cumulativeQuantityTuple ⟨n, q⟩, ⟨n, p⟩), v) i)
    (hj : ReachesFirst ((cumulativeQuantityTuple ⟨n, fun k ↦ q (π k)⟩,
      ⟨n, fun k ↦ p (π k)⟩), v) j) :
    marginalPrice ((cumulativeQuantityTuple ⟨n, fun k ↦ q (π k)⟩,
      ⟨n, fun k ↦ p (π k)⟩), v) =
      marginalPrice ((cumulativeQuantityTuple ⟨n, q⟩, ⟨n, p⟩), v) := by
  apply le_antisymm
  · rw [marginal_le_iff_below _ _ hp' v hj, below_permutation]
    exact (marginal_le_iff_below _ _ hp v hi _).mp le_rfl
  · rw [marginal_le_iff_below _ _ hp v hi, ← below_permutation p q π]
    exact (marginal_le_iff_below _ _ hp' v hj _).mp le_rfl

/-- The corresponding buy marginal is invariant as well. -/
theorem buy_marginal_permutation {n : ℕ}
    (p : Fin n → ℝ) (q : Fin n → Quantity) (π : FinitePermutation n)
    (hp : Antitone p) (hp' : Antitone (fun i ↦ p (π i))) (v : Quantity)
    {i j : ℕ}
    (hi : ReachesFirst ((cumulativeQuantityTuple ⟨n, q⟩, ⟨n, p⟩), v) i)
    (hj : ReachesFirst ((cumulativeQuantityTuple ⟨n, fun k ↦ q (π k)⟩,
      ⟨n, fun k ↦ p (π k)⟩), v) j) :
    marginalPrice ((cumulativeQuantityTuple ⟨n, fun k ↦ q (π k)⟩,
      ⟨n, fun k ↦ p (π k)⟩), v) =
      marginalPrice ((cumulativeQuantityTuple ⟨n, q⟩, ⟨n, p⟩), v) := by
  apply le_antisymm
  · rw [le_marginal_iff_above _ _ hp v hi, ← above_permutation p q π]
    exact (le_marginal_iff_above _ _ hp' v hj _).mp le_rfl
  · rw [le_marginal_iff_above _ _ hp' v hj, above_permutation]
    exact (le_marginal_iff_above _ _ hp v hi _).mp le_rfl

end Thesis.Foundations.MarketClearing.DoctoralResults
