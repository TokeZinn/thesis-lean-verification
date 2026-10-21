import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Strict ranks of a finite tie-free ensemble

The deterministic combinatorics behind `prop:midrank-coverage-expectations`:
the strict ranks of all B+1 values are a permutation of 0,...,B. The
exchangeability-to-equal-rank-laws probability step remains separate.
-/

noncomputable section
namespace Thesis.Intraday.StrictRanks
open scoped BigOperators

def below {N : ℕ} (values : Fin N → ℝ) (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun j => values j < values i

theorem below_card_lt {N : ℕ} (values : Fin N → ℝ) (i : Fin N) :
    (below values i).card < N := by
  have hs : below values i ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro he
    have h : i ∈ below values i := he.symm ▸ Finset.mem_univ i
    simp [below] at h
  simpa using Finset.card_lt_card hs

def rank {N : ℕ} (values : Fin N → ℝ) (i : Fin N) : Fin N :=
  ⟨(below values i).card, below_card_lt values i⟩

theorem rank_lt_of_value_lt {N : ℕ} (values : Fin N → ℝ) (i j : Fin N)
    (h : values i < values j) : rank values i < rank values j := by
  change (below values i).card < (below values j).card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hk).2 h⟩
  · intro he
    have hi : i ∈ below values j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [← he] at hi
    simp [below] at hi

theorem rank_injective {N : ℕ} (values : Fin N → ℝ) (h : Function.Injective values) :
    Function.Injective (rank values) := by
  intro i j he
  apply h
  rcases lt_trichotomy (values i) (values j) with hl | heq | hr
  · have := rank_lt_of_value_lt values i j hl
    rw [he] at this
    exact (lt_irrefl _ this).elim
  · exact heq
  · have := rank_lt_of_value_lt values j i hr
    rw [he] at this
    exact (lt_irrefl _ this).elim

def rankEquiv {N : ℕ} (values : Fin N → ℝ) (h : Function.Injective values) : Fin N ≃ Fin N :=
  Equiv.ofBijective (rank values) ((Finite.injective_iff_bijective).mp (rank_injective values h))

/-- Every reference rank occurs exactly once, so averaging over the identity
of the observed member gives exactly the discrete reference central count. -/
theorem rank_sum {N : ℕ} (values : Fin N → ℝ) (h : Function.Injective values)
    (f : Fin N → ℝ) : ∑ i, f (rank values i) = ∑ j, f j :=
  Equiv.sum_comp (rankEquiv values h) f

theorem rank_precomp {N : ℕ} (values : Fin N → ℝ) (permutation : Equiv.Perm (Fin N))
    (i : Fin N) : rank (values ∘ permutation) i = rank values (permutation i) := by
  apply Fin.ext
  change (below (values ∘ permutation) i).card = (below values (permutation i)).card
  apply Finset.card_bij (fun j _ => permutation j)
  · intro j hj
    simpa only [below, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply] using hj
  · intro j _ k _ he
    exact permutation.injective he
  · intro j hj
    refine ⟨permutation.symm j, ?_, by simp⟩
    simpa only [below, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply, Equiv.apply_symm_apply] using hj

end Thesis.Intraday.StrictRanks
