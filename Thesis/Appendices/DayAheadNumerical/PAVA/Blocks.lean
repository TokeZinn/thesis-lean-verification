import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # The block invariant of equal-weight PAVA

Every block stores the original consecutive observations, their arithmetic mean,
and the lower-prefix inequalities. A violating adjacent pair can be pooled while
preserving these inequalities. The certificates are constructed from the data;
they are not hypotheses imposed on the final fit.
-/

noncomputable section
namespace Thesis.DayAhead.PAVA

def mean (xs : List ℝ) : ℝ := xs.sum / xs.length

theorem length_mul_mean (xs : List ℝ) (hxs : 0 < xs.length) :
    (xs.length : ℝ) * mean xs = xs.sum := by
  unfold mean
  exact mul_div_cancel₀ _ (by exact_mod_cast (Nat.ne_of_gt hxs))

structure Block where
  data : List ℝ
  positive : 0 < data.length
  prefixBound : ∀ k ≤ data.length, (k : ℝ) * mean data ≤ (data.take k).sum

def singleton (x : ℝ) : Block where
  data := [x]
  positive := by simp
  prefixBound k hk := by
    have : k = 0 ∨ k = 1 := by simp only [List.length_singleton] at hk; omega
    rcases this with rfl | rfl <;> simp [mean]

theorem mean_append_identity (a b : Block) :
    ((a.data.length : ℝ) + b.data.length) * mean (a.data ++ b.data) =
      (a.data.length : ℝ) * mean a.data + (b.data.length : ℝ) * mean b.data := by
  rw [length_mul_mean _ a.positive, length_mul_mean _ b.positive]
  simpa only [List.length_append, Nat.cast_add, List.sum_append] using
    length_mul_mean (a.data ++ b.data) (by
      simp only [List.length_append]
      have := a.positive
      omega)

theorem mean_append_between (a b : Block) (hab : mean b.data ≤ mean a.data) :
    mean b.data ≤ mean (a.data ++ b.data) ∧ mean (a.data ++ b.data) ≤ mean a.data := by
  have hn : (0 : ℝ) < a.data.length := by exact_mod_cast a.positive
  have hm : (0 : ℝ) < b.data.length := by exact_mod_cast b.positive
  have hid := mean_append_identity a b
  constructor
  · have hp := mul_nonneg (le_of_lt hn) (sub_nonneg.mpr hab)
    nlinarith
  · have hp := mul_nonneg (le_of_lt hm) (sub_nonneg.mpr hab)
    nlinarith

def merge (a b : Block) (hab : mean b.data ≤ mean a.data) : Block where
  data := a.data ++ b.data
  positive := by simp only [List.length_append]; have := a.positive; omega
  prefixBound k hk := by
    have hc := mean_append_between a b hab
    have hid := mean_append_identity a b
    by_cases hka : k ≤ a.data.length
    · rw [List.take_append_of_le_length hka]
      exact (mul_le_mul_of_nonneg_left hc.2 (Nat.cast_nonneg k)).trans (a.prefixBound k hka)
    · have hk' : k - a.data.length ≤ b.data.length := by
        simp only [List.length_append] at hk
        omega
      have hkreal : (k : ℝ) = (a.data.length : ℝ) + (k - a.data.length : ℕ) := by
        exact_mod_cast (show k = a.data.length + (k - a.data.length) by omega)
      have ht : ((k - a.data.length : ℕ) : ℝ) ≤ b.data.length := by exact_mod_cast hk'
      have hp := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hc.1)
      have hprefix := b.prefixBound (k - a.data.length) hk'
      rw [List.take_append, List.take_of_length_le (by omega), List.sum_append,
        ← length_mul_mean _ a.positive]
      rw [hkreal]
      nlinarith

@[simp] theorem merge_data (a b : Block) (hab : mean b.data ≤ mean a.data) :
    (merge a b hab).data = a.data ++ b.data := rfl

end Thesis.DayAhead.PAVA
