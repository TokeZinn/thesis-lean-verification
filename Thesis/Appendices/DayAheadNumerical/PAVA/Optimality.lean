import Thesis.Appendices.DayAheadNumerical.PAVA.Blocks
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Pairwise

/-! # Optimality of certified PAVA blocks

The prefix invariant implies the projection inequality by finite summation by
parts. Clipping a final block mean to a common interval preserves optimality
against monotone competitors in that interval.
-/

noncomputable section
namespace Thesis.DayAhead.PAVA

def weighted (xs ys : List ℝ) : ℝ := (List.zipWith (· * ·) xs ys).sum

theorem weighted_append {xs ys : List ℝ} (h : xs.length = ys.length)
    (xs' ys' : List ℝ) : weighted (xs ++ xs') (ys ++ ys') =
      weighted xs ys + weighted xs' ys' := by
  simp only [weighted, List.zipWith_append h, List.sum_append]

theorem weighted_le_sum_mul (xs ys : List ℝ) (hlen : xs.length = ys.length)
    (hp : ∀ k ≤ xs.length, 0 ≤ (xs.take k).sum) (hy : ys.Pairwise (· ≤ ·))
    (bound : ℝ) (hbound : ∀ y ∈ ys, y ≤ bound) : weighted xs ys ≤ xs.sum * bound := by
  induction ys using List.reverseRecOn generalizing xs bound with
  | nil =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen
    subst xs
    simp [weighted]
  | append_singleton ys y ih =>
    rcases List.eq_nil_or_concat' xs with rfl | ⟨rs, r, rfl⟩
    · simp at hlen
    have hlen' : rs.length = ys.length := by simpa using hlen
    have hp' : ∀ k ≤ rs.length, 0 ≤ (rs.take k).sum := by
      intro k hk
      simpa only [List.take_append_of_le_length hk] using
        hp k (by simp only [List.length_append, List.length_singleton]; omega)
    have hyt := List.pairwise_append.mp hy
    have hs := ih rs hlen' hp' hyt.1 y (fun v hv => hyt.2.2 v hv y (by simp))
    have hlast : y ≤ bound := hbound y (by simp)
    have htotal : 0 ≤ rs.sum + r := by
      simpa using hp (rs ++ [r]).length le_rfl
    rw [weighted_append hlen']
    simp only [weighted, List.zipWith_cons_cons, List.zipWith_nil_left,
      List.sum_cons, List.sum_nil, add_zero, List.sum_append] at hs ⊢
    calc
      _ ≤ rs.sum * y + r * y := by linarith
      _ = (rs.sum + r) * y := by ring
      _ ≤ (rs.sum + r) * bound := mul_le_mul_of_nonneg_left hlast htotal

theorem weighted_nonpos (xs ys : List ℝ) (hlen : xs.length = ys.length)
    (hp : ∀ k ≤ xs.length, 0 ≤ (xs.take k).sum) (hsum : xs.sum = 0)
    (hy : ys.Pairwise (· ≤ ·)) : weighted xs ys ≤ 0 := by
  by_cases hnil : ys = []
  · subst ys
    simp [weighted]
  · have h := weighted_le_sum_mul xs ys hlen hp hy (ys.getLast hnil)
      (fun y hy' => hy.rel_getLast hy')
    simpa only [hsum, zero_mul] using h

theorem sum_sub_const (xs : List ℝ) (c : ℝ) :
    (xs.map (fun x => x - c)).sum = xs.sum - (xs.length : ℝ) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, ih]; ring

def residuals (b : Block) : List ℝ := b.data.map (fun x => x - mean b.data)

theorem residuals_sum (b : Block) : (residuals b).sum = 0 := by
  rw [residuals, sum_sub_const, length_mul_mean _ b.positive, sub_self]

theorem residuals_prefix (b : Block) :
    ∀ k ≤ (residuals b).length, 0 ≤ ((residuals b).take k).sum := by
  intro k hk
  simp only [residuals, List.length_map] at hk
  simp only [residuals, ← List.map_take, sum_sub_const, List.length_take, Nat.min_eq_left hk]
  exact sub_nonneg.mpr (b.prefixBound k hk)

theorem block_residual_pairing (b : Block) (ys : List ℝ)
    (hlen : b.data.length = ys.length) (hy : ys.Pairwise (· ≤ ·)) (c : ℝ) :
    (List.zipWith (fun x y => (x - mean b.data) * (y - c)) b.data ys).sum ≤ 0 := by
  have hym : (ys.map (fun y => y - c)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hy.imp (fun h => sub_le_sub_right h c)
  have h := weighted_nonpos (residuals b) (ys.map fun y => y - c)
    (by simpa [residuals] using hlen) (residuals_prefix b) (residuals_sum b) hym
  simpa only [weighted, residuals, List.zipWith_map_left, List.zipWith_map_right] using h

def loss (xs ys : List ℝ) : ℝ := (List.zipWith (fun x y => (x - y) ^ 2) xs ys).sum

theorem loss_append {xs ys : List ℝ} (h : xs.length = ys.length) (xs' ys' : List ℝ) :
    loss (xs ++ xs') (ys ++ ys') = loss xs ys + loss xs' ys' := by
  simp only [loss, List.zipWith_append h, List.sum_append]

theorem loss_identity (xs ys : List ℝ) (hlen : xs.length = ys.length) (c : ℝ) :
    loss xs ys = loss xs (List.replicate xs.length c) +
      (ys.map (fun y => (y - c)^2)).sum -
      2 * (List.zipWith (fun x y => (x - c) * (y - c)) xs ys).sum := by
  induction xs generalizing ys with
  | nil => have : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm; subst ys; simp [loss]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      have hh := ih ys hlen'
      simp only [loss, List.zipWith_cons_cons, List.sum_cons, List.length_cons,
        List.replicate_succ, List.map_cons] at hh ⊢
      linarith [sq_nonneg (x-y)]

theorem constantFit_minimal (xs ys : List ℝ) (hlen : xs.length = ys.length) (c : ℝ)
    (hvar : (List.zipWith (fun x y => (x - c) * (y - c)) xs ys).sum ≤ 0) :
    loss xs (List.replicate xs.length c) ≤ loss xs ys := by
  rw [loss_identity xs ys hlen c]
  have hsq : 0 ≤ (ys.map (fun y => (y - c)^2)).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp ha
    exact sq_nonneg _
  linarith

theorem block_mean_minimal (b : Block) (ys : List ℝ)
    (hlen : b.data.length = ys.length) (hy : ys.Pairwise (· ≤ ·)) :
    loss b.data (List.replicate b.data.length (mean b.data)) ≤ loss b.data ys :=
  constantFit_minimal b.data ys hlen (mean b.data) (block_residual_pairing b ys hlen hy _)

def clip (lo hi x : ℝ) : ℝ := min (max x lo) hi

theorem clip_mem {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) : clip lo hi x ∈ Set.Icc lo hi :=
  ⟨le_min (le_max_right _ _) h, min_le_right _ _⟩

theorem clip_monotone (lo hi : ℝ) : Monotone (clip lo hi) :=
  fun _ _ h => min_le_min (max_le_max h le_rfl) le_rfl

theorem clip_pairing_nonpos {lo hi y : ℝ} (h : lo ≤ hi) (hy : y ∈ Set.Icc lo hi) (m : ℝ) :
    (m - clip lo hi m) * (y - clip lo hi m) ≤ 0 := by
  by_cases hlo : m ≤ lo
  · rw [clip, max_eq_right hlo, min_eq_left h]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlo) (sub_nonneg.mpr hy.1)
  by_cases hhi : hi ≤ m
  · rw [clip, max_eq_left (le_of_not_ge hlo), min_eq_right hhi]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hhi) (sub_nonpos.mpr hy.2)
  · rw [clip, max_eq_left (le_of_not_ge hlo), min_eq_left (le_of_not_ge hhi), sub_self, zero_mul]

theorem pairing_le_of_shift (xs ys : List ℝ) (m c : ℝ)
    (h : ∀ y ∈ ys, (m - c) * (y - c) ≤ 0) :
    (List.zipWith (fun x y => (x - c) * (y - c)) xs ys).sum ≤
      (List.zipWith (fun x y => (x - m) * (y - c)) xs ys).sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have ht := ih ys (fun v hv => h v (List.mem_cons_of_mem y hv))
      have hh := h y (by simp)
      simp only [List.zipWith_cons_cons, List.sum_cons]
      nlinarith

theorem block_clipped_minimal (b : Block) (ys : List ℝ)
    (hlen : b.data.length = ys.length) (hy : ys.Pairwise (· ≤ ·))
    {lo hi : ℝ} (h : lo ≤ hi) (hys : ∀ y ∈ ys, y ∈ Set.Icc lo hi) :
    loss b.data (List.replicate b.data.length (clip lo hi (mean b.data))) ≤ loss b.data ys := by
  apply constantFit_minimal b.data ys hlen
  exact (pairing_le_of_shift b.data ys (mean b.data) _
    (fun y hy' => clip_pairing_nonpos h (hys y hy') _)).trans
      (block_residual_pairing b ys hlen hy _)

end Thesis.DayAhead.PAVA
