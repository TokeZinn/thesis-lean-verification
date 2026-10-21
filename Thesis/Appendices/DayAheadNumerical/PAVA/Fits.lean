import Thesis.Appendices.DayAheadNumerical.PAVA.Algorithm
import Thesis.Appendices.DayAheadNumerical.PAVA.Optimality

/-! # PAVA output vectors minimize the declared equal-weight losses -/

noncomputable section
namespace Thesis.DayAhead.PAVA

def expand (level : Block → ℝ) (bs : List Block) : List ℝ :=
  bs.flatMap fun b => List.replicate b.data.length (level b)

theorem expand_length (level : Block → ℝ) (bs : List Block) :
    (expand level bs).length = (observations bs).length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa only [expand, observations, List.flatMap_cons, List.length_append,
      List.length_replicate] using congrArg (b.data.length + ·) ih

theorem mem_expand {level : Block → ℝ} {bs : List Block} {y : ℝ}
    (hy : y ∈ expand level bs) : ∃ b ∈ bs, y = level b := by
  obtain ⟨b, hb, hy⟩ := List.mem_flatMap.mp hy
  exact ⟨b, hb, (List.mem_replicate.mp hy).2⟩

theorem expand_sorted (level : Block → ℝ) (bs : List Block)
    (hs : bs.Pairwise (fun a b => level a ≤ level b)) :
    (expand level bs).Pairwise (· ≤ ·) := by
  induction bs with
  | nil => simp [expand]
  | cons b bs ih =>
    have hh := List.pairwise_cons.mp hs
    change (List.replicate b.data.length (level b) ++ expand level bs).Pairwise (· ≤ ·)
    rw [List.pairwise_append]
    refine ⟨by simp, ih hh.2, ?_⟩
    intro x hx y hy
    obtain rfl := (List.mem_replicate.mp hx).2
    obtain ⟨a, ha, rfl⟩ := mem_expand hy
    exact hh.1 a ha

theorem blocks_minimal (level : Block → ℝ) (allowed : ℝ → Prop) (bs : List Block)
    (hblock : ∀ b ∈ bs, ∀ ys : List ℝ, b.data.length = ys.length →
      ys.Pairwise (· ≤ ·) → (∀ y ∈ ys, allowed y) →
      loss b.data (List.replicate b.data.length (level b)) ≤ loss b.data ys)
    (ys : List ℝ) (hlen : (observations bs).length = ys.length)
    (hy : ys.Pairwise (· ≤ ·)) (ha : ∀ y ∈ ys, allowed y) :
    loss (observations bs) (expand level bs) ≤ loss (observations bs) ys := by
  induction bs generalizing ys with
  | nil => simp [observations, expand, loss]
  | cons b bs ih =>
    have hlen' : b.data.length + (observations bs).length = ys.length := by
      simpa only [observations, List.flatMap_cons, List.length_append] using hlen
    have hle : b.data.length ≤ ys.length := by omega
    have hhead : b.data.length = (ys.take b.data.length).length := by simp [hle]
    have htail : (observations bs).length = (ys.drop b.data.length).length := by
      simp only [List.length_drop]; omega
    have hfirst := hblock b (by simp) (ys.take b.data.length) hhead hy.take
      (fun y hy' => ha y (List.mem_of_mem_take hy'))
    have hrest := ih (fun a ha' => hblock a (List.mem_cons_of_mem b ha'))
      (ys.drop b.data.length) htail hy.drop (fun y hy' => ha y (List.mem_of_mem_drop hy'))
    calc
      _ = loss b.data (List.replicate b.data.length (level b)) +
          loss (observations bs) (expand level bs) :=
        loss_append (by simp) _ _
      _ ≤ loss b.data (ys.take b.data.length) +
          loss (observations bs) (ys.drop b.data.length) := add_le_add hfirst hrest
      _ = _ := by
        rw [← loss_append hhead, List.take_append_drop]
        rfl

def fit (xs : List ℝ) : List ℝ := expand (fun b => mean b.data) (fittedBlocks xs)

def boundedFit (lo hi : ℝ) (xs : List ℝ) : List ℝ :=
  expand (fun b => clip lo hi (mean b.data)) (fittedBlocks xs)

theorem fit_length (xs : List ℝ) : (fit xs).length = xs.length := by
  rw [fit, expand_length, fittedBlocks_observations]

theorem boundedFit_length (lo hi : ℝ) (xs : List ℝ) : (boundedFit lo hi xs).length = xs.length := by
  rw [boundedFit, expand_length, fittedBlocks_observations]

theorem fit_sorted (xs : List ℝ) : (fit xs).Pairwise (· ≤ ·) :=
  expand_sorted _ _ (fittedBlocks_sorted xs)

theorem boundedFit_sorted (lo hi : ℝ) (xs : List ℝ) : (boundedFit lo hi xs).Pairwise (· ≤ ·) :=
  expand_sorted _ _ ((fittedBlocks_sorted xs).imp fun h => clip_monotone lo hi h)

theorem boundedFit_mem {lo hi : ℝ} (h : lo ≤ hi) (xs : List ℝ) {y : ℝ}
    (hy : y ∈ boundedFit lo hi xs) : y ∈ Set.Icc lo hi := by
  obtain ⟨b, _, rfl⟩ := mem_expand hy
  exact clip_mem h _

theorem fit_minimal (xs ys : List ℝ) (hlen : xs.length = ys.length)
    (hy : ys.Pairwise (· ≤ ·)) : loss xs (fit xs) ≤ loss xs ys := by
  have h := blocks_minimal (fun b => mean b.data) (fun _ => True) (fittedBlocks xs)
    (fun b _ ys hl hs _ => block_mean_minimal b ys hl hs) ys
    (by rwa [fittedBlocks_observations]) hy (fun _ _ => trivial)
  simpa only [fittedBlocks_observations] using h

theorem boundedFit_minimal (xs ys : List ℝ) (hlen : xs.length = ys.length)
    (hy : ys.Pairwise (· ≤ ·)) {lo hi : ℝ} (h : lo ≤ hi)
    (hys : ∀ y ∈ ys, y ∈ Set.Icc lo hi) : loss xs (boundedFit lo hi xs) ≤ loss xs ys := by
  have hh := blocks_minimal (fun b => clip lo hi (mean b.data)) (fun y => y ∈ Set.Icc lo hi)
    (fittedBlocks xs) (fun b _ ys hl hs hys => block_clipped_minimal b ys hl hs h hys)
    ys (by rwa [fittedBlocks_observations]) hy hys
  simpa only [fittedBlocks_observations] using hh

end Thesis.DayAhead.PAVA
