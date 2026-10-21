import Thesis.DayAhead.ForecastingImpact.RecursiveTrees
import Thesis.DayAhead.ForecastingImpact.TreeImpurity
import Thesis.DayAhead.ForecastingImpact.BoostingLoss

/-! # Constrained finite greedy regression-tree training

Chapter 5, lines 211–229, 264 and 399–421. The input cuts are a finite histogram
grid on the retained features, and the input sample is the retained row subset.
Every expansion replaces exactly one current leaf by its two empirical means.
The selected expansion minimizes training squared error among the admissible
one-leaf expansions. This fixes a best-first convention where the prose leaves
implementation choices open; it is not a global optimum over all shallow trees
or a reproduction of an archived floating-point implementation.
-/

noncomputable section
namespace Thesis.DayAhead.GreedyTree

open RecursiveTrees EmpiricalGeometry TreeImpurity
open scoped BigOperators

variable {ι H : Type*} {p : ℕ}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def loss (s : Finset ι) (x : ι → Fin p → ℝ) (y : ι → H) (t : Tree p H) : ℝ :=
  ∑ i ∈ s, ‖y i - t.eval (x i)‖ ^ 2

omit [InnerProductSpace ℝ H] in
theorem loss_split (s : Finset ι) (x : ι → Fin p → ℝ) (y : ι → H)
    (j : Fin p) (c : ℝ) (l r : Tree p H) :
    loss s x y (.split j c l r) = loss (leftCell s x j c) x y l +
      loss (rightCell s x j c) x y r := by
  classical
  unfold loss
  calc
    _ = (∑ i ∈ leftCell s x j c, ‖y i - (Tree.split j c l r).eval (x i)‖ ^ 2) +
        ∑ i ∈ rightCell s x j c, ‖y i - (Tree.split j c l r).eval (x i)‖ ^ 2 := by
      rw [← Finset.sum_union (split_disjoint s x j c), split_union]
    _ = _ := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp only [Tree.eval, if_pos (Finset.mem_filter.mp hi).2]
      · apply Finset.sum_congr rfl
        intro i hi
        simp only [Tree.eval, if_neg (not_le_of_gt (Finset.mem_filter.mp hi).2)]

theorem loss_mean_eq_impurity (s : Finset ι) (hs : s.Nonempty)
    (x : ι → Fin p → ℝ) (y : ι → H) :
    loss s x y (.leaf (cellMean s y)) = (s.card : ℝ) * impurity s y := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [loss, Tree.eval, impurity, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

/-- The global sum-of-squares reduction of a leaf split is its sample count
times the thesis's local impurity reduction. Thus best-first selection by
training loss uses the sample-weighted version of the displayed local gain. -/
theorem leaf_split_reduction [DecidableEq ι] (s : Finset ι)
    (x : ι → Fin p → ℝ) (y : ι → H)
    (j : Fin p) (c : ℝ) (hl : (leftCell s x j c).Nonempty)
    (hr : (rightCell s x j c).Nonempty) :
    loss s x y (.leaf (cellMean s y)) -
      loss s x y (.split j c (.leaf (cellMean (leftCell s x j c) y))
        (.leaf (cellMean (rightCell s x j c) y))) =
      (s.card : ℝ) * impurityGain (leftCell s x j c) (rightCell s x j c) y := by
  classical
  have hs : s.Nonempty := hl.mono (Finset.filter_subset _ _)
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  rw [loss_split, loss_mean_eq_impurity s hs, loss_mean_eq_impurity _ hl,
    loss_mean_eq_impurity _ hr, impurityGain, split_union]
  field_simp
  ring

/-- Leaf means and minimum sample sizes are checked on the actual routed rows. -/
def FitsOn (minimum : ℕ) (x : ι → Fin p → ℝ) (y : ι → H) :
    Finset ι → Tree p H → Prop
  | s, .leaf value => minimum ≤ s.card ∧ value = cellMean s y
  | s, .split j c l r =>
      FitsOn minimum x y (leftCell s x j c) l ∧
      FitsOn minimum x y (rightCell s x j c) r

def legalCuts (minimum : ℕ) (cuts : Finset (Fin p × ℝ))
    (s : Finset ι) (x : ι → Fin p → ℝ) : Finset (Fin p × ℝ) :=
  cuts.filter fun q => minimum ≤ (leftCell s x q.1 q.2).card ∧
    minimum ≤ (rightCell s x q.1 q.2).card

/-- Enumerate all single-leaf expansions, retaining every other branch. -/
def expansions (minimum : ℕ) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) (t : Tree p H) :
    Finset (Tree p H) := by
  classical
  exact match t with
  | .leaf _ => (legalCuts minimum cuts s x).image fun q =>
      .split q.1 q.2 (.leaf (cellMean (leftCell s x q.1 q.2) y))
        (.leaf (cellMean (rightCell s x q.1 q.2) y))
  | .split j c l r =>
      ((expansions minimum cuts x y (leftCell s x j c) l).image fun l' =>
        .split j c l' r) ∪
      ((expansions minimum cuts x y (rightCell s x j c) r).image fun r' =>
        .split j c l r')

theorem expansion_leafCount (minimum : ℕ) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) (t : Tree p H)
    {u : Tree p H} (hu : u ∈ expansions minimum cuts x y s t) :
    u.leafCount = t.leafCount + 1 := by
  classical
  induction t generalizing s u with
  | leaf value =>
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hu
    rfl
  | split j c l r hl hr =>
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      simp only [Tree.leafCount, hl _ hv]
      omega
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      simp only [Tree.leafCount, hr _ hv]
      omega

theorem expansion_fitsOn (minimum : ℕ) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) (t : Tree p H)
    (ht : FitsOn minimum x y s t) {u : Tree p H}
    (hu : u ∈ expansions minimum cuts x y s t) : FitsOn minimum x y s u := by
  classical
  induction t generalizing s u with
  | leaf value =>
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    have hq' := (Finset.mem_filter.mp hq).2
    exact ⟨⟨hq'.1, rfl⟩, ⟨hq'.2, rfl⟩⟩
  | split j c l r hl hr =>
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨hl _ ht.1 hv, ht.2⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨ht.1, hr _ ht.2 hv⟩

theorem fitsOn_nonempty (minimum : ℕ) (hm : 0 < minimum)
    (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) (t : Tree p H)
    (ht : FitsOn minimum x y s t) : s.Nonempty := by
  induction t generalizing s with
  | leaf value => exact Finset.card_pos.mp (lt_of_lt_of_le hm ht.1)
  | split j c l r hl _ =>
    obtain ⟨i, hi⟩ := hl _ ht.1
    exact ⟨i, (Finset.mem_filter.mp hi).1⟩

/-- Positive leaf sample sizes imply nonempty geometric terminal regions. -/
theorem fitsOn_validOn (minimum : ℕ) (hm : 0 < minimum)
    (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) (t : Tree p H)
    (ht : FitsOn minimum x y s t) (R : Set (Fin p → ℝ))
    (hR : ∀ i ∈ s, x i ∈ R) : t.ValidOn R := by
  induction t generalizing s R with
  | leaf value =>
    obtain ⟨i, hi⟩ := fitsOn_nonempty minimum hm x y s (.leaf value) ht
    exact ⟨x i, hR i hi⟩
  | split j c l r hl hr =>
    constructor
    · apply hl _ ht.1
      intro i hi
      exact ⟨hR i (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    · apply hr _ ht.2
      intro i hi
      exact ⟨hR i (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

def admissible (minimum maxLeaves maxDepth : ℕ) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) (t : Tree p H) :
    Finset (Tree p H) := by
  classical
  exact (expansions minimum cuts x y s t).filter fun u =>
    u.leafCount ≤ maxLeaves ∧ u.depth ≤ maxDepth

def improving (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (t : Tree p H) : Finset (Tree p H) := by
  classical
  exact (admissible minimum maxLeaves maxDepth cuts x y s t).filter fun u =>
    threshold < loss s x y t - loss s x y u

/-- A best admissible expansion is selected only if it clears the threshold.
The source does not specify how equal-gain cuts are ordered; choice fixes one. -/
def step (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (t : Tree p H) : Option (Tree p H) := by
  classical
  let candidates := improving minimum maxLeaves maxDepth threshold cuts x y s t
  exact if h : candidates.Nonempty then
    some (Classical.choose (Finset.exists_min_image candidates (loss s x y) h))
  else none

theorem step_spec (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (t : Tree p H) {u : Tree p H}
    (hu : step minimum maxLeaves maxDepth threshold cuts x y s t = some u) :
    u ∈ improving minimum maxLeaves maxDepth threshold cuts x y s t ∧
      ∀ v ∈ improving minimum maxLeaves maxDepth threshold cuts x y s t,
        loss s x y u ≤ loss s x y v := by
  classical
  unfold step at hu
  dsimp only at hu
  split_ifs at hu with h
  · have he := Option.some.inj hu
    subst u
    exact Classical.choose_spec (Finset.exists_min_image _ _ h)

theorem step_none_iff (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (t : Tree p H) :
    step minimum maxLeaves maxDepth threshold cuts x y s t = none ↔
      improving minimum maxLeaves maxDepth threshold cuts x y s t = ∅ := by
  classical
  simp only [step]
  split_ifs with h
  · simp only [false_iff]
    exact Finset.Nonempty.ne_empty h
  · simp only [true_iff]
    exact Finset.not_nonempty_iff_eq_empty.mp h

theorem step_constraints (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (t : Tree p H) {u : Tree p H}
    (hu : step minimum maxLeaves maxDepth threshold cuts x y s t = some u) :
    u ∈ expansions minimum cuts x y s t ∧ u.leafCount ≤ maxLeaves ∧
      u.depth ≤ maxDepth ∧ threshold < loss s x y t - loss s x y u := by
  classical
  have hi := (step_spec minimum maxLeaves maxDepth threshold cuts x y s t hu).1
  have ha := Finset.mem_filter.mp hi
  have he := Finset.mem_filter.mp ha.1
  exact ⟨he.1, he.2.1, he.2.2, ha.2⟩

/-- Minimization over all admissible single-leaf expansions, including those
that do not clear the improvement threshold. -/
theorem step_best (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (t : Tree p H) {u v : Tree p H}
    (hu : step minimum maxLeaves maxDepth threshold cuts x y s t = some u)
    (hv : v ∈ admissible minimum maxLeaves maxDepth cuts x y s t) :
    loss s x y u ≤ loss s x y v := by
  classical
  by_cases h : threshold < loss s x y t - loss s x y v
  · exact (step_spec minimum maxLeaves maxDepth threshold cuts x y s t hu).2 v
      (Finset.mem_filter.mpr ⟨hv, h⟩)
  · have hgain := (step_constraints minimum maxLeaves maxDepth threshold cuts x y s t hu).2.2.2
    linarith

def grow (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) : ℕ → Tree p H → Tree p H
  | 0, t => t
  | n + 1, t => match step minimum maxLeaves maxDepth threshold cuts x y s t with
      | none => t
      | some u => grow minimum maxLeaves maxDepth threshold cuts x y s n u

theorem grow_spec (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ) (hε : 0 ≤ threshold)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (n : ℕ) (t : Tree p H) (ht : FitsOn minimum x y s t)
    (hleaves : t.leafCount ≤ maxLeaves) (hdepth : t.depth ≤ maxDepth) :
    let u := grow minimum maxLeaves maxDepth threshold cuts x y s n t
    FitsOn minimum x y s u ∧ u.leafCount ≤ maxLeaves ∧ u.depth ≤ maxDepth ∧
      loss s x y u ≤ loss s x y t := by
  induction n generalizing t with
  | zero => exact ⟨ht, hleaves, hdepth, le_rfl⟩
  | succ n ih =>
    cases hstep : step minimum maxLeaves maxDepth threshold cuts x y s t with
    | none => simpa only [grow, hstep] using And.intro ht ⟨hleaves, hdepth, le_rfl⟩
    | some u =>
      have hu := step_constraints minimum maxLeaves maxDepth threshold cuts x y s t hstep
      have hfit := expansion_fitsOn minimum cuts x y s t ht hu.1
      have h := ih u hfit hu.2.1 hu.2.2.1
      have hloss : loss s x y u ≤ loss s x y t := by linarith [hu.2.2.2]
      simpa only [grow, hstep] using And.intro h.1 ⟨h.2.1, h.2.2.1, h.2.2.2.trans hloss⟩

/-- The leaf budget supplies enough iterations to reach the actual stopping
condition. The fuel bound does not mask an unperformed legal expansion. -/
theorem grow_stops (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (n : ℕ) (t : Tree p H) (hn : maxLeaves ≤ t.leafCount + n) :
    step minimum maxLeaves maxDepth threshold cuts x y s
      (grow minimum maxLeaves maxDepth threshold cuts x y s n t) = none := by
  induction n generalizing t with
  | zero =>
    simp only [grow]
    cases hstep : step minimum maxLeaves maxDepth threshold cuts x y s t with
    | none => rfl
    | some u =>
      have hu := step_constraints minimum maxLeaves maxDepth threshold cuts x y s t hstep
      have hc := expansion_leafCount minimum cuts x y s t hu.1
      omega
  | succ n ih =>
    cases hstep : step minimum maxLeaves maxDepth threshold cuts x y s t with
    | none => simp only [grow, hstep]
    | some u =>
      have hu := step_constraints minimum maxLeaves maxDepth threshold cuts x y s t hstep
      have hc := expansion_leafCount minimum cuts x y s t hu.1
      simpa only [grow, hstep] using ih u (by omega)

def train (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) : Tree p H :=
  grow minimum maxLeaves maxDepth threshold cuts x y s (maxLeaves - 1) (.leaf (cellMean s y))

theorem train_spec (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (hε : 0 ≤ threshold) (hmax : 0 < maxLeaves)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (hs : minimum ≤ s.card) :
    let u := train minimum maxLeaves maxDepth threshold cuts x y s
    FitsOn minimum x y s u ∧ u.leafCount ≤ maxLeaves ∧ u.depth ≤ maxDepth ∧
      loss s x y u ≤ loss s x y (.leaf (cellMean s y)) :=
  grow_spec minimum maxLeaves maxDepth threshold hε cuts x y s (maxLeaves - 1)
    (.leaf (cellMean s y)) ⟨hs, rfl⟩ hmax (Nat.zero_le _)

theorem train_stops (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) :
    step minimum maxLeaves maxDepth threshold cuts x y s
      (train minimum maxLeaves maxDepth threshold cuts x y s) = none :=
  grow_stops minimum maxLeaves maxDepth threshold cuts x y s (maxLeaves - 1)
    (.leaf (cellMean s y)) (by simp only [Tree.leafCount]; omega)

theorem train_validOn (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (hε : 0 ≤ threshold) (hmin : 0 < minimum) (hmax : 0 < maxLeaves)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (hs : minimum ≤ s.card) :
    (train minimum maxLeaves maxDepth threshold cuts x y s).ValidOn Set.univ :=
  fitsOn_validOn minimum hmin x y s _
    (train_spec minimum maxLeaves maxDepth threshold hε hmax cuts x y s hs).1
    Set.univ (fun _ _ => Set.mem_univ _)

theorem train_no_improving_expansion (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) {v : Tree p H}
    (hv : v ∈ admissible minimum maxLeaves maxDepth cuts x y s
      (train minimum maxLeaves maxDepth threshold cuts x y s)) :
    loss s x y (train minimum maxLeaves maxDepth threshold cuts x y s) -
      loss s x y v ≤ threshold := by
  classical
  have he := (step_none_iff minimum maxLeaves maxDepth threshold cuts x y s _).mp
    (train_stops minimum maxLeaves maxDepth threshold cuts x y s)
  by_contra h
  have hm : v ∈ improving minimum maxLeaves maxDepth threshold cuts x y s
      (train minimum maxLeaves maxDepth threshold cuts x y s) :=
    Finset.mem_filter.mpr ⟨hv, lt_of_not_ge h⟩
  rw [he] at hm
  exact Finset.notMem_empty v hm

def SplitsIn (cuts : Finset (Fin p × ℝ)) : Tree p H → Prop
  | .leaf _ => True
  | .split j c l r => (j, c) ∈ cuts ∧ SplitsIn cuts l ∧ SplitsIn cuts r

theorem expansion_splitsIn (minimum : ℕ) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) (t : Tree p H)
    (ht : SplitsIn cuts t) {u : Tree p H}
    (hu : u ∈ expansions minimum cuts x y s t) : SplitsIn cuts u := by
  classical
  induction t generalizing s u with
  | leaf value =>
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨(Finset.mem_filter.mp hq).1, trivial, trivial⟩
  | split j c l r hl hr =>
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨ht.1, hl _ ht.2.1 hv, ht.2.2⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨ht.1, ht.2.1, hr _ ht.2.2 hv⟩

theorem grow_splitsIn (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H)
    (s : Finset ι) (n : ℕ) (t : Tree p H) (ht : SplitsIn cuts t) :
    SplitsIn cuts (grow minimum maxLeaves maxDepth threshold cuts x y s n t) := by
  induction n generalizing t with
  | zero => exact ht
  | succ n ih =>
    cases hstep : step minimum maxLeaves maxDepth threshold cuts x y s t with
    | none => simpa only [grow, hstep] using ht
    | some u =>
      have hu := (step_constraints minimum maxLeaves maxDepth threshold cuts x y s t hstep).1
      simpa only [grow, hstep] using ih u (expansion_splitsIn minimum cuts x y s t ht hu)

theorem train_splitsIn (minimum maxLeaves maxDepth : ℕ) (threshold : ℝ)
    (cuts : Finset (Fin p × ℝ)) (x : ι → Fin p → ℝ) (y : ι → H) (s : Finset ι) :
    SplitsIn cuts (train minimum maxLeaves maxDepth threshold cuts x y s) :=
  grow_splitsIn minimum maxLeaves maxDepth threshold cuts x y s (maxLeaves - 1)
    (.leaf (cellMean s y)) trivial

/-- Finite exhaustive observed-value cuts on a retained feature set. Quantile
histogram cuts can be supplied as a smaller finite grid. -/
def observedCuts (features : Finset (Fin p)) (s : Finset ι) (x : ι → Fin p → ℝ) :
    Finset (Fin p × ℝ) := by
  classical
  exact features.biUnion fun j => s.image fun i => (j, x i j)

/-- Every cut with a nonempty left sample has an observed-value cut that routes
exactly the same rows, including ties. No interpolation of duplicate inputs is
claimed. -/
theorem observedCuts_exhaustive (features : Finset (Fin p)) (s : Finset ι)
    (x : ι → Fin p → ℝ) (j : Fin p) (hj : j ∈ features) (c : ℝ)
    (hleft : (leftCell s x j c).Nonempty) :
    ∃ d, (j, d) ∈ observedCuts features s x ∧
      leftCell s x j d = leftCell s x j c ∧ rightCell s x j d = rightCell s x j c := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (leftCell s x j c) (fun i => x i j) hleft
  have hic := (Finset.mem_filter.mp hi).2
  refine ⟨x i j, ?_, ?_, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨j, hj,
      Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩⟩
  · ext k
    simp only [leftCell, Finset.mem_filter]
    constructor
    · rintro ⟨hk, hki⟩
      exact ⟨hk, hki.trans hic⟩
    · rintro ⟨hk, hkc⟩
      exact ⟨hk, hmax k (Finset.mem_filter.mpr ⟨hk, hkc⟩)⟩
  · ext k
    simp only [rightCell, Finset.mem_filter]
    constructor
    · rintro ⟨hk, hik⟩
      refine ⟨hk, ?_⟩
      by_contra h
      exact not_le_of_gt hik (hmax k (Finset.mem_filter.mpr ⟨hk, le_of_not_gt h⟩))
    · rintro ⟨hk, hck⟩
      exact ⟨hk, hic.trans_lt hck⟩

end Thesis.DayAhead.GreedyTree
