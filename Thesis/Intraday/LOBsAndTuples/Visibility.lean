import Thesis.Intraday.LOBsAndTuples.Clearing

/-! # The literal visible projection and latent-tail recombination

The truncation acts after the full-book action and sorting. The returned tails
are retained without a second clearing pass, as required by the manuscript.
-/

noncomputable section
namespace Thesis.Intraday.Visibility

open Set Execution Clearing Foundations.MarketRepresentation
open DisjointUnionTopology TuplesMetricTopology
open Foundations.MarketActions.Primitive Foundations.MarketActions.Analytic

attribute [local instance] Execution.sigmaBorel

def take (k : ℕ) (b : Book) : Book :=
  ⟨min k b.1, fun i => b.2 ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩⟩

def drop (k : ℕ) (b : Book) : Book :=
  ⟨b.1 - min k b.1, fun i => b.2 ⟨min k b.1 + i.val, by
    have hi := i.isLt
    have hk := min_le_right k b.1
    omega⟩⟩

theorem take_eq_self (k : ℕ) (b : Book) (h : b.1 ≤ k) : take k b = b := by
  rcases b with ⟨n, b⟩
  change n ≤ k at h
  have hn : min k n = n := min_eq_right h
  apply Sigma.ext hn
  apply Function.hfunext (congrArg Fin hn)
  intro i j hij
  apply heq_of_eq
  apply congrArg b
  have hval : i.val = j.val := Fin.val_eq_val_of_heq hij
  exact Fin.ext hval

theorem take_idempotent (k : ℕ) (b : Book) : take k (take k b) = take k b :=
  take_eq_self k _ (min_le_left _ _)

theorem continuous_take (k : ℕ) : Continuous (take k) := by
  apply continuous_pasting_iff.mpr
  intro n
  dsimp only [take]
  exact (continuous_sigmaMk (i := min k n)).comp (continuous_pi fun i : Fin (min k n) =>
    continuous_apply (⟨i.val, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩ : Fin n))

theorem continuous_drop (k : ℕ) : Continuous (drop k) := by
  apply continuous_pasting_iff.mpr
  intro n
  dsimp only [drop]
  exact (continuous_sigmaMk (i := n - min k n)).comp (continuous_pi fun i : Fin (n - min k n) =>
    continuous_apply (⟨min k n + i.val, by
      have hi := i.isLt
      have hk := min_le_right k n
      omega⟩ : Fin n))

theorem take_sorted (k : ℕ) (buy : Bool) {b : Book} (h : Sorted buy b) :
    Sorted buy (take k b) := fun _ _ hij => h hij

theorem drop_sorted (k : ℕ) (buy : Bool) {b : Book} (h : Sorted buy b) :
    Sorted buy (drop k b) := by
  intro i j hij
  apply h
  change min k b.1 + i.val ≤ min k b.1 + j.val
  exact Nat.add_le_add_left hij _

theorem continuous_concatBook : Continuous (fun p : Book × Book => concat p.1 p.2) := by
  have h := continuous_concat_emetricTopology (X := Order)
  change @Continuous (Book × Book) Book
    (@instTopologicalSpaceProd Book Book (tupleHausdorffMetricTopology (X := Order))
      (tupleHausdorffMetricTopology (X := Order)))
    (tupleHausdorffMetricTopology (X := Order)) _ at h
  rw [tupleHausdorffMetricTopology_eq_sigma] at h
  exact h

/-- Original label: `defn:visible-order-book`.
Equation `eq:intraday-visible-projection` uses k = 100. -/
def visible (k : ℕ) (m : Market) : Market :=
  joinMarket (take k (side true m), take k (side false m))

theorem side_visible_true (k : ℕ) (m : Market) :
    side true (visible k m) = take k (side true m) := side_join_true _

theorem side_visible_false (k : ℕ) (m : Market) :
    side false (visible k m) = take k (side false m) := side_join_false _

/-- Exact per-side visibility count, including empty and short sides. -/
theorem visible_side_count (k : ℕ) (buy : Bool) (m : Market) :
    (side buy (visible k m)).1 = min k (side buy m).1 := by
  cases buy
  · rw [side_visible_false]; rfl
  · rw [side_visible_true]; rfl

theorem visible_side_count_le (k : ℕ) (buy : Bool) (m : Market) :
    (side buy (visible k m)).1 ≤ k := by
  rw [visible_side_count]
  exact min_le_left _ _

theorem visible_idempotent (k : ℕ) (m : Market) : visible k (visible k m) = visible k m := by
  conv_lhs => unfold visible
  rw [side_join_true, side_join_false, take_idempotent, take_idempotent]
  rfl

theorem continuous_visible (k : ℕ) : Continuous (visible k) :=
  continuous_joinMarket.comp
    (((continuous_take k).comp (continuous_side true)).prodMk
      ((continuous_take k).comp (continuous_side false)))

theorem visible_sorted (k : ℕ) {m : Market} (h : SortedMarket m) :
    SortedMarket (visible k m) :=
  joinMarket_sorted ⟨take_sorted k true (side_sorted true h),
    take_sorted k false (side_sorted false h)⟩

theorem visible_length_bound (k : ℕ) (m : Market) : (visible k m).1 ≤ 2 * k := by
  change min k (side true m).1 + min k (side false m).1 ≤ 2 * k
  have hb := min_le_left k (side true m).1
  have hs := min_le_left k (side false m).1
  omega

/-- The exact operation in Figure `fig:visible-latent-book`, on the already
acted-on and sorted book. Each cleared side is followed by its original tail. -/
def depthClear (k : ℕ) (m : Market) : Market :=
  let cleared := clearMarket (visible k m)
  joinMarket (concat (side true cleared) (drop k (side true m)),
    concat (side false cleared) (drop k (side false m)))

theorem measurable_depthClear (k : ℕ) : Measurable (depthClear k) := by
  have hc := measurable_clearMarket.comp (continuous_visible k).measurable
  have hside (buy : Bool) : Measurable (fun m : Market =>
      concat (side buy (clearMarket (visible k m))) (drop k (side buy m))) :=
    continuous_concatBook.measurable.comp
      (((continuous_side buy).measurable.comp hc).prodMk
        ((continuous_drop k).comp (continuous_side buy)).measurable)
  exact continuous_joinMarket.measurable.comp ((hside true).prodMk (hside false))

theorem visible_side_keySubset (k : ℕ) (buy : Bool) (m : Market) :
    KeySubset buy (side buy (visible k m)) (take k (side buy m)) := by
  intro i
  obtain ⟨j, hj⟩ := side_join_exists buy
    (take k (side true m), take k (side false m)) i
  cases buy <;> exact ⟨j, congrArg (priorityKey _) hj⟩

theorem concat_sorted (buy : Bool) {a b : Book}
    (ha : Sorted buy a) (hb : Sorted buy b)
    (hab : ∀ i j, priorityKey buy (a.2 i) ≤ priorityKey buy (b.2 j)) :
    Sorted buy (concat a b) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      simpa [concat, Tuple.entry] using ha (show i ≤ j from hij)
    · intro j _
      simpa [concat, Tuple.entry] using hab i j
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      have hj : j.val < a.1 := j.isLt
      change a.1 + i.val ≤ j.val at hij
      omega
    · intro j hij
      have hij' : i ≤ j := by
        change a.1 + i.val ≤ a.1 + j.val at hij
        exact Nat.le_of_add_le_add_left hij
      simpa [concat, Tuple.entry] using hb hij'

theorem take_drop_key_le (k : ℕ) (buy : Bool) {b : Book} (h : Sorted buy b)
    (i : Fin (take k b).1) (j : Fin (drop k b).1) :
    priorityKey buy ((take k b).2 i) ≤ priorityKey buy ((drop k b).2 j) := by
  apply h
  change i.val ≤ min k b.1 + j.val
  have hi : i.val < min k b.1 := i.isLt
  omega

/-- Surviving visible orders keep their price-time keys, so they still precede
the original latent tail. No second execution against that tail is used. -/
theorem depthClear_sorted (k : ℕ) {m : Market} (h : SortedMarket m) :
    SortedMarket (depthClear k m) := by
  have hclear := clearMarket_sorted (visible_sorted k h)
  have hs (buy : Bool) : Sorted buy
      (concat (side buy (clearMarket (visible k m))) (drop k (side buy m))) := by
    apply concat_sorted buy (side_sorted buy hclear) (drop_sorted k buy (side_sorted buy h))
    intro i j
    have hk := (clearMarket_keySubset buy (visible k m)).trans
      (visible_side_keySubset k buy m)
    obtain ⟨l, hl⟩ := hk i
    rw [hl]
    exact take_drop_key_le k buy (side_sorted buy h) l j
  exact joinMarket_sorted ⟨hs true, hs false⟩

end Thesis.Intraday.Visibility
