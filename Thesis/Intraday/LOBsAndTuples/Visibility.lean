import Thesis.Intraday.LOBsAndTuples.Clearing

/-! # The literal visible projection

The visible book keeps the first `k` orders of each side. The depth-restricted
step clears the full book; the projection only observes its result.
-/

noncomputable section
namespace Thesis.Intraday.Visibility

open Set Execution Clearing Foundations.MarketRepresentation
open DisjointUnionTopology TuplesMetricTopology
open Foundations.MarketActions.Primitive Foundations.MarketActions.Analytic

attribute [local instance] Execution.sigmaBorel

def take (k : ℕ) (b : Book) : Book :=
  ⟨min k b.1, fun i => b.2 ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩⟩

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

theorem take_sorted (k : ℕ) (buy : Bool) {b : Book} (h : Sorted buy b) :
    Sorted buy (take k b) := fun _ _ hij => h hij

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

end Thesis.Intraday.Visibility
