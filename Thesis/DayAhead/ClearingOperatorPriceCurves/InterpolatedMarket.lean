import Thesis.DayAhead.ClearingOperatorPriceCurves.EquilibriumQuantity
import Thesis.Foundations.MarketClearing.DoctoralPermutation
import Mathlib.Data.Prod.Lex

/-! # Tagged market tuples become the current interpolated sorted book

Unlike the retained step-model price sort, this adapter also sorts volume
increasingly within equal prices. That tie convention matters for affine
interpolation. Quantities remain individual order volumes until the Book
construction forms their cumulative sums.
-/

noncomputable section
namespace Thesis.DayAhead.InterpolatedMarket

open Set
open Foundations.MarketRepresentation TuplesBasic TuplesSorting
open Foundations.MarketClearing.Sorting
open Foundations.MarketClearing.DoctoralPermutation

def key (direction : ℝ) (o : LimitOrder) : Lex (ℝ × Quantity) :=
  toLex (direction * orderPrice o, orderQuantity o)

def sellKeyTuple (m : MarketTuple) : Tuple (Lex (ℝ × Quantity)) :=
  ⟨(sellOrders m).1, fun i => key 1 ((sellOrders m).2 i)⟩

def buyKeyTuple (m : MarketTuple) : Tuple (Lex (ℝ × Quantity)) :=
  ⟨(buyOrders m).1, fun i => key (-1) ((buyOrders m).2 i)⟩

def sellPermutation (m : MarketTuple) : FinitePermutation (sellOrders m).1 :=
  minimumSortPermutation (sellKeyTuple m)

def buyPermutation (m : MarketTuple) : FinitePermutation (buyOrders m).1 :=
  minimumSortPermutation (buyKeyTuple m)

def sellPrice (m : MarketTuple) (i : Fin (sellOrders m).1) : ℝ :=
  orderPrice ((sellOrders m).2 (sellPermutation m i))

def buyPrice (m : MarketTuple) (i : Fin (buyOrders m).1) : ℝ :=
  orderPrice ((buyOrders m).2 (buyPermutation m i))

def sellVolume (m : MarketTuple) (i : Fin (sellOrders m).1) : Quantity :=
  orderQuantity ((sellOrders m).2 (sellPermutation m i))

def buyVolume (m : MarketTuple) (i : Fin (buyOrders m).1) : Quantity :=
  orderQuantity ((buyOrders m).2 (buyPermutation m i))

theorem sellKey_monotone (m : MarketTuple) :
    Monotone (fun i => key 1 ((sellOrders m).2 (sellPermutation m i))) := by
  have h := minimumSort_isSorted (sellKeyTuple m)
  rw [minimumSort_eq_permute_minimumSortPermutation, isSorted_iff_monotone] at h
  exact h

theorem buyKey_monotone (m : MarketTuple) :
    Monotone (fun i => key (-1) ((buyOrders m).2 (buyPermutation m i))) := by
  have h := minimumSort_isSorted (buyKeyTuple m)
  rw [minimumSort_eq_permute_minimumSortPermutation, isSorted_iff_monotone] at h
  exact h

theorem sellPrice_monotone (m : MarketTuple) : Monotone (sellPrice m) := by
  intro i j hij
  have h := (Prod.Lex.toLex_le_toLex'.mp (sellKey_monotone m hij)).1
  simpa only [key, one_mul] using h

theorem buyPrice_antitone (m : MarketTuple) : Antitone (buyPrice m) := by
  intro i j hij
  have h := (Prod.Lex.toLex_le_toLex'.mp (buyKey_monotone m hij)).1
  simpa only [key, neg_one_mul, neg_le_neg_iff] using h

theorem sell_tie_volume (m : MarketTuple) {i j : Fin (sellOrders m).1} (hij : i ≤ j)
    (hprice : sellPrice m i = sellPrice m j) : sellVolume m i ≤ sellVolume m j := by
  have h := (Prod.Lex.toLex_le_toLex'.mp (sellKey_monotone m hij)).2
  exact h (by simpa only [key, one_mul] using hprice)

theorem buy_tie_volume (m : MarketTuple) {i j : Fin (buyOrders m).1} (hij : i ≤ j)
    (hprice : buyPrice m i = buyPrice m j) : buyVolume m i ≤ buyVolume m j := by
  have h := (Prod.Lex.toLex_le_toLex'.mp (buyKey_monotone m hij)).2
  apply h
  simpa only [key, neg_one_mul, neg_inj] using hprice

def priceBounded (lo hi : ℝ) (m : MarketTuple) : Prop :=
  ∀ i, orderPrice (m.2 i).2 ∈ Icc lo hi

theorem sellPrice_bounds {lo hi : ℝ} (m : MarketTuple) (hm : priceBounded lo hi m)
    (i : Fin (sellOrders m).1) : sellPrice m i ∈ Icc lo hi := by
  change orderPrice ((Foundations.MarketClearing.Selection.separationComponent
    OrderSide.sell m).2 (sellPermutation m i)) ∈ Icc lo hi
  rw [separation_entry]
  exact hm _

theorem buyPrice_bounds {lo hi : ℝ} (m : MarketTuple) (hm : priceBounded lo hi m)
    (i : Fin (buyOrders m).1) : buyPrice m i ∈ Icc lo hi := by
  change orderPrice ((Foundations.MarketClearing.Selection.separationComponent
    OrderSide.buy m).2 (buyPermutation m i)) ∈ Icc lo hi
  rw [separation_entry]
  exact hm _

theorem prepend_monotone {n : ℕ} (p : Fin n → ℝ) (hp : Monotone p) (lo : ℝ)
    (hlo : ∀ i, lo ≤ p i) : Monotone (Fin.cases lo p) := by
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · intro j hij
    refine Fin.cases le_rfl (fun l => hlo l) j
  · intro j hij
    revert hij
    refine Fin.cases ?_ (fun l h => hp (Fin.succ_le_succ_iff.mp h)) j
    intro h
    change k.val + 1 ≤ 0 at h
    omega

theorem prepend_antitone {n : ℕ} (p : Fin n → ℝ) (hp : Antitone p) (hi : ℝ)
    (hhi : ∀ i, p i ≤ hi) : Antitone (Fin.cases hi p) := by
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · intro j hij
    refine Fin.cases le_rfl (fun l => hhi l) j
  · intro j hij
    revert hij
    refine Fin.cases ?_ (fun l h => hp (Fin.succ_le_succ_iff.mp h)) j
    intro h
    change k.val + 1 ≤ 0 at h
    omega

/-- Original label: `defn:supply-and-demand-curves`.
This connects the literal separated tagged orders, with the current tie sort,
to the Book used by the completed-graph and equilibrium constructions. -/
def book (lo hi : ℝ) (hlohi : lo ≤ hi) (m : MarketTuple) (hm : priceBounded lo hi m) :
    ExcessSupply.Book lo hi where
  sellCount := (sellOrders m).1
  buyCount := (buyOrders m).1
  sellPrice := Fin.cases lo (sellPrice m)
  buyPrice := Fin.cases hi (buyPrice m)
  sellVolume := fun i => sellVolume m i
  buyVolume := fun i => buyVolume m i
  sellVolume_nonneg := fun i => (sellVolume m i).property
  buyVolume_nonneg := fun i => (buyVolume m i).property
  sellPrice_zero := rfl
  buyPrice_zero := rfl
  sellPrice_monotone := prepend_monotone _ (sellPrice_monotone m) lo
    (fun i => (sellPrice_bounds m hm i).1)
  buyPrice_antitone := prepend_antitone _ (buyPrice_antitone m) hi
    (fun i => (buyPrice_bounds m hm i).2)
  sellPrice_bounds := Fin.cases ⟨le_rfl, hlohi⟩ (sellPrice_bounds m hm)
  buyPrice_bounds := Fin.cases ⟨hlohi, le_rfl⟩ (buyPrice_bounds m hm)

def impactCurve (lo hi : ℝ) (hlohi : lo ≤ hi) (m : MarketTuple) (hm : priceBounded lo hi m) :
    PiecewiseAffinePriceCurves.Curve :=
  InterpolatedImpactCurve.Book.impactCurve (book lo hi hlohi m hm)

def equilibriumOperator (lo hi : ℝ) (hlohi : lo ≤ hi) (m : MarketTuple)
    (hm : priceBounded lo hi m) : ℝ × {q : ℝ // 0 ≤ q} :=
  EquilibriumQuantity.Book.equilibriumOperator (book lo hi hlohi m hm)

end Thesis.DayAhead.InterpolatedMarket
