import Thesis.Intraday.LOBsAndTuples.Orders
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Literal single-stage intraday execution on finite books

Tuples retain the manuscript's finite indexed representation. The Borel
structure below is identified explicitly with the indexed Hausdorff Borel
structure. Quantity updates preserve price and time, and use positive residuals.
-/

noncomputable section

namespace Thesis.Intraday.Execution

open Set Foundations.MarketRepresentation
open Foundations.MarketRepresentation.DisjointUnionTopology
open Foundations.MarketRepresentation.TuplesMetricTopology

local instance sigmaBorel {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] : BorelSpace (Sigma X) := by
  constructor
  rw [borel_sigma_eq]
  congr 1
  funext i
  exact (@BorelSpace.measurable_eq (X i) _ _ _)

abbrev Book := Tuple Order
abbrev State := Book × Book

/-- The measurable structure used below is exactly the manuscript's one. -/
theorem book_borel_eq : tupleHausdorffBorel (X := Order) =
    (inferInstance : MeasurableSpace Book) := by
  rw [tupleHausdorffBorel_eq_tupleSupBorel, tupleSupBorel_eq_sigma]
  congr 1
  funext n
  exact (@BorelSpace.measurable_eq (Fin n → Order) _ _ _).symm

theorem measurable_tuple_prod {Y Z : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Z] {f : Book × Y → Z}
    (h : ∀ n, Measurable (fun x : (Fin n → Order) × Y => f (⟨n, x.1⟩, x.2))) :
    Measurable f := by
  have hm : Measurable (fun x : Σ n, (Fin n → Order) × Y => f (⟨x.1, x.2.1⟩, x.2.2)) :=
    measurable_pasting_iff.mpr h
  exact hm.comp (Homeomorph.sigmaProdDistrib (X := fun n => Fin n → Order)
    (Y := Y)).continuous.measurable

theorem measurable_state {Z : Type*} [MeasurableSpace Z] {f : State → Z}
    (h : ∀ n m, Measurable (fun x : (Fin n → Order) × (Fin m → Order) =>
      f (⟨n, x.1⟩, ⟨m, x.2⟩))) : Measurable f := by
  apply measurable_tuple_prod
  intro n
  have hm : Measurable (fun x : Book × (Fin n → Order) => f (⟨n, x.2⟩, x.1)) := by
    apply measurable_tuple_prod
    intro m
    exact (h n m).comp measurable_swap
  exact hm.comp measurable_swap

/-- Original label: `defn:best-price-and-tradeprice`. -/
def best (emptyPrice : ℝ) : Book → ℝ
  | ⟨0, _⟩ => emptyPrice
  | ⟨_ + 1, x⟩ => price (x 0)

theorem continuous_best (emptyPrice : ℝ) : Continuous (best emptyPrice) := by
  apply continuous_sigma
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_price.comp (continuous_apply 0)

/-- `defn:best-price-and-tradeprice`: execution is priced at the opposite,
resting side's best quote. This is used only on crossing, nonempty pairs. -/
def tradeprice (incomingBuy : Bool) (x : State) : ℝ :=
  if incomingBuy then best 10000 x.2 else best (-10000) x.1

theorem continuous_tradeprice (incomingBuy : Bool) : Continuous (tradeprice incomingBuy) := by
  cases incomingBuy
  · exact (continuous_best (-10000)).comp continuous_fst
  · exact (continuous_best 10000).comp continuous_snd

/-- The crossing condition of a book pair: best bid at or above best ask. Its closedness
is the proposition `crossing_closed` below. The same closed condition works even before
restriction to sorted books. -/
def Crossing (x : State) : Prop := best (-10000) x.1 ≥ best 10000 x.2

/-- Original label: `prop:crossing-set-closed`.
The crossing set is closed: it is the preimage of the closed half-plane `{(a, b) | b ≤ a}`
under the continuous pair of best quotes. -/
theorem crossing_closed : IsClosed {x : State | Crossing x} :=
  isClosed_le ((continuous_best 10000).comp continuous_snd)
    ((continuous_best (-10000)).comp continuous_fst)

theorem crossing_nonempty {x : State} (h : Crossing x) : 0 < x.1.1 ∧ 0 < x.2.1 := by
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero =>
    cases m with
    | zero => norm_num [Crossing, best] at h
    | succ m =>
      have hp := (price_bounds (s 0)).1
      simp only [Crossing, best] at h
      linarith
  | succ n =>
    cases m with
    | zero =>
      have hp := (price_bounds (b 0)).2
      simp only [Crossing, best] at h
      linarith
    | succ m => exact ⟨Nat.succ_pos _, Nat.succ_pos _⟩

def tail {n : ℕ} (x : Fin (n + 1) → Order) : Book := ⟨n, fun i => x i.succ⟩
def changeHead {n : ℕ} (x : Fin (n + 1) → Order) (q : ℝ) : Book :=
  ⟨n + 1, Function.update x 0 (withQuantity (x 0) q)⟩

theorem measurable_tail (n : ℕ) : Measurable (@tail n) := by
  apply continuous_sigmaMk.measurable.comp
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)

theorem measurable_changeHead (n : ℕ) :
    Measurable (fun x : (Fin (n + 1) → Order) × ℝ => changeHead x.1 x.2) := by
  unfold changeHead
  apply continuous_sigmaMk.measurable.comp
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = 0
  · subst i
    have hm : Measurable (fun x : (Fin (n + 1) → Order) × ℝ => (x.1 0, x.2)) :=
      ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
    simpa only [Function.update_self] using measurable_withQuantity.comp hm
  · simpa only [Function.update_of_ne hi] using
      ((measurable_pi_apply i).comp measurable_fst :
        Measurable (fun x : (Fin (n + 1) → Order) × ℝ => x.1 i))

/-- Original label: `defn:single-stage-clearing-map`.
All four displayed branches are implemented, including exact-volume removal. -/
def step : State → State
  | (⟨0, b⟩, s) => (⟨0, b⟩, s)
  | (⟨n + 1, b⟩, ⟨0, s⟩) => (⟨n + 1, b⟩, ⟨0, s⟩)
  | (⟨n + 1, b⟩, ⟨m + 1, s⟩) =>
    if price (b 0) < price (s 0) then (⟨n + 1, b⟩, ⟨m + 1, s⟩)
    else if quantity (b 0) < quantity (s 0) then
      (tail b, changeHead s (quantity (s 0) - quantity (b 0)))
    else if quantity (s 0) < quantity (b 0) then
      (changeHead b (quantity (b 0) - quantity (s 0)), tail s)
    else (tail b, tail s)

/-- Original label: `prop:single-stage-execution`. -/
theorem measurable_step : Measurable step := by
  apply measurable_state
  intro n m
  cases n with
  | zero =>
    exact (continuous_sigmaMk.measurable.comp measurable_fst).prodMk
      (continuous_sigmaMk.measurable.comp measurable_snd)
  | succ n =>
    cases m with
    | zero =>
      exact (continuous_sigmaMk.measurable.comp measurable_fst).prodMk
        (continuous_sigmaMk.measurable.comp measurable_snd)
    | succ m =>
      have hb : Measurable (fun x : (Fin (n + 1) → Order) × (Fin (m + 1) → Order) => x.1 0) :=
        (measurable_pi_apply 0).comp measurable_fst
      have hs : Measurable (fun x : (Fin (n + 1) → Order) × (Fin (m + 1) → Order) => x.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have hqb := continuous_quantity.measurable.comp hb
      have hqs := continuous_quantity.measurable.comp hs
      apply Measurable.ite
      · exact measurableSet_lt (continuous_price.measurable.comp hb)
          (continuous_price.measurable.comp hs)
      · exact (continuous_sigmaMk.measurable.comp measurable_fst).prodMk
          (continuous_sigmaMk.measurable.comp measurable_snd)
      · apply Measurable.ite (measurableSet_lt hqb hqs)
        · exact ((measurable_tail n).comp measurable_fst).prodMk
            ((measurable_changeHead m).comp (measurable_snd.prodMk (hqs.sub hqb)))
        · apply Measurable.ite (measurableSet_lt hqs hqb)
          · exact ((measurable_changeHead n).comp (measurable_fst.prodMk (hqb.sub hqs))).prodMk
              ((measurable_tail m).comp measurable_snd)
          · exact ((measurable_tail n).comp measurable_fst).prodMk
              ((measurable_tail m).comp measurable_snd)

/-- Original label: `defn:iterated-single-stage-clearing`. -/
def iterateStep (n : ℕ) : State → State := step^[n]

/-- Original label: `cor:iterated-single-stage-measurable`. -/
theorem measurable_step_iterate (n : ℕ) : Measurable step^[n] := measurable_step.iterate n

/-- Price-time key; buys prefer high prices and sells prefer low prices. -/
def priorityKey (buy : Bool) (x : Order) : ℝ ×ₗ ℝ :=
  toLex (if buy then -price x else price x, time x)

/-- Equal price and time do not impose an artificial quantity tie-breaker. -/
@[implicit_reducible] def priceTimeOrder (buy : Bool) : PartialOrder Order where
  le x y := x = y ∨ priorityKey buy x < priorityKey buy y
  le_refl _ := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    exact Or.inr (lt_trans hxy hyz)
  le_antisymm x y hxy hyx := by
    rcases hxy with hxy | hxy
    · exact hxy
    rcases hyx with hyx | hyx
    · exact hyx.symm
    exact (lt_asymm hxy hyx).elim

theorem priority_lt_iff (buy : Bool) (x y : Order) :
    @LT.lt Order (priceTimeOrder buy).toLT x y ↔ priorityKey buy x < priorityKey buy y := by
  change ((x = y ∨ priorityKey buy x < priorityKey buy y) ∧
    ¬(y = x ∨ priorityKey buy y < priorityKey buy x)) ↔ _
  constructor
  · rintro ⟨rfl | h, hn⟩
    · exact (hn (Or.inl rfl)).elim
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rintro (rfl | h')
    · exact (lt_irrefl _ h)
    · exact lt_asymm h h'

def Sorted (buy : Bool) (x : Book) : Prop := Monotone (fun i => priorityKey buy (x.2 i))

/-- The key-based condition is exactly the thesis's partial-order sortedness. -/
theorem sorted_iff_isSorted (buy : Bool) (x : Book) :
    Sorted buy x ↔ @TuplesBasic.IsSorted Order (priceTimeOrder buy).toPreorder x := by
  simp only [Sorted, Monotone, TuplesBasic.IsSorted, Tuple.entry, priority_lt_iff, not_lt]
  constructor
  · intro h i j hij; exact h hij
  · intro h i j hij; exact h i j hij

theorem sorted_tail {n : ℕ} (buy : Bool) (x : Fin (n + 1) → Order)
    (h : Sorted buy ⟨n + 1, x⟩) : Sorted buy (tail x) := by
  intro i j hij
  exact h (Fin.succ_le_succ_iff.mpr hij)

@[simp] theorem priorityKey_withQuantity (buy : Bool) (x : Order) (q : ℝ) :
    priorityKey buy (withQuantity x q) = priorityKey buy x := rfl

theorem sorted_changeHead {n : ℕ} (buy : Bool) (x : Fin (n + 1) → Order) (q : ℝ)
    (h : Sorted buy ⟨n + 1, x⟩) : Sorted buy (changeHead x q) := by
  have heq (i : Fin (n + 1)) :
      priorityKey buy ((changeHead x q).2 i) = priorityKey buy (x i) := by
    by_cases hi : i = 0
    · subst i; simp [changeHead]
    · simp [changeHead, Function.update_of_ne hi]
  intro i j hij
  change priorityKey buy ((changeHead x q).2 i) ≤ priorityKey buy ((changeHead x q).2 j)
  rw [heq i, heq j]
  exact h hij

def SortedState (x : State) : Prop := Sorted true x.1 ∧ Sorted false x.2

/-- Original label: `prop:single-stage-execution`.
The literal update maps the sorted-side domain into itself. -/
theorem step_sorted {x : State} (h : SortedState x) : SortedState (step x) := by
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero => exact h
  | succ n =>
    cases m with
    | zero => exact h
    | succ m =>
      simp only [step]
      split
      · exact h
      · split
        · exact ⟨sorted_tail _ _ h.1, sorted_changeHead _ _ _ h.2⟩
        · split
          · exact ⟨sorted_changeHead _ _ _ h.1, sorted_tail _ _ h.2⟩
          · exact ⟨sorted_tail _ _ h.1, sorted_tail _ _ h.2⟩

theorem iterate_sorted (n : ℕ) {x : State} (h : SortedState x) :
    SortedState (step^[n] x) := by
  induction n generalizing x with
  | zero => exact h
  | succ n ih => exact ih (step_sorted h)

/-- Original label: `prop:single-stage-execution`.
The exact map with the exact sorted subtype, not an assumed-measurable update. -/
def sortedStep (x : {x : State // SortedState x}) : {x : State // SortedState x} :=
  ⟨step x, step_sorted x.property⟩

theorem measurable_sortedStep : Measurable sortedStep :=
  (measurable_step.comp measurable_subtype_coe).subtype_mk

def orderCount (x : State) : ℕ := x.1.1 + x.2.1

theorem step_of_not_crossing {x : State} (h : ¬Crossing x) : step x = x := by
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero => rfl
  | succ n =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [Crossing, best, not_le] at h
      simp only [step, if_pos h]

theorem iterate_of_not_crossing {x : State} (h : ¬Crossing x) (n : ℕ) : step^[n] x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, step_of_not_crossing h] using ih

theorem step_count_lt {x : State} (h : Crossing x) : orderCount (step x) < orderCount x := by
  have hn := crossing_nonempty h
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn.1).elim
  | succ n =>
    cases m with
    | zero => exact (Nat.not_lt_zero _ hn.2).elim
    | succ m =>
      have hp : ¬price (b 0) < price (s 0) := not_lt.mpr h
      simp only [step, if_neg hp]
      split
      · simp only [orderCount, tail, changeHead]; omega
      · split <;> simp only [orderCount, tail, changeHead] <;> omega

theorem iterate_not_crossing_of_count_le (n : ℕ) (x : State) (h : orderCount x ≤ n + 1) :
    ¬Crossing (step^[n] x) := by
  induction n generalizing x with
  | zero =>
    intro hc
    change Crossing x at hc
    have hn := crossing_nonempty hc
    change x.1.1 + x.2.1 ≤ 1 at h
    omega
  | succ n ih =>
    by_cases hc : Crossing x
    · have hd := step_count_lt hc
      exact ih (step x) (by omega)
    · simpa only [iterate_of_not_crossing hc] using hc

/-- The current manuscript's finite stopping count, with natural subtraction. -/
def clearSides (x : State) : State := step^[orderCount x - 1] x

theorem clearSides_not_crossing (x : State) : ¬Crossing (clearSides x) :=
  iterate_not_crossing_of_count_le _ _ (by omega)

theorem clearSides_sorted {x : State} (h : SortedState x) : SortedState (clearSides x) :=
  iterate_sorted _ h

theorem measurable_clearSides : Measurable clearSides := by
  apply measurable_state
  intro n m
  exact (measurable_step_iterate (n + m - 1)).comp
    ((continuous_sigmaMk.measurable.comp measurable_fst).prodMk
      (continuous_sigmaMk.measurable.comp measurable_snd))

/-- Clearing changes quantities and removes orders, preserving surviving
price-time keys. This is the invariant needed when appending latent tails. -/
def KeySubset (buy : Bool) (after before : Book) : Prop :=
  ∀ i, ∃ j, priorityKey buy (after.2 i) = priorityKey buy (before.2 j)

theorem KeySubset.refl (buy : Bool) (b : Book) : KeySubset buy b b := fun i => ⟨i, rfl⟩

theorem KeySubset.trans {buy : Bool} {a b c : Book}
    (hab : KeySubset buy a b) (hbc : KeySubset buy b c) : KeySubset buy a c := by
  intro i
  obtain ⟨j, hj⟩ := hab i
  obtain ⟨k, hk⟩ := hbc j
  exact ⟨k, hj.trans hk⟩

theorem tail_keySubset {n : ℕ} (buy : Bool) (b : Fin (n + 1) → Order) :
    KeySubset buy (tail b) ⟨n + 1, b⟩ := fun i => ⟨i.succ, rfl⟩

theorem changeHead_keySubset {n : ℕ} (buy : Bool) (b : Fin (n + 1) → Order) (q : ℝ) :
    KeySubset buy (changeHead b q) ⟨n + 1, b⟩ := by
  intro (i : Fin (n + 1))
  refine ⟨i, ?_⟩
  by_cases hi : i = 0
  · subst i; simp [changeHead, priorityKey]
  · simp [changeHead, Function.update_of_ne hi]

theorem step_keySubset (x : State) :
    KeySubset true (step x).1 x.1 ∧ KeySubset false (step x).2 x.2 := by
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero => exact ⟨KeySubset.refl _ _, KeySubset.refl _ _⟩
  | succ n =>
    cases m with
    | zero => exact ⟨KeySubset.refl _ _, KeySubset.refl _ _⟩
    | succ m =>
      simp only [step]
      split
      · exact ⟨KeySubset.refl _ _, KeySubset.refl _ _⟩
      · split
        · exact ⟨tail_keySubset _ _, changeHead_keySubset _ _ _⟩
        · split
          · exact ⟨changeHead_keySubset _ _ _, tail_keySubset _ _⟩
          · exact ⟨tail_keySubset _ _, tail_keySubset _ _⟩

theorem iterate_keySubset (n : ℕ) (x : State) :
    KeySubset true (step^[n] x).1 x.1 ∧ KeySubset false (step^[n] x).2 x.2 := by
  induction n generalizing x with
  | zero => exact ⟨KeySubset.refl _ _, KeySubset.refl _ _⟩
  | succ n ih =>
    exact ⟨((ih (step x)).1).trans (step_keySubset x).1,
      ((ih (step x)).2).trans (step_keySubset x).2⟩

end Thesis.Intraday.Execution
