import Thesis.Intraday.LOBsAndTuples.Clearing
import Thesis.Foundations.MarketActions.Identifiers

/-! # Identifier-preserving single-stage and iterated clearing

Current `defn:identifier-clearing-operator` and
`prop:identifier-clearing-properties`. The source's undefined/weak tie formula
is not adopted. `correctedPriority` uses the cited foundation proposition's
equality-or-strict-lexicographic relation. Natural identifiers carry their
discrete Borel structure; the source's 0/1 identifier metric has the same
discrete topology as the native natural-number metric.
-/

noncomputable section
namespace Thesis.Intraday.IdentifierClearing
open Set Foundations.MarketRepresentation
open Foundations.MarketRepresentation.TuplesBasic
open Foundations.MarketRepresentation.TuplesMetricTopology
open Foundations.MarketRepresentation.DisjointUnionTopology
open Foundations.MarketActions.Identifiers

attribute [local instance] Execution.sigmaBorel

abbrev IdentifiedOrder := Order × ℕ
local instance : BorelSpace IdentifiedOrder := inferInstanceAs (BorelSpace (Order × ℕ))
local instance : SecondCountableTopology IdentifiedOrder :=
  inferInstanceAs (SecondCountableTopology (Order × ℕ))
local instance (n : ℕ) : BorelSpace (Fin n → IdentifiedOrder) := inferInstance
local instance (n : ℕ) : SecondCountableTopology (Fin n → IdentifiedOrder) := inferInstance
abbrev Book := Tuple IdentifiedOrder
abbrev State := Book × Book

local instance : BorelSpace Book := by
  constructor
  rw [borel_sigma_eq]
  congr 1
  funext n
  exact (@BorelSpace.measurable_eq (Fin n → IdentifiedOrder) _ _ _)

@[implicit_reducible] def correctedPriority (buy : Bool) : PartialOrder IdentifiedOrder :=
  priorityOrder (Execution.priorityKey buy)

def erase (b : Book) : Execution.Book := Tuple.map Prod.fst b
def eraseState (x : State) : Execution.State := (erase x.1, erase x.2)

def withQuantity (o : IdentifiedOrder) (q : ℝ) : IdentifiedOrder :=
  (Thesis.Intraday.withQuantity o.1 q, o.2)

theorem measurable_withQuantity :
    Measurable (fun x : IdentifiedOrder × ℝ => withQuantity x.1 x.2) := by
  exact (Thesis.Intraday.measurable_withQuantity.comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst)

def tail {n : ℕ} (x : Fin (n + 1) → IdentifiedOrder) : Book := ⟨n, fun i => x i.succ⟩
def changeHead {n : ℕ} (x : Fin (n + 1) → IdentifiedOrder) (q : ℝ) : Book :=
  ⟨n + 1, Function.update x 0 (withQuantity (x 0) q)⟩

theorem measurable_tail (n : ℕ) : Measurable (@tail n) :=
  continuous_sigmaMk.measurable.comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.succ)

theorem measurable_changeHead (n : ℕ) :
    Measurable (fun x : (Fin (n + 1) → IdentifiedOrder) × ℝ => changeHead x.1 x.2) := by
  unfold changeHead
  apply continuous_sigmaMk.measurable.comp
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = 0
  · subst i
    have hm : Measurable (fun x : (Fin (n + 1) → IdentifiedOrder) × ℝ => (x.1 0, x.2)) :=
      ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
    simpa only [Function.update_self] using measurable_withQuantity.comp hm
  · simpa only [Function.update_of_ne hi] using
      ((measurable_pi_apply i).comp measurable_fst :
        Measurable (fun x : (Fin (n + 1) → IdentifiedOrder) × ℝ => x.1 i))

theorem measurable_book_prod {Y Z : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Z] {f : Book × Y → Z}
    (h : ∀ n, Measurable (fun x : (Fin n → IdentifiedOrder) × Y => f (⟨n, x.1⟩, x.2))) :
    Measurable f := by
  have hm : Measurable (fun x : Σ n, (Fin n → IdentifiedOrder) × Y =>
      f (⟨x.1, x.2.1⟩, x.2.2)) := measurable_pasting_iff.mpr h
  exact hm.comp (Homeomorph.sigmaProdDistrib (X := fun n => Fin n → IdentifiedOrder)
    (Y := Y)).continuous.measurable

theorem measurable_state {Z : Type*} [MeasurableSpace Z] {f : State → Z}
    (h : ∀ n m, Measurable (fun x : (Fin n → IdentifiedOrder) ×
      (Fin m → IdentifiedOrder) => f (⟨n, x.1⟩, ⟨m, x.2⟩))) : Measurable f := by
  apply measurable_book_prod
  intro n
  have hm : Measurable (fun x : Book × (Fin n → IdentifiedOrder) =>
      f (⟨n, x.2⟩, x.1)) := by
    apply measurable_book_prod
    intro m
    exact (h n m).comp measurable_swap
  exact hm.comp measurable_swap

def step : State → State
  | (⟨0, b⟩, s) => (⟨0, b⟩, s)
  | (⟨n + 1, b⟩, ⟨0, s⟩) => (⟨n + 1, b⟩, ⟨0, s⟩)
  | (⟨n + 1, b⟩, ⟨m + 1, s⟩) =>
    if price (b 0).1 < price (s 0).1 then (⟨n + 1, b⟩, ⟨m + 1, s⟩)
    else if quantity (b 0).1 < quantity (s 0).1 then
      (tail b, changeHead s (quantity (s 0).1 - quantity (b 0).1))
    else if quantity (s 0).1 < quantity (b 0).1 then
      (changeHead b (quantity (b 0).1 - quantity (s 0).1), tail s)
    else (tail b, tail s)

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
      have hb : Measurable (fun x : (Fin (n + 1) → IdentifiedOrder) ×
          (Fin (m + 1) → IdentifiedOrder) => (x.1 0).1) :=
        measurable_fst.comp ((measurable_pi_apply 0).comp measurable_fst)
      have hs : Measurable (fun x : (Fin (n + 1) → IdentifiedOrder) ×
          (Fin (m + 1) → IdentifiedOrder) => (x.2 0).1) :=
        measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
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

theorem erase_tail {n : ℕ} (x : Fin (n + 1) → IdentifiedOrder) :
    erase (tail x) = Execution.tail (fun i => (x i).1) := rfl

theorem erase_changeHead {n : ℕ} (x : Fin (n + 1) → IdentifiedOrder) (q : ℝ) :
    erase (changeHead x q) = Execution.changeHead (fun i => (x i).1) q := by
  dsimp only [erase, changeHead, Execution.changeHead, Tuple.map]
  apply congrArg (fun f : Fin (n + 1) → Order => (⟨n + 1, f⟩ : Execution.Book))
  funext i
  by_cases hi : i = 0
  · subst i
    simp [withQuantity]
  · simp [hi]

theorem erase_step (x : State) : eraseState (step x) = Execution.step (eraseState x) := by
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero => rfl
  | succ n =>
    cases m with
    | zero => rfl
    | succ m =>
      by_cases hp : price (b 0).1 < price (s 0).1
      · rw [step, if_pos hp]
        simp only [eraseState, erase, Tuple.map, Execution.step, hp, ↓reduceIte]
      · by_cases hq : quantity (b 0).1 < quantity (s 0).1
        · rw [step, if_neg hp, if_pos hq]
          have he := congrArg₂ Prod.mk (erase_tail b)
            (erase_changeHead s (quantity (s 0).1 - quantity (b 0).1))
          simpa only [hp, hq, ↓reduceIte, eraseState, erase, Tuple.map, Execution.step] using he
        · by_cases hqs : quantity (s 0).1 < quantity (b 0).1
          · rw [step, if_neg hp, if_neg hq, if_pos hqs]
            have he := congrArg₂ Prod.mk
              (erase_changeHead b (quantity (b 0).1 - quantity (s 0).1)) (erase_tail s)
            simpa only [hp, hq, hqs, ↓reduceIte, eraseState, erase, Tuple.map,
              Execution.step] using he
          · rw [step, if_neg hp, if_neg hq, if_neg hqs]
            have he := congrArg₂ Prod.mk (erase_tail b) (erase_tail s)
            simpa only [eraseState, erase, Tuple.map, Execution.step, hp, hq, hqs,
              ↓reduceIte] using he

theorem erase_iterate (n : ℕ) (x : State) :
    eraseState (step^[n] x) = Execution.step^[n] (eraseState x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, erase_step, Function.iterate_succ_apply]

/-- Original label: `defn:identifier-clearing-operator`.
Side-pair operator; `IdentifierMarket` supplies the full tagged-market merge. -/
def clearSides (x : State) : State := step^[x.1.1 + x.2.1 - 1] x

/-- Original label: `prop:identifier-clearing-properties`.
Side-pair erasure lemma used in the complete result in `IdentifierMarket`. -/
theorem erase_clearSides (x : State) :
    eraseState (clearSides x) = Execution.clearSides (eraseState x) :=
  erase_iterate _ _

theorem measurable_clearSides : Measurable clearSides := by
  apply measurable_state
  intro n m
  exact (measurable_step.iterate (n+m-1)).comp
    ((continuous_sigmaMk.measurable.comp measurable_fst).prodMk
      (continuous_sigmaMk.measurable.comp measurable_snd))

def identifiers (b : Book) : List ℕ := List.ofFn fun i => (b.2 i).2
def stateIdentifiers (x : State) : List ℕ := identifiers x.1 ++ identifiers x.2

theorem identifiers_tail {n : ℕ} (x : Fin (n + 1) → IdentifiedOrder) :
    (identifiers (tail x)).Sublist (identifiers (⟨n + 1, x⟩ : Book)) := by
  simpa only [identifiers, tail, List.ofFn_succ] using
    List.sublist_cons_self (l := List.ofFn (fun i : Fin n => (x i.succ).2)) (a := (x 0).2)

theorem identifiers_changeHead {n : ℕ} (x : Fin (n + 1) → IdentifiedOrder) (q : ℝ) :
    identifiers (changeHead x q) = identifiers (⟨n + 1, x⟩ : Book) := by
  unfold identifiers changeHead
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i; simp [withQuantity]
  · simp [hi]

theorem step_identifiers_sublist (x : State) :
    (stateIdentifiers (step x)).Sublist (stateIdentifiers x) := by
  rcases x with ⟨⟨n, b⟩, ⟨m, s⟩⟩
  cases n with
  | zero => exact List.Sublist.refl _
  | succ n =>
    cases m with
    | zero => exact List.Sublist.refl _
    | succ m =>
      simp only [step]
      split_ifs
      · exact List.Sublist.refl _
      · simpa only [stateIdentifiers, identifiers_changeHead] using
          (identifiers_tail b).append (List.Sublist.refl (identifiers (⟨m + 1, s⟩ : Book)))
      · simpa only [stateIdentifiers, identifiers_changeHead] using
          (List.Sublist.refl (identifiers (⟨n + 1, b⟩ : Book))).append (identifiers_tail s)
      · exact (identifiers_tail b).append (identifiers_tail s)

theorem iterate_identifiers_sublist (n : ℕ) (x : State) :
    (stateIdentifiers (step^[n] x)).Sublist (stateIdentifiers x) := by
  induction n generalizing x with
  | zero => exact List.Sublist.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (step x)).trans (step_identifiers_sublist x)

theorem clearSides_preserves_distinct_identifiers (x : State)
    (hx : (stateIdentifiers x).Nodup) : (stateIdentifiers (clearSides x)).Nodup :=
  hx.sublist (iterate_identifiers_sublist _ _)

def priorityKey (buy : Bool) (o : IdentifiedOrder) : (ℝ ×ₗ ℝ) ×ₗ ℕ :=
  toLex (Execution.priorityKey buy o.1, o.2)

def Sorted (buy : Bool) (b : Book) : Prop := Monotone fun i => priorityKey buy (b.2 i)

theorem sorted_iff_isSorted (buy : Bool) (b : Book) :
    Sorted buy b ↔ @IsSorted IdentifiedOrder (correctedPriority buy).toPreorder b := by
  simp only [Sorted, Monotone, IsSorted, Tuple.entry,
    priorityOrder_lt_iff, priorityKey, not_lt]
  constructor
  · intro h i j hij; exact h hij
  · intro h i j hij; exact h i j hij

theorem sorted_tail {n : ℕ} (buy : Bool) (x : Fin (n + 1) → IdentifiedOrder)
    (h : Sorted buy ⟨n + 1, x⟩) : Sorted buy (tail x) := by
  intro i j hij
  exact h (Fin.succ_le_succ_iff.mpr hij)

@[simp] theorem priorityKey_withQuantity (buy : Bool) (o : IdentifiedOrder) (q : ℝ) :
    priorityKey buy (withQuantity o q) = priorityKey buy o := rfl

theorem sorted_changeHead {n : ℕ} (buy : Bool) (x : Fin (n + 1) → IdentifiedOrder) (q : ℝ)
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

def sortedClearSides (x : {x : State // SortedState x}) : {x : State // SortedState x} :=
  ⟨clearSides x.val, iterate_sorted _ x.property⟩

theorem measurable_sortedClearSides : Measurable sortedClearSides :=
  (measurable_clearSides.comp measurable_subtype_coe).subtype_mk

end Thesis.Intraday.IdentifierClearing
