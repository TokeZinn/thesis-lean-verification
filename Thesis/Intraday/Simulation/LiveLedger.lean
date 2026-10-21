import Thesis.Intraday.LOBsAndTuples.Replay
import Thesis.Intraday.Simulation.Conservation
import Mathlib.Tactic

/-! # Finite lifecycle ledger for typed intraday replay

The simulator appendix keeps a historical local key separately from each fresh
simulated identifier. Local keys must already be qualified by the configured
sampled-window namespace; raw feed identifiers alone are not globally unique.
The ledger retains insertion order, and a reduction updates its existing slot.
Its order payload is the actual bounded-price, positive-quantity `Order`.
-/

noncomputable section
namespace Thesis.Intraday.LiveLedger

open Clearing

structure Entry where
  localKey : ℕ
  liveId : ℕ
  isBuy : Bool
  order : Order

structure Ledger where
  nextId : ℕ
  live : List Entry

def Valid (s : Ledger) : Prop :=
  s.live.Pairwise (fun a b => a.localKey ≠ b.localKey) ∧
  s.live.Pairwise (fun a b => a.liveId ≠ b.liveId) ∧
  ∀ a ∈ s.live, a.liveId < s.nextId

def empty : Ledger := ⟨0, []⟩

theorem empty_valid : Valid empty := by simp [Valid, empty]

def lookup (s : Ledger) (key : ℕ) : Option Entry :=
  s.live.find? (fun a => a.localKey == key)

theorem lookup_some_mem {s : Ledger} {key : ℕ} {a : Entry} (h : lookup s key = some a) :
    a ∈ s.live := List.mem_of_find?_eq_some h

theorem lookup_some_key {s : Ledger} {key : ℕ} {a : Entry} (h : lookup s key = some a) :
    a.localKey = key := by simpa using List.find?_some h

theorem lookup_none_iff (s : Ledger) (key : ℕ) :
    lookup s key = none ↔ ∀ a ∈ s.live, a.localKey ≠ key := by
  simp [lookup, List.find?_eq_none]

def appendFresh (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) : Ledger :=
  ⟨s.nextId + 1, s.live ++ [⟨key, s.nextId, buy, o⟩]⟩

theorem fresh_not_live {s : Ledger} (h : Valid s) : ∀ a ∈ s.live, a.liveId ≠ s.nextId :=
  fun a ha => ne_of_lt (h.2.2 a ha)

theorem appendFresh_valid {s : Ledger} (h : Valid s) {key : ℕ}
    (hk : lookup s key = none) (buy : Bool) (o : Order) : Valid (appendFresh s key buy o) := by
  have hkey := (lookup_none_iff s key).mp hk
  refine ⟨?_, ?_, ?_⟩
  · simpa [appendFresh, List.pairwise_append] using And.intro h.1 hkey
  · simpa [appendFresh, List.pairwise_append] using And.intro h.2.1 (fresh_not_live h)
  · intro a ha
    rcases List.mem_append.mp ha with hold | hnew
    · exact (h.2.2 a hold).trans (Nat.lt_succ_self _)
    · simp only [List.mem_singleton] at hnew
      subst a
      exact Nat.lt_succ_self _

def eraseId (s : Ledger) (id : ℕ) : Ledger :=
  { s with live := s.live.filter (fun a => a.liveId != id) }

theorem eraseId_valid {s : Ledger} (h : Valid s) (id : ℕ) : Valid (eraseId s id) := by
  refine ⟨h.1.sublist (List.filter_sublist), h.2.1.sublist (List.filter_sublist), ?_⟩
  intro a ha
  exact h.2.2 a (List.mem_of_mem_filter ha)

theorem eraseId_absent (s : Ledger) (id : ℕ) :
    ∀ a ∈ (eraseId s id).live, a.liveId ≠ id := by
  intro a ha
  simpa using (List.mem_filter.mp ha).2

theorem unique_of_pairwise {α β : Type*} (f : α → β) {l : List α}
    (h : l.Pairwise (fun a b => f a ≠ f b)) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (he : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons c cs ih =>
    obtain ⟨hc, hcs⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | hatail
    · rcases List.mem_cons.mp hb with rfl | hbtail
      · rfl
      · exact False.elim (hc b hbtail he)
    · rcases List.mem_cons.mp hb with rfl | hbtail
      · exact False.elim (hc a hatail he.symm)
      · exact ih hcs hatail hbtail

theorem erase_lookup_absent {s : Ledger} (h : Valid s) {key : ℕ} {a : Entry}
    (ha : lookup s key = some a) : lookup (eraseId s a.liveId) key = none := by
  apply (lookup_none_iff _ _).mpr
  intro b hb he
  have hm := (List.mem_filter.mp hb).1
  have heq := unique_of_pairwise Entry.localKey h.1 hm (lookup_some_mem ha)
    (he.trans (lookup_some_key ha).symm)
  subst b
  exact eraseId_absent s a.liveId a hb rfl

def resized (id : ℕ) (q : PositiveQuantity) (a : Entry) : Entry :=
  if a.liveId = id then { a with order := withQuantity a.order q.val } else a

@[simp] theorem resized_key (id : ℕ) (q : PositiveQuantity) (a : Entry) :
    (resized id q a).localKey = a.localKey := by unfold resized; split_ifs <;> rfl

@[simp] theorem resized_id (id : ℕ) (q : PositiveQuantity) (a : Entry) :
    (resized id q a).liveId = a.liveId := by unfold resized; split_ifs <;> rfl

@[simp] theorem resized_side (id : ℕ) (q : PositiveQuantity) (a : Entry) :
    (resized id q a).isBuy = a.isBuy := by unfold resized; split_ifs <;> rfl

@[simp] theorem resized_price (id : ℕ) (q : PositiveQuantity) (a : Entry) :
    price (resized id q a).order = price a.order := by unfold resized; split_ifs <;> rfl

@[simp] theorem resized_time (id : ℕ) (q : PositiveQuantity) (a : Entry) :
    time (resized id q a).order = time a.order := by unfold resized; split_ifs <;> rfl

theorem resized_quantity (q : PositiveQuantity) (a : Entry) :
    quantity (resized a.liveId q a).order = q.val := by
  simp [resized, withQuantity_quantity a.order q.property]

def resizeId (s : Ledger) (id : ℕ) (q : PositiveQuantity) : Ledger :=
  { s with live := s.live.map (resized id q) }

theorem resizeId_valid {s : Ledger} (h : Valid s) (id : ℕ) (q : PositiveQuantity) :
    Valid (resizeId s id q) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [resizeId, List.pairwise_map] using h.1
  · simpa [resizeId, List.pairwise_map] using h.2.1
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    simpa [resizeId] using h.2.2 b hb

theorem resizeId_length (s : Ledger) (id : ℕ) (q : PositiveQuantity) :
    (resizeId s id q).live.length = s.live.length := by simp [resizeId]

theorem resizeId_keys (s : Ledger) (id : ℕ) (q : PositiveQuantity) :
    ((resizeId s id q).live.map Entry.localKey) = s.live.map Entry.localKey := by
  simp [resizeId, List.map_map, Function.comp_def]

theorem resizeId_ids (s : Ledger) (id : ℕ) (q : PositiveQuantity) :
    ((resizeId s id q).live.map Entry.liveId) = s.live.map Entry.liveId := by
  simp [resizeId, List.map_map, Function.comp_def]

/-- Forget lifecycle metadata only at the explicit book projection. -/
def market (s : Ledger) : Market :=
  ⟨s.live.length, fun i => ⟨s.live[i].isBuy, s.live[i].order⟩⟩

def sortedMarket (s : Ledger) : Market := MarketSorting.sortMarket (market s)

theorem sortedMarket_sorted (s : Ledger) : SortedMarket (sortedMarket s) :=
  MarketSorting.sortMarket_sorted _

def visibleMarket (depth : ℕ) (s : Ledger) : Market := Visibility.visible depth (sortedMarket s)

theorem visibleMarket_sorted (depth : ℕ) (s : Ledger) : SortedMarket (visibleMarket depth s) :=
  Visibility.visible_sorted depth (sortedMarket_sorted s)

end Thesis.Intraday.LiveLedger
