import Thesis.Intraday.Simulation.LiveLedger

/-! # Typed addition, cancellation and update resolution

Simulator appendix, Burst Translation, Replay, and Anchor Shift. Requests carry
already parsed/translated actual orders. A duplicate means an addition for an
active local lifecycle key. An inactive reappearance gets a fresh live ID.
Missing cancellations and changes are explicit no-ops. An in-place change is
allowed only for unchanged side/price and nonincreasing positive quantity;
all other positive changes emit removal followed by a fresh addition.
This file does not infer whether a raw venue update was participant-authorised.
-/

noncomputable section
namespace Thesis.Intraday.LifecycleResolver

open LiveLedger

inductive Status where
  | accepted | repaired | rejected | noop | duplicate | residual | shortfall
  deriving DecidableEq

inductive Event where
  | added (entry : Entry)
  | removed (liveId : ℕ)
  | resized (liveId : ℕ) (remaining : PositiveQuantity)

def applyEvent (s : Ledger) : Event → Ledger
  | .added a => ⟨max s.nextId (a.liveId + 1), s.live ++ [a]⟩
  | .removed id => eraseId s id
  | .resized id q => resizeId s id q

def replayEvents (s : Ledger) (events : List Event) : Ledger := events.foldl applyEvent s

theorem applyEvent_counter_monotone (s : Ledger) (e : Event) :
    s.nextId ≤ (applyEvent s e).nextId := by
  cases e with
  | added a => exact le_max_left _ _
  | removed id => exact le_rfl
  | resized id q => exact le_rfl

theorem replayEvents_counter_monotone (s : Ledger) (events : List Event) :
    s.nextId ≤ (replayEvents s events).nextId := by
  induction events generalizing s with
  | nil => exact le_rfl
  | cons e es ih => exact (applyEvent_counter_monotone s e).trans (ih _)

structure Result where
  after : Ledger
  events : List Event
  statuses : List Status

def unchanged (s : Ledger) (status : Status) : Result := ⟨s, [], [status]⟩

def addition (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) : Result :=
  match lookup s key with
  | some _ => unchanged s .duplicate
  | none => ⟨appendFresh s key buy o, [.added ⟨key, s.nextId, buy, o⟩], [.accepted]⟩

def cancellation (s : Ledger) (key : ℕ) : Result :=
  match lookup s key with
  | none => unchanged s .noop
  | some a => ⟨eraseId s a.liveId, [.removed a.liveId], [.accepted]⟩

def canReduce (a : Entry) (buy : Bool) (o : Order) : Prop :=
  buy = a.isBuy ∧ price o = price a.order ∧ quantity o ≤ quantity a.order

def change (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) : Result := by
  classical
  exact match lookup s key with
  | none => unchanged s .noop
  | some a =>
    if canReduce a buy o then
      ⟨resizeId s a.liveId ⟨quantity o, quantity_pos o⟩,
        [.resized a.liveId ⟨quantity o, quantity_pos o⟩], [.accepted]⟩
    else
      ⟨appendFresh (eraseId s a.liveId) key buy o,
        [.removed a.liveId, .added ⟨key, s.nextId, buy, o⟩], [.repaired]⟩

inductive Request where
  | add (localKey : ℕ) (isBuy : Bool) (order : Order)
  | cancel (localKey : ℕ)
  | change (localKey : ℕ) (isBuy : Bool) (order : Order)

def resolve (s : Ledger) : Request → Result
  | .add key buy o => addition s key buy o
  | .cancel key => cancellation s key
  | .change key buy o => change s key buy o

theorem addition_duplicate (s : Ledger) (key : ℕ) (buy : Bool) (o : Order)
    {a : Entry} (h : lookup s key = some a) : addition s key buy o = unchanged s .duplicate := by
  simp [addition, h]

theorem addition_fresh (s : Ledger) (key : ℕ) (buy : Bool) (o : Order)
    (h : lookup s key = none) : (addition s key buy o).after = appendFresh s key buy o := by
  simp [addition, h]

theorem cancellation_missing (s : Ledger) (key : ℕ) (h : lookup s key = none) :
    cancellation s key = unchanged s .noop := by simp [cancellation, h]

theorem change_missing (s : Ledger) (key : ℕ) (buy : Bool) (o : Order)
    (h : lookup s key = none) : change s key buy o = unchanged s .noop := by simp [change, h]

theorem addition_valid {s : Ledger} (hs : Valid s) (key : ℕ) (buy : Bool) (o : Order) :
    Valid (addition s key buy o).after := by
  unfold addition
  split
  · exact hs
  · exact appendFresh_valid hs ‹_› buy o

theorem cancellation_valid {s : Ledger} (hs : Valid s) (key : ℕ) :
    Valid (cancellation s key).after := by
  unfold cancellation
  split
  · exact hs
  · exact eraseId_valid hs _

theorem change_valid {s : Ledger} (hs : Valid s) (key : ℕ) (buy : Bool) (o : Order) :
    Valid (change s key buy o).after := by
  unfold change
  split
  · exact hs
  · rename_i a ha
    split
    · exact resizeId_valid hs _ _
    · exact appendFresh_valid (eraseId_valid hs a.liveId) (erase_lookup_absent hs ha) buy o

theorem resolve_valid {s : Ledger} (hs : Valid s) (r : Request) :
    Valid (resolve s r).after := by
  cases r with
  | add key buy o => exact addition_valid hs key buy o
  | cancel key => exact cancellation_valid hs key
  | change key buy o => exact change_valid hs key buy o

theorem addition_events (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) :
    replayEvents s (addition s key buy o).events = (addition s key buy o).after := by
  unfold addition
  split <;> simp [unchanged, replayEvents, applyEvent, appendFresh]

theorem cancellation_events (s : Ledger) (key : ℕ) :
    replayEvents s (cancellation s key).events = (cancellation s key).after := by
  unfold cancellation
  split <;> rfl

theorem change_events (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) :
    replayEvents s (change s key buy o).events = (change s key buy o).after := by
  unfold change
  split
  · rfl
  · split
    · rfl
    · simp [replayEvents, applyEvent, appendFresh, eraseId]

theorem resolve_events (s : Ledger) (r : Request) :
    replayEvents s (resolve s r).events = (resolve s r).after := by
  cases r with
  | add key buy o => exact addition_events s key buy o
  | cancel key => exact cancellation_events s key
  | change key buy o => exact change_events s key buy o

theorem change_replaces (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) {a : Entry}
    (ha : lookup s key = some a) (hc : ¬ canReduce a buy o) :
    (change s key buy o).events = [.removed a.liveId, .added ⟨key, s.nextId, buy, o⟩] ∧
      (change s key buy o).statuses = [.repaired] := by simp [change, ha, hc]

theorem change_preserves_slot (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) {a : Entry}
    (ha : lookup s key = some a) (hc : canReduce a buy o) :
    (change s key buy o).after.live.map Entry.liveId = s.live.map Entry.liveId ∧
      (change s key buy o).after.live.map Entry.localKey = s.live.map Entry.localKey := by
  simp only [change, ha, if_pos hc]
  exact ⟨resizeId_ids _ _ _, resizeId_keys _ _ _⟩

/-- Source subrecords are processed against the state left by their predecessor. -/
def resolveGroup : Ledger → List Request → Result
  | s, [] => ⟨s, [], []⟩
  | s, r :: rs =>
    let first := resolve s r
    let rest := resolveGroup first.after rs
    ⟨rest.after, first.events ++ rest.events, first.statuses ++ rest.statuses⟩

theorem resolveGroup_valid {s : Ledger} (hs : Valid s) (rs : List Request) :
    Valid (resolveGroup s rs).after := by
  induction rs generalizing s with
  | nil => exact hs
  | cons r rs ih => exact ih (resolve_valid hs r)

theorem resolveGroup_events (s : Ledger) (rs : List Request) :
    replayEvents s (resolveGroup s rs).events = (resolveGroup s rs).after := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    change replayEvents s ((resolve s r).events ++ (resolveGroup (resolve s r).after rs).events) = _
    rw [replayEvents, List.foldl_append]
    change replayEvents (replayEvents s (resolve s r).events)
      (resolveGroup (resolve s r).after rs).events = _
    rw [resolve_events, ih]
    rfl

theorem resolveGroup_counter_monotone (s : Ledger) (rs : List Request) :
    s.nextId ≤ (resolveGroup s rs).after.nextId := by
  rw [← resolveGroup_events]
  exact replayEvents_counter_monotone s _

end Thesis.Intraday.LifecycleResolver
