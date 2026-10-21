import Thesis.Intraday.Simulation.LedgerTupleActions

/-! # Compile ordered lifecycle events into the actual composite action

Every primitive payload is resolved against the ledger left by its predecessors.
The resulting composite action produces exactly the ledger's market projection;
the final sorting and visible projection are the existing thesis operators.
-/

noncomputable section
namespace Thesis.Intraday.CompiledReplay

open LiveLedger LifecycleResolver BilateralReplay InstructionReplay LedgerTupleActions
open Clearing Foundations.MarketActions.Composite

def ValidTrace : Ledger → List Event → Prop
  | s, [] => Valid s
  | s, e :: es => Valid s ∧ ValidTrace (applyEvent s e) es

def compileEvents : Ledger → List Event → List (MarketAction TaggedOrder)
  | _, [] => []
  | s, e :: es => eventAction s e :: compileEvents (applyEvent s e) es

def compileScript (s : Ledger) (events : List Event) : CompositeAction TaggedOrder :=
  tupleOfList (compileEvents s events)

theorem validTrace_append {s : Ledger} {a b : List Event} (ha : ValidTrace s a)
    (hb : ValidTrace (replayEvents s a) b) : ValidTrace s (a ++ b) := by
  induction a generalizing s with
  | nil => exact hb
  | cons e es ih => exact ⟨ha.1, ih ha.2 hb⟩

theorem compileEvents_correct {s : Ledger} {events : List Event} (h : ValidTrace s events) :
    (compileEvents s events).foldl applyAction (market s) = market (replayEvents s events) := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih =>
    change (compileEvents (applyEvent s e) es).foldl applyAction
      (applyAction (market s) (eventAction s e)) = _
    rw [← applyEvent_market h.1 e]
    exact ih h.2

theorem compileScript_correct {s : Ledger} {events : List Event} (h : ValidTrace s events) :
    applyCompositeAction (market s) (compileScript s events) = market (replayEvents s events) := by
  have he : compositeActionList (compileScript s events) = compileEvents s events := by
    simp [compositeActionList, compileScript, tupleOfList]
  rw [applyCompositeAction, he]
  exact compileEvents_correct h

theorem fresh_event (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) :
    applyEvent s (.added ⟨key, s.nextId, buy, o⟩) = appendFresh s key buy o := by
  simp [applyEvent, appendFresh]

theorem addition_trace {s : Ledger} (hs : Valid s) (key : ℕ) (buy : Bool) (o : Order) :
    ValidTrace s (addition s key buy o).events := by
  unfold addition
  split
  · exact hs
  · rename_i hn
    change Valid s ∧ Valid (applyEvent s (.added ⟨key, s.nextId, buy, o⟩))
    rw [fresh_event]
    exact ⟨hs, appendFresh_valid hs hn buy o⟩

theorem cancellation_trace {s : Ledger} (hs : Valid s) (key : ℕ) :
    ValidTrace s (cancellation s key).events := by
  unfold cancellation
  split
  · exact hs
  · exact ⟨hs, eraseId_valid hs _⟩

theorem change_trace {s : Ledger} (hs : Valid s) (key : ℕ) (buy : Bool) (o : Order) :
    ValidTrace s (change s key buy o).events := by
  unfold change
  split
  · exact hs
  · rename_i a ha
    split
    · exact ⟨hs, resizeId_valid hs _ _⟩
    · refine ⟨hs, eraseId_valid hs _, ?_⟩
      change Valid (applyEvent (eraseId s a.liveId) (.added ⟨key, s.nextId, buy, o⟩))
      rw [show s.nextId = (eraseId s a.liveId).nextId from rfl, fresh_event]
      exact appendFresh_valid (eraseId_valid hs _) (erase_lookup_absent hs ha) buy o

theorem resolve_trace {s : Ledger} (hs : Valid s) (r : Request) :
    ValidTrace s (resolve s r).events := by
  cases r with
  | add key buy o => exact addition_trace hs key buy o
  | cancel key => exact cancellation_trace hs key
  | change key buy o => exact change_trace hs key buy o

theorem resolveGroup_trace {s : Ledger} (hs : Valid s) (requests : List Request) :
    ValidTrace s (resolveGroup s requests).events := by
  induction requests generalizing s with
  | nil => exact hs
  | cons r rs ih =>
    apply validTrace_append (resolve_trace hs r)
    rw [resolve_events]
    exact ih (resolve_valid hs r)

theorem resolveGroup_composite {s : Ledger} (hs : Valid s) (requests : List Request) :
    applyCompositeAction (market s) (compileScript s (resolveGroup s requests).events) =
      market (resolveGroup s requests).after := by
  rw [compileScript_correct (resolveGroup_trace hs requests), resolveGroup_events]

theorem resolveGroup_visible {s : Ledger} (hs : Valid s) (requests : List Request) (depth : ℕ) :
    Visibility.visible depth (MarketSorting.sortMarket
      (applyCompositeAction (market s) (compileScript s (resolveGroup s requests).events))) =
        visibleMarket depth (resolveGroup s requests).after := by
  rw [resolveGroup_composite hs requests]
  rfl

theorem fill_trace {s : Ledger} (hs : Valid s) (incomingKey restingKey : ℕ) (immediate : Bool) :
    ValidTrace s (fill s incomingKey restingKey immediate).events := by
  unfold fill
  split
  · split
    · exact hs
    · exact ⟨hs, finishLeg_valid hs _ _, finishLeg_valid (finishLeg_valid hs _ _) _ _⟩
  · exact hs

theorem matchSequence_trace {s : Ledger} (hs : Valid s) (incomingKey : ℕ) (restingKeys : List ℕ) :
    ValidTrace s (matchSequence s incomingKey restingKeys).events := by
  induction restingKeys generalizing s with
  | nil => exact hs
  | cons key keys ih =>
    apply validTrace_append (fill_trace hs incomingKey key false)
    rw [fill_events]
    exact ih (matchOne_valid hs _ _)

theorem finishInstruction_trace {s : Ledger} (hs : Valid s) (key : ℕ) (immediate : Bool) :
    ValidTrace s (finishInstruction s key immediate).events := by
  unfold finishInstruction
  split
  · exact hs
  · split
    · exact ⟨hs, eraseId_valid hs _⟩
    · exact hs

theorem replayInstruction_trace {s : Ledger} (hs : Valid s) (incomingKey : ℕ)
    (restingKeys : List ℕ) (immediate : Bool) :
    ValidTrace s (replayInstruction s incomingKey restingKeys immediate).events := by
  apply validTrace_append (matchSequence_trace hs incomingKey restingKeys)
  rw [matchSequence_events]
  exact finishInstruction_trace (matchSequence_valid hs _ _) _ _

theorem replayInstruction_composite {s : Ledger} (hs : Valid s) (incomingKey : ℕ)
    (restingKeys : List ℕ) (immediate : Bool) :
    applyCompositeAction (market s)
      (compileScript s (replayInstruction s incomingKey restingKeys immediate).events) =
        market (replayInstruction s incomingKey restingKeys immediate).after := by
  rw [compileScript_correct (replayInstruction_trace hs incomingKey restingKeys immediate),
    replayInstruction_events]

end Thesis.Intraday.CompiledReplay
