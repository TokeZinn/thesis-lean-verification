import Thesis.Intraday.Simulation.MappedQuantityUpdate

/-! # Ordered source groups with lifecycle and transaction output

This composes the checked lifecycle requests and ordered matched-fill records.
Inputs already contain parsed orders, translated prices, qualified local keys
and the selected counterpart links. Raw-feed preprocessing, link inference and
queue selection remain upstream. The actual tuple action and the status/tape
outputs follow the same retained source-record order.
-/

noncomputable section
namespace Thesis.Intraday.TypedReplay

open LiveLedger LifecycleResolver BilateralReplay InstructionReplay CompiledReplay
open Foundations.MarketActions.Composite

inductive SourceRecord where
  | lifecycle (request : Request)
  | quantityUpdate (localKey : ℕ) (remaining : PositiveQuantity) (replacementPriority : Time)
  | instruction (incomingKey : ℕ) (restingKeys : List ℕ) (immediate : Bool)

def resolveRecord (s : Ledger) : SourceRecord → FillResult
  | .lifecycle r => ⟨resolve s r, [], 0, 0⟩
  | .quantityUpdate key q priority =>
    ⟨MappedQuantityUpdate.resolveQuantity s key q priority, [], 0, 0⟩
  | .instruction incoming resting immediate => replayInstruction s incoming resting immediate

def resolveRecords : Ledger → List SourceRecord → FillResult
  | s, [] => ⟨⟨s, [], []⟩, [], 0, 0⟩
  | s, record :: records =>
    let first := resolveRecord s record
    let rest := resolveRecords first.after records
    { after := rest.after
      events := first.events ++ rest.events
      statuses := first.statuses ++ rest.statuses
      tape := first.tape ++ rest.tape
      residual := first.residual + rest.residual
      shortfall := first.shortfall + rest.shortfall }

theorem resolveRecord_valid {s : Ledger} (hs : Valid s) (r : SourceRecord) :
    Valid (resolveRecord s r).after := by
  cases r with
  | lifecycle r => exact resolve_valid hs r
  | quantityUpdate key q priority => exact MappedQuantityUpdate.resolveQuantity_valid hs _ _ _
  | instruction incoming resting immediate => exact replayInstruction_valid hs _ _ _

theorem resolveRecord_events (s : Ledger) (r : SourceRecord) :
    replayEvents s (resolveRecord s r).events = (resolveRecord s r).after := by
  cases r with
  | lifecycle r => exact resolve_events s r
  | quantityUpdate key q priority => exact MappedQuantityUpdate.resolveQuantity_events s _ _ _
  | instruction incoming resting immediate => exact replayInstruction_events s _ _ _

theorem resolveRecord_trace {s : Ledger} (hs : Valid s) (r : SourceRecord) :
    ValidTrace s (resolveRecord s r).events := by
  cases r with
  | lifecycle r => exact resolve_trace hs r
  | quantityUpdate key q priority => exact MappedQuantityUpdate.resolveQuantity_trace hs _ _ _
  | instruction incoming resting immediate => exact replayInstruction_trace hs _ _ _

theorem resolveRecords_valid {s : Ledger} (hs : Valid s) (records : List SourceRecord) :
    Valid (resolveRecords s records).after := by
  induction records generalizing s with
  | nil => exact hs
  | cons r rs ih => exact ih (resolveRecord_valid hs r)

theorem resolveRecords_events (s : Ledger) (records : List SourceRecord) :
    replayEvents s (resolveRecords s records).events = (resolveRecords s records).after := by
  induction records generalizing s with
  | nil => rfl
  | cons r rs ih =>
    change replayEvents s ((resolveRecord s r).events ++
      (resolveRecords (resolveRecord s r).after rs).events) = _
    rw [replayEvents, List.foldl_append]
    change replayEvents (replayEvents s (resolveRecord s r).events)
      (resolveRecords (resolveRecord s r).after rs).events = _
    rw [resolveRecord_events, ih]
    rfl

theorem resolveRecords_trace {s : Ledger} (hs : Valid s) (records : List SourceRecord) :
    ValidTrace s (resolveRecords s records).events := by
  induction records generalizing s with
  | nil => exact hs
  | cons r rs ih =>
    apply validTrace_append (resolveRecord_trace hs r)
    rw [resolveRecord_events]
    exact ih (resolveRecord_valid hs r)

/-- No substitute state update is assumed: this is the existing thesis
composite-action evaluator, applied to the compiled current-state indices. -/
theorem resolveRecords_composite {s : Ledger} (hs : Valid s) (records : List SourceRecord) :
    applyCompositeAction (market s) (compileScript s (resolveRecords s records).events) =
      market (resolveRecords s records).after := by
  rw [compileScript_correct (resolveRecords_trace hs records), resolveRecords_events]

theorem resolveRecords_visible {s : Ledger} (hs : Valid s) (records : List SourceRecord)
    (depth : ℕ) :
    Visibility.visible depth (MarketSorting.sortMarket
      (applyCompositeAction (market s) (compileScript s (resolveRecords s records).events))) =
        visibleMarket depth (resolveRecords s records).after := by
  rw [resolveRecords_composite hs records]
  rfl

theorem resolveRecords_empty (s : Ledger) :
    (resolveRecords s []).after = s ∧ (resolveRecords s []).events = [] ∧
      (resolveRecords s []).statuses = [] ∧ (resolveRecords s []).tape = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

end Thesis.Intraday.TypedReplay
