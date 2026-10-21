import Thesis.Intraday.Simulation.CompiledReplay

/-! # Resolve quantity-only updates at the current mapped live price

Source reductions do not carry an old historical price into due-time replay.
The requested quantity and replacement priority are supplied by the source;
side and price come from the current lifecycle lookup. Reductions retain the
old priority, whereas an increase uses the supplied fresh-addition priority.
-/

noncomputable section
namespace Thesis.Intraday.MappedQuantityUpdate

open LiveLedger LifecycleResolver CompiledReplay

def replacementOrder (a : Entry) (q : PositiveQuantity) (priority : Time) : Order :=
  ofPhysical (a.order.fst, q, priority)

@[simp] theorem replacementOrder_price (a : Entry) (q : PositiveQuantity) (priority : Time) :
    price (replacementOrder a q priority) = price a.order := rfl

@[simp] theorem replacementOrder_quantity (a : Entry) (q : PositiveQuantity) (priority : Time) :
    quantity (replacementOrder a q priority) = q.val := Real.exp_log q.property

@[simp] theorem replacementOrder_time (a : Entry) (q : PositiveQuantity) (priority : Time) :
    time (replacementOrder a q priority) = priority.val := rfl

def resolveQuantity (s : Ledger) (key : ℕ) (q : PositiveQuantity) (priority : Time) : Result :=
  match lookup s key with
  | none => unchanged s .noop
  | some a => change s key a.isBuy (replacementOrder a q priority)

theorem resolveQuantity_missing (s : Ledger) (key : ℕ) (q : PositiveQuantity) (priority : Time)
    (h : lookup s key = none) : resolveQuantity s key q priority = unchanged s .noop := by
  simp [resolveQuantity, h]

theorem resolveQuantity_found (s : Ledger) (key : ℕ) (q : PositiveQuantity) (priority : Time)
    {a : Entry} (h : lookup s key = some a) :
    resolveQuantity s key q priority = change s key a.isBuy (replacementOrder a q priority) := by
  simp [resolveQuantity, h]

theorem canReduce_replacement (a : Entry) (q : PositiveQuantity) (priority : Time) :
    canReduce a a.isBuy (replacementOrder a q priority) ↔ q.val ≤ quantity a.order := by
  simp [canReduce]

theorem resolveQuantity_reduction (s : Ledger) (key : ℕ) (q : PositiveQuantity) (priority : Time)
    {a : Entry} (h : lookup s key = some a) (hq : q.val ≤ quantity a.order) :
    (resolveQuantity s key q priority).after = resizeId s a.liveId q ∧
      (resolveQuantity s key q priority).events = [.resized a.liveId q] ∧
      (resolveQuantity s key q priority).statuses = [.accepted] := by
  simp [resolveQuantity, h, change, canReduce_replacement, hq]

theorem resolveQuantity_increase (s : Ledger) (key : ℕ) (q : PositiveQuantity) (priority : Time)
    {a : Entry} (h : lookup s key = some a) (hq : quantity a.order < q.val) :
    (resolveQuantity s key q priority).after =
      appendFresh (eraseId s a.liveId) key a.isBuy (replacementOrder a q priority) ∧
      (resolveQuantity s key q priority).events =
        [.removed a.liveId, .added ⟨key, s.nextId, a.isBuy, replacementOrder a q priority⟩] ∧
      (resolveQuantity s key q priority).statuses = [.repaired] := by
  simp [resolveQuantity, h, change, canReduce_replacement, not_le.mpr hq]

theorem resolveQuantity_valid {s : Ledger} (hs : Valid s) (key : ℕ)
    (q : PositiveQuantity) (priority : Time) : Valid (resolveQuantity s key q priority).after := by
  unfold resolveQuantity
  split
  · exact hs
  · exact change_valid hs _ _ _

theorem resolveQuantity_events (s : Ledger) (key : ℕ) (q : PositiveQuantity) (priority : Time) :
    replayEvents s (resolveQuantity s key q priority).events =
      (resolveQuantity s key q priority).after := by
  unfold resolveQuantity
  split
  · rfl
  · exact change_events _ _ _ _

theorem resolveQuantity_trace {s : Ledger} (hs : Valid s) (key : ℕ)
    (q : PositiveQuantity) (priority : Time) :
    ValidTrace s (resolveQuantity s key q priority).events := by
  unfold resolveQuantity
  split
  · exact hs
  · exact change_trace hs _ _ _

end Thesis.Intraday.MappedQuantityUpdate
