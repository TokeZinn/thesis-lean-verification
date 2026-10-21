import Thesis.Intraday.Simulation.LedgerVisibility

/-! # Copy an opening book with fresh lifecycle identifiers

Source local keys and the entire order payload remain in their supplied order.
Fresh identifiers occupy a disjoint interval beginning at the allocator's
current counter. Historical live identifiers are not reused. The local keys
must already encode the configured provenance namespace.
-/

noncomputable section
namespace Thesis.Intraday.LedgerSeeding

open LiveLedger LedgerTupleActions InstructionConservation

def copyEntry (start : ℕ) (source : List Entry) (i : Fin source.length) : Entry :=
  { source.get i with liveId := start + i.val }

def seedLedger (start : ℕ) (source : List Entry) : Ledger :=
  ⟨start + source.length, List.ofFn (copyEntry start source)⟩

theorem seedLedger_valid (start : ℕ) (source : List Entry)
    (hkeys : source.Pairwise (fun a b => a.localKey ≠ b.localKey)) :
    Valid (seedLedger start source) := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_ofFn.mpr
    intro a b hab
    exact hkeys.rel_get_of_lt hab
  · apply List.pairwise_ofFn.mpr
    intro a b hab
    change start + a.val ≠ start + b.val
    exact ne_of_lt (Nat.add_lt_add_left hab start)
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Nat.add_lt_add_left i.isLt start

theorem seedLedger_length (start : ℕ) (source : List Entry) :
    (seedLedger start source).live.length = source.length := List.length_ofFn

theorem seedLedger_keys (start : ℕ) (source : List Entry) :
    (seedLedger start source).live.map Entry.localKey = source.map Entry.localKey := by
  change (List.ofFn (copyEntry start source)).map _ = _
  rw [List.map_ofFn]
  change List.ofFn (Entry.localKey ∘ source.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem seedLedger_payload (start : ℕ) (source : List Entry) :
    (seedLedger start source).live.map tagged = source.map tagged := by
  change (List.ofFn (copyEntry start source)).map _ = _
  rw [List.map_ofFn]
  change List.ofFn (tagged ∘ source.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem seedLedger_market (start : ℕ) (s : Ledger) :
    market (seedLedger start s.live) = market s := by
  apply tupleList_injective
  rw [tupleList_market, tupleList_market, seedLedger_payload]

theorem seedLedger_ids (start : ℕ) (source : List Entry) :
    (seedLedger start source).live.map Entry.liveId =
      List.ofFn (fun i : Fin source.length => start + i.val) := by
  simp [seedLedger, List.map_ofFn, Function.comp_def, copyEntry]

theorem seedLedger_id_range (start : ℕ) (source : List Entry) {a : Entry}
    (ha : a ∈ (seedLedger start source).live) :
    start ≤ a.liveId ∧ a.liveId < start + source.length := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt start⟩

theorem seedLedger_avoids_old_ids (start : ℕ) (source : List Entry) {oldId : ℕ}
    (hold : oldId < start) {a : Entry} (ha : a ∈ (seedLedger start source).live) :
    a.liveId ≠ oldId := ne_of_gt (hold.trans_le (seedLedger_id_range start source ha).1)

theorem seedLedger_lookup (start : ℕ) (source : List Entry)
    (hkeys : source.Pairwise (fun a b => a.localKey ≠ b.localKey)) (i : Fin source.length) :
    lookup (seedLedger start source) (source.get i).localKey = some (copyEntry start source i) :=
  lookup_of_mem (seedLedger_valid start source hkeys) (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem seedLedger_preserves_order (start : ℕ) (source : List Entry) (i : Fin source.length) :
    (copyEntry start source i).localKey = (source.get i).localKey ∧
      (copyEntry start source i).isBuy = (source.get i).isBuy ∧
      (copyEntry start source i).order = (source.get i).order := ⟨rfl, rfl, rfl⟩

theorem seedLedger_twoSided (start : ℕ) (s : Ledger) :
    (0 < (Clearing.side true (market (seedLedger start s.live))).1 ∧
      0 < (Clearing.side false (market (seedLedger start s.live))).1) ↔
    (0 < (Clearing.side true (market s)).1 ∧
      0 < (Clearing.side false (market s)).1) := by
  rw [seedLedger_market]

theorem seedLedger_sorted (start : ℕ) (s : Ledger) :
    Clearing.SortedMarket (market (seedLedger start s.live)) ↔
      Clearing.SortedMarket (market s) := by
  rw [seedLedger_market]

end Thesis.Intraday.LedgerSeeding
