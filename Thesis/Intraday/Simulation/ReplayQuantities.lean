import Thesis.Intraday.Simulation.BilateralReplay

/-! # Fill conservation in the resulting lifecycle ledger

These identities inspect the actual post-event lookup, including deletion when
remaining quantity is zero. The incoming quantity is partitioned into its fill,
live limit residual, and immediate shortfall; the resting side loses exactly
the fill. Every other identifier retains its complete entry.
-/

noncomputable section
namespace Thesis.Intraday.ReplayQuantities

open LiveLedger LifecycleResolver BilateralReplay

def lookupId (s : Ledger) (id : ℕ) : Option Entry :=
  s.live.find? (fun a => a.liveId == id)

theorem lookupId_some_id {s : Ledger} {id : ℕ} {a : Entry} (h : lookupId s id = some a) :
    a.liveId = id := by simpa using List.find?_some h

theorem lookupId_of_mem {s : Ledger} (hs : Valid s) {a : Entry} (ha : a ∈ s.live) :
    lookupId s a.liveId = some a := by
  cases h : lookupId s a.liveId with
  | none =>
    have hn := List.find?_eq_none.mp h a ha
    simp at hn
  | some b =>
    have hb : b ∈ s.live := List.mem_of_find?_eq_some h
    have he := unique_of_pairwise Entry.liveId hs.2.1 hb ha (lookupId_some_id h)
    simp [he]

theorem lookupId_resize (s : Ledger) (id target : ℕ) (q : PositiveQuantity) :
    lookupId (resizeId s id q) target = (lookupId s target).map (resized id q) := by
  simp [lookupId, resizeId, List.find?_map, Function.comp_def]

theorem lookupId_erase_same (s : Ledger) (id : ℕ) : lookupId (eraseId s id) id = none := by
  apply List.find?_eq_none.mpr
  intro a ha
  simpa using eraseId_absent s id a ha

theorem lookupId_erase_other (s : Ledger) (id target : ℕ) (h : target ≠ id) :
    lookupId (eraseId s id) target = lookupId s target := by
  unfold lookupId eraseId
  rw [List.find?_filter]
  congr 1
  funext a
  by_cases ha : a.liveId = target
  · simp [ha, h]
  · simp [ha]

theorem lookupId_finish_other (s : Ledger) (id target : ℕ) (q : ℝ) (h : target ≠ id) :
    lookupId (finishLeg s id q) target = lookupId s target := by
  by_cases hq : 0 < q
  · rw [finishLeg_positive s id hq, lookupId_resize]
    cases ht : lookupId s target with
    | none => rfl
    | some a =>
      have ha := lookupId_some_id ht
      simp [resized, ha, h]
  · change lookupId (applyEvent s (finishEvent id q)) target = _
    simp only [finishEvent, dif_neg hq, applyEvent]
    exact lookupId_erase_other s id target h

def quantityAt (s : Ledger) (id : ℕ) : ℝ := ((lookupId s id).map (fun a => quantity a.order)).getD 0

theorem quantityAt_lookup {s : Ledger} {id : ℕ} {a : Entry} (h : lookupId s id = some a) :
    quantityAt s id = quantity a.order := by simp [quantityAt, h]

theorem quantityAt_finish_same {s : Ledger} {id : ℕ} {a : Entry}
    (ha : lookupId s id = some a) (q : ℝ) (hq : 0 ≤ q) : quantityAt (finishLeg s id q) id = q := by
  by_cases hp : 0 < q
  · rw [finishLeg_positive s id hp]
    have hid := lookupId_some_id ha
    simp only [quantityAt, lookupId_resize, ha, Option.map_some, Option.getD_some]
    rw [← hid, resized_quantity]
  · have hz : q = 0 := le_antisymm (le_of_not_gt hp) hq
    subst q
    simp [finishLeg_zero, quantityAt, lookupId_erase_same]

theorem quantityAt_finish_other (s : Ledger) (id target : ℕ) (q : ℝ) (h : target ≠ id) :
    quantityAt (finishLeg s id q) target = quantityAt s target := by
  simp only [quantityAt, lookupId_finish_other s id target q h]

theorem settlePair_incoming_quantity {s : Ledger} (hs : Valid s) {incoming resting : Entry}
    (hi : incoming ∈ s.live) (hr : resting ∈ s.live)
    (hopposite : incoming.isBuy ≠ resting.isBuy) (immediate : Bool) :
    quantityAt (settlePair s incoming resting immediate).after incoming.liveId =
      if immediate then 0 else incomingRemainder incoming resting := by
  have hid := opposite_identifiers_distinct hs hi hr hopposite
  have hl : lookupId (finishLeg s resting.liveId (restingRemainder incoming resting))
      incoming.liveId = some incoming := by
    rw [lookupId_finish_other _ _ _ _ hid]
    exact lookupId_of_mem hs hi
  apply quantityAt_finish_same hl
  cases immediate <;> simp [incomingRemainder_nonneg]

theorem settlePair_resting_quantity {s : Ledger} (hs : Valid s) {incoming resting : Entry}
    (hi : incoming ∈ s.live) (hr : resting ∈ s.live)
    (hopposite : incoming.isBuy ≠ resting.isBuy) (immediate : Bool) :
    quantityAt (settlePair s incoming resting immediate).after resting.liveId =
      restingRemainder incoming resting := by
  have hid := opposite_identifiers_distinct hs hi hr hopposite
  change quantityAt (finishLeg (finishLeg s resting.liveId (restingRemainder incoming resting))
    incoming.liveId (if immediate then 0 else incomingRemainder incoming resting))
    resting.liveId = _
  rw [quantityAt_finish_other _ _ _ _ hid.symm]
  exact quantityAt_finish_same (lookupId_of_mem hs hr) _ (restingRemainder_nonneg _ _)

theorem settlePair_other_entry (s : Ledger) (incoming resting : Entry) (immediate : Bool)
    (id : ℕ) (hi : id ≠ incoming.liveId) (hr : id ≠ resting.liveId) :
    lookupId (settlePair s incoming resting immediate).after id = lookupId s id := by
  change lookupId (finishLeg (finishLeg s resting.liveId (restingRemainder incoming resting))
    incoming.liveId (if immediate then 0 else incomingRemainder incoming resting)) id = _
  rw [lookupId_finish_other _ _ _ _ hi, lookupId_finish_other _ _ _ _ hr]

theorem fill_ledger_balance {s : Ledger} (hs : Valid s) {incoming resting : Entry}
    (hi : incoming ∈ s.live) (hr : resting ∈ s.live)
    (hopposite : incoming.isBuy ≠ resting.isBuy) (immediate : Bool) :
    quantityAt (settlePair s incoming resting immediate).after incoming.liveId +
      (settlePair s incoming resting immediate).shortfall + filled incoming resting =
        quantity incoming.order ∧
    quantityAt (settlePair s incoming resting immediate).after resting.liveId +
      filled incoming resting = quantity resting.order := by
  rw [settlePair_incoming_quantity hs hi hr hopposite,
    settlePair_resting_quantity hs hi hr hopposite]
  constructor
  · exact residual_shortfall_balance s incoming resting immediate
  · exact (matched_balance incoming resting).2

end Thesis.Intraday.ReplayQuantities
