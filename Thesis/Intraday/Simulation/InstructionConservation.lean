import Thesis.Intraday.Simulation.InstructionReplay

/-! # Conservation across every matched pair of an instruction

The proof follows the actual finite ledger through its ordered replay, including
missing/same-side rejected counterparts. Matched volume plus the final limit
residual or immediate shortfall equals the original incoming quantity.
-/

noncomputable section
namespace Thesis.Intraday.InstructionConservation

open LiveLedger LifecycleResolver BilateralReplay InstructionReplay

def keyQuantity (s : Ledger) (key : ℕ) : ℝ :=
  ((lookup s key).map (fun a => quantity a.order)).getD 0

theorem lookup_of_mem {s : Ledger} (hs : Valid s) {a : Entry} (ha : a ∈ s.live) :
    lookup s a.localKey = some a := by
  cases h : lookup s a.localKey with
  | none => exact False.elim ((lookup_none_iff _ _).mp h a ha rfl)
  | some b =>
    have he := unique_of_pairwise Entry.localKey hs.1 (lookup_some_mem h) ha (lookup_some_key h)
    simp [he]

theorem lookup_resize (s : Ledger) (id key : ℕ) (q : PositiveQuantity) :
    lookup (resizeId s id q) key = (lookup s key).map (resized id q) := by
  simp [lookup, resizeId, List.find?_map, Function.comp_def]

theorem lookup_erase_other {s : Ledger} (hs : Valid s) {key : ℕ} {a : Entry}
    (ha : lookup s key = some a) (id : ℕ) (hid : a.liveId ≠ id) :
    lookup (eraseId s id) key = some a := by
  have hm : a ∈ (eraseId s id).live := List.mem_filter.mpr
    ⟨lookup_some_mem ha, by simpa using hid⟩
  rw [← lookup_some_key ha]
  exact lookup_of_mem (eraseId_valid hs _) hm

theorem lookup_finish_other {s : Ledger} (hs : Valid s) {key : ℕ} {a : Entry}
    (ha : lookup s key = some a) (id : ℕ) (q : ℝ) (hid : a.liveId ≠ id) :
    lookup (finishLeg s id q) key = some a := by
  by_cases hq : 0 < q
  · rw [finishLeg_positive s id hq, lookup_resize, ha]
    simp [resized, hid]
  · change lookup (applyEvent s (finishEvent id q)) key = some a
    simp only [finishEvent, dif_neg hq, applyEvent]
    exact lookup_erase_other hs ha id hid

theorem keyQuantity_finish_same {s : Ledger} (hs : Valid s) {key : ℕ} {a : Entry}
    (ha : lookup s key = some a) (q : ℝ) (hq : 0 ≤ q) :
    keyQuantity (finishLeg s a.liveId q) key = q := by
  by_cases hp : 0 < q
  · rw [finishLeg_positive s a.liveId hp]
    simp only [keyQuantity, lookup_resize, ha, Option.map_some, Option.getD_some]
    exact resized_quantity _ _
  · have hz : q = 0 := le_antisymm (le_of_not_gt hp) hq
    subst q
    simp [finishLeg_zero, keyQuantity, erase_lookup_absent hs ha]

theorem matchOne_balance {s : Ledger} (hs : Valid s) (incomingKey restingKey : ℕ) :
    keyQuantity (matchOne s incomingKey restingKey).after incomingKey +
      tapeVolume (matchOne s incomingKey restingKey).tape = keyQuantity s incomingKey := by
  cases hi : lookup s incomingKey with
  | none => simp [matchOne, fill, hi, rejected, unchanged, tapeVolume, keyQuantity]
  | some incoming =>
    cases hr : lookup s restingKey with
    | none => simp [matchOne, fill, hi, hr, rejected, unchanged, tapeVolume]
    | some resting =>
      by_cases hop : incoming.isBuy = resting.isBuy
      · simp [matchOne, fill, hi, hr, hop, rejected, unchanged, tapeVolume]
      · have hid := opposite_identifiers_distinct hs (lookup_some_mem hi) (lookup_some_mem hr) hop
        have hl := lookup_finish_other hs hi resting.liveId (restingRemainder incoming resting) hid
        have hafter := keyQuantity_finish_same (finishLeg_valid hs _ _) hl
          (incomingRemainder incoming resting) (incomingRemainder_nonneg _ _)
        change keyQuantity (finishLeg
          (finishLeg s resting.liveId (restingRemainder incoming resting))
          incoming.liveId (incomingRemainder incoming resting)) incomingKey = _ at hafter
        have hstate : (matchOne s incomingKey restingKey).after =
            finishLeg (finishLeg s resting.liveId (restingRemainder incoming resting))
              incoming.liveId (incomingRemainder incoming resting) := by
          simp [matchOne, fill, hi, hr, hop, settlePair, finishLeg]
        have htape : tapeVolume (matchOne s incomingKey restingKey).tape =
            filled incoming resting := by
          simp [matchOne, fill, hi, hr, hop, settlePair, tapeVolume]
        rw [hstate, hafter, htape]
        simpa [keyQuantity, hi] using (matched_balance incoming resting).1

theorem matchSequence_balance {s : Ledger} (hs : Valid s) (incomingKey : ℕ)
    (restingKeys : List ℕ) :
    keyQuantity (matchSequence s incomingKey restingKeys).after incomingKey +
      tapeVolume (matchSequence s incomingKey restingKeys).tape = keyQuantity s incomingKey := by
  induction restingKeys generalizing s with
  | nil => simp [matchSequence, tapeVolume]
  | cons key keys ih =>
    have hfirst := matchOne_balance hs incomingKey key
    have hrest := ih (matchOne_valid hs incomingKey key)
    change keyQuantity (matchSequence (matchOne s incomingKey key).after incomingKey keys).after
      incomingKey + tapeVolume ((matchOne s incomingKey key).tape ++
        (matchSequence (matchOne s incomingKey key).after incomingKey keys).tape) = _
    rw [tapeVolume_append]
    linarith

theorem replayInstruction_balance {s : Ledger} (hs : Valid s) (incomingKey : ℕ)
    (restingKeys : List ℕ) (immediate : Bool) :
    tapeVolume (replayInstruction s incomingKey restingKeys immediate).tape +
      (replayInstruction s incomingKey restingKeys immediate).residual +
      (replayInstruction s incomingKey restingKeys immediate).shortfall =
        keyQuantity s incomingKey := by
  have hm := matchSequence_balance hs incomingKey restingKeys
  have ht := terminal_unmet_quantity
    (matchSequence s incomingKey restingKeys).after incomingKey immediate
  change _ = keyQuantity _ _ at ht
  dsimp only [replayInstruction]
  linarith

end Thesis.Intraday.InstructionConservation
