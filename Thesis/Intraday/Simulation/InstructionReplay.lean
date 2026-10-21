import Thesis.Intraday.Simulation.ReplayQuantities

/-! # Ordered multi-fill replay with terminal residual/shortfall accounting

The retained source group supplies its ordered matched resting counterpart
keys. `matchOne` retains positive incoming quantity for the next counterpart;
only `finishInstruction` classifies the final limit residual or immediate
shortfall. The choice of counterpart links/queue is an upstream policy, not a
claim that this module reconstructs unobserved venue matching.
-/

noncomputable section
namespace Thesis.Intraday.InstructionReplay

open LiveLedger LifecycleResolver BilateralReplay ReplayQuantities

def matchOne (s : Ledger) (incomingKey restingKey : ℕ) : FillResult :=
  let r := fill s incomingKey restingKey false
  { r with
    statuses := if r.tape.isEmpty then r.statuses else [.accepted]
    residual := 0
    shortfall := 0 }

def matchSequence : Ledger → ℕ → List ℕ → FillResult
  | s, _, [] => ⟨⟨s, [], []⟩, [], 0, 0⟩
  | s, incomingKey, restingKey :: remaining =>
    let first := matchOne s incomingKey restingKey
    let rest := matchSequence first.after incomingKey remaining
    { after := rest.after
      events := first.events ++ rest.events
      statuses := first.statuses ++ rest.statuses
      tape := first.tape ++ rest.tape
      residual := 0
      shortfall := 0 }

def finishInstruction (s : Ledger) (incomingKey : ℕ) (immediate : Bool) : FillResult :=
  match lookup s incomingKey with
  | none => ⟨⟨s, [], []⟩, [], 0, 0⟩
  | some incoming =>
    if immediate then
      ⟨⟨eraseId s incoming.liveId, [.removed incoming.liveId], [.shortfall]⟩,
        [], 0, quantity incoming.order⟩
    else
      ⟨⟨s, [], [.residual]⟩, [], quantity incoming.order, 0⟩

def replayInstruction (s : Ledger) (incomingKey : ℕ) (restingKeys : List ℕ)
    (immediate : Bool) : FillResult :=
  let matched := matchSequence s incomingKey restingKeys
  let terminal := finishInstruction matched.after incomingKey immediate
  { after := terminal.after
    events := matched.events ++ terminal.events
    statuses := matched.statuses ++ terminal.statuses
    tape := matched.tape
    residual := terminal.residual
    shortfall := terminal.shortfall }

theorem matchOne_valid {s : Ledger} (hs : Valid s) (incomingKey restingKey : ℕ) :
    Valid (matchOne s incomingKey restingKey).after := fill_valid hs _ _ _

theorem matchSequence_valid {s : Ledger} (hs : Valid s) (incomingKey : ℕ) (restingKeys : List ℕ) :
    Valid (matchSequence s incomingKey restingKeys).after := by
  induction restingKeys generalizing s with
  | nil => exact hs
  | cons key keys ih => exact ih (matchOne_valid hs _ _)

theorem finishInstruction_valid {s : Ledger} (hs : Valid s) (incomingKey : ℕ) (immediate : Bool) :
    Valid (finishInstruction s incomingKey immediate).after := by
  unfold finishInstruction
  split
  · exact hs
  · split
    · exact eraseId_valid hs _
    · exact hs

theorem replayInstruction_valid {s : Ledger} (hs : Valid s) (incomingKey : ℕ)
    (restingKeys : List ℕ) (immediate : Bool) :
    Valid (replayInstruction s incomingKey restingKeys immediate).after :=
  finishInstruction_valid (matchSequence_valid hs _ _) _ _

theorem matchOne_events (s : Ledger) (incomingKey restingKey : ℕ) :
    replayEvents s (matchOne s incomingKey restingKey).events =
      (matchOne s incomingKey restingKey).after := fill_events s _ _ _

theorem matchSequence_events (s : Ledger) (incomingKey : ℕ) (restingKeys : List ℕ) :
    replayEvents s (matchSequence s incomingKey restingKeys).events =
      (matchSequence s incomingKey restingKeys).after := by
  induction restingKeys generalizing s with
  | nil => rfl
  | cons key keys ih =>
    change replayEvents s ((matchOne s incomingKey key).events ++
      (matchSequence (matchOne s incomingKey key).after incomingKey keys).events) = _
    rw [replayEvents, List.foldl_append]
    change replayEvents (replayEvents s (matchOne s incomingKey key).events)
      (matchSequence (matchOne s incomingKey key).after incomingKey keys).events = _
    rw [matchOne_events, ih]
    rfl

theorem finishInstruction_events (s : Ledger) (incomingKey : ℕ) (immediate : Bool) :
    replayEvents s (finishInstruction s incomingKey immediate).events =
      (finishInstruction s incomingKey immediate).after := by
  unfold finishInstruction
  split
  · rfl
  · split <;> rfl

theorem replayInstruction_events (s : Ledger) (incomingKey : ℕ) (restingKeys : List ℕ)
    (immediate : Bool) :
    replayEvents s (replayInstruction s incomingKey restingKeys immediate).events =
      (replayInstruction s incomingKey restingKeys immediate).after := by
  unfold replayInstruction
  dsimp only
  rw [replayEvents, List.foldl_append]
  change replayEvents (replayEvents s (matchSequence s incomingKey restingKeys).events)
    (finishInstruction (matchSequence s incomingKey restingKeys).after
      incomingKey immediate).events = _
  rw [matchSequence_events, finishInstruction_events]

def tapeVolume (tape : List Transaction) : ℝ := (tape.map (fun t => t.executed.val)).sum

theorem tapeVolume_append (a b : List Transaction) :
    tapeVolume (a ++ b) = tapeVolume a + tapeVolume b := by
  simp [tapeVolume]

theorem tapeVolume_nonneg (tape : List Transaction) : 0 ≤ tapeVolume tape := by
  apply List.sum_nonneg
  intro q hq
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
  exact t.executed.property.le

theorem matchOne_no_terminal_loss (s : Ledger) (incomingKey restingKey : ℕ) :
    (matchOne s incomingKey restingKey).residual = 0 ∧
      (matchOne s incomingKey restingKey).shortfall = 0 := ⟨rfl, rfl⟩

theorem matchSequence_no_terminal_loss (s : Ledger) (incomingKey : ℕ) (restingKeys : List ℕ) :
    (matchSequence s incomingKey restingKeys).residual = 0 ∧
      (matchSequence s incomingKey restingKeys).shortfall = 0 := by
  cases restingKeys <;> exact ⟨rfl, rfl⟩

theorem immediate_has_no_limit_residual (s : Ledger) (incomingKey : ℕ) (restingKeys : List ℕ) :
    (replayInstruction s incomingKey restingKeys true).residual = 0 := by
  cases h : lookup (matchSequence s incomingKey restingKeys).after incomingKey <;>
    simp [replayInstruction, finishInstruction, h]

theorem limit_has_no_shortfall (s : Ledger) (incomingKey : ℕ) (restingKeys : List ℕ) :
    (replayInstruction s incomingKey restingKeys false).shortfall = 0 := by
  cases h : lookup (matchSequence s incomingKey restingKeys).after incomingKey <;>
    simp [replayInstruction, finishInstruction, h]

theorem terminal_unmet_quantity (s : Ledger) (incomingKey : ℕ) (immediate : Bool) :
    (finishInstruction s incomingKey immediate).residual +
      (finishInstruction s incomingKey immediate).shortfall =
        ((lookup s incomingKey).map (fun a => quantity a.order)).getD 0 := by
  unfold finishInstruction
  split
  · simp_all
  · cases immediate <;> simp_all

end Thesis.Intraday.InstructionReplay
