import Thesis.Intraday.Simulation.LifecycleResolver

/-! # Bilateral fill tape and distinct residual/shortfall handling

The simulator appendix specifies the minimum of incoming and resting quantity,
execution at the resting price, and distinct treatment of residual limit and
unmet immediate quantity. `fill` resolves both lifecycle keys in the current
ledger. Missing or same-side counterparts are rejected with no state change.
`settlePair` with the immediate flag is a terminal-pair helper: that flag is
appropriate only when no further matching is to occur. The instruction loop
uses nonterminal pairs and delays residual/shortfall classification until its
entire supplied sequence of matched resting counterparts has been replayed.
-/

noncomputable section
namespace Thesis.Intraday.BilateralReplay

open LiveLedger LifecycleResolver

structure Transaction where
  incomingId : ℕ
  restingId : ℕ
  aggressiveBuy : Bool
  executed : PositiveQuantity
  executionPrice : ℝ

structure FillResult extends Result where
  tape : List Transaction
  residual : ℝ
  shortfall : ℝ

def rejected (s : Ledger) : FillResult :=
  ⟨unchanged s .rejected, [], 0, 0⟩

def filled (incoming resting : Entry) : ℝ := min (quantity incoming.order) (quantity resting.order)

theorem filled_pos (incoming resting : Entry) : 0 < filled incoming resting :=
  lt_min (quantity_pos _) (quantity_pos _)

def incomingRemainder (incoming resting : Entry) : ℝ :=
  quantity incoming.order - filled incoming resting
def restingRemainder (incoming resting : Entry) : ℝ :=
  quantity resting.order - filled incoming resting

theorem incomingRemainder_nonneg (incoming resting : Entry) :
    0 ≤ incomingRemainder incoming resting :=
  sub_nonneg.mpr (min_le_left _ _)

theorem restingRemainder_nonneg (incoming resting : Entry) :
    0 ≤ restingRemainder incoming resting :=
  sub_nonneg.mpr (min_le_right _ _)

theorem matched_balance (incoming resting : Entry) :
    incomingRemainder incoming resting + filled incoming resting = quantity incoming.order ∧
      restingRemainder incoming resting + filled incoming resting = quantity resting.order := by
  constructor <;> simp [incomingRemainder, restingRemainder]

theorem at_least_one_exhausted (incoming resting : Entry) :
    incomingRemainder incoming resting = 0 ∨ restingRemainder incoming resting = 0 := by
  rcases le_total (quantity incoming.order) (quantity resting.order) with h | h
  · left; simp [incomingRemainder, filled, min_eq_left h]
  · right; simp [restingRemainder, filled, min_eq_right h]

def finishEvent (id : ℕ) (remaining : ℝ) : Event :=
  if h : 0 < remaining then .resized id ⟨remaining, h⟩ else .removed id

def finishLeg (s : Ledger) (id : ℕ) (remaining : ℝ) : Ledger :=
  applyEvent s (finishEvent id remaining)

theorem finishLeg_valid {s : Ledger} (hs : Valid s) (id : ℕ) (remaining : ℝ) :
    Valid (finishLeg s id remaining) := by
  unfold finishLeg finishEvent
  split
  · exact resizeId_valid hs _ _
  · exact eraseId_valid hs _

theorem finishLeg_zero (s : Ledger) (id : ℕ) : finishLeg s id 0 = eraseId s id := by
  simp [finishLeg, finishEvent, applyEvent]

theorem finishLeg_positive (s : Ledger) (id : ℕ) {q : ℝ} (hq : 0 < q) :
    finishLeg s id q = resizeId s id ⟨q, hq⟩ := by simp [finishLeg, finishEvent, hq, applyEvent]

/-- Settle a known pair and record any remaining incoming quantity. Immediate
shortfall is removed from the resting ledger; a limit residual remains live. -/
def settlePair (s : Ledger) (incoming resting : Entry) (immediate : Bool) : FillResult :=
  let rem := incomingRemainder incoming resting
  let restEvent := finishEvent resting.liveId (restingRemainder incoming resting)
  let incomingEvent := finishEvent incoming.liveId (if immediate then 0 else rem)
  { after := applyEvent (applyEvent s restEvent) incomingEvent
    events := [restEvent, incomingEvent]
    statuses := .accepted :: (if 0 < rem then [if immediate then .shortfall else .residual] else [])
    tape := [⟨incoming.liveId, resting.liveId, incoming.isBuy,
      ⟨filled incoming resting, filled_pos incoming resting⟩, price resting.order⟩]
    residual := if immediate then 0 else rem
    shortfall := if immediate then rem else 0 }

def fill (s : Ledger) (incomingKey restingKey : ℕ) (immediate : Bool) : FillResult :=
  match lookup s incomingKey, lookup s restingKey with
  | some incoming, some resting =>
    if incoming.isBuy = resting.isBuy then rejected s else settlePair s incoming resting immediate
  | _, _ => rejected s

theorem fill_matched (s : Ledger) (incomingKey restingKey : ℕ) (immediate : Bool)
    {incoming resting : Entry} (hi : lookup s incomingKey = some incoming)
    (hr : lookup s restingKey = some resting) (hopposite : incoming.isBuy ≠ resting.isBuy) :
    fill s incomingKey restingKey immediate = settlePair s incoming resting immediate := by
  simp [fill, hi, hr, hopposite]

theorem settlePair_valid {s : Ledger} (hs : Valid s) (incoming resting : Entry) (immediate : Bool) :
    Valid (settlePair s incoming resting immediate).after :=
  finishLeg_valid (finishLeg_valid hs _ _) _ _

theorem fill_valid {s : Ledger} (hs : Valid s) (incomingKey restingKey : ℕ) (immediate : Bool) :
    Valid (fill s incomingKey restingKey immediate).after := by
  unfold fill
  split
  · split
    · exact hs
    · exact settlePair_valid hs _ _ _
  · exact hs

theorem fill_events (s : Ledger) (incomingKey restingKey : ℕ) (immediate : Bool) :
    replayEvents s (fill s incomingKey restingKey immediate).events =
      (fill s incomingKey restingKey immediate).after := by
  unfold fill
  split
  · split <;> rfl
  · rfl

theorem settlePair_tape (s : Ledger) (incoming resting : Entry) (immediate : Bool) :
    (settlePair s incoming resting immediate).tape =
      [⟨incoming.liveId, resting.liveId, incoming.isBuy,
        ⟨filled incoming resting, filled_pos incoming resting⟩, price resting.order⟩] := rfl

theorem residual_shortfall_balance (s : Ledger) (incoming resting : Entry) (immediate : Bool) :
    (settlePair s incoming resting immediate).residual +
      (settlePair s incoming resting immediate).shortfall + filled incoming resting =
        quantity incoming.order := by
  cases immediate <;> simp [settlePair, incomingRemainder]

theorem residual_shortfall_nonneg (s : Ledger) (incoming resting : Entry) (immediate : Bool) :
    0 ≤ (settlePair s incoming resting immediate).residual ∧
      0 ≤ (settlePair s incoming resting immediate).shortfall := by
  cases immediate <;> simp [settlePair, incomingRemainder_nonneg]

theorem residual_shortfall_disjoint (s : Ledger) (incoming resting : Entry) (immediate : Bool) :
    (settlePair s incoming resting immediate).residual = 0 ∨
      (settlePair s incoming resting immediate).shortfall = 0 := by
  cases immediate <;> simp [settlePair]

theorem full_fill_status (s : Ledger) (incoming resting : Entry) (immediate : Bool)
    (h : quantity incoming.order ≤ quantity resting.order) :
    (settlePair s incoming resting immediate).statuses = [.accepted] := by
  simp [settlePair, incomingRemainder, filled, min_eq_left h]

theorem limit_residual_status (s : Ledger) (incoming resting : Entry)
    (h : quantity resting.order < quantity incoming.order) :
    (settlePair s incoming resting false).statuses = [.accepted, .residual] := by
  simp [settlePair, incomingRemainder, filled, min_eq_right h.le, sub_pos.mpr h]

theorem immediate_shortfall_status (s : Ledger) (incoming resting : Entry)
    (h : quantity resting.order < quantity incoming.order) :
    (settlePair s incoming resting true).statuses = [.accepted, .shortfall] := by
  simp [settlePair, incomingRemainder, filled, min_eq_right h.le, sub_pos.mpr h]

theorem immediate_incoming_absent (s : Ledger) (incoming resting : Entry) :
    ∀ a ∈ (settlePair s incoming resting true).after.live, a.liveId ≠ incoming.liveId := by
  change ∀ a ∈ (finishLeg (finishLeg s resting.liveId (restingRemainder incoming resting))
    incoming.liveId 0).live, a.liveId ≠ incoming.liveId
  rw [finishLeg_zero]
  exact eraseId_absent _ _

theorem opposite_identifiers_distinct {s : Ledger} (hs : Valid s) {incoming resting : Entry}
    (hi : incoming ∈ s.live) (hr : resting ∈ s.live) (hopposite : incoming.isBuy ≠ resting.isBuy) :
    incoming.liveId ≠ resting.liveId := by
  intro he
  have hentry := unique_of_pairwise Entry.liveId hs.2.1 hi hr he
  exact hopposite (congrArg Entry.isBuy hentry)

end Thesis.Intraday.BilateralReplay
