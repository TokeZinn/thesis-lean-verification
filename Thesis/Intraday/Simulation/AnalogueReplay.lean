import Thesis.Intraday.Simulation.AnalogueAttention
import Thesis.Intraday.Simulation.PriceTranslation
import Thesis.Intraday.LOBsAndTuples.Clearing
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Dist

/-! # Current Analogue-Attention replay conventions

The current appendix uses clock windows, opposite-touch frozen shifts, an
arrival-admitted visible queue with a bounded waiting queue, and one-half
continuation. These are distinct from the chapter's depth-restricted tuple
operator. The complete feed parser, batch matcher, guard/listener, and empirical
random stream remain separate; this module does not certify an archived run.
-/

noncomputable section
namespace Thesis.Intraday.AnalogueReplay
open Execution Clearing PriceTranslation

def windowOrigin (sessionMinutes : ℝ) (zeroBasedWindow : ℕ) : ℝ :=
  12 * zeroBasedWindow / sessionMinutes

theorem window_spacing (sessionMinutes : ℝ) (w : ℕ) :
    windowOrigin sessionMinutes (w + 1) - windowOrigin sessionMinutes w =
      12 / sessionMinutes := by simp [windowOrigin, Nat.cast_add]; ring

structure LibraryEntry where
  day : ℕ
  window : ℕ
  twoSidedStart : Bool
  hasActions : Bool

def eligible (targetDay currentWindow : ℕ) (e : LibraryEntry) : Prop :=
  e.day < targetDay ∧ Nat.dist e.window currentWindow ≤ 1 ∧
    e.twoSidedStart = true ∧ e.hasActions = true

theorem eligible_strictly_historical (targetDay currentWindow : ℕ) (e : LibraryEntry)
    (he : eligible targetDay currentWindow e) : e.day < targetDay := he.1

def continuationCoin : PMF Bool := PMF.bernoulli (1 / 2) (by norm_num)

theorem continuation_probability : continuationCoin true = (1 / 2 : ENNReal) := by
  norm_num [continuationCoin, PMF.bernoulli_apply]

def windowLaw {ι : Type*} (twoSided : Bool) (next : Option ι)
    (retrieval : PMF (Option ι)) : PMF (Option ι) :=
  if twoSided then
    match next with
    | none => retrieval
    | some j => continuationCoin.bind fun keep => if keep then PMF.pure (some j) else retrieval
  else PMF.pure none

theorem windowLaw_oneSided {ι : Type*} (next : Option ι) (retrieval : PMF (Option ι)) :
    windowLaw false next retrieval = PMF.pure none := rfl

theorem windowLaw_no_successor {ι : Type*} (retrieval : PMF (Option ι)) :
    windowLaw true none retrieval = retrieval := rfl

def oppositeShift (buy : Bool) (source live : Market) : ℝ :=
  let opposite := !buy
  if 0 < (side opposite source).1 then
    best 0 (side opposite live) - best 0 (side opposite source)
  else if 0 < (side buy source).1 then
    best 0 (side buy live) - best 0 (side buy source)
  else 0

theorem oppositeShift_twoSided (buy : Bool) (source live : Market)
    (h : 0 < (side (!buy) source).1) :
    oppositeShift buy source live = best 0 (side (!buy) live) - best 0 (side (!buy) source) := by
  simp [oppositeShift, h]

theorem opposite_anchor_distance (buy : Bool) (source live : Market) (o : Order)
    (h : 0 < (side (!buy) source).1)
    (hp : price o + oppositeShift buy source live ∈ Set.Icc (-9999 : ℝ) 9999) :
    price (shiftOrder o (oppositeShift buy source live) hp) - best 0 (side (!buy) live) =
      price o - best 0 (side (!buy) source) := by
  rw [shiftOrder_price, oppositeShift_twoSided buy source live h]
  ring

structure SideQueue (α : Type*) where
  visible : List α
  waiting : List α

def Valid {α : Type*} (s : SideQueue α) : Prop :=
  s.visible.length ≤ 100 ∧ s.waiting.length ≤ 50

/-- Admission follows arrival; an improved price cannot displace an existing
visible order. Orders beyond the 50 waiting places are dropped. -/
def arrive {α : Type*} (s : SideQueue α) (a : α) : SideQueue α :=
  if s.visible.length < 100 then ⟨s.visible ++ [a], s.waiting⟩
  else if s.waiting.length < 50 then ⟨s.visible, s.waiting ++ [a]⟩ else s

theorem arrive_valid {α : Type*} (s : SideQueue α) (hs : Valid s) (a : α) :
    Valid (arrive s a) := by
  unfold arrive
  split_ifs <;> simp_all [Valid]

theorem arrive_full_preserves_visible {α : Type*} (s : SideQueue α) (a : α)
    (hs : 100 ≤ s.visible.length) : (arrive s a).visible = s.visible := by
  simp only [arrive, not_lt.mpr hs, ↓reduceIte]
  split <;> rfl

/-- End-of-batch promotion performs no matching. The supplied permutation
orders the waiting entries by the current price-time-identifier priority. -/
def promote {α : Type*} (s : SideQueue α) (orderedWaiting : List α) : SideQueue α :=
  let slots := 100 - s.visible.length
  ⟨s.visible ++ orderedWaiting.take slots, orderedWaiting.drop slots⟩

theorem promote_valid {α : Type*} (s : SideQueue α) (hs : Valid s)
    (ordered : List α) (ho : ordered.Perm s.waiting) : Valid (promote s ordered) := by
  have he := ho.length_eq
  dsimp only [Valid, promote]
  simp only [List.length_append, List.length_take, List.length_drop]
  rcases hs with ⟨hv, hw⟩
  constructor <;> omega

theorem promote_retains_all {α : Type*} (s : SideQueue α) (ordered : List α) :
    (promote s ordered).visible ++ (promote s ordered).waiting = s.visible ++ ordered := by
  simp only [promote, List.append_assoc, List.take_append_drop]

def foreignResidual (liveQuantity sourceQuantity : ℝ) : ℝ :=
  liveQuantity - min sourceQuantity liveQuantity

theorem foreign_reduction_conserves (liveQuantity sourceQuantity : ℝ)
    (hl : 0 ≤ liveQuantity) (hs : 0 ≤ sourceQuantity) :
    0 ≤ foreignResidual liveQuantity sourceQuantity ∧
      min sourceQuantity liveQuantity + foreignResidual liveQuantity sourceQuantity = liveQuantity ∧
      foreignResidual liveQuantity sourceQuantity ≤ liveQuantity := by
  have h₁ := min_le_right sourceQuantity liveQuantity
  have h₂ := le_min hs hl
  dsimp [foreignResidual]
  constructor
  · linarith
  constructor <;> linarith

end Thesis.Intraday.AnalogueReplay
