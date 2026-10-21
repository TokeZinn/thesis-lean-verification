import Thesis.Intraday.Simulation.PriceTranslation

/-! # Operational replay and reconstruction domain bridges

The `_fix.tex` revisions distinguish two raw domains from the bounded formal
order space. Replay prices range over all real numbers and translation is
total there. Reconstruction priority times range over `[0, 1.05)`, while
pre-closure snapshots embed into the formal unit-session order space.
These are explicit inclusions and conditional restrictions, never clipping.
-/

noncomputable section
namespace Thesis.Intraday.DomainExtensions
open Set

abbrev ReplayOrder := WithLp 1 (ℝ × WithLp 1 (ℝ × Time))

def replayPrice (o : ReplayOrder) : ℝ := o.fst
def replayQuantity (o : ReplayOrder) : ℝ := Real.exp o.snd.fst
def replayTime (o : ReplayOrder) : ℝ := o.snd.snd.val

def toReplay (o : Order) : ReplayOrder := WithLp.toLp 1 (price o, o.snd)

def replayShift (o : ReplayOrder) (s : ℝ) : ReplayOrder :=
  WithLp.toLp 1 (replayPrice o + s, o.snd)

def priceAdmissible (o : ReplayOrder) : Prop := replayPrice o ∈ Icc (-9999 : ℝ) 9999

def restrictReplay (o : ReplayOrder) (h : priceAdmissible o) : Order :=
  WithLp.toLp 1 (⟨replayPrice o, h⟩, o.snd)

@[simp] theorem toReplay_price (o : Order) : replayPrice (toReplay o) = price o := rfl
@[simp] theorem toReplay_quantity (o : Order) : replayQuantity (toReplay o) = quantity o := rfl
@[simp] theorem toReplay_time (o : Order) : replayTime (toReplay o) = time o := rfl

@[simp] theorem replayShift_price (o : ReplayOrder) (s : ℝ) :
    replayPrice (replayShift o s) = replayPrice o + s := rfl

@[simp] theorem replayShift_quantity (o : ReplayOrder) (s : ℝ) :
    replayQuantity (replayShift o s) = replayQuantity o := rfl

@[simp] theorem replayShift_time (o : ReplayOrder) (s : ℝ) :
    replayTime (replayShift o s) = replayTime o := rfl

@[simp] theorem toReplay_restrictReplay (o : ReplayOrder) (h : priceAdmissible o) :
    toReplay (restrictReplay o h) = o := rfl

theorem replay_has_bounded_representative_iff (o : ReplayOrder) :
    (∃ bounded : Order, toReplay bounded = o) ↔ priceAdmissible o := by
  constructor
  · rintro ⟨bounded, rfl⟩
    exact price_bounds bounded
  · intro h
    exact ⟨restrictReplay o h, toReplay_restrictReplay o h⟩

theorem shifted_replay_has_bounded_representative_iff (o : Order) (s : ℝ) :
    (∃ bounded : Order, toReplay bounded = replayShift (toReplay o) s) ↔
      price o + s ∈ Icc (-9999 : ℝ) 9999 :=
  replay_has_bounded_representative_iff _

theorem bounded_shift_agrees (o : Order) (s : ℝ)
    (h : price o + s ∈ Icc (-9999 : ℝ) 9999) :
    toReplay (PriceTranslation.shiftOrder o s h) = replayShift (toReplay o) s := rfl

theorem replay_order_complete : CompleteSpace ReplayOrder := inferInstance
theorem replay_order_separable : TopologicalSpace.SeparableSpace ReplayOrder := inferInstance

theorem replay_order_dist (o r : ReplayOrder) :
    dist o r = |replayPrice o - replayPrice r| +
      |Real.log (replayQuantity o) - Real.log (replayQuantity r)| +
      |replayTime o - replayTime r| := by
  simp [WithLp.prod_dist_eq_add, replayPrice, replayQuantity, replayTime,
    Subtype.dist_eq, Real.dist_eq, add_assoc]

abbrev ReconstructionTime := Ico (0 : ℝ) 1.05
abbrev ReconstructionOrder := WithLp 1 (Price × WithLp 1 (ℝ × ReconstructionTime))

def reconstructionPriorityTime (o : ReconstructionOrder) : ℝ := o.snd.snd.val

def toReconstruction (o : Order) : ReconstructionOrder :=
  WithLp.toLp 1 (o.fst, WithLp.toLp 1
    (o.snd.fst, ⟨time o, o.snd.snd.property.1,
      lt_of_le_of_lt o.snd.snd.property.2 (by norm_num)⟩))

def restrictReconstruction (o : ReconstructionOrder) (h : reconstructionPriorityTime o ≤ 1) :
    Order :=
  WithLp.toLp 1 (o.fst, WithLp.toLp 1
    (o.snd.fst, ⟨reconstructionPriorityTime o, o.snd.snd.property.1, h⟩))

@[simp] theorem toReconstruction_time (o : Order) :
    reconstructionPriorityTime (toReconstruction o) = time o := rfl

@[simp] theorem toReconstruction_restrict (o : ReconstructionOrder)
    (h : reconstructionPriorityTime o ≤ 1) :
    toReconstruction (restrictReconstruction o h) = o := rfl

@[simp] theorem restrictReconstruction_toReconstruction (o : Order)
    (h : reconstructionPriorityTime (toReconstruction o) ≤ 1) :
    restrictReconstruction (toReconstruction o) h = o := rfl

theorem reconstruction_has_bounded_time_representative_iff (o : ReconstructionOrder) :
    (∃ bounded : Order, toReconstruction bounded = o) ↔ reconstructionPriorityTime o ≤ 1 := by
  constructor
  · rintro ⟨bounded, rfl⟩
    exact bounded.snd.snd.property.2
  · intro h
    exact ⟨restrictReconstruction o h, toReconstruction_restrict o h⟩

theorem priority_time_in_reconstruction_domain {priority broadcast : ℝ}
    (h₀ : 0 ≤ priority) (hp : priority ≤ broadcast) (hb : broadcast < 1.05) :
    priority ∈ ReconstructionTime := ⟨h₀, hp.trans_lt hb⟩

theorem priority_time_in_formal_domain_before_close {priority broadcast : ℝ}
    (h₀ : 0 ≤ priority) (hp : priority ≤ broadcast) (hb : broadcast ≤ 1) :
    priority ∈ Time := ⟨h₀, hp.trans hb⟩

end Thesis.Intraday.DomainExtensions
