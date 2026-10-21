import Thesis.Intraday.Simulation.DomainExtensions
import Thesis.Intraday.Simulation.DepthProfile

/-! # Depth-profile readouts on operational real-price books

The corrected replay chapter uses real prices. Its sweep, features and
encoder readout are defined here without a bounded-price premise. The exact
embedding identities show that they agree with the existing formal bounded
book formulas whenever the book belongs to that subspace.
-/

noncomputable section
namespace Thesis.Intraday.ReplayGeometry
open scoped BigOperators
open DomainExtensions Foundations.MarketRepresentation
open Execution GeometrySweep

abbrev Book := Tuple ReplayOrder
abbrev State := Book × Book

def toReplayBook (b : Execution.Book) : Book := Tuple.map toReplay b
def toReplayState (b : Execution.State) : State := (toReplayBook b.1, toReplayBook b.2)

def depth (orders : List ReplayOrder) : ℝ := (orders.map replayQuantity).sum

def allocations : List ReplayOrder → ℝ → List ℝ
  | [], _ => []
  | o :: os, v => min (replayQuantity o) (max 0 v) ::
      allocations os (max 0 (v - replayQuantity o))

def notional : List ReplayOrder → ℝ → ℝ
  | [], _ => 0
  | o :: os, v => replayPrice o * min (replayQuantity o) (max 0 v) +
      notional os (max 0 (v - replayQuantity o))

def bookOrders (b : Book) : List ReplayOrder := List.ofFn b.2
def bookQuantity (b : Book) : ℝ := ∑ i, replayQuantity (b.2 i)

def best : Book → ℝ
  | ⟨0, _⟩ => 0
  | ⟨_ + 1, b⟩ => replayPrice (b 0)

def selectedSide (b : State) (u : ℝ) : Book := if u ≤ 0 then b.1 else b.2
def requestedVolume (b : State) (u : ℝ) : ℝ := |u| * bookQuantity (selectedSide b u)
def midpoint (b : State) : ℝ := (best b.1 + best b.2) / 2

def displacement (b : State) (u : ℝ) : ℝ :=
  if u = 0 then 0 else
    (if u ≤ 0 then notional (bookOrders b.1) (-u * bookQuantity b.1)
     else notional (bookOrders b.2) (u * bookQuantity b.2)) /
      requestedVolume b u - midpoint b

def features (b : State) (i : Fin 41) : AnalogueAttention.Vector 4 :=
  let u := DepthProfile.inputNode i
  WithLp.toLp 2 ![u, Real.log (1 + requestedVolume b u),
    Real.arsinh (displacement b u / 10), SignType.sign u]

def outcome (start finish : State) : AnalogueAttention.Vector 33 :=
  WithLp.toLp 2 fun i =>
    displacement finish (DepthProfile.outputNode i) -
      displacement start (DepthProfile.outputNode i)

def encode (e : AnalogueAttention.Encoder) (b : State) (minutes : ℝ) :
    AnalogueAttention.Vector 32 := AnalogueAttention.encode e (features b) minutes

theorem depth_nonneg (orders : List ReplayOrder) : 0 ≤ depth orders := by
  exact List.sum_nonneg (fun q hq => by
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hq
    exact (Real.exp_pos o.snd.fst).le)

theorem allocations_sum (orders : List ReplayOrder) (v : ℝ) :
    (allocations orders v).sum = min (max 0 v) (depth orders) := by
  induction orders generalizing v with
  | nil => simp [allocations, depth]
  | cons o os ih =>
    simp only [allocations, List.sum_cons, ih]
    simpa [depth, max_assoc] using
      (GeometrySweep.split_volume (v := v) (Real.exp_pos o.snd.fst).le (depth_nonneg os))

theorem requestedVolume_nonneg (b : State) (u : ℝ) : 0 ≤ requestedVolume b u := by
  exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le)

theorem logarithm_argument_positive (b : State) (i : Fin 41) :
    0 < 1 + requestedVolume b (DepthProfile.inputNode i) := by
  have := requestedVolume_nonneg b (DepthProfile.inputNode i)
  linarith

theorem allocations_toReplay (orders : List Order) (v : ℝ) :
    allocations (orders.map toReplay) v = GeometrySweep.allocations orders v := by
  induction orders generalizing v with
  | nil => rfl
  | cons o os ih => simp [allocations, GeometrySweep.allocations, ih]

theorem notional_toReplay (orders : List Order) (v : ℝ) :
    notional (orders.map toReplay) v = GeometrySweep.notional orders v := by
  induction orders generalizing v with
  | nil => rfl
  | cons o os ih => simp [notional, GeometrySweep.notional, ih]

@[simp] theorem bookQuantity_toReplay (b : Execution.Book) :
    bookQuantity (toReplayBook b) = Conservation.bookQuantity b := rfl

@[simp] theorem bookOrders_toReplay (b : Execution.Book) :
    bookOrders (toReplayBook b) = (GeometrySweep.bookOrders b).map toReplay := by
  simp only [bookOrders, GeometrySweep.bookOrders, toReplayBook, Tuple.map, List.map_ofFn,
    Function.comp_def]

@[simp] theorem best_toReplay (b : Execution.Book) :
    best (toReplayBook b) = Execution.best 0 b := by
  rcases b with ⟨n, b⟩
  cases n <;> rfl

theorem requestedVolume_toReplay (b : Execution.State) (u : ℝ) :
    requestedVolume (toReplayState b) u = GeometrySweep.requestedVolume b u := by
  by_cases h : u ≤ 0 <;>
    simp [requestedVolume, selectedSide, toReplayState,
      GeometrySweep.requestedVolume, GeometrySweep.selectedSide, h]

theorem midpoint_toReplay (b : Execution.State) :
    midpoint (toReplayState b) = GeometrySweep.midpoint b := by
  simp [midpoint, toReplayState, GeometrySweep.midpoint]

theorem displacement_toReplay (b : Execution.State) (u : ℝ) :
    displacement (toReplayState b) u = GeometrySweep.displacement b u := by
  unfold displacement
  rw [requestedVolume_toReplay, midpoint_toReplay]
  simp only [GeometrySweep.displacement, toReplayState, bookOrders_toReplay,
    bookQuantity_toReplay, notional_toReplay]

theorem features_toReplay (b : Execution.State) (i : Fin 41) :
    features (toReplayState b) i = DepthProfile.features b i := by
  simp only [features, DepthProfile.features, requestedVolume_toReplay, displacement_toReplay]

theorem outcome_toReplay (start finish : Execution.State) :
    outcome (toReplayState start) (toReplayState finish) = DepthProfile.outcome start finish := by
  simp only [outcome, DepthProfile.outcome, displacement_toReplay]

theorem encode_toReplay (e : AnalogueAttention.Encoder) (b : Execution.State) (minutes : ℝ) :
    encode e (toReplayState b) minutes = AnalogueAttention.encode e (DepthProfile.features b)
      minutes := by
  simp only [encode]
  congr 1
  funext i
  exact features_toReplay b i

end Thesis.Intraday.ReplayGeometry
