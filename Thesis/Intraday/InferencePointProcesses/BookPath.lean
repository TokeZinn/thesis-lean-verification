import Thesis.Intraday.LOBsAndTuples.Replay
import Thesis.Intraday.InferencePointProcesses.PointProcessBootstrap
import Thesis.Appendices.Analysis.SkorokhodStepPaths
import Thesis.Appendices.Analysis.BoundedMetric
import Mathlib.Data.List.TakeWhile

/-! # Current finite book paths and their marked counting measures

The finite chronological input is processed in its supplied order, applying
exactly the actions whose timestamp has been reached. No continuity of an
individual transition is required for the resulting finite step path to be
cadlag. Measurability of the random marked tuple gives measurability of its
counting measure, including a random tuple length and the empty tuple.
-/

noncomputable section
namespace Thesis.Intraday.BookPath
open MeasureTheory Set
open Foundations.MarketRepresentation
open Foundations.MarketRepresentation.DisjointUnionTopology
open Foundations.Stochastic.PointProcesses
open Foundations.Preliminary.Analysis

def run {X A : Type*} (step : X → A → X) : X → List (ℝ × A) → ℝ → X
  | x, [], _ => x
  | x, event :: events, t =>
      run step (if event.1 ≤ t then step x event.2 else x) events t

/-- Original label: `defn:order-book-path-point-process`.
Literal depth-restricted book recursion; source inputs have strictly increasing
positive times, so reached events are exactly a prefix of the supplied list. -/
def bookPath (depth : ℕ) (initial : {m : Clearing.Market // Clearing.SortedMarket m})
    (events : List (ℝ × Replay.Script)) (t : ℝ) :
    {m : Clearing.Market // Clearing.SortedMarket m} :=
  run (fun state action => Replay.sortedDepthStep depth (state, action)) initial events t

theorem run_same_comparisons {X A : Type*} (step : X → A → X) (x : X)
    (events : List (ℝ × A)) (u v : ℝ)
    (h : ∀ event ∈ events, event.1 ≤ u ↔ event.1 ≤ v) :
    run step x events u = run step x events v := by
  induction events generalizing x with
  | nil => rfl
  | cons event events ih =>
    have he := h event (by simp)
    have htail : ∀ e ∈ events, e.1 ≤ u ↔ e.1 ≤ v := fun e hm => h e (by simp [hm])
    simp only [run]
    by_cases hu : event.1 ≤ u
    · simp only [hu, he.mp hu, ↓reduceIte]
      exact ih _ htail
    · have hv : ¬event.1 ≤ v := fun hv => hu (he.mpr hv)
      simp only [hu, hv, ↓reduceIte]
      exact ih _ htail

theorem run_all_future {X A : Type*} (step : X → A → X) (x : X)
    (events : List (ℝ × A)) (t : ℝ) (h : ∀ event ∈ events, t < event.1) :
    run step x events t = x := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    have he : ¬event.1 ≤ t := not_le.mpr (h event (by simp))
    simp only [run, he, ↓reduceIte]
    exact ih (fun e hm => h e (by simp [hm]))

theorem run_eq_reached_prefix {X A : Type*} (step : X → A → X) (x : X)
    (events : List (ℝ × A)) (t : ℝ)
    (hsorted : events.Pairwise (fun e f => e.1 < f.1)) :
    run step x events t =
      (events.takeWhile (fun event => decide (event.1 ≤ t))).foldl
        (fun state event => step state event.2) x := by
  induction events generalizing x with
  | nil => rfl
  | cons event events ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    by_cases ht : event.1 ≤ t
    · simpa only [run, ht, ↓reduceIte, List.takeWhile_cons, decide_true, List.foldl_cons]
        using ih (step x event.2) htail
    · have hfuture : ∀ e ∈ events, t < e.1 := by
        intro e he
        have := hhead e he
        linarith
      simpa only [run, ht, ↓reduceIte, List.takeWhile_cons, decide_false, List.foldl_nil]
        using run_all_future step x events t hfuture

theorem run_cadlag {X A : Type*} [MetricSpace X] (step : X → A → X) (x : X)
    (events : List (ℝ × A)) (a b : ℝ) :
    IsOneSidedRegularPath .cadlag (fun t : ClosedInterval a b => run step x events t) := by
  classical
  apply isCadlag_of_finite_cut_cells ((events.map Prod.fst).toFinset)
  intro u v hcell
  apply run_same_comparisons
  intro event he
  exact hcell event.1 (by simpa only [List.mem_toFinset, List.mem_map] using
    (show ∃ e ∈ events, e.1 = event.1 from ⟨event, he, rfl⟩))

/-- Truncating the source's extended tuple metric preserves its uniformity
and topology. Thus the literal sorted-book process is cadlag in the source
topology, including paths whose books change tuple length. -/
theorem bookPath_cadlag (depth : ℕ)
    (initial : {m : Clearing.Market // Clearing.SortedMarket m})
    (events : List (ℝ × Replay.Script)) :
    letI : EMetricSpace Clearing.TaggedOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
    letI : MetricSpace {m : Clearing.Market // Clearing.SortedMarket m} :=
      Foundations.Preliminary.BoundedMetric.truncatedMetricSpace _
    IsOneSidedRegularPath .cadlag
      (fun t : ClosedInterval 0 1 => bookPath depth initial events t) := by
  letI : EMetricSpace Clearing.TaggedOrder := DisjointUnionTopology.disjointUnionEMetricSpace
  letI : MetricSpace {m : Clearing.Market // Clearing.SortedMarket m} :=
    Foundations.Preliminary.BoundedMetric.truncatedMetricSpace _
  exact run_cadlag _ _ _ _ _

def atom {A : Type*} [MeasurableSpace A] (event : A) : FiniteIntegerMeasures A :=
  ⟨diracFiniteMeasure event, by
    intro s hs
    classical
    by_cases he : event ∈ s
    · exact ⟨1, by simp [diracFiniteMeasure_apply event hs, he]⟩
    · exact ⟨0, by simp [diracFiniteMeasure_apply event hs, he]⟩⟩

theorem measurable_atom {A : Type*} [MeasurableSpace A] : Measurable (atom : A → _) := by
  apply Measurable.subtype_mk
  apply Measurable.subtype_mk
  exact Measure.measurable_dirac

def markedMeasure {A : Type*} [MeasurableSpace A] (events : Tuple (ℝ × A)) :
    FiniteIntegerMeasures (ℝ × A) := PointProcessBootstrap.sum fun i => atom (events.2 i)

theorem measurable_markedMeasure {A : Type*} [MeasurableSpace A] :
    Measurable (markedMeasure : Tuple (ℝ × A) → _) := by
  apply measurable_pasting_iff.mpr
  intro n
  change Measurable (PointProcessBootstrap.sum ∘
    (fun events : Fin n → ℝ × A => fun i => atom (events i)))
  apply PointProcessBootstrap.measurable_sum.comp
  apply measurable_pi_lambda
  intro i
  exact measurable_atom.comp (measurable_pi_apply i)

/-- The exact closed-interval codomain of the source's marked point process. -/
def unitMarkedMeasure {A : Type*} [MeasurableSpace A]
    (events : Tuple (ClosedInterval 0 1 × A)) : FiniteIntegerMeasures (ClosedInterval 0 1 × A) :=
  PointProcessBootstrap.sum fun i => atom (events.2 i)

theorem measurable_unitMarkedMeasure {A : Type*} [MeasurableSpace A] :
    Measurable (unitMarkedMeasure : Tuple (ClosedInterval 0 1 × A) → _) := by
  apply measurable_pasting_iff.mpr
  intro n
  change Measurable (PointProcessBootstrap.sum ∘
    (fun events : Fin n → ClosedInterval 0 1 × A => fun i => atom (events i)))
  apply PointProcessBootstrap.measurable_sum.comp
  apply measurable_pi_lambda
  intro i
  exact measurable_atom.comp (measurable_pi_apply i)

end Thesis.Intraday.BookPath
