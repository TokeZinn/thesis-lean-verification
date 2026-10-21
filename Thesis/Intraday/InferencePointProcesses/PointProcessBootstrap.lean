import Thesis.Foundations.Stochastic.PointProcesses
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Literal block restriction and counting-measure bootstrap

`defn:block-bootstrap`: restriction and finite sums remain finite integer
measures. All constructors are measurable for the evaluation sigma-algebras,
so composing them with observed point processes produces point processes.
The interval family can be instantiated by (tau[j-1], tau[j]] times marks.
-/

noncomputable section
namespace Thesis.Intraday.PointProcessBootstrap
open MeasureTheory
open Foundations.Stochastic.PointProcesses
open scoped BigOperators

variable {X J K : Type*} [MeasurableSpace X]

def restrict (mu : FiniteIntegerMeasures X) (A : Set X) (hA : MeasurableSet A) :
    FiniteIntegerMeasures X :=
  ⟨mu.1.restrict A, by
    intro s hs
    obtain ⟨n, hn⟩ := mu.2 (s ∩ A) (hs.inter hA)
    exact ⟨n, (FiniteMeasure.restrict_apply _ _ hs).trans hn⟩⟩

theorem measurable_restrict (A : Set X) (hA : MeasurableSet A) :
    Measurable (fun mu : FiniteIntegerMeasures X => restrict mu A hA) := by
  apply Measurable.subtype_mk
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.restrict_apply hs]
  exact (Measure.measurable_coe (hs.inter hA)).comp
    (measurable_subtype_coe.comp measurable_subtype_coe)

def sum [Fintype J] (mu : J → FiniteIntegerMeasures X) : FiniteIntegerMeasures X :=
  ⟨∑ j, (mu j).1, by
    classical
    intro s hs
    choose n hn using fun j => (mu j).2 s hs
    refine ⟨∑ j, n j, ?_⟩
    have he : (∑ j, (mu j).1) s = ∑ j, (mu j).1 s := by
      induction (Finset.univ : Finset J) using Finset.induction_on with
      | empty => simp
      | @insert i rest hi ih => simp [Finset.sum_insert hi, ih]
    rw [he]
    simp only [hn, Nat.cast_sum]⟩

theorem measurable_sum [Fintype J] :
    Measurable (sum : (J → FiniteIntegerMeasures X) → FiniteIntegerMeasures X) := by
  apply Measurable.subtype_mk
  apply Measurable.subtype_mk
  change Measurable (fun mu : J → FiniteIntegerMeasures X =>
    ((∑ j, (mu j).1 : FiniteMeasure X) : Measure X))
  simp only [FiniteMeasure.toMeasure_sum]
  apply Finset.measurable_sum
  intro j _
  exact measurable_subtype_coe.comp (measurable_subtype_coe.comp (measurable_pi_apply j))

/-- Original label: `defn:block-bootstrap`. -/
def bootstrap [Fintype J] (source : K → FiniteIntegerMeasures X) (choose : J → K)
    (blocks : J → Set X) (hblocks : ∀ j, MeasurableSet (blocks j)) : FiniteIntegerMeasures X :=
  sum fun j => restrict (source (choose j)) (blocks j) (hblocks j)

theorem bootstrap_apply [Fintype J] (source : K → FiniteIntegerMeasures X)
    (choose : J → K) (blocks : J → Set X) (hblocks : ∀ j, MeasurableSet (blocks j))
    (s : Set X) (hs : MeasurableSet s) :
    (bootstrap source choose blocks hblocks).1 s =
      ∑ j, (source (choose j)).1 (s ∩ blocks j) := by
  classical
  unfold bootstrap sum
  have he : (∑ j, ((restrict (source (choose j)) (blocks j) (hblocks j)).1)) s =
      ∑ j, (restrict (source (choose j)) (blocks j) (hblocks j)).1 s := by
    induction (Finset.univ : Finset J) using Finset.induction_on with
    | empty => simp
    | @insert i rest hi ih => simp [Finset.sum_insert hi, ih]
  rw [he]
  simp only [restrict, FiniteMeasure.restrict_apply _ _ hs]

theorem measurable_bootstrap [Fintype J] (choose : J → K) (blocks : J → Set X)
    (hblocks : ∀ j, MeasurableSet (blocks j)) :
    Measurable (fun source : K → FiniteIntegerMeasures X =>
      bootstrap source choose blocks hblocks) := by
  apply measurable_sum.comp
  apply measurable_pi_lambda
  intro j
  exact (measurable_restrict (blocks j) (hblocks j)).comp (measurable_pi_apply (choose j))

end Thesis.Intraday.PointProcessBootstrap
