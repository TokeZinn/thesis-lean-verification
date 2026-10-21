import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Conditional expectations preserve the decoding constraints

The corrected integrability clause of `prop:monotone-decoding-nonexpansive`.
The argument is the thesis argument: commute the finitely many coordinate
linear maps with Bochner conditional expectation, preserve scalar order and
bounds, and intersect the finitely many full-measure sets. Coordinates may
belong to any finite-dimensional weighted Euclidean realization; the proof
uses only their continuous linear maps and hence does not change the weights.
-/

noncomputable section
namespace Thesis.DayAhead.ConditionalDecoding

open MeasureTheory

variable {Ω H : Type*} [m0 : MeasurableSpace Ω]
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable {μ : Measure Ω} {m : MeasurableSpace Ω} {W : Ω → H}

/-- The actual vector conditional expectation, followed by each coordinate,
agrees almost surely with scalar conditional expectation of that coordinate. -/
theorem coordinates_condExp (hW : Integrable W μ) {n : ℕ} (T : Fin n → H →L[ℝ] ℝ) :
    ∀ᵐ ω ∂μ, ∀ i, T i (μ[W | m] ω) = μ[(fun u => T i (W u)) | m] ω := by
  apply ae_all_iff.mpr
  intro i
  exact (T i).comp_condExp_comm hW

/-- Scalar adjacent-order preservation gives monotonicity of all coordinates
on one common full-measure set. -/
theorem monotone_coordinates_condExp (hW : Integrable W μ) {n : ℕ} (T : Fin n → H →L[ℝ] ℝ)
    (hmono : ∀ᵐ ω ∂μ, Monotone (fun i => T i (W ω))) :
    ∀ᵐ ω ∂μ, Monotone (fun i => T i (μ[W | m] ω)) := by
  have hord : ∀ᵐ ω ∂μ, ∀ i j : Fin n, i ≤ j →
      μ[(fun u => T i (W u)) | m] ω ≤ μ[(fun u => T j (W u)) | m] ω := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i ≤ j
    · filter_upwards [condExp_mono ((T i).integrable_comp hW)
        ((T j).integrable_comp hW) (hmono.mono fun _ h => h hij)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => (hij h).elim
  filter_upwards [coordinates_condExp (m0 := m0) (m := m) hW T, hord] with ω hcomm horder
  intro i j hij
  change T i (μ[W | m] ω) ≤ T j (μ[W | m] ω)
  rw [hcomm i, hcomm j]
  exact horder i j hij

/-- Bounded prices remain within the same box after conditional expectation. -/
theorem bounded_coordinates_condExp [IsProbabilityMeasure μ]
    (hm : m ≤ m0) (hW : Integrable W μ) {n : ℕ} (T : Fin n → H →L[ℝ] ℝ)
    (lower upper : ℝ)
    (hbounds : ∀ᵐ ω ∂μ, ∀ i, lower ≤ T i (W ω) ∧ T i (W ω) ≤ upper) :
    ∀ᵐ ω ∂μ, ∀ i, lower ≤ T i (μ[W | m] ω) ∧ T i (μ[W | m] ω) ≤ upper := by
  have hbox : ∀ᵐ ω ∂μ, ∀ i : Fin n,
      lower ≤ μ[(fun u => T i (W u)) | m] ω ∧
      μ[(fun u => T i (W u)) | m] ω ≤ upper := by
    apply ae_all_iff.mpr
    intro i
    have hlo := condExp_mono (m := m) (integrable_const lower)
      ((T i).integrable_comp hW) (hbounds.mono fun _ h => (h i).1)
    have hhi := condExp_mono (m := m) ((T i).integrable_comp hW)
      (integrable_const upper) (hbounds.mono fun _ h => (h i).2)
    rw [condExp_const (μ := μ) hm lower] at hlo
    rw [condExp_const (μ := μ) hm upper] at hhi
    filter_upwards [hlo, hhi] with ω hl hu
    exact ⟨hl, hu⟩
  filter_upwards [coordinates_condExp (m0 := m0) (m := m) hW T, hbox] with ω hcomm hbound
  intro i
  rw [hcomm i]
  exact hbound i

/-- Original label: `prop:monotone-decoding-nonexpansive`.
Corrected conditional-expectation clause: the unbounded quantity coordinates
require integrability of the joint random element. The price coordinate box
is retained as well as its monotonicity. The deterministic metric projection
clauses are proved in `NumericalDecoding`. -/
theorem conditional_decoding_constraints [IsProbabilityMeasure μ]
    (hm : m ≤ m0) (hW : Integrable W μ) {nq np : ℕ}
    (quantity : Fin nq → H →L[ℝ] ℝ) (price : Fin np → H →L[ℝ] ℝ)
    (lower upper : ℝ)
    (hquantity : ∀ᵐ ω ∂μ, Monotone (fun i => quantity i (W ω)))
    (hprice : ∀ᵐ ω ∂μ, Monotone (fun i => price i (W ω)))
    (hbox : ∀ᵐ ω ∂μ, ∀ i, lower ≤ price i (W ω) ∧ price i (W ω) ≤ upper) :
    ∀ᵐ ω ∂μ,
      Monotone (fun i => quantity i (μ[W | m] ω)) ∧
      Monotone (fun i => price i (μ[W | m] ω)) ∧
      ∀ i, lower ≤ price i (μ[W | m] ω) ∧ price i (μ[W | m] ω) ≤ upper := by
  filter_upwards [monotone_coordinates_condExp (m0 := m0) (m := m) hW quantity hquantity,
    monotone_coordinates_condExp (m0 := m0) (m := m) hW price hprice,
    bounded_coordinates_condExp (m0 := m0) hm hW price lower upper hbox] with ω hq hp hb
  exact ⟨hq, hp, hb⟩

end Thesis.DayAhead.ConditionalDecoding
