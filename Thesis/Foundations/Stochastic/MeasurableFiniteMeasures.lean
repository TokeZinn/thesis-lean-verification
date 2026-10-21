import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-! # Countably separated finite measures

Evaluations on finite intersections from a countable generator distinguish
finite measures. This permits measurable inverse constructions without
assuming an unproved equivalence with the Prokhorov topology.
-/

noncomputable section

open Set MeasureTheory MeasurableSpace
open scoped ENNReal

namespace Thesis.Foundations.Stochastic.MeasurableFiniteMeasures

universe u v

theorem countablySeparated_of_measurable_injective
    {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    [CountablySeparated B] {f : A → B} (hf : Measurable f)
    (hi : Function.Injective f) : CountablySeparated A := by
  obtain ⟨S, hSc, hSm, hS⟩ := exists_countable_separating B MeasurableSet univ
  refine ⟨⟨(fun s => f ⁻¹' s) '' S, hSc.image _, ?_, ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hf (hSm s hs)
  · intro x _ y _ hxy
    apply hi
    exact hS (f x) (mem_univ _) (f y) (mem_univ _)
      (fun s hs => hxy _ (mem_image_of_mem _ hs))

theorem finiteMeasures_countablySeparated
    (X : Type u) [MeasurableSpace X] [CountablyGenerated X] :
    CountablySeparated (FiniteMeasure X) := by
  classical
  let C : Finset ℕ → Set X := fun s => ⋂ i ∈ s, natGeneratingSequence X i
  have hC (s : Finset ℕ) : MeasurableSet (C s) := by
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurableSet_natGeneratingSequence i
  have hpi : IsPiSystem (range C) := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _
    refine ⟨s ∪ t, ?_⟩
    ext x
    simp [C, or_imp, forall_and]
  have hgen : generateFrom (range C) = (inferInstance : MeasurableSpace X) := by
    apply le_antisymm
    · exact generateFrom_le (fun _ ⟨s, hs⟩ => hs ▸ hC s)
    · rw [← generateFrom_natGeneratingSequence X]
      apply generateFrom_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨{i}, by simp [C]⟩
  let eval : FiniteMeasure X → Finset ℕ → ℝ≥0∞ := fun μ s => (μ : Measure X) (C s)
  have heval : Measurable eval := measurable_pi_lambda _ fun s =>
    (Measure.measurable_coe (hC s)).comp measurable_subtype_coe
  apply countablySeparated_of_measurable_injective heval
  intro μ ν h
  letI : IsFiniteMeasure μ.val := μ.property
  apply Subtype.ext
  apply ext_of_generate_finite (range C) hgen.symm hpi
  · rintro _ ⟨s, rfl⟩
    exact congrFun h s
  · simpa [eval, C] using congrFun h ∅

end Thesis.Foundations.Stochastic.MeasurableFiniteMeasures
