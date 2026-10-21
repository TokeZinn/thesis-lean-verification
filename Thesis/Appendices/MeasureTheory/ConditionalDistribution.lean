import Thesis.Appendices.MeasureTheory.MeasureTheory
import Mathlib.Probability.Kernel.CondDistrib

/-! # All clauses of the regular conditional distribution theorem

One fixed Markov kernel supplies the joint-law identity, the measurable-rectangle
formula, the bounded-test-function conditional expectation, and uniqueness.
-/

namespace Thesis.Foundations.Preliminary.MeasureTheory

open _root_.MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

universe u v w

/-- Original label: `thm:regular-conditional-distribution`.

The conditional-expectation identity is proved for every bounded measurable
test function using the same kernel as the joint-law disintegration. Uniqueness
is with respect to the law of the conditioning random element.
-/
theorem regularConditionalDistribution_full
    {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y) :
    ∃ Q : Kernel T S, IsMarkovKernel Q ∧
      (P.map Y) ⊗ₘ Q = P.map (fun ω ↦ (Y ω, X ω)) ∧
      (∀ A B, MeasurableSet A → MeasurableSet B →
        P (X ⁻¹' A ∩ Y ⁻¹' B) = ∫⁻ y in B, Q y A ∂P.map Y) ∧
      (∀ g : S → ℝ, Measurable g → (∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) →
        P[fun ω ↦ g (X ω) | (inferInstance : MeasurableSpace T).comap Y] =ᵐ[P]
          fun ω ↦ ∫ s, g s ∂Q (Y ω)) ∧
      (∀ R : Kernel T S, IsMarkovKernel R →
        (P.map Y) ⊗ₘ R = P.map (fun ω ↦ (Y ω, X ω)) →
          R =ᵐ[P.map Y] Q) := by
  letI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  letI : Nonempty S := Nonempty.map X inferInstance
  refine ⟨condDistrib X Y P, inferInstance,
    compProd_map_condDistrib hX.aemeasurable, ?_, ?_, ?_⟩
  · intro A B hA hB
    rw [← Measure.compProd_apply_prod hB hA,
      compProd_map_condDistrib hX.aemeasurable,
      Measure.map_apply (hY.prodMk hX) (hB.prod hA)]
    simp only [mk_preimage_prod, inter_comm]
  · intro g hg hbound
    obtain ⟨C, hC⟩ := hbound
    have hgX : Integrable (fun ω ↦ g (X ω)) P :=
      (integrable_const C).mono' (hg.comp hX).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω ↦ hC (X ω))
    exact condExp_ae_eq_integral_condDistrib hY hX.aemeasurable
      hg.stronglyMeasurable hgX
  · intro R hR hdis
    letI : IsMarkovKernel R := hR
    exact (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hY hX hdis.symm).symm

/-- Original label: `thm:measure-disintegration`.
The exact empty-space condition in the current statement: the target must be
inhabited when the source is inhabited. If the source is empty the unique
kernel is vacuously Markov, even when the target is empty too. -/
theorem measureDisintegration_including_empty
    {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] (h : Nonempty S → Nonempty T)
    (Λ : Measure (S × T)) [IsFiniteMeasure Λ] :
    ∃ Q : Kernel S T, IsMarkovKernel Q ∧ Λ.fst ⊗ₘ Q = Λ ∧
      ∀ R : Kernel S T, IsFiniteKernel R →
        Λ.fst ⊗ₘ R = Λ → R =ᵐ[Λ.fst] Q := by
  cases isEmpty_or_nonempty S with
  | inl hs =>
    letI := hs
    have hMarkov : IsMarkovKernel (0 : Kernel S T) := ⟨fun s => isEmptyElim s⟩
    refine ⟨0, hMarkov, Subsingleton.elim _ _, fun R _ _ => ?_⟩
    exact Filter.Eventually.of_forall (fun s => isEmptyElim s)
  | inr hs =>
    letI := h hs
    exact ⟨Λ.condKernel, measureDisintegration Λ⟩

end Thesis.Foundations.Preliminary.MeasureTheory
