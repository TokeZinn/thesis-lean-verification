import Thesis.Context.CurrentThesisContext
import Thesis.Appendices.Algebra.GroupCompletion
import Thesis.Foundations.Stochastic.KernelHilbertAlignment

/-! The distinct quotient, formal-difference, span and metric-completion
targets named in the algebra appendix's group-completion scope remark. -/

noncomputable section
namespace Thesis.Foundations.Preliminary.Algebra

open Stochastic.KernelHilbert
universe u v

/-- Original label: `rem:group-completion-scope`.
Transport of formal differences targets the span, with no assertion that
this is the whole ambient vector space. The completed object instead
targets the metric completion of that span. -/
theorem formal_difference_and_metric_completion_targets
    {X : Type u} {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Nonempty X] (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Nonempty (GrothendieckVectorization φ hφ ≃ₗ[ℝ] Submodule.span ℝ (Set.range φ)) ∧
    Nonempty (CompletedGrothendieckVectorization φ hφ ≃ₗᵢ[ℝ]
      UniformSpace.Completion (Submodule.span ℝ (Set.range φ))) ∧
    CompleteSpace (CompletedGrothendieckVectorization φ hφ) := by
  exact ⟨grothendieck_vectorization_is_span φ hφ,
    grothendieck_completion_targets_completedSpan φ hφ, inferInstance⟩

/-- Original label: `rem:group-completion-scope`.
The kernel quotient first removes only noninjectivity of the encoding;
formal inverses and Cauchy limits are separate constructions. -/
theorem encoding_quotient_injective {X : Type u} {V : Type v} (φ : X → V) :
    Function.Injective (functionKernelExtension φ) :=
  functionKernelExtension_injective φ

/-- An isometric embedding into a complete metric space extends to an
isometry from the completion onto exactly the closure of its original range. -/
theorem completion_extension_range {E F : Type*} [MetricSpace E] [MetricSpace F]
    [CompleteSpace F] (f : E → F) (hf : Isometry f) :
    Set.range (UniformSpace.Completion.extension f) = closure (Set.range f) := by
  have he := hf.completion_extension
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_closure.preimage he.continuous
    | ih x =>
      rw [UniformSpace.Completion.extension_coe hf.uniformContinuous]
      exact subset_closure ⟨x, rfl⟩
  · apply closure_minimal
    · rintro y ⟨x, rfl⟩
      exact ⟨x, UniformSpace.Completion.extension_coe hf.uniformContinuous x⟩
    · exact he.isClosedEmbedding.isClosed_range

/-- Original label: `rem:group-completion-scope`.
The actual map to the closure is the canonical continuous extension of the
kernel encoding isometry. This gives the explicit completion-to-closure
isometry (and surjectivity) missing from the earlier evidence inventory. -/
def completedKernelEquivImageClosure {X : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ) :
    CompletedKernelSpace φ hφ ≃ᵢ closure (Set.range φ) := by
  let e := innerProductKernelLinearIsometryEquivRange φ hφ
  let f : InnerProductKernelSpace φ hφ → H := fun x ↦ e x
  have hf : Isometry f := (isometry_subtype_coe).comp e.isometry
  have hr : Set.range f = Set.range φ := by
    change Set.range ((↑) ∘ e) = Set.range φ
    rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
    exact Subtype.range_coe
  let F := UniformSpace.Completion.extension f
  have hF : Isometry F := hf.completion_extension
  have hrange : Set.range F = closure (Set.range φ) := by
    rw [completion_extension_range f hf, hr]
  let j : Set.range F ≃ᵢ closure (Set.range φ) :=
    { toEquiv := Equiv.setCongr hrange
      isometry_toFun := fun _ _ ↦ rfl }
  exact hF.isometryEquivOnRange.trans j

theorem completedKernelEquivImageClosure_coe {X : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ)
    (x : InnerProductKernelSpace φ hφ) :
    ((completedKernelEquivImageClosure φ hφ (x : CompletedKernelSpace φ hφ)) : H) =
      innerProductKernelLinearIsometryEquivRange φ hφ x := by
  exact UniformSpace.Completion.extension_coe
    (((isometry_subtype_coe).comp
      (innerProductKernelLinearIsometryEquivRange φ hφ).isometry).uniformContinuous) x

end Thesis.Foundations.Preliminary.Algebra
