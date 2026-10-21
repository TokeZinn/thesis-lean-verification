import Thesis.Foundations.Stochastic.KernelMetric

/-! # Explicit quotient and completion clauses in the Hilbert construction

These bridges identify the actual transported operations and embeddings,
rather than just the existence of abstractly isomorphic spaces.
-/

noncomputable section

namespace Thesis.Foundations.Stochastic.KernelHilbert

open Set

universe u v

/-- Original label: `prop:function-kernel-quotient-injective-extension`.
The extension is uniquely determined by its values on the original classes. -/
theorem functionKernelExtension_unique {X : Type u} {Y : Type v} (φ : X → Y)
    (f : FunctionKernelQuotient φ → Y)
    (hf : ∀ x, f (functionKernelClass φ x) = φ x) :
    f = functionKernelExtension φ := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact hf x

section Convex

variable {X : Type u} {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : X → V) (hφ : WeaklyConvexOperator X V φ)

/-- Original label: `thm:grothendieck-vector-space-from-convex-cone`.
The cone addition is cancellative, as required in the manuscript's proof. -/
theorem weakConvexKernelAdd_right_cancel (a b c : WeakConvexKernelSpace φ hφ)
    (h : weakConvexKernelAdd φ hφ a c = weakConvexKernelAdd φ hφ b c) : a = b := by
  apply (weakConvexKernelSpaceEquivRange φ hφ).injective
  apply Subtype.ext
  have him := congrArg (fun q => (weakConvexKernelSpaceEquivRange φ hφ q).val) h
  simpa only [weakConvexKernelAdd_image, add_left_inj] using him

/-- Original label: `thm:grothendieck-vector-space-from-convex-cone`.
The relation expressed in the ambient space is exactly the displayed relation
using addition on the cone quotient. -/
theorem grothendieckRel_iff_quotient_add (p q : GrothendieckPair φ hφ) :
    grothendieckRel φ hφ p q ↔
      weakConvexKernelAdd φ hφ p.1 q.2 = weakConvexKernelAdd φ hφ q.1 p.2 := by
  rw [← (weakConvexKernelSpaceEquivRange φ hφ).injective.eq_iff, Subtype.ext_iff]
  simp only [weakConvexKernelAdd_image, grothendieckRel, weakConvexKernelImage]

/-- Original label: `cor:grothendieck-vectorization-inner-product-space`.
The stated cone-to-vectorization map is an embedding, not just a map. -/
theorem grothendieckConeEmbedding_injective :
    Function.Injective (grothendieckConeEmbedding φ hφ) := by
  intro x y h
  apply (weakConvexKernelSpaceEquivRange φ hφ).injective
  apply Subtype.ext
  have him := congrArg (fun q => (grothendieckVectorizationEquivSpan φ hφ q).val) h
  simpa only [grothendieckVectorizationEquivSpan_coneEmbedding,
    weakConvexKernelImage] using him

end Convex

section Inner

variable {X : Type u} {V : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Nonempty X]
    (φ : X → V) (hφ : WeaklyConvexOperator X V φ)

/-- Original label: `cor:grothendieck-vectorization-inner-product-space`.
The literal map `x ↦ [(x,0)]` preserves the metric pulled back from the image,
as required by the current third clause. -/
theorem grothendieckConeEmbedding_isometry :
    letI : MetricSpace (WeakConvexKernelSpace φ hφ) := functionKernelMetricSpace φ
    Isometry (grothendieckConeEmbedding φ hφ) := by
  letI : MetricSpace (WeakConvexKernelSpace φ hφ) := functionKernelMetricSpace φ
  apply Isometry.of_dist_eq
  intro x y
  calc
    dist (grothendieckConeEmbedding φ hφ x) (grothendieckConeEmbedding φ hφ y) =
        dist (grothendieckVectorizationLinearIsometryEquivSpan φ hφ
          (grothendieckConeEmbedding φ hφ x))
          (grothendieckVectorizationLinearIsometryEquivSpan φ hφ
            (grothendieckConeEmbedding φ hφ y)) :=
      ((grothendieckVectorizationLinearIsometryEquivSpan φ hφ).isometry.dist_eq _ _).symm
    _ = dist (weakConvexKernelImage φ hφ x) (weakConvexKernelImage φ hφ y) := by
      change dist ((grothendieckVectorizationEquivSpan φ hφ
        (grothendieckConeEmbedding φ hφ x)) : V)
        ((grothendieckVectorizationEquivSpan φ hφ
          (grothendieckConeEmbedding φ hφ y)) : V) = _
      rw [grothendieckVectorizationEquivSpan_coneEmbedding,
        grothendieckVectorizationEquivSpan_coneEmbedding]
    _ = dist x y := rfl

/-- Original label: `cor:grothendieck-vectorization-inner-product-space`.
The completed isomorphism really extends the stated map `T`. -/
theorem grothendieckCompletionLinearIsometryEquivSpanCompletion_coe
    (x : GrothendieckVectorization φ hφ) :
    grothendieckCompletionLinearIsometryEquivSpanCompletion φ hφ
        (x : CompletedGrothendieckVectorization φ hφ) =
      (grothendieckVectorizationLinearIsometryEquivSpan φ hφ x :
        CompletedGrothendieckSpan φ hφ) := by
  change UniformSpace.Completion.map
    (grothendieckVectorizationLinearIsometryEquivSpan φ hφ) x = _
  exact UniformSpace.Completion.map_coe
    (grothendieckVectorizationLinearIsometryEquivSpan φ hφ).isometry.uniformContinuous x

/-- Original label: `cor:grothendieck-vectorization-inner-product-space`.
Embed the closure in the original vectorization into the closed cone of its
completion. This makes the source's isometric identification explicit. -/
def grothendieckConeClosureToCompletion
    (x : closure (grothendieckVectorizationCone φ hφ)) :
    completedGrothendieckCone φ hφ :=
  ⟨(x.val : CompletedGrothendieckVectorization φ hφ),
    map_mem_closure (UniformSpace.Completion.continuous_coe _) x.property
      (fun y hy => ⟨y, hy, rfl⟩)⟩

/-- Original label: `cor:grothendieck-vectorization-inner-product-space`.
Distances on that closure are preserved by the actual canonical embedding. -/
theorem grothendieckConeClosureToCompletion_isometry :
    Isometry (grothendieckConeClosureToCompletion φ hφ) := by
  apply Isometry.of_dist_eq
  intro x y
  exact UniformSpace.Completion.dist_eq x.val y.val

/-- Existence wrapper for `cor:grothendieck-vectorization-inner-product-space`
(not the mapped statement): the completed vectorization carries the
inner-product instance and is complete. The completeness clause is
`completedGrothendieckVectorization_complete`, and the extension of `T` to the
completion is `grothendieckCompletionLinearIsometryEquivSpanCompletion` with
`grothendieckCompletionLinearIsometryEquivSpanCompletion_coe`. -/
theorem completedGrothendieckVectorization_hilbert :
    Nonempty (InnerProductSpace ℝ (CompletedGrothendieckVectorization φ hφ)) ∧
      CompleteSpace (CompletedGrothendieckVectorization φ hφ) :=
  ⟨⟨inferInstance⟩, inferInstance⟩

end Inner

end Thesis.Foundations.Stochastic.KernelHilbert
