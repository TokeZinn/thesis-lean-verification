import Thesis.Foundations.Stochastic.KernelHilbert

/-! # Metric kernel quotients without a linearity assumption

The quotient of any map into a metric space inherits the distance between
its images. In particular this construction applies to a nonconvex image.
-/

noncomputable section

namespace Thesis.Foundations.Stochastic.KernelHilbert

variable {X Y : Type*} [MetricSpace Y] (f : X → Y)

/-- Original label: `defn:function-kernel-quotient-space`.
The image distance is a metric on the function-kernel quotient. -/
@[implicit_reducible]
def functionKernelMetricSpace : MetricSpace (FunctionKernelQuotient f) :=
  MetricSpace.induced (functionKernelExtension f) (functionKernelExtension_injective f)
    inferInstance

/-- Original label: `prop:function-kernel-quotient-injective-extension`.
The quotient metric has the literal representative distance formula. -/
theorem functionKernel_dist_class (x y : X) :
    letI := functionKernelMetricSpace f
    dist (functionKernelClass f x) (functionKernelClass f y) = dist (f x) (f y) := rfl

/-- Original label: `prop:function-kernel-quotient-injective-extension`.
No weak-linearity or convexity hypothesis is needed for this isometry. -/
theorem functionKernelExtension_isometry :
    letI := functionKernelMetricSpace f
    Isometry (functionKernelExtension f) := by
  letI := functionKernelMetricSpace f
  exact fun _ _ => rfl

/-- Original label: `prop:function-kernel-quotient-injective-extension`.
The metric quotient is isometrically equivalent to the actual image. -/
def functionKernelIsometryEquivRange :
    letI := functionKernelMetricSpace f
    FunctionKernelQuotient f ≃ᵢ Set.range f := by
  letI := functionKernelMetricSpace f
  exact { functionKernelEquivRange f with isometry_toFun := fun _ _ => rfl }

end Thesis.Foundations.Stochastic.KernelHilbert
