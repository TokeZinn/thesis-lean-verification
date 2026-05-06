import Foundations.Stochastic.TupleMeasures
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Stochastic Markets: Kernel Hilbert Embeddings

Blueprint module for
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Hilbert Embeddings".

Planned formal content:

* functionals and operators;
* weakly linear and weakly convex operators;
* convex cones;
* `prop:phi-subspace`;
* kernel equivalence relation and kernel space;
* weak transport of vector, cone, and inner-product structure;
* Hilbert-space criterion and completion;
* convex-cone projection theorem;
* Grothendieck-style vectorization of weak convex operators;
* induced inner product and completion results.
-/

namespace Thesis
namespace Foundations
namespace Stochastic
namespace KernelHilbert

open Set
open scoped BigOperators

universe u v w

/-! ## Weak Operators and Function Kernels -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Hilbert Embeddings".

Original label: `defn:functional-and-operator`.

Informal statement: a `𝕂`-functional on `X` is just a map from `X` to the
scalar field.
-/
abbrev Functional (𝕂 : Type u) (X : Type v) : Type (max u v) :=
  X → 𝕂

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Hilbert Embeddings".

Original label: `defn:functional-and-operator`.

Informal statement: a `V`-operator on `X` is just a map from `X` to the target
space `V`.
-/
abbrev Operator (X : Type u) (V : Type v) : Type (max u v) :=
  X → V

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:weak-linear-operator`.

Original label: `defn:weak-linear-operator`.

Informal statement: an operator is weakly linear when every binary linear
combination of two image points has at least one representative back in `X`.

Lean strategy / thesis relation note: the thesis assumes `X` is nonempty in the
surrounding statement. The definition itself does not need that assumption; the
equivalence with "image is a subspace" below uses `[Nonempty X]`, exactly as the
thesis does.
-/
def WeaklyLinearOperator (𝕂 : Type u) (X : Type v) (V : Type w)
    [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] (φ : Operator X V) : Prop :=
  ∀ (α β : 𝕂) (x x' : X), ∃ xstar : X,
    φ xstar = α • φ x + β • φ x'

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:convex-cone`.

Original label: `defn:convex-cone`.

Informal statement: a subset of a real vector space is a convex cone when it is
closed under nonnegative linear combinations.

Lean strategy / thesis relation note: the closure formula only uses addition and scalar
multiplication, so Lean states the definition for an additive commutative monoid
with an `ℝ`-module structure. The thesis-literal real-vector-space wrapper
appears in `weaklyConvexOperator_iff_range_convexCone_realVectorSpace`.
-/
def ConvexCone {V : Type u} [AddCommMonoid V] [Module ℝ V]
    (C : Set V) : Prop :=
  ∀ ⦃c c' : V⦄, c ∈ C → c' ∈ C →
    ∀ ⦃α β : ℝ⦄, 0 ≤ α → 0 ≤ β → α • c + β • c' ∈ C

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:weakly-convex-operator`.

Original label: `defn:weakly-convex-operator`.

Informal statement: an operator is weakly convex when every nonnegative linear
combination of two image points has a representative back in `X`.

Lean strategy / thesis relation note: as for `ConvexCone`, the definition is stated in the minimally
needed additive-monoid/module setting; ordinary real vector spaces are covered
by the specialized theorem below.
-/
def WeaklyConvexOperator (X : Type u) (V : Type v)
    [AddCommMonoid V] [Module ℝ V] (φ : Operator X V) : Prop :=
  ∀ ⦃α β : ℝ⦄, 0 ≤ α → 0 ≤ β → ∀ (x x' : X), ∃ xstar : X,
    φ xstar = α • φ x + β • φ x'

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:phi-subspace`.

Original label: auxiliary formulation for `prop:phi-subspace`.

Informal statement: a subset of a vector space is a linear subspace when it is
the carrier set of a Lean `Submodule`.
-/
def IsLinearSubspace (𝕂 : Type u) (V : Type v)
    [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] (S : Set V) : Prop :=
  ∃ W : Submodule 𝕂 V, (W : Set V) = S

-- Thesis source:
-- `1 - theoretical foundations/5_stochastic_markets.tex`,
-- Proposition `prop:phi-subspace`.
--
-- Original label: construction used in `prop:phi-subspace`.
--
-- Informal statement: from weak linearity, the image of `φ` carries the
-- subspace structure inherited from `V`.
noncomputable def weaklyLinearRangeSubmodule {𝕂 : Type u} {X : Type v}
    {V : Type w} [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator 𝕂 X V φ) : Submodule 𝕂 V where
  carrier := Set.range φ
  zero_mem' := by
    obtain ⟨x0⟩ := (inferInstance : Nonempty X)
    obtain ⟨z, hz⟩ := hφ 0 0 x0 x0
    refine ⟨z, ?_⟩
    simpa using hz
  add_mem' := by
    rintro v w ⟨x, rfl⟩ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hφ 1 1 x y
    refine ⟨z, ?_⟩
    simpa using hz
  smul_mem' := by
    intro α v hv
    rcases hv with ⟨x, rfl⟩
    obtain ⟨y0⟩ := (inferInstance : Nonempty X)
    obtain ⟨z, hz⟩ := hφ α 0 x y0
    refine ⟨z, ?_⟩
    simpa using hz

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:phi-subspace`.

Original label: carrier identity for the weak-linear forward direction of
`prop:phi-subspace`.

Informal statement: the submodule constructed from weak linearity has carrier
set exactly `φ(X)`.
-/
theorem weaklyLinearRangeSubmodule_carrier {𝕂 : Type u} {X : Type v}
    {V : Type w} [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator 𝕂 X V φ) :
    ((weaklyLinearRangeSubmodule φ hφ : Submodule 𝕂 V) : Set V) =
      Set.range φ :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:phi-subspace`.

Original label: `prop:phi-subspace`, weak-linear half.

Informal statement: `φ` is weakly linear if and only if its image is a linear
subspace of the ambient vector space.

Lean strategy / thesis relation note: Lean phrases "subspace" as "there exists a `Submodule` whose
carrier is `Set.range φ`." The proof follows the thesis' omitted argument:
weak linearity gives closure under `0`, addition, and scalar multiplication;
conversely, submodule closure gives a representative by membership in the
range.
-/
theorem weaklyLinearOperator_iff_range_isSubspace {𝕂 : Type u} {X : Type v}
    {V : Type w} [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) :
    WeaklyLinearOperator 𝕂 X V φ ↔ IsLinearSubspace 𝕂 V (Set.range φ) := by
  constructor
  · intro hφ
    exact ⟨weaklyLinearRangeSubmodule φ hφ, rfl⟩
  · rintro ⟨W, hW⟩ α β x x'
    have hx : φ x ∈ W := by
      change φ x ∈ (W : Set V)
      rw [hW]
      exact ⟨x, rfl⟩
    have hx' : φ x' ∈ W := by
      change φ x' ∈ (W : Set V)
      rw [hW]
      exact ⟨x', rfl⟩
    have hcombo : α • φ x + β • φ x' ∈ W :=
      W.add_mem (W.smul_mem α hx) (W.smul_mem β hx')
    have hcombo' : α • φ x + β • φ x' ∈ Set.range φ := by
      change α • φ x + β • φ x' ∈ (W : Set V) at hcombo
      rwa [hW] at hcombo
    rcases hcombo' with ⟨z, hz⟩
    exact ⟨z, hz⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:phi-subspace`.

Original label: `prop:phi-subspace`, weak-convex half.

Informal statement: `φ` is weakly convex if and only if its image is a convex
cone.
-/
theorem weaklyConvexOperator_iff_range_convexCone {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X] (φ : Operator X V) :
    WeaklyConvexOperator X V φ ↔ ConvexCone (Set.range φ) := by
  constructor
  · intro hφ
    rintro c c' ⟨x, rfl⟩ ⟨y, rfl⟩ α β hα hβ
    obtain ⟨z, hz⟩ := hφ hα hβ x y
    exact ⟨z, hz⟩
  · intro hcone α β hα hβ x y
    have hmem : α • φ x + β • φ y ∈ Set.range φ :=
      hcone ⟨x, rfl⟩ ⟨y, rfl⟩ hα hβ
    rcases hmem with ⟨z, hz⟩
    exact ⟨z, hz⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:phi-subspace`.

Original label: thesis-literal real-vector-space wrapper for
`prop:phi-subspace`, weak-convex half.

Informal statement: for an ordinary real vector space, `φ` is weakly convex if
and only if its image is a convex cone.

Lean strategy / thesis strategy note: `ConvexCone` and `WeaklyConvexOperator` are defined above in
the slightly more general additive-monoid/module setting because their closure
formulas do not use additive inverses. This theorem exposes the exact
real-vector-space hypothesis package used in the manuscript.
-/
theorem weaklyConvexOperator_iff_range_convexCone_realVectorSpace
    {X : Type u} {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) :
    WeaklyConvexOperator X V φ ↔ ConvexCone (Set.range φ) :=
  weaklyConvexOperator_iff_range_convexCone φ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:phi-extends`.

Original label: `prop:phi-extends`.

Informal statement: two points are equivalent when they have the same image
under `φ`.
-/
def functionKernelSetoid {X : Type u} {Y : Type v} (φ : X → Y) : Setoid X where
  r x y := φ x = φ y
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:phi-extends`.

Original label: `prop:phi-extends`.

Informal statement: equality of images defines an equivalence relation.
-/
theorem functionKernel_equivalence {X : Type u} {Y : Type v} (φ : X → Y) :
    Equivalence (functionKernelSetoid φ).r :=
  (functionKernelSetoid φ).iseqv

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:function-kernel-quotient-space`.

Original label: `defn:function-kernel-quotient-space`.

Informal statement: the kernel space `X_φ` is the quotient of `X` by the
relation of having equal image under `φ`.

Lean strategy / thesis relation note: Lean uses `Quotient` over the `Setoid` above rather than
forming the set of equivalence classes by comprehension.
-/
abbrev FunctionKernelQuotient {X : Type u} {Y : Type v} (φ : X → Y) : Type u :=
  Quotient (functionKernelSetoid φ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:function-kernel-quotient-space`.

Original label: notation for `defn:function-kernel-quotient-space`.

Informal statement: `functionKernelClass φ x` is the equivalence class
`x_φ = [x]`.
-/
def functionKernelClass {X : Type u} {Y : Type v} (φ : X → Y) (x : X) :
    FunctionKernelQuotient φ :=
  Quotient.mk (functionKernelSetoid φ) x

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:function-kernel-quotient-injective-extension`.

Original label: extension map in
`prop:function-kernel-quotient-injective-extension`.

Informal statement: `φ` descends to a well-defined map from the kernel
quotient to the codomain.
-/
noncomputable def functionKernelExtension {X : Type u} {Y : Type v} (φ : X → Y) :
    FunctionKernelQuotient φ → Y :=
  Quotient.lift φ (by
    intro x y hxy
    exact hxy)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:function-kernel-quotient-injective-extension`.

Original label: representative formula in
`prop:function-kernel-quotient-injective-extension`.

Informal statement: the descended map sends the class of `x` to `φ x`.
-/
@[simp]
theorem functionKernelExtension_class {X : Type u} {Y : Type v} (φ : X → Y)
    (x : X) :
    functionKernelExtension φ (functionKernelClass φ x) = φ x :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:function-kernel-quotient-injective-extension`.

Original label: `prop:function-kernel-quotient-injective-extension`.

Informal statement: the descended map from `X_φ` into `Y` is injective.
-/
theorem functionKernelExtension_injective {X : Type u} {Y : Type v} (φ : X → Y) :
    Function.Injective (functionKernelExtension φ) := by
  intro q r hqr
  exact Quotient.inductionOn₂ q r
    (motive := fun q r => functionKernelExtension φ q = functionKernelExtension φ r → q = r)
    (fun x y hxy => by
      change φ x = φ y at hxy
      exact Quotient.sound hxy) hqr

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:function-kernel-quotient-injective-extension`.

Original label: image-identification corollary implicit in
`prop:function-kernel-quotient-injective-extension`.

Informal statement: the kernel quotient `X_φ` is equivalent to the image
`φ(X)`.
-/
noncomputable def functionKernelEquivRange {X : Type u} {Y : Type v}
    (φ : X → Y) :
    FunctionKernelQuotient φ ≃ Set.range φ where
  toFun q := ⟨functionKernelExtension φ q, by
    induction q using Quotient.inductionOn with
    | h x => exact ⟨x, rfl⟩⟩
  invFun y := functionKernelClass φ (Classical.choose y.2)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
        apply Quotient.sound
        exact Classical.choose_spec (show ∃ a, φ a = φ x from ⟨x, rfl⟩)
  right_inv y := by
    ext
    exact Classical.choose_spec y.2

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:weak-linear-transport-vector-space-structure`.

Original label: image-identification step in
`thm:weak-linear-transport-vector-space-structure`.

Informal statement: for a weakly linear operator, the kernel quotient is
equivalent to the image submodule of `V`.
-/
noncomputable def weakLinearKernelEquivRangeSubmodule {𝕂 : Type u}
    {X : Type v} {V : Type w}
    [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator 𝕂 X V φ) :
    FunctionKernelQuotient φ ≃ weaklyLinearRangeSubmodule φ hφ where
  toFun q := ⟨functionKernelExtension φ q, by
    induction q using Quotient.inductionOn with
    | h x => exact ⟨x, rfl⟩⟩
  invFun y := functionKernelClass φ
    (Classical.choose (show y.1 ∈ Set.range φ from y.2))
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
        apply Quotient.sound
        exact Classical.choose_spec (show ∃ a, φ a = φ x from ⟨x, rfl⟩)
  right_inv y := by
    ext
    exact Classical.choose_spec (show y.1 ∈ Set.range φ from y.2)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:weak-linear-transport-vector-space-structure`.

Original label: carrier of `thm:weak-linear-transport-vector-space-structure`.

Informal statement: the transported kernel space is the quotient `X_φ`, bundled
with the weak-linearity proof that supplies the image submodule used for
transport.
-/
def WeakLinearKernelSpace {𝕂 : Type u} {X : Type v} {V : Type w}
    [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (_hφ : WeaklyLinearOperator 𝕂 X V φ) :=
  FunctionKernelQuotient φ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:weak-linear-transport-vector-space-structure`.

Original label: transported bijection in
`thm:weak-linear-transport-vector-space-structure`.

Informal statement: the transported kernel space is equivalent to the image
submodule.
-/
noncomputable def weakLinearKernelSpaceEquivRange {𝕂 : Type u} {X : Type v}
    {V : Type w} [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator 𝕂 X V φ) :
    WeakLinearKernelSpace φ hφ ≃ weaklyLinearRangeSubmodule φ hφ :=
  weakLinearKernelEquivRangeSubmodule φ hφ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:weak-linear-transport-vector-space-structure`.

Original label: additive part of
`thm:weak-linear-transport-vector-space-structure`.

Informal statement: addition and additive inverses on `X_φ` are transported
from the image submodule along the equivalence with `φ(X)`.
-/
noncomputable instance weakLinearKernelSpace_addCommGroup {𝕂 : Type u}
    {X : Type v} {V : Type w}
    [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator 𝕂 X V φ) :
    AddCommGroup (WeakLinearKernelSpace φ hφ) :=
  Equiv.addCommGroup (weakLinearKernelSpaceEquivRange φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:weak-linear-transport-vector-space-structure`.

Original label: scalar-multiplication part of
`thm:weak-linear-transport-vector-space-structure`.

Informal statement: scalar multiplication on `X_φ` is transported from the
image submodule along the equivalence with `φ(X)`.
-/
noncomputable instance weakLinearKernelSpace_module {𝕂 : Type u}
    {X : Type v} {V : Type w}
    [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator 𝕂 X V φ) :
    Module 𝕂 (WeakLinearKernelSpace φ hφ) :=
  Equiv.module 𝕂 (weakLinearKernelSpaceEquivRange φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:weak-linear-transport-vector-space-structure`.

Original label: `thm:weak-linear-transport-vector-space-structure`.

Informal statement: `X_φ` carries the transported vector-space structure by
identifying it with the subspace `φ(X)`.

Lean strategy / thesis relation note: instead of naming formulas with a set-theoretic inverse
`Φ^{-1}`, Lean constructs an equivalence
`weakLinearKernelSpaceEquivRange φ hφ` and transports the algebraic typeclass
instances from the image submodule along that equivalence.
-/
theorem weakLinear_transport_vectorSpace_structure {𝕂 : Type u} {X : Type v}
    {V : Type w} [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator 𝕂 X V φ) :
    Nonempty (WeakLinearKernelSpace φ hφ ≃ weaklyLinearRangeSubmodule φ hφ) :=
  ⟨weakLinearKernelSpaceEquivRange φ hφ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:weak-linear-transport-vector-space-structure`.

Original label: audit-facing structure availability for
`thm:weak-linear-transport-vector-space-structure`.

Informal statement: the transported additive-group and scalar-module
structures on `X_φ` are available as Lean instances.
-/
theorem weakLinear_transport_vectorSpace_instances {𝕂 : Type u} {X : Type v}
    {V : Type w} [Field 𝕂] [AddCommGroup V] [Module 𝕂 V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator 𝕂 X V φ) :
    Nonempty (AddCommGroup (WeakLinearKernelSpace φ hφ)) ∧
      Nonempty (Module 𝕂 (WeakLinearKernelSpace φ hφ)) := by
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:weak-convex-transport-convex-cone-structure`.

Original label: carrier of `cor:weak-convex-transport-convex-cone-structure`.

Informal statement: the weak-convex transported kernel space is the quotient
`X_φ`, bundled with the weak-convexity proof that supplies the image cone.
-/
def WeakConvexKernelSpace {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (_hφ : WeaklyConvexOperator X V φ) :=
  FunctionKernelQuotient φ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:weak-convex-transport-convex-cone-structure`.

Original label: transported bijection in
`cor:weak-convex-transport-convex-cone-structure`.

Informal statement: the weak-convex kernel quotient is equivalent to the image
cone `φ(X)`.
-/
noncomputable def weakConvexKernelSpaceEquivRange {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    WeakConvexKernelSpace φ hφ ≃ Set.range φ :=
  functionKernelEquivRange φ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:weak-convex-transport-convex-cone-structure`.

Original label: transported addition in
`cor:weak-convex-transport-convex-cone-structure`.

Informal statement: addition on the weak-convex quotient is transported from
addition in the image cone by `Φ^{-1}`.
-/
noncomputable def weakConvexKernelAdd {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (q r : WeakConvexKernelSpace φ hφ) : WeakConvexKernelSpace φ hφ := by
  classical
  let e := weakConvexKernelSpaceEquivRange φ hφ
  let qv := e q
  let rv := e r
  refine e.symm ⟨qv.1 + rv.1, ?_⟩
  have hcone : ConvexCone (Set.range φ) :=
    (weaklyConvexOperator_iff_range_convexCone φ).mp hφ
  have h := hcone (c := qv.1) (c' := rv.1)
    qv.property rv.property (α := 1) (β := 1) zero_le_one zero_le_one
  simpa [one_smul] using h

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:weak-convex-transport-convex-cone-structure`.

Original label: transported nonnegative scalar multiplication in
`cor:weak-convex-transport-convex-cone-structure`.

Informal statement: nonnegative scalar multiplication on the weak-convex
quotient is transported from the image cone by `Φ^{-1}`.
-/
noncomputable def weakConvexKernelNonnegativeScalarMultiplication {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (α : ℝ) (hα : 0 ≤ α)
    (q : WeakConvexKernelSpace φ hφ) : WeakConvexKernelSpace φ hφ := by
  classical
  let e := weakConvexKernelSpaceEquivRange φ hφ
  let qv := e q
  refine e.symm ⟨α • qv.1, ?_⟩
  have hcone : ConvexCone (Set.range φ) :=
    (weaklyConvexOperator_iff_range_convexCone φ).mp hφ
  have h := hcone (c := qv.1) (c' := qv.1)
    qv.property qv.property (α := α) (β := 0) hα le_rfl
  simpa [zero_smul, add_zero] using h

/-- The transported addition has the thesis `Φ^{-1}(Φ q + Φ r)` formula. -/
@[simp]
theorem weakConvexKernelAdd_image {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (q r : WeakConvexKernelSpace φ hφ) :
    ((weakConvexKernelSpaceEquivRange φ hφ
      (weakConvexKernelAdd φ hφ q r)).1 : V) =
      (weakConvexKernelSpaceEquivRange φ hφ q).1 +
        (weakConvexKernelSpaceEquivRange φ hφ r).1 := by
  simp [weakConvexKernelAdd]

/-- The transported nonnegative scalar operation has the thesis
`Φ^{-1}(α • Φ q)` formula. -/
@[simp]
theorem weakConvexKernelNonnegativeScalarMultiplication_image {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (α : ℝ) (hα : 0 ≤ α) (q : WeakConvexKernelSpace φ hφ) :
    ((weakConvexKernelSpaceEquivRange φ hφ
      (weakConvexKernelNonnegativeScalarMultiplication φ hφ α hα q)).1 : V) =
      α • (weakConvexKernelSpaceEquivRange φ hφ q).1 := by
  simp [weakConvexKernelNonnegativeScalarMultiplication]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:weak-convex-transport-convex-cone-structure`.

Original label: transported cone-closure formula for
`cor:weak-convex-transport-convex-cone-structure`.

Informal statement: under the transported operations on `X_φ`, every
nonnegative linear combination is represented by transporting the corresponding
image-cone combination back along `Φ^{-1}`.
-/
theorem weakConvexKernel_transportedCone_combination_image
    {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (q r : WeakConvexKernelSpace φ hφ) :
    ((weakConvexKernelSpaceEquivRange φ hφ
      (weakConvexKernelAdd φ hφ
        (weakConvexKernelNonnegativeScalarMultiplication φ hφ α hα q)
        (weakConvexKernelNonnegativeScalarMultiplication φ hφ β hβ r))).1 : V) =
      α • (weakConvexKernelSpaceEquivRange φ hφ q).1 +
        β • (weakConvexKernelSpaceEquivRange φ hφ r).1 := by
  simp

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:weak-convex-transport-convex-cone-structure`.

Original label: transported operation package for
`cor:weak-convex-transport-convex-cone-structure`.

Informal statement: the quotient `X_φ` is equipped with the transported
addition and nonnegative scalar multiplication appearing in the thesis, and
these operations realize the convex-cone closure formula through the
quotient-image bijection `Φ`.
-/
theorem weakConvex_transport_convexCone_operations
    {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    (∀ q r : WeakConvexKernelSpace φ hφ,
      ((weakConvexKernelSpaceEquivRange φ hφ
        (weakConvexKernelAdd φ hφ q r)).1 : V) =
        (weakConvexKernelSpaceEquivRange φ hφ q).1 +
          (weakConvexKernelSpaceEquivRange φ hφ r).1) ∧
    (∀ ⦃α : ℝ⦄ (hα : 0 ≤ α) (q : WeakConvexKernelSpace φ hφ),
      ((weakConvexKernelSpaceEquivRange φ hφ
        (weakConvexKernelNonnegativeScalarMultiplication φ hφ α hα q)).1 : V) =
        α • (weakConvexKernelSpaceEquivRange φ hφ q).1) ∧
    (∀ ⦃α β : ℝ⦄ (hα : 0 ≤ α) (hβ : 0 ≤ β)
        (q r : WeakConvexKernelSpace φ hφ),
      ((weakConvexKernelSpaceEquivRange φ hφ
        (weakConvexKernelAdd φ hφ
          (weakConvexKernelNonnegativeScalarMultiplication φ hφ α hα q)
          (weakConvexKernelNonnegativeScalarMultiplication φ hφ β hβ r))).1 : V) =
        α • (weakConvexKernelSpaceEquivRange φ hφ q).1 +
          β • (weakConvexKernelSpaceEquivRange φ hφ r).1) := by
  exact ⟨weakConvexKernelAdd_image φ hφ,
    ⟨fun {α} hα q => weakConvexKernelNonnegativeScalarMultiplication_image φ hφ α hα q,
      fun {α} {β} hα hβ q r =>
        weakConvexKernel_transportedCone_combination_image
          φ hφ hα hβ q r⟩⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:weak-convex-transport-convex-cone-structure`.

Original label: `cor:weak-convex-transport-convex-cone-structure`.

Informal statement: if `φ` is weakly convex, then the quotient `X_φ` is
identified with the convex cone `φ(X)`.

Lean strategy / thesis relation note: the manuscript writes explicit transported addition and
nonnegative scalar multiplication using `Φ^{-1}`. The preceding declarations
define those transported operations directly; this theorem also records the
image-cone identification used later.
-/
theorem weakConvex_transport_convexCone_structure {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    ConvexCone (Set.range φ) ∧
      Nonempty (WeakConvexKernelSpace φ hφ ≃ Set.range φ) := by
  exact ⟨(weaklyConvexOperator_iff_range_convexCone φ).mp hφ,
    ⟨weakConvexKernelSpaceEquivRange φ hφ⟩⟩

/-! ## Inner-Product Kernel Spaces -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:inner-product-kernel-space`.

Original label: `defn:inner-product-kernel-space`.

Informal statement: the inner-product kernel space has carrier `X_φ`, the
kernel quotient associated with a weakly linear map into a real inner-product
space.
-/
abbrev InnerProductKernelSpace {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator ℝ X V φ) :=
  WeakLinearKernelSpace φ hφ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:inner-product-kernel-space`.

Original label: inner-product formula in `defn:inner-product-kernel-space`.

Informal statement: the kernel inner product is the ambient inner product of
the two transported image representatives.

Lean strategy / thesis relation note: the thesis writes
`\llangle x_\varphi,y_\varphi\rrangle = \langle φ(x),φ(y)\rangle`. Lean defines
the same expression through the quotient-to-image equivalence, which makes
representative independence automatic.
-/
noncomputable def innerProductKernelInner {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator ℝ X V φ) :
    InnerProductKernelSpace φ hφ → InnerProductKernelSpace φ hφ → ℝ :=
  fun q r => inner ℝ
    ((weakLinearKernelSpaceEquivRange φ hφ q).1)
    ((weakLinearKernelSpaceEquivRange φ hφ r).1)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:inner-product-kernel-space`.

Original label: representative formula in `defn:inner-product-kernel-space`.

Informal statement: on representatives, the quotient inner product is exactly
the ambient inner product of their images.
-/
@[simp]
theorem innerProductKernelInner_class {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator ℝ X V φ) (x y : X) :
    innerProductKernelInner φ hφ
      (functionKernelClass φ x) (functionKernelClass φ y) =
        inner ℝ (φ x) (φ y) := by
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:weak-linear-kernel-inner-product-space`.

Original label: well-defined formula part of
`prop:weak-linear-kernel-inner-product-space`.

Informal statement: the displayed kernel inner-product formula is a
well-defined binary form on the kernel quotient.

Lean strategy / thesis relation note: this is the representative-independence part of the thesis
proposition. The full Lean `InnerProductSpace` instance requires transporting
the compatible normed-group/topological structure as well, and remains the next
target.
-/
theorem weakLinear_kernel_innerProduct_wellDefined {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator ℝ X V φ) :
    ∃ B : InnerProductKernelSpace φ hφ → InnerProductKernelSpace φ hφ → ℝ,
      ∀ x y : X, B (functionKernelClass φ x) (functionKernelClass φ y) =
        inner ℝ (φ x) (φ y) := by
  exact ⟨innerProductKernelInner φ hφ,
    innerProductKernelInner_class φ hφ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:weak-linear-kernel-inner-product-space`.

Original label: transported inner-product core for
`prop:weak-linear-kernel-inner-product-space`.

Informal statement: the kernel inner product satisfies the algebraic axioms of
an inner-product core after transporting along the quotient-to-image
equivalence.
-/
@[reducible]
noncomputable def innerProductKernelCore {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator ℝ X V φ) :
    InnerProductSpace.Core ℝ (InnerProductKernelSpace φ hφ) where
  inner := innerProductKernelInner φ hφ
  conj_inner_symm := by
    intro x y
    exact inner_conj_symm _ _
  re_inner_nonneg := by
    intro x
    exact inner_self_nonneg
  add_left := by
    intro x y z
    let e := weakLinearKernelSpaceEquivRange φ hφ
    have hmap : e (x + y) = e x + e y := by
      change e (e.symm (e x + e y)) = e x + e y
      simp
    change inner ℝ ((e (x + y)).1) ((e z).1) =
      inner ℝ ((e x).1) ((e z).1) + inner ℝ ((e y).1) ((e z).1)
    rw [hmap]
    simpa using inner_add_left ((e x).1) ((e y).1) ((e z).1)
  smul_left := by
    intro x y r
    let e := weakLinearKernelSpaceEquivRange φ hφ
    have hmap : e (r • x) = r • e x := by
      change e (e.symm (r • e x)) = r • e x
      simp
    change inner ℝ ((e (r • x)).1) ((e y).1) =
      (starRingEnd ℝ) r * inner ℝ ((e x).1) ((e y).1)
    rw [hmap]
    simpa using inner_smul_left ((e x).1) ((e y).1) r
  definite := by
    intro x hx
    let e := weakLinearKernelSpaceEquivRange φ hφ
    have hxinner : inner ℝ ((e x).1) ((e x).1) = 0 := hx
    have hxV : ((e x).1 : V) = 0 := by
      exact (inner_self_eq_zero (𝕜 := ℝ) (E := V)).mp hxinner
    have hxSub : e x = 0 := by
      ext
      simpa using hxV
    have hzero : e 0 = 0 := by
      change e (e.symm 0) = 0
      simp
    exact (Equiv.injective e) (hxSub.trans hzero.symm)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:weak-linear-kernel-inner-product-space`.

Original label: normed additive-group part of
`prop:weak-linear-kernel-inner-product-space`.

Informal statement: the transported inner-product core supplies the compatible
normed additive-group structure on the kernel space.
-/
noncomputable instance innerProductKernelSpace_normedAddCommGroup {X : Type u}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator ℝ X V φ) :
    NormedAddCommGroup (InnerProductKernelSpace φ hφ) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := innerProductKernelCore φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:weak-linear-kernel-inner-product-space`.

Original label: `prop:weak-linear-kernel-inner-product-space`.

Informal statement: the kernel quotient, endowed with the transported inner
product, is a real inner-product space.

Lean strategy / thesis relation note: this is the typeclass version of the thesis' proof: the map
`Φ : X_φ → φ(X)` is injective and identifies the transported form with the
ambient inner product on the image.
-/
noncomputable instance innerProductKernelSpace_innerProductSpace {X : Type u}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator ℝ X V φ) :
    InnerProductSpace ℝ (InnerProductKernelSpace φ hφ) :=
  InnerProductSpace.ofCore (innerProductKernelCore φ hφ).toCore

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:weak-linear-kernel-inner-product-space`.

Original label: theorem wrapper for `prop:weak-linear-kernel-inner-product-space`.

Informal statement: the transported real inner-product-space structure on the
kernel space is available.
-/
theorem weakLinear_kernel_innerProductSpace {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyLinearOperator ℝ X V φ) :
    Nonempty (InnerProductSpace ℝ (InnerProductKernelSpace φ hφ)) :=
  ⟨inferInstance⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:kernel-space-hilbert-iff-image-closed`.

Original label: isometric-identification step in
`prop:kernel-space-hilbert-iff-image-closed`.

Informal statement: the kernel space is linearly equivalent to the image
submodule.
-/
noncomputable def innerProductKernelLinearEquivRange {X : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ) :
    InnerProductKernelSpace φ hφ ≃ₗ[ℝ] weaklyLinearRangeSubmodule φ hφ where
  toFun := weakLinearKernelSpaceEquivRange φ hφ
  invFun := (weakLinearKernelSpaceEquivRange φ hφ).symm
  left_inv := (weakLinearKernelSpaceEquivRange φ hφ).left_inv
  right_inv := (weakLinearKernelSpaceEquivRange φ hφ).right_inv
  map_add' := by
    intro x y
    let e := weakLinearKernelSpaceEquivRange φ hφ
    change e (x + y) = e x + e y
    change e (e.symm (e x + e y)) = e x + e y
    simp
  map_smul' := by
    intro r x
    let e := weakLinearKernelSpaceEquivRange φ hφ
    change e (r • x) = r • e x
    change e (e.symm (r • e x)) = r • e x
    simp

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:kernel-space-hilbert-iff-image-closed`.

Original label: isometric-identification step in
`prop:kernel-space-hilbert-iff-image-closed`.

Informal statement: the identification between `X_φ` and `φ(X)` is an
isometric linear equivalence.

Lean strategy / thesis relation note: this is the formal version of the thesis sentence that
`Φ:X_φ → φ(X)` is an isometric linear isomorphism.
-/
noncomputable def innerProductKernelLinearIsometryEquivRange {X : Type u}
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ) :
    InnerProductKernelSpace φ hφ ≃ₗᵢ[ℝ] weaklyLinearRangeSubmodule φ hφ where
  toLinearEquiv := innerProductKernelLinearEquivRange φ hφ
  norm_map' := by
    intro x
    let e := weakLinearKernelSpaceEquivRange φ hφ
    change ‖e x‖ = ‖x‖
    rw [norm_eq_sqrt_real_inner (x := (e x)), norm_eq_sqrt_real_inner (x := x)]
    rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:kernel-space-hilbert-iff-image-closed`.

Original label: `prop:kernel-space-hilbert-iff-image-closed`.

Informal statement: the kernel space is Hilbert precisely when the image
`φ(X)` is closed in the ambient Hilbert space.

Lean strategy / thesis relation note: Lean represents "Hilbert" as an inner-product space equipped
with `CompleteSpace`. The inner-product-space structure was constructed above,
so this theorem states the remaining completeness criterion.
-/
theorem kernelSpace_hilbert_iff_image_closed {X : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ) :
    CompleteSpace (InnerProductKernelSpace φ hφ) ↔ IsClosed (Set.range φ) := by
  let W := weaklyLinearRangeSubmodule φ hφ
  let e := innerProductKernelLinearIsometryEquivRange φ hφ
  have hcomp_congr : CompleteSpace (InnerProductKernelSpace φ hφ) ↔ CompleteSpace W :=
    completeSpace_congr (LinearIsometryEquiv.isometry e).isUniformEmbedding
  constructor
  · intro hcomp
    have hcompW : CompleteSpace W := hcomp_congr.mp hcomp
    have hcompleteW : IsComplete (W : Set H) :=
      completeSpace_coe_iff_isComplete.mp hcompW
    have hcompleteRange : IsComplete (Set.range φ) := by
      simpa [W] using hcompleteW
    exact hcompleteRange.isClosed
  · intro hclosed
    have hcompleteRange : IsComplete (Set.range φ) := hclosed.isComplete
    have hcompW : CompleteSpace W := by
      apply completeSpace_coe_iff_isComplete.mpr
      simpa [W] using hcompleteRange
    exact hcomp_congr.mpr hcompW

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:bijective-weak-linear-transport-hilbert-structure`.

Original label: `cor:bijective-weak-linear-transport-hilbert-structure`.

Informal statement: if `φ` is bijective into a Hilbert space, then the
transported kernel space is Hilbert.
-/
theorem bijective_weakLinear_transport_hilbert_structure {X : Type u}
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ)
    (hbij : Function.Bijective φ) :
    CompleteSpace (InnerProductKernelSpace φ hφ) := by
  rw [kernelSpace_hilbert_iff_image_closed φ hφ]
  rw [hbij.2.range_eq]
  exact isClosed_univ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:kernel-space-separable`.

Original label: `prop:kernel-space-separable`.

Informal statement: if the ambient real inner-product space is separable, then
the induced kernel space is separable.

Lean strategy / thesis relation note: this follows exactly as in the thesis: the image `φ(X)` is a
subspace of a separable space, hence separable; the isometric identification
`X_φ ≃ φ(X)` transports separability back to the kernel space.
-/
theorem kernelSpace_separable {X : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ) :
    TopologicalSpace.SeparableSpace (InnerProductKernelSpace φ hφ) := by
  let e := innerProductKernelLinearIsometryEquivRange φ hφ
  haveI : TopologicalSpace.SeparableSpace (weaklyLinearRangeSubmodule φ hφ) :=
    inferInstance
  exact (LinearIsometryEquiv.symm e).surjective.denseRange.separableSpace
    (LinearIsometryEquiv.continuous (LinearIsometryEquiv.symm e))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:completed-kernel-space`.

Original label: `defn:completed-kernel-space`.

Informal statement: the completed kernel space is the completion of the
inner-product kernel space.

Lean strategy / thesis relation note: the thesis describes the completion by Cauchy sequences. Lean
uses mathlib's `UniformSpace.Completion`, which is the canonical completion
object for any uniform space, including normed inner-product spaces.
-/
abbrev CompletedKernelSpace {X : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ) :=
  UniformSpace.Completion (InnerProductKernelSpace φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:completed-kernel-space`.

Original label: completeness property implicit in `defn:completed-kernel-space`.

Informal statement: the completed kernel space is complete.
-/
theorem completedKernelSpace_complete {X : Type u} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nonempty X]
    (φ : Operator X H) (hφ : WeaklyLinearOperator ℝ X H φ) :
    CompleteSpace (CompletedKernelSpace φ hφ) :=
  UniformSpace.Completion.completeSpace (InnerProductKernelSpace φ hφ)

/-! ## Closed Convex Cones and Metric Projection -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`.

Original label: auxiliary lemma for
`thm:closed-convex-cone-closure-projection`.

Informal statement: a nonempty convex cone contains the origin.

Lean strategy / thesis relation note: the thesis uses the usual mathematical
convention that a convex cone is nonempty. Our predicate on sets permits the
empty set vacuously, so results about metric projection carry an explicit
`C.Nonempty` hypothesis.
-/
theorem convexCone_zero_mem_of_nonempty {H : Type u} [AddCommMonoid H]
    [Module ℝ H] {C : Set H} (hC : ConvexCone C) (hne : C.Nonempty) :
    (0 : H) ∈ C := by
  rcases hne with ⟨c, hc⟩
  have h := hC hc hc (α := 0) (β := 0) le_rfl le_rfl
  simpa using h

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`.

Original label: auxiliary lemma for
`thm:closed-convex-cone-closure-projection`.

Informal statement: the thesis' convex-cone condition implies ordinary
convexity.
-/
theorem convex_of_convexCone {H : Type u} [AddCommMonoid H] [Module ℝ H]
    {C : Set H} (hC : ConvexCone C) : Convex ℝ C := by
  intro x hx y hy a b ha hb _hab
  exact hC hx hy ha hb

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`.

Original label: auxiliary lemma for
`thm:closed-convex-cone-closure-projection`.

Informal statement: nonnegative scalar multiplication preserves the closure of
a convex cone.
-/
theorem convexCone_smul_mem_closure {H : Type u} [TopologicalSpace H]
    [AddCommMonoid H] [Module ℝ H] [ContinuousConstSMul ℝ H] {C : Set H}
    (hC : ConvexCone C) {α : ℝ} (hα : 0 ≤ α) {x : H}
    (hx : x ∈ closure C) : α • x ∈ closure C := by
  exact map_mem_closure (ContinuousConstSMul.continuous_const_smul α) hx (by
    intro z hz
    have h := hC hz hz hα le_rfl
    simpa [zero_smul, add_zero] using h)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (i).

Original label: `thm:closed-convex-cone-closure-projection`, closure-cone
clause.

Informal statement: the closure of a convex cone is again a convex cone.

Lean strategy / thesis relation note: this follows the thesis narrative directly. Given
`x,y ∈ closure C` and `α,β ≥ 0`, first place `αx` and `βy` in `closure C` by
continuity of scalar multiplication, then place their sum in `closure C` by
continuity of addition and the original cone law on `C`.
-/
theorem convexCone_closure {H : Type u} [TopologicalSpace H]
    [AddCommMonoid H] [Module ℝ H] [ContinuousConstSMul ℝ H]
    [ContinuousAdd H] {C : Set H} (hC : ConvexCone C) :
    ConvexCone (closure C) := by
  intro x y hx hy α β hα hβ
  have hxα : α • x ∈ closure C := convexCone_smul_mem_closure hC hα hx
  have hyβ : β • y ∈ closure C := convexCone_smul_mem_closure hC hβ hy
  exact map_mem_closure₂ continuous_add hxα hyβ (by
    intro z hz w hw
    have h := hC hz hw (α := 1) (β := 1) (by norm_num) (by norm_num)
    simpa using h)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (i).

Original label: `thm:closed-convex-cone-closure-projection`, completeness
clause.

Informal statement: in a complete ambient Hilbert space, the closure of a
convex cone is a complete subset.
-/
theorem convexCone_closure_isComplete {H : Type u} [UniformSpace H]
    [CompleteSpace H] {C : Set H} : IsComplete (closure C) :=
  isClosed_closure.isComplete

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (i).

Original label: `thm:closed-convex-cone-closure-projection`, combined closure
and completeness statement.

Informal statement: the closure of a convex cone is a convex cone and complete.
-/
theorem closedConvexCone_closure_convexCone_and_complete {H : Type u}
    [UniformSpace H] [CompleteSpace H]
    [AddCommMonoid H] [Module ℝ H] [ContinuousConstSMul ℝ H]
    [ContinuousAdd H] {C : Set H} (hC : ConvexCone C) :
    ConvexCone (closure C) ∧ IsComplete (closure C) :=
  ⟨convexCone_closure hC, convexCone_closure_isComplete⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (ii).

Original label: `thm:closed-convex-cone-closure-projection`, metric-projection
existence clause.

Informal statement: every point has a closest point in a nonempty closed convex
cone of a real Hilbert space.

Lean strategy / thesis relation note: this invokes mathlib's Hilbert projection theorem
`exists_norm_eq_iInf_of_complete_convex`, whose proof is the standard Cauchy
minimizing-sequence argument. The thesis states this theorem as background.
-/
theorem closedConvexCone_metricProjection_exists {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : ConvexCone C) (hclosed : IsClosed C)
    (hne : C.Nonempty) (u : H) :
    ∃ p ∈ C, ‖u - p‖ = ⨅ w : C, ‖u - (w : H)‖ :=
  exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete
    (convex_of_convexCone hC) u

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (ii).

Original label: uniqueness step for
`thm:closed-convex-cone-closure-projection`.

Informal statement: the closest point in a convex subset of a real Hilbert
space is unique.

Lean strategy / thesis relation note: mathlib supplies the variational characterization of a
minimizer. The proof below is the standard Hilbert-space calculation: applying
the characterization in both directions forces `⟪p - q, p - q⟫ ≤ 0`, hence
`p=q`.
-/
theorem convexSet_metricProjection_minimizer_unique {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {C : Set H}
    (hconv : Convex ℝ C) {u p q : H} (hpC : p ∈ C) (hqC : q ∈ C)
    (hp : ‖u - p‖ = ⨅ w : C, ‖u - (w : H)‖)
    (hq : ‖u - q‖ = ⨅ w : C, ‖u - (w : H)‖) : p = q := by
  have hpq : inner ℝ (u - p) (q - p) ≤ 0 :=
    ((norm_eq_iInf_iff_real_inner_le_zero hconv hpC).mp hp) q hqC
  have hqp : inner ℝ (u - q) (p - q) ≤ 0 :=
    ((norm_eq_iInf_iff_real_inner_le_zero hconv hqC).mp hq) p hpC
  have hpq_nonneg : 0 ≤ inner ℝ (u - p) (p - q) := by
    have hneg : inner ℝ (u - p) (-(p - q)) ≤ 0 := by
      simpa [neg_sub] using hpq
    rw [inner_neg_right] at hneg
    exact neg_nonpos.mp hneg
  have hdecomp : u - q = (u - p) + (p - q) := by
    abel
  rw [hdecomp, inner_add_left] at hqp
  have hself_nonneg : 0 ≤ inner ℝ (p - q) (p - q) := by
    simpa only [RCLike.re_to_real] using
      (inner_self_nonneg (𝕜 := ℝ) (x := p - q))
  have hself_le_zero : inner ℝ (p - q) (p - q) ≤ 0 := by
    linarith
  have hself_eq_zero : inner ℝ (p - q) (p - q) = 0 :=
    le_antisymm hself_le_zero hself_nonneg
  have hzero : p - q = 0 := (inner_self_eq_zero).mp hself_eq_zero
  exact sub_eq_zero.mp hzero

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (ii).

Original label: `thm:closed-convex-cone-closure-projection`, metric-projection
map.

Informal statement: the metric projection onto a nonempty closed convex cone is
the chosen closest point.

Lean strategy / thesis relation note: Lean's `Classical.choose` materializes
the `argmin` selected by the Hilbert projection theorem. The uniqueness theorem
below shows this choice is independent of the witness.
-/
noncomputable def closedConvexConeMetricProjection {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : ConvexCone C) (hclosed : IsClosed C)
    (hne : C.Nonempty) (u : H) : C :=
  let h := closedConvexCone_metricProjection_exists hC hclosed hne u
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (ii).

Original label: specification of
`thm:closed-convex-cone-closure-projection`.

Informal statement: the selected projection point attains the infimum distance.
-/
theorem closedConvexConeMetricProjection_spec {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : ConvexCone C) (hclosed : IsClosed C)
    (hne : C.Nonempty) (u : H) :
    ‖u - (closedConvexConeMetricProjection hC hclosed hne u : H)‖ =
      ⨅ w : C, ‖u - (w : H)‖ := by
  let h := closedConvexCone_metricProjection_exists hC hclosed hne u
  exact (Classical.choose_spec h).2

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (ii).

Original label: `thm:closed-convex-cone-closure-projection`, well-definedness
clause.

Informal statement: the metric projection is well defined: there exists a
unique closest point.
-/
theorem closedConvexCone_metricProjection_existsUnique {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : ConvexCone C) (hclosed : IsClosed C)
    (hne : C.Nonempty) (u : H) :
    ∃! p : H, p ∈ C ∧ ‖u - p‖ = ⨅ w : C, ‖u - (w : H)‖ := by
  let P := closedConvexConeMetricProjection hC hclosed hne u
  refine ⟨P, ⟨P.property, closedConvexConeMetricProjection_spec hC hclosed hne u⟩, ?_⟩
  intro q hq
  exact (convexSet_metricProjection_minimizer_unique (convex_of_convexCone hC)
    P.property hq.1
    (closedConvexConeMetricProjection_spec hC hclosed hne u) hq.2).symm

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (ii).

Original label: variational form of
`thm:closed-convex-cone-closure-projection`.

Informal statement: a point of the cone is the metric projection precisely when
it satisfies the Hilbert projection variational inequality.
-/
theorem closedConvexConeMetricProjection_eq_of_inner_nonpos {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : ConvexCone C) (hclosed : IsClosed C)
    (hne : C.Nonempty) {u p : H} (hpC : p ∈ C)
    (hinner : ∀ w ∈ C, inner ℝ (u - p) (w - p) ≤ 0) :
    (closedConvexConeMetricProjection hC hclosed hne u : H) = p := by
  have hconv : Convex ℝ C := convex_of_convexCone hC
  have hpmin : ‖u - p‖ = ⨅ w : C, ‖u - (w : H)‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero hconv hpC).mpr hinner
  exact convexSet_metricProjection_minimizer_unique hconv
    (closedConvexConeMetricProjection hC hclosed hne u).property hpC
    (closedConvexConeMetricProjection_spec hC hclosed hne u) hpmin

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (iii).

Original label: `thm:closed-convex-cone-closure-projection`, idempotence
clause.

Informal statement: projecting a point already in the cone leaves it fixed;
therefore `P ∘ P = P`.
-/
theorem closedConvexConeMetricProjection_idempotent {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : ConvexCone C) (hclosed : IsClosed C)
    (hne : C.Nonempty) (u : H) :
    closedConvexConeMetricProjection hC hclosed hne
        (closedConvexConeMetricProjection hC hclosed hne u : H) =
      closedConvexConeMetricProjection hC hclosed hne u := by
  apply Subtype.ext
  exact closedConvexConeMetricProjection_eq_of_inner_nonpos hC hclosed hne
    (closedConvexConeMetricProjection hC hclosed hne u).property (by
      intro w _hw
      simp)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:closed-convex-cone-closure-projection`, part (iii).

Original label: `thm:closed-convex-cone-closure-projection`, positive
homogeneity clause.

Informal statement: projection onto a closed convex cone commutes with
nonnegative scalar multiplication.
-/
theorem closedConvexConeMetricProjection_positiveHomogeneous {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : ConvexCone C) (hclosed : IsClosed C)
    (hne : C.Nonempty) {α : ℝ} (hα : 0 ≤ α) (u : H) :
    closedConvexConeMetricProjection hC hclosed hne (α • u) =
      ⟨α • (closedConvexConeMetricProjection hC hclosed hne u : H),
        by
          have h := hC
            (closedConvexConeMetricProjection hC hclosed hne u).property
            (closedConvexConeMetricProjection hC hclosed hne u).property
            hα le_rfl
          simpa [zero_smul, add_zero] using h⟩ := by
  by_cases hαzero : α = 0
  · subst α
    simp only [zero_smul]
    apply Subtype.ext
    exact closedConvexConeMetricProjection_eq_of_inner_nonpos hC hclosed hne
      (convexCone_zero_mem_of_nonempty hC hne) (by
        intro w _hw
        simp)
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hαzero)
    apply Subtype.ext
    apply closedConvexConeMetricProjection_eq_of_inner_nonpos hC hclosed hne
    · have h := hC
        (closedConvexConeMetricProjection hC hclosed hne u).property
        (closedConvexConeMetricProjection hC hclosed hne u).property
        hα le_rfl
      simpa [zero_smul, add_zero] using h
    · intro w hw
      let p := (closedConvexConeMetricProjection hC hclosed hne u : H)
      have hwinv : α⁻¹ • w ∈ C := by
        have h := hC hw hw (inv_nonneg.mpr hα) le_rfl
        simpa [zero_smul, add_zero] using h
      have hvar : inner ℝ (u - p) (α⁻¹ • w - p) ≤ 0 := by
        have hspec := closedConvexConeMetricProjection_spec hC hclosed hne u
        exact ((norm_eq_iInf_iff_real_inner_le_zero
          (convex_of_convexCone hC)
          (closedConvexConeMetricProjection hC hclosed hne u).property).mp hspec)
          (α⁻¹ • w) hwinv
      have hleft : α • u - α • p = α • (u - p) := by
        rw [smul_sub]
      have hright : w - α • p = α • (α⁻¹ • w - p) := by
        rw [smul_sub, smul_smul]
        rw [mul_inv_cancel₀ hαzero, one_smul]
      rw [hleft, hright, inner_smul_left, inner_smul_right, starRingEnd_apply,
        TrivialStar.star_trivial]
      nlinarith [mul_nonneg hα hα, hvar]

/-! ## Grothendieck Vectorization of Weakly Convex Operators -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: auxiliary zero lemma for
`thm:grothendieck-vectorization-is-span`.

Informal statement: the image of a weakly convex operator contains `0`.
-/
theorem weakConvex_range_zero_mem {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    (0 : V) ∈ Set.range φ := by
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨z, hz⟩ := hφ (α := 0) (β := 0) le_rfl le_rfl x0 x0
  refine ⟨z, ?_⟩
  simpa using hz

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: auxiliary addition lemma for
`thm:grothendieck-vectorization-is-span`.

Informal statement: the image cone of a weakly convex operator is closed under
addition.
-/
theorem weakConvex_range_add_mem {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    {a b : V} (ha : a ∈ Set.range φ) (hb : b ∈ Set.range φ) :
    a + b ∈ Set.range φ := by
  rcases ha with ⟨x, rfl⟩
  rcases hb with ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hφ (α := 1) (β := 1) (by norm_num) (by norm_num) x y
  refine ⟨z, ?_⟩
  simpa using hz

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: auxiliary scalar lemma for
`thm:grothendieck-vectorization-is-span`.

Informal statement: the image cone of a weakly convex operator is closed under
nonnegative scalar multiplication.
-/
theorem weakConvex_range_smul_mem {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    {α : ℝ} (hα : 0 ≤ α) {a : V} (ha : a ∈ Set.range φ) :
    α • a ∈ Set.range φ := by
  rcases ha with ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hφ (α := α) (β := 0) hα le_rfl x x
  refine ⟨z, ?_⟩
  simpa [zero_smul, add_zero] using hz

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: image map used in
`thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: `Φ` sends an element of the weak-convex quotient `X_φ` to
its representative in the image cone `φ(X)`.
-/
noncomputable def weakConvexKernelImage {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (q : WeakConvexKernelSpace φ hφ) : V :=
  ((weakConvexKernelSpaceEquivRange φ hφ q).1 : V)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: pair space in
`thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: the Grothendieck construction starts from pairs
`X_φ × X_φ`.
-/
abbrev GrothendieckPair {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :=
  WeakConvexKernelSpace φ hφ × WeakConvexKernelSpace φ hφ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: relation defining
`thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: `(x,z) ~ (x',z')` iff `x + z' = x' + z`, transported to
the ambient vector space through `Φ`.

Lean strategy / thesis relation note: Lean states the relation on quotient representatives using the
image map `Φ`; the transported cone operations above justify the same
`Φ^{-1}` formulas used in the thesis.
-/
def grothendieckRel {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (p q : GrothendieckPair φ hφ) : Prop :=
  weakConvexKernelImage φ hφ p.1 + weakConvexKernelImage φ hφ q.2 =
    weakConvexKernelImage φ hφ q.1 + weakConvexKernelImage φ hφ p.2

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: equivalence-relation part of
`thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: the Grothendieck relation on pairs is an equivalence
relation.
-/
theorem grothendieckRel_equivalence {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Equivalence (grothendieckRel φ hφ) := by
  refine ⟨?refl, ?symm, ?trans⟩
  · intro p
    rfl
  · intro p q hpq
    exact hpq.symm
  · intro p q r hpq hqr
    dsimp [grothendieckRel] at hpq hqr ⊢
    calc
      weakConvexKernelImage φ hφ p.1 + weakConvexKernelImage φ hφ r.2 =
          (weakConvexKernelImage φ hφ p.1 + weakConvexKernelImage φ hφ q.2) +
            (weakConvexKernelImage φ hφ r.2 - weakConvexKernelImage φ hφ q.2) := by
            abel
      _ = weakConvexKernelImage φ hφ q.1 + weakConvexKernelImage φ hφ p.2 +
            (weakConvexKernelImage φ hφ r.2 - weakConvexKernelImage φ hφ q.2) := by
            rw [hpq]
      _ = (weakConvexKernelImage φ hφ q.1 + weakConvexKernelImage φ hφ r.2) +
            (weakConvexKernelImage φ hφ p.2 - weakConvexKernelImage φ hφ q.2) := by
            abel
      _ = weakConvexKernelImage φ hφ r.1 + weakConvexKernelImage φ hφ q.2 +
            (weakConvexKernelImage φ hφ p.2 - weakConvexKernelImage φ hφ q.2) := by
            rw [hqr]
      _ = weakConvexKernelImage φ hφ r.1 + weakConvexKernelImage φ hφ p.2 := by
            abel

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: setoid for
`thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: the Grothendieck relation is bundled as a Lean `Setoid`.
-/
def grothendieckSetoid {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Setoid (GrothendieckPair φ hφ) where
  r := grothendieckRel φ hφ
  iseqv := grothendieckRel_equivalence φ hφ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: `thm:grothendieck-vector-space-from-convex-cone`, quotient
space.

Informal statement: `𝓥(X,φ)` is the quotient of `X_φ × X_φ` by the
Grothendieck relation.
-/
def GrothendieckVectorization {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :=
  Quotient (grothendieckSetoid φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: difference submodule used in
`thm:grothendieck-vectorization-is-span`.

Informal statement: differences of two points in the image cone form a
submodule of the ambient vector space.

Lean strategy / thesis relation note: this is the formal counterpart of the
thesis' positive/negative coefficient split. For negative scalars Lean swaps
the two cone components, matching the displayed scalar rule in the manuscript.
-/
noncomputable def grothendieckDifferenceSubmodule {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) : Submodule ℝ V where
  carrier := {v | ∃ a ∈ Set.range φ, ∃ b ∈ Set.range φ, a - b = v}
  zero_mem' := by
    exact ⟨0, weakConvex_range_zero_mem φ hφ, 0, weakConvex_range_zero_mem φ hφ,
      by simp⟩
  add_mem' := by
    rintro v w ⟨a, ha, b, hb, hv⟩ ⟨c, hc, d, hd, hw⟩
    refine ⟨a + c, weakConvex_range_add_mem φ hφ ha hc,
      b + d, weakConvex_range_add_mem φ hφ hb hd, ?_⟩
    rw [← hv, ← hw]
    abel
  smul_mem' := by
    intro r v hv
    rcases hv with ⟨a, ha, b, hb, hv⟩
    by_cases hr : 0 ≤ r
    · refine ⟨r • a, weakConvex_range_smul_mem φ hφ hr ha,
        r • b, weakConvex_range_smul_mem φ hφ hr hb, ?_⟩
      rw [← smul_sub, hv]
    · have hrneg : r < 0 := lt_of_not_ge hr
      refine ⟨|r| • b, weakConvex_range_smul_mem φ hφ (abs_nonneg r) hb,
        |r| • a, weakConvex_range_smul_mem φ hφ (abs_nonneg r) ha, ?_⟩
      rw [abs_of_neg hrneg, ← smul_sub, ← hv]
      module

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: span-identification lemma for
`thm:grothendieck-vectorization-is-span`.

Informal statement: the submodule of all differences of image-cone elements is
exactly `span φ(X)`.
-/
theorem grothendieckDifferenceSubmodule_eq_span {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    grothendieckDifferenceSubmodule φ hφ = Submodule.span ℝ (Set.range φ) := by
  apply le_antisymm
  · intro v hv
    rcases hv with ⟨a, ha, b, hb, hv⟩
    rw [← hv]
    exact Submodule.sub_mem _ (Submodule.subset_span ha) (Submodule.subset_span hb)
  · rw [Submodule.span_le]
    intro v hv
    exact ⟨v, hv, 0, weakConvex_range_zero_mem φ hφ, by simp⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: map `T` in `thm:grothendieck-vectorization-is-span`.

Informal statement: `T([(x,z)]) = Φ(x) - Φ(z)`.
-/
noncomputable def grothendieckToSpan {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    GrothendieckVectorization φ hφ → Submodule.span ℝ (Set.range φ) :=
  Quotient.lift
    (fun p : GrothendieckPair φ hφ =>
      ⟨weakConvexKernelImage φ hφ p.1 - weakConvexKernelImage φ hφ p.2,
        Submodule.sub_mem _
          (Submodule.subset_span
            (weakConvexKernelSpaceEquivRange φ hφ p.1).property)
          (Submodule.subset_span
            (weakConvexKernelSpaceEquivRange φ hφ p.2).property)⟩)
    (by
      intro p q hpq
      apply Subtype.ext
      calc
        weakConvexKernelImage φ hφ p.1 - weakConvexKernelImage φ hφ p.2 =
            (weakConvexKernelImage φ hφ p.1 +
              weakConvexKernelImage φ hφ q.2) -
              (weakConvexKernelImage φ hφ p.2 +
                weakConvexKernelImage φ hφ q.2) := by
              abel
        _ = (weakConvexKernelImage φ hφ q.1 +
              weakConvexKernelImage φ hφ p.2) -
              (weakConvexKernelImage φ hφ p.2 +
                weakConvexKernelImage φ hφ q.2) := by
              rw [hpq]
        _ = weakConvexKernelImage φ hφ q.1 -
            weakConvexKernelImage φ hφ q.2 := by
              abel)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: displayed formula for `T` in
`thm:grothendieck-vectorization-is-span`.

Informal statement: on a pair representative, the span map is
`T([(x,z)]) = Φ(x) - Φ(z)`.
-/
@[simp]
theorem grothendieckToSpan_pairRepresentative_formula {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (p : GrothendieckPair φ hφ) :
    ((grothendieckToSpan φ hφ
      (Quotient.mk (grothendieckSetoid φ hφ) p)) : V) =
      weakConvexKernelImage φ hφ p.1 -
        weakConvexKernelImage φ hφ p.2 :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: injectivity of `T` in
`thm:grothendieck-vectorization-is-span`.

Informal statement: if two formal differences have the same value in the span,
then their pair representatives are Grothendieck-equivalent.
-/
theorem grothendieckToSpan_injective {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Function.Injective (grothendieckToSpan φ hφ) := by
  intro q r hqr
  refine Quotient.inductionOn₂ q r ?_ hqr
  intro p s hps
  apply Quotient.sound
  change grothendieckRel φ hφ p s
  have hval : weakConvexKernelImage φ hφ p.1 - weakConvexKernelImage φ hφ p.2 =
      weakConvexKernelImage φ hφ s.1 - weakConvexKernelImage φ hφ s.2 :=
    congrArg Subtype.val hps
  calc
    weakConvexKernelImage φ hφ p.1 + weakConvexKernelImage φ hφ s.2 =
        (weakConvexKernelImage φ hφ p.1 - weakConvexKernelImage φ hφ p.2) +
          (weakConvexKernelImage φ hφ p.2 + weakConvexKernelImage φ hφ s.2) := by
          abel
    _ = (weakConvexKernelImage φ hφ s.1 - weakConvexKernelImage φ hφ s.2) +
          (weakConvexKernelImage φ hφ p.2 + weakConvexKernelImage φ hφ s.2) := by
          rw [hval]
    _ = weakConvexKernelImage φ hφ s.1 + weakConvexKernelImage φ hφ p.2 := by
          abel

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: surjectivity of `T` in
`thm:grothendieck-vectorization-is-span`.

Informal statement: every element of `span φ(X)` is a formal difference of two
points in the image cone.
-/
theorem grothendieckToSpan_surjective {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Function.Surjective (grothendieckToSpan φ hφ) := by
  intro v
  have hvdiff : (v : V) ∈ grothendieckDifferenceSubmodule φ hφ := by
    rw [grothendieckDifferenceSubmodule_eq_span φ hφ]
    exact v.property
  rcases hvdiff with ⟨a, ha, b, hb, hv⟩
  let e := weakConvexKernelSpaceEquivRange φ hφ
  let p : GrothendieckPair φ hφ := (e.symm ⟨a, ha⟩, e.symm ⟨b, hb⟩)
  refine ⟨Quotient.mk (grothendieckSetoid φ hφ) p, ?_⟩
  apply Subtype.ext
  have ha' : weakConvexKernelImage φ hφ (e.symm ⟨a, ha⟩) = a := by
    dsimp [weakConvexKernelImage, e]
    simp
  have hb' : weakConvexKernelImage φ hφ (e.symm ⟨b, hb⟩) = b := by
    dsimp [weakConvexKernelImage, e]
    simp
  change weakConvexKernelImage φ hφ (e.symm ⟨a, ha⟩) -
      weakConvexKernelImage φ hφ (e.symm ⟨b, hb⟩) = (v : V)
  rw [ha', hb', hv]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: `thm:grothendieck-vectorization-is-span`.

Informal statement: the Grothendieck vectorization is equivalent to
`span φ(X)`.
-/
noncomputable def grothendieckVectorizationEquivSpan {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    GrothendieckVectorization φ hφ ≃ Submodule.span ℝ (Set.range φ) :=
  Equiv.ofBijective (grothendieckToSpan φ hφ)
    ⟨grothendieckToSpan_injective φ hφ, grothendieckToSpan_surjective φ hφ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: displayed formula for the equivalence `T`.

Informal statement: the equivalence with the span agrees with the quotient-lift
map `T` on pair representatives.
-/
@[simp]
theorem grothendieckVectorizationEquivSpan_pairRepresentative_formula {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (p : GrothendieckPair φ hφ) :
    ((grothendieckVectorizationEquivSpan φ hφ
      (Quotient.mk (grothendieckSetoid φ hφ) p)) : V) =
      weakConvexKernelImage φ hφ p.1 -
        weakConvexKernelImage φ hφ p.2 :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: additive structure in
`thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: addition and additive inverses on the Grothendieck
quotient are transported from `span φ(X)`.
-/
noncomputable instance grothendieckVectorization_addCommGroup {X : Type u}
    {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    AddCommGroup (GrothendieckVectorization φ hφ) :=
  Equiv.addCommGroup (grothendieckVectorizationEquivSpan φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: scalar structure in
`thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: real scalar multiplication on the Grothendieck quotient is
transported from `span φ(X)`.
-/
noncomputable instance grothendieckVectorization_module {X : Type u}
    {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Module ℝ (GrothendieckVectorization φ hφ) :=
  Equiv.module ℝ (grothendieckVectorizationEquivSpan φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: `thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: the Grothendieck quotient of a weakly convex operator
carries a real vector-space structure.

Lean strategy / thesis relation note: the manuscript writes the addition and scalar multiplication
formulas directly on pair classes. Lean obtains the same algebra by first
identifying the quotient with `span φ(X)` and transporting the vector-space
typeclasses along that equivalence.
-/
theorem grothendieck_vectorSpace_from_convexCone {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Nonempty (GrothendieckVectorization φ hφ ≃ Submodule.span ℝ (Set.range φ)) :=
  ⟨grothendieckVectorizationEquivSpan φ hφ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: `thm:grothendieck-vectorization-is-span`, linear-isomorphism
form.

Informal statement: the map `T([(x,z)]) = Φ(x)-Φ(z)` is a linear isomorphism
from the Grothendieck vectorization to `span φ(X)`.
-/
noncomputable def grothendieckVectorizationLinearEquivSpan {X : Type u}
    {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    GrothendieckVectorization φ hφ ≃ₗ[ℝ] Submodule.span ℝ (Set.range φ) where
  toFun := grothendieckVectorizationEquivSpan φ hφ
  invFun := (grothendieckVectorizationEquivSpan φ hφ).symm
  left_inv := (grothendieckVectorizationEquivSpan φ hφ).left_inv
  right_inv := (grothendieckVectorizationEquivSpan φ hφ).right_inv
  map_add' := by
    intro x y
    let e := grothendieckVectorizationEquivSpan φ hφ
    change e (x + y) = e x + e y
    change e (e.symm (e x + e y)) = e x + e y
    simp
  map_smul' := by
    intro r x
    let e := grothendieckVectorizationEquivSpan φ hφ
    change e (r • x) = r • e x
    change e (e.symm (r • e x)) = r • e x
    simp

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: displayed addition formula in
`thm:grothendieck-vector-space-from-convex-cone`.

Informal statement: addition of Grothendieck pair classes agrees with adding
the two positive components and the two negative components, using the
transported cone addition on `X_φ`.
-/
theorem grothendieckVectorization_additionOfPairRepresentatives {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (p q : GrothendieckPair φ hφ) :
    (grothendieckVectorizationEquivSpan φ hφ).symm
      (grothendieckVectorizationEquivSpan φ hφ
          (Quotient.mk (grothendieckSetoid φ hφ) p) +
        grothendieckVectorizationEquivSpan φ hφ
          (Quotient.mk (grothendieckSetoid φ hφ) q)) =
        (Quotient.mk (grothendieckSetoid φ hφ)
          (weakConvexKernelAdd φ hφ p.1 q.1,
            weakConvexKernelAdd φ hφ p.2 q.2) :
          GrothendieckVectorization φ hφ) := by
  let e := grothendieckVectorizationEquivSpan φ hφ
  apply e.injective
  apply Subtype.ext
  simp [e, weakConvexKernelImage, weakConvexKernelAdd_image]
  abel_nf

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: displayed scalar formula for nonnegative scalars in
`thm:grothendieck-vector-space-from-convex-cone`.
-/
theorem grothendieckVectorization_scalarMultiplicationOfPairRepresentative_nonnegative
    {X : Type u} {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    {α : ℝ} (hα : 0 ≤ α) (p : GrothendieckPair φ hφ) :
    (grothendieckVectorizationEquivSpan φ hφ).symm
      (α • grothendieckVectorizationEquivSpan φ hφ
        (Quotient.mk (grothendieckSetoid φ hφ) p)) =
      (Quotient.mk (grothendieckSetoid φ hφ)
        (weakConvexKernelNonnegativeScalarMultiplication φ hφ α hα p.1,
          weakConvexKernelNonnegativeScalarMultiplication φ hφ α hα p.2) :
        GrothendieckVectorization φ hφ) := by
  let e := grothendieckVectorizationEquivSpan φ hφ
  apply e.injective
  apply Subtype.ext
  rw [Equiv.apply_symm_apply]
  change α •
      (weakConvexKernelImage φ hφ p.1 -
        weakConvexKernelImage φ hφ p.2) =
    weakConvexKernelImage φ hφ
        (weakConvexKernelNonnegativeScalarMultiplication φ hφ α hα p.1) -
      weakConvexKernelImage φ hφ
        (weakConvexKernelNonnegativeScalarMultiplication φ hφ α hα p.2)
  unfold weakConvexKernelImage
  rw [weakConvexKernelNonnegativeScalarMultiplication_image,
    weakConvexKernelNonnegativeScalarMultiplication_image, smul_sub]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vector-space-from-convex-cone`.

Original label: displayed scalar formula for negative scalars in
`thm:grothendieck-vector-space-from-convex-cone`.
-/
theorem grothendieckVectorization_scalarMultiplicationOfPairRepresentative_negative
    {X : Type u} {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    {α : ℝ} (hα : α < 0) (p : GrothendieckPair φ hφ) :
    (grothendieckVectorizationEquivSpan φ hφ).symm
      (α • grothendieckVectorizationEquivSpan φ hφ
        (Quotient.mk (grothendieckSetoid φ hφ) p)) =
      (Quotient.mk (grothendieckSetoid φ hφ)
        (weakConvexKernelNonnegativeScalarMultiplication φ hφ |α| (abs_nonneg α) p.2,
          weakConvexKernelNonnegativeScalarMultiplication φ hφ |α| (abs_nonneg α) p.1) :
        GrothendieckVectorization φ hφ) := by
  let e := grothendieckVectorizationEquivSpan φ hφ
  apply e.injective
  apply Subtype.ext
  simp [e, weakConvexKernelImage,
    weakConvexKernelNonnegativeScalarMultiplication_image, abs_of_neg hα]
  module

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:grothendieck-vectorization-is-span`.

Original label: `thm:grothendieck-vectorization-is-span`.

Informal statement: the Grothendieck vectorization is linearly isomorphic to
`span φ(X)`.
-/
theorem grothendieck_vectorization_is_span {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Nonempty (GrothendieckVectorization φ hφ ≃ₗ[ℝ]
      Submodule.span ℝ (Set.range φ)) :=
  ⟨grothendieckVectorizationLinearEquivSpan φ hφ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: inner-product formula in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the inner product on the vectorization is pulled back from
the ambient inner product on `span φ(X)` along the linear isomorphism `T`.
-/
noncomputable def grothendieckVectorizationInner {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    GrothendieckVectorization φ hφ → GrothendieckVectorization φ hφ → ℝ :=
  fun q r => inner ℝ
    (grothendieckVectorizationEquivSpan φ hφ q)
    (grothendieckVectorizationEquivSpan φ hφ r)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: transported inner-product core for
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the pulled-back form satisfies the inner-product axioms.
-/
@[reducible]
noncomputable def grothendieckVectorizationInnerCore {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    InnerProductSpace.Core ℝ (GrothendieckVectorization φ hφ) where
  inner := grothendieckVectorizationInner φ hφ
  conj_inner_symm := by
    intro x y
    exact inner_conj_symm _ _
  re_inner_nonneg := by
    intro x
    exact inner_self_nonneg
  add_left := by
    intro x y z
    let e := grothendieckVectorizationEquivSpan φ hφ
    have hmap : e (x + y) = e x + e y := by
      change e (e.symm (e x + e y)) = e x + e y
      simp
    change inner ℝ (e (x + y)) (e z) =
      inner ℝ (e x) (e z) + inner ℝ (e y) (e z)
    rw [hmap]
    simpa using inner_add_left (e x) (e y) (e z)
  smul_left := by
    intro x y r
    let e := grothendieckVectorizationEquivSpan φ hφ
    have hmap : e (r • x) = r • e x := by
      change e (e.symm (r • e x)) = r • e x
      simp
    change inner ℝ (e (r • x)) (e y) =
      (starRingEnd ℝ) r * inner ℝ (e x) (e y)
    rw [hmap]
    simpa using inner_smul_left (e x) (e y) r
  definite := by
    intro x hx
    let e := grothendieckVectorizationEquivSpan φ hφ
    have hxspan : e x = 0 := by
      exact (inner_self_eq_zero (𝕜 := ℝ)
        (E := Submodule.span ℝ (Set.range φ))).mp hx
    have hzero : e 0 = 0 := by
      change e (e.symm 0) = 0
      simp
    exact (Equiv.injective e) (hxspan.trans hzero.symm)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: normed additive-group part of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the induced inner-product core supplies the compatible
normed additive-group structure.
-/
noncomputable instance grothendieckVectorization_normedAddCommGroup
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    NormedAddCommGroup (GrothendieckVectorization φ hφ) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := grothendieckVectorizationInnerCore φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: inner-product-space part of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the Grothendieck vectorization carries the induced real
inner-product-space structure.
-/
noncomputable instance grothendieckVectorization_innerProductSpace
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    InnerProductSpace ℝ (GrothendieckVectorization φ hφ) :=
  InnerProductSpace.ofCore (grothendieckVectorizationInnerCore φ hφ).toCore

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: isometry part of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: `T` is an isometric linear isomorphism.
-/
noncomputable def grothendieckVectorizationLinearIsometryEquivSpan
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    GrothendieckVectorization φ hφ ≃ₗᵢ[ℝ]
      Submodule.span ℝ (Set.range φ) where
  toLinearEquiv := grothendieckVectorizationLinearEquivSpan φ hφ
  norm_map' := by
    intro x
    let e := grothendieckVectorizationEquivSpan φ hφ
    change ‖e x‖ = ‖x‖
    rw [norm_eq_sqrt_real_inner (x := e x), norm_eq_sqrt_real_inner (x := x)]
    rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: first clause of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the vectorization is an inner-product space and `T` is an
isometric linear isomorphism onto `span φ(X)`.
-/
theorem grothendieck_vectorization_innerProductSpace_and_isometry
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Nonempty (GrothendieckVectorization φ hφ ≃ₗᵢ[ℝ]
      Submodule.span ℝ (Set.range φ)) :=
  ⟨grothendieckVectorizationLinearIsometryEquivSpan φ hφ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: completion object in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the completed Grothendieck vectorization is the uniform
completion of `𝓥(X,φ)`.
-/
abbrev CompletedGrothendieckVectorization {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :=
  UniformSpace.Completion (GrothendieckVectorization φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: span-completion object in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the comparison target for the completion theorem is the
completion of `span φ(X)`.

Lean strategy / thesis relation note: this matches the revised manuscript
statement: the completion-level extension of `T` targets the completed span.
This is the general Hilbert-space-safe target, since the raw span need not be
closed before completion.
-/
abbrev CompletedGrothendieckSpan {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (_hφ : WeaklyConvexOperator X V φ) :=
  UniformSpace.Completion (Submodule.span ℝ (Set.range φ))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: auxiliary conversion for the completion-isometry clause.

Informal statement: a linear isometric equivalence is, in particular, a uniform
equivalence.
-/
noncomputable def linearIsometryEquiv_toUniformEquiv {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [Module ℝ E] [Module ℝ F] (e : E ≃ₗᵢ[ℝ] F) : E ≃ᵤ F where
  toEquiv := e.toEquiv
  uniformContinuous_toFun := e.isometry.uniformContinuous
  uniformContinuous_invFun := e.symm.isometry.uniformContinuous

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`, completion
clause.

Original label: completion-isomorphism part of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the completions of `𝓥(X,φ)` and `span φ(X)` are uniformly
isomorphic by the completion of `T`.
-/
noncomputable def grothendieckCompletionUniformEquivSpanCompletion
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    CompletedGrothendieckVectorization φ hφ ≃ᵤ
      CompletedGrothendieckSpan φ hφ :=
  UniformSpace.Completion.mapEquiv
    (linearIsometryEquiv_toUniformEquiv
      (grothendieckVectorizationLinearIsometryEquivSpan φ hφ))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`, completion
clause.

Original label: linear isometric completion-isomorphism part of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the completion-level extension of `T` is a linear
isometric isomorphism from the completed vectorization to the completed span.

Lean strategy / thesis relation note: `ContinuousLinearMap.completion` supplies
the linear extension of the original linear isometry, while
`UniformSpace.Completion.mapEquiv` supplies the inverse-map data. The norm
identity is inherited from the original isometry by `Isometry.completion_map`.
-/
noncomputable def grothendieckCompletionLinearIsometryEquivSpanCompletion
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    CompletedGrothendieckVectorization φ hφ ≃ₗᵢ[ℝ]
      CompletedGrothendieckSpan φ hφ where
  toLinearEquiv :=
    { toFun := grothendieckCompletionUniformEquivSpanCompletion φ hφ
      invFun := (grothendieckCompletionUniformEquivSpanCompletion φ hφ).symm
      left_inv := (grothendieckCompletionUniformEquivSpanCompletion φ hφ).left_inv
      right_inv := (grothendieckCompletionUniformEquivSpanCompletion φ hφ).right_inv
      map_add' := by
        intro x y
        let e := grothendieckVectorizationLinearIsometryEquivSpan φ hφ
        let L := e.toContinuousLinearEquiv.toContinuousLinearMap
        change L.completion (x + y) = L.completion x + L.completion y
        exact L.completion.map_add x y
      map_smul' := by
        intro r x
        let e := grothendieckVectorizationLinearIsometryEquivSpan φ hφ
        let L := e.toContinuousLinearEquiv.toContinuousLinearMap
        change L.completion (r • x) = r • L.completion x
        exact L.completion.map_smul r x }
  norm_map' := by
    intro x
    let e := grothendieckVectorizationLinearIsometryEquivSpan φ hφ
    let L := e.toContinuousLinearEquiv.toContinuousLinearMap
    change ‖L.completion x‖ = ‖x‖
    have hdist : dist (L.completion x) (L.completion 0) = dist x 0 := by
      change dist (UniformSpace.Completion.map (⇑e) x)
          (UniformSpace.Completion.map (⇑e) 0) = dist x 0
      exact Isometry.dist_eq e.isometry.completion_map x 0
    have hzero : L.completion (0 : CompletedGrothendieckVectorization φ hφ) = 0 := by
      exact L.completion.map_zero
    rw [hzero] at hdist
    simpa [dist_zero_right] using hdist

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`, completion
clause.

Original label: completed-span wrapper for the completion-isomorphism clause.

Informal statement: the canonical extension of `T` identifies the completed
vectorization with the completed span by a linear isometric isomorphism,
matching the revised thesis target.
-/
theorem grothendieck_completion_targets_completedSpan
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Nonempty (CompletedGrothendieckVectorization φ hφ ≃ₗᵢ[ℝ]
      CompletedGrothendieckSpan φ hφ) :=
  ⟨grothendieckCompletionLinearIsometryEquivSpanCompletion φ hφ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`, completion
clause.

Original label: isometry extension part of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the completion map induced by `T` is an isometry.
-/
theorem grothendieckCompletionToSpanCompletion_isometry
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Isometry (UniformSpace.Completion.map
      (grothendieckVectorizationLinearIsometryEquivSpan φ hφ)) :=
  (grothendieckVectorizationLinearIsometryEquivSpan φ hφ).isometry.completion_map

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`, completion
clause.

Original label: completeness part of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the completed Grothendieck vectorization is complete.
-/
theorem completedGrothendieckVectorization_complete {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    CompleteSpace (CompletedGrothendieckVectorization φ hφ) :=
  UniformSpace.Completion.completeSpace (GrothendieckVectorization φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`, completion
clause.

Original label: span-completion completeness part of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the completed span is complete.
-/
theorem completedGrothendieckSpan_complete {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    CompleteSpace (CompletedGrothendieckSpan φ hφ) :=
  UniformSpace.Completion.completeSpace (Submodule.span ℝ (Set.range φ))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: zero representative used in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the weak-convex kernel quotient has a distinguished zero
element, namely the quotient class whose image under `Φ` is the origin.

Lean strategy / thesis relation note: weak convexity only gives a cone, not a
vector space, so this is not a typeclass zero on `X_φ`. It is the explicit zero
element of the image cone used to embed `X_φ` into its Grothendieck
vectorization by `x ↦ [(x,0)]`.
-/
noncomputable def weakConvexKernelZero {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    WeakConvexKernelSpace φ hφ :=
  (weakConvexKernelSpaceEquivRange φ hφ).symm
    ⟨0, weakConvex_range_zero_mem φ hφ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: zero representative used in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the distinguished weak-convex zero maps to the ambient
origin.
-/
@[simp]
theorem weakConvexKernelImage_zero {X : Type u} {V : Type v}
    [AddCommMonoid V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    weakConvexKernelImage φ hφ (weakConvexKernelZero φ hφ) = 0 := by
  dsimp [weakConvexKernelZero, weakConvexKernelImage]
  simp

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: cone embedding in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the original weak-convex kernel cone embeds into the
Grothendieck vectorization by sending `x` to the formal difference `[(x,0)]`.
-/
noncomputable def grothendieckConeEmbedding {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (q : WeakConvexKernelSpace φ hφ) : GrothendieckVectorization φ hφ :=
  Quotient.mk (grothendieckSetoid φ hφ)
    (q, weakConvexKernelZero φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: cone embedding calculation in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: under the span isomorphism `T([(x,z)]) = Φ(x)-Φ(z)`, the
embedded cone point `[(x,0)]` maps to `Φ(x)`.
-/
@[simp]
theorem grothendieckVectorizationEquivSpan_coneEmbedding {X : Type u}
    {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (q : WeakConvexKernelSpace φ hφ) :
    ((grothendieckVectorizationEquivSpan φ hφ
        (grothendieckConeEmbedding φ hφ q)) : V) =
      weakConvexKernelImage φ hφ q := by
  change weakConvexKernelImage φ hφ q -
      weakConvexKernelImage φ hφ (weakConvexKernelZero φ hφ) =
    weakConvexKernelImage φ hφ q
  simp

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: embedded cone in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the cone inside the Grothendieck vectorization is the image
of `X_φ` under `x ↦ [(x,0)]`.
-/
def grothendieckVectorizationCone {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Set (GrothendieckVectorization φ hφ) :=
  Set.range (grothendieckConeEmbedding φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: cone property in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the embedded copy of the weak-convex kernel space is a
convex cone in the Grothendieck vectorization.

Lean strategy / thesis relation note: the proof follows the thesis' quotient construction. We test
equality of formal sums through the isomorphism `T`, where the statement becomes
the original weak convexity of `φ(X)`.
-/
theorem grothendieckVectorizationCone_convexCone {X : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    ConvexCone (grothendieckVectorizationCone φ hφ) := by
  intro c d hc hd α β hα hβ
  rcases hc with ⟨q, rfl⟩
  rcases hd with ⟨r, rfl⟩
  let a := weakConvexKernelImage φ hφ q
  let b := weakConvexKernelImage φ hφ r
  have ha : a ∈ Set.range φ := by
    dsimp [a, weakConvexKernelImage]
    exact (weakConvexKernelSpaceEquivRange φ hφ q).property
  have hb : b ∈ Set.range φ := by
    dsimp [b, weakConvexKernelImage]
    exact (weakConvexKernelSpaceEquivRange φ hφ r).property
  have hcombo : α • a + β • b ∈ Set.range φ :=
    ((weaklyConvexOperator_iff_range_convexCone φ).mp hφ) ha hb hα hβ
  let s : WeakConvexKernelSpace φ hφ :=
    (weakConvexKernelSpaceEquivRange φ hφ).symm
      ⟨α • a + β • b, hcombo⟩
  refine ⟨s, ?_⟩
  let L := grothendieckVectorizationLinearEquivSpan φ hφ
  apply L.injective
  rw [show L (α • grothendieckConeEmbedding φ hφ q +
        β • grothendieckConeEmbedding φ hφ r) =
      L (α • grothendieckConeEmbedding φ hφ q) +
        L (β • grothendieckConeEmbedding φ hφ r) from L.map_add _ _]
  rw [show L (α • grothendieckConeEmbedding φ hφ q) =
      α • L (grothendieckConeEmbedding φ hφ q) from L.map_smul _ _,
    show L (β • grothendieckConeEmbedding φ hφ r) =
      β • L (grothendieckConeEmbedding φ hφ r) from L.map_smul _ _]
  apply Subtype.ext
  simp [L, grothendieckVectorizationLinearEquivSpan,
    grothendieckVectorizationEquivSpan_coneEmbedding, s, a, b,
    weakConvexKernelImage]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: completed embedded cone in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: before taking closure, the cone in the completed
vectorization is the image of the vectorization cone under the canonical
completion embedding.
-/
def completedGrothendieckEmbeddedCone {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Set (CompletedGrothendieckVectorization φ hφ) :=
  ((fun z : GrothendieckVectorization φ hφ =>
      (z : CompletedGrothendieckVectorization φ hφ)) ''
    grothendieckVectorizationCone φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: closed cone in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the closed cone in the completed Grothendieck vectorization
is the closure of the embedded cone.

Lean strategy / thesis relation note: this is the completion-level version of the thesis' phrase
"complete the vectorization and project onto the closed cone". The closure is
made explicit because the embedded cone need not be closed before completion.
-/
def completedGrothendieckCone {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    Set (CompletedGrothendieckVectorization φ hφ) :=
  closure (completedGrothendieckEmbeddedCone φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: closed-cone identification in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the completed cone used for projection is closed by
definition as the closure of the embedded cone.
-/
theorem completedGrothendieckCone_isClosed {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    IsClosed (completedGrothendieckCone φ hφ) := by
  dsimp [completedGrothendieckCone]
  exact isClosed_closure

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: embedded-cone convexity in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the canonical completion embedding preserves the convex
cone operations on the vectorization cone.
-/
theorem completedGrothendieckEmbeddedCone_convexCone {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    ConvexCone (completedGrothendieckEmbeddedCone φ hφ) := by
  intro x y hx hy α β hα hβ
  rcases hx with ⟨cx, hcx, rfl⟩
  rcases hy with ⟨cy, hcy, rfl⟩
  refine ⟨α • cx + β • cy,
    grothendieckVectorizationCone_convexCone φ hφ hcx hcy hα hβ, ?_⟩
  simp [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: closed-cone convexity in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the closed completed cone is again a convex cone.
-/
theorem completedGrothendieckCone_convexCone {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    ConvexCone (completedGrothendieckCone φ hφ) := by
  dsimp [completedGrothendieckCone]
  exact convexCone_closure (completedGrothendieckEmbeddedCone_convexCone φ hφ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: nonempty closed cone in
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: the closed completed cone is nonempty because it contains
the embedded zero cone point.
-/
theorem completedGrothendieckCone_nonempty {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ) :
    (completedGrothendieckCone φ hφ).Nonempty := by
  let z : WeakConvexKernelSpace φ hφ := weakConvexKernelZero φ hφ
  let g : GrothendieckVectorization φ hφ := grothendieckConeEmbedding φ hφ z
  refine ⟨(g : CompletedGrothendieckVectorization φ hφ), ?_⟩
  apply subset_closure
  exact ⟨g, ⟨z, rfl⟩, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:grothendieck-vectorization-inner-product-space`.

Original label: projection clause of
`cor:grothendieck-vectorization-inner-product-space`.

Informal statement: every point of the completed Grothendieck vectorization has
a unique metric projection onto the closed completed cone.

Lean strategy / thesis relation note: this is the corollary's Hilbert-space projection clause. The
closed cone is the closure of the embedded weak-convex cone in the canonical
completion, so the proof applies the previously verified closed-convex-cone
projection theorem.
-/
theorem completedGrothendieckCone_metricProjection_existsUnique
    {X : Type u} {V : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nonempty X]
    (φ : Operator X V) (hφ : WeaklyConvexOperator X V φ)
    (u : CompletedGrothendieckVectorization φ hφ) :
    ∃! p : CompletedGrothendieckVectorization φ hφ,
      p ∈ completedGrothendieckCone φ hφ ∧
        ‖u - p‖ = ⨅ w : completedGrothendieckCone φ hφ,
          ‖u - (w : CompletedGrothendieckVectorization φ hφ)‖ := by
  exact closedConvexCone_metricProjection_existsUnique
    (completedGrothendieckCone_convexCone φ hφ)
    (by
      dsimp [completedGrothendieckCone]
      exact isClosed_closure)
    (completedGrothendieckCone_nonempty φ hφ) u

end KernelHilbert
end Stochastic
end Foundations
end Thesis
