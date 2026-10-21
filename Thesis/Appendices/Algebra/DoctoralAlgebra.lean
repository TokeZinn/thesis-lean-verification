import Thesis.Appendices.Algebra.GroupCompletion

/-! # Current field-general vector spaces and group-completion universal property -/

noncomputable section

namespace Thesis.Foundations.Preliminary.Algebra

universe u v w

/-- Original label: `defn:field`. -/
abbrev FieldStructure (K : Type u) := Field K

/-- Original label: `defn:real-vector-space`.
The current definition is over an arbitrary field; real spaces are a
specialization of this general construction. -/
abbrev VectorSpace (K : Type u) (V : Type v) [Field K] [AddCommGroup V] := Module K V

/-- Original label: `prop:vector-space-extension`.

The source now quantifies over every field and includes the empty domain. The
scalar multiplication is pointwise, `(a • f) x = a • f x`, and each vector-space
axiom (together with Mathlib's two further `Module` fields) is checked by
evaluating the corresponding identity of `V` at every `x : X`; the additive
group of `X → V` is the pointwise `Pi` group. -/
@[implicit_reducible] def functionSpaceVectorSpace (K : Type u) (X : Type v) (V : Type w)
    [Field K] [AddCommGroup V] [Module K V] : Module K (X → V) where
  smul a f := fun x ↦ a • f x
  one_smul f := funext fun x ↦ one_smul K (f x)
  mul_smul a b f := funext fun x ↦ mul_smul a b (f x)
  smul_zero a := funext fun _ ↦ smul_zero a
  smul_add a f g := funext fun x ↦ smul_add a (f x) (g x)
  add_smul a b f := funext fun x ↦ add_smul a b (f x)
  zero_smul f := funext fun x ↦ zero_smul K (f x)

/-- The pointwise structure is definitionally Mathlib's `Pi` module instance. -/
theorem functionSpaceVectorSpace_eq_pi (K : Type u) (X : Type v) (V : Type w)
    [Field K] [AddCommGroup V] [Module K V] :
    functionSpaceVectorSpace K X V = Pi.module X (fun _ ↦ V) K := rfl

variable {M : Type u} [AddCommMonoid M]

/-- Original label: `prop:grothendieck-relation`.
The simplified relation respects addition of representatives. -/
theorem completionRelation_add_compatible [IsCancelAdd M]
    {p q r s : M × M}
    (hpq : p.1 + q.2 = q.1 + p.2) (hrs : r.1 + s.2 = s.1 + r.2) :
    (p.1 + r.1) + (q.2 + s.2) = (q.1 + s.1) + (p.2 + r.2) := by
  calc
    (p.1 + r.1) + (q.2 + s.2) = (p.1 + q.2) + (r.1 + s.2) := by ac_rfl
    _ = (q.1 + p.2) + (s.1 + r.2) := by rw [hpq, hrs]
    _ = (q.1 + s.1) + (p.2 + r.2) := by ac_rfl

/-- Original label: `defn:grothendieck-group`. -/
def completionEmbedding : M →+ GroupCompletion M :=
  _root_.Algebra.GrothendieckAddGroup.of

theorem completionEmbedding_apply (x : M) : completionEmbedding x = completionPair (x, 0) := by
  exact (AddLocalization.mk_zero_eq_addMonoidOf_mk _).symm

/-- Original label: `prop:grothendieck-universal`, clause (ii). -/
theorem completionPair_eq_sub_embedding (x y : M) :
    completionPair (x, y) = completionEmbedding x - completionEmbedding y := by
  rw [completionEmbedding_apply, completionEmbedding_apply, sub_eq_add_neg,
    (completionPair_laws y 0 0 0).2.2, (completionPair_laws x 0 0 y).1]
  simp only [add_zero, zero_add]

/-- Original label: `prop:grothendieck-universal`, clause (iii).
Every extending homomorphism has the asserted difference formula: a monoid
homomorphism between abelian groups preserves inverses, and clause (ii) gives
`χ([(x,y)]) = χ(ι(x)) − χ(ι(y)) = ψ(x) − ψ(y)`. -/
theorem completion_extension_pair_formula {G : Type v} [AddCommGroup G]
    (ψ : M →+ G) (Ψ : GroupCompletion M →+ G)
    (hΨ : Ψ.comp completionEmbedding = ψ) (x y : M) :
    Ψ (completionPair (x, y)) = ψ x - ψ y := by
  rw [completionPair_eq_sub_embedding, map_sub]
  have hcomp (z : M) : Ψ (completionEmbedding z) = ψ z :=
    DFunLike.congr_fun hΨ z
  rw [hcomp, hcomp]

/-- Original label: `prop:grothendieck-universal`, clause (iii).
Well-definedness step of `ψ̄([(x,y)]) = ψ(x) − ψ(y)`: from
`ψ(x) + ψ(y′) = ψ(x′) + ψ(y)` it follows that `ψ(x) − ψ(y) = ψ(x′) − ψ(y′)`. -/
theorem completionLift_well_defined {G : Type v} [AddCommGroup G] (ψ : M →+ G)
    {x y x' y' : M} (h : ψ x + ψ y' = ψ x' + ψ y) : ψ x - ψ y = ψ x' - ψ y' :=
  sub_eq_sub_iff_add_eq_add.mpr h

/-- Original label: `prop:grothendieck-universal`, clause (iii).
The underlying function of the thesis extension, `ψ̄([(x,y)]) = ψ(x) − ψ(y)`,
defined on classes. If `(x,y) ∼ (x′,y′)`, that is `x + y′ = x′ + y` (in
Mathlib's quotient up to a common summand `k`, whose image `ψ(k)` cancels in the
group `G`; under cancellation no such `k` is needed), applying `ψ` gives
`ψ(x) + ψ(y′) = ψ(x′) + ψ(y)`, so the value does not depend on the
representative. -/
def completionLiftFun {G : Type v} [AddCommGroup G] (ψ : M →+ G)
    (g : GroupCompletion M) : G :=
  AddLocalization.liftOn g (fun x y ↦ ψ x - ψ (y : M)) (by
    intro x x' y y' hr
    obtain ⟨k, hk⟩ := AddLocalization.r_iff_exists.mp hr
    have hψ : ψ (k : M) + (ψ (y' : M) + ψ x) = ψ (k : M) + (ψ (y : M) + ψ x') := by
      simpa only [map_add] using congrArg ψ hk
    have hcancel : ψ (y' : M) + ψ x = ψ (y : M) + ψ x' := add_left_cancel hψ
    apply completionLift_well_defined
    rw [add_comm (ψ x), add_comm (ψ x')]
    exact hcancel)

theorem completionLiftFun_pair {G : Type v} [AddCommGroup G] (ψ : M →+ G) (x y : M) :
    completionLiftFun ψ (completionPair (x, y)) = ψ x - ψ y := rfl

/-- Original label: `prop:grothendieck-universal`, clause (iii).
The thesis extension `ψ̄` as a homomorphism: it is additive because `ψ` is
additive, `ψ̄([(x,y)] + [(x′,y′)]) = ψ(x + x′) − ψ(y + y′)
= (ψ(x) − ψ(y)) + (ψ(x′) − ψ(y′))`, and `ψ̄([(e,e)]) = ψ(e) − ψ(e) = 0`. -/
def completionLift {G : Type v} [AddCommGroup G] (ψ : M →+ G) :
    GroupCompletion M →+ G where
  toFun := completionLiftFun ψ
  map_zero' := by
    change completionLiftFun ψ 0 = 0
    rw [← (completionPair_laws (0 : M) 0 0 0).2.1, completionLiftFun_pair, sub_self]
  map_add' g h := by
    obtain ⟨⟨x, y⟩, rfl⟩ := completionPair_surjective g
    obtain ⟨⟨x', y'⟩, rfl⟩ := completionPair_surjective h
    change completionLiftFun ψ (completionPair (x, y) + completionPair (x', y')) =
      completionLiftFun ψ (completionPair (x, y)) + completionLiftFun ψ (completionPair (x', y'))
    rw [(completionPair_laws x y x' y').1, completionLiftFun_pair, completionLiftFun_pair,
      completionLiftFun_pair, map_add, map_add, add_sub_add_comm]

theorem completionLift_pair {G : Type v} [AddCommGroup G] (ψ : M →+ G) (x y : M) :
    completionLift ψ (completionPair (x, y)) = ψ x - ψ y := rfl

/-- Original label: `prop:grothendieck-universal`, clause (iii).
The extension restricts to `ψ` along the canonical map:
`ψ̄(ι(x)) = ψ(x) − ψ(e) = ψ(x)`. -/
theorem completionLift_comp_embedding {G : Type v} [AddCommGroup G] (ψ : M →+ G) :
    (completionLift ψ).comp completionEmbedding = ψ := by
  ext x
  rw [AddMonoidHom.comp_apply, completionEmbedding_apply, completionLift_pair, map_zero,
    sub_zero]

/-- Original label: `prop:grothendieck-universal`, clause (iii).

The universal property, including uniqueness of the extension, along the thesis
route. Existence is the thesis extension `completionLift`,
`ψ̄([(x,y)]) = ψ(x) − ψ(y)`, which restricts to `ψ` along `ι`. Uniqueness: any
`χ` with `χ ∘ ι = ψ` satisfies `χ([(x,y)]) = χ(ι(x)) − χ(ι(y)) = ψ(x) − ψ(y)` by
clause (ii), so `χ = ψ̄` on every class, and every element is a class. Only the
quotient object itself remains Mathlib's `AddLocalization`. -/
theorem completion_universal {G : Type v} [AddCommGroup G] (ψ : M →+ G) :
    ∃! Ψ : GroupCompletion M →+ G, Ψ.comp completionEmbedding = ψ := by
  refine ⟨completionLift ψ, completionLift_comp_embedding ψ, ?_⟩
  intro χ hχ
  ext g
  obtain ⟨⟨x, y⟩, rfl⟩ := completionPair_surjective g
  rw [completion_extension_pair_formula ψ χ hχ x y, completionLift_pair]

end Thesis.Foundations.Preliminary.Algebra
