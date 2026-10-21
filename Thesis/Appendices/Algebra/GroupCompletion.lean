import Thesis.Appendices.Algebra.Algebra
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-! # The cancellative abelian-monoid completion in the algebra appendix

The general pair construction is independent of the later construction from
a convex cone in a vector space. Equality, addition, identity, inverse, and
the faithful canonical embedding are identified with the manuscript formulas.
-/

namespace Thesis.Foundations.Preliminary.Algebra

universe u
variable {M : Type u} [AddCommMonoid M]

/-- Original labels: `rem:group-completion-scope`, `defn:grothendieck-group`,
`prop:grothendieck-universal`.
The quotient object `G(X) = (X × X)/∼`, as Mathlib's Grothendieck group: the
actual abelian group of formal differences (clause (i) of the universal-property
proposition). Cancellation is needed for the faithful embedding and the
manuscript's simplified pair relation. -/
abbrev GroupCompletion (M : Type u) [AddCommMonoid M] :=
  _root_.Algebra.GrothendieckAddGroup M

/-- Original label: `defn:grothendieck-group`.
The class `[(x,y)]` of the pair `(x,y)`, interpreted as a formal difference. -/
def completionPair (p : M × M) : GroupCompletion M :=
  AddLocalization.mk p.1 ⟨p.2, AddSubmonoid.mem_top _⟩

/-- Original label: `rem:group-completion-scope`.
Without cancellation the congruence includes an extra common summand. -/
theorem completionPair_eq_iff_exists (p q : M × M) :
    completionPair p = completionPair q ↔
      ∃ c : M, c + (p.1 + q.2) = c + (q.1 + p.2) := by
  simp [completionPair, AddLocalization.mk_eq_mk_iff,
    AddLocalization.r_iff_exists, Subtype.exists, AddSubmonoid.mem_top,
    add_comm p.1 q.2, add_comm q.1 p.2]

/-- Original label: `rem:group-completion-scope`.
An idempotent element collapses to zero on introducing formal inverses. Thus
faithfulness cannot be asserted for arbitrary commutative monoids. -/
theorem completionEmbedding_eq_zero_of_idempotent (x : M) (hx : x + x = x) :
    completionPair (x, 0) = 0 := by
  have h : completionPair (x, 0) = completionPair (0, 0) :=
    (completionPair_eq_iff_exists _ _).mpr ⟨x, by simpa using hx⟩
  refine h.trans ?_
  change AddLocalization.mk (0 : M) (0 : (⊤ : AddSubmonoid M)) = 0
  rw [AddLocalization.mk_zero_eq_addMonoidOf_mk]
  exact map_zero (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M))

/-- Original labels: `rem:group-completion-scope`, `defn:grothendieck-group`,
`prop:grothendieck-universal`.
The quotient relation is exactly the displayed cross-addition relation `∼`. -/
theorem completionPair_eq_iff [IsCancelAdd M] (p q : M × M) :
    completionPair p = completionPair q ↔ p.1 + q.2 = q.1 + p.2 := by
  simpa only [completionPair, add_comm] using
    (AddLocalization.mk_eq_mk_iff' (a₁ := p.1) (b₁ := q.1)
      (a₂ := (⟨p.2, AddSubmonoid.mem_top _⟩ : (⊤ : AddSubmonoid M)))
      (b₂ := (⟨q.2, AddSubmonoid.mem_top _⟩ : (⊤ : AddSubmonoid M))))

/-- Original labels: `prop:grothendieck-relation`, `rem:group-completion-scope`.

The thesis proof that the cross-addition relation `∼` is an equivalence.
Reflexivity and symmetry are immediate. For transitivity, add the middle second
component `y′` to `x + y″`, reassociate, substitute the two defining equalities,
reassociate again, and cancel `y′` (this is where cancellation enters). -/
theorem completionRelation_equivalence [IsCancelAdd M] :
    Equivalence (fun p q : M × M ↦ p.1 + q.2 = q.1 + p.2) := by
  refine ⟨fun _ ↦ rfl, fun h ↦ h.symm, ?_⟩
  intro p q r hpq hqr
  apply add_right_cancel (b := q.2)
  calc
    (p.1 + r.2) + q.2 = (p.1 + q.2) + r.2 := by ac_rfl
    _ = (q.1 + p.2) + r.2 := by rw [hpq]
    _ = (q.1 + r.2) + p.2 := by ac_rfl
    _ = (r.1 + q.2) + p.2 := by rw [hqr]
    _ = (r.1 + p.2) + q.2 := by ac_rfl

/-- Original label: `rem:group-completion-scope`.
Every group element has a pair representative. -/
theorem completionPair_surjective : Function.Surjective (completionPair (M := M)) := by
  intro g
  induction g using AddLocalization.ind with
  | H p => exact ⟨(p.1, p.2), rfl⟩

/-- Original labels: `rem:group-completion-scope`, `prop:grothendieck-universal`.
Clause (i): the addition, identity, and inverse are precisely the source's pair
formulas. -/
theorem completionPair_laws (x y z w : M) :
    completionPair (x, y) + completionPair (z, w) = completionPair (x + z, y + w) ∧
    completionPair ((0 : M), 0) = 0 ∧
    -completionPair (x, y) = completionPair (y, x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact AddLocalization.mk_add _ _ _ _
  · change AddLocalization.mk (0 : M) (0 : (⊤ : AddSubmonoid M)) = 0
    rw [AddLocalization.mk_zero_eq_addMonoidOf_mk]
    exact map_zero (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M))
  · exact _root_.Algebra.GrothendieckAddGroup.neg_mk _ _

/-- Original labels: `rem:group-completion-scope`, `prop:grothendieck-universal`.
Clause (ii): the canonical map `x ↦ [(x,0)]` is additive and injective under
cancellation. -/
theorem completionEmbedding_faithful [IsCancelAdd M] :
    Function.Injective (fun x : M ↦ completionPair (x, 0)) ∧
    ∀ x y : M, completionPair (x + y, 0) =
      completionPair (x, 0) + completionPair (y, 0) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    simpa only [add_zero] using (completionPair_eq_iff (x, 0) (y, 0)).mp h
  · intro x y
    simpa only [add_zero] using ((completionPair_laws x 0 y 0).1).symm

end Thesis.Foundations.Preliminary.Algebra
