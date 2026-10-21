import Thesis.Appendices.SetTheory.ZFCFoundations
import Thesis.Appendices.SetTheory.DoctoralSetTheory
import Thesis.Appendices.Algebra.DoctoralAlgebra

/-! # Appendix source proofs: remaining variants

The thesis-faithful proofs that used to live here now sit on the primary
modules: `ZFCFoundations` carries `ZFC.unique_empty` (`prop:empty-set-unique`),
`ZFC.empty_domain_functions_equal` (`prop:empty-domain-function`), the
inductive-set scaffolding `ZFC.IsInductive`, `ZFC.naturals`,
`ZFC.naturals_isInductive`, `ZFC.naturals_least` and the set-universe induction
`ZFC.induction_naturals` (`prop:induction`); `DoctoralSetTheory` carries the
typed least-inductive-set clause `univ_subset_of_inductive`; and
`GroupCompletion` carries `completionRelation_equivalence`
(`prop:grothendieck-relation`).  This module keeps only the parametrised
least-inductive-set variants that have no primary counterpart (an arbitrary
ambient set `I`, respectively an arbitrary zero and successor on a type),
together with aliases of the moved names for interface stability. -/

noncomputable section

namespace Thesis.Foundations.Preliminary.SetTheory.ZFC

universe u

/-- Moved to `ZFCFoundations` as `unique_empty`; kept as an alias. -/
alias unique_empty_by_separation := unique_empty

/-- Moved to `ZFCFoundations` as `empty_domain_functions_equal`; kept as an alias. -/
alias empty_domain_functions_equal_by_graph := empty_domain_functions_equal

/-- Moved to `ZFCFoundations` as `IsInductive`; kept as an alias. -/
alias InductiveZF := IsInductive

/-- Separation inside an arbitrary ambient set `I` cuts out the elements lying in
every inductive set.  The primary `naturals` is the instance in which `I` is the
inductive set supplied by the Infinity axiom. -/
def leastInductiveZF (I : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun n ↦ ∀ S, IsInductive S → n ∈ S) I

theorem leastInductiveZF_inductive {I : ZFSet.{u}} (hI : IsInductive I) :
    IsInductive (leastInductiveZF I) := by
  constructor
  · exact ZFSet.mem_sep.mpr ⟨hI.1, fun S hS ↦ hS.1⟩
  · intro n hn
    obtain ⟨hnI, hnS⟩ := ZFSet.mem_sep.mp hn
    exact ZFSet.mem_sep.mpr ⟨hI.2 n hnI, fun S hS ↦ hS.2 n (hnS S hS)⟩

theorem leastInductiveZF_subset {I S : ZFSet.{u}} (hS : IsInductive S) :
    leastInductiveZF I ⊆ S := by
  intro n hn
  exact (ZFSet.mem_sep.mp hn).2 S hS

/-- Alternative route for `prop:induction` (not the mapped proof): the same two
inclusions for the least inductive set cut out of an arbitrary ambient set `I`.
The mapped set-universe proof is `induction_naturals` in `ZFCFoundations`. -/
theorem induction_by_leastZF {I S : ZFSet.{u}}
    (hS : S ⊆ leastInductiveZF I) (hzero : (∅ : ZFSet.{u}) ∈ S)
    (hstep : ∀ n, n ∈ S → n ∪ ({n} : ZFSet.{u}) ∈ S) :
    S = leastInductiveZF I := by
  apply ZFSet.ext
  intro n
  exact ⟨fun hn ↦ hS hn, fun hn ↦ leastInductiveZF_subset ⟨hzero, hstep⟩ hn⟩

end Thesis.Foundations.Preliminary.SetTheory.ZFC

namespace Thesis.Foundations.Preliminary.SetTheory

universe u

/-- Inductivity of a subset for a specified zero and successor on an arbitrary
type.  The primary typed clause is `univ_subset_of_inductive` in
`DoctoralSetTheory`, for `X := ℕ`, `zero := 0` and `succ := (· + 1)`. -/
def IsInductiveSet {X : Type u} (zero : X) (succ : X → X) (S : Set X) : Prop :=
  zero ∈ S ∧ ∀ x, x ∈ S → succ x ∈ S

/-- Intersection construction of the least inductive set. -/
def leastInductiveSet {X : Type u} (zero : X) (succ : X → X) : Set X :=
  {x | ∀ S : Set X, IsInductiveSet zero succ S → x ∈ S}

theorem leastInductiveSet_inductive {X : Type u} (zero : X) (succ : X → X) :
    IsInductiveSet zero succ (leastInductiveSet zero succ) := by
  constructor
  · intro S hS
    exact hS.1
  · intro x hx S hS
    exact hS.2 x (hx S hS)

/-- Alternative route for `prop:induction` (not the mapped proof): for an
arbitrary zero and successor, an inductive subset of the least inductive set
equals it, by the two inclusions and without any natural-number recursor.  The
mapped proofs are `ZFC.induction_naturals` in `ZFCFoundations` (set universe)
and `induction_set` in `DoctoralSetTheory` (typed `ℕ`). -/
theorem induction_by_least_inductive_set {X : Type u} (zero : X) (succ : X → X)
    (S : Set X) (hS : IsInductiveSet zero succ S)
    (hsub : S ⊆ leastInductiveSet zero succ) : S = leastInductiveSet zero succ := by
  apply Set.Subset.antisymm hsub
  intro x hx
  exact hx S hS

end Thesis.Foundations.Preliminary.SetTheory

namespace Thesis.Foundations.Preliminary.Algebra

/-- Moved to `GroupCompletion` as `completionRelation_equivalence`; kept as an alias. -/
alias completionRelation_equivalence_by_cancellation := completionRelation_equivalence

end Thesis.Foundations.Preliminary.Algebra
