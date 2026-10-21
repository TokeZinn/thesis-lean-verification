import Thesis.Foundations.MarketActions.Identifiers
import Thesis.Foundations.MarketActions.Composite
import Thesis.Foundations.MarketRepresentation.MetricSourceProofs
import Mathlib.Topology.Homeomorph.Lemmas

/-! Identifier-coordinate remarks from the market-actions chapter.

The coproduct-pasting proofs of `prop:application-continuous` and
`thm:composite-application-continuous` (together with the identification
`𝒜(X) ≅ ⨆_α F_α`: `ActionFamily`, `actionSigmaEquiv`, `actionSigmaIsometry`,
`actionSigmaHomeomorph`, `continuous_prod_sigma_iff`) now live in `Composite`
(`continuous_applyAction_emetricTopology`,
`continuous_applyCompositeAction_emetricTopology`), and the layer-pasting
clopenness proofs of clause (ii) of `prop:identifier-cancel-continuous` now live
in `Identifiers` (`distinctIdentifiers_fixedLayer_clopen`,
`distinctIdentifiers_clopen`, `disjointIdentifiers_fixedLayers_clopen`,
`disjointIdentifiers_clopen_tuples`, `disjointIdentifiers_clopen`,
`distinctIdentifiers_polish`); those are the mapped proofs. This module keeps
the `rem:identifier-coordinates` material, the coordinate-bound route to
clause (iv) (not the mapped proof), the `continuous_sigma_prod_iff` helper, and
aliases of the moved names for interface stability. -/

noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.MarketActions.ActionSourceProofs

universe u v
open MarketRepresentation MarketRepresentation.TuplesBasic
open MarketRepresentation.TuplesMetricTopology MarketRepresentation.DisjointUnionTopology
open MarketRepresentation.FiniteSets MarketRepresentation.FiniteSets.FiniteSubsets
open Primitive Analytic Composite Identifiers

/-! The action-coproduct identification and the product/coproduct pasting
lemma are now the `Composite` declarations of the same names; they are
re-exported so that fully qualified `ActionSourceProofs.…` references keep
working. -/
export Composite (ActionFamily actionFamilyEMetricSpace actionSigmaEquiv
  actionSigmaIsometry actionSigmaHomeomorph actionSigmaHomeomorph_apply
  actionSigmaHomeomorph_symm_apply continuous_prod_sigma_iff)

/-- Alias of the mapped pasting proof of `prop:application-continuous`,
`Composite.continuous_applyAction_emetricTopology`. -/
alias continuous_applyAction_by_pasting := Composite.continuous_applyAction_emetricTopology

/-- Alias of the mapped pasting proof of `thm:composite-application-continuous`,
`Composite.continuous_applyCompositeAction_emetricTopology`. -/
alias continuous_composite_by_layer_pasting :=
  Composite.continuous_applyCompositeAction_emetricTopology

/-- Original label: `rem:identifier-coordinates`.
Ignoring identifiers gives the kernel quotient of the forgetful projection. -/
def identifierKernelQuotientEquivRange (Y : Type u) (I : Type v) :
    Quotient (Setoid.ker (Prod.fst : Y × Identifier I → Y)) ≃
      Set.range (Prod.fst : Y × Identifier I → Y) :=
  Setoid.quotientKerEquivRange _

/-- Original label: `rem:identifier-coordinates`.
The ignored-identifier pseudometric is literally pulled back along `varpi`. -/
@[reducible] def ignoredIdentifierPseudoEMetricSpace (Y : Type u) (I : Type v)
    [EMetricSpace Y] : PseudoEMetricSpace (Y × Identifier I) :=
  PseudoEMetricSpace.induced Prod.fst inferInstance

theorem ignored_identifier_zero_iff {Y : Type u} [EMetricSpace Y] {I : Type v}
    (x y : Y × Identifier I) :
    @edist _ (ignoredIdentifierPseudoEMetricSpace Y I).toEDist x y = 0 ↔ x.1 = y.1 :=
  edist_eq_zero

/-- Original label: `rem:identifier-coordinates`.
For nonempty identifier space the zero-distance quotient recovers all of Y,
not merely the range of the projection. -/
def identifierKernelQuotientEquivPayload (Y : Type u) (I : Type v) [Nonempty I] :
    Quotient (Setoid.ker (Prod.fst : Y × Identifier I → Y)) ≃ Y where
  toFun := Quotient.lift Prod.fst (fun _ _ h ↦ h)
  invFun y := Quotient.mk _ (y, ⟨Classical.choice ‹Nonempty I›⟩)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h p => exact Quotient.sound rfl
  right_inv _ := rfl

theorem identifier_coproduct_distance {Y : Type u} [EMetricSpace Y] {I : Type v}
    (i j : I) (hij : i ≠ j) (y z : Y) :
    disjointEdist (Sigma.mk i y : Sigma (fun _ : I ↦ Y)) (Sigma.mk j z) = ⊤ :=
  disjointEdist_mk_mk_ne (X := fun _ : I ↦ Y) hij y z

/-- Original label: `rem:identifier-coordinates`.
A map ignores identifiers exactly when it factors through the forgetful
projection (with a nonempty identifier type). -/
theorem factors_through_forget_iff {Y Z : Type*} {I : Type v} [Nonempty I]
    (f : Y × Identifier I → Z) :
    (∃ g : Y → Z, f = g ∘ Prod.fst) ↔
      ∀ y i j, f (y, i) = f (y, j) := by
  constructor
  · rintro ⟨g, rfl⟩
    intros
    rfl
  · intro hf
    let i : Identifier I := ⟨Classical.choice ‹Nonempty I›⟩
    refine ⟨fun y ↦ f (y, i), ?_⟩
    funext p
    exact hf p.1 p.2 i

/-- Alternative route for `prop:identifier-cancel-continuous`, clause (iv) (not
the mapped proof, which is `Identifiers.continuous_forgetIdentifiers`): the
source coordinate maximum bound for the forgetful map. -/
theorem forget_edist_le_of_lt_one {Y : Type u} [EMetricSpace Y] {I : Type v}
    {x y : Tuple (Y × Identifier I)} (h : edist x y < 1) :
    edist (forgetIdentifiers x) (forgetIdentifiers y) ≤ edist x y := by
  rcases x with ⟨n, x⟩
  rcases y with ⟨m, y⟩
  have hnm : n = m := length_eq_of_edist_lt_one h
  subst m
  apply (fixedLength_edist_le_coordinateEDistSup _ _).trans
  rw [fixedLength_edist_eq_coordinateEDistSup_of_lt_one h]
  unfold coordinateEDistSup
  apply Finset.sup_mono_fun
  intro i _
  exact le_max_left _ _

/-- Alternative route for `prop:identifier-cancel-continuous`, clause (iv) (not
the mapped proof, which is `Identifiers.continuous_forgetIdentifiers`).
Freeze the length at radius one, then use the preceding finite-coordinate
maximum estimate, precisely the source epsilon/delta proof. -/
theorem continuous_forget_by_coordinate_bound {Y : Type u} [EMetricSpace Y] {I : Type v} :
    @Continuous (Tuple (Y × Identifier I)) (Tuple Y)
      (emetricTopology _) (emetricTopology _) forgetIdentifiers := by
  letI : TopologicalSpace (Tuple (Y × Identifier I)) := emetricTopology _
  letI : TopologicalSpace (Tuple Y) := emetricTopology _
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, fun y hy ↦ ?_⟩
  exact (forget_edist_le_of_lt_one (hy.trans_le (min_le_right ε 1))).trans_lt
    (hy.trans_le (min_le_left ε 1))

/-- Alias of the mapped fixed-layer clopenness proof
`Identifiers.distinctIdentifiers_fixedLayer_clopen`. -/
alias distinct_identifiers_fixed_layer_clopen := Identifiers.distinctIdentifiers_fixedLayer_clopen

/-- Alias of the mapped layer-pasting proof `Identifiers.distinctIdentifiers_clopen`. -/
alias distinct_identifiers_clopen_by_layers := Identifiers.distinctIdentifiers_clopen

/-- Alias of the mapped product-layer proof
`Identifiers.disjointIdentifiers_fixedLayers_clopen`. -/
alias disjoint_identifiers_fixed_layers_clopen :=
  Identifiers.disjointIdentifiers_fixedLayers_clopen

/-- Symmetric form of `Composite.continuous_prod_sigma_iff`: pasting over the
left coproduct factor of a product. -/
theorem continuous_sigma_prod_iff {A : Type u} {F : A → Type v} {P Z : Type*}
    [∀ a, TopologicalSpace (F a)] [TopologicalSpace P] [TopologicalSpace Z]
    (f : Sigma F × P → Z) :
    Continuous f ↔ ∀ a, Continuous (fun p : F a × P ↦ f (⟨a, p.1⟩, p.2)) := by
  constructor
  · intro hf a
    have h := (continuous_prod_sigma_iff _).mp (hf.comp continuous_swap) a
    exact h.comp continuous_swap
  · intro hf
    have h : Continuous (fun p : P × Sigma F ↦ f (p.2, p.1)) := by
      apply (continuous_prod_sigma_iff _).mpr
      intro a
      exact (hf a).comp continuous_swap
    exact h.comp continuous_swap

/-- Alias of the mapped product-coproduct pasting proof
`Identifiers.disjointIdentifiers_clopen_tuples`. -/
alias disjoint_identifiers_clopen_by_layers := Identifiers.disjointIdentifiers_clopen_tuples

/-- Alias of the mapped subspace restriction `Identifiers.disjointIdentifiers_clopen`. -/
alias disjoint_distinct_identifiers_clopen_by_layers := Identifiers.disjointIdentifiers_clopen

/-- Alias of the mapped Polishness proof `Identifiers.distinctIdentifiers_polish`. -/
alias distinct_identifiers_polish_by_layers := Identifiers.distinctIdentifiers_polish

end Thesis.Foundations.MarketActions.ActionSourceProofs
