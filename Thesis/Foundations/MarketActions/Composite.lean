import Thesis.Foundations.MarketActions.Analytic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Market Actions: Composite Actions

Blueprint module for
`1 - theoretical foundations/3_market_actions.tex`,
section "Composite Actions".

Planned formal content:

* `defn:actions`;
* action space and evaluation map;
* composite actions;
* `cor:action-metrisation`;
* `prop:application-continuous`;
* `thm:composite-action-metric`;
* `thm:composite-application-continuous`.
-/

namespace Thesis
namespace Foundations
namespace MarketActions
namespace Composite

open Thesis.Foundations.MarketRepresentation
open Thesis.Foundations.MarketRepresentation.FiniteSets
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
open Thesis.Foundations.MarketActions.Primitive

universe u

variable {X : Type u}

/-! ## Action Space and Evaluation Map -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: operation set `A = {\oplus, \ominus, \circledast}` in
`defn:actions`.

Informal statement: the three primitive operation labels: tuple addition,
cancellation, and modification.

Lean strategy / thesis relation note: instead of using a literal finite set of
function symbols, Lean uses an inductive type with three constructors. This is
the tag set indexing the dependent family `ActionPayload`.
-/
inductive ActionKind where
  | add
  | cancel
  | modify
  deriving DecidableEq, Repr

/-- The operation label set `A = {⊕, ⊖, ⊛}` is finite. -/
instance : Fintype ActionKind where
  elems := {ActionKind.add, ActionKind.cancel, ActionKind.modify}
  complete k := by cases k <;> simp

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: `defn:actions`, action space `\mathscr{A}(X)`.

Informal statement: an action is a disjoint-union element consisting of a
primitive operation label and a payload admissible for that operation.

Lean strategy / thesis relation note: the thesis writes a disjoint union
`\bigsqcup_{\alpha\in A} F_\alpha`. Lean represents this finite dependent
disjoint union as an inductive type with one constructor for each primitive
operation. This avoids universe bookkeeping around the heterogeneous payload
spaces while keeping the same tagged-union content.
-/
inductive MarketAction (X : Type u) : Type (max u 1) where
  /--
  Thesis source: `1 - theoretical foundations/3_market_actions.tex`,
  `defn:actions`.

  Informal statement: package a tuple as an addition action.
  -/
  | add (y : Tuple X)
  /--
  Thesis source: `1 - theoretical foundations/3_market_actions.tex`,
  `defn:actions`.

  Informal statement: package a finite natural-number set as a cancellation
  action.
  -/
  | cancel (eta : FiniteSubsets ℕ)
  /--
  Thesis source: `1 - theoretical foundations/3_market_actions.tex`,
  `defn:actions`.

  Informal statement: package a distinct finite set as a modification action.
  -/
  | modify (xi : DistinctFiniteSubsets X)

namespace MarketAction

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: operation label in `defn:actions`.

Informal statement: recover the primitive operation label from a tagged
market action.
-/
def kind : MarketAction X → ActionKind
  | add _ => ActionKind.add
  | cancel _ => ActionKind.cancel
  | modify _ => ActionKind.modify

end MarketAction

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: application/evaluation map in `defn:actions`.

Informal statement: apply one action to a tuple by selecting the primitive
operation associated with the action tag.

Lean strategy / thesis relation note: the thesis writes `x \lhd (o,\alpha)=\alpha(x,o)`. Lean
pattern matches on the action constructor, so the payload `o` automatically
has the right type in each branch.
-/
noncomputable def applyAction (x : Tuple X) (a : MarketAction X) : Tuple X :=
  match a with
  | MarketAction.add y => concat x y
  | MarketAction.cancel eta => Primitive.cancel x eta
  | MarketAction.modify xi => Primitive.modify x xi

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: addition case of the application map in `defn:actions`.
-/
@[simp]
theorem applyAction_add (x y : Tuple X) :
    applyAction x (MarketAction.add y) = concat x y :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: cancellation case of the application map in `defn:actions`.
-/
@[simp]
theorem applyAction_cancel (x : Tuple X) (eta : FiniteSubsets ℕ) :
    applyAction x (MarketAction.cancel (X := X) eta) = Primitive.cancel x eta :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: modification case of the application map in `defn:actions`.
-/
@[simp]
theorem applyAction_modify (x : Tuple X) (xi : DistinctFiniteSubsets X) :
    applyAction x (MarketAction.modify xi) = Primitive.modify x xi :=
  rfl

/-! ## Action Metric -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: `cor:action-metrisation`.

Informal statement: the action-space extended distance is the disjoint-union
distance over the three primitive action payload spaces. Actions with the same
operation label are compared by the corresponding payload distance; actions
with different labels are at distance `∞`.

Lean strategy / thesis relation note: the thesis writes the action space as a finite disjoint union
and then applies the disjoint-union metric. Since `MarketAction` is the
Lean-native tagged union used for that finite disjoint union, the same metric
is written by pattern matching on constructors.
-/
noncomputable def actionEDistance {X : Type u} [EMetricSpace X] :
    MarketAction X → MarketAction X → ENNReal
  | MarketAction.add x, MarketAction.add y => edist x y
  | MarketAction.cancel eta, MarketAction.cancel theta => edist eta theta
  | MarketAction.modify xi, MarketAction.modify zeta => edist xi zeta
  | _, _ => ⊤

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: two addition actions are compared by the tuple Hausdorff
distance of their payload tuples.
-/
@[simp]
theorem actionEDistance_add_add {X : Type u} [EMetricSpace X]
    (x y : Tuple X) :
    actionEDistance (MarketAction.add x) (MarketAction.add y) = edist x y :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: two cancellation actions are compared by the finite-set
Hausdorff distance of their index sets.
-/
@[simp]
theorem actionEDistance_cancel_cancel {X : Type u} [EMetricSpace X]
    (eta theta : FiniteSubsets ℕ) :
    actionEDistance (MarketAction.cancel (X := X) eta)
      (MarketAction.cancel theta) = edist eta theta :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: two modification actions are compared by the distinct
finite-set Hausdorff distance of their replacement graphs.
-/
@[simp]
theorem actionEDistance_modify_modify {X : Type u} [EMetricSpace X]
    (xi zeta : DistinctFiniteSubsets X) :
    actionEDistance (MarketAction.modify xi) (MarketAction.modify zeta) =
      edist xi zeta :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: different action labels lie in different disjoint-union
components, so their action distance is `∞`.
-/
theorem actionEDistance_eq_top_of_kind_ne {X : Type u} [EMetricSpace X]
    {a b : MarketAction X} (h : a.kind ≠ b.kind) :
    actionEDistance a b = ⊤ := by
  cases a <;> cases b <;> simp [MarketAction.kind] at h
  all_goals rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: finite action distance forces the two actions to have the
same operation label.
-/
theorem kind_eq_of_actionEDistance_lt_top {X : Type u} [EMetricSpace X]
    {a b : MarketAction X} (h : actionEDistance a b < ⊤) :
    a.kind = b.kind := by
  by_contra hne
  have htop := actionEDistance_eq_top_of_kind_ne (X := X) hne
  rw [htop] at h
  exact (not_top_lt h).elim

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Original label: `cor:action-metrisation`, component family `F_α`.

Informal statement: the three payload spaces `F_⊕ = T(X)`, `F_⊖ = F(ℕ)` and
`F_⊛ = L(X)`, indexed by the operation labels and lifted to a common universe so
that they form a Lean `Sigma` family: the thesis disjoint union
`⨆_{α ∈ A} F_α`.
-/
def ActionFamily (X : Type u) : ActionKind → Type (max u 1)
  | .add => ULift.{max u 1} (Tuple X)
  | .cancel => ULift.{max u 1} (FiniteSubsets ℕ)
  | .modify => ULift.{max u 1} (DistinctFiniteSubsets X)

/-- Each component `F_α` carries its thesis metric `d_α` (universe lifting is
isometric). -/
@[reducible] noncomputable instance actionFamilyEMetricSpace {X : Type u} [EMetricSpace X]
    (k : ActionKind) : EMetricSpace (ActionFamily X k) := by
  cases k <;> dsimp [ActionFamily] <;> infer_instance

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Original label: `cor:action-metrisation`, `𝒜(X) = ⨆_{α ∈ A} F_α`.

Informal statement: the tagged union `MarketAction X` is (in bijection with)
the thesis disjoint union of the payload spaces.
-/
def actionSigmaEquiv (X : Type u) : MarketAction X ≃ Sigma (ActionFamily X) where
  toFun
    | .add y => ⟨.add, ⟨y⟩⟩
    | .cancel η => ⟨.cancel, ⟨η⟩⟩
    | .modify ξ => ⟨.modify, ⟨ξ⟩⟩
  invFun
    | ⟨.add, y⟩ => .add y.down
    | ⟨.cancel, η⟩ => .cancel η.down
    | ⟨.modify, ξ⟩ => .modify ξ.down
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨k, a⟩; cases k <;> rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Original label: `cor:action-metrisation`, definition of `Δ`.

Informal statement: under the identification `𝒜(X) = ⨆_α F_α`, the action
distance `Δ` is literally the disjoint-union distance of
`defn:disjoint-union-metrisation`.
-/
theorem disjointEdist_actionSigmaEquiv {X : Type u} [EMetricSpace X]
    (a b : MarketAction X) :
    DisjointUnionTopology.disjointEdist (actionSigmaEquiv X a) (actionSigmaEquiv X b) =
      actionEDistance a b := by
  cases a <;> cases b <;>
    simp [actionSigmaEquiv, DisjointUnionTopology.disjointEdist, actionEDistance] <;> rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: register the thesis action distance as the Lean extended
distance on the action space.
-/
noncomputable instance instEDist {X : Type u} [EMetricSpace X] :
    EDist (MarketAction X) where
  edist := actionEDistance

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: the action-space distance satisfies the extended
pseudometric laws.

Lean strategy / thesis relation note: exactly the thesis citation of
`prop:disjoint-union-metrisation`: by `disjointEdist_actionSigmaEquiv`, `Δ` is
the disjoint-union distance on `⨆_α F_α`, so the pseudometric laws are those of
`DisjointUnionTopology.disjointUnionEMetricSpace`.
-/
noncomputable instance instPseudoEMetricSpace {X : Type u} [EMetricSpace X] :
    PseudoEMetricSpace (MarketAction X) where
  edist_self := by
    intro a
    change actionEDistance a a = 0
    simp only [← disjointEdist_actionSigmaEquiv]
    exact (DisjointUnionTopology.disjointUnionEMetricSpace
      (X := ActionFamily X)).edist_self _
  edist_comm := by
    intro a b
    change actionEDistance a b = actionEDistance b a
    simp only [← disjointEdist_actionSigmaEquiv]
    exact (DisjointUnionTopology.disjointUnionEMetricSpace
      (X := ActionFamily X)).edist_comm _ _
  edist_triangle := by
    intro a b c
    change actionEDistance a c ≤ actionEDistance a b + actionEDistance b c
    simp only [← disjointEdist_actionSigmaEquiv]
    exact (DisjointUnionTopology.disjointUnionEMetricSpace
      (X := ActionFamily X)).edist_triangle _ _ _

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: the action-space pseudometric separates points, hence is
an extended metric.

Lean strategy / thesis relation note: as in the thesis, this is the separation
clause of `prop:disjoint-union-metrisation` for `⨆_α F_α`, transported along
the identification `actionSigmaEquiv`.
-/
noncomputable instance instEMetricSpace {X : Type u} [EMetricSpace X] :
    EMetricSpace (MarketAction X) :=
  EMetricSpace.mk (by
    intro a b h
    change actionEDistance a b = 0 at h
    rw [← disjointEdist_actionSigmaEquiv] at h
    exact (actionSigmaEquiv X).injective
      ((DisjointUnionTopology.disjointUnionEMetricSpace
        (X := ActionFamily X)).eq_of_edist_eq_zero h))

@[simp]
theorem edist_add_add {X : Type u} [EMetricSpace X] (x y : Tuple X) :
    edist (MarketAction.add x) (MarketAction.add y) = edist x y :=
  rfl

@[simp]
theorem edist_cancel_cancel {X : Type u} [EMetricSpace X]
    (eta theta : FiniteSubsets ℕ) :
    edist (MarketAction.cancel (X := X) eta) (MarketAction.cancel theta) =
      edist eta theta :=
  rfl

@[simp]
theorem edist_modify_modify {X : Type u} [EMetricSpace X]
    (xi zeta : DistinctFiniteSubsets X) :
    edist (MarketAction.modify xi) (MarketAction.modify zeta) =
      edist xi zeta :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Original label: `cor:action-metrisation`.

Informal statement: `(𝒜(X), Δ)` is isometric to the disjoint union
`⨆_{α ∈ A} F_α` carrying the metric of `prop:disjoint-union-metrisation`. This
is the identification through which the thesis cites the disjoint-union
propositions for the metric, completeness and separability of `𝒜(X)`.
-/
def actionSigmaIsometry (X : Type u) [EMetricSpace X] :
    letI : EMetricSpace (Sigma (ActionFamily X)) :=
      DisjointUnionTopology.disjointUnionEMetricSpace
    MarketAction X ≃ᵢ Sigma (ActionFamily X) := by
  letI : EMetricSpace (Sigma (ActionFamily X)) :=
    DisjointUnionTopology.disjointUnionEMetricSpace
  refine ⟨actionSigmaEquiv X, ?_⟩
  intro a b
  change DisjointUnionTopology.disjointEdist (actionSigmaEquiv X a) (actionSigmaEquiv X b) =
    actionEDistance a b
  exact disjointEdist_actionSigmaEquiv a b

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Original label: `cor:action-metrisation`.

Informal statement: topologically, the action space is the coproduct
`⨆_{α ∈ A} F_α` (every component is open). This follows from the isometry above
and the thesis topology bridge `metricTopology_eq_sigma`; it is the canonical
identification used by the pasting arguments below.
-/
def actionSigmaHomeomorph (X : Type u) [EMetricSpace X] :
    MarketAction X ≃ₜ Sigma (ActionFamily X) := by
  refine ⟨actionSigmaEquiv X, ?_, ?_⟩
  · rw [← DisjointUnionTopology.metricTopology_eq_sigma (X := ActionFamily X)]
    letI : EMetricSpace (Sigma (ActionFamily X)) :=
      DisjointUnionTopology.disjointUnionEMetricSpace
    letI : TopologicalSpace (Sigma (ActionFamily X)) :=
      DisjointUnionTopology.disjointUnionMetricTopology
    exact (actionSigmaIsometry X).continuous
  · rw [← DisjointUnionTopology.metricTopology_eq_sigma (X := ActionFamily X)]
    letI : EMetricSpace (Sigma (ActionFamily X)) :=
      DisjointUnionTopology.disjointUnionEMetricSpace
    letI : TopologicalSpace (Sigma (ActionFamily X)) :=
      DisjointUnionTopology.disjointUnionMetricTopology
    exact (actionSigmaIsometry X).symm.continuous

@[simp] theorem actionSigmaHomeomorph_apply {X : Type u} [EMetricSpace X]
    (a : MarketAction X) : actionSigmaHomeomorph X a = actionSigmaEquiv X a := rfl

@[simp] theorem actionSigmaHomeomorph_symm_apply {X : Type u} [EMetricSpace X]
    (a : Sigma (ActionFamily X)) :
    (actionSigmaHomeomorph X).symm a = (actionSigmaEquiv X).symm a := rfl

/-- Universe lifting is an isometric equivalence, so each lifted component of
`ActionFamily` has exactly the metric properties of its payload space. -/
def uliftIsometryEquiv (α : Type*) [PseudoEMetricSpace α] : ULift.{max u 1} α ≃ᵢ α :=
  ⟨Equiv.ulift, fun _ _ => rfl⟩

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: in the registered metric, actions in different operation
components have distance `∞`.
-/
theorem edist_eq_top_of_kind_ne {X : Type u} [EMetricSpace X]
    {a b : MarketAction X} (h : a.kind ≠ b.kind) :
    edist a b = ⊤ := by
  exact actionEDistance_eq_top_of_kind_ne (X := X) h

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrisation`.

Informal statement: finite registered action distance forces a shared
operation label.
-/
theorem kind_eq_of_edist_lt_top {X : Type u} [EMetricSpace X]
    {a b : MarketAction X} (h : edist a b < ⊤) :
    a.kind = b.kind :=
  kind_eq_of_actionEDistance_lt_top (X := X) h

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrisation`.

Informal statement: a Cauchy sequence of actions is eventually contained in
one operation component.

Lean strategy / thesis relation note: an auxiliary consequence of the
disjoint-union metric (distance `< ∞` forces equal tags, and a Cauchy sequence
is eventually at distance `< 1`); it is the action-space instance of
`DisjointUnionTopology.cauchySeq_eventually_constant_tag`. It is not used by
the mapped completeness proof `completeSpace`, which transfers
`prop:disjoint-union-metric-properties` along `actionSigmaIsometry`.
-/
theorem cauchySeq_eventually_constant_kind {X : Type u} [EMetricSpace X]
    {u : ℕ → MarketAction X} (hu : CauchySeq u) :
    ∃ N : ℕ, ∀ n, N ≤ n → (u n).kind = (u N).kind := by
  rcases (EMetric.cauchySeq_iff.1 hu) (1 : ENNReal) zero_lt_one with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hlt : edist (u n) (u N) < (⊤ : ENNReal) :=
    lt_trans (hN n hn N le_rfl) ENNReal.one_lt_top
  exact kind_eq_of_edist_lt_top hlt

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrisation`.

Informal statement: extract an addition payload, using a default value away
from the addition component.
-/
def addPayloadD (default : Tuple X) : MarketAction X → Tuple X
  | MarketAction.add y => y
  | _ => default

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrisation`.

Informal statement: extract a cancellation payload, using a default value
away from the cancellation component.
-/
def cancelPayloadD (default : FiniteSubsets ℕ) : MarketAction X → FiniteSubsets ℕ
  | MarketAction.cancel eta => eta
  | _ => default

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrisation`.

Informal statement: extract a modification payload, using a default value away
from the modification component.
-/
def modifyPayloadD (default : DistinctFiniteSubsets X) :
    MarketAction X → DistinctFiniteSubsets X
  | MarketAction.modify xi => xi
  | _ => default

theorem add_payload_mk_of_kind {X : Type u} {default : Tuple X}
    {a : MarketAction X} (h : a.kind = ActionKind.add) :
    MarketAction.add (addPayloadD default a) = a := by
  cases a <;> simp [MarketAction.kind, addPayloadD] at h ⊢

theorem cancel_payload_mk_of_kind {X : Type u} {default : FiniteSubsets ℕ}
    {a : MarketAction X} (h : a.kind = ActionKind.cancel) :
    MarketAction.cancel (X := X) (cancelPayloadD default a) = a := by
  cases a <;> simp [MarketAction.kind, cancelPayloadD] at h ⊢

theorem modify_payload_mk_of_kind {X : Type u}
    {default : DistinctFiniteSubsets X} {a : MarketAction X}
    (h : a.kind = ActionKind.modify) :
    MarketAction.modify (modifyPayloadD default a) = a := by
  cases a <;> simp [MarketAction.kind, modifyPayloadD] at h ⊢

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrisation`.

Informal statement: if `X` is complete, then the action space
`\mathscr{A}(X)` is complete.

Lean strategy / thesis relation note: this is the thesis proof. The components
are complete (`thm:tuple-space-properties` for `T(X)`,
`thm:labelled-properties` for `L(X)`, uniform discreteness for `F(ℕ)`), so the
disjoint union `⨆_α F_α` is complete by `prop:disjoint-union-metric-properties`
(`DisjointUnionTopology.completeSpace`), and `𝒜(X)` is isometric to it
(`actionSigmaIsometry`).
-/
theorem completeSpace {X : Type u} [EMetricSpace X] [CompleteSpace X] :
    CompleteSpace (MarketAction X) := by
  haveI : CompleteSpace (Tuple X) :=
    Thesis.Foundations.MarketRepresentation.TuplesMetricTopology.completeSpace (X := X)
  haveI : CompleteSpace (FiniteSubsets ℕ) :=
    finiteSubsets_completeSpace_of_isolative Analytic.nat_isolative_bound_one
  haveI : CompleteSpace (DistinctFiniteSubsets X) :=
    DistinctFiniteSubsets.completeSpace (α := X)
  haveI : ∀ k : ActionKind, CompleteSpace (ActionFamily X k) := by
    intro k
    cases k
    · exact (uliftIsometryEquiv (Tuple X)).completeSpace_iff.mpr inferInstance
    · exact (uliftIsometryEquiv (FiniteSubsets ℕ)).completeSpace_iff.mpr inferInstance
    · exact (uliftIsometryEquiv (DistinctFiniteSubsets X)).completeSpace_iff.mpr inferInstance
  letI : EMetricSpace (Sigma (ActionFamily X)) :=
    DisjointUnionTopology.disjointUnionEMetricSpace
  haveI hc : CompleteSpace (Sigma (ActionFamily X)) :=
    DisjointUnionTopology.completeSpace (X := ActionFamily X)
  exact (actionSigmaIsometry X).completeSpace_iff.mpr hc

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrisation`.

Informal statement: if `X` is separable, then the action space
`\mathscr{A}(X)` is separable.

Lean strategy / thesis relation note: this is the thesis proof. The components
are separable (`thm:tuple-space-properties`, `thm:labelled-properties`,
`prop:finite-separable`), so the finite disjoint union `⨆_α F_α` is separable
by `prop:disjoint-union-metric-properties`
(`DisjointUnionTopology.separableSpace_sigma_of_countable`), and `𝒜(X)` is
homeomorphic to it (`actionSigmaHomeomorph`, built from the isometry).
-/
theorem separableSpace {X : Type u} [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (MarketAction X) := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  haveI : TopologicalSpace.SeparableSpace (Tuple X) :=
    Thesis.Foundations.MarketRepresentation.TuplesMetricTopology.separableSpace (X := X)
  haveI : TopologicalSpace.SeparableSpace (FiniteSubsets ℕ) :=
    finiteSubsets_separableSpace (α := ℕ)
  haveI : TopologicalSpace.SeparableSpace (DistinctFiniteSubsets X) :=
    DistinctFiniteSubsets.separableSpace (α := X)
  haveI : ∀ k : ActionKind, TopologicalSpace.SeparableSpace (ActionFamily X k) := by
    intro k
    cases k
    · exact (uliftIsometryEquiv (Tuple X)).symm.surjective.denseRange.separableSpace
        (uliftIsometryEquiv (Tuple X)).symm.continuous
    · exact (uliftIsometryEquiv (FiniteSubsets ℕ)).symm.surjective.denseRange.separableSpace
        (uliftIsometryEquiv (FiniteSubsets ℕ)).symm.continuous
    · exact (uliftIsometryEquiv
        (DistinctFiniteSubsets X)).symm.surjective.denseRange.separableSpace
        (uliftIsometryEquiv (DistinctFiniteSubsets X)).symm.continuous
  haveI : TopologicalSpace.SeparableSpace (Sigma (ActionFamily X)) :=
    DisjointUnionTopology.separableSpace_sigma_of_countable (X := ActionFamily X)
  exact (actionSigmaHomeomorph X).symm.surjective.denseRange.separableSpace
    (actionSigmaHomeomorph X).symm.continuous

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`prop:application-continuous`.

Informal statement: if an action is finitely close to an addition action,
then it is itself an addition action and its tuple payload is close.

Lean strategy / thesis relation note: an auxiliary local consequence of the
disjoint-union metric (different components have distance `∞`, so any
finite-radius neighborhood of an addition action stays in the addition
component). It is not used by the mapped continuity proof below, which follows
the thesis pasting argument.
-/
theorem exists_add_payload_of_edist_lt {X : Type u} [EMetricSpace X]
    {a : MarketAction X} {y₀ : Tuple X} {δ : ENNReal}
    (h : edist a (MarketAction.add y₀) < δ) :
    ∃ y : Tuple X, a = MarketAction.add y ∧ edist y y₀ < δ := by
  change actionEDistance a (MarketAction.add y₀) < δ at h
  cases a with
  | add y =>
      exact ⟨y, rfl, by simpa [actionEDistance] using h⟩
  | cancel eta =>
      simp [actionEDistance] at h
  | modify xi =>
      simp [actionEDistance] at h

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`prop:application-continuous`.

Informal statement: finite closeness to a cancellation action forces the
nearby action to be cancellation, with close finite-index payload.
-/
theorem exists_cancel_payload_of_edist_lt {X : Type u} [EMetricSpace X]
    {a : MarketAction X} {eta₀ : FiniteSubsets ℕ} {δ : ENNReal}
    (h : edist a (MarketAction.cancel (X := X) eta₀) < δ) :
    ∃ eta : FiniteSubsets ℕ,
      a = MarketAction.cancel (X := X) eta ∧ edist eta eta₀ < δ := by
  change actionEDistance a (MarketAction.cancel (X := X) eta₀) < δ at h
  cases a with
  | add y =>
      simp [actionEDistance] at h
  | cancel eta =>
      exact ⟨eta, rfl, by simpa [actionEDistance] using h⟩
  | modify xi =>
      simp [actionEDistance] at h

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`prop:application-continuous`.

Informal statement: finite closeness to a modification action forces the
nearby action to be modification, with close distinct finite-set payload.
-/
theorem exists_modify_payload_of_edist_lt {X : Type u} [EMetricSpace X]
    {a : MarketAction X} {xi₀ : DistinctFiniteSubsets X} {δ : ENNReal}
    (h : edist a (MarketAction.modify xi₀) < δ) :
    ∃ xi : DistinctFiniteSubsets X,
      a = MarketAction.modify xi ∧ edist xi xi₀ < δ := by
  change actionEDistance a (MarketAction.modify xi₀) < δ at h
  cases a with
  | add y =>
      simp [actionEDistance] at h
  | cancel eta =>
      simp [actionEDistance] at h
  | modify xi =>
      exact ⟨xi, rfl, by simpa [actionEDistance] using h⟩

/-- Product distributes over the open coproduct: a map out of `P × ⨆_a F a` is
continuous iff each restriction to `P × F a` is. This is the canonical
homeomorphism `P × ⨆_a F_a ≅ ⨆_a (P × F_a)` (every component is open) followed
by the pasting lemma for disjoint unions. -/
theorem continuous_prod_sigma_iff {A : Type*} {F : A → Type*} {P Z : Type*}
    [∀ a, TopologicalSpace (F a)] [TopologicalSpace P] [TopologicalSpace Z]
    (f : P × Sigma F → Z) :
    Continuous f ↔ ∀ a, Continuous (fun p : P × F a => f (p.1, ⟨a, p.2⟩)) := by
  let h : P × Sigma F ≃ₜ Sigma (fun a => F a × P) :=
    (Homeomorph.prodComm P (Sigma F)).trans Homeomorph.sigmaProdDistrib
  have hp : Continuous f ↔ Continuous (f ∘ h.symm) :=
    h.symm.comp_continuous_iff'.symm
  rw [hp, continuous_sigma_iff]
  constructor
  · intro hf a
    exact (hf a).comp (Homeomorph.prodComm P (F a)).continuous
  · intro hf a
    exact (hf a).comp (Homeomorph.prodComm (F a) P).continuous

section PastingContinuity

-- Keep the structural algorithms opaque while transporting continuity;
-- otherwise elaboration expands cancellation's finite survivor enumeration.
attribute [local irreducible] Primitive.cancel Primitive.modify

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`prop:application-continuous`.

Informal statement: the action application map
`\mathscr{T}(X) × \mathscr{A}(X) → \mathscr{T}(X)` is continuous.

Lean strategy / thesis relation note: this is the thesis proof. The canonical
identification `T(X) × ⨆_α F_α ≅ ⨆_α (T(X) × F_α)` is a homeomorphism
(`actionSigmaHomeomorph` followed by `continuous_prod_sigma_iff`); the
restriction of `◁` to each component is exactly the corresponding primitive
operation, which is continuous by `thm:analytic-properties-actions`; and the
pasting lemma for disjoint unions gives continuity of `◁`. No epsilon-delta
argument is used.
-/
theorem continuous_applyAction_emetricTopology {X : Type u} [EMetricSpace X] :
    @Continuous (Tuple X × MarketAction X) (Tuple X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p : Tuple X × MarketAction X => applyAction p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) := Analytic.emetricTopology _
  letI : TopologicalSpace (MarketAction X) := Analytic.emetricTopology _
  letI : TopologicalSpace (FiniteSubsets ℕ) := Analytic.emetricTopology _
  letI : TopologicalSpace (DistinctFiniteSubsets X) := Analytic.emetricTopology _
  letI (k : ActionKind) : TopologicalSpace (ActionFamily X k) :=
    (actionFamilyEMetricSpace k).toUniformSpace.toTopologicalSpace
  let h := actionSigmaHomeomorph X
  have hc : Continuous (fun p : Tuple X × Sigma (ActionFamily X) =>
      applyAction p.1 (h.symm p.2)) := by
    dsimp only [h]
    simp_rw [actionSigmaHomeomorph_symm_apply]
    rw [continuous_prod_sigma_iff]
    intro k
    cases k
    all_goals dsimp only [actionSigmaEquiv, Equiv.symm, applyAction]
    · have hd : Isometry (fun p : Tuple X × ActionFamily X .add => (p.1, p.2.down)) := by
        intro p q
        rfl
      exact @Continuous.comp _ (Tuple X × Tuple X) (Tuple X) inferInstance
        (Analytic.emetricTopology _) (Analytic.emetricTopology _) _ _
        (Analytic.continuous_concat_emetricTopology (X := X)) hd.continuous
    · have hd : Isometry (fun p : Tuple X × ActionFamily X .cancel => (p.1, p.2.down)) := by
        intro p q
        rfl
      exact @Continuous.comp _ (Tuple X × FiniteSubsets ℕ) (Tuple X) inferInstance
        (Analytic.emetricTopology _) (Analytic.emetricTopology _) _ _
        (Analytic.continuous_cancel_emetricTopology (X := X)) hd.continuous
    · have hd : Isometry (fun p : Tuple X × ActionFamily X .modify => (p.1, p.2.down)) := by
        intro p q
        rfl
      exact @Continuous.comp _ (Tuple X × DistinctFiniteSubsets X) (Tuple X) inferInstance
        (Analytic.emetricTopology _) (Analytic.emetricTopology _) _ _
        (Analytic.continuous_modify_emetricTopology (X := X)) hd.continuous
  simpa only [Function.comp_def, h.symm_apply_apply] using
    hc.comp (continuous_fst.prodMk (h.continuous.comp continuous_snd))

end PastingContinuity

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`prop:application-continuous`.

Informal statement: the action application map is continuous at every point
for the thesis extended-metric topologies.

Lean strategy / thesis relation note: the pointwise form of the pasting proof
`continuous_applyAction_emetricTopology`.
-/
theorem continuousAt_applyAction_emetricTopology {X : Type u} [EMetricSpace X]
    (p₀ : Tuple X × MarketAction X) :
    @ContinuousAt (Tuple X × MarketAction X) (Tuple X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p : Tuple X × MarketAction X => applyAction p.1 p.2) p₀ := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (MarketAction X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Tuple X × MarketAction X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  exact (continuous_applyAction_emetricTopology (X := X)).continuousAt

/-! ## Composite Actions -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: `defn:composite-actions`.

Informal statement: a composite action is a tuple of admissible single
actions.

Lean strategy / thesis relation note: this directly follows the thesis equation
`\mathscr{C}(X)=\mathscr{T}(\mathscr{A}(X))`.
-/
abbrev CompositeAction (X : Type u) : Type (max u 1) :=
  Tuple (MarketAction X)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`thm:composite-action-metric`.

Informal statement: the composite-action space carries the tuple Hausdorff
extended metric induced by the action-space metric `Δ`.

Lean strategy / thesis relation note: because `CompositeAction X` is definitionally
`Tuple (MarketAction X)`, the metric is exactly the existing tuple Hausdorff
metric instance applied to the action space.
-/
@[reducible]
noncomputable def compositeActionEMetricSpace {X : Type u} [EMetricSpace X] :
    EMetricSpace (CompositeAction X) :=
  inferInstance

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`thm:composite-action-metric`.

Informal statement: the registered distance on composite actions is the tuple
Hausdorff distance induced by the action metric.
-/
theorem compositeAction_edist_eq_tupleHausdorffEDistance {X : Type u}
    [EMetricSpace X] (c d : CompositeAction X) :
    edist c d = TuplesMetricTopology.tupleHausdorffEDistance c d :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`thm:composite-action-metric`.

Informal statement: if `X` is complete, then the composite-action space
`\mathscr{C}(X)=\mathscr{T}(\mathscr{A}(X))` is complete.

Lean strategy / thesis relation note: this is exactly the thesis proof: combine
`cor:action-metrisation` for completeness of `\mathscr{A}(X)` with
the Chapter 2 tuple-space completeness theorem.

Lean strategy / thesis strategy note: this declaration belongs to `thm:composite-action-metric`.
It uses the tuple-space completeness theorem as an imported dependency; it is
not itself one of the five clauses of the Chapter 2 tuple-space-properties
theorem.
-/
theorem compositeAction_completeSpace {X : Type u} [EMetricSpace X]
    [CompleteSpace X] : CompleteSpace (CompositeAction X) := by
  haveI : CompleteSpace (MarketAction X) := completeSpace (X := X)
  exact Thesis.Foundations.MarketRepresentation.TuplesMetricTopology.completeSpace
    (X := MarketAction X)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`thm:composite-action-metric`.

Informal statement: if `X` is separable, then the composite-action space
`\mathscr{C}(X)=\mathscr{T}(\mathscr{A}(X))` is separable for the induced
tuple Hausdorff topology.

Lean strategy / thesis relation note: as with tuple spaces, the separability statement is explicit
about the extended-metric topology to avoid Lean's native Sigma topology for
tuples.
-/
theorem compositeAction_separableSpace {X : Type u} [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] :
    @TopologicalSpace.SeparableSpace
      (CompositeAction X) PseudoEMetricSpace.toUniformSpace.toTopologicalSpace := by
  haveI : TopologicalSpace.SeparableSpace (MarketAction X) :=
    separableSpace (X := X)
  exact Thesis.Foundations.MarketRepresentation.TuplesMetricTopology.separableSpace
    (X := MarketAction X)

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: recursive application equation
`eq:recursive-application`.

Informal statement: list the actions in a composite action in their tuple
order so they can be applied sequentially.

Lean strategy / thesis relation note: the thesis indexes from `1` to `n`; Lean uses `Fin n`, and
`List.ofFn` enumerates `Fin n` in increasing zero-based order.
-/
def compositeActionList (c : CompositeAction X) : List (MarketAction X) :=
  List.ofFn c.2

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: `defn:composite-actions`, extended application map in
Definition "Composite Actions".

Informal statement: apply a composite action by applying each single action in
tuple order, returning the original tuple for the empty composite action.

Lean strategy / thesis relation note: the thesis defines this recursively. Lean implements the same
recursion as a left fold over the ordered list of action entries.
-/
noncomputable def applyCompositeAction (x : Tuple X) (c : CompositeAction X) :
    Tuple X :=
  (compositeActionList c).foldl applyAction x

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: empty-composite case in Definition "Composite Actions".

Informal statement: applying the empty composite action leaves the market
tuple unchanged.
-/
@[simp]
theorem applyCompositeAction_empty (x : Tuple X) :
    applyCompositeAction x (Tuple.empty (MarketAction X)) = x := by
  simp [applyCompositeAction, compositeActionList, Tuple.empty]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: recursive application equation
`eq:recursive-application`.

Informal statement: for a composite action represented by `Fin n → A(X)`,
application is left-folded application of the entries in index order.
-/
@[simp]
theorem applyCompositeAction_mk (x : Tuple X) {n : ℕ}
    (c : Fin n → MarketAction X) :
    applyCompositeAction x (Sigma.mk n c : CompositeAction X) =
      (List.ofFn c).foldl applyAction x :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`thm:composite-application-continuous`.

Informal statement: on a fixed composite-action length layer
`\mathscr{C}_n(X) ≃ \mathscr{A}(X)^n`, recursive application is continuous.

Lean strategy / thesis relation note: this is the thesis recursion
`Φ_0(x) = x` and `Φ_n(x, a_1, …, a_n) = Φ_{n-1}(x, a_1, …, a_{n-1}) ◁ a_n`.
Lean uses zero-based `Fin` indices and `List.ofFn`; the proof is induction on
the composite length, peeling off the last action (`List.ofFn_succ'`) and using
the continuity of the one-step application map
(`prop:application-continuous`).
-/
theorem continuous_fixedCompositeApply_emetricTopology {X : Type u}
    [EMetricSpace X] (n : ℕ) :
    @Continuous (Tuple X × (Fin n → MarketAction X)) (Tuple X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p : Tuple X × (Fin n → MarketAction X) =>
        (List.ofFn p.2).foldl applyAction p.1) := by
  induction n with
  | zero =>
      letI : TopologicalSpace (Tuple X) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (MarketAction X) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (Fin 0 → MarketAction X) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (Tuple X × (Fin 0 → MarketAction X)) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      simpa using (@continuous_fst (Tuple X) (Fin 0 → MarketAction X) _ _)
  | succ n ih =>
      letI : TopologicalSpace (Tuple X) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (MarketAction X) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (Fin n → MarketAction X) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (Fin (n + 1) → MarketAction X) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (Tuple X × MarketAction X) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (Tuple X × (Fin n → MarketAction X)) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (Tuple X × (Fin (n + 1) → MarketAction X)) :=
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      -- `(x, a_1, …, a_{n-1})`: drop the last action
      have hinit :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            (p.1, fun i : Fin n => p.2 (Fin.castSucc i))) :=
        continuous_fst.prodMk
          (continuous_pi fun i => (continuous_apply (Fin.castSucc i)).comp continuous_snd)
      -- `Φ_{n-1}(x, a_1, …, a_{n-1})`
      have hprev :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            (List.ofFn (fun i : Fin n => p.2 (Fin.castSucc i))).foldl applyAction p.1) :=
        ih.comp hinit
      -- the last action `a_n`
      have hlast :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            p.2 (Fin.last n)) :=
        (continuous_apply (Fin.last n)).comp continuous_snd
      -- `Φ_n = Φ_{n-1} ◁ a_n`, continuous by `prop:application-continuous`
      have hstep :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            applyAction
              ((List.ofFn (fun i : Fin n => p.2 (Fin.castSucc i))).foldl applyAction p.1)
              (p.2 (Fin.last n))) :=
        (continuous_applyAction_emetricTopology (X := X)).comp (hprev.prodMk hlast)
      refine hstep.congr (fun p => ?_)
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons,
        List.foldl_nil]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`thm:composite-application-continuous`.

Informal statement: the extended application map
`\mathscr{T}(X) × \mathscr{C}(X) → \mathscr{T}(X)` is continuous.

Lean strategy / thesis relation note: this is the thesis proof. The fixed-length
maps `Φ_n` are continuous by induction
(`continuous_fixedCompositeApply_emetricTopology`); the standard machinery
identifies the composite tuple topology with the coproduct of its length layers
`𝒞(X) = ⨆ₙ 𝒞ₙ(X)` (`tupleHausdorffMetricTopology_eq_sigma`); the product with
`T(X)` distributes over this coproduct (`continuous_prod_sigma_iff`), and the
pasting lemma for disjoint unions gives global continuity.
-/
theorem continuous_applyCompositeAction_emetricTopology {X : Type u}
    [EMetricSpace X] :
    @Continuous (Tuple X × CompositeAction X) (Tuple X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p : Tuple X × CompositeAction X =>
        applyCompositeAction p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) := Analytic.emetricTopology _
  letI : TopologicalSpace (MarketAction X) := Analytic.emetricTopology _
  change @Continuous _ _
    (@instTopologicalSpaceProd (Tuple X) (CompositeAction X) (Analytic.emetricTopology _)
      (tupleHausdorffMetricTopology (X := MarketAction X))) (Analytic.emetricTopology _) _
  rw [tupleHausdorffMetricTopology_eq_sigma]
  rw [continuous_prod_sigma_iff]
  intro n
  exact continuous_fixedCompositeApply_emetricTopology n

end Composite
end MarketActions
end Foundations
end Thesis
