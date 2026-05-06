import Foundations.MarketActions.Analytic

/-!
# Market Actions: Composite Actions

Blueprint module for
`1 - theoretical foundations/3_market_actions.tex`,
section "Composite Actions".

Planned formal content:

* `defn:actions`;
* action space and evaluation map;
* composite actions;
* `cor:action-metrization`;
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

Original label: `cor:action-metrization`.

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
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

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
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

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
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

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
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

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
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

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
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

Informal statement: register the thesis action distance as the Lean extended
distance on the action space.
-/
noncomputable instance instEDist {X : Type u} [EMetricSpace X] :
    EDist (MarketAction X) where
  edist := actionEDistance

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

Informal statement: the action-space distance satisfies the extended
pseudometric laws.
-/
noncomputable instance instPseudoEMetricSpace {X : Type u} [EMetricSpace X] :
    PseudoEMetricSpace (MarketAction X) where
  edist_self := by
    intro a
    change actionEDistance a a = 0
    cases a <;> simp [actionEDistance]
  edist_comm := by
    intro a b
    change actionEDistance a b = actionEDistance b a
    cases a <;> cases b <;> simp [actionEDistance, edist_comm]
  edist_triangle := by
    intro a b c
    change actionEDistance a c ≤ actionEDistance a b + actionEDistance b c
    cases a <;> cases b <;> cases c <;> simp [actionEDistance, edist_triangle]

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

Informal statement: the action-space pseudometric separates points, hence is
an extended metric.

Lean strategy / thesis relation note: constructor equality is used to translate equality of payloads
back to equality in the finite tagged union.
-/
noncomputable instance instEMetricSpace {X : Type u} [EMetricSpace X] :
    EMetricSpace (MarketAction X) :=
  EMetricSpace.mk (by
    intro a b h
    change actionEDistance a b = 0 at h
    cases a with
    | add x =>
        cases b with
        | add y =>
            have hxy : x = y := by
              simpa [actionEDistance] using h
            simp [hxy]
        | cancel eta =>
            simp [actionEDistance] at h
        | modify xi =>
            simp [actionEDistance] at h
    | cancel eta =>
        cases b with
        | add x =>
            simp [actionEDistance] at h
        | cancel theta =>
            have heta : eta = theta := by
              simpa [actionEDistance] using h
            simp [heta]
        | modify xi =>
            simp [actionEDistance] at h
    | modify xi =>
        cases b with
        | add x =>
            simp [actionEDistance] at h
        | cancel eta =>
            simp [actionEDistance] at h
        | modify zeta =>
            have hxi : xi = zeta := by
              simpa [actionEDistance] using h
            simp [hxi])

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
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

Informal statement: in the registered metric, actions in different operation
components have distance `∞`.
-/
theorem edist_eq_top_of_kind_ne {X : Type u} [EMetricSpace X]
    {a b : MarketAction X} (h : a.kind ≠ b.kind) :
    edist a b = ⊤ := by
  exact actionEDistance_eq_top_of_kind_ne (X := X) h

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, `cor:action-metrization`.

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
`cor:action-metrization`.

Informal statement: a Cauchy sequence of actions is eventually contained in
one operation component.

Lean strategy / thesis relation note: this is the finite tagged-union analogue of the thesis'
disjoint-union completeness proof: distance `< ∞` forces equal tags, and a
Cauchy sequence is eventually at distance `< 1`.
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
`cor:action-metrization`.

Informal statement: extract an addition payload, using a default value away
from the addition component.
-/
def addPayloadD (default : Tuple X) : MarketAction X → Tuple X
  | MarketAction.add y => y
  | _ => default

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrization`.

Informal statement: extract a cancellation payload, using a default value
away from the cancellation component.
-/
def cancelPayloadD (default : FiniteSubsets ℕ) : MarketAction X → FiniteSubsets ℕ
  | MarketAction.cancel eta => eta
  | _ => default

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrization`.

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
`cor:action-metrization`.

Informal statement: if `X` is complete, then the action space
`\mathscr{A}(X)` is complete.

Lean strategy / thesis relation note: this follows the thesis proof via the disjoint-union metric.
After the action tag stabilizes, the Cauchy sequence reduces to a Cauchy
sequence in the matching payload space: tuples, finite natural-number sets,
or distinct finite sets.
-/
theorem completeSpace {X : Type u} [EMetricSpace X] [CompleteSpace X] :
    CompleteSpace (MarketAction X) := by
  haveI : CompleteSpace (Tuple X) :=
    Thesis.Foundations.MarketRepresentation.TuplesMetricTopology.completeSpace (X := X)
  haveI : CompleteSpace (FiniteSubsets ℕ) :=
    finiteSubsets_completeSpace_of_isolative Analytic.nat_isolative_bound_one
  haveI : CompleteSpace (DistinctFiniteSubsets X) :=
    DistinctFiniteSubsets.completeSpace (α := X)
  refine EMetric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  rcases cauchySeq_eventually_constant_kind hu with ⟨N, hNkind⟩
  cases hbase : u N with
  | add y₀ =>
      let v : ℕ → Tuple X := fun n => addPayloadD y₀ (u n)
      have hv_cauchy : CauchySeq v := by
        rw [EMetric.cauchySeq_iff]
        intro ε hε
        rcases (EMetric.cauchySeq_iff.1 hu) ε hε with ⟨M, hM⟩
        refine ⟨max N M, ?_⟩
        intro m hm n hn
        have hmN : N ≤ m := le_trans (le_max_left N M) hm
        have hnN : N ≤ n := le_trans (le_max_left N M) hn
        have hmM : M ≤ m := le_trans (le_max_right N M) hm
        have hnM : M ≤ n := le_trans (le_max_right N M) hn
        have hmkind : (u m).kind = ActionKind.add := by
          simpa [hbase, MarketAction.kind] using hNkind m hmN
        have hnkind : (u n).kind = ActionKind.add := by
          simpa [hbase, MarketAction.kind] using hNkind n hnN
        have hmact := add_payload_mk_of_kind (default := y₀) hmkind
        have hnact := add_payload_mk_of_kind (default := y₀) hnkind
        have hdist : edist (u m) (u n) < ε := hM m hmM n hnM
        have hvdist : edist (v m) (v n) = edist (u m) (u n) := by
          rw [← hmact, ← hnact]
          rfl
        simpa [hvdist] using hdist
      rcases _root_.cauchySeq_tendsto_of_complete hv_cauchy with ⟨y, hy⟩
      refine ⟨MarketAction.add y, ?_⟩
      rw [EMetric.tendsto_nhds]
      intro ε hε
      have hyε := EMetric.tendsto_nhds.1 hy ε hε
      have hNevent : ∀ᶠ n in Filter.atTop, N ≤ n :=
        Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩
      filter_upwards [hyε, hNevent] with n hnε hnN
      have hnkind : (u n).kind = ActionKind.add := by
        simpa [hbase, MarketAction.kind] using hNkind n hnN
      have hnact := add_payload_mk_of_kind (default := y₀) hnkind
      have hdist : edist (MarketAction.add (v n)) (MarketAction.add y) < ε := by
        simpa [v] using hnε
      rw [← hnact]
      simpa [v] using hnε
  | cancel eta₀ =>
      let v : ℕ → FiniteSubsets ℕ := fun n => cancelPayloadD eta₀ (u n)
      have hv_cauchy : CauchySeq v := by
        rw [EMetric.cauchySeq_iff]
        intro ε hε
        rcases (EMetric.cauchySeq_iff.1 hu) ε hε with ⟨M, hM⟩
        refine ⟨max N M, ?_⟩
        intro m hm n hn
        have hmN : N ≤ m := le_trans (le_max_left N M) hm
        have hnN : N ≤ n := le_trans (le_max_left N M) hn
        have hmM : M ≤ m := le_trans (le_max_right N M) hm
        have hnM : M ≤ n := le_trans (le_max_right N M) hn
        have hmkind : (u m).kind = ActionKind.cancel := by
          simpa [hbase, MarketAction.kind] using hNkind m hmN
        have hnkind : (u n).kind = ActionKind.cancel := by
          simpa [hbase, MarketAction.kind] using hNkind n hnN
        have hmact := cancel_payload_mk_of_kind (default := eta₀) hmkind
        have hnact := cancel_payload_mk_of_kind (default := eta₀) hnkind
        have hdist : edist (u m) (u n) < ε := hM m hmM n hnM
        have hvdist : edist (v m) (v n) = edist (u m) (u n) := by
          rw [← hmact, ← hnact]
          rfl
        simpa [hvdist] using hdist
      rcases _root_.cauchySeq_tendsto_of_complete hv_cauchy with ⟨eta, heta⟩
      refine ⟨MarketAction.cancel (X := X) eta, ?_⟩
      rw [EMetric.tendsto_nhds]
      intro ε hε
      have hetaε := EMetric.tendsto_nhds.1 heta ε hε
      have hNevent : ∀ᶠ n in Filter.atTop, N ≤ n :=
        Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩
      filter_upwards [hetaε, hNevent] with n hnε hnN
      have hnkind : (u n).kind = ActionKind.cancel := by
        simpa [hbase, MarketAction.kind] using hNkind n hnN
      have hnact := cancel_payload_mk_of_kind (default := eta₀) hnkind
      have hdist :
          edist (MarketAction.cancel (X := X) (v n))
            (MarketAction.cancel eta) < ε := by
        simpa [v] using hnε
      rw [← hnact]
      simpa [v] using hnε
  | modify xi₀ =>
      let v : ℕ → DistinctFiniteSubsets X := fun n => modifyPayloadD xi₀ (u n)
      have hv_cauchy : CauchySeq v := by
        rw [EMetric.cauchySeq_iff]
        intro ε hε
        rcases (EMetric.cauchySeq_iff.1 hu) ε hε with ⟨M, hM⟩
        refine ⟨max N M, ?_⟩
        intro m hm n hn
        have hmN : N ≤ m := le_trans (le_max_left N M) hm
        have hnN : N ≤ n := le_trans (le_max_left N M) hn
        have hmM : M ≤ m := le_trans (le_max_right N M) hm
        have hnM : M ≤ n := le_trans (le_max_right N M) hn
        have hmkind : (u m).kind = ActionKind.modify := by
          simpa [hbase, MarketAction.kind] using hNkind m hmN
        have hnkind : (u n).kind = ActionKind.modify := by
          simpa [hbase, MarketAction.kind] using hNkind n hnN
        have hmact := modify_payload_mk_of_kind (default := xi₀) hmkind
        have hnact := modify_payload_mk_of_kind (default := xi₀) hnkind
        have hdist : edist (u m) (u n) < ε := hM m hmM n hnM
        have hvdist : edist (v m) (v n) = edist (u m) (u n) := by
          rw [← hmact, ← hnact]
          rfl
        simpa [hvdist] using hdist
      rcases _root_.cauchySeq_tendsto_of_complete hv_cauchy with ⟨xi, hxi⟩
      refine ⟨MarketAction.modify xi, ?_⟩
      rw [EMetric.tendsto_nhds]
      intro ε hε
      have hxiε := EMetric.tendsto_nhds.1 hxi ε hε
      have hNevent : ∀ᶠ n in Filter.atTop, N ≤ n :=
        Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩
      filter_upwards [hxiε, hNevent] with n hnε hnN
      have hnkind : (u n).kind = ActionKind.modify := by
        simpa [hbase, MarketAction.kind] using hNkind n hnN
      have hnact := modify_payload_mk_of_kind (default := xi₀) hnkind
      have hdist : edist (MarketAction.modify (v n)) (MarketAction.modify xi) < ε := by
        simpa [v] using hnε
      rw [← hnact]
      simpa [v] using hnε

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`cor:action-metrization`.

Informal statement: if `X` is separable, then the action space
`\mathscr{A}(X)` is separable.

Lean strategy / thesis relation note: the countable dense set is the finite union of the constructor
images of countable dense sets in the three payload spaces, matching the
thesis' appeal to finite disjoint-union separability.
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
  rcases TopologicalSpace.exists_countable_dense (Tuple X) with
    ⟨Dadd, hDadd_count, hDadd_dense⟩
  rcases TopologicalSpace.exists_countable_dense (FiniteSubsets ℕ) with
    ⟨Dcancel, hDcancel_count, hDcancel_dense⟩
  rcases TopologicalSpace.exists_countable_dense (DistinctFiniteSubsets X) with
    ⟨Dmodify, hDmodify_count, hDmodify_dense⟩
  let D : Set (MarketAction X) :=
    MarketAction.add '' Dadd ∪
      (MarketAction.cancel (X := X) '' Dcancel ∪
        MarketAction.modify '' Dmodify)
  refine ⟨⟨D, ?_, ?_⟩⟩
  · simpa [D] using (hDadd_count.image MarketAction.add).union
      ((hDcancel_count.image (MarketAction.cancel (X := X))).union
        (hDmodify_count.image MarketAction.modify))
  · rw [dense_iff_closure_eq]
    apply Set.eq_univ_iff_forall.mpr
    intro a
    rw [EMetric.mem_closure_iff]
    intro ε hε
    cases a with
    | add y =>
        have hycl : y ∈ closure Dadd := by
          rw [dense_iff_closure_eq.mp hDadd_dense]
          trivial
        rcases (EMetric.mem_closure_iff.mp hycl) ε hε with ⟨z, hzD, hzε⟩
        refine ⟨MarketAction.add z, ?_, ?_⟩
        · simp [D, hzD]
        · simpa using hzε
    | cancel eta =>
        have hetacl : eta ∈ closure Dcancel := by
          rw [dense_iff_closure_eq.mp hDcancel_dense]
          trivial
        rcases (EMetric.mem_closure_iff.mp hetacl) ε hε with ⟨theta, hthetaD, hthetaε⟩
        refine ⟨MarketAction.cancel (X := X) theta, ?_, ?_⟩
        · simp [D, hthetaD]
        · simpa using hthetaε
    | modify xi =>
        have hξcl : xi ∈ closure Dmodify := by
          rw [dense_iff_closure_eq.mp hDmodify_dense]
          trivial
        rcases (EMetric.mem_closure_iff.mp hξcl) ε hε with ⟨zeta, hzetaD, hzetaε⟩
        refine ⟨MarketAction.modify zeta, ?_, ?_⟩
        · simp [D, hzetaD]
        · simpa using hzetaε

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`prop:application-continuous`.

Informal statement: if an action is finitely close to an addition action,
then it is itself an addition action and its tuple payload is close.

Lean strategy / thesis relation note: this is the local metric form of the thesis pasting argument:
different disjoint-union components have distance `∞`, so any finite-radius
neighborhood of an addition action stays in the addition component.
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

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`prop:application-continuous`.

Informal statement: the action application map is continuous at every point
for the thesis extended-metric topologies.

Lean strategy / thesis relation note: the thesis proves this by restricting the application map to
each disjoint-union component and applying the pasting lemma. Lean spells out
the same idea in epsilon-delta form: finite distance to a tagged action forces
the same tag, after which the corresponding primitive continuity theorem
applies.
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
  rcases p₀ with ⟨x₀, a₀⟩
  cases a₀ with
  | add y₀ =>
      have hprim :
          Filter.Tendsto (fun p : Tuple X × Tuple X => concat p.1 p.2)
            (nhds (x₀, y₀)) (nhds (concat x₀ y₀)) :=
        Analytic.continuousAt_concat_emetricTopology (X := X) (p₀ := (x₀, y₀))
      rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
      rw [EMetric.tendsto_nhds_nhds] at hprim
      intro ε hε
      rcases hprim ε hε with ⟨δ, hδpos, hδ⟩
      let ρ : ENNReal := min δ 1
      refine ⟨ρ, lt_min hδpos zero_lt_one, ?_⟩
      intro p hp
      rcases p with ⟨x, a⟩
      rw [Prod.edist_eq] at hp
      have hxρ : edist x x₀ < ρ := (max_lt_iff.mp hp).1
      have haρ : edist a (MarketAction.add y₀) < ρ := (max_lt_iff.mp hp).2
      have hxδ : edist x x₀ < δ :=
        lt_of_lt_of_le hxρ (min_le_left δ (1 : ENNReal))
      have haδ : edist a (MarketAction.add y₀) < δ :=
        lt_of_lt_of_le haρ (min_le_left δ (1 : ENNReal))
      rcases exists_add_payload_of_edist_lt haδ with ⟨y, rfl, hyδ⟩
      have hpδ : edist (x, y) (x₀, y₀) < δ := by
        rw [Prod.edist_eq]
        exact (max_lt_iff.mpr ⟨hxδ, hyδ⟩)
      simpa using hδ hpδ
  | cancel eta₀ =>
      have hprim :
          Filter.Tendsto (fun p : Tuple X × FiniteSubsets ℕ => cancel p.1 p.2)
            (nhds (x₀, eta₀)) (nhds (cancel x₀ eta₀)) :=
        Analytic.continuousAt_cancel_emetricTopology (X := X) (p₀ := (x₀, eta₀))
      rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
      rw [EMetric.tendsto_nhds_nhds] at hprim
      intro ε hε
      rcases hprim ε hε with ⟨δ, hδpos, hδ⟩
      let ρ : ENNReal := min δ 1
      refine ⟨ρ, lt_min hδpos zero_lt_one, ?_⟩
      intro p hp
      rcases p with ⟨x, a⟩
      rw [Prod.edist_eq] at hp
      have hxρ : edist x x₀ < ρ := (max_lt_iff.mp hp).1
      have haρ : edist a (MarketAction.cancel (X := X) eta₀) < ρ :=
        (max_lt_iff.mp hp).2
      have hxδ : edist x x₀ < δ :=
        lt_of_lt_of_le hxρ (min_le_left δ (1 : ENNReal))
      have haδ : edist a (MarketAction.cancel (X := X) eta₀) < δ :=
        lt_of_lt_of_le haρ (min_le_left δ (1 : ENNReal))
      rcases exists_cancel_payload_of_edist_lt haδ with ⟨eta, rfl, hetaδ⟩
      have hpδ : edist (x, eta) (x₀, eta₀) < δ := by
        rw [Prod.edist_eq]
        exact (max_lt_iff.mpr ⟨hxδ, hetaδ⟩)
      simpa using hδ hpδ
  | modify xi₀ =>
      have hprim :
          Filter.Tendsto
            (fun p : Tuple X × DistinctFiniteSubsets X => Primitive.modify p.1 p.2)
            (nhds (x₀, xi₀)) (nhds (Primitive.modify x₀ xi₀)) :=
        Analytic.continuousAt_modify_emetricTopology (X := X) (p₀ := (x₀, xi₀))
      rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
      rw [EMetric.tendsto_nhds_nhds] at hprim
      intro ε hε
      rcases hprim ε hε with ⟨δ, hδpos, hδ⟩
      let ρ : ENNReal := min δ 1
      refine ⟨ρ, lt_min hδpos zero_lt_one, ?_⟩
      intro p hp
      rcases p with ⟨x, a⟩
      rw [Prod.edist_eq] at hp
      have hxρ : edist x x₀ < ρ := (max_lt_iff.mp hp).1
      have haρ : edist a (MarketAction.modify xi₀) < ρ := (max_lt_iff.mp hp).2
      have hxδ : edist x x₀ < δ :=
        lt_of_lt_of_le hxρ (min_le_left δ (1 : ENNReal))
      have haδ : edist a (MarketAction.modify xi₀) < δ :=
        lt_of_lt_of_le haρ (min_le_left δ (1 : ENNReal))
      rcases exists_modify_payload_of_edist_lt haδ with ⟨xi, rfl, hxiδ⟩
      have hpδ : edist (x, xi) (x₀, xi₀) < δ := by
        rw [Prod.edist_eq]
        exact (max_lt_iff.mpr ⟨hxδ, hxiδ⟩)
      simpa using hδ hpδ

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`prop:application-continuous`.

Informal statement: the action application map
`\mathscr{T}(X) × \mathscr{A}(X) → \mathscr{T}(X)` is continuous.
-/
theorem continuous_applyAction_emetricTopology {X : Type u} [EMetricSpace X] :
    @Continuous (Tuple X × MarketAction X) (Tuple X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p : Tuple X × MarketAction X => applyAction p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (MarketAction X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Tuple X × MarketAction X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  rw [continuous_iff_continuousAt]
  exact continuousAt_applyAction_emetricTopology

/-! ## Composite Actions -/

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`, section
"Composite Actions".

Original label: Definition "Composite Actions", `\mathscr{C}(X)`.

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
`cor:action-metrization` for completeness of `\mathscr{A}(X)` with
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

Original label: extended application map in Definition "Composite Actions".

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

Lean strategy / thesis relation note: this is the formal version of the thesis recursion
`F_0(x)=x` and `F_{n+1}(x,a_0,\dots,a_n)=F_n(x,a_1,\dots,a_n)` after first
applying `a_0`. Lean uses zero-based `Fin` indices and `List.ofFn`; the proof
is induction on the composite length, using the already verified continuity of
the one-step application map.
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
      have hfirstAction :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            p.2 0) := by
        exact (continuous_apply 0).comp continuous_snd
      have hfirstPair :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            (p.1, p.2 0)) :=
        continuous_fst.prodMk hfirstAction
      have hfirstApplied :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            applyAction p.1 (p.2 0)) := by
        exact (continuous_applyAction_emetricTopology (X := X)).comp hfirstPair
      have htail :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            fun i : Fin n => p.2 (Fin.succ i)) := by
        apply continuous_pi
        intro i
        exact (continuous_apply (Fin.succ i)).comp continuous_snd
      have hpair :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            (applyAction p.1 (p.2 0),
              fun i : Fin n => p.2 (Fin.succ i))) :=
        hfirstApplied.prodMk htail
      have hprev :
          Continuous (fun p : Tuple X × (Fin (n + 1) → MarketAction X) =>
            (List.ofFn (fun i : Fin n => p.2 (Fin.succ i))).foldl
              applyAction (applyAction p.1 (p.2 0))) := by
        exact ih.comp hpair
      simpa [List.ofFn_succ] using hprev

/--
Thesis source:
`1 - theoretical foundations/3_market_actions.tex`,
`thm:composite-application-continuous`.

Informal statement: the extended application map
`\mathscr{T}(X) × \mathscr{C}(X) → \mathscr{T}(X)` is continuous.

Lean strategy / thesis relation note: this follows the thesis proof. The fixed-length maps
`F_n` are continuous by induction. Around a composite action of length `n`,
the tuple Hausdorff distance `< 1` forces nearby composite actions to have the
same length, and the standard machinery identifies that layer with the
finite product `\mathscr{A}(X)^n`.
-/
theorem continuous_applyCompositeAction_emetricTopology {X : Type u}
    [EMetricSpace X] :
    @Continuous (Tuple X × CompositeAction X) (Tuple X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p : Tuple X × CompositeAction X =>
        applyCompositeAction p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (MarketAction X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (CompositeAction X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Tuple X × CompositeAction X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  rw [continuous_iff_continuousAt]
  intro p₀
  rcases p₀ with ⟨x₀, c₀⟩
  rcases c₀ with ⟨n, c₀⟩
  have hfixed :
      @ContinuousAt (Tuple X × (Fin n → MarketAction X)) (Tuple X)
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
        (fun p : Tuple X × (Fin n → MarketAction X) =>
          (List.ofFn p.2).foldl applyAction p.1) (x₀, c₀) :=
    (continuous_fixedCompositeApply_emetricTopology (X := X) n).continuousAt
  rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
  rw [ContinuousAt, EMetric.tendsto_nhds_nhds] at hfixed
  intro ε hε
  rcases hfixed ε hε with ⟨δ, hδpos, hδ⟩
  let ρ : ENNReal := min δ 1
  refine ⟨ρ, lt_min hδpos zero_lt_one, ?_⟩
  intro p hp
  rcases p with ⟨x, c⟩
  rcases c with ⟨m, c⟩
  rw [Prod.edist_eq] at hp
  have hxρ : edist x x₀ < ρ := (max_lt_iff.mp hp).1
  have hcρ :
      edist (Sigma.mk m c : Tuple (MarketAction X))
        (Sigma.mk n c₀ : Tuple (MarketAction X)) < ρ :=
    (max_lt_iff.mp hp).2
  have hc_one :
      edist (Sigma.mk m c : Tuple (MarketAction X))
        (Sigma.mk n c₀ : Tuple (MarketAction X)) < (1 : ENNReal) :=
    lt_of_lt_of_le hcρ (min_le_right δ (1 : ENNReal))
  have hmn : m = n :=
    length_eq_of_edist_lt_one (X := MarketAction X) hc_one
  subst m
  have hxδ : edist x x₀ < δ :=
    lt_of_lt_of_le hxρ (min_le_left δ (1 : ENNReal))
  have hcδ_tuple :
      edist (Sigma.mk n c : Tuple (MarketAction X))
        (Sigma.mk n c₀ : Tuple (MarketAction X)) < δ :=
    lt_of_lt_of_le hcρ (min_le_left δ (1 : ENNReal))
  have hcpi : edist c c₀ < δ := by
    have heq := fixedLength_edist_eq_coordinateEDistSup_of_lt_one
      (X := MarketAction X) (x := c) (y := c₀) hc_one
    have hcoord : coordinateEDistSup c c₀ < δ := by
      simpa [heq] using hcδ_tuple
    simpa [coordinateEDistSup, edist_pi_def] using hcoord
  have hpairδ : edist (x, c) (x₀, c₀) < δ := by
    rw [Prod.edist_eq]
    exact max_lt_iff.mpr ⟨hxδ, hcpi⟩
  have hout := hδ hpairδ
  simpa [applyCompositeAction, compositeActionList] using hout

end Composite
end MarketActions
end Foundations
end Thesis
