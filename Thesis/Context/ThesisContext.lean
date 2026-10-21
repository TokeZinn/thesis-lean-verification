import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Setoid.Basic
import Thesis.Foundations.MarketActions.Primitive
import Thesis.Foundations.MarketClearing.Sorting
import Thesis.Foundations.Stochastic.KernelHilbert

-- Stable source-based block IDs must remain on one line for the inventory parser.
set_option linter.style.longLine false

/-!
# Thesis Context Blocks

This module formalizes the active-thesis principles, examples, and remarks
that are mathematical enough to be represented in Lean but are not the main
definition/theorem chain of their surrounding chapters.  The declarations are
kept in one audit-facing namespace so that these contextual blocks do not
distort the chapter modules.
-/

namespace Thesis
namespace Foundations
namespace ThesisContext

open Thesis.Foundations.MarketRepresentation
open Thesis.Foundations.MarketRepresentation.DisjointUnion
open Thesis.Foundations.MarketRepresentation.FiniteSets
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesSorting
open Thesis.Foundations.MarketActions.Primitive
open Thesis.Foundations.MarketClearing.Selection
open Thesis.Foundations.MarketClearing.Sorting
open Thesis.Foundations.Stochastic.PermutedTuples
open Thesis.Foundations.Stochastic.PointProcesses
open Thesis.Foundations.Stochastic.TupleMeasures
open Thesis.Foundations.Stochastic.KernelHilbert
open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

universe u v w

/-! ## Economic principles -/

/--
Thesis source: `1 - theoretical foundations/1_economics.tex`.

Original label: `prin:agent-actions`.

Informal statement: an action is admissible for an agent in a state exactly
when resources, authority over the affected orders, and venue rules permit it.

Lean strategy / thesis relation note: all three constraints are explicit
state-dependent predicates. No rationality or utility condition is imposed.
-/
def AdmissibleAction {Agent : Type u} {State : Type v} {Action : Type w}
    (resourcePermitted authorityPermitted venuePermitted : Agent → State → Action → Prop)
    (agent : Agent) (state : State) (action : Action) : Prop :=
  resourcePermitted agent state action ∧ authorityPermitted agent state action ∧
    venuePermitted agent state action

/--
Thesis source: `1 - theoretical foundations/1_economics.tex`.

Original label: `prin:finitism`.

Informal statement: a market observed on one finite interval carries a finite
set of participating agents and, for each participant, a finite set of
actions performed during that interval.

Lean strategy / thesis relation note: `Finset` records both finiteness claims
as data and leaves the agent and action types otherwise unrestricted.
-/
structure FiniteMarketInterval (Agent : Type u) (Action : Type v) where
  agents : Finset Agent
  actions : (agent : ↑agents) → Finset Action

/--
Thesis source: `1 - theoretical foundations/1_economics.tex`.

Original label: `prin:clearing`.

Informal statement: a market is cleared precisely when there is no exchange
that is both admissible and jointly acceptable to the involved agents.

Lean strategy / thesis relation note: the thesis biconditional is used as the
definition of `IsCleared`; the existential packages a remaining exchange and
the two required properties.
-/
def IsCleared {Exchange : Type u} (admissible jointlyWilling : Exchange → Prop) : Prop :=
  ¬ ∃ exchange, admissible exchange ∧ jointlyWilling exchange

/-! ## Disjoint unions and elementary market examples -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:52:rem:2`

Informal statement: two components of a dependent sum with different tags
are disjoint, even when their payload types or underlying sets overlap.

Lean strategy / thesis relation note: applying `Sigma.fst` to an alleged
equality of tagged elements would identify the tags, contradicting the
hypothesis that they differ.
-/
theorem sigma_mk_ne_of_tag_ne {A : Type u} {X : A → Type v}
    {a b : A} (hab : a ≠ b) (x : X a) (y : X b) :
    Sigma.mk a x ≠ Sigma.mk b y := by
  intro hxy
  exact hab (congrArg Sigma.fst hxy)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:adm-static`.

Informal statement: unrestricted tagged static orders are canonically
equivalent to price/quantity/direction triples.

Lean strategy / thesis relation note: the equivalence merely reassociates and
reorders the coordinates of the dependent sum; its inverse restores the
direction tag.
-/
def unrestrictedStaticOrdersEquiv :
    (Σ _ : OrderSide, ℝ × Quantity) ≃ ((ℝ × Quantity) × OrderSide) where
  toFun order := (order.2, order.1)
  invFun order := ⟨order.2, order.1⟩
  left_inv order := by cases order; rfl
  right_inv order := by cases order; rfl

/--
Informal statement: an agent-constrained static order stores its direction and
agent together with proofs that its price and quantity are admissible for
that pair.

Lean strategy / thesis relation note: this dependent-sum type is the literal
Lean counterpart of the restricted disjoint union used in the thesis.
-/
abbrev AgentStaticOrder (Agent : Type u)
    (P : OrderSide → Agent → Set ℝ)
    (Q : OrderSide → Agent → Set Quantity) : Type u :=
  Σ ka : OrderSide × Agent, (P ka.1 ka.2) × (Q ka.1 ka.2)

/--
Informal statement: forgetting admissibility proofs embeds a constrained
static order into the unrestricted price/quantity/direction/agent product.

Lean strategy / thesis relation note: the tag and both subtype values are
retained, so equality in the target determines equality in the source.
-/
def agentStaticOrderEmbedding {Agent : Type u}
    {P : OrderSide → Agent → Set ℝ}
    {Q : OrderSide → Agent → Set Quantity} :
    AgentStaticOrder Agent P Q → ((ℝ × Quantity) × (OrderSide × Agent)) :=
  fun order => ((order.2.1.1, order.2.2.1), order.1)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:agent-adm-static`.

Informal statement: the canonical map from agent-constrained static orders to
the unrestricted product is injective, though it need not be surjective.

Lean strategy / thesis relation note: injectivity follows because the map
forgets only proof fields; subtype proof irrelevance reconstructs the original
dependent-sum element.
-/
theorem agentStaticOrderEmbedding_injective {Agent : Type u}
    {P : OrderSide → Agent → Set ℝ}
    {Q : OrderSide → Agent → Set Quantity} :
    Function.Injective (agentStaticOrderEmbedding (P := P) (Q := Q)) := by
  intro x y hxy
  rcases x with ⟨tag, value⟩
  rcases y with ⟨tag', value'⟩
  have htag : tag = tag' := congrArg Prod.snd hxy
  subst tag'
  have hvalue : value = value' := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z => z.1.1) hxy
    · apply Subtype.ext
      exact congrArg (fun z => z.1.2) hxy
  exact congrArg (fun z => Sigma.mk tag z) hvalue

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:adm-dyn`.

Informal statement: unrestricted tagged dynamic orders are canonically
equivalent to price/quantity/time/direction tuples.

Lean strategy / thesis relation note: as in the static example, the map is a
coordinate reassociation; time is represented by the nonnegative-real type.
-/
def unrestrictedDynamicOrdersEquiv :
    (Σ _ : OrderSide × Quantity, ℝ × Quantity) ≃
      (((ℝ × Quantity) × Quantity) × OrderSide) where
  toFun order := ((order.2, order.1.2), order.1.1)
  invFun order := ⟨(order.2, order.1.2), order.1.1⟩
  left_inv order := by rcases order with ⟨⟨κ, t⟩, payload⟩; rfl
  right_inv order := by rcases order with ⟨⟨payload, t⟩, κ⟩; rfl

/--
Informal statement: a dynamically constrained order stores direction, agent,
and submission time together with an admissible price and quantity.

Lean strategy / thesis relation note: the admissible sets depend on all three
indices exactly as in the thesis disjoint union.
-/
abbrev AgentDynamicOrder (Agent : Type u)
    (P : OrderSide → Agent → Quantity → Set ℝ)
    (Q : OrderSide → Agent → Quantity → Set Quantity) : Type u :=
  Σ kat : (OrderSide × Agent) × Quantity,
    (P kat.1.1 kat.1.2 kat.2) × (Q kat.1.1 kat.1.2 kat.2)

/--
Informal statement: forgetting the admissibility proofs maps a dynamically
constrained order into the unrestricted coordinate product.

Lean strategy / thesis relation note: all mathematical coordinates are kept;
only membership proofs are erased.
-/
def agentDynamicOrderEmbedding {Agent : Type u}
    {P : OrderSide → Agent → Quantity → Set ℝ}
    {Q : OrderSide → Agent → Quantity → Set Quantity} :
    AgentDynamicOrder Agent P Q →
      (((ℝ × Quantity) × (OrderSide × Agent)) × Quantity) :=
  fun order => (((order.2.1.1, order.2.2.1), order.1.1), order.1.2)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:agent-adm-dyn`.

Informal statement: the canonical map from time-varying constrained orders to
the unrestricted dynamic-order product is injective.

Lean strategy / thesis relation note: equality of the retained coordinates
fixes the dependent tag and both subtype values; proof irrelevance then gives
equality of the original orders.
-/
theorem agentDynamicOrderEmbedding_injective {Agent : Type u}
    {P : OrderSide → Agent → Quantity → Set ℝ}
    {Q : OrderSide → Agent → Quantity → Set Quantity} :
    Function.Injective (agentDynamicOrderEmbedding (P := P) (Q := Q)) := by
  intro x y hxy
  rcases x with ⟨tag, value⟩
  rcases y with ⟨tag', value'⟩
  have hsideAgent : tag.1 = tag'.1 :=
    congrArg (fun z : (((ℝ × Quantity) × (OrderSide × Agent)) × Quantity) => z.1.2) hxy
  have htime : tag.2 = tag'.2 :=
    congrArg (fun z : (((ℝ × Quantity) × (OrderSide × Agent)) × Quantity) => z.2) hxy
  have htag : tag = tag' := Prod.ext hsideAgent htime
  subst tag'
  have hvalue : value = value' := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z => z.1.1.1) hxy
    · apply Subtype.ext
      exact congrArg (fun z => z.1.1.2) hxy
  exact congrArg (fun z => Sigma.mk tag z) hvalue

/-! ## Priority orders -/

/--
Informal statement: the thesis priority relation on static orders first
compares price (decreasing for buys, increasing for sells) and then compares
quantity decreasingly when prices tie.

Lean strategy / thesis relation note: the definition follows the displayed
buy and sell formulas verbatim, using the direction tag to choose the branch.
-/
def staticPriority (side : OrderSide) (x y : ℝ × Quantity) : Prop :=
  match side with
  | OrderSide.buy => x.1 > y.1 ∨ (x.1 = y.1 ∧ x.2 ≥ y.2)
  | OrderSide.sell => x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≥ y.2)

/--
Informal statement: tagged static orders are comparable only when their buy
or sell tags agree, in which case the side-specific priority is used.

Lean strategy / thesis relation note: the explicit tag equality is what turns
two total side orders into a partial order on their disjoint union.
-/
def taggedStaticPriority
    (x y : OrderSide × (ℝ × Quantity)) : Prop :=
  x.1 = y.1 ∧ staticPriority x.1 x.2 y.2

/--
Informal statement: any two price/quantity payloads on the same side are
comparable by the thesis static priority.

Lean strategy / thesis relation note: trichotomy of prices decides the first
coordinate; when prices agree, totality of nonnegative quantities decides the
tie-breaker.
-/
theorem staticPriority_total (side : OrderSide) (x y : ℝ × Quantity) :
    staticPriority side x y ∨ staticPriority side y x := by
  rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
  · cases side
    · exact Or.inr (Or.inl hlt)
    · exact Or.inl (Or.inl hlt)
  · rcases le_total x.2 y.2 with hxy | hyx
    · exact Or.inr (by cases side <;> exact Or.inr ⟨heq.symm, hxy⟩)
    · exact Or.inl (by cases side <;> exact Or.inr ⟨heq, hyx⟩)
  · cases side
    · exact Or.inl (Or.inl hgt)
    · exact Or.inr (Or.inl hgt)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:partial-order-static-market`.

Informal statement: two tagged static orders are comparable in at least one
direction exactly when their direction tags agree.

Lean strategy / thesis relation note: same-side comparability uses
`staticPriority_total`; the reverse implication reads the tag equality from
either possible comparison.
-/
theorem taggedStaticPriority_comparable_iff_same_side
    (x y : OrderSide × (ℝ × Quantity)) :
    (taggedStaticPriority x y ∨ taggedStaticPriority y x) ↔ x.1 = y.1 := by
  constructor
  · rintro (hxy | hyx)
    · exact hxy.1
    · exact hyx.1.symm
  · intro hside
    rcases staticPriority_total x.1 x.2 y.2 with hxy | hyx
    · exact Or.inl ⟨hside, hxy⟩
    · exact Or.inr ⟨hside.symm, by simpa [hside] using hyx⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Supplementary definition for the price-time-priority prose at source line 194.

Informal statement: price-time priority ranks a better price first and, when
prices tie, an earlier submission time first.

Lean strategy / thesis relation note: this definition records the market
convention mentioned in the prose independently of the quantity tie-breaker
used in the preceding static example.
-/
def priceTimePriority (side : OrderSide) (x y : ℝ × Quantity) : Prop :=
  match side with
  | OrderSide.buy => x.1 > y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
  | OrderSide.sell => x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:249:rem:12`

Informal statement: for a partial order, the associated strict relation is
the non-strict relation with its diagonal removed, and adjoining the diagonal
recovers the non-strict relation.

Lean strategy / thesis relation note: Lean's `<` and `≤` are predicates rather
than sets of pairs; antisymmetry supplies the two equivalences pointwise.
-/
theorem strict_and_nonstrict_order_differ_by_diagonal
    {X : Type u} [PartialOrder X] (x y : X) :
    (x < y ↔ x ≤ y ∧ x ≠ y) ∧ (x ≤ y ↔ x < y ∨ x = y) := by
  constructor
  · constructor
    · intro hxy
      exact ⟨hxy.le, ne_of_lt hxy⟩
    · rintro ⟨hxy, hne⟩
      exact lt_of_le_of_ne hxy hne
  · constructor
    · intro hxy
      exact lt_or_eq_of_le hxy
    · rintro (hxy | rfl)
      · exact hxy.le
      · exact le_rfl

/--
Informal statement: a static total priority first puts all buys before all
sells and otherwise uses the side-specific static priority.

Lean strategy / thesis relation note: this is the displayed lexicographic
construction with the arbitrary convention `buy < sell`.
-/
def staticTotalPriority
    (x y : OrderSide × (ℝ × Quantity)) : Prop :=
  (x.1 = OrderSide.buy ∧ y.1 = OrderSide.sell) ∨
    (x.1 = y.1 ∧ staticPriority x.1 x.2 y.2)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:total-order-static-market`.

Informal statement: the lexicographic static priority compares every pair of
tagged orders.

Lean strategy / thesis relation note: different sides are decided by the
chosen buy-before-sell order; equal sides reduce to
`staticPriority_total`.
-/
theorem staticTotalPriority_total
    (x y : OrderSide × (ℝ × Quantity)) :
    staticTotalPriority x y ∨ staticTotalPriority y x := by
  rcases x with ⟨κ, x⟩
  rcases y with ⟨ρ, y⟩
  cases κ <;> cases ρ
  · rcases staticPriority_total OrderSide.buy x y with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
  · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases staticPriority_total OrderSide.sell x y with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)

/--
Informal statement: dynamic price-time-quantity priority compares price first,
then submission time, and then quantity, reversing only the price direction
between buys and sells.

Lean strategy / thesis relation note: the two branches transcribe the two
displayed formulas from the thesis example.
-/
def dynamicPriority (side : OrderSide)
    (x y : (ℝ × Quantity) × Quantity) : Prop :=
  match side with
  | OrderSide.buy =>
      x.1.1 > y.1.1 ∨
        (x.1.1 = y.1.1 ∧ x.2 < y.2) ∨
        (x.1.1 = y.1.1 ∧ x.2 = y.2 ∧ x.1.2 ≥ y.1.2)
  | OrderSide.sell =>
      x.1.1 < y.1.1 ∨
        (x.1.1 = y.1.1 ∧ x.2 < y.2) ∨
        (x.1.1 = y.1.1 ∧ x.2 = y.2 ∧ x.1.2 ≥ y.1.2)

/--
Informal statement: any two dynamic payloads on a fixed side are comparable
by price, time, and quantity priority.

Lean strategy / thesis relation note: nested trichotomy follows exactly the
three successive tie-breakers in `dynamicPriority`.
-/
theorem dynamicPriority_total (side : OrderSide)
    (x y : (ℝ × Quantity) × Quantity) :
    dynamicPriority side x y ∨ dynamicPriority side y x := by
  rcases lt_trichotomy x.1.1 y.1.1 with hp | hp | hp
  · cases side
    · exact Or.inr (Or.inl hp)
    · exact Or.inl (Or.inl hp)
  · rcases lt_trichotomy x.2 y.2 with ht | ht | ht
    · exact Or.inl (by cases side <;> exact Or.inr (Or.inl ⟨hp, ht⟩))
    · rcases le_total x.1.2 y.1.2 with hq | hq
      · exact Or.inr (by
          cases side <;> exact Or.inr (Or.inr ⟨hp.symm, ht.symm, hq⟩))
      · exact Or.inl (by
          cases side <;> exact Or.inr (Or.inr ⟨hp, ht, hq⟩))
    · exact Or.inr (by
        cases side <;> exact Or.inr (Or.inl ⟨hp.symm, ht⟩))
  · cases side
    · exact Or.inl (Or.inl hp)
    · exact Or.inr (Or.inl hp)

/--
Informal statement: dynamic total priority orders sides lexicographically and
uses dynamic price-time-quantity priority within each side.

Lean strategy / thesis relation note: it is the dynamic analogue of
`staticTotalPriority`.
-/
def dynamicTotalPriority
    (x y : OrderSide × ((ℝ × Quantity) × Quantity)) : Prop :=
  (x.1 = OrderSide.buy ∧ y.1 = OrderSide.sell) ∨
    (x.1 = y.1 ∧ dynamicPriority x.1 x.2 y.2)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:total-order-dynamic-market`.

Informal statement: the lexicographic dynamic priority compares every pair of
tagged dynamic orders.

Lean strategy / thesis relation note: side comparison handles mixed tags,
while `dynamicPriority_total` handles matching tags.
-/
theorem dynamicTotalPriority_total
    (x y : OrderSide × ((ℝ × Quantity) × Quantity)) :
    dynamicTotalPriority x y ∨ dynamicTotalPriority y x := by
  rcases x with ⟨κ, x⟩
  rcases y with ⟨ρ, y⟩
  cases κ <;> cases ρ
  · rcases dynamicPriority_total OrderSide.buy x y with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
  · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases dynamicPriority_total OrderSide.sell x y with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)

/--
Informal statement: an agent-labelled order consists of its market-visible
price/quantity/direction payload and the submitting agent.

Lean strategy / thesis relation note: putting the visible payload first makes
the market-view projection the ordinary first projection.
-/
abbrev AgentLabelledOrder (Agent : Type u) : Type u :=
  (OrderSide × (ℝ × Quantity)) × Agent

/--
Informal statement: the market view forgets which agent submitted an order
while retaining price, quantity, and direction.

Lean strategy / thesis relation note: this is the thesis quotient map before
passing to its kernel equivalence classes.
-/
def marketView {Agent : Type u} :
    AgentLabelledOrder Agent → OrderSide × (ℝ × Quantity) :=
  Prod.fst

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:completing-order-agent-based-static-market`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:350:rem:18`.

Informal statement: quotienting agent-labelled orders by equality of their
market view is canonically equivalent to the range of visible orders.

Lean strategy / thesis relation note: mathlib's kernel-quotient equivalence
implements the thesis map from equivalence classes to price/quantity/direction
orders and proves well-definedness and bijectivity at once.
-/
noncomputable def agentOrderQuotientEquivMarketViewRange (Agent : Type u) :
    Quotient (Setoid.ker (marketView (Agent := Agent))) ≃
      Set.range (marketView (Agent := Agent)) :=
  Setoid.quotientKerEquivRange marketView

/-! ## Metric, finite-set, and tuple conventions -/

/--
Informal statement: truncate an extended distance at one, producing a finite
extended-real value even when the original distance is infinite.

Lean strategy / thesis relation note: this is the pointwise formula
`min (d x y) 1` used in the thesis remark.
-/
def truncatedEDistance {X : Type u} (d : X → X → ENNReal) (x y : X) : ENNReal :=
  min (d x y) 1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:368:rem:20`

Informal statement: truncation at one is bounded and it agrees with the
original extended distance whenever that distance is below one.

Lean strategy / thesis relation note: the local agreement on every ball of
radius less than one is the precise small-scale fact behind the thesis claim
that truncation does not change the induced topology.
-/
theorem truncatedEDistance_bounded_and_locally_equal {X : Type u}
    (d : X → X → ENNReal) (x y : X) :
    truncatedEDistance d x y ≤ 1 ∧
      (d x y < 1 → truncatedEDistance d x y = d x y) := by
  constructor
  · exact min_le_right _ _
  · intro hxy
    exact min_eq_left hxy.le

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:498:rem:25`

Informal statement: the measurable direct sum of an indexed family of spaces
has the dependent-sum carrier `Σ a, X a`.

Lean strategy / thesis relation note: Lean's measurable-space instance for a
dependent sum is the standard direct-sum sigma algebra; this abbreviation
records the terminology used by the remark without duplicating the instance.
-/
abbrev MeasurableDirectSum (A : Type u) (X : A → Type v)
    [∀ a, MeasurableSpace (X a)] : Type (max u v) :=
  Σ a, X a

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `rem:unordered-configuration-space`.

Informal statement: the unordered finite-configuration space over `X` is the
type of finite subsets of `X`.

Lean strategy / thesis relation note: finite subsets carry no enumeration or
ordering, matching the configuration-space terminology exactly.
-/
abbrev UnorderedFiniteConfiguration (X : Type u) : Type u :=
  FiniteSubsets X

/--
Informal statement: the empty finite subset is a point of every finite-subset
space.

Lean strategy / thesis relation note: its finiteness proof is the standard
finiteness theorem for the empty set.
-/
def emptyFiniteSubset (X : Type u) : FiniteSubsets X :=
  ⟨∅, Set.finite_empty⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `rem:hausdorff-convention`.

Informal statement: the extended Hausdorff distance from the empty set is
zero for the empty set and infinity for every nonempty finite set.

Lean strategy / thesis relation note: the proof invokes mathlib's extended
Hausdorff empty-set theorem after splitting on whether the second finite set
is empty.
-/
theorem hausdorffEDistance_empty_convention {X : Type u}
    [PseudoEMetricSpace X] (s : FiniteSubsets X) :
    hausdorffEDistance (emptyFiniteSubset X) s =
      if (s : Set X) = ∅ then 0 else ∞ := by
  by_cases hs : (s : Set X) = ∅
  · have hse : s = emptyFiniteSubset X := Subtype.ext hs
    subst s
    simp [hausdorffEDistance, emptyFiniteSubset]
  · have hsne : (s : Set X).Nonempty := Set.nonempty_iff_ne_empty.mpr hs
    rw [if_neg hs, hausdorffEDistance, Metric.hausdorffEDist_comm]
    exact Metric.hausdorffEDist_empty hsne

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `rem:hausdorff-infinite-values`.

Informal statement: in a finite-valued metric space, the Hausdorff extended
distance between two nonempty finite subsets is not infinite.

Lean strategy / thesis relation note: finite subsets of a metric space are
bounded, so the standard bounded-nonempty Hausdorff theorem excludes `∞`;
the preceding convention accounts for the remaining empty-set cases.
-/
theorem hausdorffEDistance_ne_top_of_nonempty_finite {X : Type u}
    [PseudoMetricSpace X] (s t : FiniteSubsets X)
    (hs : (s : Set X).Nonempty) (ht : (t : Set X).Nonempty) :
    hausdorffEDistance s t ≠ ∞ := by
  exact Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    hs ht s.2.isBounded t.2.isBounded

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:903:rem:45`

Informal statement: the graph/range of the empty tuple is the empty set.

Lean strategy / thesis relation note: Lean represents the empty tuple as a
map from `Fin 0`; eliminating a hypothetical index proves its range empty,
which is the typed analogue of the ZFC graph observation in the thesis.
-/
theorem range_emptyTuple {X : Type u} :
    Set.range (Tuple.empty X).2 = ∅ := by
  ext x
  simp [Tuple.empty]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:985:rem:50`

Informal statement: the length stored with a finite permutation is the
cardinality of its finite domain.

Lean strategy / thesis relation note: a finite permutation is indexed by
`Fin n`, whose cardinality is definitionally the thesis domain size `n`.
-/
theorem finitePermutation_domain_card (permutation : FinitePermutations) :
    Fintype.card (Fin permutation.1) = permutation.1 :=
  Fintype.card_fin permutation.1

/-- Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:985:rem:50`
The source's inclusion of permutations into natural-valued tuples. Adding one
translates Lean's zero-based indices to the thesis's positive naturals. -/
def finitePermutationTuple (permutation : FinitePermutations) : Tuple ℕ :=
  ⟨permutation.1, fun i => (permutation.2 i).val + 1⟩

theorem finitePermutationTuple_injective : Function.Injective finitePermutationTuple := by
  rintro ⟨n, π⟩ ⟨m, σ⟩ h
  have hlen : n = m := congrArg Tuple.length h
  subst m
  have hf : (fun i : Fin n => (π i).val + 1) = (fun i : Fin n => (σ i).val + 1) :=
    eq_of_heq (Sigma.mk.inj h).2
  have hp : π = σ := by
    ext i
    exact Nat.add_right_cancel (congrFun hf i)
  cases hp
  rfl

@[simp] theorem finitePermutationTuple_length (permutation : FinitePermutations) :
    (finitePermutationTuple permutation).length = permutation.1 := rfl

/-! ## Sorting existence, uniqueness, and notation -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:1048:cor:54`

Informal statement: every partially ordered type admits at least one sorting
rule on all finite tuples.

Lean strategy / thesis relation note: Alias for `cor:54` (the mapped
construction is TuplesSorting.choiceSortingRule). The construction itself lives
in `TuplesSorting`: `chosenSortingPermutation` selects one sorting permutation
for each tuple, `choiceSortingRule` packages those selections as a sorting
rule, and `sortingRule_exists` records the resulting existence statement; those
declarations carry the thesis label `thm:sorting-exists`. This one-line bridge
only re-exposes `sortingRule_exists` under the stable block ID, which is
necessary because the thesis labels this corollary with a theorem prefix.
-/
theorem context_sortingRule_exists (X : Type u) [PartialOrder X] :
    Nonempty (SortingRule X) :=
  sortingRule_exists X

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:1899:rem:95`

Informal statement: over a total order, any two sorting permutations produce
the same sorted tuple even if the permutations themselves differ on repeated
entries.

Lean strategy / thesis relation note: the chapter's uniqueness theorem for
sorted permutations compares the resulting tuples, deliberately not the
witnessing permutations.
-/
theorem sorting_output_unique_despite_permutation_choice
    {X : Type u} [LinearOrder X] (x : Tuple X)
    (pi rho : SortingPermutations x) :
    permute x pi.1 = permute x rho.1 :=
  sortedPermutations_eq_of_linearOrder x pi rho

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:1386:rem:65`

Informal statement: relational composition connects `x` to `z` when some
intermediate `y` is related to `x` by the first relation and to `z` by the
second.

Lean strategy / thesis relation note: relations are predicates in Lean, so
the thesis set-builder definition becomes this existential predicate.
-/
def relationComposition {X : Type u} (R S : X → X → Prop) (x z : X) : Prop :=
  ∃ y, R x y ∧ S y z

/--
Informal statement: concatenate a finite list of tuples from left to right,
using the empty tuple as the zero-length base case.

Lean strategy / thesis relation note: recursion fixes the parenthesization of
the thesis shorthand and preserves the displayed order of the tuple factors.
-/
def concatList {X : Type u} : List (Tuple X) → Tuple X
  | [] => Tuple.empty X
  | [x] => x
  | x :: y :: xs => concat x (concatList (y :: xs))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:1550:rem:77`

Informal statement: the three-term concatenation shorthand expands in the
listed order to `x ⊕ (y ⊕ z)`.

Lean strategy / thesis relation note: this is a definitional unfolding of
`concatList`; no commutativity is introduced or assumed.
-/
theorem concatList_three {X : Type u} (x y z : Tuple X) :
    concatList [x, y, z] = concat x (concat y z) :=
  rfl

/-! ## Concrete sorting examples -/

/--
Informal statement: lexicographic order on pairs first compares the first
coordinate strictly and uses the non-strict second-coordinate order on ties.

Lean strategy / thesis relation note: this is exactly the order relation used
in the discontinuity example.
-/
def lexicographicPairLE (x y : ℝ × ℝ) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

/--
Informal statement: the discontinuity witness is the two-entry tuple
`((0,1),(1/(n+1),0))`; the shift by one makes every denominator positive.

Lean strategy / thesis relation note: using `n+1` makes explicit the positive
natural-number indexing intended by the thesis formula `1/n`.
-/
noncomputable def lexSortingWitness (n : ℕ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((0, 1), (1 / ((n : ℝ) + 1), 0))

/--
Informal statement: the pointwise limit of the discontinuity witness is the
pair `((0,1),(0,0))`.

Lean strategy / thesis relation note: this names the exact limiting tuple
displayed in the thesis.
-/
def lexSortingLimit : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((0, 1), (0, 0))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `exmp:sort-discont`.

Informal statement: every shifted reciprocal witness is lexicographically
sorted, the sequence converges to `((0,1),(0,0))`, and that limit is not
sorted.

Lean strategy / thesis relation note: positivity proves sortedness, the
standard reciprocal limit proves convergence, and the tie at first coordinate
with `1 ≤ 0` false proves failure of sortedness at the limit.  This is the
closed-graph obstruction used by the thesis to show sorting discontinuous.
-/
theorem lexSorting_discontinuity_witness :
    (∀ n, lexicographicPairLE (lexSortingWitness n).1 (lexSortingWitness n).2) ∧
      Tendsto lexSortingWitness atTop (nhds lexSortingLimit) ∧
      ¬ lexicographicPairLE lexSortingLimit.1 lexSortingLimit.2 := by
  constructor
  · intro n
    left
    change (0 : ℝ) < 1 / ((n : ℝ) + 1)
    positivity
  · constructor
    · have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hfirst : Tendsto (fun _ : ℕ => ((0, 1) : ℝ × ℝ))
          atTop (nhds (0, 1)) :=
        tendsto_const_nhds
      have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds
      change Tendsto
        (fun n : ℕ => (((0, 1) : ℝ × ℝ),
          ((1 / ((n : ℝ) + 1), 0) : ℝ × ℝ)))
        atTop (nhds (((0, 1) : ℝ × ℝ), ((0, 0) : ℝ × ℝ)))
      simpa only [one_div] using
        hfirst.prodMk_nhds (hdiv.prodMk_nhds hzero)
    · norm_num [lexicographicPairLE, lexSortingLimit]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `rem:sorting-permutations-not-unique`.

Informal statement: a constant real tuple of length two is fixed by both the
identity permutation and the transposition, although those permutations are
distinct.

Lean strategy / thesis relation note: the swap moves the two indices, while
constant-function extensionality shows that both reindexings yield the same
tuple values.
-/
theorem equalRealPair_has_distinct_sortingPermutations (x : ℝ) :
    ∃ pi rho : Equiv.Perm (Fin 2), pi ≠ rho ∧
      (fun _ : Fin 2 => x) ∘ pi = (fun _ : Fin 2 => x) ∘ rho := by
  refine ⟨Equiv.refl (Fin 2), Equiv.swap 0 1, ?_, ?_⟩
  · intro h
    have hzero := congrArg (fun e : Equiv.Perm (Fin 2) => e 0) h
    simp at hzero
  · funext i
    rfl

/-! ## Market-action conventions -/

/--
Thesis source: `1 - theoretical foundations/3_market_actions.tex`.

Original label: `rem:concat-empty-tuples`.

Informal statement: concatenating two empty tuples produces the empty tuple.

Lean strategy / thesis relation note: both input domains are `Fin 0`; after
unfolding concatenation, function extensionality eliminates the impossible
output index.
-/
theorem concat_empty_empty (X : Type u) :
    concat (Tuple.empty X) (Tuple.empty X) = Tuple.empty X := by
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  · funext i
    exact Fin.elim0 i

/--
Thesis source: `1 - theoretical foundations/3_market_actions.tex`.

Original label: `defn:sorted-tuple-add`.

Informal statement: fix one sorting rule for a partially ordered type.

Lean strategy / thesis relation note: `choiceSortingRule` chooses one sorting
permutation for each finite tuple, providing the globally well-defined rule
that the market convention requires.
-/
noncomputable def fixedSortingRule (X : Type u) [PartialOrder X] : SortingRule X :=
  choiceSortingRule X

/--
Thesis source: `1 - theoretical foundations/3_market_actions.tex`.

Original label: `rem:reindex-bracket-notation`.

Informal statement: whenever the selected-index set has strictly fewer
members than the original tuple domain, reindexing strictly shortens the
tuple and hence cannot be a permutation of that domain.

Lean strategy / thesis relation note: the exact length formula for `reindex`
turns the cardinality hypothesis directly into the claimed strict inequality.
-/
theorem reindex_shortens_when_indices_discarded {X : Type u}
    (x : Tuple X) (indices : FiniteSubsets ℕ)
    (hcard :
      (FiniteSubsets.toFinset
        (finiteSubsetInter indices (tupleDomain x))).card < x.length) :
    (reindex x indices).length < x.length := by
  simpa using hcard

/--
Informal statement: the empty modification contains no index/value pairs and
therefore satisfies the distinct-index condition.

Lean strategy / thesis relation note: the condition is immediate because
membership in the underlying empty finite subset is impossible.
-/
def emptyModification (X : Type u) : DistinctFiniteSubsets X :=
  ⟨emptyFiniteSubset (IndexAugmented X), by
    intro n x y hx
    simp [emptyFiniteSubset] at hx⟩

/--
Informal statement: applying the empty modification leaves every tuple
unchanged.

Lean strategy / thesis relation note: every coordinate falls into the
no-replacement branch of `modificationValue`.
-/
theorem modify_emptyModification {X : Type u} (x : Tuple X) :
    modify x (emptyModification X) = x := by
  cases x with
  | mk n f =>
      apply congrArg (fun g => (Sigma.mk n g : Tuple X))
      funext i
      apply modificationValue_eq_default_of_not_exists
      simp [emptyModification, emptyFiniteSubset]

/--
Thesis source: `1 - theoretical foundations/3_market_actions.tex`.

Original label: `rem:void-modification`.

Informal statement: a void modification leaves the ordinary tuple fixed,
while sorted modification returns the chosen sorting of that same tuple.

Lean strategy / thesis relation note: the first equality is
`modify_emptyModification`; unfolding `sortedModify` and rewriting by it
gives the second equality.
-/
theorem voidModification_behavior {X : Type u} [Preorder X]
    (sortingRule : SortingRule X) (x : Tuple X) :
    modify x (emptyModification X) = x ∧
      (sortedModify sortingRule x (emptyModification X)).1 = sortingRule.sort x := by
  constructor
  · exact modify_emptyModification x
  · change sortingRule.sort (modify x (emptyModification X)) = sortingRule.sort x
    rw [modify_emptyModification]

/-! ## Market-clearing notation -/

/--
Thesis source: `1 - theoretical foundations/4_market_clearing.tex`.

Original label: `rem:tuple-projection-operator-notation`.

Informal statement: tuple decomposition is exactly the map sending each
coordinate tag to the corresponding tuple projection.

Lean strategy / thesis relation note: the operator-style and function-style
notations are definitionally equal in the dependent-product representation.
-/
theorem tupleDecomposition_eq_projectionMap
    {A : Type v} {X : A → Type u}
    (x : Tuple ((a : A) → X a)) :
    tupleDecomposition x = fun a => tupleProjection a x :=
  rfl

/--
Thesis source: `1 - theoretical foundations/4_market_clearing.tex`.

Original label: `rem:separation-element-projection`.

Informal statement: separating the entries tagged by `a` and projecting away
their tags yields a tuple in the untagged component type `X a`.

Lean strategy / thesis relation note: `separationComponent` performs both the
index filtering and the proof-carrying dependent projection, so its result
type formally enforces the codomain claimed in the remark.
-/
noncomputable def untaggedSeparation {A : Type v} [DecidableEq A]
    {X : A → Type u} (a : A) (x : Tuple (DisjointUnion X)) : Tuple (X a) :=
  separationComponent a x

/-! ## Stochastic-market conventions -/

/--
Supporting lemma for empty atomic decompositions: a sum indexed by the empty
finite type is zero. The current stochastic-market chapter explicitly uses
this convention inside its atomic-representation lemma.
-/
theorem sum_fin_zero {M : Type u} [AddCommMonoid M] (f : Fin 0 → M) :
    ∑ i, f i = 0 := by
  simp

/--
Thesis source: `1 - theoretical foundations/5_stochastic_markets.tex`.

Original label: `rem:permuted-tuple-notation`.

Informal statement: every permuted-tuple quotient class has a tuple
representative whose quotient is the original class.

Lean strategy / thesis relation note: the existing quotient choice function
supplies the representative; its `Quot.out_eq` theorem certifies the chosen
notation without pretending the representative map is injective.
-/
theorem permutedTupleClass_has_representative {X : Type u}
    (q : PermutedTupleQuotientSpace X) :
    ∃ x : Tuple X, Quot.mk (permutativeSetoid X) x = q :=
  ⟨chooseRepresentative q, mk_chooseRepresentative q⟩

/--
Thesis source: `1 - theoretical foundations/5_stochastic_markets.tex`.

Original label: `rem:measurable-enumeration-adaptation`.

Informal statement: repeating the atoms of a finite atomic decomposition by
their multiplicities produces a tuple whose induced counting measure is the
original finite integer-valued measure.

Lean strategy / thesis relation note: this is the constructive tuple bridge
used when adapting a measurable atom enumeration; it invokes no new axiom and
is independent of the cited measurability theorem itself.
-/
theorem atomicEnumeration_corresponds_to_tuple {X : Type u}
    [MeasurableSpace X] {μ : FiniteIntegerMeasures X}
    (decomposition : AtomicDecomposition μ) :
    tupleInducedIntegerMeasure (tupleOfAtomicDecomposition decomposition) = μ :=
  tupleInducedIntegerMeasure_tupleOfAtomicDecomposition decomposition

/--
Informal statement: the fiber of a group action over `y` consists of the
group elements that move a fixed point `x` to `y`.

Lean strategy / thesis relation note: for the thesis application, the group
is the finite permutation group and these fibers are the cosets of the tuple
stabilizer.
-/
abbrev OrbitFiber (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x y : X) : Type u :=
  {g : G // g • x = y}

/--
Informal statement: left multiplication by `g` bijects the action fiber over
`y` with the action fiber over `g • y`.

Lean strategy / thesis relation note: multiplication by `g⁻¹` is the inverse;
the action laws prove both fiber-membership conditions and inverse laws.
-/
def orbitFiberLeftMulEquiv {G : Type u} {X : Type v}
    [Group G] [MulAction G X] (x y : X) (g : G) :
    OrbitFiber G X x y ≃ OrbitFiber G X x (g • y) where
  toFun h := ⟨g * h.1, by rw [mul_smul, h.2]⟩
  invFun h := ⟨g⁻¹ * h.1, by rw [mul_smul, h.2, inv_smul_smul]⟩
  left_inv h := by
    apply Subtype.ext
    simp
  right_inv h := by
    apply Subtype.ext
    simp

/--
Thesis source: `1 - theoretical foundations/5_stochastic_markets.tex`.

Informal statement: all fibers lying in one finite group orbit have equal
cardinality; in particular, every tuple in a permutation orbit is produced by
the same number of permutations.

Supporting group-action lemma: `orbitFiberLeftMulEquiv` gives the explicit
coset bijection. The current tuple multiplicity and uniform point-process
sampling results specialize this orbit-counting argument.
-/
theorem orbitFiber_card_eq {G : Type u} {X : Type v}
    [Group G] [Finite G] [MulAction G X] (x y : X) (g : G) :
    Nat.card (OrbitFiber G X x y) =
      Nat.card (OrbitFiber G X x (g • y)) :=
  Nat.card_congr (orbitFiberLeftMulEquiv x y g)

/--
Informal statement: the kernel equivalence relation of a map identifies
exactly the inputs having the same image.

Lean strategy / thesis relation note: mathlib's `Setoid.ker` is the typed
quotient relation meant by "kernel" outside the linear-algebra null-space
sense.
-/
def kernelEquivalence {X : Type u} {Y : Type v} (f : X → Y) : Setoid X :=
  Setoid.ker f

/--
Thesis source: `1 - theoretical foundations/5_stochastic_markets.tex`.

Original label: `rem:kernel-quotient-terminology`.

Informal statement: two elements are related by the kernel equivalence of
`f` if and only if `f` maps them to the same value.

Lean strategy / thesis relation note: unfolding `Setoid.ker` distinguishes
this fiber relation from the null space of a linear operator.
-/
theorem kernelEquivalence_apply {X : Type u} {Y : Type v}
    (f : X → Y) (x y : X) :
    kernelEquivalence f x y ↔ f x = f y :=
  Iff.rfl

/--
Thesis source: `1 - theoretical foundations/5_stochastic_markets.tex`.

Original block id: `source:1 - theoretical foundations/5_stochastic_markets.tex:1296:cor:45`

Informal statement: for a nonempty domain and weakly convex real-vector-space
operator, the map `T([(x,z)]) = Φ(x) - Φ(z)` is a linear isomorphism from the
Grothendieck vectorization onto the span of the operator image.

Lean strategy / thesis relation note: the witness is
`KernelHilbert.grothendieckVectorizationLinearEquivSpan`, and the displayed
formula for `T` on pair representatives is
`grothendieckVectorizationEquivSpan_pairRepresentative_formula`; the stable ID
is needed because the thesis corollary carries a theorem-prefixed label.
-/
theorem context_grothendieck_vectorization_linearEquiv_span
    {X : Type u} {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (phi : Operator X V) (hphi : WeaklyConvexOperator X V phi) :
    ∃ T : GrothendieckVectorization phi hphi ≃ₗ[ℝ] Submodule.span ℝ (Set.range phi),
      ∀ p : GrothendieckPair phi hphi,
        ((T (Quotient.mk (grothendieckSetoid phi hphi) p) :
            Submodule.span ℝ (Set.range phi)) : V) =
          weakConvexKernelImage phi hphi p.1 - weakConvexKernelImage phi hphi p.2 :=
  ⟨grothendieckVectorizationLinearEquivSpan phi hphi,
    fun p => grothendieckVectorizationEquivSpan_pairRepresentative_formula phi hphi p⟩

/--
Existence wrapper for the corollary at line 1296 of
`1 - theoretical foundations/5_stochastic_markets.tex` (not the mapped
statement): the linear isomorphism of
`context_grothendieck_vectorization_linearEquiv_span`, forgetting the formula
for `T`. Kept under its former name for interface stability.
-/
theorem context_grothendieck_vectorization_is_span
    {X : Type u} {V : Type v} [AddCommGroup V] [Module ℝ V] [Nonempty X]
    (phi : Operator X V) (hphi : WeaklyConvexOperator X V phi) :
    Nonempty (GrothendieckVectorization phi hphi ≃ₗ[ℝ]
      Submodule.span ℝ (Set.range phi)) :=
  (context_grothendieck_vectorization_linearEquiv_span phi hphi).elim fun T _ => ⟨T⟩

/-! ## Day-ahead modelling conventions -/

/--
Thesis source: `2 - day-ahead/2_clearing_operator_price_curves.tex`.

Original label: `rem:lp-point-evaluation`.

Informal statement: the thesis `ℒ²` convention is the type of actual
functions together with a square-integrability proof, before identifying
functions that agree almost everywhere.

Lean strategy / thesis relation note: the subtype retains pointwise function
values; mathlib's separate `Lp E 2 μ` type below is the almost-everywhere
quotient.  Thus the distinction in the thesis is visible in the Lean types.
-/
abbrev L2Representatives (Domain : Type u) (E : Type v)
    [MeasurableSpace Domain] [NormedAddCommGroup E]
    (measure : Measure Domain) : Type (max u v) :=
  {f : Domain → E // MemLp f 2 measure}

/--
Informal statement: the conventional Hilbert `L²` space is the
almost-everywhere quotient of square-integrable functions.

Lean strategy / thesis relation note: this abbreviation names the quotient
type used by mathlib and contrasts it with `L2Representatives`.
-/
abbrev L2EquivalenceClasses (Domain : Type u) (E : Type v)
    [MeasurableSpace Domain] [NormedAddCommGroup E]
    (measure : Measure Domain) : Type (max u v) :=
  Lp E 2 measure

end ThesisContext
end Foundations
end Thesis
