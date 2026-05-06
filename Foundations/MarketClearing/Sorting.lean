import Mathlib.Data.NNReal.Basic
import Foundations.MarketClearing.Selection

/-!
# Market Clearing: Sorting

Blueprint module for
`1 - theoretical foundations/4_market_clearing.tex`,
clearing procedure steps 1--3.

Formal content:

* buy/sell separation;
* price and quantity tuple projections;

Planned formal content:

* `eq:minimal-sort`;
* `lem:tuple-space-measurable-2`;
* `prop:minimal-sorting-measurable` for real-valued price sorting.
-/

open scoped NNReal

namespace Thesis
namespace Foundations
namespace MarketClearing
namespace Sorting

open Thesis.Foundations.MarketRepresentation
open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
open Thesis.Foundations.MarketRepresentation.TuplesSorting
open Thesis.Foundations.MarketRepresentation.TuplesMeasurableSorting
open Thesis.Foundations.MarketClearing.Selection

/-! ## Market Orders -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: market-order convention before Step 1.

Informal statement: market orders have one of two directions, buy or sell.
This is Lean's finite type for the thesis set
`\{\mathrm{buy},\mathrm{sell}\}`.
-/
inductive OrderSide where
  | buy
  | sell
  deriving DecidableEq, Fintype

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: product-coordinate convention in Step 2.

Informal statement: a limit order has two fields, price and quantity. This
is Lean's two-point index set corresponding to the thesis' `{1,2}`.
-/
inductive OrderField where
  | price
  | quantity
  deriving DecidableEq, Fintype

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: order quantity space `[0,\infty)`.

Informal statement: order quantities are nonnegative real numbers.

Lean strategy / thesis relation note: the thesis writes `[0,\infty)`. Lean uses mathlib's bundled
type `ℝ≥0`, which stores both a real value and the proof of nonnegativity.
-/
abbrev Quantity : Type := ℝ≥0

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: equation identifying `\mathbb{R} \times [0,\infty)` with a
two-coordinate function type.

Informal statement: the price coordinate has values in `\mathbb{R}`, while
the quantity coordinate has values in `[0,\infty)`.

Lean strategy / thesis relation note: this is the dependent-family version of the thesis product
representation. It lets `tupleProjection` apply directly as `P_price` and
`P_quantity`.
-/
def OrderFieldValue : OrderField → Type
  | OrderField.price => ℝ
  | OrderField.quantity => Quantity

/-- Auxiliary metric instance for the two order-field value spaces. -/
instance instOrderFieldValueEMetricSpace (c : OrderField) :
    EMetricSpace (OrderFieldValue c) :=
  match c with
  | OrderField.price => inferInstanceAs (EMetricSpace ℝ)
  | OrderField.quantity => inferInstanceAs (EMetricSpace Quantity)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: order payload `\mathbb{R} \times [0,\infty)`.

Informal statement: a limit order is a price/quantity pair.

Lean strategy / thesis relation note: instead of a binary product, Lean stores the pair as a
dependent function over `OrderField`. This is definitionally the form needed
for the tuple projections used in Step 2.
-/
abbrev LimitOrder : Type := (c : OrderField) → OrderFieldValue c

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: payload family for the disjoint union of buy/sell orders.

Informal statement: both buy and sell sides carry the same limit-order
payload.
-/
abbrev MarketOrderPayload (_ : OrderSide) : Type := LimitOrder

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: `O = \bigsqcup_{\kappa \in \{\mathrm{buy},\mathrm{sell}\}}
\mathbb{R} \times [0,\infty)`.

Informal statement: the market-order space is the disjoint union of the buy
and sell order payload spaces.

Lean strategy / thesis relation note: this uses the Chapter 2 dependent-sum representation
`Σ κ, MarketOrderPayload κ`.
-/
abbrev MarketOrder : Type := DisjointUnion MarketOrderPayload

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: market tuple space `\mathscr{T}(O)`.

Informal statement: a market is a finite tuple of tagged buy/sell orders.
-/
abbrev MarketTuple : Type := Tuple MarketOrder

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: order notation `o = ((p,q),\kappa)`, payload part.

Informal statement: build the payload of an order from its price and
nonnegative quantity.
-/
def mkLimitOrder (p : ℝ) (q : Quantity) : LimitOrder
  | OrderField.price => p
  | OrderField.quantity => q

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: price coordinate of `o = ((p,q),\kappa)`.
-/
def orderPrice (o : LimitOrder) : ℝ :=
  o OrderField.price

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, clearing procedure,
before Step 1.

Original label: quantity coordinate of `o = ((p,q),\kappa)`.
-/
def orderQuantity (o : LimitOrder) : Quantity :=
  o OrderField.quantity

/-- The price coordinate of a constructed limit order is the supplied price. -/
@[simp]
theorem orderPrice_mkLimitOrder (p : ℝ) (q : Quantity) :
    orderPrice (mkLimitOrder p q) = p :=
  rfl

/-- The quantity coordinate of a constructed limit order is the supplied quantity. -/
@[simp]
theorem orderQuantity_mkLimitOrder (p : ℝ) (q : Quantity) :
    orderQuantity (mkLimitOrder p q) = q :=
  rfl

/-! ## Step 1: Separation of Buy and Sell Orders -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 1.

Original label: Step 1, `\bm{b} = \bm{\Pi}_{\mathrm{buy}}\bm{m}`.

Informal statement: extract the buy-order subtuple from a market tuple.
-/
noncomputable def buyOrders (m : MarketTuple) : Tuple LimitOrder :=
  separationComponent (X := MarketOrderPayload) OrderSide.buy m

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 1.

Original label: Step 1, `\bm{s} = \bm{\Pi}_{\mathrm{sell}}\bm{m}`.

Informal statement: extract the sell-order subtuple from a market tuple.
-/
noncomputable def sellOrders (m : MarketTuple) : Tuple LimitOrder :=
  separationComponent (X := MarketOrderPayload) OrderSide.sell m

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 1.

Original label: Step 1, full map `\bm{\Pi}\bm{m} = (\bm{b},\bm{s})`.

Informal statement: separate a market tuple into all side-indexed order
subtuples.
-/
noncomputable def separatedMarket (m : MarketTuple) :
    OrderSide → Tuple LimitOrder :=
  separationOperator (X := MarketOrderPayload) m

/-- Step 1: the buy component of the full separation map is `buyOrders`. -/
theorem separatedMarket_buy (m : MarketTuple) :
    separatedMarket m OrderSide.buy = buyOrders m :=
  rfl

/-- Step 1: the sell component of the full separation map is `sellOrders`. -/
theorem separatedMarket_sell (m : MarketTuple) :
    separatedMarket m OrderSide.sell = sellOrders m :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 1.

Original label: Step 1 continuity, from `prop:separation-continuous`.

Informal statement: extracting buy orders is continuous.
-/
theorem continuous_buyOrders :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Continuous MarketTuple (Tuple LimitOrder)
      (tupleHausdorffMetricTopology (X := MarketOrder))
      (tupleHausdorffMetricTopology (X := LimitOrder))
      buyOrders := by
  simpa [buyOrders, MarketOrder, MarketOrderPayload, MarketTuple] using
    (continuous_separationComponent_disjointTopology
      (X := MarketOrderPayload) OrderSide.buy)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 1.

Original label: Step 1 continuity, from `prop:separation-continuous`.

Informal statement: extracting sell orders is continuous.
-/
theorem continuous_sellOrders :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Continuous MarketTuple (Tuple LimitOrder)
      (tupleHausdorffMetricTopology (X := MarketOrder))
      (tupleHausdorffMetricTopology (X := LimitOrder))
      sellOrders := by
  simpa [sellOrders, MarketOrder, MarketOrderPayload, MarketTuple] using
    (continuous_separationComponent_disjointTopology
      (X := MarketOrderPayload) OrderSide.sell)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 1.

Original label: Step 1 full-map continuity, from `prop:separation-continuous`.

Informal statement: the map from a market tuple to its buy/sell separated
tuple family is continuous.
-/
theorem continuous_separatedMarket :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    letI : ∀ _ : OrderSide, TopologicalSpace (Tuple LimitOrder) :=
      fun _ => tupleHausdorffMetricTopology (X := LimitOrder)
    @Continuous MarketTuple (OrderSide → Tuple LimitOrder)
      (tupleHausdorffMetricTopology (X := MarketOrder)) inferInstance
      separatedMarket := by
  simpa [separatedMarket, MarketOrder, MarketOrderPayload, MarketTuple] using
    (continuous_separationOperator_disjointTopology
      (X := MarketOrderPayload))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 1.

Original label: finite buy/sell product-metric form of
`prop:separation-continuous`.

Informal statement: the full buy/sell separation map is continuous when the
two-component codomain is equipped with Lean's finite `Pi` extended-metric
topology.

Lean strategy / thesis strategy note: this is the market-specific wrapper for the thesis'
maximum product metric wording. The generic epsilon-delta proof is in
`continuous_separationOperator_finitePiEMetric`; here the only work is
specializing it to the finite side set `{buy,sell}`.
-/
theorem continuous_separatedMarket_finitePiEMetric :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    letI : ∀ _ : OrderSide, TopologicalSpace (Tuple LimitOrder) :=
      fun _ => tupleHausdorffMetricTopology (X := LimitOrder)
    @Continuous MarketTuple (OrderSide → Tuple LimitOrder)
      (tupleHausdorffMetricTopology (X := MarketOrder))
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      separatedMarket := by
  simpa [separatedMarket, MarketOrder, MarketOrderPayload, MarketTuple] using
    (continuous_separationOperator_finitePiEMetric
      (X := MarketOrderPayload))

/-! ## Step 2: Prices and Quantities -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2, `\bm{P}_{\mathrm{price}} = \bm{P}_1`.

Informal statement: project a tuple of limit orders to the tuple of prices.
-/
noncomputable def priceTuple (x : Tuple LimitOrder) : Tuple ℝ :=
  tupleProjection (X := OrderFieldValue) OrderField.price x

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2, `\bm{P}_{\mathrm{quantity}} = \bm{P}_2`.

Informal statement: project a tuple of limit orders to the tuple of
nonnegative quantities.
-/
noncomputable def quantityTuple (x : Tuple LimitOrder) : Tuple Quantity :=
  tupleProjection (X := OrderFieldValue) OrderField.quantity x

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2, joint coordinate map.

Informal statement: decompose a tuple of limit orders into its side-indexed
family of coordinate tuples.
-/
noncomputable def orderCoordinateTuples
    (x : Tuple LimitOrder) : (c : OrderField) → Tuple (OrderFieldValue c) :=
  tupleDecomposition x

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2, `(P_price b, P_quantity b)`.

Informal statement: return the price and quantity tuple projections together.
-/
noncomputable def orderCoordinates
    (x : Tuple LimitOrder) : Tuple ℝ × Tuple Quantity :=
  (priceTuple x, quantityTuple x)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: `\bm{p}^{\bm{b}}`.

Informal statement: the buy-price tuple of a market.
-/
noncomputable def buyPriceTuple (m : MarketTuple) : Tuple ℝ :=
  priceTuple (buyOrders m)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: `\bm{q}^{\bm{b}}`.

Informal statement: the buy-quantity tuple of a market.
-/
noncomputable def buyQuantityTuple (m : MarketTuple) : Tuple Quantity :=
  quantityTuple (buyOrders m)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: `\bm{p}^{\bm{s}}`.

Informal statement: the sell-price tuple of a market.
-/
noncomputable def sellPriceTuple (m : MarketTuple) : Tuple ℝ :=
  priceTuple (sellOrders m)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: `\bm{q}^{\bm{s}}`.

Informal statement: the sell-quantity tuple of a market.
-/
noncomputable def sellQuantityTuple (m : MarketTuple) : Tuple Quantity :=
  quantityTuple (sellOrders m)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: length bookkeeping for `\bm{p}^{\bm{b}}` and
`\bm{q}^{\bm{b}}`.

Informal statement: the buy price and buy quantity tuples have the same
length, since both are coordinate projections of the same buy-order tuple.
-/
theorem buyPriceTuple_length_eq_buyQuantityTuple_length (m : MarketTuple) :
    (buyPriceTuple m).length = (buyQuantityTuple m).length := by
  rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: length bookkeeping for `\bm{p}^{\bm{s}}` and
`\bm{q}^{\bm{s}}`.

Informal statement: the sell price and sell quantity tuples have the same
length, since both are coordinate projections of the same sell-order tuple.
-/
theorem sellPriceTuple_length_eq_sellQuantityTuple_length (m : MarketTuple) :
    (sellPriceTuple m).length = (sellQuantityTuple m).length := by
  rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: continuity of `P_price`.

Informal statement: the price projection on tuple space is continuous.

Lean strategy / thesis strategy note: this is the market-order specialization of the individual
projection clause in `prop:tuple-projection-continuous`.
-/
theorem continuous_priceTuple :
    @Continuous (Tuple LimitOrder) (Tuple ℝ)
      (tupleHausdorffMetricTopology (X := LimitOrder))
      (tupleHausdorffMetricTopology (X := ℝ))
      priceTuple := by
  simpa [priceTuple, LimitOrder, OrderFieldValue, Quantity] using
    (continuous_tupleProjection_tupleHausdorff
      (X := OrderFieldValue) OrderField.price)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: continuity of `P_quantity`.

Informal statement: the quantity projection on tuple space is continuous.

Lean strategy / thesis strategy note: this is the market-order specialization of the individual
projection clause in `prop:tuple-projection-continuous`.
-/
theorem continuous_quantityTuple :
    @Continuous (Tuple LimitOrder) (Tuple Quantity)
      (tupleHausdorffMetricTopology (X := LimitOrder))
      (tupleHausdorffMetricTopology (X := Quantity))
      quantityTuple := by
  simpa [quantityTuple, LimitOrder, OrderFieldValue, Quantity] using
    (continuous_tupleProjection_tupleHausdorff
      (X := OrderFieldValue) OrderField.quantity)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: joint form of `prop:tuple-projection-continuous`.

Informal statement: the full price/quantity decomposition map is continuous.

Lean strategy / thesis strategy note: this is the market-order specialization of the full
decomposition-continuity clause of `prop:tuple-projection-continuous`.
-/
theorem continuous_orderCoordinateTuples :
    letI : ∀ c : OrderField, TopologicalSpace (Tuple (OrderFieldValue c)) :=
      fun c => tupleHausdorffMetricTopology (X := OrderFieldValue c)
    @Continuous (Tuple LimitOrder) ((c : OrderField) → Tuple (OrderFieldValue c))
      (tupleHausdorffMetricTopology (X := LimitOrder)) inferInstance
      orderCoordinateTuples := by
  simpa [orderCoordinateTuples, LimitOrder, OrderFieldValue, Quantity] using
    (continuous_tupleDecomposition_tupleHausdorff (X := OrderFieldValue))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: market-order injectivity clause of
`prop:tuple-projection-continuous`.

Informal statement: a tuple of limit orders is recovered from its price tuple
and quantity tuple, equivalently from the full family of order-coordinate
tuples.

Lean strategy / thesis strategy note: the thesis proves injectivity of the finite product
decomposition by coordinatewise equality. The generic proof is
`tupleDecomposition_injective`; this theorem exposes the exact market-order
instance used in Step 2.
-/
theorem orderCoordinateTuples_injective :
    Function.Injective orderCoordinateTuples := by
  haveI : Nonempty OrderField := ⟨OrderField.price⟩
  simpa [orderCoordinateTuples, LimitOrder, OrderFieldValue, Quantity] using
    (tupleDecomposition_injective (A := OrderField) (X := OrderFieldValue))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 joint continuity of
`b \mapsto (P_price b, P_quantity b)` and analogously for sells.

Informal statement: sending an order tuple to its pair of price and quantity
tuples is continuous.
-/
theorem continuous_orderCoordinates :
    letI : TopologicalSpace (Tuple ℝ) :=
      tupleHausdorffMetricTopology (X := ℝ)
    letI : TopologicalSpace (Tuple Quantity) :=
      tupleHausdorffMetricTopology (X := Quantity)
    @Continuous (Tuple LimitOrder) (Tuple ℝ × Tuple Quantity)
      (tupleHausdorffMetricTopology (X := LimitOrder)) inferInstance
      orderCoordinates := by
  letI : TopologicalSpace (Tuple LimitOrder) :=
    tupleHausdorffMetricTopology (X := LimitOrder)
  letI : TopologicalSpace (Tuple ℝ) :=
    tupleHausdorffMetricTopology (X := ℝ)
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  exact continuous_priceTuple.prodMk continuous_quantityTuple

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 continuity of `\bm{m} \mapsto \bm{p}^{\bm{b}}`.

Informal statement: the buy-price tuple is a continuous function of the
market tuple.
-/
theorem continuous_buyPriceTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Continuous MarketTuple (Tuple ℝ)
      (tupleHausdorffMetricTopology (X := MarketOrder))
      (tupleHausdorffMetricTopology (X := ℝ))
      buyPriceTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : TopologicalSpace MarketTuple :=
    tupleHausdorffMetricTopology (X := MarketOrder)
  letI : TopologicalSpace (Tuple LimitOrder) :=
    tupleHausdorffMetricTopology (X := LimitOrder)
  letI : TopologicalSpace (Tuple ℝ) :=
    tupleHausdorffMetricTopology (X := ℝ)
  change Continuous buyPriceTuple
  exact continuous_priceTuple.comp continuous_buyOrders

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 continuity of `\bm{m} \mapsto \bm{q}^{\bm{b}}`.

Informal statement: the buy-quantity tuple is a continuous function of the
market tuple.
-/
theorem continuous_buyQuantityTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Continuous MarketTuple (Tuple Quantity)
      (tupleHausdorffMetricTopology (X := MarketOrder))
      (tupleHausdorffMetricTopology (X := Quantity))
      buyQuantityTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : TopologicalSpace MarketTuple :=
    tupleHausdorffMetricTopology (X := MarketOrder)
  letI : TopologicalSpace (Tuple LimitOrder) :=
    tupleHausdorffMetricTopology (X := LimitOrder)
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  change Continuous buyQuantityTuple
  exact continuous_quantityTuple.comp continuous_buyOrders

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 continuity of `\bm{m} \mapsto \bm{p}^{\bm{s}}`.

Informal statement: the sell-price tuple is a continuous function of the
market tuple.
-/
theorem continuous_sellPriceTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Continuous MarketTuple (Tuple ℝ)
      (tupleHausdorffMetricTopology (X := MarketOrder))
      (tupleHausdorffMetricTopology (X := ℝ))
      sellPriceTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : TopologicalSpace MarketTuple :=
    tupleHausdorffMetricTopology (X := MarketOrder)
  letI : TopologicalSpace (Tuple LimitOrder) :=
    tupleHausdorffMetricTopology (X := LimitOrder)
  letI : TopologicalSpace (Tuple ℝ) :=
    tupleHausdorffMetricTopology (X := ℝ)
  change Continuous sellPriceTuple
  exact continuous_priceTuple.comp continuous_sellOrders

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 continuity of `\bm{m} \mapsto \bm{q}^{\bm{s}}`.

Informal statement: the sell-quantity tuple is a continuous function of the
market tuple.
-/
theorem continuous_sellQuantityTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Continuous MarketTuple (Tuple Quantity)
      (tupleHausdorffMetricTopology (X := MarketOrder))
      (tupleHausdorffMetricTopology (X := Quantity))
      sellQuantityTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : TopologicalSpace MarketTuple :=
    tupleHausdorffMetricTopology (X := MarketOrder)
  letI : TopologicalSpace (Tuple LimitOrder) :=
    tupleHausdorffMetricTopology (X := LimitOrder)
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  change Continuous sellQuantityTuple
  exact continuous_quantityTuple.comp continuous_sellOrders

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 measurability of `\bm{p}^{\bm{b}}`.

Informal statement: the buy-price tuple is Borel measurable.
-/
theorem measurable_buyPriceTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple ℝ)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := ℝ))
      buyPriceTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : TopologicalSpace MarketTuple :=
    tupleHausdorffMetricTopology (X := MarketOrder)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : OpensMeasurableSpace MarketTuple := ⟨le_rfl⟩
  letI : BorelSpace MarketTuple := ⟨rfl⟩
  letI : TopologicalSpace (Tuple ℝ) :=
    tupleHausdorffMetricTopology (X := ℝ)
  letI : MeasurableSpace (Tuple ℝ) :=
    tupleHausdorffBorel (X := ℝ)
  letI : OpensMeasurableSpace (Tuple ℝ) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple ℝ) := ⟨rfl⟩
  exact continuous_buyPriceTuple.measurable

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 measurability of `\bm{q}^{\bm{b}}`.

Informal statement: the buy-quantity tuple is Borel measurable.
-/
theorem measurable_buyQuantityTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple Quantity)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := Quantity))
      buyQuantityTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : TopologicalSpace MarketTuple :=
    tupleHausdorffMetricTopology (X := MarketOrder)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : OpensMeasurableSpace MarketTuple := ⟨le_rfl⟩
  letI : BorelSpace MarketTuple := ⟨rfl⟩
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  letI : OpensMeasurableSpace (Tuple Quantity) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple Quantity) := ⟨rfl⟩
  exact continuous_buyQuantityTuple.measurable

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 measurability of `\bm{p}^{\bm{s}}`.

Informal statement: the sell-price tuple is Borel measurable.
-/
theorem measurable_sellPriceTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple ℝ)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := ℝ))
      sellPriceTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : TopologicalSpace MarketTuple :=
    tupleHausdorffMetricTopology (X := MarketOrder)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : OpensMeasurableSpace MarketTuple := ⟨le_rfl⟩
  letI : BorelSpace MarketTuple := ⟨rfl⟩
  letI : TopologicalSpace (Tuple ℝ) :=
    tupleHausdorffMetricTopology (X := ℝ)
  letI : MeasurableSpace (Tuple ℝ) :=
    tupleHausdorffBorel (X := ℝ)
  letI : OpensMeasurableSpace (Tuple ℝ) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple ℝ) := ⟨rfl⟩
  exact continuous_sellPriceTuple.measurable

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 2.

Original label: Step 2 measurability of `\bm{q}^{\bm{s}}`.

Informal statement: the sell-quantity tuple is Borel measurable.
-/
theorem measurable_sellQuantityTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple Quantity)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := Quantity))
      sellQuantityTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : TopologicalSpace MarketTuple :=
    tupleHausdorffMetricTopology (X := MarketOrder)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : OpensMeasurableSpace MarketTuple := ⟨le_rfl⟩
  letI : BorelSpace MarketTuple := ⟨rfl⟩
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  letI : OpensMeasurableSpace (Tuple Quantity) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple Quantity) := ⟨rfl⟩
  exact continuous_sellQuantityTuple.measurable

/-! ## Step 3: Minimal Sorting Permutations -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `eq:minimal-sort`, order `\leq`.

Informal statement: the `\leq`-minimal permutation map sends a real tuple to
the finite permutation produced by the Chapter 2 least-index
value-minimal sorting recursion.

Lean strategy / thesis relation note: the thesis defines the permutation recursively by remaining
index sets `D_k`. In Lean this recursion was already implemented in Chapter 2
as `minimumSortPermutation`; this definition specializes it to real prices.
-/
noncomputable def realMinimalPermutationLE (x : Tuple ℝ) :
    FinitePermutations :=
  Sigma.mk x.length (minimumSortPermutation (X := ℝ) x)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: auxiliary representation for `eq:minimal-sort`, order `\geq`.

Informal statement: view a real tuple in the order-dual real line. Sorting
this dual tuple increasingly is the Lean representation of sorting the
original tuple decreasingly.
-/
noncomputable def dualizeRealTuple (x : Tuple ℝ) :
    Tuple (OrderDual ℝ) :=
  Sigma.mk x.length (fun i => OrderDual.toDual (Tuple.entry x i))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `eq:minimal-sort`, order `\geq`.

Informal statement: the `\geq`-minimal permutation map sends a real tuple to
the finite permutation obtained by applying the Chapter 2 minimum-sort
recursion in the order-dual real line.

Lean strategy / thesis relation note: this keeps the thesis' two usual orders
while avoiding a second copy of the recursive proof. The order-dual formulation
is type-theoretic bookkeeping for the same decreasing-order recursion.
-/
noncomputable def realMinimalPermutationGE (x : Tuple ℝ) :
    FinitePermutations :=
  Sigma.mk x.length
    (minimumSortPermutation (X := OrderDual ℝ) (dualizeRealTuple x))

/-- The increasing minimal real permutation has the same length as its tuple. -/
@[simp]
theorem realMinimalPermutationLE_length (x : Tuple ℝ) :
    (realMinimalPermutationLE x).1 = x.length :=
  rfl

/-- The decreasing minimal real permutation has the same length as its tuple. -/
@[simp]
theorem realMinimalPermutationGE_length (x : Tuple ℝ) :
    (realMinimalPermutationGE x).1 = x.length :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `eq:minimal-sort`, compatibility with the sorted tuple.

Informal statement: sorting a real tuple increasingly is the same as applying
the `\leq`-minimal permutation map to that tuple.
-/
theorem realMinimumSortLE_eq_permutationMap (x : Tuple ℝ) :
    minimumSort (X := ℝ) x =
      permutationMap x (realMinimalPermutationLE x) := by
  rcases x with ⟨n, x⟩
  simp [realMinimalPermutationLE,
    minimumSort_eq_permute_minimumSortPermutation]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `eq:minimal-sort`, sortedness of the selected `\leq`
permutation.

Informal statement: the real `\leq`-minimal permutation really sorts the tuple.
-/
theorem realMinimalPermutationLE_sorts (x : Tuple ℝ) :
    IsSorted (permutationMap x (realMinimalPermutationLE x)) := by
  rw [← realMinimumSortLE_eq_permutationMap]
  exact minimumSort_isSorted (X := ℝ) x

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `eq:minimal-sort`, compatibility for order `\geq`.

Informal statement: sorting the order-dual tuple increasingly is the same as
applying the `\geq`-minimal permutation map.
-/
theorem realMinimumSortGE_dual_eq_permutationMap (x : Tuple ℝ) :
    minimumSort (X := OrderDual ℝ) (dualizeRealTuple x) =
      permutationMap (dualizeRealTuple x) (realMinimalPermutationGE x) := by
  rcases x with ⟨n, x⟩
  simp [realMinimalPermutationGE, dualizeRealTuple,
    minimumSort_eq_permute_minimumSortPermutation]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `eq:minimal-sort`, sortedness of the selected `\geq`
permutation.

Informal statement: the real `\geq`-minimal permutation sorts the order-dual
tuple increasingly, equivalently the original tuple decreasingly.
-/
theorem realMinimalPermutationGE_sorts_dual (x : Tuple ℝ) :
    IsSorted
      (permutationMap (dualizeRealTuple x) (realMinimalPermutationGE x)) := by
  rw [← realMinimumSortGE_dual_eq_permutationMap]
  exact minimumSort_isSorted (X := OrderDual ℝ) (dualizeRealTuple x)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: auxiliary continuity for `eq:minimal-sort`, order `\geq`.

Informal statement: sending a real price tuple to the same tuple viewed in
the order-dual real line is continuous.

Lean strategy / thesis relation note: the thesis treats decreasing order directly. Lean uses the
type alias `OrderDual ℝ`; this theorem records that the translation does not
change the tuple topology.
-/
theorem continuous_dualizeRealTuple :
    @Continuous (Tuple ℝ) (Tuple (OrderDual ℝ))
      (tupleHausdorffMetricTopology (X := ℝ))
      (tupleHausdorffMetricTopology (X := OrderDual ℝ))
      dualizeRealTuple := by
  letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology (X := ℝ)
  letI : TopologicalSpace (Tuple (OrderDual ℝ)) :=
    tupleHausdorffMetricTopology (X := OrderDual ℝ)
  rw [continuous_tupleHausdorff_iff_fixedLength]
  intro n
  change @Continuous (Fin n → ℝ) (Tuple (OrderDual ℝ)) inferInstance
    (tupleHausdorffMetricTopology (X := OrderDual ℝ))
    (fun x : Fin n → ℝ =>
      Sigma.mk n (fun i => OrderDual.toDual (x i)))
  rw [tupleHausdorffMetricTopology_eq_sigma]
  have hcoord : Continuous
      (fun x : Fin n → ℝ => fun i : Fin n =>
        OrderDual.toDual (x i)) :=
    continuous_pi fun i => continuous_toDual.comp (continuous_apply i)
  letI : TopologicalSpace (Tuple (OrderDual ℝ)) := instTopologicalSpaceSigma
  exact continuous_sigmaMk.comp hcoord

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: auxiliary measurability for `eq:minimal-sort`, order `\geq`.

Informal statement: the order-dual translation on real tuples is Borel
measurable.
-/
theorem measurable_dualizeRealTuple :
    @Measurable (Tuple ℝ) (Tuple (OrderDual ℝ))
      (tupleHausdorffBorel (X := ℝ))
      (tupleHausdorffBorel (X := OrderDual ℝ))
      dualizeRealTuple := by
  letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology (X := ℝ)
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  letI : OpensMeasurableSpace (Tuple ℝ) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple ℝ) := ⟨rfl⟩
  letI : TopologicalSpace (Tuple (OrderDual ℝ)) :=
    tupleHausdorffMetricTopology (X := OrderDual ℝ)
  letI : MeasurableSpace (Tuple (OrderDual ℝ)) :=
    tupleHausdorffBorel (X := OrderDual ℝ)
  letI : OpensMeasurableSpace (Tuple (OrderDual ℝ)) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple (OrderDual ℝ)) := ⟨rfl⟩
  exact continuous_dualizeRealTuple.measurable

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `lem:tuple-space-measurable-2`.

Informal statement: a subset of real tuple space is Borel iff all of its
fixed-length restrictions are Borel subsets of the corresponding Euclidean
finite product.

Lean strategy / thesis relation note: this is exactly the Chapter 2 Sigma/fixed-length Borel bridge,
specialized to `X = ℝ`.
-/
theorem measurableSet_realTupleHausdorff_iff_fixedLength
    {s : Set (Tuple ℝ)} :
    @MeasurableSet (Tuple ℝ) (tupleHausdorffBorel (X := ℝ)) s ↔
      ∀ n : ℕ,
        @MeasurableSet (Fin n → ℝ) (@borel (Fin n → ℝ) inferInstance)
          {x | (Sigma.mk n x : Tuple ℝ) ∈ s} := by
  simpa using
    (measurableSet_tupleHausdorff_iff_fixedLength (X := ℝ) (s := s))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: tuple-valued prerequisite for
`prop:minimal-sorting-measurable`.

Informal statement: the real increasing minimum-sort map is Borel measurable.

Lean strategy / thesis relation note: the proposition in the thesis is stated for the
permutation-valued map `\pi^\preceq`. This theorem records the companion
tuple-valued specialization of the Chapter 2 result.
-/
theorem measurable_minimumSort_real_LE :
    @Measurable (Tuple ℝ) (Tuple ℝ)
      (tupleHausdorffBorel (X := ℝ)) (tupleHausdorffBorel (X := ℝ))
      (minimumSort (X := ℝ)) := by
  have hclosed : IsClosed
      ({p : ℝ × ℝ | p.1 ≤ p.2} : Set (ℝ × ℝ)) :=
    isClosed_le continuous_fst continuous_snd
  have hle :
      @MeasurableSet (ℝ × ℝ) (@borel (ℝ × ℝ) inferInstance)
        ({p : ℝ × ℝ | p.1 ≤ p.2} : Set (ℝ × ℝ)) := by
    letI : MeasurableSpace (ℝ × ℝ) := @borel (ℝ × ℝ) inferInstance
    letI : BorelSpace (ℝ × ℝ) := ⟨rfl⟩
    exact hclosed.measurableSet
  exact measurable_minimumSort_of_borelOrder (X := ℝ) hle

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `prop:minimal-sorting-measurable`, order `\leq`.

Informal statement: the increasing real-valued minimal price sorting
permutation map is Borel measurable.

Lean strategy / thesis relation note: this is the thesis proposition specialized to real price
tuples, using the Chapter 2 finite-cell pasting proof for the
permutation-valued minimum sorting rule.
-/
theorem measurable_realMinimalPermutationLE :
    letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
    letI : MeasurableSpace FinitePermutations :=
      @borel FinitePermutations finitePermutationMetricTopology
    @Measurable (Tuple ℝ) FinitePermutations
      (tupleHausdorffBorel (X := ℝ))
      (@borel FinitePermutations finitePermutationMetricTopology)
      realMinimalPermutationLE := by
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  have hclosed : IsClosed
      ({p : ℝ × ℝ | p.1 ≤ p.2} : Set (ℝ × ℝ)) :=
    isClosed_le continuous_fst continuous_snd
  have hle :
      @MeasurableSet (ℝ × ℝ) (@borel (ℝ × ℝ) inferInstance)
        ({p : ℝ × ℝ | p.1 ≤ p.2} : Set (ℝ × ℝ)) := by
    letI : MeasurableSpace (ℝ × ℝ) := @borel (ℝ × ℝ) inferInstance
    letI : BorelSpace (ℝ × ℝ) := ⟨rfl⟩
    exact hclosed.measurableSet
  simpa [realMinimalPermutationLE] using
    (measurable_minimumSortPermutation_of_borelOrder (X := ℝ) hle)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `prop:minimal-sorting-measurable`, order `\geq`.

Informal statement: the decreasing real-valued minimal price sorting
permutation map is Borel measurable.

Lean strategy / thesis relation note: this is proved by transporting the thesis' decreasing order to
the increasing order on `OrderDual ℝ`, then composing with the measurable
dualization map above.
-/
theorem measurable_realMinimalPermutationGE :
    letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
    letI : MeasurableSpace FinitePermutations :=
      @borel FinitePermutations finitePermutationMetricTopology
    @Measurable (Tuple ℝ) FinitePermutations
      (tupleHausdorffBorel (X := ℝ))
      (@borel FinitePermutations finitePermutationMetricTopology)
      realMinimalPermutationGE := by
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  have hclosed : IsClosed
      ({p : OrderDual ℝ × OrderDual ℝ | p.1 ≤ p.2} :
        Set (OrderDual ℝ × OrderDual ℝ)) :=
    isClosed_le continuous_fst continuous_snd
  have hle :
      @MeasurableSet (OrderDual ℝ × OrderDual ℝ)
        (@borel (OrderDual ℝ × OrderDual ℝ) inferInstance)
        ({p : OrderDual ℝ × OrderDual ℝ | p.1 ≤ p.2} :
          Set (OrderDual ℝ × OrderDual ℝ)) := by
    letI : MeasurableSpace (OrderDual ℝ × OrderDual ℝ) :=
      @borel (OrderDual ℝ × OrderDual ℝ) inferInstance
    letI : BorelSpace (OrderDual ℝ × OrderDual ℝ) := ⟨rfl⟩
    exact hclosed.measurableSet
  have hperm :
      @Measurable (Tuple (OrderDual ℝ)) FinitePermutations
        (tupleHausdorffBorel (X := OrderDual ℝ))
        (@borel FinitePermutations finitePermutationMetricTopology)
        (fun y => Sigma.mk y.length
          (minimumSortPermutation (X := OrderDual ℝ) y)) := by
    simpa using
      (measurable_minimumSortPermutation_of_borelOrder
        (X := OrderDual ℝ) hle)
  simpa [realMinimalPermutationGE, dualizeRealTuple] using
    hperm.comp measurable_dualizeRealTuple

/-! ## Step 3: Sorted Buy and Sell Price/Quantity Tuples -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: definition after `prop:minimal-sorting-measurable`,
`\tilde{\bm{p}}^{\bm{b}} = \bm{p}^{\bm{b}}[\pi^\ge(\bm{p}^{\bm{b}})]`.

Informal statement: sort buy prices decreasingly by applying the measurable
`\geq`-minimal price permutation.
-/
noncomputable def sortedBuyPriceTuple (m : MarketTuple) : Tuple ℝ :=
  permutationMap (buyPriceTuple m) (realMinimalPermutationGE (buyPriceTuple m))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: definition after `prop:minimal-sorting-measurable`,
`\tilde{\bm{q}}^{\bm{b}} = \bm{q}^{\bm{b}}[\pi^\ge(\bm{p}^{\bm{b}})]`.

Informal statement: reindex buy quantities by the same decreasing price
permutation used for buy prices.
-/
noncomputable def sortedBuyQuantityTuple (m : MarketTuple) : Tuple Quantity :=
  permutationMap (buyQuantityTuple m)
    (realMinimalPermutationGE (buyPriceTuple m))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: definition after `prop:minimal-sorting-measurable`,
`\tilde{\bm{p}}^{\bm{s}} = \bm{p}^{\bm{s}}[\pi^\le(\bm{p}^{\bm{s}})]`.

Informal statement: sort sell prices increasingly by applying the measurable
`\leq`-minimal price permutation.
-/
noncomputable def sortedSellPriceTuple (m : MarketTuple) : Tuple ℝ :=
  permutationMap (sellPriceTuple m)
    (realMinimalPermutationLE (sellPriceTuple m))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: definition after `prop:minimal-sorting-measurable`,
`\tilde{\bm{q}}^{\bm{s}} = \bm{q}^{\bm{s}}[\pi^\le(\bm{p}^{\bm{s}})]`.

Informal statement: reindex sell quantities by the same increasing price
permutation used for sell prices.
-/
noncomputable def sortedSellQuantityTuple (m : MarketTuple) : Tuple Quantity :=
  permutationMap (sellQuantityTuple m)
    (realMinimalPermutationLE (sellPriceTuple m))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: paired definition
`(\tilde{\bm{p}}^{\bm{b}},\tilde{\bm{q}}^{\bm{b}})`.

Informal statement: the sorted buy price tuple paired with the correspondingly
reindexed buy quantity tuple.
-/
noncomputable def sortedBuyCoordinates
    (m : MarketTuple) : Tuple ℝ × Tuple Quantity :=
  (sortedBuyPriceTuple m, sortedBuyQuantityTuple m)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: paired definition
`(\tilde{\bm{p}}^{\bm{s}},\tilde{\bm{q}}^{\bm{s}})`.

Informal statement: the sorted sell price tuple paired with the
correspondingly reindexed sell quantity tuple.
-/
noncomputable def sortedSellCoordinates
    (m : MarketTuple) : Tuple ℝ × Tuple Quantity :=
  (sortedSellPriceTuple m, sortedSellQuantityTuple m)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: measurable sorting of
`\tilde{\bm{p}}^{\bm{b}}`.

Informal statement: the sorted buy-price tuple is Borel measurable.

Lean strategy / thesis relation note: this is the thesis composition argument: measurable
`\bm{p}^{\bm{b}}`, measurable `\pi^\ge`, and continuous two-variable
permutation application.
-/
theorem measurable_sortedBuyPriceTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple ℝ)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := ℝ))
      sortedBuyPriceTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  have hπ :
      @Measurable MarketTuple FinitePermutations
        (tupleHausdorffBorel (X := MarketOrder))
        (@borel FinitePermutations finitePermutationMetricTopology)
        (fun m => realMinimalPermutationGE (buyPriceTuple m)) :=
    measurable_realMinimalPermutationGE.comp measurable_buyPriceTuple
  simpa [sortedBuyPriceTuple] using
    (measurable_permutationMap_comp
      (α := MarketTuple) (X := ℝ)
      (f := buyPriceTuple)
      (π := fun m => realMinimalPermutationGE (buyPriceTuple m))
      measurable_buyPriceTuple hπ)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: measurable sorting of
`\tilde{\bm{q}}^{\bm{b}}`.

Informal statement: the buy-quantity tuple reindexed by the buy-price sorting
permutation is Borel measurable.
-/
theorem measurable_sortedBuyQuantityTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple Quantity)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := Quantity))
      sortedBuyQuantityTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  have hπ :
      @Measurable MarketTuple FinitePermutations
        (tupleHausdorffBorel (X := MarketOrder))
        (@borel FinitePermutations finitePermutationMetricTopology)
        (fun m => realMinimalPermutationGE (buyPriceTuple m)) :=
    measurable_realMinimalPermutationGE.comp measurable_buyPriceTuple
  simpa [sortedBuyQuantityTuple] using
    (measurable_permutationMap_comp
      (α := MarketTuple) (X := Quantity)
      (f := buyQuantityTuple)
      (π := fun m => realMinimalPermutationGE (buyPriceTuple m))
      measurable_buyQuantityTuple hπ)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: measurable sorting of
`\tilde{\bm{p}}^{\bm{s}}`.

Informal statement: the sorted sell-price tuple is Borel measurable.
-/
theorem measurable_sortedSellPriceTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple ℝ)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := ℝ))
      sortedSellPriceTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  have hπ :
      @Measurable MarketTuple FinitePermutations
        (tupleHausdorffBorel (X := MarketOrder))
        (@borel FinitePermutations finitePermutationMetricTopology)
        (fun m => realMinimalPermutationLE (sellPriceTuple m)) :=
    measurable_realMinimalPermutationLE.comp measurable_sellPriceTuple
  simpa [sortedSellPriceTuple] using
    (measurable_permutationMap_comp
      (α := MarketTuple) (X := ℝ)
      (f := sellPriceTuple)
      (π := fun m => realMinimalPermutationLE (sellPriceTuple m))
      measurable_sellPriceTuple hπ)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: measurable sorting of
`\tilde{\bm{q}}^{\bm{s}}`.

Informal statement: the sell-quantity tuple reindexed by the sell-price
sorting permutation is Borel measurable.
-/
theorem measurable_sortedSellQuantityTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple Quantity)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := Quantity))
      sortedSellQuantityTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : TopologicalSpace FinitePermutations := finitePermutationMetricTopology
  letI : MeasurableSpace FinitePermutations :=
    @borel FinitePermutations finitePermutationMetricTopology
  have hπ :
      @Measurable MarketTuple FinitePermutations
        (tupleHausdorffBorel (X := MarketOrder))
        (@borel FinitePermutations finitePermutationMetricTopology)
        (fun m => realMinimalPermutationLE (sellPriceTuple m)) :=
    measurable_realMinimalPermutationLE.comp measurable_sellPriceTuple
  simpa [sortedSellQuantityTuple] using
    (measurable_permutationMap_comp
      (α := MarketTuple) (X := Quantity)
      (f := sellQuantityTuple)
      (π := fun m => realMinimalPermutationLE (sellPriceTuple m))
      measurable_sellQuantityTuple hπ)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: measurable paired buy sorting
`(\tilde{\bm{p}}^{\bm{b}},\tilde{\bm{q}}^{\bm{b}})`.

Informal statement: the paired sorted buy price/quantity map is Borel
measurable.
-/
theorem measurable_sortedBuyCoordinates :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
    letI : MeasurableSpace (Tuple Quantity) :=
      tupleHausdorffBorel (X := Quantity)
    @Measurable MarketTuple (Tuple ℝ × Tuple Quantity)
      (tupleHausdorffBorel (X := MarketOrder)) inferInstance
      sortedBuyCoordinates := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : MeasurableSpace (Tuple ℝ) :=
    tupleHausdorffBorel (X := ℝ)
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  change Measurable sortedBuyCoordinates
  exact Measurable.prod measurable_sortedBuyPriceTuple
    measurable_sortedBuyQuantityTuple

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: measurable paired sell sorting
`(\tilde{\bm{p}}^{\bm{s}},\tilde{\bm{q}}^{\bm{s}})`.

Informal statement: the paired sorted sell price/quantity map is Borel
measurable.
-/
theorem measurable_sortedSellCoordinates :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
    letI : MeasurableSpace (Tuple Quantity) :=
      tupleHausdorffBorel (X := Quantity)
    @Measurable MarketTuple (Tuple ℝ × Tuple Quantity)
      (tupleHausdorffBorel (X := MarketOrder)) inferInstance
      sortedSellCoordinates := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : MeasurableSpace (Tuple ℝ) :=
    tupleHausdorffBorel (X := ℝ)
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  change Measurable sortedSellCoordinates
  exact Measurable.prod measurable_sortedSellPriceTuple
    measurable_sortedSellQuantityTuple

end Sorting
end MarketClearing
end Foundations
end Thesis
