import Mathlib.Data.NNReal.Basic
import Thesis.Foundations.MarketClearing.Selection

/-!
# Market Clearing: Sorting

Blueprint module for
`1 - theoretical foundations/4_market_clearing.tex`,
clearing procedure steps 1--3.

Formal content:

* buy/sell separation;
* price and quantity tuple projections;

Planned formal content:

* `defn:minimal-sort`;
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

Original label: `defn:minimal-sort`, order `\leq`.

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

Original label: auxiliary representation for `defn:minimal-sort`, order `\geq`.

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

Original label: `defn:minimal-sort`, order `\geq`.

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

Original label: `defn:minimal-sort`, compatibility with the sorted tuple.

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

Original label: `defn:minimal-sort`, sortedness of the selected `\leq`
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

Original label: `defn:minimal-sort`, compatibility for order `\geq`.

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

Original label: `defn:minimal-sort`, sortedness of the selected `\geq`
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

Original label: auxiliary continuity for `defn:minimal-sort`, order `\geq`.

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

Original label: auxiliary measurability for `defn:minimal-sort`, order `\geq`.

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

Original label: `lem:tuple-space-measurable-2`, single-factor restriction
criterion.

Informal statement: a subset of real tuple space is Borel iff all of its
fixed-length restrictions are Borel subsets of the corresponding Euclidean
finite product.

Lean strategy / thesis relation note: this is the Chapter 2 Sigma/fixed-length
Borel bridge specialized to `X = ℝ`, i.e. the `k = 1` restriction criterion.
The thesis lemma itself, for `k` simultaneous layers
`L = ℝ^{n_1} × ⋯ × ℝ^{n_k} ⊆ \mathscr{T}(ℝ)^k`, is `fixedLayers_Borel` below,
proved along the thesis route.
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

Original label: `lem:tuple-space-measurable-2`, the layer
`L = ℝ^{n_1} × ⋯ × ℝ^{n_k}`.

Informal statement: the simultaneous fixed-length layer of `\mathscr{T}(ℝ)^k`
with prescribed lengths `n_1, …, n_k` (with `ℝ^0 = {e}`), as the image of the
Euclidean product under the coordinatewise layer embeddings.
-/
def fixedLayers {k : ℕ} (n : Fin k → ℕ)
    (x : (i : Fin k) → Fin (n i) → ℝ) : Fin k → Tuple ℝ :=
  fun i => ⟨n i, x i⟩

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `lem:tuple-space-measurable-2`, topological step.

Informal statement: `L` is open in `\mathscr{T}(ℝ)^k` and its subspace
topology is the usual topology of `ℝ^{n_1} × ⋯ × ℝ^{n_k}`.

Lean strategy / thesis relation note: this is the standard-machinery step of
the thesis proof. Each fixed-length layer of `\mathscr{T}(ℝ)` is clopen and
homeomorphic to `ℝ^n` (the tuple topology is the Sigma topology,
`tupleHausdorffMetricTopology_eq_sigma`, so `Sigma.mk n` is an open
embedding); taking the product over the `k` factors gives the open embedding
of `L`.
-/
theorem fixedLayers_isOpenEmbedding {k : ℕ} (n : Fin k → ℕ) :
    letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology
    Topology.IsOpenEmbedding (fixedLayers n) := by
  letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology
  change @Topology.IsOpenEmbedding _ _ _
    (Pi.topologicalSpace (t₂ := fun _ => tupleHausdorffMetricTopology (X := ℝ))) _
  change @Topology.IsOpenEmbedding _ _ _
    (@Pi.topologicalSpace (Fin k) (fun _ => Tuple ℝ)
      (fun _ => tupleHausdorffMetricTopology (X := ℝ))) _
  rw [tupleHausdorffMetricTopology_eq_sigma]
  letI : TopologicalSpace (Tuple ℝ) := instTopologicalSpaceSigma
  exact Topology.IsOpenEmbedding.piMap (fun _ => Topology.IsOpenEmbedding.sigmaMk)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `lem:tuple-space-measurable-2`.

Informal statement: for `k ∈ ℕ` and lengths `n_1, …, n_k ∈ ℕ_0`, every Borel
subset of `L = ℝ^{n_1} × ⋯ × ℝ^{n_k}` is Borel in `\mathscr{T}(ℝ)^k` (with the
product of the tuple Hausdorff topologies), and conversely the trace on `L`
of a Borel subset of `\mathscr{T}(ℝ)^k` is Borel in `L`.

Lean strategy / thesis relation note: this is the thesis proof. Since `L`
embeds openly (hence Borel-measurably, with Borel image) by
`fixedLayers_isOpenEmbedding`, the Borel σ-algebra of `L` is the trace of the
Borel σ-algebra of `\mathscr{T}(ℝ)^k`, which gives both assertions; the second
one is the preimage statement under the embedding.
-/
theorem fixedLayers_Borel {k : ℕ} (n : Fin k → ℕ) :
    letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology
    (∀ A : Set ((i : Fin k) → Fin (n i) → ℝ),
      @MeasurableSet _ (borel _) A →
      @MeasurableSet _ (borel (Fin k → Tuple ℝ)) (fixedLayers n '' A)) ∧
    (∀ A : Set (Fin k → Tuple ℝ), @MeasurableSet _ (borel _) A →
      @MeasurableSet _ (borel _) (fixedLayers n ⁻¹' A)) := by
  letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology
  letI : MeasurableSpace (Fin k → Tuple ℝ) := borel _
  letI : BorelSpace (Fin k → Tuple ℝ) := ⟨rfl⟩
  letI : MeasurableSpace ((i : Fin k) → Fin (n i) → ℝ) := borel _
  letI : BorelSpace ((i : Fin k) → Fin (n i) → ℝ) := ⟨rfl⟩
  have h := (fixedLayers_isOpenEmbedding n).measurableEmbedding
  exact ⟨fun _ hA => h.measurableSet_image.mpr hA, fun _ hA => hA.preimage h.measurable⟩

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `lem:tuple-space-measurable-2`, case `k = 1`, as used in the
proof of `prop:minimal-sorting-measurable`.

Informal statement: a Borel subset of `ℝ^n` is Borel in `\mathscr{T}(ℝ)` for
the tuple Hausdorff Borel σ-algebra, via the length-`n` layer embedding.

Lean strategy / thesis relation note: same open-embedding argument as
`fixedLayers_Borel`, stated for one factor and the project's
`tupleHausdorffBorel` on `\mathscr{T}(ℝ)` so that fixed-length Borel fibres
can be transported to tuple space directly.
-/
theorem measurableSet_fixedLayer_image {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : @MeasurableSet (Fin n → ℝ) (@borel (Fin n → ℝ) inferInstance) A) :
    @MeasurableSet (Tuple ℝ) (tupleHausdorffBorel (X := ℝ))
      ((fun x : Fin n → ℝ => (Sigma.mk n x : Tuple ℝ)) '' A) := by
  letI : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology (X := ℝ)
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  letI : BorelSpace (Tuple ℝ) := ⟨rfl⟩
  letI : MeasurableSpace (Fin n → ℝ) := @borel (Fin n → ℝ) inferInstance
  letI : BorelSpace (Fin n → ℝ) := ⟨rfl⟩
  have hemb : Topology.IsOpenEmbedding
      (fun x : Fin n → ℝ => (Sigma.mk n x : Tuple ℝ)) := by
    change @Topology.IsOpenEmbedding (Fin n → ℝ) (Tuple ℝ) inferInstance
      (tupleHausdorffMetricTopology (X := ℝ)) _
    rw [tupleHausdorffMetricTopology_eq_sigma]
    exact Topology.IsOpenEmbedding.sigmaMk (σ := fun k : ℕ => Fin k → ℝ) (i := n)
  exact hemb.measurableEmbedding.measurableSet_image.mpr hA

/-! ### The cells `A^π_k`, `B^π_k` and the fibre identity of
`prop:minimal-sorting-measurable`

The thesis proof of `prop:minimal-sorting-measurable` fixes a permutation `π`
of length `n` and describes the fibre `𝒲_π = (π^⪯)⁻¹{π} ⊆ ℝ^n` as the finite
intersection `⋂_{k=1}^n (A^π_k ∩ B^π_k)`, where `A^π_k` says that `π(k)`
attains the `k`-th selected minimum and `B^π_k` enforces the smallest-index
tie-break. This section defines these cells for a general linear order, proves
the fibre identity along the greedy recursion of `defn:minimal-sort`, and shows
the cells are Borel. -/

section MinimalPermutationCells

open FiniteSets.FiniteSubsets

universe u

variable {X : Type u}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: the set `A^\pi_k` in the proof of
`prop:minimal-sorting-measurable`.

Informal statement: `A^\pi_k = ⋂_{j ∈ D^\pi_{k-1}} \{x ∈ ℝ^n \mid x(\pi(k)) ⪯ x(j)\}`
with `D^\pi_{k-1} = \{\pi(j) \mid j ≥ k\}`: the tuples for which `\pi(k)` attains the
`k`-th selected minimum.

Lean strategy / thesis relation note: `D^\pi_{k-1}` is enumerated as
`\{\pi(j) \mid k ≤ j\}`, so the intersection over `j ∈ D^\pi_{k-1}` becomes a
universal quantifier over `j ≥ k`. The cell is stated for any preorder `X`;
the thesis uses `X = ℝ` with `⪯ ∈ \{≤, ≥\}`.
-/
def minimalSelectionCell [Preorder X] {n : ℕ} (π : FinitePermutation n)
    (k : Fin n) : Set (Fin n → X) :=
  {x | ∀ j : Fin n, k ≤ j → x (π k) ≤ x (π j)}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: the set `B^\pi_k` in the proof of
`prop:minimal-sorting-measurable`.

Informal statement: `B^\pi_k = ⋂_{j ∈ D^\pi_{k-1}, j < \pi(k)} \{x \mid x(\pi(k)) ≠ x(j)\}`,
the tie-breaking rule preferring the smallest original index. As in the thesis,
`j ∈ D^\pi_{k-1}` with `j < \pi(k)` is written `j = \pi(m)` with `m > k`, so
`B^\pi_k = ⋂_{m > k, \pi(m) < \pi(k)} \{x \mid x(\pi(k)) ≠ x(\pi(m))\}`.
-/
def minimalTieBreakCell [Preorder X] {n : ℕ} (π : FinitePermutation n)
    (k : Fin n) : Set (Fin n → X) :=
  {x | ∀ m : Fin n, k < m → π m < π k → x (π k) ≠ x (π m)}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: the finite intersection `⋂_{k=1}^n (A^\pi_k ∩ B^\pi_k)` in the
proof of `prop:minimal-sorting-measurable`.

Informal statement: the candidate description of the fibre
`𝒲_\pi = \{x ∈ ℝ^{ℓ(\pi)} \mid \pi^⪯(x) = \pi\}` as a finite intersection of the
selection cells `A^\pi_k` and tie-break cells `B^\pi_k`. The identity with the
fibre is `minimumSortPermutation_eq_iff_mem_cell` below.
-/
def minimalPermutationCell [Preorder X] {n : ℕ} (π : FinitePermutation n) :
    Set (Fin n → X) :=
  ⋂ k : Fin n, minimalSelectionCell (X := X) π k ∩ minimalTieBreakCell (X := X) π k

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: pointwise reading of `⋂_{k=1}^n (A^\pi_k ∩ B^\pi_k)` in the proof
of `prop:minimal-sorting-measurable`.

Informal statement: `x ∈ ⋂_k (A^\pi_k ∩ B^\pi_k)` iff for all positions `k < m`,
`x(\pi(k)) ⪯ x(\pi(m))`, and `x(\pi(k)) ≠ x(\pi(m))` whenever `\pi(m) < \pi(k)`.

Lean strategy / thesis relation note: the `j = k` instance of `A^\pi_k` is
trivial (`x(\pi(k)) ⪯ x(\pi(k))`), so only `k < m` remains; this is the form
in which the greedy recursion is compared with the cells.
-/
theorem mem_minimalPermutationCell_iff [Preorder X] {n : ℕ}
    (π : FinitePermutation n) (x : Fin n → X) :
    x ∈ minimalPermutationCell (X := X) π ↔
      ∀ k m : Fin n, k < m →
        x (π k) ≤ x (π m) ∧ (π m < π k → x (π k) ≠ x (π m)) := by
  simp only [minimalPermutationCell, minimalSelectionCell, minimalTieBreakCell,
    Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro h k m hkm
    exact ⟨(h k).1 m hkm.le, (h k).2 m hkm⟩
  · intro h k
    refine ⟨fun j hkj => ?_, fun m hkm => (h k m hkm).2⟩
    rcases hkj.lt_or_eq with hlt | rfl
    · exact (h k j hlt).1
    · exact le_rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: Lean bookkeeping for the proof of
`prop:minimal-sorting-measurable`.

Informal statement: the relation between two graph points `p` (selected
earlier) and `q` (selected later) expressed by the cells: `p` has value `⪯`
the value of `q`, and if `q` has the smaller original index then the values
differ. A graph-point list is pairwise in this relation exactly when it lists
the cells' conditions position by position.
-/
def GreedyPairwiseStep [Preorder X] (p q : IndexAugmented X) : Prop :=
  IndexAugmented.value p ≤ IndexAugmented.value q ∧
    (IndexAugmented.index q < IndexAugmented.index p →
      IndexAugmented.value p ≠ IndexAugmented.value q)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "Sorted Tuples".

Original label: membership in `M^{(n)}`, the value-minimal remainder points of
`defn:sorting-finite-sets`.

Informal statement: a graph point is value-minimal in a finite remainder iff it
belongs to the remainder and no remainder point has strictly smaller value.

Lean strategy / thesis relation note: this unfolds the Chapter 2 definition with
the decidability instance used there (`classical`), so the lemma can be used
in a linear-order context without instance mismatch.
-/
theorem mem_valueMinimalElements_iff [Preorder X]
    (s : Finset (IndexAugmented X)) (p : IndexAugmented X) :
    p ∈ valueMinimalElements (X := X) s ↔
      p ∈ s ∧ ∀ q ∈ s, ¬ IndexAugmented.value q < IndexAugmented.value p := by
  classical
  rw [valueMinimalElements, Finset.mem_filter]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: the recursive argument for
`𝒲_\pi = ⋂_{k=1}^n (A^\pi_k ∩ B^\pi_k)` in the proof of
`prop:minimal-sorting-measurable`.

Informal statement: for a graph-point list `l` with pairwise distinct original
indices, the recursive least-index value-minimal selector of
`defn:minimal-sort` (Chapter 2's `\varsigma^\ast`) run on the finite set of
points of `l` returns exactly `l` iff `l` satisfies the cells' conditions
position by position.

Lean strategy / thesis relation note: this is the thesis argument, by
induction along the greedy recursion `D_0 ⊇ D_1 ⊇ ⋯`. "⊆": the head is the
least-index value-minimal point, so its value is `⪯` every later value, and
a later point with equal value must have a larger index. "⊇": if the list
satisfies the cell conditions then its head is value-minimal, has the least
index among value-minimal points (otherwise, in the words of the thesis,
`\pi^⪯` would have selected `\pi(m)` before `\pi(k)`), and is the unique
point with its index; hence the selector picks the head, removes it, and the
induction hypothesis handles the tail `D_k`.
-/
theorem distinctFiniteSetSortListAux_eq_iff_pairwise_greedy [LinearOrder X]
    (l : List (IndexAugmented X))
    (hidx : (l.map IndexAugmented.index).Nodup) :
    distinctFiniteSetSortListAux (X := X) (graphPointListToFinset (X := X) l) = l ↔
      List.Pairwise (GreedyPairwiseStep (X := X)) l := by
  classical
  induction l with
  | nil =>
      rw [distinctFiniteSetSortListAux.eq_1]
      simp [graphPointListToFinset]
  | cons p l ih =>
      rw [List.map_cons, List.nodup_cons] at hidx
      obtain ⟨hp_idx, hidx_tail⟩ := hidx
      have hp_not_tail : p ∉ l := fun h => hp_idx (List.mem_map.mpr ⟨p, h, rfl⟩)
      have hp_s : p ∈ graphPointListToFinset (X := X) (p :: l) :=
        (mem_graphPointListToFinset (X := X)).mpr List.mem_cons_self
      have hs : (graphPointListToFinset (X := X) (p :: l)).Nonempty := ⟨p, hp_s⟩
      have hmem_s : ∀ r ∈ graphPointListToFinset (X := X) (p :: l), r = p ∨ r ∈ l :=
        fun r hr => List.mem_cons.mp ((mem_graphPointListToFinset (X := X)).mp hr)
      have hl_s : ∀ r ∈ l, r ∈ graphPointListToFinset (X := X) (p :: l) := fun r hr =>
        (mem_graphPointListToFinset (X := X)).mpr (List.mem_cons_of_mem p hr)
      -- `D_1 = D_0 \ {π_1}`: erasing the head leaves the points of the tail.
      have herase : ∀ (inst : DecidableEq (IndexAugmented X)),
          @Finset.erase _ inst (graphPointListToFinset (X := X) (p :: l)) p =
            graphPointListToFinset (X := X) l := by
        intro inst
        ext r
        rw [Finset.mem_erase, mem_graphPointListToFinset, mem_graphPointListToFinset,
          List.mem_cons]
        constructor
        · rintro ⟨hrp, hr | hr⟩
          · exact absurd hr hrp
          · exact hr
        · intro hr
          exact ⟨fun hrp => hp_not_tail (hrp ▸ hr), Or.inr hr⟩
      set s := graphPointListToFinset (X := X) (p :: l) with hs_def
      have hmin := leastIndexValueMinimal_value_minimal (X := X) s hs
      have hidxle : ∀ r ∈ valueMinimalElements (X := X) s,
          IndexAugmented.index (leastIndexValueMinimal (X := X) s hs) ≤
            IndexAugmented.index r :=
        fun r hr => leastIndexValueMinimal_index_le (X := X) s hs hr
      have heqmin : ∀ r : IndexAugmented X, r ∈ valueMinimalElements (X := X) s →
          (∀ t ∈ valueMinimalElements (X := X) s,
            IndexAugmented.index r ≤ IndexAugmented.index t) →
          (∀ t ∈ s, IndexAugmented.index t = IndexAugmented.index r → t = r) →
          leastIndexValueMinimal (X := X) s hs = r :=
        fun r h1 h2 h3 => leastIndexValueMinimal_eq_of_index_min (X := X) s hs h1 h2 h3
      -- One step of the recursion: `π_1` is the least-index value-minimal point.
      rw [distinctFiniteSetSortListAux.eq_1, dif_pos hs]
      simp only [List.cons.injEq]
      generalize leastIndexValueMinimal (X := X) s hs = q at hmin hidxle heqmin ⊢
      constructor
      · -- "⊆": the selected head satisfies `A` and `B` against every later point.
        rintro ⟨rfl, htail⟩
        rw [herase] at htail
        refine List.pairwise_cons.mpr ⟨fun r hr => ?_, (ih hidx_tail).mp htail⟩
        have hr_s : r ∈ s := hl_s r hr
        refine ⟨not_lt.mp (hmin r hr_s), fun hlt heq => ?_⟩
        have hr_min : r ∈ valueMinimalElements (X := X) s := by
          rw [mem_valueMinimalElements_iff]
          refine ⟨hr_s, fun t ht hlt' => hmin t ht ?_⟩
          rw [heq]
          exact hlt'
        exact (not_lt.mpr (hidxle r hr_min)) hlt
      · -- "⊇": a list satisfying `A` and `B` has the selected point as its head.
        intro hpair
        obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
        have hqp : q = p := by
          refine heqmin p ?_ ?_ ?_
          · rw [mem_valueMinimalElements_iff]
            refine ⟨hp_s, fun t ht hlt => ?_⟩
            rcases hmem_s t ht with rfl | ht_l
            · exact lt_irrefl _ hlt
            · exact (not_lt.mpr (hhead t ht_l).1) hlt
          · intro t ht_min
            rw [mem_valueMinimalElements_iff] at ht_min
            obtain ⟨ht_s, ht_minimal⟩ := ht_min
            rcases hmem_s t ht_s with rfl | ht_l
            · exact le_rfl
            · rcases le_or_gt (IndexAugmented.index p) (IndexAugmented.index t) with hle | hlt
              · exact hle
              exfalso
              have hne := (hhead t ht_l).2 hlt
              have h1 : IndexAugmented.value p ≤ IndexAugmented.value t :=
                (hhead t ht_l).1
              have h2 : IndexAugmented.value t ≤ IndexAugmented.value p :=
                not_lt.mp (ht_minimal p hp_s)
              exact hne (le_antisymm h1 h2)
          · intro t ht_s hidx_eq
            rcases hmem_s t ht_s with rfl | ht_l
            · rfl
            · exfalso
              exact hp_idx (hidx_eq ▸ List.mem_map_of_mem ht_l)
        subst hqp
        refine ⟨rfl, ?_⟩
        rw [herase]
        exact (ih hidx_tail).mpr htail

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: the enumeration `(\pi(k), x(\pi(k)))_{k=1}^n` of the graph of
`x` used in the proof of `prop:minimal-sorting-measurable`.

Informal statement: the graph points of `x ∈ X^n` listed in the order
`\pi(1), …, \pi(n)`; `\pi^⪯(x) = \pi` means precisely that the greedy recursion
produces this list.
-/
def permutationGraphList {n : ℕ} (x : Fin n → X) (π : FinitePermutation n) :
    List (IndexAugmented X) :=
  List.ofFn fun k : Fin n => IndexAugmented.mk (π k).1 (x (π k))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: injectivity of `\pi` in the proof of
`prop:minimal-sorting-measurable`.

Informal statement: the original indices `\pi(1), …, \pi(n)` are pairwise
distinct.
-/
theorem nodup_map_index_permutationGraphList {n : ℕ} (x : Fin n → X)
    (π : FinitePermutation n) :
    ((permutationGraphList x π).map IndexAugmented.index).Nodup := by
  unfold permutationGraphList
  rw [List.map_ofFn, List.nodup_ofFn]
  intro a b hab
  simp only [Function.comp, IndexAugmented.index_mk] at hab
  exact π.injective (Fin.ext hab)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: reading `⋂_{k=1}^n (A^\pi_k ∩ B^\pi_k)` along the enumeration
`(\pi(k), x(\pi(k)))_k` in the proof of `prop:minimal-sorting-measurable`.

Informal statement: the graph list in `\pi`-order satisfies the cell conditions
position by position iff `x ∈ ⋂_k (A^\pi_k ∩ B^\pi_k)`.
-/
theorem pairwise_greedy_permutationGraphList_iff [LinearOrder X] {n : ℕ}
    (x : Fin n → X) (π : FinitePermutation n) :
    List.Pairwise (GreedyPairwiseStep (X := X)) (permutationGraphList x π) ↔
      x ∈ minimalPermutationCell (X := X) π := by
  rw [mem_minimalPermutationCell_iff, permutationGraphList, List.pairwise_ofFn]
  simp only [GreedyPairwiseStep, IndexAugmented.index_mk, IndexAugmented.value_mk,
    Fin.val_fin_lt]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3 (remark after
`defn:minimal-sort`); `2_chapter_market_representations.tex`,
`defn:comparability-components`.

Original label: single comparability component of a totally ordered tuple.

Informal statement: over a totally ordered set every two indices are
immediately comparable, hence connected, so all indices lie in one
comparability component.
-/
theorem indexSegment_eq_of_linearOrder [LinearOrder X] (x : Tuple X)
    (i j : Fin x.length) : indexSegment x i = indexSegment x j :=
  (indexConnected_iff_same_segment x i j).mp
    (indexConnected_of_indexComparable x (le_total _ _))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3 (remark after
`defn:minimal-sort`).

Original label: single comparability component of a totally ordered tuple,
membership form.

Informal statement: over a totally ordered set every index belongs to every
(hence the unique) comparability component.
-/
theorem mem_segmentIndices_of_linearOrder [LinearOrder X] (x : Tuple X)
    (i : Fin x.length) (K : ConnectedSegment x) : i ∈ segmentIndices x K := by
  induction K using Quotient.inductionOn with
  | h j => exact indexSegment_eq_of_linearOrder x i j

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3 (remark after
`defn:minimal-sort`).

Original label: single comparability component of a totally ordered tuple,
enumeration form.

Informal statement: for a totally ordered tuple with at least one entry, the
first-arrival list of comparability components is the one-element list.

Lean strategy / thesis relation note: the list is duplicate-free, every member
equals `K`, and `K` is a member; hence it is `[K]`.
-/
theorem segmentListByArrival_eq_singleton_of_linearOrder [LinearOrder X]
    (x : Tuple X) (K : ConnectedSegment x) :
    segmentListByArrival (X := X) x = [K] := by
  have hall : ∀ L ∈ segmentListByArrival (X := X) x, L = K := by
    intro L hL
    obtain ⟨i, rfl⟩ := (mem_segmentListByArrival_iff (X := X) x L).mp hL
    exact mem_segmentIndices_of_linearOrder x i K
  have hmem : K ∈ segmentListByArrival (X := X) x :=
    mem_segmentListByArrival (X := X) x K
  have hrep : segmentListByArrival (X := X) x =
      List.replicate (segmentListByArrival (X := X) x).length K :=
    List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  have hle : (segmentListByArrival (X := X) x).length ≤ 1 := by
    have hnd := nodup_segmentListByArrival (X := X) x
    rw [hrep] at hnd
    exact (List.nodup_replicate).mp hnd
  have hpos : 0 < (segmentListByArrival (X := X) x).length :=
    List.length_pos_of_mem hmem
  have h1 : (segmentListByArrival (X := X) x).length = 1 := le_antisymm hle hpos
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
  have haK : a = K := hall a (by rw [ha]; exact List.mem_singleton_self a)
  rw [ha, haK]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3 (remark after
`defn:minimal-sort`).

Original label: agreement of `defn:minimal-sort` with the Chapter 2 segmentwise
rule on a single comparability component.

Informal statement: for a totally ordered tuple, the Chapter 2 minimum sorting
graph list is the greedy least-index value-minimal recursion run once over the
whole graph of the tuple, i.e. the recursion `D_0, D_1, …` of
`defn:minimal-sort`.
-/
theorem minimumSortGraphList_eq_of_linearOrder [LinearOrder X] (x : Tuple X)
    (K : ConnectedSegment x) :
    minimumSortGraphList (X := X) x =
      distinctFiniteSetSortListAux (X := X)
        (toFinset (segmentDistinctFiniteSet x K).1) := by
  rw [minimumSortGraphList, minimumSortGraphBlocks,
    segmentListByArrival_eq_singleton_of_linearOrder x K]
  simp [distinctFiniteSetSortList]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `D_0 = \mathrm{domain}(x)` in `defn:minimal-sort`, in graph
form.

Informal statement: for a totally ordered tuple of length `n`, the (unique)
segment graph is the whole graph of `x`, which is the set of points of the
`\pi`-ordered enumeration `(\pi(k), x(\pi(k)))_{k=1}^n` for any permutation `\pi`.
-/
theorem toFinset_segmentDistinctFiniteSet_eq_permutationGraphList [LinearOrder X]
    {n : ℕ} (y : Fin n → X) (π : FinitePermutation n)
    (K : ConnectedSegment (⟨n, y⟩ : Tuple X)) :
    toFinset (segmentDistinctFiniteSet (⟨n, y⟩ : Tuple X) K).1 =
      graphPointListToFinset (X := X) (permutationGraphList y π) := by
  ext p
  rw [mem_toFinset, mem_segmentDistinctFiniteSet, mem_graphPointListToFinset,
    permutationGraphList, List.mem_ofFn]
  constructor
  · rintro ⟨i, _, rfl⟩
    refine ⟨π.symm i, ?_⟩
    simp [Tuple.entry]
  · rintro ⟨k, rfl⟩
    exact ⟨π k, mem_segmentIndices_of_linearOrder (⟨n, y⟩ : Tuple X) (π k) K, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `\pi^⪯(x)(k) = \pi_k` in `defn:minimal-sort`.

Informal statement: the `k`-th value of the minimal permutation is the original
index of the `k`-th selected graph point.
-/
theorem minimumSortPermutation_val_eq_index_graphList [Preorder X] {n : ℕ}
    (y : Fin n → X) (k : Fin n) :
    (minimumSortPermutation (X := X) (⟨n, y⟩ : Tuple X) k).1 =
      IndexAugmented.index
        ((minimumSortGraphList (X := X) (⟨n, y⟩ : Tuple X))[k.1]'
          (by rw [length_minimumSortGraphList]; exact k.2)) := by
  change ((minimumSortIndexList (X := X) (⟨n, y⟩ : Tuple X)).get
    (Fin.cast (length_minimumSortIndexList (X := X) (⟨n, y⟩ : Tuple X)).symm k)) = _
  simp [minimumSortIndexList, List.get_eq_getElem]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `\pi^⪯(x) = \pi` as a statement about the selected graph points,
in the proof of `prop:minimal-sorting-measurable`.

Informal statement: `\pi^⪯(x) = \pi` iff the greedy recursion selects the graph
points of `x` in the order `\pi(1), …, \pi(n)`.

Lean strategy / thesis relation note: both directions compare the two lists
position by position; the selected point at position `k` has index
`\pi^⪯(x)(k)` and value `x(\pi^⪯(x)(k))`.
-/
theorem minimumSortPermutation_eq_iff_graphList_eq [LinearOrder X] {n : ℕ}
    (y : Fin n → X) (π : FinitePermutation n) :
    minimumSortPermutation (X := X) (⟨n, y⟩ : Tuple X) = π ↔
      minimumSortGraphList (X := X) (⟨n, y⟩ : Tuple X) = permutationGraphList y π := by
  have hLlen : (minimumSortGraphList (X := X) (⟨n, y⟩ : Tuple X)).length = n :=
    length_minimumSortGraphList (X := X) _
  constructor
  · intro hπ
    unfold permutationGraphList
    apply List.ext_getElem
    · rw [hLlen, List.length_ofFn]
    · intro j hj₁ hj₂
      rw [List.getElem_ofFn]
      have hjn : j < n := by rw [← hLlen]; exact hj₁
      have hidx : IndexAugmented.index
          ((minimumSortGraphList (X := X) (⟨n, y⟩ : Tuple X))[j]) = (π ⟨j, hjn⟩).1 := by
        rw [← hπ]
        exact (minimumSortPermutation_val_eq_index_graphList y ⟨j, hjn⟩).symm
      apply IndexAugmented.ext
      · exact hidx
      · have hidx_lt : IndexAugmented.index
            ((minimumSortGraphList (X := X) (⟨n, y⟩ : Tuple X))[j]) < n := by
          rw [hidx]; exact (π ⟨j, hjn⟩).2
        have hv := minimumSortGraphList_get_value_eq_entry_index (X := X)
          (⟨n, y⟩ : Tuple X) ⟨j, hj₁⟩ hidx_lt
        have hfin : (⟨IndexAugmented.index
            ((minimumSortGraphList (X := X) (⟨n, y⟩ : Tuple X))[j]), hidx_lt⟩ : Fin n) =
              π ⟨j, hjn⟩ := Fin.ext hidx
        calc IndexAugmented.value ((minimumSortGraphList (X := X) (⟨n, y⟩ : Tuple X))[j])
            = y ⟨IndexAugmented.index
                ((minimumSortGraphList (X := X) (⟨n, y⟩ : Tuple X))[j]), hidx_lt⟩ := hv
          _ = y (π ⟨j, hjn⟩) := congrArg y hfin
  · intro hLeq
    ext k
    rw [minimumSortPermutation_val_eq_index_graphList y k]
    simp only [hLeq, permutationGraphList, List.getElem_ofFn, IndexAugmented.index_mk]
    rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `prop:minimal-sorting-measurable`, fibre identity
`𝒲_\pi = ⋂_{k=1}^n (A^\pi_k ∩ B^\pi_k)`.

Informal statement: for a tuple `x ∈ X^n` over a totally ordered set and a
permutation `\pi` of length `n`, `\pi^⪯(x) = \pi` iff
`x ∈ ⋂_{k=1}^n (A^\pi_k ∩ B^\pi_k)`: `\pi(k)` attains the `k`-th selected minimum
(`A^\pi_k`) and, among equal values, has the smallest original index (`B^\pi_k`).

Lean strategy / thesis relation note: this is the thesis argument. Over a
totally ordered set all entries lie in one comparability component
(`minimumSortGraphList_eq_of_linearOrder`), so the Chapter 2 rule is the
greedy recursion of `defn:minimal-sort` on the whole graph `D_0`;
`\pi^⪯(x) = \pi` means the recursion lists the graph in `\pi`-order
(`minimumSortPermutation_eq_iff_graphList_eq`), which by induction along the
recursion is equivalent to the cell conditions
(`distinctFiniteSetSortListAux_eq_iff_pairwise_greedy`,
`pairwise_greedy_permutationGraphList_iff`). The empty tuple is the trivial
case `n = 0`.
-/
theorem minimumSortPermutation_eq_iff_mem_cell [LinearOrder X] {n : ℕ}
    (y : Fin n → X) (π : FinitePermutation n) :
    minimumSortPermutation (X := X) (⟨n, y⟩ : Tuple X) = π ↔
      y ∈ minimalPermutationCell (X := X) π := by
  rw [minimumSortPermutation_eq_iff_graphList_eq,
    ← pairwise_greedy_permutationGraphList_iff,
    ← distinctFiniteSetSortListAux_eq_iff_pairwise_greedy _
      (nodup_map_index_permutationGraphList y π)]
  by_cases hn : n = 0
  · subst hn
    have h1 : minimumSortGraphList (X := X) (⟨0, y⟩ : Tuple X) = [] :=
      List.eq_nil_of_length_eq_zero (length_minimumSortGraphList (X := X) _)
    have h2 : permutationGraphList y π = [] :=
      List.eq_nil_of_length_eq_zero (by simp [permutationGraphList])
    have h3 : distinctFiniteSetSortListAux (X := X)
        (graphPointListToFinset (X := X) ([] : List (IndexAugmented X))) = [] := by
      rw [distinctFiniteSetSortListAux.eq_1]
      simp [graphPointListToFinset]
    rw [h1, h2, h3]
  · have hi : (0 : ℕ) < n := Nat.pos_of_ne_zero hn
    let K : ConnectedSegment (⟨n, y⟩ : Tuple X) := indexSegment _ ⟨0, hi⟩
    rw [minimumSortGraphList_eq_of_linearOrder _ K,
      toFinset_segmentDistinctFiniteSet_eq_permutationGraphList y π K]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: Borel measurability of `A^\pi_k` and `B^\pi_k` in the proof of
`prop:minimal-sorting-measurable`.

Informal statement: `⋂_{k=1}^n (A^\pi_k ∩ B^\pi_k)` is a Borel subset of `X^n`.

Lean strategy / thesis relation note: this is the thesis argument. Each
`\{x \mid x(\pi(k)) ⪯ x(j)\}` is closed because the order is closed
(`isClosed_le`, the thesis' closed set `\{(x,y) \mid x ≤ y\}`), and each
`\{x \mid x(\pi(k)) ≠ x(\pi(m))\}` is open because the diagonal is closed
(`isOpen_ne_fun`); `A^\pi_k`, `B^\pi_k` and `⋂_k (A^\pi_k ∩ B^\pi_k)` are finite
intersections of these, hence Borel. Stated for the Borel σ-algebra of the
product topology on `X^n`, which for `X = ℝ` is the usual Borel σ-algebra of
`ℝ^n`.
-/
theorem measurableSet_minimalPermutationCell {X : Type u} [LinearOrder X]
    [TopologicalSpace X] [OrderClosedTopology X] {n : ℕ} (π : FinitePermutation n) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      (minimalPermutationCell (X := X) π) := by
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  haveI : BorelSpace (Fin n → X) := ⟨rfl⟩
  refine MeasurableSet.iInter fun k => MeasurableSet.inter ?_ ?_
  · have hA : minimalSelectionCell (X := X) π k =
        ⋂ j : Fin n, ⋂ (_ : k ≤ j), {x : Fin n → X | x (π k) ≤ x (π j)} := by
      ext x; simp [minimalSelectionCell]
    rw [hA]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (isClosed_le (continuous_apply (π k)) (continuous_apply (π j))).measurableSet
  · have hB : minimalTieBreakCell (X := X) π k =
        ⋂ m : Fin n, ⋂ (_ : k < m), ⋂ (_ : π m < π k),
          {x : Fin n → X | x (π k) ≠ x (π m)} := by
      ext x; simp [minimalTieBreakCell]
    rw [hB]
    exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ =>
        (isOpen_ne_fun (continuous_apply (π k)) (continuous_apply (π m))).measurableSet

end MinimalPermutationCells

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `𝒲_\pi = \{x ∈ ℝ^{ℓ(\pi)} \mid \pi^⪯(x) = \pi\} ⊆ ℝ^{ℓ(\pi)}` in the
proof of `prop:minimal-sorting-measurable`, order `\leq`.

Informal statement: the fibre `(\pi^\le)^{-1}(\{\pi\})` consists of tuples of
length `ℓ(\pi)` only, and inside `ℝ^{ℓ(\pi)}` it is the finite intersection
`⋂_{k=1}^{ℓ(\pi)} (A^\pi_k ∩ B^\pi_k)`.
-/
theorem realMinimalPermutationLE_preimage_singleton {n : ℕ} (π : FinitePermutation n) :
    realMinimalPermutationLE ⁻¹' {(⟨n, π⟩ : FinitePermutations)} =
      (fun x : Fin n → ℝ => (Sigma.mk n x : Tuple ℝ)) ''
        minimalPermutationCell (X := ℝ) π := by
  ext ⟨m, y⟩
  constructor
  · intro h
    have h' : (⟨m, minimumSortPermutation (X := ℝ) (⟨m, y⟩ : Tuple ℝ)⟩ :
        FinitePermutations) = ⟨n, π⟩ := h
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h'
    exact ⟨y, (minimumSortPermutation_eq_iff_mem_cell y π).mp (eq_of_heq hh), rfl⟩
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hzx
    obtain rfl := eq_of_heq hh
    change (⟨n, minimumSortPermutation (X := ℝ) (⟨n, z⟩ : Tuple ℝ)⟩ :
      FinitePermutations) = ⟨n, π⟩
    rw [(minimumSortPermutation_eq_iff_mem_cell z π).mpr hz]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `𝒲_\pi = \{x ∈ ℝ^{ℓ(\pi)} \mid \pi^⪯(x) = \pi\} ⊆ ℝ^{ℓ(\pi)}` in the
proof of `prop:minimal-sorting-measurable`, order `\geq`.

Informal statement: the fibre `(\pi^\ge)^{-1}(\{\pi\})` consists of tuples of
length `ℓ(\pi)` only, and inside `ℝ^{ℓ(\pi)}` it is the finite intersection
`⋂_{k=1}^{ℓ(\pi)} (A^\pi_k ∩ B^\pi_k)` for `⪯ = ≥`.

Lean strategy / thesis relation note: `⪯ = ≥` is the order `≤` of `OrderDual ℝ`,
so the cells are those of `OrderDual ℝ`, pulled back along the coordinatewise
identification `x ↦ (\mathrm{toDual}(x(i)))_i` of `ℝ^n` with `(ℝ^{op})^n`.
-/
theorem realMinimalPermutationGE_preimage_singleton {n : ℕ} (π : FinitePermutation n) :
    realMinimalPermutationGE ⁻¹' {(⟨n, π⟩ : FinitePermutations)} =
      (fun x : Fin n → ℝ => (Sigma.mk n x : Tuple ℝ)) ''
        ((fun x : Fin n → ℝ => fun i => OrderDual.toDual (x i)) ⁻¹'
          minimalPermutationCell (X := OrderDual ℝ) π) := by
  ext ⟨m, y⟩
  constructor
  · intro h
    have h' : (⟨m, minimumSortPermutation (X := OrderDual ℝ)
        (⟨m, fun i => OrderDual.toDual (y i)⟩ : Tuple (OrderDual ℝ))⟩ :
        FinitePermutations) = ⟨n, π⟩ := h
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h'
    exact ⟨y, (minimumSortPermutation_eq_iff_mem_cell
      (fun i => OrderDual.toDual (y i)) π).mp (eq_of_heq hh), rfl⟩
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hzx
    obtain rfl := eq_of_heq hh
    change (⟨n, minimumSortPermutation (X := OrderDual ℝ)
      (⟨n, fun i => OrderDual.toDual (z i)⟩ : Tuple (OrderDual ℝ))⟩ :
      FinitePermutations) = ⟨n, π⟩
    rw [(minimumSortPermutation_eq_iff_mem_cell
      (fun i => OrderDual.toDual (z i)) π).mpr hz]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `prop:minimal-sorting-measurable`, order `\leq`.

Informal statement: the increasing real-valued minimal price sorting
permutation map is Borel measurable.

Lean strategy / thesis relation note: this is the thesis proof. Since
`\mathscr{P}` is countable (`prop:permutations-countable`,
`finitePermutations_countable`), every `B ⊆ \mathscr{P}` is the countable union
`⋃_{\pi ∈ B} \{\pi\}` of its singletons (so `\mathcal{B}(\mathscr{P})` is the
power set and no measurability hypothesis on `B` is needed), and it suffices
that each fibre `𝒲_\pi = (\pi^\le)^{-1}(\{\pi\})` is Borel. The fibre lies in
the layer `ℝ^{ℓ(\pi)}`, where it equals `⋂_{k=1}^{ℓ(\pi)} (A^\pi_k ∩ B^\pi_k)`
(`realMinimalPermutationLE_preimage_singleton`, built on the fibre identity
`minimumSortPermutation_eq_iff_mem_cell`); this finite intersection of closed
and open sets is Borel in `ℝ^{ℓ(\pi)}` (`measurableSet_minimalPermutationCell`)
and hence, by `lem:tuple-space-measurable-2` (`measurableSet_fixedLayer_image`),
Borel in `\mathscr{T}(ℝ)`.
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
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  haveI : Countable FinitePermutations := finitePermutations_countable
  change @Measurable (Tuple ℝ) FinitePermutations (tupleHausdorffBorel (X := ℝ))
    (@borel FinitePermutations finitePermutationMetricTopology) realMinimalPermutationLE
  intro B _hB
  -- `B = ⋃_{π ∈ B} {π}`, a countable union.
  rw [← Set.biUnion_preimage_singleton realMinimalPermutationLE B]
  refine MeasurableSet.biUnion (Set.to_countable B) fun σ _ => ?_
  rcases σ with ⟨n, π⟩
  -- The fibre `𝒲_π ⊆ ℝ^n` is `⋂_k (A^π_k ∩ B^π_k)`, Borel in `ℝ^n`, hence in `𝒯(ℝ)`.
  rw [realMinimalPermutationLE_preimage_singleton π]
  exact measurableSet_fixedLayer_image (measurableSet_minimalPermutationCell (X := ℝ) π)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: tuple-valued consequence of
`prop:minimal-sorting-measurable`.

Informal statement: the real increasing minimum-sort map is Borel measurable.

Lean strategy / thesis relation note: the proposition in the thesis is stated
for the permutation-valued map `\pi^\preceq`. The tuple-valued map is
`x ↦ x[\pi^\le(x)]` (`realMinimumSortLE_eq_permutationMap`), which is Borel
measurable because `\pi^\le` is (`prop:minimal-sorting-measurable`) and
`(x,\pi) ↦ x[\pi]` is continuous (`prop:permuting-continuous`,
`measurable_permutationMap_comp`), exactly as in the thesis paragraph after
`prop:minimal-sorting-measurable`.
-/
theorem measurable_minimumSort_real_LE :
    @Measurable (Tuple ℝ) (Tuple ℝ)
      (tupleHausdorffBorel (X := ℝ)) (tupleHausdorffBorel (X := ℝ))
      (minimumSort (X := ℝ)) := by
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  have h := measurable_permutationMap_comp (α := Tuple ℝ) (X := ℝ)
    (f := id) (π := realMinimalPermutationLE) measurable_id
    measurable_realMinimalPermutationLE
  have hfun : (fun a : Tuple ℝ => permutationMap (id a) (realMinimalPermutationLE a)) =
      minimumSort (X := ℝ) := by
    funext a
    exact (realMinimumSortLE_eq_permutationMap a).symm
  rw [hfun] at h
  exact h

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 3.

Original label: `prop:minimal-sorting-measurable`, order `\geq`.

Informal statement: the decreasing real-valued minimal price sorting
permutation map is Borel measurable.

Lean strategy / thesis relation note: this is the thesis proof for `⪯ = ≥`,
with the same structure as the `\leq` case. Since `\mathscr{P}` is countable
(`prop:permutations-countable`), every `B ⊆ \mathscr{P}` is the countable union
of its singletons and it suffices that each fibre `(\pi^\ge)^{-1}(\{\pi\})` is
Borel. The fibre lies in `ℝ^{ℓ(\pi)}` and equals
`⋂_{k=1}^{ℓ(\pi)} (A^\pi_k ∩ B^\pi_k)` for `⪯ = ≥`
(`realMinimalPermutationGE_preimage_singleton`, via the fibre identity
`minimumSortPermutation_eq_iff_mem_cell` over `OrderDual ℝ`). The cells for
`≥` are the `OrderDual ℝ` cells pulled back along the continuous coordinatewise
identification `ℝ^n ≅ (ℝ^{op})^n`; they are Borel by
`measurableSet_minimalPermutationCell` (closed order relation, closed diagonal),
and `lem:tuple-space-measurable-2` (`measurableSet_fixedLayer_image`) transports
the fibre to `\mathscr{T}(ℝ)`.
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
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  haveI : Countable FinitePermutations := finitePermutations_countable
  change @Measurable (Tuple ℝ) FinitePermutations (tupleHausdorffBorel (X := ℝ))
    (@borel FinitePermutations finitePermutationMetricTopology) realMinimalPermutationGE
  intro B _hB
  -- `B = ⋃_{π ∈ B} {π}`, a countable union.
  rw [← Set.biUnion_preimage_singleton realMinimalPermutationGE B]
  refine MeasurableSet.biUnion (Set.to_countable B) fun σ _ => ?_
  rcases σ with ⟨n, π⟩
  -- The fibre `𝒲_π ⊆ ℝ^n` is the `≥`-cell, Borel in `ℝ^n`, hence in `𝒯(ℝ)`.
  rw [realMinimalPermutationGE_preimage_singleton π]
  refine measurableSet_fixedLayer_image ?_
  letI : MeasurableSpace (Fin n → ℝ) := @borel (Fin n → ℝ) inferInstance
  haveI : BorelSpace (Fin n → ℝ) := ⟨rfl⟩
  letI : MeasurableSpace (Fin n → OrderDual ℝ) := @borel (Fin n → OrderDual ℝ) inferInstance
  haveI : BorelSpace (Fin n → OrderDual ℝ) := ⟨rfl⟩
  have hcont : Continuous (fun x : Fin n → ℝ => fun i => OrderDual.toDual (x i)) :=
    continuous_pi fun i => continuous_toDual.comp (continuous_apply i)
  exact hcont.measurable (measurableSet_minimalPermutationCell (X := OrderDual ℝ) π)

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
