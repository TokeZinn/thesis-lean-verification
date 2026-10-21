import Thesis.Foundations.MarketClearing.MidpointPrice

/-!
Scope note (2026-10-20): this module proves the finite-level step-order
submodel. The current thesis uses interpolated piecewise-affine orders;
these results are supporting simple-curve lemmas, not the current
`prop:pl-encoding-measurable` or full market reconstruction.
 # The actual state-dependent price-impact construction

This module starts from tagged order tuples and the proved marginal-midpoint
clearing map. No measurable curve map is assumed as an input.
-/

noncomputable section
namespace Thesis.DayAhead.MarketImpact

open Set MeasureTheory
open Foundations.MarketRepresentation
open DisjointUnionTopology TuplesMetricTopology
open Foundations.MarketActions.Primitive Foundations.MarketActions.Analytic
open Foundations.MarketClearing.Sorting Foundations.MarketClearing.Equilibrium
open Foundations.MarketClearing.MidpointPrice

local instance : EMetricSpace MarketOrder := disjointUnionEMetricSpace
local instance : MeasurableSpace MarketOrder := borel _
local instance : BorelSpace MarketOrder := ⟨rfl⟩
local instance : MeasurableSpace MarketTuple := borel _
local instance : BorelSpace MarketTuple := ⟨rfl⟩

local instance (c : OrderField) : SecondCountableTopology (OrderFieldValue c) := by
  cases c
  · exact inferInstanceAs (SecondCountableTopology ℝ)
  · exact inferInstanceAs (SecondCountableTopology Quantity)

theorem market_topology_eq : tupleHausdorffMetricTopology (X := MarketOrder) =
    (inferInstance : TopologicalSpace MarketTuple) := by
  rw [tupleHausdorffMetricTopology_eq_sigma]
  exact congrArg (fun t : TopologicalSpace MarketOrder =>
    @instTopologicalSpaceSigma ℕ (fun n => Fin n → MarketOrder)
      (fun n => @Pi.topologicalSpace (Fin n) (fun _ => MarketOrder) (fun _ => t)))
    (metricTopology_eq_sigma (X := MarketOrderPayload))

theorem market_borel_eq : tupleHausdorffBorel (X := MarketOrder) =
    (inferInstance : MeasurableSpace MarketTuple) := by
  exact congrArg (fun t => @borel MarketTuple t) market_topology_eq

def orderSingleton (o : MarketOrder) : MarketTuple := ⟨1, fun _ => o⟩

theorem continuous_orderSingleton : Continuous orderSingleton := by
  exact continuous_sigmaMk.comp (continuous_pi fun _ => continuous_id)

theorem continuous_taggedOrder (side : OrderSide) :
    Continuous (fun x : ℝ × Quantity => (Sigma.mk side (mkLimitOrder x.1 x.2) : MarketOrder)) := by
  apply continuous_sigmaMk.comp
  apply continuous_pi
  intro c
  cases c
  · exact continuous_fst
  · exact continuous_snd

/-- Chapter 2 price-impact definition, lines 104–114.
Positive perturbations buy at the regime ceiling; negative perturbations sell
at the fixed floor. A zero perturbation retains the stated buy-side branch. -/
def extremeOrder (upper q : ℝ) : MarketOrder :=
  if 0 ≤ q then Sigma.mk OrderSide.buy (mkLimitOrder upper ⟨|q|, abs_nonneg q⟩)
  else Sigma.mk OrderSide.sell (mkLimitOrder (-500) ⟨|q|, abs_nonneg q⟩)

theorem measurable_extremeOrder (upper : ℝ) :
    @Measurable ℝ MarketOrder _ (borel _) (extremeOrder upper) := by
  letI : MeasurableSpace MarketOrder := borel _
  letI : BorelSpace MarketOrder := ⟨rfl⟩
  have hq : Continuous (fun q : ℝ => (⟨|q|, abs_nonneg q⟩ : Quantity)) :=
    continuous_abs.subtype_mk _
  exact ((continuous_taggedOrder OrderSide.buy).comp (continuous_const.prodMk hq)).measurable.ite
    (isClosed_le continuous_const continuous_id).measurableSet
    ((continuous_taggedOrder OrderSide.sell).comp (continuous_const.prodMk hq)).measurable

def adjoinExtreme (upper : ℝ) (x : MarketTuple × ℝ) : MarketTuple :=
  concat (orderSingleton (extremeOrder upper x.2)) x.1

theorem measurable_adjoinExtreme (upper : ℝ) : Measurable (adjoinExtreme upper) := by
  letI : MeasurableSpace MarketOrder := borel _
  letI : BorelSpace MarketOrder := ⟨rfl⟩
  have hc := continuous_concat_emetricTopology (X := MarketOrder)
  change @Continuous (MarketTuple × MarketTuple) MarketTuple
    (@instTopologicalSpaceProd MarketTuple MarketTuple
      (tupleHausdorffMetricTopology (X := MarketOrder))
      (tupleHausdorffMetricTopology (X := MarketOrder)))
    (tupleHausdorffMetricTopology (X := MarketOrder)) _ at hc
  rw [market_topology_eq] at hc
  exact hc.measurable.comp
    ((continuous_orderSingleton.measurable.comp
      ((measurable_extremeOrder upper).comp measurable_snd)).prodMk measurable_fst)

/-- The scalar impact price is evaluated by the actual separated, sorted,
cumulative marginal rule already used for the thesis equilibrium operator. -/
def impactPrice (upper : ℝ) (x : MarketTuple × ℝ) : ℝ :=
  marketMidpointPrice (adjoinExtreme upper x)

theorem measurable_impactPrice (upper : ℝ) : Measurable (impactPrice upper) := by
  have h := measurable_marketMidpointPrice
  rw [market_borel_eq] at h
  exact h.comp (measurable_adjoinExtreme upper)

def positiveStates : Set MarketTuple := {m | 0 < marketEquilibriumQuantity m}

/-- The positive-volume state domain in the Hilbert-curve proposition is Borel. -/
theorem measurableSet_positiveStates : MeasurableSet positiveStates := by
  have h := measurable_marketEquilibriumQuantity
  rw [market_borel_eq] at h
  exact measurableSet_lt measurable_const h

/-- The total available quantity on a side, before permutation. -/
def totalQuantity (x : Tuple Quantity) : ℝ := ∑ i : Fin x.1, (x.2 i : ℝ)

theorem continuous_totalQuantity : Continuous totalQuantity := by
  apply continuous_sigma
  intro n
  exact continuous_finset_sum Finset.univ fun i _ =>
    continuous_subtype_val.comp (continuous_apply i)

def buyDepth (m : MarketTuple) : ℝ := totalQuantity (buyQuantityTuple m)
def sellDepth (m : MarketTuple) : ℝ := totalQuantity (sellQuantityTuple m)
def depth (m : MarketTuple) : ℝ := max (buyDepth m) (sellDepth m)
def availableDepth (m : MarketTuple) : Set ℝ := Icc (-buyDepth m) (sellDepth m)

theorem continuous_buyDepth : Continuous buyDepth := by
  have h := continuous_buyQuantityTuple
  rw [market_topology_eq, tupleHausdorffMetricTopology_eq_sigma] at h
  exact continuous_totalQuantity.comp h

theorem continuous_sellDepth : Continuous sellDepth := by
  have h := continuous_sellQuantityTuple
  rw [market_topology_eq, tupleHausdorffMetricTopology_eq_sigma] at h
  exact continuous_totalQuantity.comp h

theorem continuous_depth : Continuous depth := continuous_buyDepth.max continuous_sellDepth

theorem totalQuantity_nonneg (x : Tuple Quantity) : 0 ≤ totalQuantity x :=
  Finset.sum_nonneg fun i _ => (x.2 i).coe_nonneg

/-- Original label: `claim:zero-is-contained`. -/
theorem zero_mem_availableDepth (m : MarketTuple) : 0 ∈ availableDepth m :=
  ⟨neg_nonpos.mpr (totalQuantity_nonneg _), totalQuantity_nonneg _⟩

/-- Original label: `claim:compact-dom`. -/
theorem isCompact_availableDepth (m : MarketTuple) : IsCompact (availableDepth m) := isCompact_Icc

theorem abs_le_depth {m : MarketTuple} {q : ℝ} (hq : q ∈ availableDepth m) :
    |q| ≤ depth m := by
  apply abs_le.mpr
  exact ⟨(neg_le_neg (le_max_left _ _)).trans hq.1, hq.2.trans (le_max_right _ _)⟩

def priceBounded (upper : ℝ) (m : MarketTuple) : Prop :=
  ∀ i : Fin m.1, orderPrice (m.2 i).2 ∈ Icc (-500) upper

theorem continuous_orderPrice : Continuous (fun o : MarketOrder => orderPrice o.2) := by
  apply continuous_sigma
  intro side
  exact continuous_apply OrderField.price

theorem isClosed_priceBounded (upper : ℝ) : IsClosed {m | priceBounded upper m} := by
  apply isClosed_sigma_iff.mpr
  intro n
  change IsClosed {x : Fin n → MarketOrder | ∀ i, orderPrice (x i).2 ∈ Icc (-500) upper}
  simp only [setOf_forall]
  exact isClosed_iInter fun i => isClosed_Icc.preimage
    (continuous_orderPrice.comp (continuous_apply i))

/-- The thesis's fixed-regime, positive-volume domain is a Borel subset of
the unrestricted order space used in the clearing implementation. -/
theorem measurableSet_regimePositiveStates (upper : ℝ) :
    MeasurableSet {m | priceBounded upper m ∧ m ∈ positiveStates} :=
  (isClosed_priceBounded upper).measurableSet.inter measurableSet_positiveStates

open Foundations.MarketClearing.Selection FiniteSets TuplesBasic TuplesMeasurableSorting

theorem separation_entry_exists (side : OrderSide) (m : MarketTuple)
    (i : Fin (separationComponent side m).1) :
    ∃ j : Fin m.1, Sigma.mk side ((separationComponent side m).2 i) = m.2 j := by
  let k := (pairing (separationIndexSet side m)).2 i
  have hk := (mem_separationIndexSet side m).mp
    (pairing_entry_mem (separationIndexSet side m) i)
  refine ⟨⟨k, hk.choose⟩, ?_⟩
  have ht : (m.2 ⟨k, hk.choose⟩).1 = side := hk.choose_spec
  change Sigma.mk side (valueAtTag side (m.2 ⟨k, hk.choose⟩) ht) = _
  generalize m.2 ⟨k, hk.choose⟩ = z at ht ⊢
  rcases z with ⟨a, z⟩
  cases ht
  rfl

theorem permutationMap_all {X : Type*} (p : X → Prop) (x : Tuple X)
    (π : FinitePermutations) (h : ∀ i, p (x.2 i)) :
    ∀ i, p ((permutationMap x π).2 i) := by
  by_cases hlen : x.length = π.1
  · rw [permutationMap, dif_pos hlen]
    exact fun i => h _
  · rw [permutationMap, dif_neg hlen]
    exact fun i => Fin.elim0 i

theorem sortedPrice_all (p : ℝ → Prop) (m : MarketTuple)
    (h : ∀ i, p (orderPrice (m.2 i).2)) :
    (∀ i, p ((sortedSellPriceTuple m).2 i)) ∧
      (∀ i, p ((sortedBuyPriceTuple m).2 i)) := by
  have hs (side : OrderSide) (i : Fin (separationComponent side m).1) :
      p (orderPrice ((separationComponent side m).2 i)) := by
    obtain ⟨j, hj⟩ := separation_entry_exists side m i
    have he := congrArg (fun o : MarketOrder => orderPrice o.2) hj
    change orderPrice ((separationComponent side m).2 i) = orderPrice (m.2 j).2 at he
    rw [he]
    exact h j
  exact ⟨permutationMap_all p _ _ (hs OrderSide.sell),
    permutationMap_all p _ _ (hs OrderSide.buy)⟩

/-- Actual clearing respects any common interval containing zero and all order prices. -/
theorem marketMidpointPrice_mem_Icc (lo hi : ℝ) (m : MarketTuple)
    (h0 : (0 : ℝ) ∈ Icc lo hi) (hm : ∀ i, orderPrice (m.2 i).2 ∈ Icc lo hi) :
    marketMidpointPrice m ∈ Icc lo hi := by
  by_cases hz : marketEquilibriumQuantity m = 0
  · simpa [marketMidpointPrice_zero hz] using h0
  obtain ⟨i, j, _, _, _, _, hi', hj', he⟩ :=
    marketMidpointPrice_positive_formula m (pos_iff_ne_zero.mpr hz)
  have hs := (sortedPrice_all (fun p => p ∈ Icc lo hi) m hm).1 ⟨i, hi'⟩
  have hb := (sortedPrice_all (fun p => p ∈ Icc lo hi) m hm).2 ⟨j, hj'⟩
  dsimp only [Tuple.length] at hi' hj'
  rw [he]
  simp only [tuplePriceEval, dif_pos hi', dif_pos hj']
  constructor <;> linarith [hs.1, hs.2, hb.1, hb.2]

theorem adjoinExtreme_all (p : ℝ → Prop) (upper : ℝ) (x : MarketTuple × ℝ)
    (hlo : p (-500)) (hhi : p upper) (hm : ∀ i, p (orderPrice (x.1.2 i).2)) :
    ∀ i, p (orderPrice ((adjoinExtreme upper x).2 i).2) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i
    dsimp only [adjoinExtreme, concat, Tuple.entry, Tuple.length, orderSingleton]
    rw [Fin.append_left]
    by_cases hq : 0 ≤ x.2
    · rw [extremeOrder, if_pos hq]
      exact hhi
    · rw [extremeOrder, if_neg hq]
      exact hlo
  · intro i
    dsimp only [adjoinExtreme, concat, Tuple.entry, Tuple.length, orderSingleton]
    rw [Fin.append_right]
    exact hm i

theorem impactPrice_mem_Icc (upper : ℝ) (hupper : 0 ≤ upper)
    (m : MarketTuple) (hm : priceBounded upper m) (q : ℝ) :
    impactPrice upper (m, q) ∈ Icc (-500) upper := by
  apply marketMidpointPrice_mem_Icc
  · exact ⟨by norm_num, hupper⟩
  · exact adjoinExtreme_all _ _ _ ⟨le_rfl, by linarith⟩
      ⟨by linarith, le_rfl⟩ hm

/-- All prices that can enter a marginal midpoint after an extreme order.
Zero is retained for the general clearing operator's zero-volume convention. -/
def candidatePrices (upper : ℝ) (m : MarketTuple) : Set ℝ :=
  insert 0 (insert (-500) (insert upper (Set.range fun i : Fin m.1 => orderPrice (m.2 i).2)))

def candidateMidpoints (upper : ℝ) (m : MarketTuple) : Set ℝ :=
  (fun p : ℝ × ℝ => (p.1 + p.2) / 2) '' (candidatePrices upper m ×ˢ candidatePrices upper m)

theorem candidateMidpoints_finite (upper : ℝ) (m : MarketTuple) :
    (candidateMidpoints upper m).Finite := by
  have h : (candidatePrices upper m).Finite :=
    ((Set.finite_range _).insert _ |>.insert _).insert _
  exact (h.prod h).image _

theorem impactPrice_mem_candidateMidpoints (upper : ℝ) (m : MarketTuple) (q : ℝ) :
    impactPrice upper (m, q) ∈ candidateMidpoints upper m := by
  have hz : (0 : ℝ) ∈ candidatePrices upper m := by simp [candidatePrices]
  by_cases hq : marketEquilibriumQuantity (adjoinExtreme upper (m, q)) = 0
  · refine ⟨(0, 0), ⟨hz, hz⟩, ?_⟩
    simp only [impactPrice, marketMidpointPrice_zero hq, add_zero, zero_div]
  obtain ⟨i, j, _, _, _, _, hi, hj, he⟩ :=
    marketMidpointPrice_positive_formula (adjoinExtreme upper (m, q)) (pos_iff_ne_zero.mpr hq)
  have hm : ∀ k, orderPrice ((adjoinExtreme upper (m, q)).2 k).2 ∈ candidatePrices upper m :=
    adjoinExtreme_all _ _ _ (by simp [candidatePrices]) (by simp [candidatePrices])
      (fun k => by simp [candidatePrices])
  have hs := sortedPrice_all (fun p => p ∈ candidatePrices upper m) _ hm
  refine ⟨((sortedSellPriceTuple (adjoinExtreme upper (m, q))).2 ⟨i, hi⟩,
    (sortedBuyPriceTuple (adjoinExtreme upper (m, q))).2 ⟨j, hj⟩),
    ⟨hs.1 _, hs.2 _⟩, ?_⟩
  dsimp only [Tuple.length] at hi hj
  change _ = marketMidpointPrice _
  rw [he, tuplePriceEval, dif_pos hi, tuplePriceEval, dif_pos hj]

/-- The actual market construction has only finitely many price levels.
This proves the finite-image part of `claim:pw-constant`; the interval-partition
claim additionally needs the monotonicity argument. -/
theorem impactPrice_finite_range (upper : ℝ) (m : MarketTuple) :
    (Set.range fun q => impactPrice upper (m, q)).Finite :=
  (candidateMidpoints_finite upper m).subset
    (Set.range_subset_iff.mpr (impactPrice_mem_candidateMidpoints upper m))

end Thesis.DayAhead.MarketImpact
