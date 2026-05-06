import Foundations.MarketClearing.Sorting

/-!
# Market Clearing: Aggregation and Equilibrium Quantity

Blueprint module for
`1 - theoretical foundations/4_market_clearing.tex`,
clearing procedure steps 4--5.

Planned formal content:

* cumulative summation continuity;
* feasible equilibrium index map `eq:index-mapping`;
* `thm:index-measurable`;
* `lem:increasing-decreasing-measurable`;
* `lem:bounded-sets-measurable`;
* measurability of the equilibrium quantity map.
-/

namespace Thesis
namespace Foundations
namespace MarketClearing
namespace Equilibrium

open Thesis.Foundations.MarketRepresentation
open Thesis.Foundations.MarketRepresentation.FiniteSets
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
open Thesis.Foundations.MarketRepresentation.TuplesMeasurableSorting
open Thesis.Foundations.MarketActions.Analytic
open Thesis.Foundations.MarketClearing.Sorting

/-! ## Step 4: Aggregation by Cumulative Quantities -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 4,
`lem:cumulative-summation-continuous`.

Original label: definition of the cumulative summation function
`\bm{\Sigma}`.

Informal statement: for a tuple of nonnegative quantities, return the tuple
whose `i`th entry is the cumulative sum of all entries with index `j ≤ i`.

Lean strategy / thesis relation note: the thesis writes indices as `1,\dots,n`; Lean uses zero-based
`Fin n`, so the formula is written as a finite sum over `j ≤ i`.
-/
noncomputable def cumulativeQuantityTuple
    (x : Tuple Quantity) : Tuple Quantity :=
  Sigma.mk x.length
    (fun i : Fin x.length =>
      ∑ j : Fin x.length, if j ≤ i then Tuple.entry x j else 0)

/-- The cumulative summation map preserves tuple length. -/
@[simp]
theorem cumulativeQuantityTuple_length (x : Tuple Quantity) :
    (cumulativeQuantityTuple x).length = x.length :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 4,
proof of `lem:cumulative-summation-continuous`.

Original label: fixed-length matrix map `S_n`.

Informal statement: on a fixed length `n`, cumulative summation is continuous.

Lean strategy / thesis relation note: this is the lower-triangular matrix from the thesis, expressed
coordinatewise as finite sums of continuous coordinate projections.
-/
theorem continuous_fixedLength_cumulativeQuantityTuple (n : ℕ) :
    letI : TopologicalSpace (Tuple Quantity) :=
      tupleHausdorffMetricTopology (X := Quantity)
    @Continuous (Fin n → Quantity) (Tuple Quantity) inferInstance
      (tupleHausdorffMetricTopology (X := Quantity))
      (fun x : Fin n → Quantity =>
        cumulativeQuantityTuple (Sigma.mk n x : Tuple Quantity)) := by
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  change @Continuous (Fin n → Quantity) (Tuple Quantity) inferInstance
    (tupleHausdorffMetricTopology (X := Quantity))
    (fun x : Fin n → Quantity =>
      Sigma.mk n
        (fun i : Fin n => ∑ j : Fin n, if j ≤ i then x j else 0))
  rw [tupleHausdorffMetricTopology_eq_sigma]
  have hcoord : Continuous
      (fun x : Fin n → Quantity =>
        fun i : Fin n => ∑ j : Fin n, if j ≤ i then x j else 0) := by
    exact continuous_pi fun i =>
      continuous_finset_sum Finset.univ (fun j _ => by
        by_cases hji : j ≤ i
        · simpa [hji] using
            (continuous_apply (A := fun _ : Fin n => Quantity) j)
        · simpa [hji] using
            (continuous_const :
              Continuous fun _ : Fin n → Quantity => (0 : Quantity)))
  letI : TopologicalSpace (Tuple Quantity) := instTopologicalSpaceSigma
  exact continuous_sigmaMk.comp hcoord

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 4.

Original label: `lem:cumulative-summation-continuous`.

Informal statement: cumulative summation is continuous on the Hausdorff tuple
space over `[0,\infty)`.

Lean strategy / thesis relation note: this follows the thesis exactly: prove the fixed-length
matrix/finite-sum map is continuous for each `n`, then use the Chapter 2
standard machinery for tuple spaces as disjoint unions of fixed-length layers.
-/
theorem continuous_cumulativeQuantityTuple :
    @Continuous (Tuple Quantity) (Tuple Quantity)
      (tupleHausdorffMetricTopology (X := Quantity))
      (tupleHausdorffMetricTopology (X := Quantity))
      cumulativeQuantityTuple := by
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  rw [continuous_tupleHausdorff_iff_fixedLength]
  intro n
  exact continuous_fixedLength_cumulativeQuantityTuple n

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 4.

Original label: measurable consequence of
`lem:cumulative-summation-continuous`.

Informal statement: cumulative summation is Borel measurable on nonnegative
quantity tuple space.
-/
theorem measurable_cumulativeQuantityTuple :
    @Measurable (Tuple Quantity) (Tuple Quantity)
      (tupleHausdorffBorel (X := Quantity))
      (tupleHausdorffBorel (X := Quantity))
      cumulativeQuantityTuple := by
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  letI : OpensMeasurableSpace (Tuple Quantity) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple Quantity) := ⟨rfl⟩
  exact continuous_cumulativeQuantityTuple.measurable

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 4.

Original label: `\bm{Q}^{\bm{b}} = \bm{\Sigma}(\bm{q}^{\bm{b}})`.

Informal statement: aggregate sorted buy quantities by cumulative summation.
-/
noncomputable def cumulativeBuyQuantityTuple
    (m : MarketTuple) : Tuple Quantity :=
  cumulativeQuantityTuple (sortedBuyQuantityTuple m)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 4.

Original label: `\bm{Q}^{\bm{s}} = \bm{\Sigma}(\bm{q}^{\bm{s}})`.

Informal statement: aggregate sorted sell quantities by cumulative summation.
-/
noncomputable def cumulativeSellQuantityTuple
    (m : MarketTuple) : Tuple Quantity :=
  cumulativeQuantityTuple (sortedSellQuantityTuple m)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 4.

Original label: Step 4 measurability of `\bm{Q}^{\bm{b}}`.

Informal statement: aggregated buy quantities are Borel measurable as a
function of the market tuple.

Lean strategy / thesis relation note: the thesis says the cumulative map itself is continuous. Since
the preceding price-based sorting map is only measurable in general, the
market-to-aggregated-quantity composite is recorded as measurable.
-/
theorem measurable_cumulativeBuyQuantityTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple Quantity)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := Quantity))
      cumulativeBuyQuantityTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  exact measurable_cumulativeQuantityTuple.comp
    measurable_sortedBuyQuantityTuple

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 4.

Original label: Step 4 measurability of `\bm{Q}^{\bm{s}}`.

Informal statement: aggregated sell quantities are Borel measurable as a
function of the market tuple.
-/
theorem measurable_cumulativeSellQuantityTuple :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple (Tuple Quantity)
      (tupleHausdorffBorel (X := MarketOrder))
      (tupleHausdorffBorel (X := Quantity))
      cumulativeSellQuantityTuple := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  exact measurable_cumulativeQuantityTuple.comp
    measurable_sortedSellQuantityTuple

/-! ## Step 5: Feasible Equilibrium Index Sets -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`thm:index-measurable`.

Original label: auxiliary fixed-layer coordinate map for
`thm:index-measurable`.

Informal statement: read a tuple as an element of the fixed product
`\mathbb{R}^n`; if its length is not `n`, return the zero vector.

Lean strategy / thesis relation note: the thesis works directly on the fixed layer
`\mathbb{R}^n`. Lean packages all tuple lengths in one Sigma type, so this
totalized map is a convenient way to restrict the global tuple space back to
one fixed layer while keeping a total function.
-/
noncomputable def tupleFixedRealCoordinates (n : ℕ)
    (x : Tuple ℝ) : Fin n → ℝ :=
  if h : x.length = n then h ▸ x.2 else 0

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`thm:index-measurable`.

Original label: auxiliary fixed-layer reconstruction for
`thm:index-measurable`.

Informal statement: on the length-`n` layer, the totalized fixed-coordinate
map reconstructs the original tuple.
-/
theorem sigmaMk_tupleFixedRealCoordinates_eq_of_length
    {n : ℕ} {x : Tuple ℝ} (hx : x.length = n) :
    (Sigma.mk n (tupleFixedRealCoordinates n x) : Tuple ℝ) = x := by
  rcases x with ⟨k, x⟩
  dsimp [Tuple.length] at hx
  subst n
  simp [tupleFixedRealCoordinates, Tuple.length]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`thm:index-measurable`.

Original label: auxiliary fixed-layer measurability for
`thm:index-measurable`.

Informal statement: the totalized coordinate map
`\mathscr{T}(\mathbb{R}) \to \mathbb{R}^n` is Borel measurable.

Lean strategy / thesis relation note: this is the tuple-space pasting lemma from Chapter 2 applied
to a map whose fixed-length restrictions are either the identity/cast branch
or a constant zero branch.
-/
theorem measurable_tupleFixedRealCoordinates (n : ℕ) :
    @Measurable (Tuple ℝ) (Fin n → ℝ)
      (tupleHausdorffBorel (X := ℝ)) (@borel (Fin n → ℝ) inferInstance)
      (tupleFixedRealCoordinates n) := by
  letI : MeasurableSpace (Fin n → ℝ) := @borel (Fin n → ℝ) inferInstance
  rw [measurable_tupleHausdorff_iff_fixedLength]
  intro k
  by_cases hk : k = n
  · subst k
    simpa [tupleFixedRealCoordinates, Tuple.length] using
      (measurable_id :
        @Measurable (Fin n → ℝ) (Fin n → ℝ)
          (@borel (Fin n → ℝ) inferInstance)
          (@borel (Fin n → ℝ) inferInstance) id)
  · have hconst :
        (fun x : Fin k → ℝ =>
          tupleFixedRealCoordinates n (Sigma.mk k x : Tuple ℝ)) =
          fun _ => (0 : Fin n → ℝ) := by
      funext x
      simp [tupleFixedRealCoordinates, Tuple.length, hk]
    rw [hconst]
    exact measurable_const

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`thm:index-measurable`.

Original label: auxiliary length-cell measurability for
`thm:index-measurable`.

Informal statement: the set of real tuples of a fixed length is Borel.
-/
theorem measurableSet_tupleReal_length_eq (n : ℕ) :
    @MeasurableSet (Tuple ℝ) (tupleHausdorffBorel (X := ℝ))
      {x : Tuple ℝ | x.length = n} := by
  rw [measurableSet_tupleHausdorff_iff_fixedLength]
  intro k
  by_cases hk : k = n
  · subst k
    simp [Tuple.length]
  · simp [Tuple.length, hk]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `eq:index-mapping`.

Informal statement: given a sell-price tuple and a buy-price tuple, return the
finite set of feasible index pairs `(i,j)` for which the sell price is at most
the buy price.

Lean strategy / thesis relation note: the thesis writes
`\mathrm{domain}(\bm{p}^s) \times \mathrm{domain}(\bm{p}^b)` with
one-based indices. Lean uses zero-based natural indices and carries the
domain proofs `i < length` and `j < length` explicitly.
-/
noncomputable def feasibleEquilibriumIndexSet
    (ps pb : Tuple ℝ) : FiniteSubsets (ℕ × ℕ) := by
  classical
  refine ⟨{ij : ℕ × ℕ |
    ∃ hi : ij.1 < ps.length, ∃ hj : ij.2 < pb.length,
      Tuple.entry ps ⟨ij.1, hi⟩ ≤ Tuple.entry pb ⟨ij.2, hj⟩}, ?_⟩
  let rectangle : Set (ℕ × ℕ) :=
    (fun p : Fin ps.length × Fin pb.length => (p.1.1, p.2.1)) '' Set.univ
  have hrect_finite : rectangle.Finite :=
    (Set.finite_univ :
      (Set.univ : Set (Fin ps.length × Fin pb.length)).Finite).image _
  apply hrect_finite.subset
  intro ij hij
  rcases hij with ⟨hi, hj, _hprice⟩
  exact ⟨(⟨ij.1, hi⟩, ⟨ij.2, hj⟩), trivial, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `eq:index-mapping`, membership form.

Informal statement: an index pair belongs to the feasible equilibrium index
set exactly when both indices are in the respective tuple domains and the
sell price is at most the buy price.
-/
@[simp]
theorem mem_feasibleEquilibriumIndexSet (ps pb : Tuple ℝ) {ij : ℕ × ℕ} :
    ij ∈ (feasibleEquilibriumIndexSet ps pb : Set (ℕ × ℕ)) ↔
      ∃ hi : ij.1 < ps.length, ∃ hj : ij.2 < pb.length,
        Tuple.entry ps ⟨ij.1, hi⟩ ≤ Tuple.entry pb ⟨ij.2, hj⟩ :=
  Iff.rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: restricted sorted sell-price domain `S(\mathbb{R},\leq)`.

Informal statement: increasing real tuples are the sell-price tuples in the
domain of the thesis feasible-index map.

Lean strategy / thesis relation note: the thesis writes the sorted tuple space as
`\mathscr{S}(\mathbb{R},\leq)`. Lean represents it as a subtype of the
ambient tuple space carrying the proof of `IsSorted`.
-/
def IsIncreasingRealTuple (x : Tuple ℝ) : Prop :=
  IsSorted x

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: restricted sorted buy-price domain `S(\mathbb{R},\geq)`.

Informal statement: decreasing real tuples are represented by saying their
order-dual tuple is increasing.

Lean strategy / thesis relation note: this keeps the carrier as `Tuple ℝ`, matching the thesis
notation, while using `OrderDual ℝ` for the formal decreasing-order predicate.
-/
def IsDecreasingRealTuple (x : Tuple ℝ) : Prop :=
  IsSorted (dualizeRealTuple x)

/-- The thesis domain `S(\mathbb{R},\leq)` as a subtype of real tuples. -/
abbrev IncreasingRealTuples : Type :=
  {x : Tuple ℝ // IsIncreasingRealTuple x}

/-- The thesis domain `S(\mathbb{R},\geq)` as a subtype of real tuples. -/
abbrev DecreasingRealTuples : Type :=
  {x : Tuple ℝ // IsDecreasingRealTuple x}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: restricted-domain form of `eq:index-mapping`.

Informal statement: the feasible-index map restricted to sorted sell and buy
price tuples.
-/
noncomputable def feasibleEquilibriumIndexSet_restricted
    (state : IncreasingRealTuples × DecreasingRealTuples) :
    FiniteSubsets (ℕ × ℕ) :=
  feasibleEquilibriumIndexSet state.1.1 state.2.1

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `lem:increasing-decreasing-measurable`, set `I_n`.

Informal statement: the fixed-length region of increasing real tuples.

Lean strategy / thesis relation note: the thesis writes `x_1 ≤ ... ≤ x_n`. Lean uses `Fin n`, so
the statement is monotonicity with respect to the finite index order.
-/
def increasingRealFixedSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i j : Fin n, i ≤ j → x i ≤ x j}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `lem:increasing-decreasing-measurable`, set `D_n`.

Informal statement: the fixed-length region of decreasing real tuples.
-/
def decreasingRealFixedSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i j : Fin n, i ≤ j → x j ≤ x i}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `lem:increasing-decreasing-measurable`, increasing part.

Informal statement: for every fixed length `n`, the set of increasing real
tuples is Borel measurable.

Lean strategy / thesis relation note: the thesis uses adjacent coordinate differences
`\Delta_{i,i-1}`. Lean proves the same Borel fact as a finite intersection
over all ordered index pairs `i ≤ j`; this is equivalent to the displayed
chain condition and keeps the proof uniform for `n = 0` and `n = 1`.
-/
theorem measurableSet_increasingRealFixedSet (n : ℕ) :
    @MeasurableSet (Fin n → ℝ) (@borel (Fin n → ℝ) inferInstance)
      (increasingRealFixedSet n) := by
  letI : MeasurableSpace (Fin n → ℝ) := @borel (Fin n → ℝ) inferInstance
  letI : BorelSpace (Fin n → ℝ) := ⟨rfl⟩
  let cell : Fin n × Fin n → Set (Fin n → ℝ) := fun p =>
    if h : p.1 ≤ p.2 then {x | x p.1 ≤ x p.2} else Set.univ
  have hcell : ∀ p, MeasurableSet (cell p) := by
    intro p
    by_cases hp : p.1 ≤ p.2
    · have hle : MeasurableSet ({x : Fin n → ℝ | x p.1 ≤ x p.2}) := by
        exact (isClosed_le (continuous_apply p.1)
          (continuous_apply p.2)).measurableSet
      simpa [cell, hp] using hle
    · simp [cell, hp]
  have hset : increasingRealFixedSet n = ⋂ p : Fin n × Fin n, cell p := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iInter]
      intro p
      by_cases hp : p.1 ≤ p.2
      · simpa [cell, hp] using hx p.1 p.2 hp
      · simp [cell, hp]
    · intro hx i j hij
      have hp := Set.mem_iInter.mp hx (i, j)
      simpa [cell, hij] using hp
  rw [hset]
  exact MeasurableSet.iInter hcell

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `lem:increasing-decreasing-measurable`, decreasing part.

Informal statement: for every fixed length `n`, the set of decreasing real
tuples is Borel measurable.
-/
theorem measurableSet_decreasingRealFixedSet (n : ℕ) :
    @MeasurableSet (Fin n → ℝ) (@borel (Fin n → ℝ) inferInstance)
      (decreasingRealFixedSet n) := by
  letI : MeasurableSpace (Fin n → ℝ) := @borel (Fin n → ℝ) inferInstance
  letI : BorelSpace (Fin n → ℝ) := ⟨rfl⟩
  let cell : Fin n × Fin n → Set (Fin n → ℝ) := fun p =>
    if h : p.1 ≤ p.2 then {x | x p.2 ≤ x p.1} else Set.univ
  have hcell : ∀ p, MeasurableSet (cell p) := by
    intro p
    by_cases hp : p.1 ≤ p.2
    · have hle : MeasurableSet ({x : Fin n → ℝ | x p.2 ≤ x p.1}) := by
        exact (isClosed_le (continuous_apply p.2)
          (continuous_apply p.1)).measurableSet
      simpa [cell, hp] using hle
    · simp [cell, hp]
  have hset : decreasingRealFixedSet n = ⋂ p : Fin n × Fin n, cell p := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iInter]
      intro p
      by_cases hp : p.1 ≤ p.2
      · simpa [cell, hp] using hx p.1 p.2 hp
      · simp [cell, hp]
    · intro hx i j hij
      have hp := Set.mem_iInter.mp hx (i, j)
      simpa [cell, hij] using hp
  rw [hset]
  exact MeasurableSet.iInter hcell

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `lem:bounded-sets-measurable`, set `L^{i,j}_{n,m}`.

Informal statement: inside increasing sell prices and decreasing buy prices,
the cell where `p^s_i ≤ p^b_j` is Borel.
-/
def feasibleComparisonCell (n m : ℕ) (i : Fin n) (j : Fin m) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {z | z.1 ∈ increasingRealFixedSet n ∧
    z.2 ∈ decreasingRealFixedSet m ∧ z.1 i ≤ z.2 j}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `lem:bounded-sets-measurable`, set `G^{i,j}_{n,m}`.

Informal statement: inside increasing sell prices and decreasing buy prices,
the complementary strict cell where `p^s_i > p^b_j` is Borel.
-/
def infeasibleComparisonCell (n m : ℕ) (i : Fin n) (j : Fin m) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {z | z.1 ∈ increasingRealFixedSet n ∧
    z.2 ∈ decreasingRealFixedSet m ∧ z.2 j < z.1 i}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `lem:bounded-sets-measurable`, feasible cell.

Informal statement: the fixed-length feasible comparison cell is Borel
measurable.
-/
theorem measurableSet_feasibleComparisonCell
    {n m : ℕ} (i : Fin n) (j : Fin m) :
    @MeasurableSet ((Fin n → ℝ) × (Fin m → ℝ))
      (@borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance)
      (feasibleComparisonCell n m i j) := by
  letI : MeasurableSpace ((Fin n → ℝ) × (Fin m → ℝ)) :=
    @borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance
  letI : MeasurableSpace (Fin n → ℝ) := @borel (Fin n → ℝ) inferInstance
  letI : MeasurableSpace (Fin m → ℝ) := @borel (Fin m → ℝ) inferInstance
  letI : OpensMeasurableSpace ((Fin n → ℝ) × (Fin m → ℝ)) := ⟨le_rfl⟩
  letI : BorelSpace ((Fin n → ℝ) × (Fin m → ℝ)) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Fin n → ℝ) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → ℝ) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Fin m → ℝ) := ⟨le_rfl⟩
  letI : BorelSpace (Fin m → ℝ) := ⟨rfl⟩
  have hfst : @Measurable ((Fin n → ℝ) × (Fin m → ℝ)) (Fin n → ℝ)
      (@borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance)
      (@borel (Fin n → ℝ) inferInstance) Prod.fst :=
    continuous_fst.measurable
  have hsnd : @Measurable ((Fin n → ℝ) × (Fin m → ℝ)) (Fin m → ℝ)
      (@borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance)
      (@borel (Fin m → ℝ) inferInstance) Prod.snd :=
    continuous_snd.measurable
  have hI : MeasurableSet ({z : (Fin n → ℝ) × (Fin m → ℝ) |
      z.1 ∈ increasingRealFixedSet n}) :=
    (measurableSet_increasingRealFixedSet n).preimage hfst
  have hD : MeasurableSet ({z : (Fin n → ℝ) × (Fin m → ℝ) |
      z.2 ∈ decreasingRealFixedSet m}) :=
    (measurableSet_decreasingRealFixedSet m).preimage hsnd
  have hle : MeasurableSet
      ({z : (Fin n → ℝ) × (Fin m → ℝ) | z.1 i ≤ z.2 j}) := by
    exact (isClosed_le
      ((continuous_apply (A := fun _ : Fin n => ℝ) i).comp continuous_fst)
      ((continuous_apply (A := fun _ : Fin m => ℝ) j).comp
        continuous_snd)).measurableSet
  change MeasurableSet ({z : (Fin n → ℝ) × (Fin m → ℝ) |
      z.1 ∈ increasingRealFixedSet n} ∩
      ({z : (Fin n → ℝ) × (Fin m → ℝ) |
        z.2 ∈ decreasingRealFixedSet m} ∩
        {z : (Fin n → ℝ) × (Fin m → ℝ) | z.1 i ≤ z.2 j}))
  exact hI.inter (hD.inter hle)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `lem:bounded-sets-measurable`, strict complement cell.

Informal statement: the fixed-length infeasible strict comparison cell is
Borel measurable.
-/
theorem measurableSet_infeasibleComparisonCell
    {n m : ℕ} (i : Fin n) (j : Fin m) :
    @MeasurableSet ((Fin n → ℝ) × (Fin m → ℝ))
      (@borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance)
      (infeasibleComparisonCell n m i j) := by
  letI : MeasurableSpace ((Fin n → ℝ) × (Fin m → ℝ)) :=
    @borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance
  letI : MeasurableSpace (Fin n → ℝ) := @borel (Fin n → ℝ) inferInstance
  letI : MeasurableSpace (Fin m → ℝ) := @borel (Fin m → ℝ) inferInstance
  letI : OpensMeasurableSpace ((Fin n → ℝ) × (Fin m → ℝ)) := ⟨le_rfl⟩
  letI : BorelSpace ((Fin n → ℝ) × (Fin m → ℝ)) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Fin n → ℝ) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → ℝ) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Fin m → ℝ) := ⟨le_rfl⟩
  letI : BorelSpace (Fin m → ℝ) := ⟨rfl⟩
  have hfst : @Measurable ((Fin n → ℝ) × (Fin m → ℝ)) (Fin n → ℝ)
      (@borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance)
      (@borel (Fin n → ℝ) inferInstance) Prod.fst :=
    continuous_fst.measurable
  have hsnd : @Measurable ((Fin n → ℝ) × (Fin m → ℝ)) (Fin m → ℝ)
      (@borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance)
      (@borel (Fin m → ℝ) inferInstance) Prod.snd :=
    continuous_snd.measurable
  have hI : MeasurableSet ({z : (Fin n → ℝ) × (Fin m → ℝ) |
      z.1 ∈ increasingRealFixedSet n}) :=
    (measurableSet_increasingRealFixedSet n).preimage hfst
  have hD : MeasurableSet ({z : (Fin n → ℝ) × (Fin m → ℝ) |
      z.2 ∈ decreasingRealFixedSet m}) :=
    (measurableSet_decreasingRealFixedSet m).preimage hsnd
  have hle : MeasurableSet
      ({z : (Fin n → ℝ) × (Fin m → ℝ) | z.1 i ≤ z.2 j}) := by
    exact (isClosed_le
      ((continuous_apply (A := fun _ : Fin n => ℝ) i).comp continuous_fst)
      ((continuous_apply (A := fun _ : Fin m => ℝ) j).comp
        continuous_snd)).measurableSet
  have hlt : MeasurableSet
      ({z : (Fin n → ℝ) × (Fin m → ℝ) | z.2 j < z.1 i}) := by
    simpa [Set.compl_setOf, not_le] using hle.compl
  change MeasurableSet ({z : (Fin n → ℝ) × (Fin m → ℝ) |
      z.1 ∈ increasingRealFixedSet n} ∩
      ({z : (Fin n → ℝ) × (Fin m → ℝ) |
        z.2 ∈ decreasingRealFixedSet m} ∩
        {z : (Fin n → ℝ) × (Fin m → ℝ) | z.2 j < z.1 i}))
  exact hI.inter (hD.inter hlt)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`thm:index-measurable`.

Original label: fixed-length fiber step for `thm:index-measurable`.

Informal statement: for fixed lengths `n,m`, the fiber where the feasible
index map equals a prescribed finite set `eta` is Borel in
`\mathbb{R}^n \times \mathbb{R}^m`.

Lean strategy / thesis relation note: this formalizes the thesis' finite-intersection argument. If
`eta` contains a pair outside `{0,...,n-1} × {0,...,m-1}`, the fiber is empty.
Otherwise it is the intersection, over all in-domain pairs, of either the
closed half-space `p^s_i ≤ p^b_j` or its Borel complement.
-/
theorem measurableSet_fixedLength_feasibleEquilibriumIndexSet_fiber
    (n m : ℕ) (eta : FiniteSubsets (ℕ × ℕ)) :
    @MeasurableSet ((Fin n → ℝ) × (Fin m → ℝ))
      (@borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance)
      {z | feasibleEquilibriumIndexSet
          (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ) = eta} := by
  classical
  letI : MeasurableSpace ((Fin n → ℝ) × (Fin m → ℝ)) :=
    @borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance
  letI : BorelSpace ((Fin n → ℝ) × (Fin m → ℝ)) := ⟨rfl⟩
  let rectangle : Set (ℕ × ℕ) := {ij | ij.1 < n ∧ ij.2 < m}
  let cell : Fin n × Fin m → Set ((Fin n → ℝ) × (Fin m → ℝ)) := fun p =>
    if (p.1.1, p.2.1) ∈ (eta : Set (ℕ × ℕ)) then
      {z | z.1 p.1 ≤ z.2 p.2}
    else
      {z | z.2 p.2 < z.1 p.1}
  have hcell_meas : ∀ p, MeasurableSet (cell p) := by
    intro p
    have hle : MeasurableSet
        ({z : (Fin n → ℝ) × (Fin m → ℝ) | z.1 p.1 ≤ z.2 p.2}) := by
      exact (isClosed_le
        ((continuous_apply (A := fun _ : Fin n => ℝ) p.1).comp continuous_fst)
        ((continuous_apply (A := fun _ : Fin m => ℝ) p.2).comp
          continuous_snd)).measurableSet
    have hlt : MeasurableSet
        ({z : (Fin n → ℝ) × (Fin m → ℝ) | z.2 p.2 < z.1 p.1}) := by
      simpa [Set.compl_setOf, not_le] using hle.compl
    by_cases hp : (p.1.1, p.2.1) ∈ (eta : Set (ℕ × ℕ))
    · simpa [cell, hp] using hle
    · simpa [cell, hp] using hlt
  by_cases heta_domain : (eta : Set (ℕ × ℕ)) ⊆ rectangle
  · have hfiber :
        {z : (Fin n → ℝ) × (Fin m → ℝ) |
            feasibleEquilibriumIndexSet
              (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ) = eta} =
          ⋂ p : Fin n × Fin m, cell p := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_iInter]
        intro p
        by_cases hpeta : (p.1.1, p.2.1) ∈ (eta : Set (ℕ × ℕ))
        · have hpfeas : (p.1.1, p.2.1) ∈
              (feasibleEquilibriumIndexSet
                (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ) :
                Set (ℕ × ℕ)) := by
            change (p.1.1, p.2.1) ∈
              (feasibleEquilibriumIndexSet
                (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ) :
                Set (ℕ × ℕ))
            rw [hz]
            exact hpeta
          rcases (mem_feasibleEquilibriumIndexSet
              (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ)).mp
              hpfeas with
            ⟨hi, hj, hprice⟩
          simpa [cell, hpeta, Tuple.entry] using hprice
        · have hlt : z.2 p.2 < z.1 p.1 := by
            have hnot : ¬ z.1 p.1 ≤ z.2 p.2 := by
              intro hle
              have hpfeas : (p.1.1, p.2.1) ∈
                  (feasibleEquilibriumIndexSet
                    (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ) :
                    Set (ℕ × ℕ)) := by
                exact (mem_feasibleEquilibriumIndexSet
                  (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ)).mpr
                  ⟨p.1.2, p.2.2, by simpa [Tuple.entry] using hle⟩
              have hpeta' : (p.1.1, p.2.1) ∈ (eta : Set (ℕ × ℕ)) := by
                change (p.1.1, p.2.1) ∈ (eta : Set (ℕ × ℕ))
                rw [← hz]
                exact hpfeas
              exact hpeta hpeta'
            exact lt_of_not_ge hnot
          simpa [cell, hpeta] using hlt
      · intro hzcell
        apply Subtype.ext
        ext ij
        constructor
        · intro hij
          rcases (mem_feasibleEquilibriumIndexSet
              (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ)).mp
              hij with
            ⟨hi, hj, hprice⟩
          let p : Fin n × Fin m := (⟨ij.1, hi⟩, ⟨ij.2, hj⟩)
          have hcellp : z ∈ cell p := by
            exact Set.mem_iInter.mp hzcell p
          by_cases hpeta : (p.1.1, p.2.1) ∈ (eta : Set (ℕ × ℕ))
          · simpa [p] using hpeta
          · have hlt : z.2 p.2 < z.1 p.1 := by
              simpa [cell, hpeta] using hcellp
            exact False.elim
              ((not_le_of_gt hlt) (by simpa [p, Tuple.entry] using hprice))
        · intro hijeta
          have hijrect : ij ∈ rectangle := heta_domain hijeta
          rcases hijrect with ⟨hi, hj⟩
          let p : Fin n × Fin m := (⟨ij.1, hi⟩, ⟨ij.2, hj⟩)
          have hcellp : z ∈ cell p := Set.mem_iInter.mp hzcell p
          by_cases hpeta : (p.1.1, p.2.1) ∈ (eta : Set (ℕ × ℕ))
          · have hprice : z.1 p.1 ≤ z.2 p.2 := by
              simpa [cell, hpeta] using hcellp
            exact (mem_feasibleEquilibriumIndexSet
              (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ)).mpr
              ⟨hi, hj, by simpa [p, Tuple.entry] using hprice⟩
          · exact False.elim (hpeta (by simpa [p] using hijeta))
    rw [hfiber]
    exact MeasurableSet.iInter hcell_meas
  · have hfiber_empty :
        {z : (Fin n → ℝ) × (Fin m → ℝ) |
            feasibleEquilibriumIndexSet
              (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ) = eta} =
          ∅ := by
      ext z
      constructor
      · intro hz
        exfalso
        rcases Set.not_subset.mp heta_domain with ⟨ij, hijeta, hijnot⟩
        have hijfeas : ij ∈
            (feasibleEquilibriumIndexSet
              (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ) :
              Set (ℕ × ℕ)) := by
          change ij ∈
            (feasibleEquilibriumIndexSet
              (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ) :
              Set (ℕ × ℕ))
          rw [hz]
          exact hijeta
        rcases (mem_feasibleEquilibriumIndexSet
            (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ)).mp
            hijfeas with
          ⟨hi, hj, _hprice⟩
        exact hijnot ⟨hi, hj⟩
      · intro hz
        simp at hz
    rw [hfiber_empty]
    exact MeasurableSet.empty

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`thm:index-measurable`.

Original label: fixed-length measurable component of `thm:index-measurable`.

Informal statement: on each fixed product layer
`\mathbb{R}^n \times \mathbb{R}^m`, the feasible equilibrium index map is
Borel measurable.

Lean strategy / thesis relation note: this is the fixed-dimensional part of the thesis proof before
the final tuple-space pasting step.
-/
theorem measurable_fixedLength_feasibleEquilibriumIndexSet
    (n m : ℕ) :
    @Measurable ((Fin n → ℝ) × (Fin m → ℝ)) (FiniteSubsets (ℕ × ℕ))
      (@borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance)
      (emetricBorel (FiniteSubsets (ℕ × ℕ)))
      (fun z => feasibleEquilibriumIndexSet
        (Sigma.mk n z.1 : Tuple ℝ) (Sigma.mk m z.2 : Tuple ℝ)) := by
  classical
  letI : MeasurableSpace ((Fin n → ℝ) × (Fin m → ℝ)) :=
    @borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance
  letI : MeasurableSpace (FiniteSubsets (ℕ × ℕ)) :=
    emetricBorel (FiniteSubsets (ℕ × ℕ))
  haveI : Countable (FiniteSubsets (ℕ × ℕ)) := FiniteSubsets.countable
  exact measurable_to_countable' (fun eta =>
    measurableSet_fixedLength_feasibleEquilibriumIndexSet_fiber n m eta)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `thm:index-measurable`.

Informal statement: the feasible equilibrium index map is Borel measurable
on the product of sell-price and buy-price tuple spaces.

Lean strategy / thesis relation note: the thesis proves this by decomposing the tuple spaces into
the countable family of fixed-dimensional layers
`\mathbb{R}^n \times \mathbb{R}^m`, proving measurability on each layer, and
pasting. Lean follows that strategy by writing each singleton fiber as a
countable union over `(n,m)` of fixed-layer fibers.
-/
theorem measurable_feasibleEquilibriumIndexSet :
    letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
    @Measurable ((Tuple ℝ) × (Tuple ℝ)) (FiniteSubsets (ℕ × ℕ))
      inferInstance (emetricBorel (FiniteSubsets (ℕ × ℕ)))
      (fun z => feasibleEquilibriumIndexSet z.1 z.2) := by
  classical
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  letI : MeasurableSpace (FiniteSubsets (ℕ × ℕ)) :=
    emetricBorel (FiniteSubsets (ℕ × ℕ))
  haveI : Countable (FiniteSubsets (ℕ × ℕ)) := FiniteSubsets.countable
  refine measurable_to_countable' (fun eta => ?_)
  let layerFiber : ℕ × ℕ → Set ((Tuple ℝ) × (Tuple ℝ)) := fun nm =>
    {z |
      z.1.length = nm.1 ∧ z.2.length = nm.2 ∧
        feasibleEquilibriumIndexSet
          (Sigma.mk nm.1 (tupleFixedRealCoordinates nm.1 z.1) : Tuple ℝ)
          (Sigma.mk nm.2 (tupleFixedRealCoordinates nm.2 z.2) : Tuple ℝ) = eta}
  have hlayer_meas : ∀ nm : ℕ × ℕ, MeasurableSet (layerFiber nm) := by
    intro nm
    let n := nm.1
    let m := nm.2
    have hlen_sell : MeasurableSet
        {z : (Tuple ℝ) × (Tuple ℝ) | z.1.length = n} :=
      (measurableSet_tupleReal_length_eq n).preimage measurable_fst
    have hlen_buy : MeasurableSet
        {z : (Tuple ℝ) × (Tuple ℝ) | z.2.length = m} :=
      (measurableSet_tupleReal_length_eq m).preimage measurable_snd
    have hfixed : MeasurableSet
        {z : (Tuple ℝ) × (Tuple ℝ) |
          feasibleEquilibriumIndexSet
            (Sigma.mk n (tupleFixedRealCoordinates n z.1) : Tuple ℝ)
            (Sigma.mk m (tupleFixedRealCoordinates m z.2) : Tuple ℝ) = eta} := by
      letI : MeasurableSpace (Fin n → ℝ) := @borel (Fin n → ℝ) inferInstance
      letI : MeasurableSpace (Fin m → ℝ) := @borel (Fin m → ℝ) inferInstance
      haveI : BorelSpace (Fin n → ℝ) := ⟨rfl⟩
      haveI : BorelSpace (Fin m → ℝ) := ⟨rfl⟩
      have hcoord :
          @Measurable ((Tuple ℝ) × (Tuple ℝ))
            ((Fin n → ℝ) × (Fin m → ℝ))
            inferInstance inferInstance
            (fun z => (tupleFixedRealCoordinates n z.1,
              tupleFixedRealCoordinates m z.2)) :=
        ((measurable_tupleFixedRealCoordinates n).comp measurable_fst).prodMk
          ((measurable_tupleFixedRealCoordinates m).comp measurable_snd)
      have hfiber : @MeasurableSet ((Fin n → ℝ) × (Fin m → ℝ))
          inferInstance
          {w |
            feasibleEquilibriumIndexSet
              (Sigma.mk n w.1 : Tuple ℝ)
              (Sigma.mk m w.2 : Tuple ℝ) = eta} := by
        have hB :
            (inferInstance :
              MeasurableSpace ((Fin n → ℝ) × (Fin m → ℝ))) =
              @borel ((Fin n → ℝ) × (Fin m → ℝ)) inferInstance :=
          BorelSpace.measurable_eq
        rw [hB]
        exact measurableSet_fixedLength_feasibleEquilibriumIndexSet_fiber n m eta
      exact hfiber.preimage hcoord
    change MeasurableSet
      ({z : (Tuple ℝ) × (Tuple ℝ) | z.1.length = n} ∩
        ({z : (Tuple ℝ) × (Tuple ℝ) | z.2.length = m} ∩
          {z : (Tuple ℝ) × (Tuple ℝ) |
          feasibleEquilibriumIndexSet
            (Sigma.mk n (tupleFixedRealCoordinates n z.1) : Tuple ℝ)
            (Sigma.mk m (tupleFixedRealCoordinates m z.2) : Tuple ℝ) = eta}))
    exact hlen_sell.inter (hlen_buy.inter hfixed)
  have hfiber :
      {z : (Tuple ℝ) × (Tuple ℝ) |
        feasibleEquilibriumIndexSet z.1 z.2 = eta} =
        ⋃ nm : ℕ × ℕ, layerFiber nm := by
    ext z
    constructor
    · intro hz
      refine Set.mem_iUnion.2 ⟨(z.1.length, z.2.length), ?_⟩
      refine ⟨rfl, rfl, ?_⟩
      simpa [
        sigmaMk_tupleFixedRealCoordinates_eq_of_length (x := z.1) rfl,
        sigmaMk_tupleFixedRealCoordinates_eq_of_length (x := z.2) rfl] using hz
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨nm, hnm⟩
      rcases hnm with ⟨hlen_sell, hlen_buy, hfixed⟩
      have hs :
          (Sigma.mk nm.1 (tupleFixedRealCoordinates nm.1 z.1) : Tuple ℝ) =
            z.1 :=
        sigmaMk_tupleFixedRealCoordinates_eq_of_length hlen_sell
      have hb :
          (Sigma.mk nm.2 (tupleFixedRealCoordinates nm.2 z.2) : Tuple ℝ) =
            z.2 :=
        sigmaMk_tupleFixedRealCoordinates_eq_of_length hlen_buy
      simpa [hs, hb] using hfixed
  change MeasurableSet
    {z : (Tuple ℝ) × (Tuple ℝ) | feasibleEquilibriumIndexSet z.1 z.2 = eta}
  rw [hfiber]
  exact MeasurableSet.iUnion hlayer_meas

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: restricted-domain wrapper for `thm:index-measurable`.

Informal statement: the feasible-index map is measurable on the thesis
domain `S(\mathbb{R},\leq) × S(\mathbb{R},\geq)`.

Lean strategy / thesis strategy note: the substantial fixed-layer singleton-fiber proof is the
ambient theorem `measurable_feasibleEquilibriumIndexSet`. This wrapper is the
subspace restriction that matches the theorem's displayed domain.
-/
theorem measurable_feasibleEquilibriumIndexSet_restricted :
    letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
    @Measurable (IncreasingRealTuples × DecreasingRealTuples)
      (FiniteSubsets (ℕ × ℕ)) inferInstance
      (emetricBorel (FiniteSubsets (ℕ × ℕ)))
      feasibleEquilibriumIndexSet_restricted := by
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  letI : MeasurableSpace (FiniteSubsets (ℕ × ℕ)) :=
    emetricBorel (FiniteSubsets (ℕ × ℕ))
  have hpair :
      @Measurable (IncreasingRealTuples × DecreasingRealTuples)
        ((Tuple ℝ) × (Tuple ℝ)) inferInstance inferInstance
        (fun state => ((state.1 : Tuple ℝ), (state.2 : Tuple ℝ))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)
  simpa [feasibleEquilibriumIndexSet_restricted] using
    measurable_feasibleEquilibriumIndexSet.comp hpair

/-! ## Step 5: Equilibrium Quantity -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5,
proof of `thm:equilibrium-quantity-measurable`.

Original label: auxiliary coordinate evaluation `ev_i`.

Informal statement: read the `i`th coordinate of a quantity tuple, returning
`0` when `i` is outside the tuple domain.

Lean strategy / thesis relation note: the thesis defines `ev_i` on the tuple domain and says it is
naturally continuous in the standard tuple machinery. Lean makes this a total
map by assigning the harmless value `0` off the fixed-length layer where the
coordinate exists.
-/
noncomputable def tupleQuantityEval (i : ℕ)
    (x : Tuple Quantity) : Quantity :=
  if h : i < x.length then Tuple.entry x ⟨i, h⟩ else 0

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5,
proof of `thm:equilibrium-quantity-measurable`.

Original label: continuity of auxiliary coordinate evaluation `ev_i`.

Informal statement: each totalized quantity-coordinate evaluation is
continuous on the tuple Hausdorff topology.

Lean strategy / thesis relation note: this is exactly the tuple-space pasting argument from the
thesis: on each fixed-length component the map is either a coordinate
projection or the constant zero map.
-/
theorem continuous_tupleQuantityEval (i : ℕ) :
    @Continuous (Tuple Quantity) Quantity
      (tupleHausdorffMetricTopology (X := Quantity)) inferInstance
      (tupleQuantityEval i) := by
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  rw [continuous_tupleHausdorff_iff_fixedLength]
  intro n
  by_cases hi : i < n
  · simpa [tupleQuantityEval, Tuple.length, Tuple.entry, hi] using
      (continuous_apply (A := fun _ : Fin n => Quantity) ⟨i, hi⟩)
  · have hconst :
        (fun x : Fin n → Quantity =>
          tupleQuantityEval i (Sigma.mk n x : Tuple Quantity)) =
        fun _ => (0 : Quantity) := by
      funext x
      simp [tupleQuantityEval, Tuple.length, hi]
    rw [hconst]
    exact continuous_const

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5,
proof of `thm:equilibrium-quantity-measurable`.

Original label: measurability of auxiliary coordinate evaluation `ev_i`.

Informal statement: each totalized quantity-coordinate evaluation is Borel
measurable.
-/
theorem measurable_tupleQuantityEval (i : ℕ) :
    @Measurable (Tuple Quantity) Quantity
      (tupleHausdorffBorel (X := Quantity)) inferInstance
      (tupleQuantityEval i) := by
  letI : TopologicalSpace (Tuple Quantity) :=
    tupleHausdorffMetricTopology (X := Quantity)
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  letI : OpensMeasurableSpace (Tuple Quantity) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple Quantity) := ⟨rfl⟩
  exact (continuous_tupleQuantityEval i).measurable

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5,
definition preceding `thm:equilibrium-quantity-measurable`.

Original label: potential quantity `min(Q^s_i,Q^b_j)`.

Informal statement: for a feasible sell/buy index pair, the candidate cleared
quantity is the smaller of cumulative sell and buy quantities.
-/
noncomputable def clearedQuantityAt
    (Qs Qb : Tuple Quantity) (ij : ℕ × ℕ) : Quantity :=
  min (tupleQuantityEval ij.1 Qs) (tupleQuantityEval ij.2 Qb)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5,
definition preceding `thm:equilibrium-quantity-measurable`.

Original label: local quantity map `m_eta`.

Informal statement: on a fixed feasible-index cell `eta`, take the maximum of
the candidate quantities `min(Q^s_i,Q^b_j)` over `(i,j) in eta`.

Lean strategy / thesis relation note: the thesis writes a separate `0` case when `eta` is empty.
`Finset.sup` over `ℝ≥0` has bottom value `0`, so the Lean definition is the
same case distinction packaged as a finite supremum.
-/
noncomputable def maxClearedQuantityForIndexSet
    (eta : FiniteSubsets (ℕ × ℕ))
    (Qs Qb : Tuple Quantity) : Quantity :=
  (FiniteSubsets.toFinset eta).sup (fun ij =>
    clearedQuantityAt Qs Qb ij)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5,
proof of `thm:equilibrium-quantity-measurable`.

Original label: measurability of the local map `m_eta`.

Informal statement: for a fixed finite feasible-index set `eta`, the map
`(Q^s,Q^b) ↦ max_{(i,j)∈eta} min(Q^s_i,Q^b_j)` is Borel measurable.

Lean strategy / thesis relation note: this is the thesis' finite composition of
measurable coordinate evaluations by continuous `min` and `max`.
-/
theorem measurable_maxClearedQuantityForIndexSet
    (eta : FiniteSubsets (ℕ × ℕ)) :
    letI : MeasurableSpace (Tuple Quantity) :=
      tupleHausdorffBorel (X := Quantity)
    @Measurable ((Tuple Quantity) × (Tuple Quantity)) Quantity
      inferInstance inferInstance
      (fun z => maxClearedQuantityForIndexSet eta z.1 z.2) := by
  classical
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  have hpoint : ∀ ij : ℕ × ℕ,
      @Measurable ((Tuple Quantity) × (Tuple Quantity)) Quantity
        inferInstance inferInstance
        (fun z => clearedQuantityAt z.1 z.2 ij) := by
    intro ij
    have hs :
        @Measurable ((Tuple Quantity) × (Tuple Quantity)) Quantity
          inferInstance inferInstance
          (fun z => tupleQuantityEval ij.1 z.1) :=
      (measurable_tupleQuantityEval ij.1).comp measurable_fst
    have hb :
        @Measurable ((Tuple Quantity) × (Tuple Quantity)) Quantity
          inferInstance inferInstance
          (fun z => tupleQuantityEval ij.2 z.2) :=
      (measurable_tupleQuantityEval ij.2).comp measurable_snd
    simpa [clearedQuantityAt] using hs.min hb
  let s : Finset (ℕ × ℕ) := FiniteSubsets.toFinset eta
  have hfinset : ∀ t : Finset (ℕ × ℕ),
      @Measurable ((Tuple Quantity) × (Tuple Quantity)) Quantity
        inferInstance inferInstance
        (fun z => t.sup (fun ij => clearedQuantityAt z.1 z.2 ij)) := by
    intro t
    refine Finset.induction_on t ?empty ?insert
    · exact
        (measurable_const :
          @Measurable ((Tuple Quantity) × (Tuple Quantity)) Quantity
            inferInstance inferInstance
            (fun _ => (0 : Quantity)))
    · intro ij t hij ht
      simpa [Finset.sup_insert, hij] using (hpoint ij).max ht
  simpa [maxClearedQuantityForIndexSet, s] using hfinset s

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: equilibrium quantity map `\mathscr{Q}`.

Informal statement: from sorted cumulative sell quantities/prices and sorted
cumulative buy quantities/prices, compute the maximum feasible cleared
quantity.

Lean strategy / thesis relation note: the thesis states this on
`C(≤) × C(≥)`, where quantity and price tuple lengths agree and prices are
already sorted. Lean first defines the same formula on the ambient product
`(Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ)` using total
coordinate evaluation; restricting this function to the thesis domain gives
the displayed `\mathscr{Q}`.
-/
noncomputable def equilibriumQuantity
    (state : (Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ)) :
    Quantity :=
  maxClearedQuantityForIndexSet
    (feasibleEquilibriumIndexSet state.1.2 state.2.2)
    state.1.1 state.2.1

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: sell-side clearing-state domain `C(\leq)`.

Informal statement: a sell-side clearing state consists of a cumulative
quantity tuple and an increasing price tuple with matching lengths.
-/
def IsIncreasingClearingState (state : Tuple Quantity × Tuple ℝ) : Prop :=
  state.1.length = state.2.length ∧ IsIncreasingRealTuple state.2

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: buy-side clearing-state domain `C(\geq)`.

Informal statement: a buy-side clearing state consists of a cumulative
quantity tuple and a decreasing price tuple with matching lengths.
-/
def IsDecreasingClearingState (state : Tuple Quantity × Tuple ℝ) : Prop :=
  state.1.length = state.2.length ∧ IsDecreasingRealTuple state.2

/-- The thesis domain `C(\leq)` as a subtype of quantity/price tuple pairs. -/
abbrev IncreasingClearingStates : Type :=
  {state : Tuple Quantity × Tuple ℝ // IsIncreasingClearingState state}

/-- The thesis domain `C(\geq)` as a subtype of quantity/price tuple pairs. -/
abbrev DecreasingClearingStates : Type :=
  {state : Tuple Quantity × Tuple ℝ // IsDecreasingClearingState state}

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: restricted-domain equilibrium quantity map
`\mathscr{Q} : C(\leq) \times C(\geq) \to [0,\infty)`.

Informal statement: restrict the ambient equilibrium quantity formula to the
sorted, length-compatible thesis domain.
-/
noncomputable def equilibriumQuantity_restricted
    (state : IncreasingClearingStates × DecreasingClearingStates) :
    Quantity :=
  equilibriumQuantity (state.1.1, state.2.1)

set_option maxHeartbeats 800000 in
-- The countable-pasting proof elaborates a nested product/Sigma source type
-- and finite-subset codomain; keep the larger budget scoped to this theorem.
/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: `thm:equilibrium-quantity-measurable`.

Informal statement: the equilibrium quantity map is Borel measurable.

Lean strategy / thesis relation note: this follows the thesis proof: the measurable feasible-index
map partitions the domain into countably many cells `I_eta`; on each cell the
equilibrium quantity is the fixed finite max/min expression `m_eta`; the
Chapter 2 countable pasting lemma then gives global measurability. As above,
the Lean statement is the ambient-product version whose restriction is the
thesis map on `C(≤) × C(≥)`.
-/
theorem measurable_equilibriumQuantity :
    letI : MeasurableSpace (Tuple Quantity) :=
      tupleHausdorffBorel (X := Quantity)
    letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
    @Measurable
      ((Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ))
      Quantity inferInstance inferInstance equilibriumQuantity := by
  classical
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  letI : MeasurableSpace (FiniteSubsets (ℕ × ℕ)) :=
    emetricBorel (FiniteSubsets (ℕ × ℕ))
  letI : TopologicalSpace (FiniteSubsets (ℕ × ℕ)) :=
    emetricTopology (FiniteSubsets (ℕ × ℕ))
  letI : OpensMeasurableSpace (FiniteSubsets (ℕ × ℕ)) := ⟨le_rfl⟩
  letI : BorelSpace (FiniteSubsets (ℕ × ℕ)) := ⟨rfl⟩
  haveI : Countable (FiniteSubsets (ℕ × ℕ)) := FiniteSubsets.countable
  let Source :=
    ((Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ))
  let S : FiniteSubsets (ℕ × ℕ) → Set Source := fun eta =>
    {state | feasibleEquilibriumIndexSet state.1.2 state.2.2 = eta}
  have hpricePair :
      @Measurable Source ((Tuple ℝ) × (Tuple ℝ))
        inferInstance inferInstance
        (fun state => (state.1.2, state.2.2)) :=
    (measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)
  have hindex :
      @Measurable Source (FiniteSubsets (ℕ × ℕ))
        inferInstance inferInstance
        (fun state => feasibleEquilibriumIndexSet state.1.2 state.2.2) :=
    measurable_feasibleEquilibriumIndexSet.comp hpricePair
  have hS : ∀ eta : FiniteSubsets (ℕ × ℕ), MeasurableSet (S eta) := by
    intro eta
    exact (measurableSet_singleton eta).preimage hindex
  have hcover : ⋃ eta : FiniteSubsets (ℕ × ℕ), S eta = Set.univ := by
    ext state
    constructor
    · intro _h
      trivial
    · intro _h
      exact Set.mem_iUnion.2
        ⟨feasibleEquilibriumIndexSet state.1.2 state.2.2, rfl⟩
  refine measurable_of_measurable_restrict_countable_cover
    (S := S) hS hcover ?_
  intro eta
  have hquantityPair :
      @Measurable (S eta) ((Tuple Quantity) × (Tuple Quantity))
        inferInstance inferInstance
        (fun x => ((x : Source).1.1, (x : Source).2.1)) :=
    ((measurable_fst.comp measurable_fst).comp measurable_subtype_coe).prodMk
      ((measurable_fst.comp measurable_snd).comp measurable_subtype_coe)
  have hlocal :
      @Measurable (S eta) Quantity inferInstance inferInstance
        (fun x => maxClearedQuantityForIndexSet eta
          (x : Source).1.1 (x : Source).2.1) :=
    (measurable_maxClearedQuantityForIndexSet eta).comp hquantityPair
  have hfun :
      (fun x : S eta => equilibriumQuantity x) =
        fun x : S eta => maxClearedQuantityForIndexSet eta
          (x : Source).1.1 (x : Source).2.1 := by
    funext x
    have hx :
        feasibleEquilibriumIndexSet (x : Source).1.2 (x : Source).2.2 =
          eta := x.2
    simp [equilibriumQuantity, hx]
  rw [hfun]
  exact hlocal

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: restricted-domain wrapper for
`thm:equilibrium-quantity-measurable`.

Informal statement: the equilibrium quantity map is measurable on
`C(\leq) × C(\geq)`.

Lean strategy / thesis strategy note: the countable-cell proof is the ambient theorem
`measurable_equilibriumQuantity`. This theorem packages the subspace
restriction whose domain is displayed in the thesis statement.
-/
theorem measurable_equilibriumQuantity_restricted :
    letI : MeasurableSpace (Tuple Quantity) :=
      tupleHausdorffBorel (X := Quantity)
    letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
    @Measurable
      (IncreasingClearingStates × DecreasingClearingStates)
      Quantity inferInstance inferInstance equilibriumQuantity_restricted := by
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  have hstate :
      @Measurable (IncreasingClearingStates × DecreasingClearingStates)
        ((Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ))
        inferInstance inferInstance
        (fun state =>
          ((state.1 : Tuple Quantity × Tuple ℝ),
            (state.2 : Tuple Quantity × Tuple ℝ))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)
  simpa [equilibriumQuantity_restricted] using
    measurable_equilibriumQuantity.comp hstate

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: market-level equilibrium quantity composite following
`thm:equilibrium-quantity-measurable`.

Informal statement: apply the clearing pipeline to a market tuple: separate
and sort buy/sell orders, aggregate cumulative quantities, then compute the
equilibrium quantity.

Lean strategy / thesis relation note: the theorem in the thesis isolates the final map on
`C(≤) × C(≥)`. This wrapper records the natural composite from raw market
tuples that the surrounding narrative uses.
-/
noncomputable def marketEquilibriumQuantity (m : MarketTuple) : Quantity :=
  equilibriumQuantity
    ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m),
      (cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m))

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, Step 5.

Original label: market-level measurable consequence of
`thm:equilibrium-quantity-measurable`.

Informal statement: the equilibrium quantity obtained from a raw market tuple
is Borel measurable.

Lean strategy / thesis relation note: this is the direct composition of the measurable Step 3 sorted
price/quantity maps, the measurable Step 4 cumulative quantity maps, and the
ambient-product version of `thm:equilibrium-quantity-measurable`.
-/
theorem measurable_marketEquilibriumQuantity :
    letI : EMetricSpace MarketOrder :=
      DisjointUnionTopology.disjointUnionEMetricSpace
        (X := MarketOrderPayload)
    @Measurable MarketTuple Quantity
      (tupleHausdorffBorel (X := MarketOrder)) inferInstance
      marketEquilibriumQuantity := by
  letI : EMetricSpace MarketOrder :=
    DisjointUnionTopology.disjointUnionEMetricSpace
      (X := MarketOrderPayload)
  letI : MeasurableSpace MarketTuple :=
    tupleHausdorffBorel (X := MarketOrder)
  letI : MeasurableSpace (Tuple Quantity) :=
    tupleHausdorffBorel (X := Quantity)
  letI : MeasurableSpace (Tuple ℝ) := tupleHausdorffBorel (X := ℝ)
  have hsell :
      @Measurable MarketTuple (Tuple Quantity × Tuple ℝ)
        inferInstance inferInstance
        (fun m => (cumulativeSellQuantityTuple m, sortedSellPriceTuple m)) :=
    measurable_cumulativeSellQuantityTuple.prod
      measurable_sortedSellPriceTuple
  have hbuy :
      @Measurable MarketTuple (Tuple Quantity × Tuple ℝ)
        inferInstance inferInstance
        (fun m => (cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m)) :=
    measurable_cumulativeBuyQuantityTuple.prod
      measurable_sortedBuyPriceTuple
  have hstate :
      @Measurable MarketTuple
        ((Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ))
        inferInstance inferInstance
        (fun m => ((cumulativeSellQuantityTuple m, sortedSellPriceTuple m),
          (cumulativeBuyQuantityTuple m, sortedBuyPriceTuple m))) :=
    hsell.prod hbuy
  have hQ :
      @Measurable
        ((Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ))
        Quantity inferInstance inferInstance equilibriumQuantity :=
    measurable_equilibriumQuantity
  exact hQ.comp hstate

end Equilibrium
end MarketClearing
end Foundations
end Thesis
