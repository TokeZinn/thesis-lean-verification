import Thesis.Context.ThesisContext
import Thesis.Foundations.MarketRepresentation.TupleSortingAlignment
import Thesis.Appendices.Analysis.BoundedMetric
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Data.Prod.Lex

/-! # Tuple topology: exact codomains and boundary examples

Thesis source: `1 - theoretical foundations/2_chapter_market_representations.tex`.
-/

namespace Thesis.Foundations.MarketRepresentation.TupleTopologyAlignment

open TuplesBasic TuplesSorting TuplesMetricTopology TuplesMeasurableSorting
open FiniteSets FiniteSets.FiniteSubsets
open Filter Topology

universe u

/-- Original label: `prop:truncated-metric-equivalent-topology`.
The source's extended-metric convention is allowed: truncation is an
ordinary finite metric with exactly the original topology. -/
theorem extended_truncation_same_topology (X : Type u) [EMetricSpace X] :
    ∃ m : MetricSpace X,
      (∀ x y : X, @edist X m.toEDist x y = min (edist x y) 1) ∧
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X) :=
  ⟨Preliminary.BoundedMetric.truncatedMetricSpace X, fun _ _ => rfl, rfl⟩

/-- Original label: `thm:tuple-space-properties`.
DA-046: the value alone does not determine an indexed graph point.
The proof of `thm:tuple-space-properties` must instead fix the index. -/
theorem tuple_graph_value_not_injective {X : Type u} (a : X) :
    ¬ Set.InjOn IndexAugmented.value
      ((graph (⟨2, fun _ => a⟩ : Tuple X)).1 : Set (IndexAugmented X)) := by
  intro h
  have h0 : IndexAugmented.mk 0 a ∈
      ((graph (⟨2, fun _ => a⟩ : Tuple X)).1 : Set (IndexAugmented X)) :=
    (mem_graph _).mpr ⟨⟨0, by change 0 < 2; decide⟩, rfl⟩
  have h1 : IndexAugmented.mk 1 a ∈
      ((graph (⟨2, fun _ => a⟩ : Tuple X)).1 : Set (IndexAugmented X)) :=
    (mem_graph _).mpr ⟨⟨1, by change 1 < 2; decide⟩, rfl⟩
  have heq := congrArg IndexAugmented.index (h h0 h1 rfl)
  exact Nat.zero_ne_one heq

/-- Original label: `thm:minimal-sorting-measurable`.
The actual minimum rule is measurable into the sorted subtype with its
subspace Borel sigma-algebra, as specified in the current statement. -/
theorem measurable_minimumSortingRule_toSortedTuple
    {X : Type u} [EMetricSpace X] [PartialOrder X]
    (hle : @MeasurableSet (X × X) (@borel (X × X) inferInstance) {p | p.1 ≤ p.2}) :
    @Measurable (Tuple X) (SortedTuple X) (tupleHausdorffBorel (X := X))
      (@borel (SortedTuple X) (sortedTupleTopology (X := X)))
      (minimumSortingRule (X := X)).toSortedTuple := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  rw [show @borel (SortedTuple X) (sortedTupleTopology (X := X)) =
    MeasurableSpace.comap Subtype.val (tupleHausdorffBorel (X := X)) from
      borel_comap]
  change Measurable (fun x : Tuple X =>
    (⟨minimumSort x, minimumSort_isSorted x⟩ : SortedTuple X))
  exact (measurable_minimumSort_of_borelOrder hle).subtype_mk

/-- The Euclidean, rather than maximum, norm on a pair of real coordinates. -/
abbrev EuclideanPair := WithLp 2 (ℝ × ℝ)

/-- Original label: `exmp:sort-discont`.
The lexicographic order on the Euclidean plane is the exact source formula. -/
@[reducible] noncomputable def euclideanLexOrder : LinearOrder EuclideanPair :=
  LinearOrder.lift' (fun p : EuclideanPair => toLex (WithLp.ofLp p))
    (toLex.injective.comp (WithLp.equiv 2 (ℝ × ℝ)).injective)

attribute [local instance] euclideanLexOrder

def twoTuple (p : (ℝ × ℝ) × (ℝ × ℝ)) : Tuple EuclideanPair :=
  ⟨2, ![WithLp.toLp 2 p.1, WithLp.toLp 2 p.2]⟩

theorem twoTuple_isSorted_iff (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    IsSorted (twoTuple p) ↔ ThesisContext.lexicographicPairLE p.1 p.2 := by
  rw [isSorted_iff_monotone]
  constructor
  · intro h
    have hp := h (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≤ 1 by decide)
    exact Prod.Lex.toLex_le_toLex.mp hp
  · intro h i j hij
    fin_cases i <;> fin_cases j
    · exact le_rfl
    · exact Prod.Lex.toLex_le_toLex.mpr h
    · norm_num at hij
    · exact le_rfl

theorem continuous_twoTuple :
    @Continuous ((ℝ × ℝ) × (ℝ × ℝ)) (Tuple EuclideanPair) inferInstance
      (tupleHausdorffMetricTopology (X := EuclideanPair)) twoTuple := by
  letI : TopologicalSpace (Tuple EuclideanPair) :=
    tupleHausdorffMetricTopology (X := EuclideanPair)
  apply (continuous_sigmaMk_tupleHausdorff 2).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (WithLp.prod_continuous_toLp 2 ℝ ℝ).comp continuous_fst
  · exact (WithLp.prod_continuous_toLp 2 ℝ ℝ).comp continuous_snd

/-- Original label: `exmp:sort-discont`.
The displayed sequence consists of sorted tuples in the actual tuple
Hausdorff space over the Euclidean plane, and converges to an unsorted tuple. -/
theorem euclidean_tuple_sorting_counterexample :
    (∀ n, IsSorted (twoTuple (ThesisContext.lexSortingWitness n))) ∧
      @Tendsto ℕ (Tuple EuclideanPair)
        (fun n => twoTuple (ThesisContext.lexSortingWitness n)) atTop
        (@nhds (Tuple EuclideanPair) (tupleHausdorffMetricTopology (X := EuclideanPair))
          (twoTuple ThesisContext.lexSortingLimit)) ∧
      ¬ IsSorted (twoTuple ThesisContext.lexSortingLimit) := by
  letI : TopologicalSpace (Tuple EuclideanPair) :=
    tupleHausdorffMetricTopology (X := EuclideanPair)
  obtain ⟨hsorted, hlim, hnot⟩ := ThesisContext.lexSorting_discontinuity_witness
  exact ⟨fun n => (twoTuple_isSorted_iff _).mpr (hsorted n),
    (continuous_twoTuple.tendsto _).comp hlim,
    fun h => hnot ((twoTuple_isSorted_iff _).mp h)⟩

/-- Original label: `exmp:sort-discont`.
At the limiting tuple the unique sorted output is exactly the reversed pair
displayed in the manuscript. -/
theorem euclidean_sortingRule_limit (σ : SortingRule EuclideanPair) :
    σ.sort (twoTuple ThesisContext.lexSortingLimit) = twoTuple ((0, 0), (0, 1)) := by
  let z := twoTuple ThesisContext.lexSortingLimit
  let w := twoTuple ((0, 0), (0, 1))
  let π : FinitePermutation z.length := Equiv.swap (0 : Fin 2) (1 : Fin 2)
  have hp : permute z π = w := by
    refine Sigma.ext (show (permute z π).1 = w.1 from rfl) ?_
    apply heq_of_eq
    change (fun i : Fin 2 =>
      ![WithLp.toLp 2 ((0, 1) : ℝ × ℝ), WithLp.toLp 2 ((0, 0) : ℝ × ℝ)]
        (Equiv.swap (0 : Fin 2) (1 : Fin 2) i)) =
      ![WithLp.toLp 2 ((0, 0) : ℝ × ℝ), WithLp.toLp 2 ((0, 1) : ℝ × ℝ)]
    funext i
    fin_cases i <;> simp
  have hw : IsSorted w := (twoTuple_isSorted_iff _).mpr (by
    norm_num [ThesisContext.lexicographicPairLE])
  let ρ : SortingPermutations z := ⟨π, by
    change IsSorted (permute z π)
    rw [hp]
    exact hw⟩
  obtain ⟨τ, hτ⟩ := σ.exists_sortingPermutation z
  exact hτ.trans ((sortedPermutations_eq_of_linearOrder z τ ρ).trans hp)

/-- Original label: `exmp:sort-discont`.
Every sorting rule for this total order is discontinuous, not merely the
particular minimum rule. -/
theorem euclidean_sortingRule_not_continuous (σ : SortingRule EuclideanPair) :
    ¬ @Continuous (Tuple EuclideanPair) (Tuple EuclideanPair)
      (tupleHausdorffMetricTopology (X := EuclideanPair))
      (tupleHausdorffMetricTopology (X := EuclideanPair)) σ.sort := by
  letI : TopologicalSpace (Tuple EuclideanPair) :=
    tupleHausdorffMetricTopology (X := EuclideanPair)
  intro hc
  obtain ⟨hsorted, hlim, hnot⟩ := euclidean_tuple_sorting_counterexample
  have hfixed : ∀ n, σ.sort (twoTuple (ThesisContext.lexSortingWitness n)) =
      twoTuple (ThesisContext.lexSortingWitness n) := fun n =>
    TupleSortingAlignment.sortingRule_fixes_sorted σ _ (hsorted n)
  have hlim' := (hc.tendsto _).comp hlim
  simp only [Function.comp_def, hfixed] at hlim'
  have heq := tendsto_nhds_unique hlim hlim'
  exact hnot (heq.symm ▸ σ.sorted_sort (twoTuple ThesisContext.lexSortingLimit))

/-- Original label: `exmp:sort-discont`.
The sorted tuples in the Euclidean example do not form a closed set. -/
theorem euclidean_sortedTuples_not_closed :
    ¬ @IsClosed (Tuple EuclideanPair) (tupleHausdorffMetricTopology (X := EuclideanPair))
      {x | IsSorted x} := by
  letI : TopologicalSpace (Tuple EuclideanPair) :=
    tupleHausdorffMetricTopology (X := EuclideanPair)
  intro hc
  obtain ⟨hsorted, hlim, hnot⟩ := euclidean_tuple_sorting_counterexample
  exact hnot (hc.mem_of_tendsto hlim (Filter.Eventually.of_forall hsorted))

/-- Original label: `exmp:sort-discont`.
With the inherited tuple Hausdorff distance, the sorted subspace is incomplete. -/
theorem euclidean_sortedTuples_not_complete :
    ¬ CompleteSpace (SortedTuple EuclideanPair) := by
  letI : TopologicalSpace (Tuple EuclideanPair) :=
    tupleHausdorffMetricTopology (X := EuclideanPair)
  intro h
  have hc : IsClosed ({x : Tuple EuclideanPair | IsSorted x}) :=
    (completeSpace_coe_iff_isComplete.mp h).isClosed
  exact euclidean_sortedTuples_not_closed hc

end Thesis.Foundations.MarketRepresentation.TupleTopologyAlignment
