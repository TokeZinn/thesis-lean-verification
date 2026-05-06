import Foundations.External
import Foundations.Stochastic.PermutedTuples
import Mathlib.Probability.Kernel.Basic

/-!
# Stochastic Markets: Tuple Measures

Blueprint module for
`1 - theoretical foundations/5_stochastic_markets.tex`,
the tuple-to-integer-measure part of "Tuples and Point Processes".

Planned formal content:

* tuple-induced integer-valued measure map;
* continuity of the tuple-measure map;
* `prop:tuple-measure-surjective`;
* quotient invariance and bijection;
* continuity of inverse;
* `thm:integer-measures-tuples-homeomorphic`;
* `lem:measurable-enumeration`;
* Markov kernel selecting a uniformly random representative.
-/

namespace Thesis
namespace Foundations
namespace Stochastic
namespace TupleMeasures

open Thesis.Foundations.MarketRepresentation
open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesSorting
open Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
open Thesis.Foundations.External
open Thesis.Foundations.Stochastic.PointProcesses
open Thesis.Foundations.Stochastic.PermutedTuples
open MeasureTheory Metric Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-! ## Tuple-Induced Integer-Valued Measures -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Point Processes", display `eq:prelim-pp` and
Definition `defn:tuple-induced-integer-valued-measure`.

Original label: `eq:prelim-pp` /
`defn:tuple-induced-integer-valued-measure`.

Informal statement: a tuple induces a finite integer-valued measure by placing
one Dirac atom at each tuple entry.

Lean strategy / thesis relation note: the thesis writes
`\sum_{i \in \mathrm{domain}(\bm{x})}\delta_{\bm{x}(i)}`. Lean represents the
domain as `Fin x.length`, so this is the finite atomic measure with constant
multiplicity `1`.
-/
noncomputable def tupleInducedIntegerMeasure {X : Type u}
    [MeasurableSpace X] (x : Tuple X) : FiniteIntegerMeasures X :=
  finiteAtomicIntegerMeasure
    (fun i : Fin x.length => Tuple.entry x i)
    (fun _ : Fin x.length => 1)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Point Processes", display `eq:prelim-pp` and
Definition `defn:tuple-induced-integer-valued-measure`.

Original label: `eq:prelim-pp` /
`defn:tuple-induced-integer-valued-measure`.

Informal statement: evaluating the tuple-induced measure on a measurable set
counts the entries of the tuple that lie in that set.
-/
theorem tupleInducedIntegerMeasure_apply {X : Type u}
    [MeasurableSpace X] (x : Tuple X) {B : Set X}
    (hB : MeasurableSet B) :
    (tupleInducedIntegerMeasure x).1 B =
      ∑ i : Fin x.length,
        B.indicator (fun _ : X => (1 : ℝ≥0)) (Tuple.entry x i) := by
  simpa [tupleInducedIntegerMeasure] using
    finiteAtomicMeasure_apply
      (fun i : Fin x.length => Tuple.entry x i)
      (fun _ : Fin x.length => 1) hB

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: length/total-mass identity used in
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: the total mass of a tuple-induced integer measure is the
length of the tuple.
-/
theorem tupleInducedIntegerMeasure_univ {X : Type u}
    [MeasurableSpace X] (x : Tuple X) :
    (tupleInducedIntegerMeasure x).1 Set.univ = x.length := by
  change finiteAtomicMeasure
      (fun i : Fin x.length => Tuple.entry x i)
      (fun _ : Fin x.length => 1) Set.univ = (x.length : ℝ≥0)
  rw [finiteAtomicMeasure_univ]
  simp

/-! ## Continuity of the Tuple-Induced Measure Map -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-induced-measure-continuous`.

Original label: finite-sum evaluation used in
`prop:tuple-induced-measure-continuous`.

Informal statement: the underlying measure of a tuple-induced integer-valued
measure evaluates a Borel set by summing singleton indicators over tuple
entries.
-/
theorem tupleInducedIntegerMeasure_toMeasure_apply {X : Type u}
    [MeasurableSpace X] (x : Tuple X) {B : Set X}
    (hB : MeasurableSet B) :
    ((tupleInducedIntegerMeasure x).1 : Measure X) B =
      ∑ i : Fin x.length,
        ((B.indicator (fun _ : X => (1 : ℝ≥0)) (Tuple.entry x i) :
          ℝ≥0) : ℝ≥0∞) := by
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [tupleInducedIntegerMeasure_apply x hB]
  simp

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-induced-measure-continuous`.

Original label: coordinate-thickening step in
`prop:tuple-induced-measure-continuous`.

Informal statement: if every coordinate of `y` lies within `ε` of the
corresponding coordinate of `x`, then the mass that `x` assigns to `B` is
bounded by the mass that `y` assigns to the `ε`-extension of `B`.

Lean strategy / thesis relation note: this is the formal version of the thesis implication
`x_i ∈ B ⇒ y_i ∈ B^ε`, summed over the finite tuple domain.
-/
theorem tupleInducedIntegerMeasure_apply_le_thickening_of_forall_edist_lt
    {X : Type u} [MeasurableSpace X]
    [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    {n : ℕ} {x y : Fin n → X} {ε : ℝ≥0∞} (hε_top : ε < ∞)
    (hxy : ∀ i : Fin n, edist (y i) (x i) < ε)
    {B : Set X} (hB : MeasurableSet B) :
    ((tupleInducedIntegerMeasure (Sigma.mk n x : Tuple X)).1 : Measure X) B ≤
      ((tupleInducedIntegerMeasure (Sigma.mk n y : Tuple X)).1 : Measure X)
        (thickening ε.toReal B) := by
  rw [tupleInducedIntegerMeasure_toMeasure_apply _ hB,
    tupleInducedIntegerMeasure_toMeasure_apply _
      isOpen_thickening.measurableSet]
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hmem : x i ∈ B
  · have hy : y i ∈ thickening ε.toReal B := by
      rw [Metric.mem_thickening_iff_exists_edist_lt]
      refine ⟨x i, hmem, ?_⟩
      simpa [ENNReal.ofReal_toReal hε_top.ne] using hxy i
    simp [Tuple.entry, hmem, hy]
  · simp [Tuple.entry, hmem]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-induced-measure-continuous`.

Original label: fixed-length Prokhorov estimate in
`prop:tuple-induced-measure-continuous`.

Informal statement: on a fixed-length tuple layer, if the tuple Hausdorff
distance is below `1`, then the Prokhorov distance between the induced
counting measures is bounded by the tuple Hausdorff distance.

Lean strategy / thesis relation note: the proof follows the thesis. Below radius `1`, Chapter 2's
tuple machinery identifies the tuple Hausdorff distance with the maximum
coordinate distance. The two Prokhorov inequalities then follow by summing
the coordinate-thickening implication in both directions.
-/
theorem tupleInducedIntegerMeasure_prokhorovEDistance_le_of_fixedLength_edist_lt_one
    {X : Type u} [MeasurableSpace X]
    [EMetricSpace X] [OpensMeasurableSpace X]
    {n : ℕ} (x y : Fin n → X)
    (hxy_one :
      edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) <
        (1 : ℝ≥0∞)) :
    prokhorovEDistance
      (tupleInducedIntegerMeasure (Sigma.mk n x : Tuple X)).1
      (tupleInducedIntegerMeasure (Sigma.mk n y : Tuple X)).1 ≤
        edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) := by
  unfold prokhorovEDistance
  apply MeasureTheory.levyProkhorovEDist_le_of_forall
  intro ε B hδ_lt_ε hε_top hB
  have hxy_coord : ∀ i : Fin n, edist (y i) (x i) < ε := by
    intro i
    calc
      edist (y i) (x i) = edist (x i) (y i) := edist_comm _ _
      _ ≤ edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) :=
          coordinate_edist_le_fixedLength_edist_of_lt_one hxy_one i
      _ < ε := hδ_lt_ε
  have hyx_coord : ∀ i : Fin n, edist (x i) (y i) < ε := by
    intro i
    exact lt_of_le_of_lt
      (coordinate_edist_le_fixedLength_edist_of_lt_one hxy_one i) hδ_lt_ε
  refine ⟨?_, ?_⟩
  · exact
      (tupleInducedIntegerMeasure_apply_le_thickening_of_forall_edist_lt
        (x := x) (y := y) hε_top hxy_coord hB).trans
          (le_add_right le_rfl)
  · exact
      (tupleInducedIntegerMeasure_apply_le_thickening_of_forall_edist_lt
        (x := y) (y := x) hε_top hyx_coord hB).trans
          (le_add_right le_rfl)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-induced-measure-continuous`.

Original label: global Prokhorov estimate in
`prop:tuple-induced-measure-continuous`.

Informal statement: if two tuples are within Hausdorff distance `< 1`, then
their induced integer-valued measures are within at most that distance in the
Prokhorov metric.

Lean strategy / thesis relation note: the only extra Lean step is transporting the proof into the
common fixed-length layer after Chapter 2 proves that distance `< 1` forces
equal tuple lengths.
-/
theorem tupleInducedIntegerMeasure_prokhorovEDistance_le_of_edist_lt_one
    {X : Type u} [MeasurableSpace X]
    [EMetricSpace X] [OpensMeasurableSpace X]
    {x y : Tuple X} (hxy_one : edist x y < (1 : ℝ≥0∞)) :
    prokhorovEDistance (tupleInducedIntegerMeasure x).1
      (tupleInducedIntegerMeasure y).1 ≤ edist x y := by
  rcases x with ⟨m, x⟩
  rcases y with ⟨n, y⟩
  have hmn : m = n := by
    simpa [Tuple.length] using
      (length_eq_of_edist_lt_one
        (x := (Sigma.mk m x : Tuple X))
        (y := (Sigma.mk n y : Tuple X)) hxy_one)
  subst n
  exact
    tupleInducedIntegerMeasure_prokhorovEDistance_le_of_fixedLength_edist_lt_one
      x y hxy_one

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-induced-measure-continuous`.

Original label: epsilon-delta core of
`prop:tuple-induced-measure-continuous`.

Informal statement: if two tuples are closer than both `ε` and `1`, then
their induced integer-valued measures have Prokhorov distance `< ε`.
-/
theorem tupleInducedIntegerMeasure_prokhorovEDistance_lt_of_edist_lt_min
    {X : Type u} [MeasurableSpace X]
    [EMetricSpace X] [OpensMeasurableSpace X]
    {x y : Tuple X} {ε : ℝ≥0∞}
    (hxy : edist x y < min ε 1) :
    prokhorovEDistance (tupleInducedIntegerMeasure x).1
      (tupleInducedIntegerMeasure y).1 < ε := by
  have hxy_one : edist x y < (1 : ℝ≥0∞) :=
    lt_of_lt_of_le hxy (min_le_right ε 1)
  exact lt_of_le_of_lt
    (tupleInducedIntegerMeasure_prokhorovEDistance_le_of_edist_lt_one hxy_one)
    (lt_of_lt_of_le hxy (min_le_left ε 1))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-induced-measure-continuous`.

Original label: Prokhorov-topology version of the map `\mathfrak{m}`.

Informal statement: a tuple is sent to its induced finite measure, but the
codomain is equipped with mathlib's Lévy-Prokhorov metric topology.

Lean strategy / thesis relation note: `FiniteIntegerMeasures X` is a subtype of `FiniteMeasure X`.
Rather than installing a separate subtype topology at this stage, Lean proves
continuity into `LevyProkhorov (FiniteMeasures X)` and the definition itself
still lands in the integer-valued subtype.
-/
noncomputable def tupleInducedLevyProkhorovFiniteMeasure {X : Type u}
    [MeasurableSpace X] :
    Tuple X → MeasureTheory.LevyProkhorov (FiniteMeasures X) :=
  fun x => MeasureTheory.LevyProkhorov.ofMeasure
    (tupleInducedIntegerMeasure x).1

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-induced-measure-continuous`.

Original label: `prop:tuple-induced-measure-continuous`.

Informal statement: the tuple-induced integer-valued measure map is
continuous from tuple Hausdorff space to finite measures with the Prokhorov
metric.

Lean strategy / thesis relation note: the thesis writes an epsilon-delta proof. Lean uses the same
proof against the explicit tuple Hausdorff metric topology
`tupleHausdorffMetricTopology`; Chapter 2 separately proves this topology is
the standard fixed-length disjoint-union topology.
-/
theorem tupleInducedLevyProkhorovFiniteMeasure_continuous {X : Type u}
    [MeasurableSpace X] [EMetricSpace X] [OpensMeasurableSpace X] :
    @Continuous (Tuple X) (MeasureTheory.LevyProkhorov (FiniteMeasures X))
      (tupleHausdorffMetricTopology (X := X)) inferInstance
      (tupleInducedLevyProkhorovFiniteMeasure (X := X)) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  change Continuous (tupleInducedLevyProkhorovFiniteMeasure (X := X))
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
  intro ε hε
  rcases exists_pos_lt_ennreal hε with ⟨r, hr_pos, hr_lt⟩
  refine ⟨min r 1, lt_min hr_pos zero_lt_one, ?_⟩
  intro x hx
  have hx_one : edist x x0 < (1 : ℝ≥0∞) :=
    lt_of_lt_of_le hx (min_le_right r 1)
  have hLP_le :
      prokhorovEDistance (tupleInducedIntegerMeasure x).1
        (tupleInducedIntegerMeasure x0).1 ≤ edist x x0 :=
    tupleInducedIntegerMeasure_prokhorovEDistance_le_of_edist_lt_one hx_one
  have hLP_lt_r :
      prokhorovEDistance (tupleInducedIntegerMeasure x).1
        (tupleInducedIntegerMeasure x0).1 < r :=
    lt_of_le_of_lt hLP_le (lt_of_lt_of_le hx (min_le_left r 1))
  change MeasureTheory.levyProkhorovEDist
      ((tupleInducedIntegerMeasure x).1 : Measure X)
      ((tupleInducedIntegerMeasure x0).1 : Measure X) < ε
  exact lt_trans hLP_lt_r hr_lt

/-! ## Atomic Decompositions Give Tuples -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: list-sum helper for `prop:tuple-measure-surjective`.

Informal statement: summing over a flattened list is the same as first
summing each block and then summing the block sums.
-/
theorem list_sum_flatMap {α M : Type*} [AddMonoid M]
    (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: finite partition summation for the sets `L_k`.

Informal statement: if finite sets `s k` cover every index exactly once, then
summing over the blocks and then over block members is the same as summing
over all indices.
-/
theorem Finset.sum_sum_mem_eq_sum_of_unique_cover
    {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (s : ι → Finset κ) (f : κ → M)
    (hcover : ∀ l : κ, ∃! k : ι, l ∈ s k) :
    (∑ k : ι, ∑ l ∈ s k, f l) = ∑ l : κ, f l := by
  classical
  calc
    (∑ k : ι, ∑ l ∈ s k, f l)
        = ∑ k : ι, ∑ l : κ, if l ∈ s k then f l else 0 := by
          apply Finset.sum_congr rfl
          intro k _hk
          calc
            (∑ l ∈ s k, f l)
                = ∑ l ∈ Finset.univ.filter (fun l : κ => l ∈ s k), f l := by
                apply Finset.sum_congr
                · ext l
                  simp
                · intro l hl
                  rfl
            _ = ∑ l : κ, if l ∈ s k then f l else 0 := by
                rw [Finset.sum_filter]
    _ = ∑ l : κ, ∑ k : ι, if l ∈ s k then f l else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ l : κ, f l := by
          apply Finset.sum_congr rfl
          intro l _hl
          rcases hcover l with ⟨k0, hk0, huniq⟩
          rw [Finset.sum_eq_single k0]
          · simp [hk0]
          · intro k _hk hk_ne
            have hnot : l ∉ s k := by
              intro hk
              exact hk_ne (huniq k hk)
            simp [hnot]
          · intro hk0_not
            exact False.elim (hk0_not (Finset.mem_univ k0))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: exact-cover consequence of the disintegration lemma.

Informal statement: if finite blocks are pairwise disjoint, every atom has
positive multiplicity, and the sum of multiplicities over the blocks equals
the total multiplicity, then the blocks cover every atom exactly once.

Lean strategy / thesis relation note: this is the finite arithmetic step the manuscript uses when
the disjoint `L_k` with the correct block masses are treated as a partition.
-/
theorem Finset.unique_cover_of_disjoint_of_sum_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → Finset κ) (w : κ → ℕ)
    (hpos : ∀ l : κ, 0 < w l)
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (s i) (s j))
    (hsum : (∑ i : ι, ∑ l ∈ s i, w l) = ∑ l : κ, w l) :
    ∀ l : κ, ∃! i : ι, l ∈ s i := by
  classical
  have huniq_mem : ∀ l : κ, ∀ i j : ι, l ∈ s i → l ∈ s j → i = j := by
    intro l i j hi hj
    by_contra hij
    exact Finset.disjoint_left.mp (hdisj i j hij) hi hj
  have hblocks :
      (∑ i : ι, ∑ l ∈ s i, w l) =
        ∑ l : κ, ∑ i : ι, if l ∈ s i then w l else 0 := by
    calc
      (∑ i : ι, ∑ l ∈ s i, w l)
          = ∑ i : ι, ∑ l : κ, if l ∈ s i then w l else 0 := by
            apply Finset.sum_congr rfl
            intro i _hi
            calc
              (∑ l ∈ s i, w l)
                  = ∑ l ∈ Finset.univ.filter (fun l : κ => l ∈ s i), w l := by
                  apply Finset.sum_congr
                  · ext l
                    simp
                  · intro l hl
                    rfl
              _ = ∑ l : κ, if l ∈ s i then w l else 0 := by
                  rw [Finset.sum_filter]
      _ = ∑ l : κ, ∑ i : ι, if l ∈ s i then w l else 0 := by
            rw [Finset.sum_comm]
  have hweighted :
      (∑ l : κ, ∑ i : ι, if l ∈ s i then w l else 0) =
        ∑ l : κ, w l :=
    hblocks.symm.trans hsum
  intro l0
  have hexists : ∃ i : ι, l0 ∈ s i := by
    by_contra hmissing
    have hle : ∀ l : κ,
        (∑ i : ι, if l ∈ s i then w l else 0) ≤ w l := by
      intro l
      by_cases hcov : ∃ i : ι, l ∈ s i
      · rcases hcov with ⟨i0, hi0⟩
        have hsum_single :
            (∑ i : ι, if l ∈ s i then w l else 0) = w l := by
          rw [Finset.sum_eq_single i0]
          · simp [hi0]
          · intro i _hi hneq
            have hnot : l ∉ s i := by
              intro hi
              exact hneq (huniq_mem l i i0 hi hi0)
            simp [hnot]
          · intro hi0_not
            exact False.elim (hi0_not (Finset.mem_univ i0))
        rw [hsum_single]
      · have hsum_zero :
            (∑ i : ι, if l ∈ s i then w l else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i _hi
          have hnot : l ∉ s i := by
            intro hi
            exact hcov ⟨i, hi⟩
          simp [hnot]
        rw [hsum_zero]
        exact Nat.zero_le (w l)
    have hlt_l0 :
        (∑ i : ι, if l0 ∈ s i then w l0 else 0) < w l0 := by
      have hsum_zero :
          (∑ i : ι, if l0 ∈ s i then w l0 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _hi
        have hnot : l0 ∉ s i := by
          intro hi
          exact hmissing ⟨i, hi⟩
        simp [hnot]
      rw [hsum_zero]
      exact hpos l0
    have hstrict :
        (∑ l : κ, ∑ i : ι, if l ∈ s i then w l else 0) <
          ∑ l : κ, w l := by
      apply Finset.sum_lt_sum
      · intro l _hl
        exact hle l
      · exact ⟨l0, Finset.mem_univ l0, hlt_l0⟩
    exact (ne_of_lt hstrict) hweighted
  rcases hexists with ⟨i0, hi0⟩
  refine ⟨i0, hi0, ?_⟩
  intro i hi
  exact huniq_mem l0 i i0 hi hi0

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: repeated-atom tuple construction in
`prop:tuple-measure-surjective`.

Informal statement: from atoms `x_k` and multiplicities `β_k`, form the list
`[x_1,\dots,x_1,x_2,\dots,x_2,\dots]` where atom `x_k` appears `β_k` times.

Lean strategy / thesis relation note: the thesis writes this as a piecewise definition on intervals
of the tuple domain. Lean uses the equivalent flattened list of repeated
blocks, then converts the list into a tuple.
-/
def atomicExpansionList {X : Type u} {n : ℕ} (atom : Fin n → X)
    (multiplicity : Fin n → ℕ) : List X :=
  (List.finRange n).flatMap fun i => List.replicate (multiplicity i) (atom i)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: block-sum helper for `prop:tuple-measure-surjective`.

Informal statement: summing singleton indicators over `β` copies of `x`
equals the weighted singleton indicator with weight `β`.
-/
theorem sum_replicate_indicator {X : Type u} (B : Set X) (β : ℕ) (x : X) :
    ((List.replicate β x).map
      (fun z => B.indicator (fun _ : X => (1 : ℝ≥0)) z)).sum =
      B.indicator (fun _ : X => (β : ℝ≥0)) x := by
  by_cases hx : x ∈ B
  · simp [hx, List.sum_replicate, nsmul_eq_mul]
  · simp [hx]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: repeated-block sum in the grouped representative.

Informal statement: if a block repeats an auxiliary index `β` times, and
every repeated entry is read as the same atom `x`, then summing singleton
indicators over that block gives multiplicity `β` at `x`.
-/
theorem sum_replicate_indicator_const {A : Type v} {X : Type u}
    (B : Set X) (β : ℕ) (a : A) (x : X) :
    ((List.replicate β a).map
      (fun _ => B.indicator (fun _ : X => (1 : ℝ≥0)) x)).sum =
      B.indicator (fun _ : X => (β : ℝ≥0)) x := by
  by_cases hx : x ∈ B
  · simp [hx, List.sum_replicate, nsmul_eq_mul]
  · simp [hx]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: repeated-atom evaluation in
`prop:tuple-measure-surjective`.

Informal statement: evaluating singleton indicators over the expanded atom
list gives the finite weighted atomic sum.
-/
theorem atomicExpansionList_sum_indicator {X : Type u} {n : ℕ}
    (atom : Fin n → X) (multiplicity : Fin n → ℕ) (B : Set X) :
    ((atomicExpansionList atom multiplicity).map
        (fun z => B.indicator (fun _ : X => (1 : ℝ≥0)) z)).sum =
      ∑ i : Fin n,
        B.indicator (fun _ : X => (multiplicity i : ℝ≥0)) (atom i) := by
  rw [atomicExpansionList, List.map_flatMap, list_sum_flatMap]
  simp only [sum_replicate_indicator]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: tuple/list evaluation helper for
`prop:tuple-measure-surjective`.

Informal statement: summing a function over the entries of the tuple
associated to a list is the same as summing over the list.
-/
theorem tupleOfList_sum_indicator {X : Type u} (l : List X) (B : Set X) :
    (∑ i : Fin (tupleOfList (X := X) l).length,
      B.indicator (fun _ : X => (1 : ℝ≥0))
        (Tuple.entry (tupleOfList (X := X) l) i)) =
    (l.map fun z => B.indicator (fun _ : X => (1 : ℝ≥0)) z).sum := by
  rw [← List.sum_ofFn]
  congr 1
  rw [List.ofFn_comp']
  congr 1
  exact List.ofFn_get l

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: tuple/list bookkeeping for the grouped representative.

Informal statement: a list of indices can be converted into a tuple after
applying a value map to every list entry.

Lean strategy / thesis relation note: this is a proof device for the manuscript's blockwise
construction. Both grouped representatives below are built from the same
index list, so their lengths are definitionally identical.
-/
def tupleOfListMap {A : Type v} {X : Type u} (l : List A) (f : A → X) :
    Tuple X :=
  ⟨l.length, fun i => f (l.get i)⟩

@[simp]
theorem tupleOfListMap_length {A : Type v} {X : Type u}
    (l : List A) (f : A → X) :
    (tupleOfListMap l f).length = l.length :=
  rfl

@[simp]
theorem tupleOfListMap_entry {A : Type v} {X : Type u}
    (l : List A) (f : A → X) (i : Fin (tupleOfListMap l f).length) :
    Tuple.entry (tupleOfListMap l f) i = f (l.get i) :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: tuple/list sum bookkeeping for the grouped representative.

Informal statement: summing singleton indicators over a tuple obtained by
mapping a list is the same as summing over the mapped list itself.
-/
theorem tupleOfListMap_sum_indicator {A : Type v} {X : Type u}
    (l : List A) (f : A → X) (B : Set X) :
    (∑ i : Fin (tupleOfListMap l f).length,
      B.indicator (fun _ : X => (1 : ℝ≥0))
        (Tuple.entry (tupleOfListMap l f) i)) =
    (l.map fun a => B.indicator (fun _ : X => (1 : ℝ≥0)) (f a)).sum := by
  rw [← List.sum_ofFn]
  change
    (List.ofFn
      (fun i : Fin l.length =>
        B.indicator (fun _ : X => (1 : ℝ≥0)) (f (l.get i)))).sum =
      (l.map fun a => B.indicator (fun _ : X => (1 : ℝ≥0)) (f a)).sum
  congr 1
  rw [List.ofFn_comp']
  change
    List.map (B.indicator (fun _ : X => (1 : ℝ≥0)))
      (List.ofFn (fun i : Fin l.length => f (l.get i))) =
      List.map ((B.indicator (fun _ : X => (1 : ℝ≥0))) ∘ f) l
  rw [← List.map_map]
  congr 1
  rw [List.ofFn_comp']
  rw [List.ofFn_get l]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: constructive core of `prop:tuple-measure-surjective`.

Informal statement: the tuple obtained by repeating each atom according to
its multiplicity induces exactly the corresponding finite atomic measure.
-/
theorem tupleInducedIntegerMeasure_atomicExpansion {X : Type u}
    [MeasurableSpace X] {n : ℕ} (atom : Fin n → X)
    (multiplicity : Fin n → ℕ) :
    tupleInducedIntegerMeasure
      (tupleOfList (X := X) (atomicExpansionList atom multiplicity)) =
      finiteAtomicIntegerMeasure atom multiplicity := by
  apply Subtype.ext
  apply FiniteMeasure.eq_of_forall_apply_eq
  intro B hB
  rw [tupleInducedIntegerMeasure_apply _ hB]
  change
    (∑ i : Fin (tupleOfList (X := X)
        (atomicExpansionList atom multiplicity)).length,
      B.indicator (fun _ : X => (1 : ℝ≥0))
        (Tuple.entry (tupleOfList (X := X)
          (atomicExpansionList atom multiplicity)) i)) =
      finiteAtomicMeasure atom multiplicity B
  rw [tupleOfList_sum_indicator, atomicExpansionList_sum_indicator,
    finiteAtomicMeasure_apply atom multiplicity hB]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: tuple constructed from an atomic decomposition.

Informal statement: given a finite atomic decomposition of an integer-valued
measure, choose the tuple that repeats each atom by its multiplicity.
-/
def tupleOfAtomicDecomposition {X : Type u} [MeasurableSpace X]
    {μ : FiniteIntegerMeasures X} (d : AtomicDecomposition μ) : Tuple X :=
  tupleOfList (X := X) (atomicExpansionList d.atom d.multiplicity)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: construction verifies `prop:tuple-measure-surjective`.

Informal statement: the tuple associated to an atomic decomposition induces
the original finite integer-valued measure.
-/
theorem tupleInducedIntegerMeasure_tupleOfAtomicDecomposition {X : Type u}
    [MeasurableSpace X] {μ : FiniteIntegerMeasures X}
    (d : AtomicDecomposition μ) :
    tupleInducedIntegerMeasure (tupleOfAtomicDecomposition d) = μ := by
  calc
    tupleInducedIntegerMeasure (tupleOfAtomicDecomposition d)
        = finiteAtomicIntegerMeasure d.atom d.multiplicity := by
          exact tupleInducedIntegerMeasure_atomicExpansion d.atom d.multiplicity
    _ = μ := by
          apply Subtype.ext
          exact d.represents

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: conditional form of `prop:tuple-measure-surjective`.

Informal statement: every finite integer-valued measure that admits an atomic
decomposition lies in the image of the tuple-induced measure map.

Lean strategy / thesis relation note: the thesis invokes
`thm:sufficient-decomposition` to supply the decomposition for every `μ`. This
local theorem isolates the constructive use of one chosen decomposition. The
universal standard-Borel existence theorem, together with the thesis
uniqueness-up-to-permutation clause, is recorded in `Foundations.External`;
only the existence half is needed for this surjectivity construction.
-/
theorem tupleInducedIntegerMeasure_surjective_of_atomicDecomposition
    {X : Type u} [MeasurableSpace X] {μ : FiniteIntegerMeasures X}
    (d : AtomicDecomposition μ) :
    ∃ x : Tuple X, tupleInducedIntegerMeasure x = μ :=
  ⟨tupleOfAtomicDecomposition d,
    tupleInducedIntegerMeasure_tupleOfAtomicDecomposition d⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: `prop:tuple-measure-surjective`.

Informal statement: if every finite integer-valued measure admits the atomic
decomposition from `thm:sufficient-decomposition`, then the tuple-induced
measure map is surjective.

Lean strategy / thesis relation note: the hypothesis is exactly the existence
part of the external/cited input used in the thesis proof. Keeping it explicit
separates the tuple construction from the background decomposition theorem;
the companion uniqueness-up-to-permutation statement is tracked externally
because this proposition does not use it.
-/
theorem tupleInducedIntegerMeasure_surjective_of_forall_atomicDecomposition
    {X : Type u} [MeasurableSpace X]
    (hdec : ∀ μ : FiniteIntegerMeasures X, AtomicDecomposition μ) :
    Function.Surjective (tupleInducedIntegerMeasure (X := X)) := by
  intro μ
  exact tupleInducedIntegerMeasure_surjective_of_atomicDecomposition (hdec μ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:tuple-measure-surjective`.

Original label: `prop:tuple-measure-surjective`.

Informal statement: on a standard Borel space, every finite integer-valued
measure is induced by some tuple.

Lean strategy / thesis relation note: the thesis proposition is stated in the
surrounding complete/separable metric setting and proves surjectivity by
citing `thm:sufficient-decomposition`. Lean uses the precise measurable
hypothesis needed by the external theorem, `StandardBorelSpace X`, and applies
only its existence component here; the uniqueness component is still present in
`Foundations.External` for faithfulness to the theorem label.
-/
theorem tupleInducedIntegerMeasure_surjective_standardBorel
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X] :
    Function.Surjective (tupleInducedIntegerMeasure (X := X)) :=
  tupleInducedIntegerMeasure_surjective_of_forall_atomicDecomposition
    finiteIntegerMeasure_atomicDecomposition

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:tuple-induced-measure-permutation-invariant`.

Original label: `cor:tuple-induced-measure-permutation-invariant`.

Informal statement: permuting the order of entries in a tuple does not change
the induced finite integer-valued measure.

Lean strategy / thesis relation note: this proves the corollary for the concrete permutation action
`permute`. The later quotient-space statement will package this as
well-definedness of the map from permuted tuples.
-/
theorem tupleInducedIntegerMeasure_permute {X : Type u}
    [MeasurableSpace X] (x : Tuple X)
    (π : FinitePermutation x.length) :
    tupleInducedIntegerMeasure (permute x π) =
      tupleInducedIntegerMeasure x := by
  apply Subtype.ext
  apply FiniteMeasure.eq_of_forall_apply_eq
  intro B hB
  rw [tupleInducedIntegerMeasure_apply _ hB,
    tupleInducedIntegerMeasure_apply _ hB]
  change
    (∑ i : Fin x.length,
      B.indicator (fun _ : X => (1 : ℝ≥0))
        (Tuple.entry (permute x π) i)) =
    ∑ i : Fin x.length,
      B.indicator (fun _ : X => (1 : ℝ≥0)) (Tuple.entry x i)
  simp only [permute, Tuple.entry, Tuple.length]
  exact Fintype.sum_bijective
    (fun i : Fin x.length => π i) π.bijective
    (fun i : Fin x.length =>
      B.indicator (fun _ : X => (1 : ℝ≥0)) (x.2 (π i)))
    (fun i : Fin x.length =>
      B.indicator (fun _ : X => (1 : ℝ≥0)) (x.2 i))
    (fun _ => rfl)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:tuple-induced-measure-permutation-invariant`.

Original label: `cor:tuple-induced-measure-permutation-invariant`.

Informal statement: tuple-induced measures are constant on permutative
equivalence classes.
-/
theorem tupleInducedIntegerMeasure_eq_of_permutativeEquality {X : Type u}
    [MeasurableSpace X] {x y : Tuple X}
    (hxy : PermutativeEquality x y) :
    tupleInducedIntegerMeasure x = tupleInducedIntegerMeasure y := by
  rcases hxy with ⟨π, rfl⟩
  exact (tupleInducedIntegerMeasure_permute x π).symm

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: multiplicity-counting helper for
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: summing singleton indicators over a fixed-length tuple
counts the indices whose entry is that singleton.

Lean strategy / thesis relation note: this is a finite-index version of the thesis observation that
the measure of `{a}` is the multiplicity of the atom `a`.
-/
theorem sum_singleton_indicator_eq_filter_card {X : Type u} [DecidableEq X]
    {n : ℕ} (f : Fin n → X) (a : X) :
    (∑ i : Fin n,
      ({a} : Set X).indicator (fun _ : X => (1 : ℝ≥0)) (f i)) =
      ((Finset.univ.filter fun i : Fin n => f i = a).card : ℝ≥0) := by
  simp [Set.indicator]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: list-counting helper for
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: the list count of `a` in `List.ofFn f` is the cardinality
of the finite fiber of `f` over `a`.
-/
theorem list_count_ofFn_eq_filter_card {X : Type u} [DecidableEq X]
    {n : ℕ} (f : Fin n → X) (a : X) :
    List.count a (List.ofFn f) =
      (Finset.univ.filter fun i : Fin n => f i = a).card := by
  rw [List.count_eq_countP, List.ofFn_eq_map, List.countP_map,
    List.countP_eq_length_filter]
  have hnodup : ((List.finRange n).filter (((fun x => x == a) ∘ f))).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1
  rw [List.toFinset_filter, List.toFinset_finRange]
  ext i
  simp

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: total-mass helper for
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: equal tuple-induced measures come from tuples of the same
length.
-/
theorem length_eq_of_tupleInducedIntegerMeasure_eq {X : Type u}
    [MeasurableSpace X] {x y : Tuple X}
    (h : tupleInducedIntegerMeasure x = tupleInducedIntegerMeasure y) :
    x.length = y.length := by
  have hmass : (tupleInducedIntegerMeasure x).1 Set.univ =
      (tupleInducedIntegerMeasure y).1 Set.univ := by
    exact congrArg (fun μ : FiniteIntegerMeasures X => μ.1 Set.univ) h
  rw [tupleInducedIntegerMeasure_univ x, tupleInducedIntegerMeasure_univ y] at hmass
  exact_mod_cast hmass

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: singleton-multiplicity helper for
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: equal tuple-induced measures give equal multiplicities
for every atom `a`.

Lean strategy / thesis relation note: Lean states the multiplicity equality as equality of list
counts for the `List.ofFn` entry lists. The `[DecidableEq X]` assumption is
Lean bookkeeping for list counts; it is available classically and does not add
mathematical content.
-/
theorem list_count_entries_eq_of_tupleInducedIntegerMeasure_eq {X : Type u}
    [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    {x y : Tuple X} (h : tupleInducedIntegerMeasure x = tupleInducedIntegerMeasure y)
    (a : X) :
    List.count a (List.ofFn fun i : Fin x.length => Tuple.entry x i) =
      List.count a (List.ofFn fun j : Fin y.length => Tuple.entry y j) := by
  have hmass : (tupleInducedIntegerMeasure x).1 ({a} : Set X) =
      (tupleInducedIntegerMeasure y).1 ({a} : Set X) := by
    exact congrArg (fun μ : FiniteIntegerMeasures X => μ.1 ({a} : Set X)) h
  rw [tupleInducedIntegerMeasure_apply x (measurableSet_singleton a),
    tupleInducedIntegerMeasure_apply y (measurableSet_singleton a)] at hmass
  rw [sum_singleton_indicator_eq_filter_card
      (fun i : Fin x.length => Tuple.entry x i) a,
    sum_singleton_indicator_eq_filter_card
      (fun j : Fin y.length => Tuple.entry y j) a] at hmass
  rw [list_count_ofFn_eq_filter_card
      (fun i : Fin x.length => Tuple.entry x i) a,
    list_count_ofFn_eq_filter_card
      (fun j : Fin y.length => Tuple.entry y j) a]
  exact_mod_cast hmass

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: multiset half of
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: if two tuples induce the same integer-valued measure,
then their entry lists are permutations of one another, i.e. they contain the
same atoms with the same multiplicities.
-/
theorem list_perm_entries_of_tupleInducedIntegerMeasure_eq {X : Type u}
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {x y : Tuple X} (h : tupleInducedIntegerMeasure x = tupleInducedIntegerMeasure y) :
    (List.ofFn fun i : Fin x.length => Tuple.entry x i).Perm
      (List.ofFn fun j : Fin y.length => Tuple.entry y j) := by
  classical
  rw [List.perm_iff_count]
  intro a
  exact list_count_entries_eq_of_tupleInducedIntegerMeasure_eq h a

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:tuple-induced-measure-permutation-invariant` and proof of
`prop:permuted-tuple-measure-map-bijective`.

Original label: converse multiset helper for
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: if the entry lists of two tuples are permutations of one
another, then the tuples induce the same integer-valued measure.
-/
theorem tupleInducedIntegerMeasure_eq_of_list_perm_entries {X : Type u}
    [MeasurableSpace X] {x y : Tuple X}
    (hperm : (List.ofFn fun i : Fin x.length => Tuple.entry x i).Perm
      (List.ofFn fun j : Fin y.length => Tuple.entry y j)) :
    tupleInducedIntegerMeasure x = tupleInducedIntegerMeasure y := by
  apply Subtype.ext
  apply FiniteMeasure.eq_of_forall_apply_eq
  intro B hB
  rw [tupleInducedIntegerMeasure_apply x hB,
    tupleInducedIntegerMeasure_apply y hB]
  rw [← List.sum_ofFn, ← List.sum_ofFn]
  rw [List.ofFn_comp' (fun i : Fin x.length => Tuple.entry x i)
      (fun z => B.indicator (fun _ : X => (1 : ℝ≥0)) z),
    List.ofFn_comp' (fun j : Fin y.length => Tuple.entry y j)
      (fun z => B.indicator (fun _ : X => (1 : ℝ≥0)) z)]
  exact (hperm.map (fun z => B.indicator (fun _ : X => (1 : ℝ≥0)) z)).sum_eq

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: multiset normal form for
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: under singleton measurability, equality of tuple-induced
integer-valued measures is equivalent to equality of the finite entry
multisets.

Lean strategy / thesis relation note: this theorem is intentionally one step weaker than the final
quotient-level bijection: it gives list permutation rather than an explicit
`Equiv.Perm (Fin n)` witness. The remaining upgrade is the finite matching
from a list permutation of fixed-length entry lists to a Lean index
permutation.
-/
theorem tupleInducedIntegerMeasure_eq_iff_list_perm_entries {X : Type u}
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {x y : Tuple X} :
    tupleInducedIntegerMeasure x = tupleInducedIntegerMeasure y ↔
      (List.ofFn fun i : Fin x.length => Tuple.entry x i).Perm
        (List.ofFn fun j : Fin y.length => Tuple.entry y j) := by
  constructor
  · exact list_perm_entries_of_tupleInducedIntegerMeasure_eq
  · exact tupleInducedIntegerMeasure_eq_of_list_perm_entries

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: finite matching step in
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: if two finite entry lists are permutations of one another,
then the associated tuples are permutatively equal.

Lean strategy / thesis relation note: the thesis phrases this as choosing a permutation of
`{1,\dots,n}`. Lean obtains the same finite permutation from Batteries'
`List.Perm.idxBij`, a canonical bijection between the positions of permuted
lists.
-/
theorem permutativeEquality_of_list_perm_entries {X : Type u} {x y : Tuple X}
    (hperm : (List.ofFn fun i : Fin x.length => Tuple.entry x i).Perm
      (List.ofFn fun j : Fin y.length => Tuple.entry y j)) :
    PermutativeEquality x y := by
  classical
  cases x with
  | mk n f =>
      cases y with
      | mk m g =>
          have hlen : n = m := by
            have := hperm.length_eq
            simpa [Tuple.length, Tuple.entry] using this
          subst m
          let toG : Fin n → Fin (List.ofFn g).length := Fin.cast (by simp)
          let fromG : Fin (List.ofFn g).length → Fin n := Fin.cast (by simp)
          let toF : Fin n → Fin (List.ofFn f).length := Fin.cast (by simp)
          let fromF : Fin (List.ofFn f).length → Fin n := Fin.cast (by simp)
          let π : Equiv.Perm (Fin n) :=
            { toFun := fun i => fromF (hperm.symm.idxBij (toG i))
              invFun := fun i => fromG (hperm.idxBij (toF i))
              left_inv := by
                intro i
                apply Fin.ext
                have hidx := hperm.idxBij_idxBij_symm (i := toG i)
                simpa [toG, fromG, toF, fromF] using congrArg Fin.val hidx
              right_inv := by
                intro i
                apply Fin.ext
                have hidx := hperm.idxBij_symm_idxBij (i := toF i)
                simpa [toG, fromG, toF, fromF] using congrArg Fin.val hidx }
          refine ⟨π, ?_⟩
          change (Sigma.mk n g : Tuple X) = permute (Sigma.mk n f : Tuple X) π
          congr
          funext i
          have hget := hperm.getElem_idxBij_symm_eq_getElem (toG i)
          have hleft := List.get_ofFn f (hperm.symm.idxBij (toG i))
          have hleft' : (List.ofFn f).get (hperm.symm.idxBij (toG i)) =
              f (fromF (hperm.symm.idxBij (toG i))) := by
            simpa [fromF] using hleft
          have hright := List.get_ofFn g (toG i)
          have hright' : (List.ofFn g).get (toG i) = g i := by
            simp [toG]
          have hfg : f (fromF (hperm.symm.idxBij (toG i))) = g i := by
            rw [← hleft', ← hright']
            exact hget
          simpa [π, toG, fromF, permute, Tuple.entry, Tuple.length] using hfg.symm

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `prop:permuted-tuple-measure-map-bijective`.

Original label: injective normal form for
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: under singleton measurability, two tuples induce the same
finite integer-valued measure exactly when they are equal up to permutation.
-/
theorem tupleInducedIntegerMeasure_eq_iff_permutativeEquality {X : Type u}
    [MeasurableSpace X] [MeasurableSingletonClass X] {x y : Tuple X} :
    tupleInducedIntegerMeasure x = tupleInducedIntegerMeasure y ↔
      PermutativeEquality x y := by
  constructor
  · intro h
    exact permutativeEquality_of_list_perm_entries
      ((tupleInducedIntegerMeasure_eq_iff_list_perm_entries).mp h)
  · exact tupleInducedIntegerMeasure_eq_of_permutativeEquality

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:permuted-tuple-measure-map-bijective`.

Original label: well-defined map in
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: because the tuple-induced measure is invariant under
permutation, it descends to a map from permuted tuple classes to finite
integer-valued measures.

Lean strategy / thesis relation note: this is the well-definedness half of the thesis map
`\mathfrak{m}^{\pi}`. The later bijection proof still needs the converse
statement that equal induced measures determine the same permutative class.
-/
noncomputable def permutedTupleInducedIntegerMeasure {X : Type u}
    [MeasurableSpace X] :
    PermutedTupleQuotientSpace X → FiniteIntegerMeasures X :=
  Quot.lift tupleInducedIntegerMeasure
    (fun _ _ hxy => tupleInducedIntegerMeasure_eq_of_permutativeEquality hxy)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:permuted-tuple-measure-map-bijective`.

Original label: representative formula for
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: the descended map sends the class of `x` to the finite
integer-valued measure induced by `x`.
-/
theorem permutedTupleInducedIntegerMeasure_mk {X : Type u}
    [MeasurableSpace X] (x : Tuple X) :
    permutedTupleInducedIntegerMeasure
      (Quot.mk (permutativeSetoid X) x) =
        tupleInducedIntegerMeasure x :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:permuted-tuple-measure-map-bijective`.

Original label: injective half of
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: the descended tuple-measure map on permuted tuple classes
is injective.

Lean strategy / thesis relation note: the full thesis proposition is
bijectivity. This theorem closes the injective half; the surjective half still
depends on the cited atomic decomposition theorem for arbitrary finite
integer-valued measures.
-/
theorem permutedTupleInducedIntegerMeasure_injective {X : Type u}
    [MeasurableSpace X] [MeasurableSingletonClass X] :
    Function.Injective (permutedTupleInducedIntegerMeasure (X := X)) := by
  intro q r hqr
  refine Quot.induction_on₂ q r ?_ hqr
  intro x y hxy
  apply Quot.sound
  exact (tupleInducedIntegerMeasure_eq_iff_permutativeEquality).mp hxy

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:permuted-tuple-measure-map-bijective`.

Original label: surjective half of
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: assuming the cited atomic-decomposition theorem, the
descended tuple-measure map from permuted tuple classes is surjective.
-/
theorem permutedTupleInducedIntegerMeasure_surjective_of_forall_atomicDecomposition
    {X : Type u} [MeasurableSpace X]
    (hdec : ∀ μ : FiniteIntegerMeasures X, AtomicDecomposition μ) :
    Function.Surjective (permutedTupleInducedIntegerMeasure (X := X)) := by
  intro μ
  rcases tupleInducedIntegerMeasure_surjective_of_atomicDecomposition
      (hdec μ) with ⟨x, hx⟩
  refine ⟨Quot.mk (permutativeSetoid X) x, ?_⟩
  simpa [permutedTupleInducedIntegerMeasure_mk] using hx

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:permuted-tuple-measure-map-bijective`.

Original label: surjective half of
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: on a standard Borel space, the descended tuple-measure map
from permuted tuple classes is surjective.
-/
theorem permutedTupleInducedIntegerMeasure_surjective_standardBorel
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X] :
    Function.Surjective (permutedTupleInducedIntegerMeasure (X := X)) :=
  permutedTupleInducedIntegerMeasure_surjective_of_forall_atomicDecomposition
    finiteIntegerMeasure_atomicDecomposition

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:permuted-tuple-measure-map-bijective`.

Original label: conditional form of
`prop:permuted-tuple-measure-map-bijective`.

Informal statement: assuming the cited atomic-decomposition theorem, the
descended tuple-measure map is bijective.

Lean strategy / thesis relation note: the injective half is fully constructive and proved above.
The surjective half is conditional on the same background theorem invoked in
the thesis proof of `prop:tuple-measure-surjective`.
-/
theorem permutedTupleInducedIntegerMeasure_bijective_of_forall_atomicDecomposition
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (hdec : ∀ μ : FiniteIntegerMeasures X, AtomicDecomposition μ) :
    Function.Bijective (permutedTupleInducedIntegerMeasure (X := X)) :=
  ⟨permutedTupleInducedIntegerMeasure_injective,
    permutedTupleInducedIntegerMeasure_surjective_of_forall_atomicDecomposition hdec⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:permuted-tuple-measure-map-bijective`.

Original label: `prop:permuted-tuple-measure-map-bijective`.

Informal statement: on a standard Borel space with measurable singletons, the
map from permuted tuple classes to finite integer-valued measures is bijective.

Lean strategy / thesis relation note: the standard-Borel axiom supplies surjectivity via atomic
decomposition. The `MeasurableSingletonClass` hypothesis is the singleton
measurability used in the injective proof when reading off multiplicities
from the values on `{a}`. In the thesis' complete/separable metric setting,
this singleton measurability is automatic for the Borel measurable space.
-/
theorem permutedTupleInducedIntegerMeasure_bijective_standardBorel
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] :
    Function.Bijective (permutedTupleInducedIntegerMeasure (X := X)) :=
  permutedTupleInducedIntegerMeasure_bijective_of_forall_atomicDecomposition
    finiteIntegerMeasure_atomicDecomposition

/-! ## Grouped Representatives from the Disintegration Lemma -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: audit-facing import bridge for `lem:disintegration-lemma`.

Informal statement: the direct point-process disintegration theorem gives the
mass equality, pairwise disjointness, and proximity conclusions for the sets
`L_k` used below.

Lean strategy / thesis strategy note: the full proof is in `PointProcesses.lean` as
`atomicDecomposition_disintegration_of_lt_separationGamma`. This wrapper keeps
the later tuple-measure file explicit about which labelled lemma it consumes.
-/
theorem tupleMeasures_disintegrationLemma
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε)
    (hεγ : ε < atomicDecompositionSeparationGamma dξ)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε) :
    (∀ k : Fin dξ.length,
      dξ.multiplicity k =
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l) ∧
    (∀ k k' : Fin dξ.length, k ≠ k' →
      Disjoint (nearbyAtomIndices dη (dξ.atom k) ε)
        (nearbyAtomIndices dη (dξ.atom k') ε)) ∧
    (∀ k : Fin dξ.length, ∀ l : Fin dη.length,
      l ∈ nearbyAtomIndices dη (dξ.atom k) ε →
        edist (dξ.atom k) (dη.atom l) < ε) :=
  atomicDecomposition_disintegration_of_lt_separationGamma
    dξ dη hε_pos hεγ hρ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:measures-coincide`.

Original label: audit-facing import bridge for `cor:measures-coincide`.

Informal statement: Prokhorov distance below `1` forces equality of the total
multiplicities in any two atomic decompositions.

Lean strategy / thesis strategy note: the direct proof is in `PointProcesses.lean` as
`atomicDecomposition_totalMultiplicity_eq_of_prokhorovEDistance_lt_one`; this
file uses the result when proving the inverse tuple-measure continuity estimate.
-/
theorem tupleMeasures_totalMultiplicity_eq_of_prokhorovEDistance_lt_one
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    (hρ : prokhorovEDistance ξ.1 η.1 < 1) :
    (∑ k : Fin dξ.length, dξ.multiplicity k) =
      ∑ l : Fin dη.length, dη.multiplicity l :=
  atomicDecomposition_totalMultiplicity_eq_of_prokhorovEDistance_lt_one
    dξ dη hρ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: enumeration of the sets `L_k` in the proof of
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: enumerate every pair `(k,l)` with
`l ∈ L_k`, repeating the pair `α_l` times. This is the Lean version of
choosing enumerations `L_k = {l_{k,1},...,l_{k,m_k}}` and then filling each
subblock according to the multiplicity `α_l`.

Lean strategy / thesis relation note: the thesis chooses arbitrary finite enumerations. Lean uses
`Finset.toList`; the eventual quotient statement is insensitive to this
choice because tuple order is quotiented by permutative equality.
-/
noncomputable def disintegrationGroupedIndexList {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    (ε : ℝ≥0∞) : List (Fin dξ.length × Fin dη.length) :=
  (List.finRange dξ.length).flatMap fun k =>
    (nearbyAtomIndices dη (dξ.atom k) ε).toList.flatMap fun l =>
      List.replicate (dη.multiplicity l) (k, l)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: membership property of the grouped enumeration.

Informal statement: every pair appearing in the grouped list really has
second coordinate in the corresponding nearby set `L_k`.
-/
theorem mem_disintegrationGroupedIndexList_nearby {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    (ε : ℝ≥0∞) {p : Fin dξ.length × Fin dη.length}
    (hp : p ∈ disintegrationGroupedIndexList dξ dη ε) :
    p.2 ∈ nearbyAtomIndices dη (dξ.atom p.1) ε := by
  classical
  unfold disintegrationGroupedIndexList at hp
  rcases List.mem_flatMap.mp hp with ⟨k, _hk, hpblock⟩
  rcases List.mem_flatMap.mp hpblock with ⟨l, hl, hrep⟩
  have hp_eq : p = (k, l) := List.eq_of_mem_replicate hrep
  subst p
  simpa using (Finset.mem_toList.mp hl)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: the reference tuple in the grouped construction.

Informal statement: replace each grouped pair `(k,l)` by the reference atom
`x_k`. This is the tuple denoted `x_0` after it has been subdivided according
to the nearby sets `L_k`.
-/
noncomputable def disintegrationReferenceTuple {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    (ε : ℝ≥0∞) : Tuple X :=
  tupleOfListMap (disintegrationGroupedIndexList dξ dη ε)
    fun p => dξ.atom p.1

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: the nearby tuple in the grouped construction.

Informal statement: replace each grouped pair `(k,l)` by the nearby atom
`y_l`. This is the thesis tuple `x` built blockwise from the disjoint sets
`L_k`.
-/
noncomputable def disintegrationNearbyTuple {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    (ε : ℝ≥0∞) : Tuple X :=
  tupleOfListMap (disintegrationGroupedIndexList dξ dη ε)
    fun p => dη.atom p.2

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: coordinate estimate after constructing the grouped tuple.

Informal statement: every coordinate of the grouped nearby tuple lies within
`ε` of the corresponding coordinate of the grouped reference tuple.

Lean strategy / thesis relation note: this is the formal version of the thesis line
`d(x(i),x_0(i)) < δ`: a coordinate is represented by some pair `(k,l)` in
the grouped list, and membership in that list implies `l ∈ L_k`.
-/
theorem disintegrationNearbyTuple_coordinatewise_edist_lt {X : Type u}
    [MeasurableSpace X] [EMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞}
    (hnear : ∀ k : Fin dξ.length, ∀ l : Fin dη.length,
      l ∈ nearbyAtomIndices dη (dξ.atom k) ε →
        edist (dξ.atom k) (dη.atom l) < ε)
    (i : Fin (disintegrationReferenceTuple dξ dη ε).length) :
    edist
      (Tuple.entry (disintegrationNearbyTuple dξ dη ε) i)
      (Tuple.entry (disintegrationReferenceTuple dξ dη ε) i) < ε := by
  let pairs := disintegrationGroupedIndexList dξ dη ε
  let p := pairs.get i
  have hp : p ∈ disintegrationGroupedIndexList dξ dη ε := by
    have hpairs : p ∈ pairs := List.get_mem pairs i
    simpa [pairs] using hpairs
  have hp_near : p.2 ∈ nearbyAtomIndices dη (dξ.atom p.1) ε :=
    mem_disintegrationGroupedIndexList_nearby dξ dη ε hp
  have hdist : edist (dξ.atom p.1) (dη.atom p.2) < ε :=
    hnear p.1 p.2 hp_near
  simpa [disintegrationNearbyTuple, disintegrationReferenceTuple,
    tupleOfListMap, Tuple.entry, pairs, p, edist_comm] using hdist

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: reference-side measure identity in the grouped construction.

Informal statement: if the disintegration lemma gives
`β_k = \sum_{l\in L_k} α_l`, then the grouped reference tuple, which replaces
each pair `(k,l)` by `x_k`, induces the original reference measure `ξ`.

Lean strategy / thesis relation note: the thesis treats this as immediate from the block lengths.
Lean expands the flattened list and checks the finite sums block by block.
-/
theorem tupleInducedIntegerMeasure_disintegrationReferenceTuple {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞}
    (hcount : ∀ k : Fin dξ.length,
      dξ.multiplicity k =
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l) :
    tupleInducedIntegerMeasure (disintegrationReferenceTuple dξ dη ε) = ξ := by
  classical
  apply Subtype.ext
  apply FiniteMeasure.eq_of_forall_apply_eq
  intro B hB
  rw [tupleInducedIntegerMeasure_apply _ hB]
  rw [disintegrationReferenceTuple, tupleOfListMap_sum_indicator]
  rw [← dξ.represents]
  rw [finiteAtomicMeasure_apply dξ.atom dξ.multiplicity hB]
  unfold disintegrationGroupedIndexList
  rw [List.map_flatMap, list_sum_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [List.map_flatMap, list_sum_flatMap]
  by_cases hx : dξ.atom k ∈ B
  · simp [hx, List.sum_replicate, nsmul_eq_mul, hcount k]
  · simp [hx, List.sum_replicate]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: nearby-side measure identity in the grouped construction.

Informal statement: if the sets `L_k` form a partition of the atoms of `η`,
then the grouped nearby tuple, which replaces each pair `(k,l)` by `y_l`,
induces exactly the nearby measure `η`.

Lean strategy / thesis relation note: the thesis obtains this partition from the disjointness and
mass-counting conclusions of `lem:disintegration-lemma`. This theorem states
the partition property as the exact-cover hypothesis used by the finite-sum
calculation.
-/
theorem tupleInducedIntegerMeasure_disintegrationNearbyTuple_of_unique_cover
    {X : Type u} [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞}
    (hcover : ∀ l : Fin dη.length,
      ∃! k : Fin dξ.length, l ∈ nearbyAtomIndices dη (dξ.atom k) ε) :
    tupleInducedIntegerMeasure (disintegrationNearbyTuple dξ dη ε) = η := by
  classical
  apply Subtype.ext
  apply FiniteMeasure.eq_of_forall_apply_eq
  intro B hB
  rw [tupleInducedIntegerMeasure_apply _ hB]
  rw [disintegrationNearbyTuple, tupleOfListMap_sum_indicator]
  rw [← dη.represents]
  rw [finiteAtomicMeasure_apply dη.atom dη.multiplicity hB]
  unfold disintegrationGroupedIndexList
  rw [List.map_flatMap, list_sum_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  calc
    (∑ k : Fin dξ.length,
      (((nearbyAtomIndices dη (dξ.atom k) ε).toList.flatMap fun l =>
        List.replicate (dη.multiplicity l) (k, l)).map
          (fun p =>
            B.indicator (fun _ : X => (1 : ℝ≥0)) (dη.atom p.2))).sum)
        =
          ∑ k : Fin dξ.length,
            ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
              B.indicator
                (fun _ : X => (dη.multiplicity l : ℝ≥0)) (dη.atom l) := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [List.map_flatMap, list_sum_flatMap]
          simp only [List.map_replicate, List.sum_replicate, nsmul_eq_mul,
            Finset.sum_map_toList]
          apply Finset.sum_congr rfl
          intro l _hl
          by_cases hmem : dη.atom l ∈ B
          · simp [hmem]
          · simp [hmem]
    _ = ∑ l : Fin dη.length,
          B.indicator
            (fun _ : X => (dη.multiplicity l : ℝ≥0)) (dη.atom l) := by
          exact Finset.sum_sum_mem_eq_sum_of_unique_cover
            (fun k : Fin dξ.length =>
              nearbyAtomIndices dη (dξ.atom k) ε)
            (fun l : Fin dη.length =>
              B.indicator
                (fun _ : X => (dη.multiplicity l : ℝ≥0)) (dη.atom l))
            hcover

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: exact-cover bridge for the sets `L_k`.

Informal statement: the multiplicity equality for each `L_k`, pairwise
disjointness of the `L_k`, equality of total multiplicities, and positivity
of atomic multiplicities imply that every atom index of `η` lies in exactly
one `L_k`.

Lean strategy / thesis relation note: this makes explicit the finite partition step that the thesis
uses when passing from the disintegration lemma to the blockwise tuple
representative.
-/
theorem nearbyAtomIndices_unique_cover_of_disintegration {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞}
    (hcount : ∀ k : Fin dξ.length,
      dξ.multiplicity k =
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l)
    (hdisj : ∀ k k' : Fin dξ.length, k ≠ k' →
      Disjoint (nearbyAtomIndices dη (dξ.atom k) ε)
        (nearbyAtomIndices dη (dξ.atom k') ε))
    (htotal : (∑ k : Fin dξ.length, dξ.multiplicity k) =
      ∑ l : Fin dη.length, dη.multiplicity l) :
    ∀ l : Fin dη.length,
      ∃! k : Fin dξ.length,
        l ∈ nearbyAtomIndices dη (dξ.atom k) ε := by
  classical
  apply Finset.unique_cover_of_disjoint_of_sum_eq
  · intro l
    exact dη.multiplicity_pos l
  · exact hdisj
  · calc
      (∑ k : Fin dξ.length,
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l)
          = ∑ k : Fin dξ.length, dξ.multiplicity k := by
            apply Finset.sum_congr rfl
            intro k _hk
            exact (hcount k).symm
      _ = ∑ l : Fin dη.length, dη.multiplicity l := htotal

/-! ## Inverse Map on Permuted Tuples -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: inverse map `( \mathfrak m^\pi )^{-1}` used in
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: choose an atomic decomposition of a finite integer-valued
measure, expand it into a tuple by repeating each atom according to its
multiplicity, and then pass to the permuted-tuple quotient.

Lean strategy / thesis relation note: the thesis writes the inverse using the bijection already
proved. Lean makes the choice explicit through the cited atomic-decomposition
axiom `finiteIntegerMeasure_atomicDecomposition`.
-/
noncomputable def inversePermutedTupleMeasure {X : Type u}
    [MeasurableSpace X] [StandardBorelSpace X] :
    FiniteIntegerMeasures X → PermutedTupleQuotientSpace X := fun μ =>
  Quot.mk (permutativeSetoid X)
    (tupleOfAtomicDecomposition (finiteIntegerMeasure_atomicDecomposition μ))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: right-inverse identity for
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: applying the descended tuple-measure map to the chosen
inverse representative returns the original finite integer-valued measure.
-/
theorem permutedTupleInducedIntegerMeasure_inversePermutedTupleMeasure
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : FiniteIntegerMeasures X) :
    permutedTupleInducedIntegerMeasure (inversePermutedTupleMeasure μ) = μ := by
  simp [inversePermutedTupleMeasure, permutedTupleInducedIntegerMeasure_mk,
    tupleInducedIntegerMeasure_tupleOfAtomicDecomposition]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: left-inverse identity for
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: after quotienting by permutations, the chosen inverse of
the induced measure of a quotient class returns that quotient class.

Lean strategy / thesis relation note: this is where Lean uses the injective half of
`prop:permuted-tuple-measure-map-bijective`; the thesis treats the inverse as
already determined by bijectivity.
-/
theorem inversePermutedTupleMeasure_permutedTupleInducedIntegerMeasure
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] (q : PermutedTupleQuotientSpace X) :
    inversePermutedTupleMeasure (permutedTupleInducedIntegerMeasure q) = q := by
  apply permutedTupleInducedIntegerMeasure_injective
  rw [permutedTupleInducedIntegerMeasure_inversePermutedTupleMeasure]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: final epsilon step in
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: if `ξ` and `η` have fixed-length tuple representatives
whose matching coordinates are all within `ε`, then the chosen inverse
permuted-tuple classes of `ξ` and `η` are within `ε`.

Lean strategy / thesis relation note: this packages the last displayed calculation in the thesis.
The remaining work for the full proposition is the preceding construction of
the coordinatewise-close representative of `η` from the sets `L_k` supplied by
`lem:disintegration-lemma`.
-/
theorem inversePermutedTupleMeasure_edist_lt_of_coordinatewise_representatives
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X]
    {ξ η : FiniteIntegerMeasures X} {n : ℕ} {x y : Fin n → X}
    {ε : ℝ≥0∞} (hε_pos : 0 < ε)
    (hx : permutedTupleInducedIntegerMeasure
      (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X)) = ξ)
    (hy : permutedTupleInducedIntegerMeasure
      (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X)) = η)
    (hxy : ∀ i : Fin n, edist (x i) (y i) < ε) :
    edist (inversePermutedTupleMeasure ξ)
      (inversePermutedTupleMeasure η) < ε := by
  have hxinv :
      inversePermutedTupleMeasure ξ =
        Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X) := by
    rw [← hx]
    exact inversePermutedTupleMeasure_permutedTupleInducedIntegerMeasure _
  have hyinv :
      inversePermutedTupleMeasure η =
        Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X) := by
    rw [← hy]
    exact inversePermutedTupleMeasure_permutedTupleInducedIntegerMeasure _
  rw [hxinv, hyinv]
  change permutedTupleHausdorffEDistance
      (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X))
      (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X)) < ε
  exact permutedTupleHausdorffEDistance_mk_mk_lt_of_forall_edist_lt
    hε_pos hxy

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: grouped-representative epsilon step in
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: once the disintegration sets `L_k` preserve the
reference multiplicities, partition the nearby atoms, and place each selected
nearby atom within `ε` of its reference atom, the inverse map on permuted
tuples moves `ξ` to `η` by less than `ε`.

Lean strategy / thesis relation note: this is the thesis' blockwise construction of the tuple `x`
from the sets `L_k`, followed by the displayed Hausdorff-distance estimate.
The only remaining bridge to the full proposition is deriving the exact-cover
hypothesis from the mass-counting and pairwise-disjoint conclusions of
`lem:disintegration-lemma`.
-/
theorem inversePermutedTupleMeasure_edist_lt_of_disintegration_grouped
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε)
    (hcount : ∀ k : Fin dξ.length,
      dξ.multiplicity k =
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l)
    (hcover : ∀ l : Fin dη.length,
      ∃! k : Fin dξ.length, l ∈ nearbyAtomIndices dη (dξ.atom k) ε)
    (hnear : ∀ k : Fin dξ.length, ∀ l : Fin dη.length,
      l ∈ nearbyAtomIndices dη (dξ.atom k) ε →
        edist (dξ.atom k) (dη.atom l) < ε) :
    edist (inversePermutedTupleMeasure ξ)
      (inversePermutedTupleMeasure η) < ε := by
  classical
  let pairs := disintegrationGroupedIndexList dξ dη ε
  let x : Fin pairs.length → X := fun i => dξ.atom (pairs.get i).1
  let y : Fin pairs.length → X := fun i => dη.atom (pairs.get i).2
  have hx :
      permutedTupleInducedIntegerMeasure
        (Quot.mk (permutativeSetoid X) (Sigma.mk pairs.length x : Tuple X)) =
          ξ := by
    have hmeasure :=
      tupleInducedIntegerMeasure_disintegrationReferenceTuple dξ dη hcount
    simpa [permutedTupleInducedIntegerMeasure_mk,
      disintegrationReferenceTuple, tupleOfListMap, pairs, x] using hmeasure
  have hy :
      permutedTupleInducedIntegerMeasure
        (Quot.mk (permutativeSetoid X) (Sigma.mk pairs.length y : Tuple X)) =
          η := by
    have hmeasure :=
      tupleInducedIntegerMeasure_disintegrationNearbyTuple_of_unique_cover
        dξ dη hcover
    simpa [permutedTupleInducedIntegerMeasure_mk,
      disintegrationNearbyTuple, tupleOfListMap, pairs, y] using hmeasure
  have hxy : ∀ i : Fin pairs.length, edist (x i) (y i) < ε := by
    intro i
    let p := pairs.get i
    have hp : p ∈ disintegrationGroupedIndexList dξ dη ε := by
      have hpairs : p ∈ pairs := List.get_mem pairs i
      simpa [pairs] using hpairs
    have hp_near : p.2 ∈ nearbyAtomIndices dη (dξ.atom p.1) ε :=
      mem_disintegrationGroupedIndexList_nearby dξ dη ε hp
    have hdist : edist (dξ.atom p.1) (dη.atom p.2) < ε :=
      hnear p.1 p.2 hp_near
    simpa [x, y, p] using hdist
  exact inversePermutedTupleMeasure_edist_lt_of_coordinatewise_representatives
    hε_pos hx hy hxy

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: disintegration-output epsilon step.

Informal statement: the three conclusions of `lem:disintegration-lemma`,
together with equality of total multiplicities, give the grouped
representative estimate for the inverse tuple-measure map.

Lean strategy / thesis relation note: this packages the exact-cover bridge separately from the
metric construction so the proof follows the manuscript order: first
disintegrate the atoms, then build the tuple representative.
-/
theorem inversePermutedTupleMeasure_edist_lt_of_disintegration_outputs
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε)
    (hcount : ∀ k : Fin dξ.length,
      dξ.multiplicity k =
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l)
    (hdisj : ∀ k k' : Fin dξ.length, k ≠ k' →
      Disjoint (nearbyAtomIndices dη (dξ.atom k) ε)
        (nearbyAtomIndices dη (dξ.atom k') ε))
    (htotal : (∑ k : Fin dξ.length, dξ.multiplicity k) =
      ∑ l : Fin dη.length, dη.multiplicity l)
    (hnear : ∀ k : Fin dξ.length, ∀ l : Fin dη.length,
      l ∈ nearbyAtomIndices dη (dξ.atom k) ε →
        edist (dξ.atom k) (dη.atom l) < ε) :
    edist (inversePermutedTupleMeasure ξ)
      (inversePermutedTupleMeasure η) < ε := by
  have hcover :
      ∀ l : Fin dη.length,
        ∃! k : Fin dξ.length,
          l ∈ nearbyAtomIndices dη (dξ.atom k) ε :=
    nearbyAtomIndices_unique_cover_of_disintegration
      dξ dη hcount hdisj htotal
  exact inversePermutedTupleMeasure_edist_lt_of_disintegration_grouped
    dξ dη hε_pos hcount hcover hnear

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: local Prokhorov-to-quotient estimate for
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: if `η` is within Prokhorov distance `< ε` of `ξ`, and
`ε` lies below the finite separation radius `γ` of an atomic decomposition of
`ξ`, then the inverse permuted-tuple representatives are within `ε`.

Lean strategy / thesis relation note: this is the main local estimate in the thesis proof. Lean uses
`cor:measures-coincide` to get equality of total multiplicities, then applies
`lem:disintegration-lemma` and the grouped representative construction above.
-/
theorem inversePermutedTupleMeasure_edist_lt_of_lt_separationGamma
    {X : Type u}
    [MeasurableSpace X] [StandardBorelSpace X] [EMetricSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε)
    (hεγ : ε < atomicDecompositionSeparationGamma dξ)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε) :
    edist (inversePermutedTupleMeasure ξ)
      (inversePermutedTupleMeasure η) < ε := by
  rcases atomicDecomposition_disintegration_of_lt_separationGamma
      dξ dη hε_pos hεγ hρ with ⟨hcount, hdisj, hnear⟩
  have hε_lt_one : ε < 1 :=
    lt_of_lt_of_le hεγ (atomicDecompositionSeparationGamma_le_one dξ)
  have hρ_one : prokhorovEDistance ξ.1 η.1 < 1 :=
    lt_trans hρ hε_lt_one
  have htotal :
      (∑ k : Fin dξ.length, dξ.multiplicity k) =
        ∑ l : Fin dη.length, dη.multiplicity l :=
    atomicDecomposition_totalMultiplicity_eq_of_prokhorovEDistance_lt_one
      dξ dη hρ_one
  exact inversePermutedTupleMeasure_edist_lt_of_disintegration_outputs
    dξ dη hε_pos hcount hdisj htotal hnear

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: epsilon-radius form of the inverse continuity proof.

Informal statement: if the Prokhorov distance from `ξ` to `η` is less than
both the target radius `ε` and the separation radius `γ` of `ξ`, then the
inverse permuted-tuple classes are within `ε`.

Lean strategy / thesis relation note: the proof inserts an intermediate radius `r`, exactly as in an
epsilon-delta argument, so that `ρ(ξ,η) < r < min(ε,γ)` and the local
disintegration theorem can be applied with radius `r`.
-/
theorem inversePermutedTupleMeasure_edist_lt_of_prokhorovEDistance_lt_min
    {X : Type u}
    [MeasurableSpace X] [StandardBorelSpace X] [EMetricSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ)
    {ε : ℝ≥0∞}
    (hρ : prokhorovEDistance ξ.1 η.1 <
      min ε (atomicDecompositionSeparationGamma dξ)) :
    edist (inversePermutedTupleMeasure ξ)
      (inversePermutedTupleMeasure η) < ε := by
  rcases exists_between hρ with ⟨r, hρr, hr_min⟩
  have hr_pos : 0 < r := lt_of_le_of_lt bot_le hρr
  have hrε : r < ε := lt_of_lt_of_le hr_min (min_le_left ε _)
  have hrγ : r < atomicDecompositionSeparationGamma dξ :=
    lt_of_lt_of_le hr_min (min_le_right ε _)
  have hlocal :
      edist (inversePermutedTupleMeasure ξ)
        (inversePermutedTupleMeasure η) < r :=
    inversePermutedTupleMeasure_edist_lt_of_lt_separationGamma
      dξ (finiteIntegerMeasure_atomicDecomposition η) hr_pos hrγ hρr
  exact lt_trans hlocal hrε

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: `prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: at every finite integer-valued measure `ξ`, the inverse
map from integer measures to permuted tuple classes is epsilon-delta
continuous from the Prokhorov distance to the permuted tuple Hausdorff
extended distance.

Lean strategy / thesis relation note: rather than installing a global metric instance on the subtype
`FiniteIntegerMeasures X`, Lean states the metric continuity estimate
directly using the thesis distances: Prokhorov distance in the domain and
permuted tuple Hausdorff edistance in the codomain.
-/
theorem inversePermutedTupleMeasure_epsilon_delta_at
    {X : Type u}
    [MeasurableSpace X] [StandardBorelSpace X] [EMetricSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (ξ : FiniteIntegerMeasures X) (dξ : AtomicDecomposition ξ) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ δ : ℝ≥0∞, 0 < δ ∧
        ∀ η : FiniteIntegerMeasures X,
          prokhorovEDistance ξ.1 η.1 < δ →
            edist (inversePermutedTupleMeasure ξ)
              (inversePermutedTupleMeasure η) < ε := by
  intro ε hε_pos
  let δ := min ε (atomicDecompositionSeparationGamma dξ)
  have hδ_pos : 0 < δ := by
    exact lt_min hε_pos (atomicDecompositionSeparationGamma_pos dξ)
  refine ⟨δ, hδ_pos, ?_⟩
  intro η hρη
  exact inversePermutedTupleMeasure_edist_lt_of_prokhorovEDistance_lt_min
    dξ hρη

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: decomposition-free statement of
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: the inverse map from finite integer-valued measures to
permuted tuple classes is epsilon-delta continuous at every measure.

Lean strategy / thesis strategy note: the preceding theorem proves the thesis epsilon-delta
argument relative to an atomic decomposition of the base measure. This wrapper
uses the external standard-Borel atomic-decomposition theorem, matching the
proposition as stated in the manuscript.
-/
theorem inversePermutedTupleMeasure_epsilon_delta
    {X : Type u}
    [MeasurableSpace X] [StandardBorelSpace X] [EMetricSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (ξ : FiniteIntegerMeasures X) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ δ : ℝ≥0∞, 0 < δ ∧
        ∀ η : FiniteIntegerMeasures X,
          prokhorovEDistance ξ.1 η.1 < δ →
            edist (inversePermutedTupleMeasure ξ)
              (inversePermutedTupleMeasure η) < ε :=
  inversePermutedTupleMeasure_epsilon_delta_at ξ
    (finiteIntegerMeasure_atomicDecomposition ξ)

/-! ## Homeomorphism Between Integer Measures and Permuted Tuples -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:integer-measures-tuples-homeomorphic`.

Original label: forward-continuity estimate used in
`thm:integer-measures-tuples-homeomorphic`.

Informal statement: if two permuted-tuple classes are close in the quotient
Hausdorff distance, then their induced integer-valued measures are close in
Prokhorov distance.

Lean strategy / thesis relation note: the thesis argues on quotient classes. Lean unfolds the
quotient distance as the Hausdorff distance between finite permutation
orbits. A close class therefore has a close representative in the other
orbit, and the already-proved tuple-level Prokhorov estimate applies because
tuple-induced measures are invariant under permutation.
-/
theorem permutedTupleInducedIntegerMeasure_prokhorovEDistance_lt_of_edist_lt_min
    {X : Type u} [MeasurableSpace X] [EMetricSpace X]
    [OpensMeasurableSpace X]
    {q r : PermutedTupleQuotientSpace X} {ε : ℝ≥0∞}
    (hqr : edist q r < min ε 1) :
    prokhorovEDistance (permutedTupleInducedIntegerMeasure q).1
      (permutedTupleInducedIntegerMeasure r).1 < ε := by
  refine Quot.induction_on₂ q r ?_ hqr
  intro x y hxy
  change edist (permutativeOrbit x) (permutativeOrbit y) <
    min ε 1 at hxy
  have hx_mem : x ∈ ((permutativeOrbit x).1 : Set (Tuple X)) := by
    change x ∈ permutativeClass x
    exact self_mem_permutativeClass x
  rcases Metric.exists_edist_lt_of_hausdorffEDist_lt hx_mem hxy with
    ⟨z, hz_mem, hxz⟩
  have hyz : PermutativeEquality y z := by
    change z ∈ permutativeClass y at hz_mem
    exact hz_mem
  have hzy :
      (tupleInducedIntegerMeasure z).1 =
        (tupleInducedIntegerMeasure y).1 := by
    exact congrArg Subtype.val
      (tupleInducedIntegerMeasure_eq_of_permutativeEquality
        (permutativeEquality_symm hyz))
  have hprox :
      prokhorovEDistance (tupleInducedIntegerMeasure x).1
        (tupleInducedIntegerMeasure z).1 < ε :=
    tupleInducedIntegerMeasure_prokhorovEDistance_lt_of_edist_lt_min hxz
  rw [hzy] at hprox
  simpa [permutedTupleInducedIntegerMeasure_mk] using hprox

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:integer-measures-tuples-homeomorphic`.

Original label: distance-form homeomorphism data for
`thm:integer-measures-tuples-homeomorphic`.

Informal statement: the descended tuple-measure map and the chosen inverse
map are inverse bijections, the forward map is epsilon-delta continuous from
permuted tuple Hausdorff distance to Prokhorov distance, and the inverse map
is epsilon-delta continuous in the reverse direction.

Lean strategy / thesis relation note: this is the theorem in the thesis' metric language. Lean keeps
the topological content as explicit epsilon-delta fields because the current
development has not installed a separate global topological-space instance on
the subtype `FiniteIntegerMeasures X`; the distances are exactly the thesis
distances.
-/
structure IntegerMeasuresPermutedTuplesHomeomorphismData
    (X : Type u) [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X] where
  toFun : PermutedTupleQuotientSpace X → FiniteIntegerMeasures X
  invFun : FiniteIntegerMeasures X → PermutedTupleQuotientSpace X
  right_inv : ∀ μ : FiniteIntegerMeasures X, toFun (invFun μ) = μ
  left_inv : ∀ q : PermutedTupleQuotientSpace X, invFun (toFun q) = q
  bijective : Function.Bijective toFun
  forward_epsilon_delta_at :
    ∀ q : PermutedTupleQuotientSpace X, ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ δ : ℝ≥0∞, 0 < δ ∧
        ∀ r : PermutedTupleQuotientSpace X, edist q r < δ →
          prokhorovEDistance (toFun q).1 (toFun r).1 < ε
  inverse_epsilon_delta_at :
    ∀ μ : FiniteIntegerMeasures X, ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ δ : ℝ≥0∞, 0 < δ ∧
        ∀ ν : FiniteIntegerMeasures X,
          prokhorovEDistance μ.1 ν.1 < δ →
            edist (invFun μ) (invFun ν) < ε

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:integer-measures-tuples-homeomorphic`.

Original label: `thm:integer-measures-tuples-homeomorphic`.

Informal statement: on a standard Borel ambient space with the thesis Borel
metric hypotheses, finite integer-valued measures with Prokhorov distance and
permuted tuple classes with quotient Hausdorff distance are homeomorphic via
the tuple-induced measure map.

Lean strategy / thesis relation note: the proof follows the manuscript: bijectivity comes from the
atomic-decomposition/surjectivity theorem and permutation-invariance
injectivity; forward continuity descends from tuple-level continuity through
finite permutation orbits; inverse continuity is the disintegration/separation
argument proved above.
-/
noncomputable def integerMeasuresPermutedTuples_homeomorphismData
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X] :
    IntegerMeasuresPermutedTuplesHomeomorphismData X where
  toFun := permutedTupleInducedIntegerMeasure
  invFun := inversePermutedTupleMeasure
  right_inv := permutedTupleInducedIntegerMeasure_inversePermutedTupleMeasure
  left_inv := inversePermutedTupleMeasure_permutedTupleInducedIntegerMeasure
  bijective := permutedTupleInducedIntegerMeasure_bijective_standardBorel
  forward_epsilon_delta_at := by
    intro q ε hε_pos
    refine ⟨min ε 1, lt_min hε_pos zero_lt_one, ?_⟩
    intro r hqr
    exact
      permutedTupleInducedIntegerMeasure_prokhorovEDistance_lt_of_edist_lt_min hqr
  inverse_epsilon_delta_at := by
    intro μ ε hε_pos
    exact inversePermutedTupleMeasure_epsilon_delta_at μ
      (finiteIntegerMeasure_atomicDecomposition μ) ε hε_pos

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:integer-measures-tuples-homeomorphic`.

Original label: `thm:integer-measures-tuples-homeomorphic`.

Informal statement: the thesis homeomorphism data exists for the descended
tuple-induced measure map and its chosen inverse.
-/
theorem integerMeasuresPermutedTuples_homeomorphic
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X] :
    ∃ H : IntegerMeasuresPermutedTuplesHomeomorphismData X,
      H.toFun = permutedTupleInducedIntegerMeasure ∧
        H.invFun = inversePermutedTupleMeasure := by
  exact ⟨integerMeasuresPermutedTuples_homeomorphismData, rfl, rfl⟩

/-!
## Measurable Enumeration Reference

The next thesis item, `lem:measurable-enumeration`, is not a thesis
contribution in the same sense as the homeomorphism above. The manuscript
cites Daley--Vere-Jones, *An Introduction to the Theory of Point Processes*,
Volume II, for a measurable enumeration of point-process atoms and then
adapts that enumeration to tuples by including multiplicities.
-/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:measurable-enumeration`.

Original label: `lem:measurable-enumeration`.

Informal statement: on a complete separable metric space, the atoms of a
finite point process can be measurably enumerated, with multiplicity, as a
tuple whose induced counting measure is the original point process.

External reference note: this is the cited measurable-enumeration theorem
from Daley--Vere-Jones, *An Introduction to the Theory of Point Processes*,
Volume II. The manuscript notes that their atom-enumeration statement is
equivalent to the tuple statement after repeating atoms according to
multiplicity. The Lean axiom records exactly that adapted consequence:
measurability into the thesis tuple Borel space and equality with
`tupleInducedIntegerMeasure`.

Lean strategy / thesis relation note: this axiom is kept in this module rather than
`Foundations.External` because its conclusion mentions
`tupleInducedIntegerMeasure`, which is defined here; placing it upstream would
create an import cycle. It is still explicit, citation-bearing external
background rather than a thesis proof.
-/
axiom daleyVereJones_measurableEnumeration
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    ∃ τ : FiniteIntegerMeasures X → Tuple X,
      @Measurable (FiniteIntegerMeasures X) (Tuple X)
        inferInstance (tupleHausdorffBorel (X := X)) τ ∧
      ∀ ξ : FiniteIntegerMeasures X, tupleInducedIntegerMeasure (τ ξ) = ξ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:measurable-enumeration`.

Original label: `lem:measurable-enumeration`.

Informal statement: there exists a measurable tuple enumeration of every
finite integer-valued measure, and the tuple induces the original measure.
-/
theorem exists_measurableEnumeration
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    ∃ τ : FiniteIntegerMeasures X → Tuple X,
      @Measurable (FiniteIntegerMeasures X) (Tuple X)
        inferInstance (tupleHausdorffBorel (X := X)) τ ∧
      ∀ ξ : FiniteIntegerMeasures X, tupleInducedIntegerMeasure (τ ξ) = ξ :=
  daleyVereJones_measurableEnumeration

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:measurable-enumeration`.

Original label: chosen enumeration map from `lem:measurable-enumeration`.

Informal statement: a fixed choice of the cited measurable enumeration map.
-/
noncomputable def measurableEnumeration
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    FiniteIntegerMeasures X → Tuple X :=
  Classical.choose (exists_measurableEnumeration (X := X))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:measurable-enumeration`.

Original label: measurability clause of `lem:measurable-enumeration`.

Informal statement: the chosen enumeration map is Borel measurable.
-/
theorem measurable_measurableEnumeration
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    @Measurable (FiniteIntegerMeasures X) (Tuple X)
      inferInstance (tupleHausdorffBorel (X := X))
      (measurableEnumeration (X := X)) :=
  (Classical.choose_spec (exists_measurableEnumeration (X := X))).1

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:measurable-enumeration`.

Original label: representative clause of `lem:measurable-enumeration`.

Informal statement: the tuple selected by the chosen measurable enumeration
induces the original finite integer-valued measure.
-/
theorem tupleInducedIntegerMeasure_measurableEnumeration
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (ξ : FiniteIntegerMeasures X) :
    tupleInducedIntegerMeasure (measurableEnumeration (X := X) ξ) = ξ :=
  (Classical.choose_spec (exists_measurableEnumeration (X := X))).2 ξ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:measurable-enumeration`.

Original label: quotient-inverse form of `lem:measurable-enumeration`.

Informal statement: the selected tuple represents a permuted tuple class that
maps back to the original finite integer-valued measure.
-/
theorem permutedTupleInducedIntegerMeasure_measurableEnumeration
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSingletonClass X] [EMetricSpace X] [OpensMeasurableSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (ξ : FiniteIntegerMeasures X) :
    permutedTupleInducedIntegerMeasure
      (Quot.mk (permutativeSetoid X) (measurableEnumeration (X := X) ξ)) =
        ξ := by
  simpa [permutedTupleInducedIntegerMeasure]
    using tupleInducedIntegerMeasure_measurableEnumeration (X := X) ξ

/-! ## Uniform Permutation Kernel, Fixed-Measure Part -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: finite permutation average in `thm:point-process-tuple`.

Informal statement: given a tuple `x`, put uniform mass on all tuples obtained
by permuting the finite domain of `x`.

Lean strategy / thesis relation note: the thesis writes
`(1/n!) \sum_{\pi \in \mathscr{P}_n} δ_{x \circ \pi}`. Lean uses the finite
type `FinitePermutation x.length`; its cardinality is `x.length!`, but the
proof only needs that this finite type is nonempty and finite.
-/
noncomputable def uniformPermutationMeasure {X : Type u}
    [MeasurableSpace (Tuple X)] (x : Tuple X) : Measure (Tuple X) :=
  ((Fintype.card (FinitePermutation x.length) : ℝ≥0∞)⁻¹) •
    ∑ π : FinitePermutation x.length, Measure.dirac (permute x π)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: factorial normalization in `thm:point-process-tuple`.

Informal statement: the finite type of permutations of an `n`-tuple has
cardinality `n!`, so the Lean normalizing factor in
`uniformPermutationMeasure` is the thesis factor `1 / n!`.
-/
theorem uniformPermutationMeasure_card_eq_factorial {X : Type u}
    [MeasurableSpace (Tuple X)] (x : Tuple X) :
    Fintype.card (FinitePermutation x.length) = x.length.factorial := by
  simp [FinitePermutation, Fintype.card_perm, Fintype.card_fin]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: fixed-length permutation maps used in
`thm:point-process-tuple`.

Informal statement: on a fixed tuple-length layer, permuting coordinates is
continuous for the thesis tuple Hausdorff topology.
-/
theorem continuous_fixedLength_permute_mk {X : Type u} [EMetricSpace X]
    {n : ℕ} (π : FinitePermutation n) :
    @Continuous (Fin n → X) (Tuple X) inferInstance
      (tupleHausdorffMetricTopology (X := X))
      (fun x : Fin n → X => permute (Sigma.mk n x : Tuple X) π) := by
  rw [tupleHausdorffMetricTopology_eq_tupleSup]
  rw [DisjointUnionTopology.metricTopology_eq_sigma]
  change Continuous
    (fun x : Fin n → X =>
      (Sigma.mk n (fun i : Fin n => x (π i)) : Tuple X))
  exact continuous_sigmaMk.comp
    (continuous_pi fun i => continuous_apply (π i))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: fixed-length measurable permutation maps used in
`thm:point-process-tuple`.

Informal statement: on a fixed tuple-length layer, permuting coordinates is
Borel measurable.
-/
theorem measurable_fixedLength_permute_mk {X : Type u} [EMetricSpace X]
    {n : ℕ} (π : FinitePermutation n) :
    @Measurable (Fin n → X) (Tuple X)
      (@borel (Fin n → X) inferInstance) (tupleHausdorffBorel (X := X))
      (fun x : Fin n → X => permute (Sigma.mk n x : Tuple X) π) := by
  letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : MeasurableSpace (Tuple X) :=
    @borel (Tuple X) (tupleHausdorffMetricTopology (X := X))
  haveI : BorelSpace (Fin n → X) := ⟨rfl⟩
  haveI : BorelSpace (Tuple X) := ⟨rfl⟩
  exact (continuous_fixedLength_permute_mk (X := X) π).measurable

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: finite permutation average in `thm:point-process-tuple`.

Informal statement: evaluating the uniform permutation measure on a
measurable set is the normalized finite sum of membership indicators over all
permutations.
-/
theorem uniformPermutationMeasure_apply {X : Type u}
    [MeasurableSpace (Tuple X)] (x : Tuple X)
    {B : Set (Tuple X)} (hB : MeasurableSet B) :
    uniformPermutationMeasure x B =
      ((Fintype.card (FinitePermutation x.length) : ℝ≥0∞)⁻¹) *
        ∑ π : FinitePermutation x.length,
          B.indicator (fun _ : Tuple X => (1 : ℝ≥0∞)) (permute x π) := by
  rw [uniformPermutationMeasure]
  change ((Fintype.card (FinitePermutation x.length) : ℝ≥0∞)⁻¹) *
      ((∑ π : FinitePermutation x.length, Measure.dirac (permute x π)) B) =
        _
  simp only [Measure.coe_finset_sum, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro π _hπ
  exact Measure.dirac_apply' (permute x π) hB

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: probability-measure part of `thm:point-process-tuple`.

Informal statement: the uniform permutation measure has total mass one.
-/
theorem uniformPermutationMeasure_univ {X : Type u}
    [MeasurableSpace (Tuple X)] (x : Tuple X) :
    uniformPermutationMeasure x Set.univ = 1 := by
  rw [uniformPermutationMeasure]
  change ((Fintype.card (FinitePermutation x.length) : ℝ≥0∞)⁻¹) *
      ((∑ π : FinitePermutation x.length, Measure.dirac (permute x π))
        Set.univ) = 1
  simp only [Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have h0 : (Fintype.card (FinitePermutation x.length) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (FinitePermutation x.length) ≠ 0)
  have htop : (Fintype.card (FinitePermutation x.length) : ℝ≥0∞) ≠ ∞ := by
    simp
  exact ENNReal.inv_mul_cancel h0 htop

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: probability-measure part of `thm:point-process-tuple`.

Informal statement: for a fixed point-process realization, the displayed
finite average over tuple permutations is a probability measure.
-/
theorem uniformPermutationMeasure_isProbabilityMeasure {X : Type u}
    [MeasurableSpace (Tuple X)] (x : Tuple X) :
    IsProbabilityMeasure (uniformPermutationMeasure x) :=
  ⟨uniformPermutationMeasure_univ x⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: measurability clause of `thm:point-process-tuple`.

Informal statement: the finite uniform average over all permutations of a tuple
depends measurably on the tuple.

Lean strategy / thesis relation note: the thesis proves this by checking the preimage/evaluation
formula on the finite tuple layers. Lean packages a measurable map into
`Measure (Tuple X)` by proving that evaluation on every measurable set is
measurable; the fixed-length layer reduction is exactly
`measurable_tupleHausdorff_iff_fixedLength`.
-/
theorem measurable_uniformPermutationMeasure {X : Type u} [EMetricSpace X] :
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    Measurable (uniformPermutationMeasure (X := X)) := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  refine Measure.measurable_of_measurable_coe _ ?_
  intro B hB
  rw [measurable_tupleHausdorff_iff_fixedLength]
  intro n
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  have hsum : Measurable fun x : Fin n → X =>
      ∑ π : FinitePermutation n,
        B.indicator (fun _ : Tuple X => (1 : ℝ≥0∞))
          (permute (Sigma.mk n x : Tuple X) π) := by
    apply Finset.measurable_sum
    intro π _hπ
    exact (measurable_const.indicator hB).comp
      (measurable_fixedLength_permute_mk (X := X) π)
  have hmul : Measurable fun x : Fin n → X =>
      ((Fintype.card (FinitePermutation n) : ℝ≥0∞)⁻¹) *
        ∑ π : FinitePermutation n,
          B.indicator (fun _ : Tuple X => (1 : ℝ≥0∞))
            (permute (Sigma.mk n x : Tuple X) π) := by
    exact measurable_const.mul hsum
  convert hmul using 1
  funext x
  rw [uniformPermutationMeasure_apply (x := (Sigma.mk n x : Tuple X)) hB]
  simp [Tuple.length]
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: point-process tuple kernel formula.

Informal statement: after a point process is measurably enumerated as a tuple,
the candidate kernel at `ω` is the uniform permutation measure of that tuple.
-/
noncomputable def pointProcessTupleMeasure {Ω X : Type u}
    [MeasurableSpace X] [MeasurableSpace (Tuple X)]
    (ξ : Ω → FiniteIntegerMeasures X)
    (τ : FiniteIntegerMeasures X → Tuple X) (ω : Ω) :
    Measure (Tuple X) :=
  uniformPermutationMeasure (τ (ξ ω))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: measurable-in-`ω` clause of `thm:point-process-tuple`.

Informal statement: if the point process is a measurable finite integer
measure and the enumeration map is measurable, then the displayed finite
permutation average is measurable as a map from states to probability
measures on tuple space.

Lean strategy / thesis relation note: Lean's kernel API separates the measurable-space source
`Ω` from any probability measure on it. This theorem proves the measurable
part of the kernel before the Markov-kernel wrapper is introduced below.
-/
theorem measurable_pointProcessTupleMeasure {Ω X : Type u}
    [MeasurableSpace Ω] [MeasurableSpace X] [EMetricSpace X]
    (ξ : Ω → FiniteIntegerMeasures X) (hξ : Measurable ξ)
    (τ : FiniteIntegerMeasures X → Tuple X)
    (hτ : @Measurable (FiniteIntegerMeasures X) (Tuple X)
      inferInstance (tupleHausdorffBorel (X := X)) τ) :
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    Measurable (pointProcessTupleMeasure ξ τ) := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  exact measurable_uniformPermutationMeasure.comp (hτ.comp hξ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: fixed-`ω` probability clause of `thm:point-process-tuple`.

Informal statement: for each `ω`, the candidate kernel measure is a
probability measure.
-/
theorem pointProcessTupleMeasure_isProbabilityMeasure {Ω X : Type u}
    [MeasurableSpace X] [MeasurableSpace (Tuple X)]
    (ξ : Ω → FiniteIntegerMeasures X)
    (τ : FiniteIntegerMeasures X → Tuple X) (ω : Ω) :
    IsProbabilityMeasure (pointProcessTupleMeasure ξ τ ω) :=
  uniformPermutationMeasure_isProbabilityMeasure (τ (ξ ω))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: Markov kernel construction in `thm:point-process-tuple`.

Informal statement: the thesis' displayed assignment
`ω ↦ (1/n!) ∑_{π ∈ P_n} δ_{x(ω)∘π}` is a Lean `Kernel` from the state
space to tuple space.

Lean strategy / thesis relation note: the thesis begins with a probability space `(Ω,\mathcal F,P)`.
For Lean's `Kernel Ω (Tuple X)`, only the measurable space on `Ω` is needed;
the source probability measure `P` is irrelevant to the two kernel axioms.
-/
noncomputable def pointProcessTupleKernel {Ω X : Type u}
    [MeasurableSpace Ω] [MeasurableSpace X] [EMetricSpace X]
    (ξ : Ω → FiniteIntegerMeasures X) (hξ : Measurable ξ)
    (τ : FiniteIntegerMeasures X → Tuple X)
    (hτ : @Measurable (FiniteIntegerMeasures X) (Tuple X)
      inferInstance (tupleHausdorffBorel (X := X)) τ) :
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    Kernel Ω (Tuple X) := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  exact Kernel.mk (pointProcessTupleMeasure ξ τ)
    (measurable_pointProcessTupleMeasure ξ hξ τ hτ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: probability-measure clause of `thm:point-process-tuple`.

Informal statement: the tuple kernel is Markov: every fiber over `ω` is a
probability measure.
-/
theorem pointProcessTupleKernel_isMarkovKernel {Ω X : Type u}
    [MeasurableSpace Ω] [MeasurableSpace X] [EMetricSpace X]
    (ξ : Ω → FiniteIntegerMeasures X) (hξ : Measurable ξ)
    (τ : FiniteIntegerMeasures X → Tuple X)
    (hτ : @Measurable (FiniteIntegerMeasures X) (Tuple X)
      inferInstance (tupleHausdorffBorel (X := X)) τ) :
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    IsMarkovKernel (pointProcessTupleKernel ξ hξ τ hτ) := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  refine ⟨?_⟩
  intro ω
  change IsProbabilityMeasure (pointProcessTupleMeasure ξ τ ω)
  exact pointProcessTupleMeasure_isProbabilityMeasure ξ τ ω

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:point-process-tuple`.

Original label: `thm:point-process-tuple`.

Informal statement: every measurable finite point process with values in the
finite integer-valued measures admits the thesis' tuple-valued Markov kernel:
choose a measurable enumeration, then average uniformly over all finite
permutations of that tuple.

Lean strategy / thesis relation note: the measurable enumeration is the cited
Daley--Vere-Jones/Kallenberg background result recorded above as
`lem:measurable-enumeration`; the remaining finite permutation averaging is
proved directly here.
-/
theorem pointProcessTuple_markovKernel {Ω X : Type u}
    [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSingletonClass X]
    [EMetricSpace X] [OpensMeasurableSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (ξ : Ω → FiniteIntegerMeasures X) (hξ : Measurable ξ) :
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    ∃ Q : Kernel Ω (Tuple X), IsMarkovKernel Q := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  refine ⟨pointProcessTupleKernel ξ hξ (measurableEnumeration (X := X))
      (measurable_measurableEnumeration (X := X)), ?_⟩
  exact pointProcessTupleKernel_isMarkovKernel ξ hξ
    (measurableEnumeration (X := X)) (measurable_measurableEnumeration (X := X))

end TupleMeasures
end Stochastic
end Foundations
end Thesis
