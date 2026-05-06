import Foundations.MarketRepresentation.TuplesSorting

/-!
# Market Representation: Tuple Metrics and Standard Machinery

Blueprint module for
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsections "The Tuple Hausdorff Metric" and "The Tuple Topology".

Planned formal content:

* tuple Hausdorff distance;
* tuple-space metric properties;
* length rigidity below distance `1`;
* collapse to maximum product metric on fixed-length layers;
* completeness and separability transfer;
* `cor:tuple-metrization` for `d∞`;
* `thm:the-standard-machinery`.
-/

namespace Thesis
namespace Foundations
namespace MarketRepresentation
namespace TuplesMetricTopology

open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets

universe u v

/-! ## Tuple Hausdorff Distance -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: tuple Hausdorff distance before
`thm:tuple-space-metrization`.

Informal statement: the Hausdorff distance between tuples is the Hausdorff
distance between their graph images in the distinct finite-set space.
-/
noncomputable def tupleHausdorffEDistance {X : Type u} [EMetricSpace X]
    (x y : Tuple X) : ENNReal :=
  edist (graph x) (graph y)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: distance definition in `thm:tuple-space-metrization`.

Informal statement: tuple edistance is graph-induced Hausdorff edistance.
-/
noncomputable instance instEDist {X : Type u} [EMetricSpace X] : EDist (Tuple X) where
  edist := tupleHausdorffEDistance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: pseudometric part of `thm:tuple-space-metrization`.

Informal statement: the graph-induced tuple Hausdorff distance satisfies the
extended pseudometric laws.
-/
noncomputable instance instPseudoEMetricSpace {X : Type u} [EMetricSpace X] :
    PseudoEMetricSpace (Tuple X) where
  edist_self := by
    intro x
    change edist (graph x) (graph x) = 0
    simp
  edist_comm := by
    intro x y
    change edist (graph x) (graph y) = edist (graph y) (graph x)
    exact edist_comm _ _
  edist_triangle := by
    intro x y z
    change edist (graph x) (graph z) ≤
      edist (graph x) (graph y) + edist (graph y) (graph z)
    exact edist_triangle _ _ _

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: `thm:tuple-space-metrization`.

Informal statement: the graph-induced tuple Hausdorff distance is an extended
metric.

Lean strategy / thesis relation note: Lean again uses `EMetricSpace` because the thesis distance
takes values in `[0,\infty]`.
-/
noncomputable instance instEMetricSpace {X : Type u} [EMetricSpace X] :
    EMetricSpace (Tuple X) :=
  EMetricSpace.mk (by
    intro x y h
    apply graph_injective
    change edist (graph x) (graph y) = 0 at h
    exact edist_eq_zero.mp h)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: graph-isometry step in `thm:tuple-space-properties`.

Informal statement: the graph map `Γ : \mathscr{T}(X) → \mathscr{D}(X)` is
an isometry when tuple space carries the graph-induced tuple Hausdorff metric.

Lean strategy / thesis relation note: this is definitionally true because `tupleHausdorffEDistance`
was defined as the pullback of the distinct-finite-set Hausdorff distance
along `Γ`.
-/
theorem graph_isometry {X : Type u} [EMetricSpace X] :
    Isometry (graph (X := X)) := by
  intro x y
  rfl

/-- The topology induced by the tuple Hausdorff extended metric. -/
@[reducible]
noncomputable def tupleHausdorffMetricTopology {X : Type u} [EMetricSpace X] :
    TopologicalSpace (Tuple X) :=
  PseudoEMetricSpace.toUniformSpace.toTopologicalSpace

/-! ## First Tuple-Space Properties -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: cardinality helper for `thm:tuple-space-properties`.

Informal statement: the finite initial segment `{k | k < n}` has cardinality
`n`.
-/
theorem ncard_initialSegment (n : ℕ) : ({k : ℕ | k < n} : Set ℕ).ncard = n := by
  apply Set.ncard_eq_of_bijective (fun i _ => i)
  · intro a ha
    exact ⟨a, ha, rfl⟩
  · intro i hi
    exact hi
  · intro i j _hi _hj h
    exact h

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: graph index-cardinality helper for
`thm:tuple-space-properties`.

Informal statement: the projected index set of a tuple graph has cardinality
equal to the tuple length.
-/
theorem ncard_indexSet_graph {X : Type u} (x : Tuple X) :
    (DistinctFiniteSubsets.indexSet (graph x) : Set ℕ).ncard = x.length := by
  have hset : (DistinctFiniteSubsets.indexSet (graph x) : Set ℕ) =
      {k : ℕ | k < x.length} := by
    ext k
    exact mem_indexSet_graph x
  rw [hset, ncard_initialSegment]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: graph cardinality helper for `thm:tuple-space-properties`.

Informal statement: the graph of a tuple has cardinality equal to the tuple
length.
-/
theorem ncard_graph {X : Type u} (x : Tuple X) :
    ((graph x).1 : Set (IndexAugmented X)).ncard = x.length := by
  rw [← ncard_indexSet_graph x]
  exact (DistinctFiniteSubsets.ncard_indexSet_eq (graph x)).symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: first item of `thm:tuple-space-properties`.

Informal statement: if the tuple Hausdorff distance is below `1`, then the
two tuples have the same length.
-/
theorem length_eq_of_edist_lt_one {X : Type u} [EMetricSpace X]
    {x y : Tuple X} (h : edist x y < (1 : ENNReal)) :
    x.length = y.length := by
  change edist (graph x) (graph y) < (1 : ENNReal) at h
  have hcard := DistinctFiniteSubsets.ncard_eq_of_edist_lt_one h
  rw [ncard_graph x, ncard_graph y] at hcard
  exact hcard

/-! ## Local Collapse to Fixed-Length Maximum Distance -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: maximum product metric in the second item of
`thm:tuple-space-properties`.

Informal statement: on a fixed-length tuple layer, the coordinate maximum
edistance is the finite supremum of the coordinate edistances.
-/
noncomputable def coordinateEDistSup {X : Type u} [PseudoEMetricSpace X]
    {n : ℕ} (x y : Fin n → X) : ENNReal :=
  Finset.univ.sup fun i => edist (x i) (y i)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: upper-bound half of the local collapse in
`thm:tuple-space-properties`.

Informal statement: for fixed-length tuples, the tuple Hausdorff distance is
bounded above by the maximum coordinate distance.
-/
theorem fixedLength_edist_le_coordinateEDistSup {X : Type u} [EMetricSpace X]
    {n : ℕ} (x y : Fin n → X) :
    edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) ≤
      coordinateEDistSup x y := by
  change hausdorffEDistance (graph (Sigma.mk n x : Tuple X)).1
    (graph (Sigma.mk n y : Tuple X)).1 ≤ coordinateEDistSup x y
  apply Metric.hausdorffEDist_le_of_mem_edist
  · intro p hp
    rcases (mem_graph (Sigma.mk n x : Tuple X)).mp hp with ⟨i, rfl⟩
    refine ⟨IndexAugmented.mk i.1 (y i), ?_, ?_⟩
    · rw [mem_graph]
      exact ⟨i, rfl⟩
    · rw [IndexAugmented.edist_mk_mk]
      simpa [coordinateEDistSup] using
        (Finset.le_sup (s := Finset.univ)
          (f := fun i : Fin n => edist (x i) (y i)) (Finset.mem_univ i))
  · intro p hp
    rcases (mem_graph (Sigma.mk n y : Tuple X)).mp hp with ⟨i, rfl⟩
    refine ⟨IndexAugmented.mk i.1 (x i), ?_, ?_⟩
    · rw [mem_graph]
      exact ⟨i, rfl⟩
    · rw [IndexAugmented.edist_mk_mk]
      simpa [coordinateEDistSup, edist_comm] using
        (Finset.le_sup (s := Finset.univ)
          (f := fun i : Fin n => edist (x i) (y i)) (Finset.mem_univ i))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: same-index coordinate consequence used in the local collapse
proof of `thm:tuple-space-properties`.

Informal statement: below tuple Hausdorff distance `1`, each same-index
coordinate distance is itself below `1`.
-/
theorem coordinate_edist_lt_one_of_fixedLength_edist_lt_one {X : Type u}
    [EMetricSpace X] {n : ℕ} {x y : Fin n → X}
    (h : edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) < (1 : ENNReal))
    (i : Fin n) :
    edist (x i) (y i) < (1 : ENNReal) := by
  change edist (graph (Sigma.mk n x : Tuple X))
    (graph (Sigma.mk n y : Tuple X)) < (1 : ENNReal) at h
  have hmem :
      IndexAugmented.mk i.1 (x i) ∈
        ((graph (Sigma.mk n x : Tuple X)).1 : Set (IndexAugmented X)) := by
    rw [mem_graph]
    exact ⟨i, rfl⟩
  rcases DistinctFiniteSubsets.exists_same_index_near_of_edist_lt_one h hmem with
    ⟨z, hzlt, hzmem⟩
  rcases (mem_graph (Sigma.mk n y : Tuple X)).mp hzmem with ⟨j, hj⟩
  have hij : j = i := by
    apply Fin.ext
    simpa using (congrArg IndexAugmented.index hj).symm
  have hz : z = y j := by
    simpa using congrArg IndexAugmented.value hj
  rw [hij] at hz
  simpa [hz]
    using hzlt

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: lower-bound coordinate step in the local collapse proof of
`thm:tuple-space-properties`.

Informal statement: below distance `1`, each fixed coordinate distance is
bounded by the tuple Hausdorff distance.
-/
theorem coordinate_edist_le_fixedLength_edist_of_lt_one {X : Type u}
    [EMetricSpace X] {n : ℕ} {x y : Fin n → X}
    (h : edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) < (1 : ENNReal))
    (i : Fin n) :
    edist (x i) (y i) ≤ edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) := by
  have hcoord_lt_one := coordinate_edist_lt_one_of_fixedLength_edist_lt_one h i
  have hmem :
      IndexAugmented.mk i.1 (x i) ∈
        ((graph (Sigma.mk n x : Tuple X)).1 : Set (IndexAugmented X)) := by
    rw [mem_graph]
    exact ⟨i, rfl⟩
  change edist (x i) (y i) ≤
    hausdorffEDistance (graph (Sigma.mk n x : Tuple X)).1
      (graph (Sigma.mk n y : Tuple X)).1
  have hle_inf : edist (x i) (y i) ≤
      Metric.infEDist (IndexAugmented.mk i.1 (x i))
        ((graph (Sigma.mk n y : Tuple X)).1 : Set (IndexAugmented X)) := by
    rw [Metric.le_infEDist]
    intro q hq
    rcases (mem_graph (Sigma.mk n y : Tuple X)).mp hq with ⟨j, hj⟩
    rw [hj]
    by_cases hji : j = i
    · subst j
      rw [IndexAugmented.edist_mk_mk]
      simp
    · have hval_ne : i.1 ≠ j.1 := by
        intro hval
        exact hji (Fin.ext hval.symm)
      have hnot_lt : ¬ edist i.1 j.1 < (1 : ENNReal) := by
        intro hlt
        exact hval_ne (IndexAugmented.nat_eq_of_edist_lt_one hlt)
      have hone_le : (1 : ENNReal) ≤ edist i.1 j.1 := le_of_not_gt hnot_lt
      have hindex_le :
          edist i.1 j.1 ≤
            edist (IndexAugmented.mk i.1 (x i)) (IndexAugmented.mk j.1 (y j)) := by
        rw [IndexAugmented.edist_mk_mk]
        exact le_self_add
      exact le_trans hcoord_lt_one.le (le_trans hone_le hindex_le)
  exact le_trans hle_inf (Metric.infEDist_le_hausdorffEDist_of_mem hmem)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: lower-bound half of the local collapse in
`thm:tuple-space-properties`.

Informal statement: below distance `1`, the maximum coordinate distance is
bounded by the tuple Hausdorff distance.
-/
theorem coordinateEDistSup_le_fixedLength_edist_of_lt_one {X : Type u}
    [EMetricSpace X] {n : ℕ} {x y : Fin n → X}
    (h : edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) < (1 : ENNReal)) :
    coordinateEDistSup x y ≤ edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) := by
  apply Finset.sup_le
  intro i _hi
  exact coordinate_edist_le_fixedLength_edist_of_lt_one h i

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: second item of `thm:tuple-space-properties`, fixed-length
form.

Informal statement: for two fixed-length tuples whose tuple Hausdorff distance
is below `1`, the tuple Hausdorff distance is exactly the maximum coordinate
edistance.

Lean strategy / thesis relation note: this is the Lean-native fixed-layer version of the thesis'
`\max_{i=1,\dots,\ell(x)} d(x_i,y_i)` statement. The general tuple statement
first uses `length_eq_of_edist_lt_one` to move into this fixed-length layer.
-/
theorem fixedLength_edist_eq_coordinateEDistSup_of_lt_one {X : Type u}
    [EMetricSpace X] {n : ℕ} {x y : Fin n → X}
    (h : edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) < (1 : ENNReal)) :
    edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) =
      coordinateEDistSup x y :=
  le_antisymm (fixedLength_edist_le_coordinateEDistSup x y)
    (coordinateEDistSup_le_fixedLength_edist_of_lt_one h)

/-! ## Completeness and Separability Transfer -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: Cauchy-sequence step in `thm:tuple-space-properties`.

Informal statement: a Cauchy sequence of tuples is eventually contained in a
single fixed-length layer.

Lean strategy / thesis relation note: this is the formal version of the thesis' stabilization at
Hausdorff radius `< 1`: below that radius, tuple length is forced to agree.
-/
theorem cauchySeq_eventually_constant_length {X : Type u} [EMetricSpace X]
    {u : ℕ → Tuple X} (hu : CauchySeq u) :
    ∃ L : ℕ, ∀ᶠ n in Filter.atTop, (u n).length = L := by
  rcases (EMetric.cauchySeq_iff.1 hu) (1 : ENNReal) zero_lt_one with ⟨N, hN⟩
  refine ⟨(u N).length, Filter.eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn
  exact length_eq_of_edist_lt_one (hN n hn N le_rfl)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: constructive completeness proof in
`thm:tuple-space-properties`.

Informal statement: if the ambient space is complete, every Cauchy sequence
of tuples converges.

Lean strategy / thesis relation note: the proof follows the thesis. First the tuple length
stabilizes. Then each coordinate sequence in the fixed finite layer is Cauchy
in `X`, hence converges. The limiting tuple is formed coordinatewise.
-/
theorem cauchySeq_tendsto_of_complete {X : Type u} [EMetricSpace X]
    [CompleteSpace X] {u : ℕ → Tuple X} (hu : CauchySeq u) :
    ∃ x : Tuple X,
      Filter.Tendsto u Filter.atTop
        (@nhds (Tuple X) PseudoEMetricSpace.toUniformSpace.toTopologicalSpace x) := by
  rcases (EMetric.cauchySeq_iff.1 hu) (1 : ENNReal) zero_lt_one with ⟨N, hNsmall⟩
  let L : ℕ := (u N).length
  have hLength : ∀ n, N ≤ n → (u n).length = L := by
    intro n hn
    exact length_eq_of_edist_lt_one (hNsmall n hn N le_rfl)
  have hFixedExists : ∀ n, N ≤ n → ∃ f : Fin L → X,
      u n = (Sigma.mk L f : Tuple X) := by
    intro n hn
    cases htuple : u n with
    | mk m f =>
        have hlen : m = L := by
          simpa [Tuple.length, htuple] using hLength n hn
        subst m
        exact ⟨f, rfl⟩
  let fixed : (n : ℕ) → N ≤ n → Fin L → X := fun n hn =>
    Classical.choose (hFixedExists n hn)
  have fixed_eq : ∀ (n : ℕ) (hn : N ≤ n),
      u n = (Sigma.mk L (fixed n hn) : Tuple X) := by
    intro n hn
    exact Classical.choose_spec (hFixedExists n hn)
  let coord : Fin L → ℕ → X := fun i n =>
    if hn : N ≤ n then
      fixed n hn i
    else
      fixed N le_rfl i
  have hu_eq : ∀ n, N ≤ n →
      (Sigma.mk L (fun i : Fin L => coord i n) : Tuple X) = u n := by
    intro n hn
    rw [fixed_eq n hn]
    congr
    funext i
    simp [coord, hn]
  have hcoord_cauchy : ∀ i : Fin L, CauchySeq (coord i) := by
    intro i
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    rcases exists_pos_le_one_lt_ennreal hε with ⟨δ, hδpos, hδle_one, hδε⟩
    rcases (EMetric.cauchySeq_iff.1 hu) δ hδpos with ⟨M, hM⟩
    refine ⟨max N M, ?_⟩
    intro m hm n hn
    have hmN : N ≤ m := le_trans (le_max_left N M) hm
    have hnN : N ≤ n := le_trans (le_max_left N M) hn
    have hmM : M ≤ m := le_trans (le_max_right N M) hm
    have hnM : M ≤ n := le_trans (le_max_right N M) hn
    have hdist : edist (u m) (u n) < δ := hM m hmM n hnM
    have hfixed : edist
        (Sigma.mk L (fun j : Fin L => coord j m) : Tuple X)
        (Sigma.mk L (fun j : Fin L => coord j n) : Tuple X) < δ := by
      simpa [hu_eq m hmN, hu_eq n hnN] using hdist
    have hfixed_one :
        edist (Sigma.mk L (fun j : Fin L => coord j m) : Tuple X)
          (Sigma.mk L (fun j : Fin L => coord j n) : Tuple X) <
            (1 : ENNReal) :=
      lt_of_lt_of_le hfixed hδle_one
    have hcoord_le :
        edist (coord i m) (coord i n) ≤
          edist (Sigma.mk L (fun j : Fin L => coord j m) : Tuple X)
            (Sigma.mk L (fun j : Fin L => coord j n) : Tuple X) :=
      coordinate_edist_le_fixedLength_edist_of_lt_one hfixed_one i
    exact lt_trans (lt_of_le_of_lt hcoord_le hfixed) hδε
  choose xlim hxlim using fun i : Fin L =>
    _root_.cauchySeq_tendsto_of_complete (hcoord_cauchy i)
  refine ⟨(Sigma.mk L xlim : Tuple X), ?_⟩
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  rw [EMetric.tendsto_nhds]
  intro ε hε
  rcases exists_pos_lt_ennreal hε with ⟨δ, hδpos, hδε⟩
  have hcoord_event : ∀ i : Fin L, ∀ᶠ n in Filter.atTop,
      edist (coord i n) (xlim i) < δ := by
    intro i
    exact EMetric.tendsto_nhds.1 (hxlim i) δ hδpos
  have hall : ∀ᶠ n in Filter.atTop,
      ∀ i : Fin L, edist (coord i n) (xlim i) < δ := by
    rw [Filter.eventually_all]
    exact hcoord_event
  have hNevent : ∀ᶠ n in Filter.atTop, N ≤ n :=
    Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩
  filter_upwards [hall, hNevent] with n halln hnN
  have hle :
      edist (Sigma.mk L (fun i : Fin L => coord i n) : Tuple X)
        (Sigma.mk L xlim : Tuple X) ≤
          coordinateEDistSup (fun i : Fin L => coord i n) xlim :=
    fixedLength_edist_le_coordinateEDistSup (fun i : Fin L => coord i n) xlim
  have hsup : coordinateEDistSup (fun i : Fin L => coord i n) xlim < δ := by
    rw [coordinateEDistSup]
    exact (Finset.sup_lt_iff hδpos).mpr (fun i _hi => halln i)
  have htuple :
      edist (Sigma.mk L (fun i : Fin L => coord i n) : Tuple X)
        (Sigma.mk L xlim : Tuple X) < ε :=
    lt_trans (lt_of_le_of_lt hle hsup) hδε
  simpa [hu_eq n hnN] using htuple

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: completeness transfer in `thm:tuple-space-properties`.

Informal statement: if `X` is complete, then the tuple Hausdorff space
`\mathscr{T}(X)` is complete.
-/
theorem completeSpace {X : Type u} [EMetricSpace X] [CompleteSpace X] :
    CompleteSpace (Tuple X) := by
  refine EMetric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  exact cauchySeq_tendsto_of_complete hu

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: dense support set used in the separability transfer in
`thm:tuple-space-properties`.

Informal statement: `tupleSupportedOn U` consists of tuples whose entries all
belong to the support set `U`.
-/
def tupleSupportedOn {X : Type u} (U : Set X) : Set (Tuple X) :=
  {x | ∀ i : Fin x.length, Tuple.entry x i ∈ U}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: countability step in the separability transfer in
`thm:tuple-space-properties`.

Informal statement: if `U` is countable, then the tuples supported on `U`
form a countable set.
-/
theorem tupleSupportedOn_countable {X : Type u} {U : Set X}
    (hU : U.Countable) : (tupleSupportedOn U).Countable := by
  haveI : Countable {x : X // x ∈ U} := hU.to_subtype
  haveI : Countable (Σ n : ℕ, Fin n → {x : X // x ∈ U}) := by infer_instance
  let f : (Σ n : ℕ, Fin n → {x : X // x ∈ U}) → Tuple X := fun z =>
    Sigma.mk z.1 (fun i => (z.2 i).1)
  have hsubset : tupleSupportedOn U ⊆ Set.range f := by
    intro x hx
    refine ⟨Sigma.mk x.length (fun i : Fin x.length =>
      ⟨Tuple.entry x i, hx i⟩), ?_⟩
    cases x
    rfl
  exact (Set.countable_range f).mono hsubset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: density step in the separability transfer in
`thm:tuple-space-properties`.

Informal statement: if `U` is dense in `X`, then tuples supported on `U` are
dense in the tuple Hausdorff space.

Lean strategy / thesis relation note: the proof follows the thesis finite-product argument: on a
fixed-length layer, approximate each coordinate by a point of `U`, then use
the fixed-layer Hausdorff upper bound.
-/
theorem tupleSupportedOn_dense {X : Type u} [EMetricSpace X] {U : Set X}
    (hU : Dense U) :
    @Dense (Tuple X) PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (tupleSupportedOn U) := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.mpr
  intro x
  rw [EMetric.mem_closure_iff]
  intro ε hε
  rcases exists_pos_lt_ennreal hε with ⟨δ, hδpos, hδε⟩
  rcases x with ⟨n, f⟩
  have hApprox : ∀ i : Fin n, ∃ u ∈ U, edist (f i) u < δ := by
    intro i
    have hcl : f i ∈ closure U := by
      rw [dense_iff_closure_eq.mp hU]
      trivial
    exact (EMetric.mem_closure_iff.mp hcl) δ hδpos
  choose g hgU hgδ using hApprox
  refine ⟨(Sigma.mk n g : Tuple X), ?_, ?_⟩
  · intro i
    exact hgU i
  · have hle : edist (Sigma.mk n f : Tuple X) (Sigma.mk n g : Tuple X) ≤
        coordinateEDistSup f g :=
      fixedLength_edist_le_coordinateEDistSup f g
    have hsup : coordinateEDistSup f g < δ := by
      rw [coordinateEDistSup]
      exact (Finset.sup_lt_iff hδpos).mpr (fun i _hi => hgδ i)
    exact lt_trans (lt_of_le_of_lt hle hsup) hδε

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: separability transfer in `thm:tuple-space-properties`.

Informal statement: if `X` is separable, then the tuple Hausdorff space
`\mathscr{T}(X)` is separable by viewing it as an isometric subspace of
the distinct finite-set space through the graph map.

Lean strategy / thesis relation note: this is the proof route used in the thesis. The codomain
`DistinctFiniteSubsets X` is separable by `thm:distinct-properties`; the
graph map is an isometry, hence an embedding, so separability transfers back
to tuple space.
-/
theorem separableSpace_via_graphImage {X : Type u} [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] :
    @TopologicalSpace.SeparableSpace
      (Tuple X) PseudoEMetricSpace.toUniformSpace.toTopologicalSpace := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace.SeparableSpace (DistinctFiniteSubsets X) :=
    DistinctFiniteSubsets.separableSpace (α := X)
  haveI : SecondCountableTopology (DistinctFiniteSubsets X) :=
    UniformSpace.secondCountable_of_separable (DistinctFiniteSubsets X)
  exact (graph_isometry (X := X)).isEmbedding.separableSpace

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: separability transfer in `thm:tuple-space-properties`.

Informal statement: if `X` is separable, then the tuple Hausdorff space
`\mathscr{T}(X)` is separable.

Lean strategy / thesis strategy note: the headline theorem now follows the thesis graph-image
argument. The earlier direct dense-support construction remains available as
the auxiliary lemmas `tupleSupportedOn_countable` and `tupleSupportedOn_dense`.
-/
theorem separableSpace {X : Type u} [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] :
    @TopologicalSpace.SeparableSpace
      (Tuple X) PseudoEMetricSpace.toUniformSpace.toTopologicalSpace :=
  separableSpace_via_graphImage (X := X)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Hausdorff Metric".

Original label: sorted tuple separability in `thm:tuple-space-properties`,
item `eq:sorted-tuple-separable`.

Informal statement: if `(X, \preceq, d)` is totally ordered and separable,
then the sorted tuple space is separable as a metric subspace of the tuple
Hausdorff space.

Lean strategy / thesis relation note: the thesis invokes the standard metric-space fact that every
subspace of a separable metric space is separable. Lean states this through
`TopologicalSpace.IsSeparable.separableSpace`; the theorem is explicit about
the tuple Hausdorff metric topology to avoid the native Sigma topology on
`Tuple X`.
-/
theorem sortedTuple_separableSpace {X : Type u} [EMetricSpace X]
    [LinearOrder X] [TopologicalSpace.SeparableSpace X] :
    @TopologicalSpace.SeparableSpace
      (SortedTuple X) PseudoEMetricSpace.toUniformSpace.toTopologicalSpace := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  haveI : TopologicalSpace.SeparableSpace (Tuple X) := separableSpace (X := X)
  have hs : TopologicalSpace.IsSeparable
      ({x : Tuple X | IsSorted x} : Set (Tuple X)) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  exact hs.separableSpace

/-! ## The Tuple `d∞` Metric -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `cor:tuple-metrization`.

Informal statement: the `d∞` metric on tuple space is the disjoint-union
metric over the fixed-length product layers `Fin n → X`.

Lean strategy / thesis relation note: `Tuple X` is definitionally the dependent sum
`Σ n, Fin n → X`, so the thesis' disjoint union
`\bigsqcup_{n\in\mathbb{N}_0} X^n` is already the Lean representation. This
definition deliberately does not become the global `EMetricSpace` instance,
because the file's default tuple metric is the tuple Hausdorff distance.
-/
@[reducible]
noncomputable def tupleSupEMetricSpace {X : Type u} [EMetricSpace X] :
    EMetricSpace (Tuple X) :=
  DisjointUnionTopology.disjointUnionEMetricSpace
    (X := fun n : ℕ => Fin n → X)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: distance function in `cor:tuple-metrization`.

Informal statement: the `d∞` distance function itself, kept as a named
function so it can coexist with the global tuple Hausdorff `edist`.
-/
noncomputable def tupleSupEDistance {X : Type u} [EMetricSpace X]
    (x y : Tuple X) : ENNReal :=
  DisjointUnionTopology.disjointEdist
    (X := fun n : ℕ => Fin n → X) x y

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: same-length case in `cor:tuple-metrization`.

Informal statement: on a fixed-length layer, `d∞` is the maximum coordinate
edistance.
-/
theorem tupleSup_edist_same {X : Type u} [EMetricSpace X]
    {n : ℕ} (x y : Fin n → X) :
    tupleSupEDistance (Sigma.mk n x : Tuple X) (Sigma.mk n y) =
      coordinateEDistSup x y := by
  unfold tupleSupEDistance
  rw [DisjointUnionTopology.disjointEdist_mk_mk_same]
  rw [edist_pi_def]
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: different-length case in `cor:tuple-metrization`.

Informal statement: tuples of different lengths have `d∞` distance `∞`.
-/
theorem tupleSup_edist_ne_length {X : Type u} [EMetricSpace X]
    {m n : ℕ} (h : m ≠ n) (x : Fin m → X) (y : Fin n → X) :
    tupleSupEDistance (Sigma.mk m x : Tuple X) (Sigma.mk n y) = ⊤ := by
  unfold tupleSupEDistance
  exact DisjointUnionTopology.disjointEdist_mk_mk_ne
    (X := fun n : ℕ => Fin n → X) h x y

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: proposition following `cor:tuple-metrization`.

Informal statement: after truncating at radius `1`, the tuple Hausdorff
distance and the thesis `d∞` distance agree.

Lean strategy / thesis relation note: the thesis says that replacing a metric by `min(d,1)`
preserves the induced topology. The formal bridge recorded here is the
pointwise identity needed for tuple space: below radius `1`, the tuple
Hausdorff metric collapses to the fixed-layer maximum metric; across different
lengths, both truncated distances are exactly `1`.
-/
theorem tupleHausdorff_min_one_eq_tupleSup_min_one {X : Type u}
    [EMetricSpace X] (x y : Tuple X) :
    min (edist x y) (1 : ENNReal) =
      min (tupleSupEDistance x y) (1 : ENNReal) := by
  rcases x with ⟨m, x⟩
  rcases y with ⟨n, y⟩
  by_cases hmn : m = n
  · subst n
    by_cases hlt :
        edist (Sigma.mk m x : Tuple X) (Sigma.mk m y : Tuple X) < (1 : ENNReal)
    · have hhaus :
          edist (Sigma.mk m x : Tuple X) (Sigma.mk m y : Tuple X) =
            coordinateEDistSup x y :=
        fixedLength_edist_eq_coordinateEDistSup_of_lt_one hlt
      have hsup :
          tupleSupEDistance (Sigma.mk m x : Tuple X) (Sigma.mk m y) =
            coordinateEDistSup x y :=
        tupleSup_edist_same x y
      rw [hhaus, hsup]
    · have hhaus_min :
          min (edist (Sigma.mk m x : Tuple X) (Sigma.mk m y : Tuple X))
              (1 : ENNReal) = 1 :=
        min_eq_right (le_of_not_gt hlt)
      have hcoord_not_lt :
          ¬ coordinateEDistSup x y < (1 : ENNReal) := by
        intro hcoord_lt
        exact hlt
          (lt_of_le_of_lt (fixedLength_edist_le_coordinateEDistSup x y) hcoord_lt)
      have hsup_min :
          min (tupleSupEDistance (Sigma.mk m x : Tuple X) (Sigma.mk m y))
              (1 : ENNReal) = 1 := by
        rw [tupleSup_edist_same]
        exact min_eq_right (le_of_not_gt hcoord_not_lt)
      rw [hhaus_min, hsup_min]
  · have hhaus_not_lt :
        ¬ edist (Sigma.mk m x : Tuple X) (Sigma.mk n y : Tuple X) < (1 : ENNReal) := by
      intro hlt
      have hlen : m = n := by
        simpa using
          (length_eq_of_edist_lt_one
            (x := (Sigma.mk m x : Tuple X)) (y := (Sigma.mk n y : Tuple X)) hlt)
      exact hmn hlen
    have hhaus_min :
        min (edist (Sigma.mk m x : Tuple X) (Sigma.mk n y : Tuple X))
            (1 : ENNReal) = 1 :=
      min_eq_right (le_of_not_gt hhaus_not_lt)
    have hsup_top :
        tupleSupEDistance (Sigma.mk m x : Tuple X) (Sigma.mk n y) = ⊤ :=
      tupleSup_edist_ne_length hmn x y
    have hsup_min :
        min (tupleSupEDistance (Sigma.mk m x : Tuple X) (Sigma.mk n y))
            (1 : ENNReal) = 1 := by
      rw [hsup_top]
      exact min_eq_right le_top
    rw [hhaus_min, hsup_min]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: proposition following `cor:tuple-metrization`.

Informal statement: the Hausdorff and `d∞` tuple distances have the same
open balls below radius `1`.

Lean strategy / thesis relation note: this is the local form of the thesis truncation argument:
small neighborhoods are fixed-length neighborhoods, and on each fixed-length
layer the two distances coincide with the same coordinate supremum metric.
-/
theorem tupleHausdorff_lt_one_iff_tupleSup_lt_one {X : Type u}
    [EMetricSpace X] (x y : Tuple X) :
    edist x y < (1 : ENNReal) ↔
      tupleSupEDistance x y < (1 : ENNReal) := by
  rcases x with ⟨m, x⟩
  rcases y with ⟨n, y⟩
  constructor
  · intro h
    have hlen : m = n := by
      simpa using
        (length_eq_of_edist_lt_one
          (x := (Sigma.mk m x : Tuple X)) (y := (Sigma.mk n y : Tuple X)) h)
    subst n
    have hhaus :
        edist (Sigma.mk m x : Tuple X) (Sigma.mk m y : Tuple X) =
          coordinateEDistSup x y :=
      fixedLength_edist_eq_coordinateEDistSup_of_lt_one h
    rw [tupleSup_edist_same, ← hhaus]
    exact h
  · intro h
    by_cases hmn : m = n
    · subst n
      rw [tupleSup_edist_same] at h
      exact lt_of_le_of_lt (fixedLength_edist_le_coordinateEDistSup x y) h
    · have htop :
          tupleSupEDistance (Sigma.mk m x : Tuple X) (Sigma.mk n y) = ⊤ :=
        tupleSup_edist_ne_length hmn x y
      rw [htop] at h
      exact False.elim ((not_lt_of_ge (le_top : (1 : ENNReal) ≤ ⊤)) h)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, topology component.

Informal statement: a set is open for the tuple Hausdorff metric iff its
restriction to every fixed-length tuple layer is open.

Lean strategy / thesis relation note: this is the tuple analogue of the disjoint-union topology
pasting criterion. The proof follows the thesis: below radius `1`, tuple
Hausdorff neighborhoods cannot change length; inside a fixed-length layer,
they are exactly product-sup neighborhoods.
-/
theorem tupleHausdorffMetricTopology_isOpen_iff {X : Type u} [EMetricSpace X]
    {s : Set (Tuple X)} :
    @IsOpen (Tuple X) (tupleHausdorffMetricTopology (X := X)) s ↔
      ∀ n : ℕ, IsOpen (Sigma.mk n ⁻¹' s) := by
  constructor
  · intro hs n
    rw [isOpen_iff_mem_nhds]
    intro x hx
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    change IsOpen s at hs
    have hs_mem : s ∈ nhds (Sigma.mk n x : Tuple X) :=
      (isOpen_iff_mem_nhds.mp hs) (Sigma.mk n x) hx
    rw [EMetric.mem_nhds_iff] at hs_mem
    rcases hs_mem with ⟨ε, hε, hball⟩
    rw [EMetric.mem_nhds_iff]
    refine ⟨ε, hε, ?_⟩
    intro y hy
    have hle :
        edist (Sigma.mk n y : Tuple X) (Sigma.mk n x : Tuple X) ≤
          coordinateEDistSup y x :=
      fixedLength_edist_le_coordinateEDistSup y x
    have hcoord : coordinateEDistSup y x < ε := by
      rw [Metric.mem_eball, edist_pi_def] at hy
      simpa [coordinateEDistSup] using hy
    exact hball (Metric.mem_eball.mpr (lt_of_le_of_lt hle hcoord))
  · intro hs
    letI : TopologicalSpace (Tuple X) := tupleHausdorffMetricTopology (X := X)
    change IsOpen s
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases z with ⟨n, x⟩
    have hpre_open : IsOpen (Sigma.mk n ⁻¹' s) := hs n
    have hpre_mem : (Sigma.mk n ⁻¹' s) ∈ nhds x :=
      (isOpen_iff_mem_nhds.mp hpre_open) x hz
    rw [EMetric.mem_nhds_iff] at hpre_mem
    rcases hpre_mem with ⟨ε, hε, hball⟩
    rw [EMetric.mem_nhds_iff]
    let δ : ENNReal := min ε 1
    have hδpos : 0 < δ := lt_min hε zero_lt_one
    refine ⟨δ, hδpos, ?_⟩
    intro w hw
    rcases w with ⟨m, y⟩
    have hδ_le_one : δ ≤ (1 : ENNReal) := min_le_right ε 1
    have hlt_one :
        edist (Sigma.mk m y : Tuple X) (Sigma.mk n x : Tuple X) < (1 : ENNReal) :=
      lt_of_lt_of_le hw hδ_le_one
    have hlen : m = n := by
      simpa using
        (length_eq_of_edist_lt_one
          (x := (Sigma.mk m y : Tuple X)) (y := (Sigma.mk n x : Tuple X)) hlt_one)
    subst m
    have hhaus :
        edist (Sigma.mk n y : Tuple X) (Sigma.mk n x : Tuple X) =
          coordinateEDistSup y x :=
      fixedLength_edist_eq_coordinateEDistSup_of_lt_one hlt_one
    have hcoord_lt_delta : coordinateEDistSup y x < δ := by
      simpa [hhaus] using hw
    have hcoord_lt_eps : coordinateEDistSup y x < ε :=
      lt_of_lt_of_le hcoord_lt_delta (min_le_left ε 1)
    apply hball
    rw [Metric.mem_eball, edist_pi_def]
    simpa [coordinateEDistSup] using hcoord_lt_eps

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, topology component.

Informal statement: the tuple Hausdorff metric topology is the usual
topological disjoint union of the fixed-length product layers.
-/
theorem tupleHausdorffMetricTopology_eq_sigma {X : Type u} [EMetricSpace X] :
    tupleHausdorffMetricTopology (X := X) = instTopologicalSpaceSigma := by
  rw [TopologicalSpace.ext_iff]
  intro s
  rw [tupleHausdorffMetricTopology_isOpen_iff, isOpen_sigma_iff]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, topology component.

Informal statement: the tuple Hausdorff topology and the thesis `d∞`
disjoint-union topology coincide.
-/
theorem tupleHausdorffMetricTopology_eq_tupleSup {X : Type u} [EMetricSpace X] :
    tupleHausdorffMetricTopology (X := X) =
      DisjointUnionTopology.disjointUnionMetricTopology
        (X := fun n : ℕ => Fin n → X) := by
  rw [tupleHausdorffMetricTopology_eq_sigma,
    DisjointUnionTopology.metricTopology_eq_sigma]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, identity homeomorphism.

Informal statement: the identity map is a homeomorphism between tuple space
with the tuple Hausdorff topology and tuple space with the thesis `d∞`
topology.
-/
noncomputable def tupleHausdorffTupleSupHomeomorph {X : Type u}
    [EMetricSpace X] :
    @Homeomorph (Tuple X) (Tuple X)
      (tupleHausdorffMetricTopology (X := X))
      (DisjointUnionTopology.disjointUnionMetricTopology
        (X := fun n : ℕ => Fin n → X)) := by
  refine @Homeomorph.mk (Tuple X) (Tuple X)
    (tupleHausdorffMetricTopology (X := X))
    (DisjointUnionTopology.disjointUnionMetricTopology
      (X := fun n : ℕ => Fin n → X))
    (Equiv.refl (Tuple X)) ?_ ?_
  · change @Continuous (Tuple X) (Tuple X)
      (tupleHausdorffMetricTopology (X := X))
      (DisjointUnionTopology.disjointUnionMetricTopology
        (X := fun n : ℕ => Fin n → X)) id
    rw [tupleHausdorffMetricTopology_eq_tupleSup]
    exact @continuous_id (Tuple X)
      (DisjointUnionTopology.disjointUnionMetricTopology
        (X := fun n : ℕ => Fin n → X))
  · change @Continuous (Tuple X) (Tuple X)
      (DisjointUnionTopology.disjointUnionMetricTopology
        (X := fun n : ℕ => Fin n → X))
      (tupleHausdorffMetricTopology (X := X)) id
    rw [tupleHausdorffMetricTopology_eq_tupleSup]
    exact @continuous_id (Tuple X)
      (DisjointUnionTopology.disjointUnionMetricTopology
        (X := fun n : ℕ => Fin n → X))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, continuity equivalence.

Informal statement: a map out of tuple space is continuous for the tuple
Hausdorff topology iff it is continuous for the thesis `d∞` topology.
-/
theorem continuous_tupleHausdorff_iff_tupleSup {X : Type u} {Y : Type v}
    [EMetricSpace X] [TopologicalSpace Y] {f : Tuple X → Y} :
    @Continuous (Tuple X) Y (tupleHausdorffMetricTopology (X := X))
      inferInstance f ↔
      @Continuous (Tuple X) Y
        (DisjointUnionTopology.disjointUnionMetricTopology
          (X := fun n : ℕ => Fin n → X)) inferInstance f := by
  rw [tupleHausdorffMetricTopology_eq_tupleSup]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, fixed-layer continuity.

Informal statement: a map out of tuple space is continuous iff each
fixed-length restriction is continuous.
-/
theorem continuous_tupleHausdorff_iff_fixedLength {X : Type u} {Y : Type v}
    [EMetricSpace X] [TopologicalSpace Y] {f : Tuple X → Y} :
    @Continuous (Tuple X) Y (tupleHausdorffMetricTopology (X := X))
      inferInstance f ↔
      ∀ n : ℕ, Continuous (fun x : Fin n → X => f (Sigma.mk n x)) := by
  rw [continuous_tupleHausdorff_iff_tupleSup]
  exact DisjointUnionTopology.continuous_metricTopology_pasting_iff
    (X := fun n : ℕ => Fin n → X)

/-! ## Borel Standard Machinery -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: measurable convention in `thm:the-standard-machinery`.

Informal statement: the Borel sigma-algebra generated by the tuple Hausdorff
topology.
-/
@[reducible]
noncomputable def tupleHausdorffBorel {X : Type u} [EMetricSpace X] :
    MeasurableSpace (Tuple X) :=
  @borel (Tuple X) (tupleHausdorffMetricTopology (X := X))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: measurable convention in `thm:the-standard-machinery`.

Informal statement: the Borel sigma-algebra generated by the thesis `d∞`
topology on tuple space.
-/
@[reducible]
noncomputable def tupleSupBorel {X : Type u} [EMetricSpace X] :
    MeasurableSpace (Tuple X) :=
  @borel (Tuple X)
    (DisjointUnionTopology.disjointUnionMetricTopology
      (X := fun n : ℕ => Fin n → X))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, Borel equivalence.

Informal statement: the tuple Hausdorff and `d∞` topologies generate the same
Borel sigma-algebra.
-/
theorem tupleHausdorffBorel_eq_tupleSupBorel {X : Type u} [EMetricSpace X] :
    tupleHausdorffBorel (X := X) = tupleSupBorel (X := X) := by
  unfold tupleHausdorffBorel tupleSupBorel
  rw [tupleHausdorffMetricTopology_eq_tupleSup]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, measurable fixed-layer bridge.

Informal statement: the `d∞` Borel sigma-algebra is the Sigma measurable
structure generated by the Borel sigma-algebras on each fixed-length product
layer.

Lean strategy / thesis relation note: this specializes the countable disjoint-union Borel bridge to
the thesis tuple decomposition `\mathscr{T}(X)=\bigsqcup_n X^n`.

Lean strategy / thesis strategy note: this is the Sigma-Borel bridge used by the final
fixed-length measurability clause of `thm:the-standard-machinery`.
-/
theorem tupleSupBorel_eq_sigma {X : Type u} [EMetricSpace X] :
    tupleSupBorel (X := X) =
      @Sigma.instMeasurableSpace ℕ (fun n : ℕ => Fin n → X)
        (fun n => @borel (Fin n → X) inferInstance) := by
  exact DisjointUnionTopology.borel_metricTopology_eq_sigma
    (A := ℕ) (X := fun n : ℕ => Fin n → X)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, measurability equivalence.

Informal statement: a map out of tuple space is Borel measurable for the
tuple Hausdorff topology iff it is Borel measurable for the thesis `d∞`
topology.
-/
theorem measurable_tupleHausdorff_iff_tupleSup {X : Type u} {Y : Type v}
    [EMetricSpace X] [MeasurableSpace Y] {f : Tuple X → Y} :
    @Measurable (Tuple X) Y (tupleHausdorffBorel (X := X))
      inferInstance f ↔
      @Measurable (Tuple X) Y (tupleSupBorel (X := X)) inferInstance f := by
  rw [tupleHausdorffBorel_eq_tupleSupBorel]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: `thm:the-standard-machinery`, fixed-layer measurability.

Informal statement: a map out of tuple space is Borel measurable iff each
fixed-length restriction is Borel measurable.

Lean strategy / thesis relation note: the thesis invokes the standard measurable pasting lemma for a
countable disjoint union. Lean proves it by first rewriting the tuple
Hausdorff Borel structure to the `d∞` Borel structure, then to the Sigma
measurable structure on the fixed-length layers.
-/
theorem measurable_tupleHausdorff_iff_fixedLength {X : Type u} {Y : Type v}
    [EMetricSpace X] [MeasurableSpace Y] {f : Tuple X → Y} :
    @Measurable (Tuple X) Y (tupleHausdorffBorel (X := X))
      inferInstance f ↔
      ∀ n : ℕ,
        @Measurable (Fin n → X) Y (@borel (Fin n → X) inferInstance)
          inferInstance (fun x : Fin n → X => f (Sigma.mk n x)) := by
  rw [measurable_tupleHausdorff_iff_tupleSup]
  rw [tupleSupBorel_eq_sigma]
  letI : ∀ n : ℕ, MeasurableSpace (Fin n → X) :=
    fun n => @borel (Fin n → X) inferInstance
  exact DisjointUnionTopology.measurable_pasting_iff
    (X := fun n : ℕ => Fin n → X)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: completeness part of `cor:tuple-metrization`.

Informal statement: if `X` is complete, then tuple space with `d∞` is
complete.
-/
theorem tupleSup_completeSpace {X : Type u} [EMetricSpace X] [CompleteSpace X] :
    @CompleteSpace (Tuple X)
      (@PseudoEMetricSpace.toUniformSpace (Tuple X)
        (tupleSupEMetricSpace (X := X)).toPseudoEMetricSpace) := by
  exact DisjointUnionTopology.completeSpace
    (A := ℕ) (X := fun n : ℕ => Fin n → X)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
subsection "The Tuple Topology".

Original label: separability part of `cor:tuple-metrization`.

Informal statement: if `X` is separable, then tuple space with `d∞` is
separable.
-/
theorem tupleSup_separableSpace {X : Type u} [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] :
    @TopologicalSpace.SeparableSpace (Tuple X)
      (DisjointUnionTopology.disjointUnionMetricTopology
        (X := fun n : ℕ => Fin n → X)) := by
  exact DisjointUnionTopology.separableSpace_metricTopology_of_countable
    (A := ℕ) (X := fun n : ℕ => Fin n → X)

end TuplesMetricTopology
end MarketRepresentation
end Foundations
end Thesis
