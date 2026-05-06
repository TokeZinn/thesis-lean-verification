import Foundations.MarketRepresentation.DisjointUnion
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Constructions
import Mathlib.Topology.EMetricSpace.Basic

/-!
# Market Representation: Topology of Disjoint Unions

Formalizes the first results from
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "A Topology for Orders".

This module covers:

* `defn:disjoint-union-metrization`;
* `prop:disjoint-union-metrization`;
* the topology bridge between the thesis extended metric and mathlib's Sigma
  coproduct topology;
* the completeness and countable-index separability parts of
  `prop:disjoint-union-metric-properties`;
* `thm:pasting-lemma`;
* `thm:pasting-lemma-measurable`.

Lean/type-theory note: the thesis metric takes value `∞` between different
components. Lean represents this directly with `EMetricSpace` and `ℝ≥0∞`
(`ENNReal`). Mathlib also has a built-in coproduct topology on `Σ a, X a`.
The theorem `metricTopology_eq_sigma` proves these two topologies coincide,
so later topological arguments can move between metric balls and Sigma
component restrictions.
-/

universe u v

namespace Thesis
namespace Foundations
namespace MarketRepresentation
namespace DisjointUnionTopology

/-- Thesis `defn:disjoint-union-metrization`.

The extended distance on a disjoint union: use the component distance for
points with the same tag, and `∞` for points from different components.
-/
noncomputable def disjointEdist {A : Type u} {X : A → Type v}
    [∀ a, EDist (X a)] (z w : DisjointUnion X) : ENNReal := by
  classical
  exact
    match z, w with
    | ⟨a, x⟩, ⟨b, y⟩ =>
        if h : a = b then edist (h ▸ x) y else ⊤

@[simp]
theorem disjointEdist_mk_mk_same {A : Type u} {X : A → Type v}
    [∀ a, EDist (X a)] {a : A} (x y : X a) :
    disjointEdist (Sigma.mk a x : DisjointUnion X) (Sigma.mk a y) = edist x y := by
  simp [disjointEdist]

@[simp]
theorem disjointEdist_mk_mk_ne {A : Type u} {X : A → Type v}
    [∀ a, EDist (X a)] {a b : A} (h : a ≠ b) (x : X a) (y : X b) :
    disjointEdist (Sigma.mk a x : DisjointUnion X) (Sigma.mk b y) = ⊤ := by
  simp [disjointEdist, h]

/-- Thesis `prop:disjoint-union-metrization`.

The extended disjoint-union distance is an `EMetricSpace`. This is intentionally
not registered as a global instance: mathlib already provides a Sigma topology,
and we prove below that the topology induced by this explicit metric agrees
with mathlib's topology.
-/
@[reducible]
noncomputable def disjointUnionEMetricSpace {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] : EMetricSpace (DisjointUnion X) where
  edist := disjointEdist
  edist_self := by
    rintro ⟨a, x⟩
    simp [disjointEdist]
  edist_comm := by
    rintro ⟨a, x⟩ ⟨b, y⟩
    by_cases h : a = b
    · subst b
      simpa [disjointEdist] using edist_comm x y
    · have hba : b ≠ a := by
        intro hb
        exact h hb.symm
      simp [disjointEdist, h, hba]
  edist_triangle := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩
    by_cases hab : a = b
    · subst b
      by_cases hac : a = c
      · subst c
        simpa [disjointEdist] using edist_triangle x y z
      · simp [disjointEdist, hac]
    · simp [disjointEdist, hab]
  eq_of_edist_eq_zero := by
    rintro ⟨a, x⟩ ⟨b, y⟩ hxy
    by_cases h : a = b
    · subst b
      simp [disjointEdist] at hxy
      subst y
      rfl
    · simp [disjointEdist, h] at hxy

/-- The topology induced by the thesis extended disjoint-union metric. -/
@[reducible]
noncomputable def disjointUnionMetricTopology {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] : TopologicalSpace (DisjointUnion X) := by
  letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
  exact PseudoEMetricSpace.toUniformSpace.toTopologicalSpace

theorem sigma_mk_cast_eq {A : Type u} {X : A → Type v} {a b : A}
    (h : b = a) (x : X b) :
    Sigma.mk a (h ▸ x) = (Sigma.mk b x : DisjointUnion X) := by
  cases h
  rfl

/-- Thesis `defn:disjoint-union-metrization`, different-component clause. -/
theorem edist_eq_top_of_tag_ne {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] {z w : DisjointUnion X} (h : z.1 ≠ w.1) :
    letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
    edist z w = ⊤ := by
  rcases z with ⟨a, x⟩
  rcases w with ⟨b, y⟩
  change disjointEdist (Sigma.mk a x : DisjointUnion X) (Sigma.mk b y) = ⊤
  exact disjointEdist_mk_mk_ne h x y

/-- Finite extended distance forces points to lie in the same component. -/
theorem tag_eq_of_edist_lt_top {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] {z w : DisjointUnion X} :
    letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
    edist z w < ⊤ → z.1 = w.1 := by
  letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
  intro hlt
  change edist z w < ⊤ at hlt
  by_contra hne
  have hdist : edist z w = (⊤ : ENNReal) := edist_eq_top_of_tag_ne (X := X) hne
  rw [hdist] at hlt
  exact (not_top_lt hlt).elim

/-- Thesis topology bridge for `defn:disjoint-union-metrization`.

A set is open in the topology induced by the thesis extended metric iff each
component restriction is open. This is the componentwise Sigma-topology
characterization.
-/
theorem metricTopology_isOpen_iff {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] {s : Set (DisjointUnion X)} :
    @IsOpen (DisjointUnion X) (disjointUnionMetricTopology (X := X)) s ↔
      ∀ a, IsOpen (Sigma.mk a ⁻¹' s) := by
  constructor
  · intro hs a
    rw [isOpen_iff_mem_nhds]
    intro x hx
    letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
    letI : TopologicalSpace (DisjointUnion X) := disjointUnionMetricTopology (X := X)
    change IsOpen s at hs
    have hs_mem : s ∈ nhds (Sigma.mk a x : DisjointUnion X) :=
      (isOpen_iff_mem_nhds.mp hs) (Sigma.mk a x) hx
    rw [EMetric.mem_nhds_iff] at hs_mem
    rcases hs_mem with ⟨ε, hε, hball⟩
    rw [EMetric.mem_nhds_iff]
    refine ⟨ε, hε, ?_⟩
    intro y hy
    apply hball
    change disjointEdist (Sigma.mk a y : DisjointUnion X) (Sigma.mk a x) < ε
    simpa using hy
  · intro hs
    letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
    letI : TopologicalSpace (DisjointUnion X) := disjointUnionMetricTopology (X := X)
    change IsOpen s
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases z with ⟨a, x⟩
    have hpre_open : IsOpen (Sigma.mk a ⁻¹' s) := hs a
    have hpre_mem : (Sigma.mk a ⁻¹' s) ∈ nhds x :=
      (isOpen_iff_mem_nhds.mp hpre_open) x hz
    rw [EMetric.mem_nhds_iff] at hpre_mem
    rcases hpre_mem with ⟨ε, hε, hball⟩
    rw [EMetric.mem_nhds_iff]
    let δ : ENNReal := min ε 1
    have hδpos : 0 < δ := lt_min hε zero_lt_one
    refine ⟨δ, hδpos, ?_⟩
    intro w hw
    have hδtop : δ < (⊤ : ENNReal) :=
      lt_of_le_of_lt (min_le_right ε (1 : ENNReal)) ENNReal.one_lt_top
    have htop : edist w (Sigma.mk a x : DisjointUnion X) < ⊤ := lt_trans hw hδtop
    have htag : w.1 = a := tag_eq_of_edist_lt_top (X := X) htop
    rcases w with ⟨b, y⟩
    dsimp at htag
    subst b
    apply hball
    have hle : δ ≤ ε := min_le_left ε 1
    have hy : edist y x < δ := by
      change disjointEdist (Sigma.mk a y : DisjointUnion X) (Sigma.mk a x) < δ at hw
      simpa using hw
    exact lt_of_lt_of_le hy hle

/-- Thesis topology bridge for `defn:disjoint-union-metrization`.

The topology induced by the thesis extended metric is exactly mathlib's native
Sigma coproduct topology. This theorem resolves the Lean instance mismatch:
metric arguments can be rewritten to componentwise Sigma arguments, and
componentwise topological arguments can be rewritten back to metric arguments.
-/
theorem metricTopology_eq_sigma {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] :
    disjointUnionMetricTopology (X := X) = instTopologicalSpaceSigma := by
  rw [TopologicalSpace.ext_iff]
  intro s
  rw [metricTopology_isOpen_iff, isOpen_sigma_iff]

/-- Thesis `thm:pasting-lemma`.

A function out of a disjoint union is continuous exactly when its restriction
to every component is continuous. This is mathlib's Sigma-topology pasting
lemma, restated with thesis terminology.
-/
theorem continuous_pasting_iff {A : Type u} {X : A → Type v} {Y : Type w}
    [∀ a, TopologicalSpace (X a)] [TopologicalSpace Y] {f : DisjointUnion X → Y} :
    Continuous f ↔ ∀ a, Continuous (fun x => f (Sigma.mk a x)) :=
  continuous_sigma_iff

/-- Thesis `thm:pasting-lemma`, metric-topology version.

Using `metricTopology_eq_sigma`, the same pasting statement holds when the
source topology is the thesis extended-metric topology rather than the default
Sigma topology.
-/
theorem continuous_metricTopology_pasting_iff {A : Type u} {X : A → Type v}
    {Y : Type w} [∀ a, EMetricSpace (X a)] [TopologicalSpace Y]
    {f : DisjointUnion X → Y} :
    @Continuous (DisjointUnion X) Y (disjointUnionMetricTopology (X := X))
      inferInstance f ↔
      ∀ a, Continuous (fun x => f (Sigma.mk a x)) := by
  rw [metricTopology_eq_sigma]
  exact continuous_sigma_iff

/-- Thesis `thm:pasting-lemma-measurable`.

A function out of a disjoint union is measurable exactly when its restriction
to every component is measurable. Lean formulates this for the Sigma
measurable structure, the measurable analogue of the topological coproduct.
-/
theorem measurable_pasting_iff {A : Type u} {X : A → Type v} {Y : Type w}
    [∀ a, MeasurableSpace (X a)] [MeasurableSpace Y]
    {f : DisjointUnion X → Y} :
    Measurable f ↔ ∀ a, Measurable (fun x => f (Sigma.mk a x)) := by
  rw [measurable_iff_le_map]
  rw [Sigma.instMeasurableSpace, MeasurableSpace.map_iInf]
  simp_rw [MeasurableSpace.map_comp]
  constructor
  · intro h a
    rw [measurable_iff_le_map]
    exact le_iInf_iff.mp h a
  · intro h
    rw [le_iInf_iff]
    intro a
    rw [← measurable_iff_le_map]
    exact h a

/--
Thesis `thm:pasting-lemma-measurable`, measurable-structure bridge.

For a countable disjoint union, the Borel sigma-algebra of mathlib's Sigma
coproduct topology is exactly the Sigma measurable structure generated by the
Borel sigma-algebras on the components.

Lean strategy / thesis relation note: this is the measurable analogue of `metricTopology_eq_sigma`.
The countability hypothesis is used in the reverse inclusion, where a set in
the Sigma measurable structure is reconstructed as a countable union of its
componentwise images.
-/
theorem borel_sigma_eq {A : Type u} {X : A → Type v} [Countable A]
    [∀ a, TopologicalSpace (X a)] :
    @borel (DisjointUnion X) instTopologicalSpaceSigma =
      @Sigma.instMeasurableSpace A X
        (fun a => @borel (X a) inferInstance) := by
  letI : ∀ a, MeasurableSpace (X a) := fun a => @borel (X a) inferInstance
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    have hmeas_prop :
        @Measurable (DisjointUnion X) Prop
          (@Sigma.instMeasurableSpace A X
            (fun a => @borel (X a) inferInstance))
          inferInstance (fun z => z ∈ s) := by
      rw [measurable_pasting_iff]
      intro a
      have hopen : IsOpen (Sigma.mk a ⁻¹' s) :=
        (isOpen_sigma_iff.mp hs) a
      exact measurableSet_setOf.mp
        (MeasurableSpace.measurableSet_generateFrom hopen)
    simpa using measurableSet_setOf.mpr hmeas_prop
  · change
      (@Sigma.instMeasurableSpace A X
          (fun a => @borel (X a) inferInstance)) ≤
        (@borel (DisjointUnion X) instTopologicalSpaceSigma)
    rw [MeasurableSpace.le_def]
    change ∀ s,
      @MeasurableSet (DisjointUnion X)
          (@Sigma.instMeasurableSpace A X
            (fun a => @borel (X a) inferInstance)) s →
        @MeasurableSet (DisjointUnion X)
          (@borel (DisjointUnion X) instTopologicalSpaceSigma) s
    intro s hs
    rw [Sigma.instMeasurableSpace, MeasurableSpace.measurableSet_iInf] at hs
    have himage : ∀ a,
        @MeasurableSet (DisjointUnion X)
          (@borel (DisjointUnion X) instTopologicalSpaceSigma)
          (Sigma.mk a '' (Sigma.mk a ⁻¹' s)) := by
      intro a
      letI : TopologicalSpace (DisjointUnion X) := instTopologicalSpaceSigma
      letI : MeasurableSpace (DisjointUnion X) :=
        @borel (DisjointUnion X) instTopologicalSpaceSigma
      haveI : BorelSpace (DisjointUnion X) := ⟨rfl⟩
      haveI : BorelSpace (X a) := ⟨rfl⟩
      exact (Topology.IsOpenEmbedding.sigmaMk (i := a)).measurableEmbedding
        |>.measurableSet_image.mpr (hs a)
    have hunion : s = ⋃ a, Sigma.mk a '' (Sigma.mk a ⁻¹' s) := by
      ext z
      constructor
      · intro hz
        exact Set.mem_iUnion.2 ⟨z.1, ⟨z.2, hz, rfl⟩⟩
      · intro hz
        rcases Set.mem_iUnion.1 hz with ⟨a, y, hy, hzy⟩
        simpa [hzy] using hy
    rw [hunion]
    exact MeasurableSet.iUnion himage

/--
Thesis `thm:pasting-lemma-measurable`, measurable-structure bridge.

For a countable disjoint union equipped with the thesis extended metric, its
Borel sigma-algebra is the Sigma measurable structure generated by the Borel
sigma-algebras on the metric components.
-/
theorem borel_metricTopology_eq_sigma {A : Type u} {X : A → Type v}
    [Countable A] [∀ a, EMetricSpace (X a)] :
    @borel (DisjointUnion X) (disjointUnionMetricTopology (X := X)) =
      @Sigma.instMeasurableSpace A X
        (fun a => @borel (X a) inferInstance) := by
  rw [metricTopology_eq_sigma]
  exact borel_sigma_eq (X := X)

/--
Thesis `thm:pasting-lemma-measurable`, metric-Borel version.

A function from the thesis extended-metric disjoint union is Borel measurable
iff each component restriction is Borel measurable.

Lean strategy / thesis relation note: this is the exact bridge requested by the manuscript
formulation. The proof first rewrites the Borel sigma-algebra induced by the
extended metric to the Sigma measurable structure using
`borel_metricTopology_eq_sigma`, then applies the abstract Sigma measurable
pasting theorem `measurable_pasting_iff`.
-/
theorem measurable_metricTopology_pasting_iff {A : Type u} {X : A → Type v}
    {Y : Type w} [Countable A] [∀ a, EMetricSpace (X a)] [MeasurableSpace Y]
    {f : DisjointUnion X → Y} :
    @Measurable (DisjointUnion X) Y
      (@borel (DisjointUnion X) (disjointUnionMetricTopology (X := X)))
      inferInstance f ↔
      ∀ a, @Measurable (X a) Y (@borel (X a) inferInstance) inferInstance
        (fun x => f (Sigma.mk a x)) := by
  rw [borel_metricTopology_eq_sigma]
  letI : ∀ a, MeasurableSpace (X a) := fun a => @borel (X a) inferInstance
  exact measurable_pasting_iff (X := X) (Y := Y) (f := f)

/-- Cauchy sequences for the thesis metric eventually remain in one component. -/
theorem cauchySeq_eventually_constant_tag {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] {u : ℕ → DisjointUnion X} :
    letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
    CauchySeq u → ∃ a : A, ∀ᶠ n in Filter.atTop, (u n).1 = a := by
  letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
  intro hu
  change CauchySeq u at hu
  rcases (EMetric.cauchySeq_iff.1 hu) (1 : ENNReal) zero_lt_one with ⟨N, hN⟩
  refine ⟨(u N).1, Filter.eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn
  have hlt : edist (u N) (u n) < (⊤ : ENNReal) :=
    lt_trans (hN N le_rfl n hn) ENNReal.one_lt_top
  exact (tag_eq_of_edist_lt_top (X := X) hlt).symm

/-- Thesis `prop:disjoint-union-metric-properties`, completeness transfer.

If every component is complete, then the thesis extended metric on the disjoint
union is complete.
-/
theorem completeSpace {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] [∀ a, CompleteSpace (X a)] :
    letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
    CompleteSpace (DisjointUnion X) := by
  classical
  letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
  refine EMetric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  rcases cauchySeq_eventually_constant_tag (X := X) hu with ⟨a, htag_eventually⟩
  rcases Filter.eventually_atTop.1 htag_eventually with ⟨N, hNtag⟩
  let x0 : X a := hNtag N le_rfl ▸ (u N).2
  let v : ℕ → X a := fun n =>
    if hn : N ≤ n then hNtag n hn ▸ (u n).2 else x0
  have hv_eq : ∀ n, N ≤ n → Sigma.mk a (v n) = u n := by
    intro n hn
    change Sigma.mk a (if hn' : N ≤ n then hNtag n hn' ▸ (u n).2 else x0) = u n
    rw [dif_pos hn]
    calc
      Sigma.mk a (hNtag n hn ▸ (u n).2) =
          Sigma.mk (u n).1 (u n).2 :=
        sigma_mk_cast_eq (hNtag n hn) (u n).2
      _ = u n := by
        cases u n
        rfl
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
    have hdu : edist (u m) (u n) < ε := hM m hmM n hnM
    have hdu' :
        edist (Sigma.mk a (v m) : DisjointUnion X) (Sigma.mk a (v n)) < ε := by
      simpa [hv_eq m hmN, hv_eq n hnN] using hdu
    change
      disjointEdist (Sigma.mk a (v m) : DisjointUnion X) (Sigma.mk a (v n)) < ε
        at hdu'
    simpa using hdu'
  rcases cauchySeq_tendsto_of_complete hv_cauchy with ⟨x, hx⟩
  refine ⟨Sigma.mk a x, ?_⟩
  rw [EMetric.tendsto_nhds]
  intro ε hε
  rw [EMetric.tendsto_nhds] at hx
  have hx_ev := hx ε hε
  have hv_ev : ∀ᶠ n in Filter.atTop, Sigma.mk a (v n) = u n :=
    Filter.eventually_atTop.2 ⟨N, hv_eq⟩
  filter_upwards [hx_ev, hv_ev] with n hn hnv
  have hdu : edist (Sigma.mk a (v n) : DisjointUnion X) (Sigma.mk a x) < ε := by
    change disjointEdist (Sigma.mk a (v n) : DisjointUnion X) (Sigma.mk a x) < ε
    simpa using hn
  simpa [← hnv] using hdu

/-- Thesis `prop:disjoint-union-metric-properties`, separability transfer.

A countable Sigma coproduct of separable components is separable.
-/
theorem separableSpace_sigma_of_countable {A : Type u} {X : A → Type v}
    [Countable A] [∀ a, TopologicalSpace (X a)]
    [∀ a, TopologicalSpace.SeparableSpace (X a)] :
    TopologicalSpace.SeparableSpace (DisjointUnion X) := by
  classical
  choose D hD_count hD_dense using
    fun a => TopologicalSpace.exists_countable_dense (X a)
  refine ⟨⟨⋃ a, Sigma.mk a '' D a, ?_, ?_⟩⟩
  · exact Set.countable_iUnion (fun a => (hD_count a).image (Sigma.mk a))
  · intro z
    rcases z with ⟨a, x⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    have hpre : (Sigma.mk a ⁻¹' t) ∈ nhds x := continuous_sigmaMk.tendsto x ht
    have hnear : ((Sigma.mk a ⁻¹' t) ∩ D a).Nonempty :=
      mem_closure_iff_nhds.1 (hD_dense a x) (Sigma.mk a ⁻¹' t) hpre
    rcases hnear with ⟨y, hyt, hyD⟩
    exact ⟨Sigma.mk a y, hyt, Set.mem_iUnion.2 ⟨a, ⟨y, hyD, rfl⟩⟩⟩

/-- Thesis `prop:disjoint-union-metric-properties`, separability transfer.

Using `metricTopology_eq_sigma`, the same countable-index separability result
holds for the topology induced by the thesis extended metric.
-/
theorem separableSpace_metricTopology_of_countable {A : Type u} {X : A → Type v}
    [Countable A] [∀ a, EMetricSpace (X a)]
    [∀ a, TopologicalSpace.SeparableSpace (X a)] :
    @TopologicalSpace.SeparableSpace
      (DisjointUnion X) (disjointUnionMetricTopology (X := X)) := by
  rw [metricTopology_eq_sigma]
  exact separableSpace_sigma_of_countable (X := X)

end DisjointUnionTopology
end MarketRepresentation
end Foundations
end Thesis
