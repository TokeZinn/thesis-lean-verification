import Thesis.Foundations.MarketRepresentation.DisjointUnion
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Constructions
import Mathlib.Topology.EMetricSpace.Basic

/-!
# Market Representation: Topology of Disjoint Unions

Formalizes the first results from
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "A Topology for Orders".

This module covers:

* `defn:disjoint-union-metrisation`;
* `prop:disjoint-union-metrisation`;
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

/-- Thesis `defn:disjoint-union-metrisation`.

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

/-- Thesis `prop:disjoint-union-metrisation`.

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

/-- Thesis `defn:disjoint-union-metrisation`, different-component clause. -/
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

/-- Thesis topology bridge for `defn:disjoint-union-metrisation`.

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

/-- Thesis topology bridge for `defn:disjoint-union-metrisation`.

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

/-- Alternative route for `thm:pasting-lemma` (not the mapped proof).

Sigma-topology version for arbitrary topological components: a function out of
a disjoint union is continuous exactly when its restriction to every component
is continuous. This is mathlib's Sigma-topology pasting lemma
`continuous_sigma_iff`, restated with thesis terminology. The thesis's own
metric argument is `continuous_metricTopology_pasting_iff` below.
-/
theorem continuous_pasting_iff {A : Type u} {X : A → Type v} {Y : Type w}
    [∀ a, TopologicalSpace (X a)] [TopologicalSpace Y] {f : DisjointUnion X → Y} :
    Continuous f ↔ ∀ a, Continuous (fun x => f (Sigma.mk a x)) :=
  continuous_sigma_iff

/-- Thesis `thm:pasting-lemma`.

A function `f` out of the disjoint-union metric space is continuous exactly
when every restriction `f ∘ ι_α : x ↦ f (x, α)` is continuous.

Lean strategy / thesis relation note: the proof is the thesis's function-level
`ε`-`δ` argument, not the Sigma-topology shortcut. Forward direction: fix `α`,
`x₀ ∈ X_α` and a neighbourhood of `f (x₀, α)`; continuity of `f` at `(x₀, α)`
gives a radius `δ`, and `d((x, α), (x₀, α)) = d_α(x, x₀)`
(`disjointEdist_mk_mk_same`) turns it into a radius for `f ∘ ι_α` at `x₀`.
Converse: fix `(x₀, α₀)`; continuity of `f ∘ ι_{α₀}` at `x₀` gives `δ₀`; with
`δ = min(δ₀, 1/2)` every point within `δ` of `(x₀, α₀)` has tag `α₀`
(`tag_eq_of_edist_lt_top`), so the component estimate applies. The target `Y`
is only assumed topological, so the thesis's `ε`-ball in `Y` is an arbitrary
neighbourhood of `f (x₀, α₀)`; the thesis statement (metric `Y`) is the special
case.
-/
theorem continuous_metricTopology_pasting_iff {A : Type u} {X : A → Type v}
    {Y : Type w} [∀ a, EMetricSpace (X a)] [TopologicalSpace Y]
    {f : DisjointUnion X → Y} :
    @Continuous (DisjointUnion X) Y (disjointUnionMetricTopology (X := X))
      inferInstance f ↔
      ∀ a, Continuous (fun x => f (Sigma.mk a x)) := by
  letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
  letI : TopologicalSpace (DisjointUnion X) := disjointUnionMetricTopology (X := X)
  change Continuous f ↔ _
  constructor
  · -- Forward direction: fix `α`, `x₀ ∈ X_α` and a neighbourhood `V` of `f (x₀, α)`.
    intro hf a
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [ContinuousAt, Filter.tendsto_def]
    intro V hV
    -- Continuity of `f` at `(x₀, α)` yields a radius `δ`.
    have hV' : f ⁻¹' V ∈ nhds (Sigma.mk a x₀ : DisjointUnion X) :=
      Filter.tendsto_def.mp (hf.continuousAt (x := Sigma.mk a x₀)) V hV
    rw [EMetric.mem_nhds_iff] at hV'
    rcases hV' with ⟨δ, hδ, hball⟩
    rw [EMetric.mem_nhds_iff]
    refine ⟨δ, hδ, fun x hx => ?_⟩
    change f (Sigma.mk a x) ∈ V
    apply hball
    -- The same `δ` works for `f ∘ ι_α`, since `d((x, α), (x₀, α)) = d_α(x, x₀)`.
    change disjointEdist (Sigma.mk a x : DisjointUnion X) (Sigma.mk a x₀) < δ
    simpa only [Metric.mem_eball, disjointEdist_mk_mk_same] using hx
  · -- Converse: fix `(x₀, α₀)` and a neighbourhood `V` of `f (x₀, α₀)`.
    intro hf
    rw [continuous_iff_continuousAt]
    rintro ⟨a, x₀⟩
    rw [ContinuousAt, Filter.tendsto_def]
    intro V hV
    -- Continuity of `f ∘ ι_{α₀}` at `x₀` yields `δ₀`.
    have hV' : (fun x => f (Sigma.mk a x)) ⁻¹' V ∈ nhds x₀ :=
      Filter.tendsto_def.mp ((hf a).continuousAt (x := x₀)) V hV
    rw [EMetric.mem_nhds_iff] at hV'
    rcases hV' with ⟨δ₀, hδ₀, hball⟩
    rw [EMetric.mem_nhds_iff]
    -- Set `δ = min(δ₀, 1/2)`.
    refine ⟨min δ₀ (1 / 2), lt_min hδ₀ (ENNReal.half_pos one_ne_zero), ?_⟩
    rintro ⟨b, x⟩ hx
    rw [Metric.mem_eball] at hx
    -- `d((x, α), (x₀, α₀)) < δ ≤ 1/2 < ∞` forces `α = α₀` by the definition of the metric.
    have htag : b = a := tag_eq_of_edist_lt_top (X := X)
      (lt_of_lt_of_le hx ((min_le_right δ₀ (1 / 2)).trans
        (ENNReal.div_lt_top ENNReal.one_ne_top two_ne_zero).le))
    subst b
    -- Hence the component estimate for `f ∘ ι_{α₀}` applies.
    change f (Sigma.mk a x) ∈ V
    apply hball
    rw [Metric.mem_eball]
    change disjointEdist (Sigma.mk a x : DisjointUnion X) (Sigma.mk a x₀) < min δ₀ (1 / 2) at hx
    exact lt_of_lt_of_le (by simpa only [disjointEdist_mk_mk_same] using hx)
      (min_le_left δ₀ (1 / 2))

/-- Alternative route for `thm:pasting-lemma-measurable` (not the mapped proof).

Abstract direct-sum version: for arbitrary measurable spaces on the components
and mathlib's Sigma measurable structure on the disjoint union (the "direct sum
of measurable spaces" of the remark following the thesis theorem), a function
out of the disjoint union is measurable exactly when its restriction to every
component is measurable. No countability is needed here, and the proof is
sigma-algebra lattice algebra. The thesis's own Borel argument for a countable
family of metric spaces is `measurable_metricTopology_pasting_iff` below.
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

/-- Thesis `thm:pasting-lemma-measurable`, first step.

The canonical injection `ι_α : X_α → X`, `x ↦ (x, α)`, is an isometry for the
thesis disjoint-union metric, since `d((x, α), (x', α)) = d_α(x, x')`.
-/
theorem isometry_sigmaMk {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] (a : A) :
    letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
    Isometry (Sigma.mk a : X a → DisjointUnion X) := by
  letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
  change ∀ x y : X a, edist (Sigma.mk a x : DisjointUnion X) (Sigma.mk a y) = edist x y
  intro x y
  exact disjointEdist_mk_mk_same x y

/-- Thesis `thm:pasting-lemma-measurable`, first step.

Each component `X_α × {α} = ι_α(X_α)` is open in the disjoint-union metric
space: the ball of radius `1/2` around `(x, α)` stays inside the component,
because points at finite distance share the tag.
-/
theorem isOpen_range_sigmaMk_metricTopology {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] (a : A) :
    @IsOpen (DisjointUnion X) (disjointUnionMetricTopology (X := X))
      (Set.range (Sigma.mk a : X a → DisjointUnion X)) := by
  letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
  letI : TopologicalSpace (DisjointUnion X) := disjointUnionMetricTopology (X := X)
  change IsOpen (Set.range (Sigma.mk a : X a → DisjointUnion X))
  rw [EMetric.isOpen_iff]
  rintro z ⟨x, rfl⟩
  refine ⟨1 / 2, ENNReal.half_pos one_ne_zero, ?_⟩
  rintro ⟨b, y⟩ hy
  rw [Metric.mem_eball] at hy
  have htag : b = a := tag_eq_of_edist_lt_top (X := X)
    (hy.trans (ENNReal.div_lt_top ENNReal.one_ne_top two_ne_zero))
  subst b
  exact ⟨y, rfl⟩

/-- Thesis `thm:pasting-lemma-measurable`, first step.

The canonical injection `ι_α` is a homeomorphism onto the open component
`X_α × {α}`, i.e. an open embedding for the disjoint-union metric topology.
-/
theorem isOpenEmbedding_sigmaMk_metricTopology {A : Type u} {X : A → Type v}
    [∀ a, EMetricSpace (X a)] (a : A) :
    @Topology.IsOpenEmbedding (X a) (DisjointUnion X) inferInstance
      (disjointUnionMetricTopology (X := X)) (Sigma.mk a) := by
  letI : EMetricSpace (DisjointUnion X) := disjointUnionEMetricSpace (X := X)
  letI : TopologicalSpace (DisjointUnion X) := disjointUnionMetricTopology (X := X)
  exact ⟨(isometry_sigmaMk (X := X) a).isEmbedding,
    isOpen_range_sigmaMk_metricTopology (X := X) a⟩

/--
Thesis `thm:pasting-lemma-measurable`.

For a countable family of metric spaces, a function `f` from the disjoint-union
metric space (with its Borel sigma-algebra) to a measurable space is measurable
exactly when every restriction `f ∘ ι_α : x ↦ f (x, α)` is Borel measurable.

Lean strategy / thesis relation note: the proof follows the thesis's two
directions rather than the Sigma-structure bridge. First, `ι_α` is an isometry
onto the open component `X_α × {α}` (`isometry_sigmaMk`,
`isOpen_range_sigmaMk_metricTopology`), hence a homeomorphism onto a Borel set
(`isOpenEmbedding_sigmaMk_metricTopology`). Forward direction:
`(f ∘ ι_α)⁻¹(B) = ι_α⁻¹(f⁻¹(B))` is Borel because `ι_α` is continuous.
Converse: `f⁻¹(B) = ⋃_α ι_α((f ∘ ι_α)⁻¹(B))`; each image is Borel because
`ι_α` is a measurable embedding onto a Borel set, and the union is countable.
-/
theorem measurable_metricTopology_pasting_iff {A : Type u} {X : A → Type v}
    {Y : Type w} [Countable A] [∀ a, EMetricSpace (X a)] [MeasurableSpace Y]
    {f : DisjointUnion X → Y} :
    @Measurable (DisjointUnion X) Y
      (@borel (DisjointUnion X) (disjointUnionMetricTopology (X := X)))
      inferInstance f ↔
      ∀ a, @Measurable (X a) Y (@borel (X a) inferInstance) inferInstance
        (fun x => f (Sigma.mk a x)) := by
  letI : TopologicalSpace (DisjointUnion X) := disjointUnionMetricTopology (X := X)
  letI : MeasurableSpace (DisjointUnion X) := borel (DisjointUnion X)
  haveI : BorelSpace (DisjointUnion X) := ⟨rfl⟩
  letI : ∀ a, MeasurableSpace (X a) := fun a => borel (X a)
  haveI : ∀ a, BorelSpace (X a) := fun a => ⟨rfl⟩
  -- `ι_α` is a homeomorphism onto the open, hence Borel, component `X_α × {α}`.
  have hι : ∀ a, Topology.IsOpenEmbedding (Sigma.mk a : X a → DisjointUnion X) :=
    fun a => isOpenEmbedding_sigmaMk_metricTopology (X := X) a
  constructor
  · -- `(f ∘ ι_α)⁻¹(B) = ι_α⁻¹(f⁻¹(B))`, and `ι_α` is continuous, hence Borel measurable.
    intro hf a
    exact hf.comp (hι a).continuous.measurable
  · intro hf B hB
    -- `f⁻¹(B) = ⋃_α ι_α((f ∘ ι_α)⁻¹(B))`.
    have hunion :
        f ⁻¹' B = ⋃ a, Sigma.mk a '' ((fun x => f (Sigma.mk a x)) ⁻¹' B) := by
      ext ⟨a, x⟩
      constructor
      · intro hz
        exact Set.mem_iUnion.2 ⟨a, x, hz, rfl⟩
      · intro hz
        rcases Set.mem_iUnion.1 hz with ⟨b, y, hy, hzy⟩
        rw [← hzy]
        exact hy
    rw [hunion]
    -- Each image is Borel since `ι_α` is a measurable embedding; the union is countable.
    exact MeasurableSet.iUnion fun a =>
      (hι a).measurableEmbedding.measurableSet_image.mpr (hf a hB)

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
