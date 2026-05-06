import Foundations.MarketRepresentation.DisjointUnionTopology
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Market Representation: Finite Sets and Hausdorff Distance

Formal content for
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

This file starts the thesis finite-set layer. The thesis treats finite sets
as ordinary sets with a finiteness condition; Lean records that condition in
the subtype

`{s : Set α // s.Finite}`.

This is not a ZFC encoding of the set of all finite subsets. It is the same
mathematical object as a Lean type, and we bridge it to mathlib's computable
finite-set object `Finset α` whenever we need finite/countable machinery.
-/

namespace Thesis
namespace Foundations
namespace MarketRepresentation
namespace FiniteSets

universe u

/-! ## Finite Subsets -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: definition of the space of finite subsets.

Informal statement: a point of the finite-subset space is a subset together
with a proof that it is finite.

Lean strategy / thesis relation note: the thesis speaks of the collection of finite subsets. Lean
uses a subtype of `Set α`, carrying the finiteness proof as data in the type.
-/
abbrev FiniteSubsets (α : Type u) : Type u := {s : Set α // s.Finite}

namespace FiniteSubsets

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary bridge for finite subsets.

Informal statement: every finite subset has an associated `Finset`.

Lean strategy / thesis relation note: this is the main Lean bridge from proof-carrying finite
subsets to mathlib's finite combinatorial object.
-/
noncomputable def toFinset {α : Type u} (s : FiniteSubsets α) : Finset α :=
  s.2.toFinset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary bridge for finite subsets.

Informal statement: the `Finset` associated to a finite subset has exactly the
same elements as the original subset.
-/
theorem coe_toFinset {α : Type u} (s : FiniteSubsets α) :
    ↑(toFinset s) = (s : Set α) :=
  Set.Finite.coe_toFinset s.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary bridge for finite subsets.

Informal statement: membership in the finite subset is equivalent to
membership in its associated `Finset`.
-/
theorem mem_toFinset {α : Type u} (s : FiniteSubsets α) {x : α} :
    x ∈ toFinset s ↔ x ∈ (s : Set α) :=
  Set.Finite.mem_toFinset s.2

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary bridge for `prop:countable-finite-sets`.

Informal statement: the representation map from proof-carrying finite subsets
to mathlib `Finset`s is injective.

Lean strategy / thesis relation note: the target is `Finset α`, mathlib's finite-set structure. The
result says no set-theoretic information is lost by passing through this
representation. The thesis proposition `prop:injection-into-finite-sets`
itself is the singleton injection formalized below as `singleton_injective`.
-/
theorem toFinset_injective {α : Type u} :
    Function.Injective (toFinset (α := α)) := by
  intro s t h
  apply Subtype.ext
  exact Set.Finite.toFinset_inj.mp h

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary singleton map for finite subsets.

Informal statement: each point of the ambient space determines a singleton
finite subset.
-/
def singleton {α : Type u} (x : α) : FiniteSubsets α :=
  ⟨{x}, Set.finite_singleton x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `prop:injection-into-finite-sets`.

Informal statement: the singleton map into finite subsets is injective.
-/
theorem singleton_injective {α : Type u} :
    Function.Injective (singleton (α := α)) := by
  intro x y h
  have hset : ({x} : Set α) = {y} := congrArg Subtype.val h
  simpa using hset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: finite subsets over a fixed base set.

Informal statement: `Of s` is the type of finite subsets contained in `s`.
-/
abbrev Of {α : Type u} (s : Set α) : Type u :=
  {t : FiniteSubsets α // (t : Set α) ⊆ s}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary map for `prop:finite-sets-over-finite-set`.

Informal statement: finite subsets of a finite base inject into the powerset
of the base `Finset`.
-/
noncomputable def ofFiniteSetEmbedding {α : Type u} {s : Set α} (hs : s.Finite) :
    Of s → {u : Finset α // u ∈ hs.toFinset.powerset} :=
  fun t => ⟨toFinset t.1, by
    rw [Finset.mem_powerset]
    rw [← Finset.coe_subset]
    intro x hx
    have hxset : x ∈ (t.1 : Set α) := (mem_toFinset t.1).mp hx
    exact (Set.Finite.mem_toFinset hs).mpr (t.2 hxset)⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary map for `prop:finite-sets-over-finite-set`.

Informal statement: the embedding of finite subsets into the base powerset is
injective.
-/
theorem ofFiniteSetEmbedding_injective {α : Type u} {s : Set α} (hs : s.Finite) :
    Function.Injective (ofFiniteSetEmbedding (α := α) hs) := by
  intro t u h
  apply Subtype.ext
  apply toFinset_injective
  exact congrArg Subtype.val h

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `prop:finite-sets-over-finite-set`.

Informal statement: if the base set `s` is finite, then finite subsets
contained in `s` are equivalent to arbitrary subsets of `s`.

Lean strategy / thesis relation note: this is the thesis equality `𝓕(X) = 𝒫(X)` for finite `X`,
stated as an equivalence between the subtype of finite subsets contained in
`s` and the ambient powerset subtype `{u : Set α // u ⊆ s}`. The inverse
uses the finite-base hypothesis to prove every subset of `s` is finite.
-/
noncomputable def ofFiniteSetEquivPowerset {α : Type u} {s : Set α} (hs : s.Finite) :
    Of s ≃ {u : Set α // u ⊆ s} where
  toFun t := ⟨(t.1 : Set α), t.2⟩
  invFun u := ⟨⟨u.1, hs.subset u.2⟩, u.2⟩
  left_inv := by
    intro t
    rfl
  right_inv := by
    intro u
    rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: consequence of `prop:finite-sets-over-finite-set`.

Informal statement: finite subsets contained in a finite base set form a
finite type.
-/
theorem finite_of_finite_set {α : Type u} {s : Set α} (hs : s.Finite) :
    Finite (Of s) := by
  haveI : Finite {u : Finset α // u ∈ hs.toFinset.powerset} :=
    (Finset.finite_toSet hs.toFinset.powerset).to_subtype
  exact Finite.of_injective (ofFiniteSetEmbedding (α := α) hs)
    (ofFiniteSetEmbedding_injective (α := α) hs)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: finite-base corollary for the whole ambient type.

Informal statement: if the ambient type is finite, then its finite-subset
space is finite.
-/
theorem finite_of_finite_type {α : Type u} [Finite α] :
    Finite (FiniteSubsets α) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  haveI : Finite (Finset α) := Finite.of_fintype (Finset α)
  exact Finite.of_injective (toFinset (α := α)) (toFinset_injective (α := α))

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `prop:countable-finite-sets`.

Informal statement: finite subsets of a countable ambient type form a
countable type.
-/
theorem countable {α : Type u} [Countable α] :
    Countable (FiniteSubsets α) := by
  haveI : Countable (Finset α) := Finset.countable
  exact Function.Injective.countable (toFinset_injective (α := α))

/-! ## Separability -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `defn:separable`.

Informal statement: a topological space is separable if it has a countable
dense subset.

Lean strategy / thesis relation note: mathlib packages the same assertion as the typeclass
`TopologicalSpace.SeparableSpace`; this definition keeps the thesis spelling
available as an explicit proposition.
-/
def ThesisSeparable (α : Type u) [TopologicalSpace α] : Prop :=
  ∃ s : Set α, s.Countable ∧ Dense s

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: compatibility lemma for `defn:separable`.

Informal statement: the thesis separability definition is equivalent to
mathlib's `SeparableSpace` typeclass.
-/
theorem thesisSeparable_iff_separableSpace {α : Type u} [TopologicalSpace α] :
    ThesisSeparable α ↔ TopologicalSpace.SeparableSpace α := by
  constructor
  · intro h
    exact ⟨h⟩
  · intro h
    letI : TopologicalSpace.SeparableSpace α := h
    exact TopologicalSpace.exists_countable_dense α

/-! ## Hausdorff Distance -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: real-valued compatibility form of `defn:Hausdorff-distance`.

Informal statement: the Hausdorff distance between two finite subsets is the
Hausdorff distance between their underlying sets.

Lean strategy / thesis relation note: mathlib defines this for all subsets of a pseudometric space.
The thesis uses the `[0,∞]`-valued convention. This real-valued wrapper is kept
only as a compatibility bridge to mathlib's ordinary `hausdorffDist`; it is not
the canonical thesis distance on `FiniteSubsets`.
-/
noncomputable def hausdorffDistance {α : Type u} [PseudoMetricSpace α]
    (s t : FiniteSubsets α) : ℝ :=
  Metric.hausdorffDist (s : Set α) (t : Set α)

/--
Thesis source:
`A - preliminary theory/analysis.tex`,
Proposition `prop:hausdorff-distance`, used in
`1 - theoretical foundations/2_chapter_market_representations.tex`.

Original label: `prop:hausdorff-distance`.

Informal statement: the extended Hausdorff distance on the full powerset
`𝒫(X)`.

Lean strategy / thesis relation note: the thesis states the background pseudometric theorem on
`𝒫(X)` before specializing to finite subsets. Mathlib defines
`Metric.hausdorffEDist` for arbitrary subsets; this wrapper keeps the
full-powerset theorem visible in the thesis namespace.
-/
noncomputable def powersetHausdorffEDistance {α : Type u} [PseudoEMetricSpace α]
    (s t : Set α) : ENNReal :=
  Metric.hausdorffEDist s t

/--
Thesis source:
`A - preliminary theory/analysis.tex`,
Proposition `prop:hausdorff-distance`.

Original label: `prop:hausdorff-distance`.

Informal statement: the full-powerset Hausdorff distance is zero on the
diagonal.
-/
theorem powersetHausdorffEDistance_self {α : Type u} [PseudoEMetricSpace α]
    (s : Set α) :
    powersetHausdorffEDistance s s = 0 :=
  Metric.hausdorffEDist_self

/--
Thesis source:
`A - preliminary theory/analysis.tex`,
Proposition `prop:hausdorff-distance`.

Original label: `prop:hausdorff-distance`.

Informal statement: the full-powerset Hausdorff distance is symmetric.
-/
theorem powersetHausdorffEDistance_comm {α : Type u} [PseudoEMetricSpace α]
    (s t : Set α) :
    powersetHausdorffEDistance s t = powersetHausdorffEDistance t s :=
  Metric.hausdorffEDist_comm

/--
Thesis source:
`A - preliminary theory/analysis.tex`,
Proposition `prop:hausdorff-distance`.

Original label: `prop:hausdorff-distance`.

Informal statement: the full-powerset Hausdorff distance satisfies the
triangle inequality.
-/
theorem powersetHausdorffEDistance_triangle {α : Type u} [PseudoEMetricSpace α]
    (s t u : Set α) :
    powersetHausdorffEDistance s u ≤
      powersetHausdorffEDistance s t + powersetHausdorffEDistance t u :=
  Metric.hausdorffEDist_triangle

/--
Thesis source:
`A - preliminary theory/analysis.tex`,
Proposition `prop:hausdorff-distance`.

Original label: `prop:hausdorff-distance`.

Informal statement: the full powerset `𝒫(X)`, equipped with the Hausdorff
extended distance, is an extended pseudometric space.

Lean strategy / thesis relation note: this is kept as a named structure rather
than a global instance on `Set α`, so it does not change mathlib's default
topology or measurable structure for sets. The finite-subset instance below is
the downstream specialization used in Chapter 2.
-/
@[reducible]
noncomputable def powersetPseudoEMetricSpace {α : Type u} [PseudoEMetricSpace α] :
    PseudoEMetricSpace (Set α) where
  edist := powersetHausdorffEDistance
  edist_self := powersetHausdorffEDistance_self
  edist_comm := powersetHausdorffEDistance_comm
  edist_triangle := powersetHausdorffEDistance_triangle

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `defn:Hausdorff-distance`.

Informal statement: the extended Hausdorff distance between finite subsets is
the extended Hausdorff distance between their underlying sets.

Lean strategy / thesis relation note: this is the thesis distance. It takes values in `ℝ≥0∞`
(`ENNReal`), matching the thesis codomain `[0,\infty]` and preserving the
empty-set convention.
-/
noncomputable def hausdorffEDistance {α : Type u} [PseudoEMetricSpace α]
    (s t : FiniteSubsets α) : ENNReal :=
  Metric.hausdorffEDist (s : Set α) (t : Set α)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: basic property for `defn:Hausdorff-distance`.

Informal statement: the extended Hausdorff distance from a finite subset to
itself is zero.
-/
theorem hausdorffEDistance_self {α : Type u} [PseudoEMetricSpace α]
    (s : FiniteSubsets α) :
    hausdorffEDistance s s = 0 :=
  Metric.hausdorffEDist_self

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: basic property for `defn:Hausdorff-distance`.

Informal statement: the extended Hausdorff distance is symmetric.
-/
theorem hausdorffEDistance_comm {α : Type u} [PseudoEMetricSpace α]
    (s t : FiniteSubsets α) :
    hausdorffEDistance s t = hausdorffEDistance t s :=
  Metric.hausdorffEDist_comm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: basic property for `defn:Hausdorff-distance`.

Informal statement: the extended Hausdorff distance satisfies the triangle
inequality.
-/
theorem hausdorffEDistance_triangle {α : Type u} [PseudoEMetricSpace α]
    (s t u : FiniteSubsets α) :
    hausdorffEDistance s u ≤ hausdorffEDistance s t + hausdorffEDistance t u :=
  Metric.hausdorffEDist_triangle

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: pseudometric part of `thm:Hausdorff-finite-sets`.

Informal statement: the thesis Hausdorff distance is the extended distance on
the finite-subset space.
-/
noncomputable instance instEDist {α : Type u} [PseudoEMetricSpace α] :
    EDist (FiniteSubsets α) where
  edist := hausdorffEDistance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: pseudometric part of `thm:Hausdorff-finite-sets`.

Informal statement: by the background Hausdorff-distance theorem, the extended
Hausdorff distance on finite subsets is a pseudometric.

Lean strategy / thesis relation note: the thesis cites the background result
`prop:hausdorff-distance`; in Lean this is provided by mathlib's Hausdorff
edistance lemmas.
-/
noncomputable instance instPseudoEMetricSpace {α : Type u} [PseudoEMetricSpace α] :
    PseudoEMetricSpace (FiniteSubsets α) where
  edist_self := hausdorffEDistance_self
  edist_comm := hausdorffEDistance_comm
  edist_triangle := hausdorffEDistance_triangle

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: empty finite subset.

Informal statement: the empty set is a finite subset.
-/
def empty {α : Type u} : FiniteSubsets α :=
  ⟨∅, Set.finite_empty⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `rem:hausdorff-convention`.

Informal statement: mathlib's real-valued Hausdorff distance assigns distance
zero to the empty-set case.

Lean strategy / thesis relation note: the thesis convention is better tracked by the extended
distance below, where nonempty-to-empty has distance `⊤`. This theorem records
mathlib's real-valued convention explicitly so later code cannot silently rely
on it.
-/
theorem hausdorffDistance_empty_right {α : Type u} [PseudoMetricSpace α]
    (s : FiniteSubsets α) :
    hausdorffDistance s (empty : FiniteSubsets α) = 0 :=
  Metric.hausdorffDist_empty

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `rem:hausdorff-convention`.

Informal statement: the real-valued empty-set convention is symmetric.
-/
theorem hausdorffDistance_empty_left {α : Type u} [PseudoMetricSpace α]
    (s : FiniteSubsets α) :
    hausdorffDistance (empty : FiniteSubsets α) s = 0 := by
  rw [hausdorffDistance, Metric.hausdorffDist_comm]
  exact Metric.hausdorffDist_empty

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `rem:hausdorff-convention`.

Informal statement: in the extended Hausdorff distance, a nonempty finite
subset is infinitely far from the empty finite subset.
-/
theorem hausdorffEDistance_empty_right {α : Type u} [PseudoEMetricSpace α]
    {s : FiniteSubsets α} (hs : (s : Set α).Nonempty) :
    hausdorffEDistance s (empty : FiniteSubsets α) = ⊤ :=
  Metric.hausdorffEDist_empty hs

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `rem:hausdorff-convention`.

Informal statement: the extended nonempty-to-empty convention is symmetric.
-/
theorem hausdorffEDistance_empty_left {α : Type u} [PseudoEMetricSpace α]
    {s : FiniteSubsets α} (hs : (s : Set α).Nonempty) :
    hausdorffEDistance (empty : FiniteSubsets α) s = ⊤ := by
  rw [hausdorffEDistance_comm]
  exact hausdorffEDistance_empty_right hs

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary closedness step in `thm:Hausdorff-finite-sets`.

Informal statement: finite subsets of a T1 topological space are closed.

Lean strategy / thesis relation note: the thesis proves separation through
finite minima/maxima. Lean uses the equivalent standard theorem that Hausdorff
edistance zero means equal closures, together with this finite-closedness lemma.
-/
theorem isClosed_coe {α : Type u} [TopologicalSpace α] [T1Space α]
    (s : FiniteSubsets α) : IsClosed (s : Set α) :=
  s.2.isClosed

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: separation step in `thm:Hausdorff-finite-sets`.

Informal statement: if two finite subsets are at extended Hausdorff distance
zero, then they are equal, and conversely.

Lean strategy / thesis relation note: this is the Lean version of the thesis proof's final
pseudometric-to-metric step. The empty-set cases are already covered by the
extended convention; the nonempty finite-set argument is compressed through
mathlib's theorem for closed sets.
-/
theorem hausdorffEDistance_eq_zero {α : Type u} [PseudoEMetricSpace α] [T1Space α]
    (s t : FiniteSubsets α) :
    hausdorffEDistance s t = 0 ↔ s = t := by
  constructor
  · intro h
    apply Subtype.ext
    exact (IsClosed.hausdorffEDist_zero_iff (isClosed_coe s) (isClosed_coe t)).mp h
  · intro h
    have hset : (s : Set α) = (t : Set α) := congrArg Subtype.val h
    exact (IsClosed.hausdorffEDist_zero_iff (isClosed_coe s) (isClosed_coe t)).mpr hset

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `thm:Hausdorff-finite-sets`.

Informal statement: if the ambient space is an extended metric space, then the
finite-subset space equipped with the thesis Hausdorff distance is an extended
metric space.

Lean strategy / thesis relation note: the thesis calls this a metric because its metrics take values
in `[0,\infty]`. Lean's matching structure is `EMetricSpace`, whose distance
takes values in `ℝ≥0∞`.
-/
noncomputable instance instEMetricSpace {α : Type u} [EMetricSpace α] :
    EMetricSpace (FiniteSubsets α) :=
  EMetricSpace.mk (by
    intro s t h
    exact (hausdorffEDistance_eq_zero s t).mp h)

/-! ## Finite-Set Separability -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary order-density lemma for
`prop:finite-separable` and `prop:finite-set-cauchy`.

Informal statement: below every positive extended radius there is a smaller
positive extended radius.

Lean strategy / thesis relation note: this lets the Lean proofs turn non-strict Hausdorff upper
bounds into the strict inequalities used in Cauchy and closure statements.
-/
theorem exists_pos_lt_ennreal {ε : ENNReal} (hε : 0 < ε) :
    ∃ δ : ENNReal, 0 < δ ∧ δ < ε := by
  by_cases htop : ε = ⊤
  · exact ⟨1, zero_lt_one, by simp [htop, ENNReal.one_lt_top]⟩
  · exact ⟨ε / 2, ENNReal.half_pos (ne_of_gt hε),
      ENNReal.half_lt_self (ne_of_gt hε) htop⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: quantitative radius choice used in
`property:distinct-finite-complete`.

Informal statement: below every positive radius there is a positive radius
which is at most `1`.
-/
theorem exists_pos_le_one_lt_ennreal {ε : ENNReal} (hε : 0 < ε) :
    ∃ δ : ENNReal, 0 < δ ∧ δ ≤ (1 : ENNReal) ∧ δ < ε := by
  by_cases hεle : ε ≤ (1 : ENNReal)
  · rcases exists_pos_lt_ennreal hε with ⟨δ, hδpos, hδε⟩
    exact ⟨δ, hδpos, le_trans hδε.le hεle, hδε⟩
  · exact ⟨1, zero_lt_one, le_rfl, lt_of_not_ge hεle⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary construction in `prop:finite-separable`.

Informal statement: finite subsets whose points all lie in a fixed set `U`.
-/
def finiteSubsetsOf {α : Type u} (U : Set α) : Set (FiniteSubsets α) :=
  {s | (s : Set α) ⊆ U}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: countability step in `prop:finite-separable`.

Informal statement: if `U` is countable, then the finite subsets supported on
`U` are countable.
-/
theorem finiteSubsetsOf_countable {α : Type u} {U : Set α} (hU : U.Countable) :
    (finiteSubsetsOf U).Countable := by
  have hSetCount : ({t : Set α | t.Finite ∧ t ⊆ U}).Countable :=
    Set.countable_setOf_finite_subset hU
  haveI : Countable {t : Set α // t.Finite ∧ t ⊆ U} := hSetCount.to_subtype
  let f : {s : FiniteSubsets α // s ∈ finiteSubsetsOf U} →
      {t : Set α // t.Finite ∧ t ⊆ U} :=
    fun s => ⟨s.1.1, s.1.2, s.2⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {t : Set α // t.Finite ∧ t ⊆ U} => (z : Set α)) h
  exact Function.Injective.countable hf

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: density step in `prop:finite-separable`.

Informal statement: if `U` is dense in `X`, then finite subsets supported on
`U` are dense in the finite-subset Hausdorff space.

Lean strategy / thesis relation note: this follows the thesis construction
pointwise: each point of a finite set is approximated by a nearby point of `U`,
and the approximating finite subset is the finite range of those chosen points.
-/
theorem finiteSubsetsOf_dense {α : Type u} [PseudoEMetricSpace α]
    {U : Set α} (hU : Dense U) : Dense (finiteSubsetsOf U) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.mpr
  intro s
  rw [EMetric.mem_closure_iff]
  intro ε hε
  rcases exists_pos_lt_ennreal hε with ⟨δ, hδpos, hδε⟩
  have hApprox : ∀ z : (s : Set α), ∃ u ∈ U, edist z.1 u < δ := by
    intro z
    have hzcl : z.1 ∈ closure U := by
      rw [dense_iff_closure_eq.mp hU]
      trivial
    exact (EMetric.mem_closure_iff.mp hzcl) δ hδpos
  choose u huU hu using hApprox
  haveI : Finite (s : Set α) := s.2.to_subtype
  let η : FiniteSubsets α := ⟨Set.range u, Set.finite_range u⟩
  refine ⟨η, ?_, ?_⟩
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    exact huU z
  · change hausdorffEDistance s η < ε
    have hle : hausdorffEDistance s η ≤ δ := by
      apply Metric.hausdorffEDist_le_of_mem_edist
      · intro x hx
        let z : (s : Set α) := ⟨x, hx⟩
        exact ⟨u z, by exact ⟨z, rfl⟩, le_of_lt (hu z)⟩
      · intro y hy
        rcases hy with ⟨z, rfl⟩
        exact ⟨z.1, z.2, by rw [edist_comm]; exact le_of_lt (hu z)⟩
    exact lt_of_le_of_lt hle hδε

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `prop:finite-separable`.

Informal statement: if the ambient space is separable, then its finite-subset
Hausdorff space is separable.
-/
theorem finiteSubsets_separableSpace {α : Type u} [PseudoEMetricSpace α]
    [TopologicalSpace.SeparableSpace α] :
    TopologicalSpace.SeparableSpace (FiniteSubsets α) := by
  rcases TopologicalSpace.exists_countable_dense α with ⟨U, hUc, hUd⟩
  exact ⟨⟨finiteSubsetsOf U, finiteSubsetsOf_countable hUc, finiteSubsetsOf_dense hUd⟩⟩

/-! ## Cauchy Prefixes -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: construction in `prop:finite-set-cauchy`.

Informal statement: the `n`th finite prefix of a sequence is the finite set
of all values `x i` with `i ≤ n`.

Lean strategy / thesis relation note: the thesis indexes by positive natural numbers and uses
`i = 1, ..., n`; Lean uses zero-based `ℕ`, so this prefix uses `i ≤ n`.
-/
noncomputable def finitePrefix {α : Type u} (x : ℕ → α) (n : ℕ) : FiniteSubsets α :=
  ⟨x '' {i | i ≤ n}, (Set.finite_Iic n).image x⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary membership fact for `prop:finite-set-cauchy`.

Informal statement: membership in the `n`th prefix means being equal to some
sequence value with index at most `n`.
-/
theorem mem_finitePrefix {α : Type u} (x : ℕ → α) (n : ℕ) {y : α} :
    y ∈ (finitePrefix x n : Set α) ↔ ∃ i, i ≤ n ∧ x i = y := by
  simp [finitePrefix]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary membership fact for `prop:finite-set-cauchy`.

Informal statement: the current sequence value belongs to its finite prefix.
-/
theorem finitePrefix_mem_self {α : Type u} (x : ℕ → α) (n : ℕ) :
    x n ∈ (finitePrefix x n : Set α) := by
  rw [mem_finitePrefix]
  exact ⟨n, le_rfl, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary membership fact for `prop:finite-set-cauchy`.

Informal statement: earlier sequence values belong to later finite prefixes.
-/
theorem finitePrefix_mem_of_le {α : Type u} (x : ℕ → α) {i n : ℕ} (hi : i ≤ n) :
    x i ∈ (finitePrefix x n : Set α) := by
  rw [mem_finitePrefix]
  exact ⟨i, hi, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `prop:finite-set-cauchy`.

Informal statement: if `x n` is a Cauchy sequence in `X`, then the increasing
finite-prefix sequence is Cauchy in the finite-subset Hausdorff space.

Lean strategy / thesis relation note: the proof follows the thesis estimate: when comparing two
large prefixes, any new point in the larger prefix is close to the terminal
point of the smaller prefix by Cauchyness of the original sequence.
-/
theorem finitePrefix_cauchySeq {α : Type u} [PseudoEMetricSpace α]
    {x : ℕ → α} (hx : CauchySeq x) : CauchySeq (finitePrefix x) := by
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  rcases exists_pos_lt_ennreal hε with ⟨δ, hδpos, hδε⟩
  rw [EMetric.cauchySeq_iff] at hx
  rcases hx δ hδpos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  change hausdorffEDistance (finitePrefix x m) (finitePrefix x n) < ε
  have hle : hausdorffEDistance (finitePrefix x m) (finitePrefix x n) ≤ δ := by
    apply Metric.hausdorffEDist_le_of_mem_edist
    · intro y hy
      rcases (mem_finitePrefix x m).mp hy with ⟨i, him, rfl⟩
      by_cases hin : i ≤ n
      · exact ⟨x i, finitePrefix_mem_of_le x hin, by simp⟩
      · have hni : n < i := Nat.lt_of_not_ge hin
        have hNi : N ≤ i := le_trans hn hni.le
        exact ⟨x n, finitePrefix_mem_self x n, le_of_lt (hN i hNi n hn)⟩
    · intro y hy
      rcases (mem_finitePrefix x n).mp hy with ⟨i, hin, rfl⟩
      by_cases him : i ≤ m
      · exact ⟨x i, finitePrefix_mem_of_le x him, by simp⟩
      · have hmi : m < i := Nat.lt_of_not_ge him
        have hNi : N ≤ i := le_trans hm hmi.le
        exact ⟨x m, finitePrefix_mem_self x m, le_of_lt (hN i hNi m hm)⟩
  exact lt_of_le_of_lt hle hδε

/-! ## Isolative Spaces -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `defn:isolative`.

Informal statement: an extended metric space is isolative if distinct points
are separated by a common positive lower bound.

Lean strategy / thesis relation note: the thesis writes `B > 0`. Since the thesis distance may be
`∞`, Lean states this with `B : ℝ≥0∞` and `0 < B`.
-/
def Isolative (α : Type u) [EDist α] : Prop :=
  ∃ B : ENNReal, 0 < B ∧ ∀ x y : α, x ≠ y → B ≤ edist x y

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: sequence part of `prop:isolative-finite-sets-complete`.

Informal statement: in an isolative space, every Cauchy sequence is eventually
constant.
-/
theorem eventually_constant_of_isolative {α : Type u} [PseudoEMetricSpace α]
    (hIso : Isolative α) {x : ℕ → α} (hx : CauchySeq x) :
    ∃ N : ℕ, ∀ n ≥ N, x n = x N := by
  rcases hIso with ⟨B, hBpos, hB⟩
  rw [EMetric.cauchySeq_iff] at hx
  rcases hx B hBpos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  by_contra hne
  have hle : B ≤ edist (x n) (x N) := hB (x n) (x N) hne
  have hlt : edist (x n) (x N) < B := hN n hn N le_rfl
  exact (not_lt_of_ge hle) hlt

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: completeness part of `prop:isolative-finite-sets-complete`.

Informal statement: every isolative extended pseudometric space is complete.

Lean strategy / thesis relation note: Lean's `CompleteSpace` is filter-level completeness. The proof
uses the same isolation-bound idea as the thesis: a Cauchy filter contains a
set of diameter `< B`, hence a singleton.
-/
theorem completeSpace_of_isolative {α : Type u} [PseudoEMetricSpace α]
    (hIso : Isolative α) : CompleteSpace α := by
  rw [completeSpace_iff_isComplete_univ]
  intro f hf _
  rcases hIso with ⟨B, hBpos, hB⟩
  rw [EMetric.cauchy_iff] at hf
  rcases hf with ⟨hne, hsmall⟩
  rcases hsmall B hBpos with ⟨t, ht, htSmall⟩
  have hneBot : f.NeBot := Filter.neBot_iff.mpr hne
  rcases hneBot.nonempty_of_mem ht with ⟨x, hx⟩
  refine ⟨x, by simp, ?_⟩
  have htSubset : t ⊆ {x} := by
    intro y hy
    by_contra hyx
    have hle : B ≤ edist y x := hB y x hyx
    have hlt : edist y x < B := htSmall y hy x hx
    exact (not_lt_of_ge hle) hlt
  have hpure : {x} ∈ f := Filter.mem_of_superset ht htSubset
  have hlePure : f ≤ pure x := by
    rw [← Filter.principal_singleton, Filter.le_principal_iff]
    exact hpure
  exact hlePure.trans (pure_le_nhds x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary lower-bound step in
`prop:finite-hausdorff-isolative`.

Informal statement: if `x` belongs to one finite set but not the other, and
the ambient space has isolation bound `B`, then the Hausdorff distance between
the finite sets is at least `B`.
-/
theorem hausdorffEDistance_lower_bound_of_mem_notMem {α : Type u} [PseudoEMetricSpace α]
    {B : ENNReal} (hB : ∀ x y : α, x ≠ y → B ≤ edist x y)
    {s t : FiniteSubsets α} {x : α} (hx : x ∈ (s : Set α)) (hxt : x ∉ (t : Set α)) :
    B ≤ hausdorffEDistance s t := by
  have hInf : B ≤ Metric.infEDist x (t : Set α) := by
    rw [Metric.le_infEDist]
    intro y hy
    exact hB x y (by
      intro hxy
      exact hxt (hxy ▸ hy))
  exact hInf.trans (Metric.infEDist_le_hausdorffEDist_of_mem hx)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `prop:finite-hausdorff-isolative`.

Informal statement: if the ambient space is isolative, then the finite-subset
Hausdorff space is isolative with the same bound.
-/
theorem finiteSubsets_isolative {α : Type u} [PseudoEMetricSpace α]
    (hIso : Isolative α) : Isolative (FiniteSubsets α) := by
  rcases hIso with ⟨B, hBpos, hB⟩
  refine ⟨B, hBpos, ?_⟩
  intro s t hne
  change B ≤ hausdorffEDistance s t
  have hset_ne : (s : Set α) ≠ (t : Set α) := by
    intro hset
    exact hne (Subtype.ext hset)
  by_cases hst : (s : Set α) ⊆ (t : Set α)
  · have hnot : ¬ (t : Set α) ⊆ (s : Set α) := by
      intro hts
      exact hset_ne (Set.Subset.antisymm hst hts)
    rcases Set.not_subset.mp hnot with ⟨x, hxt, hxs⟩
    rw [hausdorffEDistance_comm]
    exact hausdorffEDistance_lower_bound_of_mem_notMem hB hxt hxs
  · rcases Set.not_subset.mp hst with ⟨x, hxs, hxt⟩
    exact hausdorffEDistance_lower_bound_of_mem_notMem hB hxs hxt

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: consequence after `prop:finite-hausdorff-isolative`.

Informal statement: if the ambient space is isolative, then the finite-subset
Hausdorff space is complete.
-/
theorem finiteSubsets_completeSpace_of_isolative {α : Type u} [PseudoEMetricSpace α]
    (hIso : Isolative α) : CompleteSpace (FiniteSubsets α) :=
  completeSpace_of_isolative (finiteSubsets_isolative hIso)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: singleton observation in
`prop:finite-hausdorff-isolative-iff-isolative`.

Informal statement: the Hausdorff distance between singleton finite subsets is
the original ambient distance.
-/
theorem singleton_edist {α : Type u} [PseudoEMetricSpace α] (x y : α) :
    edist (singleton x : FiniteSubsets α) (singleton y) = edist x y := by
  change hausdorffEDistance (singleton x) (singleton y) = edist x y
  exact Metric.hausdorffEDist_singleton

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: reverse implication of
`prop:finite-hausdorff-isolative-iff-isolative`.

Informal statement: if the finite-subset Hausdorff space is isolative, then
the ambient space is isolative.
-/
theorem isolative_of_finiteSubsets_isolative {α : Type u} [PseudoEMetricSpace α]
    (hIso : Isolative (FiniteSubsets α)) : Isolative α := by
  rcases hIso with ⟨B, hBpos, hB⟩
  refine ⟨B, hBpos, ?_⟩
  intro x y hne
  have hsne : (singleton x : FiniteSubsets α) ≠ singleton y := by
    intro h
    exact hne (singleton_injective h)
  have hle := hB (singleton x) (singleton y) hsne
  rwa [singleton_edist] at hle

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `prop:finite-hausdorff-isolative-iff-isolative`.

Informal statement: the finite-subset Hausdorff space is isolative if and
only if the ambient space is isolative.
-/
theorem finiteSubsets_isolative_iff_isolative {α : Type u} [PseudoEMetricSpace α] :
    Isolative (FiniteSubsets α) ↔ Isolative α :=
  ⟨isolative_of_finiteSubsets_isolative, finiteSubsets_isolative⟩

/-! ## Distinct Finite Sets -/

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: metric carrier in `thm:distinct-properties` /
`prop:index-augmented-hausdorff`.

Informal statement: the index-augmented copy of `ℕ × X`, equipped with the
`L¹` product extended distance.

Lean strategy / thesis relation note: the thesis uses the product set `ℕ × X` with the custom metric
`d*((n,x),(m,y)) = d(x,y) + |n-m|`. Mathlib's ordinary product metric is the
maximum metric, so Lean wraps the same underlying product in `WithLp 1` to
carry the thesis metric without creating an instance diamond.
-/
abbrev IndexAugmented (α : Type u) : Type u :=
  WithLp 1 (ℕ × α)

namespace IndexAugmented

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: point constructor for the index-augmented space.

Informal statement: build the indexed point `(n,x)`.
-/
def mk {α : Type u} (n : ℕ) (x : α) : IndexAugmented α :=
  WithLp.toLp 1 (n, x)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: index projection used in `defn:distinct-finite-sets`.
-/
def index {α : Type u} (p : IndexAugmented α) : ℕ :=
  (WithLp.ofLp p).1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: value projection used in `defn:distinct-finite-sets`.
-/
def value {α : Type u} (p : IndexAugmented α) : α :=
  (WithLp.ofLp p).2

@[simp]
theorem index_mk {α : Type u} (n : ℕ) (x : α) :
    index (mk n x) = n :=
  rfl

@[simp]
theorem value_mk {α : Type u} (n : ℕ) (x : α) :
    value (mk n x) = x :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: extensionality for the index-augmented product.

Informal statement: indexed points are equal when both their index and value
coordinates agree.
-/
theorem ext {α : Type u} {p q : IndexAugmented α}
    (hi : index p = index q) (hv : value p = value q) : p = q := by
  apply (WithLp.equiv 1 (ℕ × α)).injective
  exact Prod.ext hi hv

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: product-coordinate identity for the index-augmented product.

Informal statement: every indexed point is reconstructed from its index and
value.
-/
theorem mk_index_value {α : Type u} (p : IndexAugmented α) :
    mk (index p) (value p) = p := by
  apply ext <;> rfl

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `d*` in `thm:distinct-properties` /
`prop:index-augmented-hausdorff`.

Informal statement: the distance between indexed points is the distance
between their values plus the distance between their indices.
-/
theorem edist_mk_mk {α : Type u} [PseudoEMetricSpace α]
    (n m : ℕ) (x y : α) :
    edist (mk n x) (mk m y) = edist n m + edist x y := by
  simp [mk, WithLp.prod_edist_eq_add]

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary natural-number step in `lem:helpful-distinct`.

Informal statement: for natural-number indices, distance `< 1` forces the
indices to be equal.
-/
theorem nat_eq_of_edist_lt_one {n m : ℕ} (h : edist n m < (1 : ENNReal)) :
    n = m := by
  rw [edist_dist] at h
  rw [← ENNReal.ofReal_one] at h
  rw [ENNReal.ofReal_lt_ofReal_iff zero_lt_one] at h
  by_contra hne
  have hge : (1 : ℝ) ≤ dist n m := by
    rw [Nat.dist_eq]
    by_cases hnm : n < m
    · have hle : n + 1 ≤ m := Nat.succ_le_of_lt hnm
      have hleR : (n : ℝ) + 1 ≤ m := by exact_mod_cast hle
      have hnonpos : (n : ℝ) - m ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      linarith
    · have hle_nm : m ≤ n := Nat.le_of_not_gt hnm
      have hmn : m < n := Nat.lt_of_le_of_ne hle_nm (Ne.symm hne)
      have hle : m + 1 ≤ n := Nat.succ_le_of_lt hmn
      have hleR : (m : ℝ) + 1 ≤ n := by exact_mod_cast hle
      have hnonneg : 0 ≤ (n : ℝ) - m := by linarith
      have habs : |(n : ℝ) - m| = (n : ℝ) - m := abs_of_nonneg hnonneg
      rw [habs]
      linarith
  linarith

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: index-augmented separability step in
`thm:distinct-properties` / `prop:index-augmented-hausdorff`.

Informal statement: if `X` is separable, then the index-augmented product
`ℕ × X` with the thesis `L¹` extended distance is separable.
-/
theorem separableSpace {α : Type u} [EMetricSpace α]
    [TopologicalSpace.SeparableSpace α] :
    TopologicalSpace.SeparableSpace (IndexAugmented α) := by
  infer_instance

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: index-augmented completeness step in
`thm:distinct-properties` / `prop:index-augmented-hausdorff`.

Informal statement: if `X` is complete, then the index-augmented product
`ℕ × X` with the thesis `L¹` extended distance is complete.
-/
theorem completeSpace {α : Type u} [EMetricSpace α] [CompleteSpace α] :
    CompleteSpace (IndexAugmented α) := by
  infer_instance

end IndexAugmented

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: predicate in `defn:distinct-finite-sets`.

Informal statement: a finite subset of `ℕ × X` has distinct indices if each
index `n` occurs at most once.

Lean strategy / thesis relation note: the thesis writes
`|({n} × X) ∩ ξ| ≤ 1`; Lean states the same fact as uniqueness of the second
coordinate whenever two pairs with the same first coordinate are present.
-/
def HasDistinctIndices {α : Type u} (s : FiniteSubsets (IndexAugmented α)) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃x y : α⦄, IndexAugmented.mk n x ∈ (s : Set (IndexAugmented α)) →
    IndexAugmented.mk n y ∈ (s : Set (IndexAugmented α)) → x = y

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `defn:distinct-finite-sets`.

Informal statement: distinct finite sets over `X` are finite subsets of
`ℕ × X` with at most one element at each natural-number index.
-/
abbrev DistinctFiniteSubsets (α : Type u) : Type u :=
  {s : FiniteSubsets (IndexAugmented α) // HasDistinctIndices s}

namespace DistinctFiniteSubsets

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: immediate property of `defn:distinct-finite-sets`.

Informal statement: two members of a distinct finite set with the same index
have the same value.
-/
theorem value_eq_of_same_index {α : Type u} (s : DistinctFiniteSubsets α)
    {n : ℕ} {x y : α} (hx : IndexAugmented.mk n x ∈ (s.1 : Set (IndexAugmented α)))
    (hy : IndexAugmented.mk n y ∈ (s.1 : Set (IndexAugmented α))) : x = y :=
  s.2 hx hy

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary projection used in the proof of
`thm:distinct-properties`.

Informal statement: the finite set of indices appearing in a distinct finite
set.
-/
noncomputable def indexSet {α : Type u} (s : DistinctFiniteSubsets α) : FiniteSubsets ℕ :=
  ⟨IndexAugmented.index '' (s.1 : Set (IndexAugmented α)),
    s.1.2.image IndexAugmented.index⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary projection fact for `thm:distinct-properties`.

Informal statement: an index belongs to the projected index set exactly when
some value appears at that index.
-/
theorem mem_indexSet {α : Type u} (s : DistinctFiniteSubsets α) {n : ℕ} :
    n ∈ (indexSet s : Set ℕ) ↔
      ∃ x : α, IndexAugmented.mk n x ∈ (s.1 : Set (IndexAugmented α)) := by
  constructor
  · intro hn
    rcases hn with ⟨p, hp, rfl⟩
    exact ⟨IndexAugmented.value p, by
      simpa [IndexAugmented.mk_index_value p] using hp⟩
  · rintro ⟨x, hx⟩
    exact ⟨IndexAugmented.mk n x, hx, rfl⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary uniqueness fact for `lem:helpful-distinct`.

Informal statement: for a fixed index in a distinct finite set, the value
witnessing membership of that index is unique.
-/
theorem exists_unique_value_of_mem_indexSet {α : Type u}
    (s : DistinctFiniteSubsets α) {n : ℕ} (hn : n ∈ (indexSet s : Set ℕ)) :
    ∃! x : α, IndexAugmented.mk n x ∈ (s.1 : Set (IndexAugmented α)) := by
  rcases (mem_indexSet s).mp hn with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact value_eq_of_same_index s hy hx

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: coordinate selection used in the proof of
`property:distinct-finite-complete`.

Informal statement: for an index appearing in a distinct finite set, select
the unique value at that index.
-/
noncomputable def valueAt {α : Type u} (s : DistinctFiniteSubsets α) (n : ℕ)
    (hn : n ∈ (indexSet s : Set ℕ)) : α :=
  Classical.choose (exists_unique_value_of_mem_indexSet s hn)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: coordinate selection fact used in
`property:distinct-finite-complete`.

Informal statement: the selected value really occurs at the chosen index.
-/
theorem valueAt_mem {α : Type u} (s : DistinctFiniteSubsets α) {n : ℕ}
    (hn : n ∈ (indexSet s : Set ℕ)) :
    IndexAugmented.mk n (valueAt s n hn) ∈ (s.1 : Set (IndexAugmented α)) :=
  (Classical.choose_spec (exists_unique_value_of_mem_indexSet s hn)).1

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: coordinate uniqueness fact used in
`property:distinct-finite-complete`.

Informal statement: any value occurring at the chosen index is the selected
value.
-/
theorem valueAt_eq_of_mem {α : Type u} (s : DistinctFiniteSubsets α) {n : ℕ} {x : α}
    (hn : n ∈ (indexSet s : Set ℕ))
    (hx : IndexAugmented.mk n x ∈ (s.1 : Set (IndexAugmented α))) :
    valueAt s n hn = x :=
  ((Classical.choose_spec (exists_unique_value_of_mem_indexSet s hn)).2 x hx).symm

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: auxiliary injectivity fact behind `lem:helpful-distinct`.

Informal statement: the index projection is injective on each distinct finite
set.
-/
theorem index_injOn {α : Type u} (s : DistinctFiniteSubsets α) :
    Set.InjOn IndexAugmented.index (s.1 : Set (IndexAugmented α)) := by
  intro p hp q hq hi
  apply IndexAugmented.ext hi
  have hp' : IndexAugmented.mk (IndexAugmented.index p) (IndexAugmented.value p) ∈
      (s.1 : Set (IndexAugmented α)) := by
    simpa [IndexAugmented.mk_index_value p] using hp
  have hq' : IndexAugmented.mk (IndexAugmented.index p) (IndexAugmented.value q) ∈
      (s.1 : Set (IndexAugmented α)) := by
    rw [hi]
    simpa [IndexAugmented.mk_index_value q] using hq
  exact value_eq_of_same_index s hp' hq'

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: cardinality bridge for `lem:helpful-distinct`.

Informal statement: the cardinality of a distinct finite set agrees with the
cardinality of its projected finite index set.
-/
theorem ncard_indexSet_eq {α : Type u} (s : DistinctFiniteSubsets α) :
    (indexSet s : Set ℕ).ncard = (s.1 : Set (IndexAugmented α)).ncard := by
  change (IndexAugmented.index '' (s.1 : Set (IndexAugmented α))).ncard =
    (s.1 : Set (IndexAugmented α)).ncard
  exact (index_injOn s).ncard_image

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: dense support used for
`property:distinct-finite-separable`.

Informal statement: distinct finite sets whose values all lie in a fixed
subset `U` of the original space.
-/
def valueSupportedOn {α : Type u} (U : Set α) : Set (DistinctFiniteSubsets α) :=
  {s | ∀ p ∈ (s.1 : Set (IndexAugmented α)), IndexAugmented.value p ∈ U}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: countability support used for
`property:distinct-finite-separable`.

Informal statement: the indexed points whose value coordinate lies in `U`.
-/
def valuePreimage {α : Type u} (U : Set α) : Set (IndexAugmented α) :=
  {p | IndexAugmented.value p ∈ U}

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: countability step for
`property:distinct-finite-separable`.

Informal statement: if `U` is countable, then its index-augmented preimage
inside `ℕ × X` is countable.
-/
theorem valuePreimage_countable {α : Type u} {U : Set α} (hU : U.Countable) :
    (valuePreimage U).Countable := by
  haveI : Countable U := hU.to_subtype
  let f : ℕ × U → IndexAugmented α := fun p => IndexAugmented.mk p.1 p.2.1
  have hsub : valuePreimage U ⊆ Set.range f := by
    intro p hp
    refine ⟨(IndexAugmented.index p, ⟨IndexAugmented.value p, hp⟩), ?_⟩
    simp [f, IndexAugmented.mk_index_value p]
  exact (Set.countable_range f).mono hsub

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: countability step for
`property:distinct-finite-separable`.

Informal statement: if `U` is countable, then the distinct finite sets
supported on `U` are countable.
-/
theorem valueSupportedOn_countable {α : Type u} {U : Set α} (hU : U.Countable) :
    (valueSupportedOn U).Countable := by
  have hpre : (valuePreimage U).Countable := valuePreimage_countable hU
  have hfin : (finiteSubsetsOf (valuePreimage U)).Countable := finiteSubsetsOf_countable hpre
  haveI : Countable {s : FiniteSubsets (IndexAugmented α) //
      s ∈ finiteSubsetsOf (valuePreimage U)} :=
    hfin.to_subtype
  let f : {s : DistinctFiniteSubsets α // s ∈ valueSupportedOn U} →
      {s : FiniteSubsets (IndexAugmented α) // s ∈ finiteSubsetsOf (valuePreimage U)} :=
    fun s => ⟨s.1.1, s.2⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : {s : FiniteSubsets (IndexAugmented α) //
          s ∈ finiteSubsetsOf (valuePreimage U)} =>
        (z : FiniteSubsets (IndexAugmented α))) h
  exact Function.Injective.countable hf

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: density step for `property:distinct-finite-separable`.

Informal statement: if `U` is dense in `X`, then distinct finite sets
supported on `U` are dense in the distinct finite-set Hausdorff space.

Lean strategy / thesis relation note: the thesis says this follows because
`\mathscr{D}(X) ⊆ \mathscr{F}(\mathbb{N} × X)`. In Lean, arbitrary subspaces
of separable spaces are not automatically separable without additional
hypotheses, so we prove the same pointwise dense-support construction
directly for distinct finite sets.
-/
theorem valueSupportedOn_dense {α : Type u} [EMetricSpace α]
    {U : Set α} (hU : Dense U) : Dense (valueSupportedOn U) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.mpr
  intro s
  rw [EMetric.mem_closure_iff]
  intro ε hε
  rcases exists_pos_lt_ennreal hε with ⟨δ, hδpos, hδε⟩
  have hApprox : ∀ z : (s.1 : Set (IndexAugmented α)),
      ∃ u ∈ U, edist (IndexAugmented.value z.1) u < δ := by
    intro z
    have hzcl : IndexAugmented.value z.1 ∈ closure U := by
      rw [dense_iff_closure_eq.mp hU]
      trivial
    exact (EMetric.mem_closure_iff.mp hzcl) δ hδpos
  choose u huU hu using hApprox
  haveI : Finite (s.1 : Set (IndexAugmented α)) := s.1.2.to_subtype
  let approx : (s.1 : Set (IndexAugmented α)) → IndexAugmented α :=
    fun z => IndexAugmented.mk (IndexAugmented.index z.1) (u z)
  let η0 : FiniteSubsets (IndexAugmented α) :=
    ⟨Set.range approx, Set.finite_range approx⟩
  have hηdistinct : HasDistinctIndices η0 := by
    intro n x y hx hy
    rcases hx with ⟨z, hz⟩
    rcases hy with ⟨w, hw⟩
    have hzidx : IndexAugmented.index z.1 = n := by
      simpa [approx] using congrArg IndexAugmented.index hz
    have hwidx : IndexAugmented.index w.1 = n := by
      simpa [approx] using congrArg IndexAugmented.index hw
    have hzval : u z = x := by
      simpa [approx] using congrArg IndexAugmented.value hz
    have hwval : u w = y := by
      simpa [approx] using congrArg IndexAugmented.value hw
    have hzm : IndexAugmented.mk n (IndexAugmented.value z.1) ∈
        (s.1 : Set (IndexAugmented α)) := by
      simp [← hzidx, IndexAugmented.mk_index_value z.1]
    have hwm : IndexAugmented.mk n (IndexAugmented.value w.1) ∈
        (s.1 : Set (IndexAugmented α)) := by
      simp [← hwidx, IndexAugmented.mk_index_value w.1]
    have hvaleq : IndexAugmented.value z.1 = IndexAugmented.value w.1 :=
      value_eq_of_same_index s hzm hwm
    have hzw : z = w := by
      apply Subtype.ext
      apply IndexAugmented.ext
      · exact hzidx.trans hwidx.symm
      · exact hvaleq
    calc
      x = u z := hzval.symm
      _ = u w := by rw [hzw]
      _ = y := hwval
  let η : DistinctFiniteSubsets α := ⟨η0, hηdistinct⟩
  refine ⟨η, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨z, rfl⟩
    exact huU z
  · change edist s η < ε
    change hausdorffEDistance s.1 η.1 < ε
    have hle : hausdorffEDistance s.1 η.1 ≤ δ := by
      apply Metric.hausdorffEDist_le_of_mem_edist
      · intro p hp
        let z : (s.1 : Set (IndexAugmented α)) := ⟨p, hp⟩
        refine ⟨approx z, by exact ⟨z, rfl⟩, ?_⟩
        change edist p (IndexAugmented.mk (IndexAugmented.index p) (u z)) ≤ δ
        rw [← IndexAugmented.mk_index_value p, IndexAugmented.edist_mk_mk]
        norm_num
        exact le_of_lt (hu z)
      · intro p hp
        rcases hp with ⟨z, rfl⟩
        refine ⟨z.1, z.2, ?_⟩
        change edist (IndexAugmented.mk (IndexAugmented.index z.1) (u z)) z.1 ≤ δ
        rw [← IndexAugmented.mk_index_value z.1, IndexAugmented.edist_mk_mk]
        norm_num
        exact le_of_lt (by simpa [edist_comm] using hu z)
    exact lt_of_le_of_lt hle hδε

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `property:distinct-finite-separable` in
`thm:distinct-properties` / `prop:index-augmented-hausdorff`.

Informal statement: if `X` is separable, then the distinct finite-set
Hausdorff space over `X` is separable.
-/
theorem separableSpace {α : Type u} [EMetricSpace α]
    [TopologicalSpace.SeparableSpace α] :
    TopologicalSpace.SeparableSpace (DistinctFiniteSubsets α) := by
  rcases TopologicalSpace.exists_countable_dense α with ⟨U, hUc, hUd⟩
  exact ⟨⟨valueSupportedOn U, valueSupportedOn_countable hUc, valueSupportedOn_dense hUd⟩⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: quantitative form of the second assertion of
`lem:helpful-distinct`.

Informal statement: if two distinct finite sets have Hausdorff distance below
`r ≤ 1`, then every indexed element of the first has an element in the second
with the same natural-number index and value-distance below `r`.
-/
theorem exists_same_index_near_of_edist_lt {α : Type u} [EMetricSpace α]
    {ξ η : DistinctFiniteSubsets α} {r : ENNReal} (hr : r ≤ (1 : ENNReal))
    (h : edist ξ η < r)
    {n : ℕ} {x : α} (hx : IndexAugmented.mk n x ∈ (ξ.1 : Set (IndexAugmented α))) :
    ∃ y : α, edist x y < r ∧
      IndexAugmented.mk n y ∈ (η.1 : Set (IndexAugmented α)) := by
  change hausdorffEDistance ξ.1 η.1 < r at h
  rcases Metric.exists_edist_lt_of_hausdorffEDist_lt hx h with ⟨q, hq, hpq⟩
  have hpq' : edist (IndexAugmented.mk n x)
      (IndexAugmented.mk (IndexAugmented.index q) (IndexAugmented.value q)) < r := by
    simp [IndexAugmented.mk_index_value q, hpq]
  rw [IndexAugmented.edist_mk_mk] at hpq'
  have hidx_lt_r : edist n (IndexAugmented.index q) < r :=
    lt_of_le_of_lt le_self_add hpq'
  have hidx_lt : edist n (IndexAugmented.index q) < (1 : ENNReal) :=
    lt_of_lt_of_le hidx_lt_r hr
  have hidx : n = IndexAugmented.index q := IndexAugmented.nat_eq_of_edist_lt_one hidx_lt
  refine ⟨IndexAugmented.value q, ?_, ?_⟩
  · have hvalue_le : edist x (IndexAugmented.value q) ≤
        edist n (IndexAugmented.index q) + edist x (IndexAugmented.value q) := by
      exact le_add_left le_rfl
    exact lt_of_le_of_lt hvalue_le hpq'
  · have hqeq : IndexAugmented.mk n (IndexAugmented.value q) = q := by
      rw [hidx]
      exact IndexAugmented.mk_index_value q
    simpa [hqeq] using hq

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: second assertion of `lem:helpful-distinct`.

Informal statement: if two distinct finite sets have Hausdorff distance below
`1`, then every indexed element of the first has a nearby element in the
second with the same natural-number index.
-/
theorem exists_same_index_near_of_edist_lt_one {α : Type u} [EMetricSpace α]
    {ξ η : DistinctFiniteSubsets α} (h : edist ξ η < (1 : ENNReal))
    {n : ℕ} {x : α} (hx : IndexAugmented.mk n x ∈ (ξ.1 : Set (IndexAugmented α))) :
    ∃ y : α, edist x y < (1 : ENNReal) ∧
      IndexAugmented.mk n y ∈ (η.1 : Set (IndexAugmented α)) :=
  exists_same_index_near_of_edist_lt le_rfl h hx

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: index-set form of `lem:helpful-distinct`.

Informal statement: if the Hausdorff distance is below `1`, then two distinct
finite sets have the same projected index set.
-/
theorem indexSet_eq_of_edist_lt_one {α : Type u} [EMetricSpace α]
    {ξ η : DistinctFiniteSubsets α} (h : edist ξ η < (1 : ENNReal)) :
    indexSet ξ = indexSet η := by
  apply Subtype.ext
  ext n
  constructor
  · intro hn
    rcases (mem_indexSet ξ).mp hn with ⟨x, hx⟩
    rcases exists_same_index_near_of_edist_lt_one h hx with ⟨y, _hy_close, hy⟩
    exact (mem_indexSet η).mpr ⟨y, hy⟩
  · intro hn
    rcases (mem_indexSet η).mp hn with ⟨y, hy⟩
    have hsym : edist η ξ < (1 : ENNReal) := by
      simpa [edist_comm] using h
    rcases exists_same_index_near_of_edist_lt_one hsym hy with ⟨x, _hx_close, hx⟩
    exact (mem_indexSet ξ).mpr ⟨x, hx⟩

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: first assertion of `lem:helpful-distinct`.

Informal statement: if two distinct finite sets have Hausdorff distance below
`1`, then they have the same cardinality.

Lean strategy / thesis relation note: Lean states cardinality using `Set.ncard` on the underlying
finite sets.
-/
theorem ncard_eq_of_edist_lt_one {α : Type u} [EMetricSpace α]
    {ξ η : DistinctFiniteSubsets α} (h : edist ξ η < (1 : ENNReal)) :
    (ξ.1 : Set (IndexAugmented α)).ncard = (η.1 : Set (IndexAugmented α)).ncard := by
  have hidx : indexSet ξ = indexSet η := indexSet_eq_of_edist_lt_one h
  calc
    (ξ.1 : Set (IndexAugmented α)).ncard = (indexSet ξ : Set ℕ).ncard :=
      (ncard_indexSet_eq ξ).symm
    _ = (indexSet η : Set ℕ).ncard := by rw [hidx]
    _ = (η.1 : Set (IndexAugmented α)).ncard :=
      ncard_indexSet_eq η

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: first step in the proof of
`property:distinct-finite-complete`.

Informal statement: a Cauchy sequence of distinct finite sets eventually has
a constant projected finite index set.
-/
theorem cauchySeq_eventually_constant_indexSet {α : Type u} [EMetricSpace α]
    {u : ℕ → DistinctFiniteSubsets α} (hu : CauchySeq u) :
    ∃ I : FiniteSubsets ℕ, ∀ᶠ n in Filter.atTop, indexSet (u n) = I := by
  rcases (EMetric.cauchySeq_iff.1 hu) (1 : ENNReal) zero_lt_one with ⟨N, hN⟩
  refine ⟨indexSet (u N), Filter.eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn
  exact indexSet_eq_of_edist_lt_one (hN n hn N le_rfl)

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: constructive proof of
`property:distinct-finite-complete`.

Informal statement: every Cauchy sequence of distinct finite sets over a
complete space converges.

Lean strategy / thesis relation note: this follows the thesis proof. Once the Hausdorff distance is
eventually `< 1`, `lem:helpful-distinct` stabilizes the finite index set.
Then each fixed-index coordinate is a Cauchy sequence in `X`, hence converges;
the limit distinct finite set is the graph of those coordinate limits over
the stabilized finite index set.
-/
theorem cauchySeq_tendsto_of_complete {α : Type u} [EMetricSpace α] [CompleteSpace α]
    {u : ℕ → DistinctFiniteSubsets α} (hu : CauchySeq u) :
    ∃ ξ : DistinctFiniteSubsets α, Filter.Tendsto u Filter.atTop (nhds ξ) := by
  rcases (EMetric.cauchySeq_iff.1 hu) (1 : ENNReal) zero_lt_one with ⟨N, hNsmall⟩
  let I : FiniteSubsets ℕ := indexSet (u N)
  have hIndex : ∀ n, N ≤ n → indexSet (u n) = I := by
    intro n hn
    exact indexSet_eq_of_edist_lt_one (hNsmall n hn N le_rfl)
  haveI : Finite {i : ℕ // i ∈ (I : Set ℕ)} := I.2.to_subtype
  let coord : {i : ℕ // i ∈ (I : Set ℕ)} → ℕ → α := fun i n =>
    if hn : N ≤ n then
      valueAt (u n) i.1 (by rw [hIndex n hn]; exact i.2)
    else
      valueAt (u N) i.1 (by exact i.2)
  have coord_mem : ∀ (i : {i : ℕ // i ∈ (I : Set ℕ)}) (n : ℕ), N ≤ n →
      IndexAugmented.mk i.1 (coord i n) ∈ ((u n).1 : Set (IndexAugmented α)) := by
    intro i n hn
    change IndexAugmented.mk i.1
        (if hn' : N ≤ n then valueAt (u n) i.1 (by rw [hIndex n hn']; exact i.2)
          else valueAt (u N) i.1 (by exact i.2)) ∈ ((u n).1 : Set (IndexAugmented α))
    rw [dif_pos hn]
    exact valueAt_mem (u n) (by rw [hIndex n hn]; exact i.2)
  have coord_eq_of_mem : ∀ (i : {i : ℕ // i ∈ (I : Set ℕ)}) (n : ℕ)
      (hn : N ≤ n) {x : α},
      IndexAugmented.mk i.1 x ∈ ((u n).1 : Set (IndexAugmented α)) → coord i n = x := by
    intro i n hn x hx
    change (if hn' : N ≤ n then valueAt (u n) i.1 (by rw [hIndex n hn']; exact i.2)
          else valueAt (u N) i.1 (by exact i.2)) = x
    rw [dif_pos hn]
    exact valueAt_eq_of_mem (u n) (by rw [hIndex n hn]; exact i.2) hx
  have hcoord_cauchy : ∀ i : {i : ℕ // i ∈ (I : Set ℕ)}, CauchySeq (coord i) := by
    intro i
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    rcases exists_pos_le_one_lt_ennreal hε with ⟨δ, hδpos, hδle1, hδε⟩
    rcases (EMetric.cauchySeq_iff.1 hu) δ hδpos with ⟨M, hM⟩
    refine ⟨max N M, ?_⟩
    intro m hm n hn
    have hmN : N ≤ m := le_trans (le_max_left N M) hm
    have hnN : N ≤ n := le_trans (le_max_left N M) hn
    have hmM : M ≤ m := le_trans (le_max_right N M) hm
    have hnM : M ≤ n := le_trans (le_max_right N M) hn
    have hdist : edist (u m) (u n) < δ := hM m hmM n hnM
    have hmem_m : IndexAugmented.mk i.1 (coord i m) ∈
        ((u m).1 : Set (IndexAugmented α)) :=
      coord_mem i m hmN
    rcases exists_same_index_near_of_edist_lt hδle1 hdist hmem_m with
      ⟨y, hylt, hymem⟩
    have hcoord_n : coord i n = y := coord_eq_of_mem i n hnN hymem
    exact lt_trans (by simpa [hcoord_n] using hylt) hδε
  choose xlim hxlim using fun i : {i : ℕ // i ∈ (I : Set ℕ)} =>
    _root_.cauchySeq_tendsto_of_complete (hcoord_cauchy i)
  let limitPoint : {i : ℕ // i ∈ (I : Set ℕ)} → IndexAugmented α := fun i =>
    IndexAugmented.mk i.1 (xlim i)
  let ξ0 : FiniteSubsets (IndexAugmented α) :=
    ⟨Set.range limitPoint, Set.finite_range limitPoint⟩
  have hξdistinct : HasDistinctIndices ξ0 := by
    intro n x y hx hy
    rcases hx with ⟨i, hi⟩
    rcases hy with ⟨j, hj⟩
    have hiidx : i.1 = n := by
      simpa [limitPoint] using congrArg IndexAugmented.index hi
    have hjidx : j.1 = n := by
      simpa [limitPoint] using congrArg IndexAugmented.index hj
    have hix : xlim i = x := by
      simpa [limitPoint] using congrArg IndexAugmented.value hi
    have hjy : xlim j = y := by
      simpa [limitPoint] using congrArg IndexAugmented.value hj
    have hij : i = j := Subtype.ext (hiidx.trans hjidx.symm)
    calc
      x = xlim i := hix.symm
      _ = xlim j := by rw [hij]
      _ = y := hjy
  let ξ : DistinctFiniteSubsets α := ⟨ξ0, hξdistinct⟩
  refine ⟨ξ, ?_⟩
  rw [EMetric.tendsto_nhds]
  intro ε hε
  rcases exists_pos_lt_ennreal hε with ⟨δ, hδpos, hδε⟩
  have hcoord_event : ∀ i : {i : ℕ // i ∈ (I : Set ℕ)}, ∀ᶠ n in Filter.atTop,
      edist (coord i n) (xlim i) < δ := by
    intro i
    exact EMetric.tendsto_nhds.1 (hxlim i) δ hδpos
  have hall : ∀ᶠ n in Filter.atTop,
      ∀ i : {i : ℕ // i ∈ (I : Set ℕ)}, edist (coord i n) (xlim i) < δ := by
    rw [Filter.eventually_all]
    exact hcoord_event
  have hNevent : ∀ᶠ n in Filter.atTop, N ≤ n :=
    Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩
  filter_upwards [hall, hNevent] with n halln hnN
  change hausdorffEDistance (u n).1 ξ.1 < ε
  have hle : hausdorffEDistance (u n).1 ξ.1 ≤ δ := by
    apply Metric.hausdorffEDist_le_of_mem_edist
    · intro p hp
      have hpidx_un : IndexAugmented.index p ∈ (indexSet (u n) : Set ℕ) :=
        (mem_indexSet (u n)).mpr ⟨IndexAugmented.value p, by
          simpa [IndexAugmented.mk_index_value p] using hp⟩
      have hpidx_I : IndexAugmented.index p ∈ (I : Set ℕ) := by
        simpa [hIndex n hnN] using hpidx_un
      let i : {i : ℕ // i ∈ (I : Set ℕ)} := ⟨IndexAugmented.index p, hpidx_I⟩
      have hpval : coord i n = IndexAugmented.value p := by
        apply coord_eq_of_mem i n hnN
        simpa [IndexAugmented.mk_index_value p]
      refine ⟨limitPoint i, by exact ⟨i, rfl⟩, ?_⟩
      change edist p (IndexAugmented.mk i.1 (xlim i)) ≤ δ
      rw [← IndexAugmented.mk_index_value p, IndexAugmented.edist_mk_mk]
      exact le_of_lt (by simpa [i, hpval] using halln i)
    · intro p hp
      rcases hp with ⟨i, rfl⟩
      refine ⟨IndexAugmented.mk i.1 (coord i n), coord_mem i n hnN, ?_⟩
      change edist (IndexAugmented.mk i.1 (xlim i)) (IndexAugmented.mk i.1 (coord i n)) ≤ δ
      rw [IndexAugmented.edist_mk_mk]
      exact le_of_lt (by simpa [edist_comm] using halln i)
  exact lt_of_le_of_lt hle hδε

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `property:distinct-finite-complete` in
`thm:distinct-properties` / `prop:index-augmented-hausdorff`.

Informal statement: if `X` is complete, then the distinct finite-set
Hausdorff space over `X` is complete.
-/
theorem completeSpace {α : Type u} [EMetricSpace α] [CompleteSpace α] :
    CompleteSpace (DistinctFiniteSubsets α) := by
  refine EMetric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  exact cauchySeq_tendsto_of_complete hu

/--
Thesis source:
`1 - theoretical foundations/2_chapter_market_representations.tex`,
section "Finite Sets and the Hausdorff Distance".

Original label: `thm:distinct-properties` /
`prop:index-augmented-hausdorff`.

Informal statement: if `X` is separable and complete, then the
index-augmented distinct finite-set Hausdorff space is separable and complete.

Lean strategy / thesis relation note: the thesis presents the metric carrier, separability, and
completeness together. Lean splits the ingredients above, then bundles the two
space-level transfer properties here.
-/
theorem distinctProperties {α : Type u} [EMetricSpace α]
    [TopologicalSpace.SeparableSpace α] [CompleteSpace α] :
    TopologicalSpace.SeparableSpace (DistinctFiniteSubsets α) ∧
      CompleteSpace (DistinctFiniteSubsets α) :=
  ⟨separableSpace, completeSpace⟩

end DistinctFiniteSubsets
end FiniteSubsets
end FiniteSets
end MarketRepresentation
end Foundations
end Thesis
