import Thesis.Appendices.Analysis.AnalysisBasic
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.GDelta.Basic

/-! # Current doctoral appendix: quotients and finite maximum products

These replace the former local-compactness and p-product detour. The general
Alexandrov characterization is tracked separately until proved internally.
-/

noncomputable section

open Set Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.DoctoralAnalysis

universe u v

/-- Original label: `defn:g-delta`. -/
abbrev IsGDelta {X : Type u} [TopologicalSpace X] (s : Set X) : Prop := IsGδ s

/-- Original label: `defn:g-delta`.
Natural indexing starts at zero in Lean, a harmless reindexing of the
positive-natural sequence in the source. -/
theorem isGDelta_iff {X : Type u} [TopologicalSpace X] (s : Set X) :
    IsGDelta s ↔ ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ s = ⋂ n, U n := by
  rw [IsGDelta, isGδ_iff_eq_iInter_nat]

/-- Original label: `prop:pseudometric-quotient`.
In a pseudometric topology, topological inseparability is precisely zero
distance, so the standard separation quotient is the exact stated quotient. -/
abbrev ZeroDistanceQuotient (X : Type u) [PseudoEMetricSpace X] := SeparationQuotient X

/-- Original label: `prop:pseudometric-quotient`. -/
theorem zeroDistance_equivalence {X : Type u} [PseudoEMetricSpace X] :
    Equivalence (fun x y : X => edist x y = 0) := by
  refine ⟨edist_self, fun h => by rwa [edist_comm], ?_⟩
  intro x y z hxy hyz
  apply le_antisymm _ (zero_le _)
  exact (edist_triangle x y z).trans (by rw [hxy, hyz, zero_add])

/-- Original label: `prop:pseudometric-quotient`.
Well-definedness of the quotient distance, by the manuscript's four-term
triangle inequality: if `x ∼ y` and `x* ∼ y*`, then
`d(x,x*) ≤ d(x,y) + d(y,y*) + d(y*,x*) = d(y,y*)`, and exchanging the two
representative pairs gives the reverse inequality. -/
theorem zeroDistance_edist_congr {X : Type u} [PseudoEMetricSpace X] {x y x' y' : X}
    (hxy : edist x y = 0) (hxy' : edist x' y' = 0) : edist x x' = edist y y' := by
  apply le_antisymm
  · calc edist x x' ≤ edist x y + edist y y' + edist y' x' := edist_triangle4 x y y' x'
      _ = edist y y' := by rw [hxy, edist_comm y' x', hxy', zero_add, add_zero]
  · calc edist y y' ≤ edist y x + edist x x' + edist x' y' := edist_triangle4 y x x' y'
      _ = edist x x' := by rw [edist_comm y x, hxy, hxy', zero_add, add_zero]

/-- Original label: `prop:pseudometric-quotient`.
The quotient distance `d∼([x],[x*]) = d(x,x*)`, defined through representatives;
`zeroDistance_edist_congr` is the independence of the representatives
(inseparability in a pseudometric space is zero distance). -/
def zeroDistanceQuotientEDist {X : Type u} [PseudoEMetricSpace X] :
    ZeroDistanceQuotient X → ZeroDistanceQuotient X → ℝ≥0∞ :=
  SeparationQuotient.lift₂ edist fun _ _ _ _ hac hbd =>
    zeroDistance_edist_congr (EMetric.inseparable_iff.mp hac) (EMetric.inseparable_iff.mp hbd)

/-- Original label: `prop:pseudometric-quotient`.
The displayed formula `d∼([x],[x*]) = d(x,x*)`. -/
theorem zeroDistanceQuotientEDist_mk {X : Type u} [PseudoEMetricSpace X] (x y : X) :
    zeroDistanceQuotientEDist (SeparationQuotient.mk x) (SeparationQuotient.mk y) =
      edist x y := rfl

/-- Original label: `prop:pseudometric-quotient`.
Mathlib's separation-quotient distance is the same quotient distance. -/
theorem zeroDistanceQuotient_edist {X : Type u} [PseudoEMetricSpace X] (x y : X) :
    edist (SeparationQuotient.mk x) (SeparationQuotient.mk y) = edist x y := rfl

/-- Original label: `prop:pseudometric-quotient`. -/
theorem zeroDistanceQuotient_mk_eq_iff {X : Type u} [PseudoEMetricSpace X] (x y : X) :
    SeparationQuotient.mk x = SeparationQuotient.mk y ↔ edist x y = 0 := by
  rw [← edist_eq_zero, SeparationQuotient.edist_mk]

/-- Original label: `prop:pseudometric-quotient`.
The quotient distance is an extended metric on `X_∼`: symmetry and the triangle
inequality descend directly from `d` through representatives, and
`d∼([x],[x*]) = 0` means `d(x,x*) = 0`, i.e. `x ∼ x*`, i.e. `[x] = [x*]`. -/
theorem zeroDistanceQuotient_metric (X : Type u) [PseudoEMetricSpace X] :
    Analysis.IsExtendedMetric (zeroDistanceQuotientEDist (X := X)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
    obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
    rw [zeroDistanceQuotientEDist_mk, SeparationQuotient.mk_eq_mk, EMetric.inseparable_iff]
  · intro a b
    obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
    obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
    rw [zeroDistanceQuotientEDist_mk, zeroDistanceQuotientEDist_mk, edist_comm]
  · intro a b c
    obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
    obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
    obtain ⟨z, rfl⟩ := SeparationQuotient.surjective_mk c
    rw [zeroDistanceQuotientEDist_mk, zeroDistanceQuotientEDist_mk,
      zeroDistanceQuotientEDist_mk]
    exact edist_triangle x y z

/-- Original label: `prop:finite-metric-products`.
The manuscript's maximum metric `(x, x′) ↦ max_i d_i(x(i), x′(i))` on a finite
product, written as the finite supremum of the coordinate distances (the empty
product has distance zero). -/
def maximumEDist {I : Type u} [Fintype I] {X : I → Type v}
    [∀ i, PseudoEMetricSpace (X i)] (x y : (i : I) → X i) : ℝ≥0∞ :=
  Finset.univ.sup fun i => edist (x i) (y i)

/-- Original label: `prop:finite-metric-products`.
The indexed supremum over a finite set is its maximum. The empty product
has distance zero, consistent with the source's later empty-product use. -/
theorem finite_maximum_edist {I : Type u} [Fintype I] {X : I → Type v}
    [∀ i, PseudoEMetricSpace (X i)] (x y : (i : I) → X i) :
    edist x y = Finset.univ.sup (fun i => edist (x i) (y i)) := edist_pi_def x y

/-- Original label: `prop:finite-metric-products`.
Mathlib's product distance is the maximum metric. -/
theorem maximumEDist_eq_edist {I : Type u} [Fintype I] {X : I → Type v}
    [∀ i, PseudoEMetricSpace (X i)] (x y : (i : I) → X i) :
    maximumEDist x y = edist x y := (finite_maximum_edist x y).symm

/-- Original label: `prop:finite-metric-products`.
The maximum metric is a pseudometric: it vanishes on the diagonal and is
symmetric because every `d_i` is, and the triangle inequality holds in each
coordinate and therefore for the maximum. -/
theorem finite_maximum_pseudometric {I : Type u} [Fintype I] (X : I → Type v)
    [∀ i, PseudoEMetricSpace (X i)] :
    Analysis.IsExtendedPseudometric (maximumEDist (X := X)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact le_antisymm (Finset.sup_le fun i _ => (edist_self (x i)).le) (zero_le _)
  · intro x y
    exact Finset.sup_congr rfl fun i _ => edist_comm (x i) (y i)
  · intro x y z
    refine Finset.sup_le fun i _ => (edist_triangle (x i) (y i) (z i)).trans ?_
    exact add_le_add (Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i))
      (Finset.le_sup (f := fun i => edist (y i) (z i)) (Finset.mem_univ i))

/-- Original label: `prop:finite-metric-products`.
If every `d_i` is a metric, vanishing of the maximum forces equality in every
coordinate, so the maximum metric is a metric. -/
theorem finite_maximum_metric {I : Type u} [Fintype I] (X : I → Type v)
    [∀ i, EMetricSpace (X i)] : Analysis.IsExtendedMetric (maximumEDist (X := X)) := by
  obtain ⟨hself, hsymm, htri⟩ := finite_maximum_pseudometric X
  refine ⟨fun x y => ⟨fun h => ?_, by rintro rfl; exact hself x⟩, hsymm, htri⟩
  funext i
  refine edist_eq_zero.mp (le_antisymm ?_ (zero_le _))
  calc edist (x i) (y i) ≤ maximumEDist x y :=
        Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
    _ = 0 := h

/-- Original label: `prop:finite-metric-products`.
The ball of radius `ε` around `x` for the maximum metric is the product
`∏ B^{d_i}_ε(x(i))` of the coordinate balls. -/
theorem finite_maximum_ball {I : Type u} [Fintype I] {X : I → Type v}
    [∀ i, PseudoEMetricSpace (X i)] (x : (i : I) → X i) {ε : ℝ≥0∞} (hε : 0 < ε) :
    {y | maximumEDist x y < ε} = Set.univ.pi fun i => {z | edist (x i) z < ε} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
  constructor
  · intro h i
    exact (Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)).trans_lt h
  · intro h
    exact (Finset.sup_lt_iff (bot_le.trans_lt hε)).mpr fun i _ => h i

/-- Original label: `prop:finite-metric-products`.
The maximum metric induces the product topology, via the centred-ball
characterisation of open sets: a maximum ball is a product of coordinate balls,
hence open in the product topology; conversely a basic product open set
`∏ O_i ∋ x` contains the maximum ball of radius `min_i ε_i` as soon as
`B^{d_i}_{ε_i}(x(i)) ⊆ O_i` for every `i`. -/
theorem finite_maximum_isOpen_iff {I : Type u} [Fintype I] {X : I → Type v}
    [∀ i, PseudoEMetricSpace (X i)] (s : Set ((i : I) → X i)) :
    (∀ x ∈ s, ∃ ε > 0, {y | maximumEDist x y < ε} ⊆ s) ↔ IsOpen s := by
  constructor
  · intro h
    refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
    obtain ⟨ε, hε, hsub⟩ := h x hx
    refine ⟨{y | maximumEDist x y < ε}, hsub, ?_, ?_⟩
    · rw [finite_maximum_ball x hε]
      refine isOpen_set_pi Set.finite_univ fun i _ => ?_
      have hball : {z | edist (x i) z < ε} = Metric.eball (x i) ε := by
        ext z
        rw [Set.mem_setOf_eq, Metric.mem_eball, edist_comm]
      rw [hball]
      exact Metric.isOpen_eball
    · change maximumEDist x x < ε
      rw [(finite_maximum_pseudometric X).1 x]
      exact hε
  · intro hs x hx
    obtain ⟨J, u, hu, hJ⟩ := isOpen_pi_iff.mp hs x hx
    have hchoice : ∀ a, ∃ ε : ℝ≥0∞, 0 < ε ∧ (a ∈ J → Metric.eball (x a) ε ⊆ u a) := by
      intro a
      by_cases ha : a ∈ J
      · obtain ⟨ε, hε, hsub⟩ := EMetric.isOpen_iff.mp (hu a ha).1 (x a) (hu a ha).2
        exact ⟨ε, hε, fun _ => hsub⟩
      · exact ⟨1, zero_lt_one, fun h => (ha h).elim⟩
    choose ε hεpos hεsub using hchoice
    refine ⟨J.inf ε, (Finset.lt_inf_iff ENNReal.zero_lt_top).mpr fun a _ => hεpos a, ?_⟩
    intro y hy
    have hy' : maximumEDist x y < J.inf ε := hy
    refine hJ (Set.mem_pi.mpr fun a ha => hεsub a (Finset.mem_coe.mp ha) ?_)
    rw [Metric.mem_eball, edist_comm]
    exact ((Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ a)).trans_lt
      hy').trans_le (Finset.inf_le (Finset.mem_coe.mp ha))

/-- Original label: `prop:finite-metric-products`.
The product extended-metric instance retains the coordinate product
topology, rather than introducing a merely equivalent unrelated topology. -/
theorem finite_maximum_product_topology {I : Type u} [Finite I] (X : I → Type v)
    [∀ i, PseudoEMetricSpace (X i)] :
    (inferInstance : TopologicalSpace ((i : I) → X i)) = Pi.topologicalSpace := rfl

/-- Original label: `prop:finite-metric-products`.
Completeness by coordinates: a Cauchy sequence for the maximum metric is Cauchy
in every coordinate because `d_i ≤ d_max`; if every factor is complete, the
coordinate limits form a point `x` of the product, and convergence in every
coordinate gives `d_max(x_m, x) < ε` for all large `m`. -/
theorem finite_maximum_complete {I : Type u} [Finite I] (X : I → Type v)
    [∀ i, EMetricSpace (X i)] [∀ i, CompleteSpace (X i)] :
    CompleteSpace ((i : I) → X i) := by
  letI := Fintype.ofFinite I
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hcoord : ∀ i, CauchySeq fun n => u n i := by
    intro i
    refine EMetric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hu ε hε
    exact ⟨N, fun m hm n hn => (edist_le_pi_edist (u m) (u n) i).trans_lt (hN m hm n hn)⟩
  choose x hx using fun i => cauchySeq_tendsto_of_complete (hcoord i)
  refine ⟨x, EMetric.tendsto_atTop.mpr fun ε hε => ?_⟩
  choose N hN using fun i => EMetric.tendsto_atTop.mp (hx i) ε hε
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  refine (finite_maximum_edist (u n) x).trans_lt ?_
  exact (Finset.sup_lt_iff (bot_le.trans_lt hε)).mpr fun i _ =>
    hN i n ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn)

/-- Original label: `prop:finite-metric-products`.
Separability by coordinates: if `D_i ⊆ X_i` is countable and dense for every
`i`, then `∏ D_i` is countable, and it is dense because choosing `y_i ∈ D_i`
with `d_i(x(i), y_i) < ε` for every `i` gives `d_max(x, y) < ε`. -/
theorem finite_maximum_separable {I : Type u} [Finite I] (X : I → Type v)
    [∀ i, EMetricSpace (X i)] [∀ i, TopologicalSpace.SeparableSpace (X i)] :
    TopologicalSpace.SeparableSpace ((i : I) → X i) := by
  letI := Fintype.ofFinite I
  choose D hDc hDd using fun i => TopologicalSpace.exists_countable_dense (X i)
  refine ⟨⟨Set.univ.pi D, Set.countable_univ_pi hDc, ?_⟩⟩
  change ∀ x, x ∈ closure (Set.univ.pi D)
  intro x
  refine EMetric.mem_closure_iff.mpr fun ε hε => ?_
  choose y hyD hyx using fun i => EMetric.mem_closure_iff.mp (hDd i (x i)) ε hε
  refine ⟨y, Set.mem_univ_pi.mpr hyD, ?_⟩
  refine (finite_maximum_edist x y).trans_lt ?_
  exact (Finset.sup_lt_iff (bot_le.trans_lt hε)).mpr fun i _ => hyx i

end Thesis.Foundations.Preliminary.DoctoralAnalysis
