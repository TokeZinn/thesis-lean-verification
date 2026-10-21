import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Sequences
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Gδ subspaces of Polish spaces

The forward direction embeds the intersection into the product of its open
Polish superspaces as the closed set of coherent coordinate families. The
converse uses small-diameter neighborhoods and completeness of a compatible
metric on the subspace.
-/

noncomputable section

open Set Topology Filter TopologicalSpace

namespace Thesis.Foundations.Preliminary.DoctoralPolish

universe u

/-- Original label: `thm:alexandrov`, Gδ-to-Polish direction. -/
theorem polishSpace_of_isGDelta {X : Type u} [TopologicalSpace X] [PolishSpace X]
    {Y : Set X} (hY : IsGδ Y) : PolishSpace Y := by
  obtain ⟨U, hU, hYU⟩ := hY.eq_iInter_nat
  have hmem (y : Y) (n : ℕ) : (y : X) ∈ U n := by
    have hy : (y : X) ∈ ⋂ n, U n := hYU ▸ y.property
    exact Set.mem_iInter.mp hy n
  letI (n : ℕ) : PolishSpace (U n) := (hU n).polishSpace
  let embed : Y → (n : ℕ) → U n := fun y n => ⟨y.val, hmem y n⟩
  have hc : Continuous embed := continuous_pi fun n =>
    continuous_subtype_val.subtype_mk (fun y => hmem y n)
  have hemb : Topology.IsEmbedding embed :=
    Topology.IsEmbedding.of_comp hc
      (continuous_subtype_val.comp (continuous_apply 0)) Topology.IsEmbedding.subtypeVal
  have hrange : Set.range embed =
      ⋂ n : ℕ, {z : (n : ℕ) → U n | (z n : X) = (z 0 : X)} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact Set.mem_iInter.mpr (fun _ => rfl)
    · intro hz
      have hz' := Set.mem_iInter.mp hz
      have hy : (z 0 : X) ∈ Y := by
        rw [hYU]
        apply Set.mem_iInter.mpr
        intro n
        rw [← hz' n]
        exact (z n).property
      refine ⟨⟨z 0, hy⟩, ?_⟩
      funext n
      apply Subtype.ext
      exact (hz' n).symm
  have hclosed : IsClosed (Set.range embed) := by
    rw [hrange]
    exact isClosed_iInter (fun n => isClosed_eq
      (continuous_subtype_val.comp (continuous_apply n))
      (continuous_subtype_val.comp (continuous_apply 0)))
  exact (show Topology.IsClosedEmbedding embed from ⟨hemb, hclosed⟩).polishSpace

/-- Original label: `thm:alexandrov`, Polish-to-Gδ direction.
A compatible complete metric on the subspace forces every ambient limit
that has arbitrarily small subspace-diameter neighborhoods back into the
subspace. -/
theorem isGDelta_of_polishSubspace {X : Type u} [MetricSpace X]
    (Y : Set X) [PolishSpace Y] : IsGδ Y := by
  let completeMetric := completelyMetrizableMetric Y
  letI : MetricSpace Y := completeMetric
  letI : PseudoMetricSpace Y := completeMetric.toPseudoMetricSpace
  letI : Dist Y := completeMetric.toDist
  letI : UniformSpace Y := completeMetric.toUniformSpace
  letI : CompleteSpace Y := complete_completelyMetrizableMetric Y
  let V : ℕ → Set X := fun n => {x | ∃ U : Set X,
    IsOpen U ∧ x ∈ U ∧ ∀ y z : Y, (y : X) ∈ U → (z : X) ∈ U →
      dist y z < 1 / (n + 1 : ℝ)}
  have hV (n : ℕ) : IsOpen (V n) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨U, hU, hxU, hdiam⟩
    exact mem_of_superset (hU.mem_nhds hxU) (fun z hz => ⟨U, hU, hz, hdiam⟩)
  have hsub (n : ℕ) : Y ⊆ V n := by
    intro x hx
    let y : Y := ⟨x, hx⟩
    let r : ℝ := (1 / (n + 1 : ℝ)) / 2
    have hr : 0 < r := by dsimp [r]; positivity
    obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.mp
      (show IsOpen (Metric.ball y r) from Metric.isOpen_ball)
    have hmem (z : Y) : (z : X) ∈ U ↔ dist z y < r := by
      change z ∈ Subtype.val ⁻¹' U ↔ _
      rw [hpre]
      exact Metric.mem_ball
    refine ⟨U, hU, (hmem y).mpr (by simpa using hr), ?_⟩
    intro z w hz hw
    have hz' := (hmem z).mp hz
    have hw' := (hmem w).mp hw
    have htri := dist_triangle z y w
    rw [dist_comm y w] at htri
    dsimp [r] at hz' hw'
    linarith
  have heq : Y = closure Y ∩ ⋂ n, V n := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨subset_closure hx, Set.mem_iInter.mpr (fun n => hsub n hx)⟩
    · rintro x ⟨hxclosure, hxV⟩
      obtain ⟨s, hsY, hs⟩ := mem_closure_iff_seq_limit.mp hxclosure
      let t : ℕ → Y := fun n => ⟨s n, hsY n⟩
      have ht : CauchySeq t := by
        rw [@Metric.cauchySeq_iff Y ℕ completeMetric.toPseudoMetricSpace
          inferInstance inferInstance t]
        intro ε hε
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        obtain ⟨U, hU, hxU, hdiam⟩ := Set.mem_iInter.mp hxV n
        obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually (hU.mem_nhds hxU))
        exact ⟨N, fun i hi j hj => (hdiam (t i) (t j) (hN i hi) (hN j hj)).trans hn⟩
      obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete ht
      have hyX : Tendsto s atTop (𝓝 (y : X)) :=
        continuous_subtype_val.continuousAt.tendsto.comp hy
      have hxy : x = (y : X) := tendsto_nhds_unique hs hyX
      exact hxy.symm ▸ y.property
  rw [heq]
  exact isClosed_closure.isGδ.inter (IsGδ.iInter_of_isOpen hV)

/-- Original label: `thm:alexandrov`.
Both directions concern the actual inherited subspace topology. -/
theorem alexandrov {X : Type u} [TopologicalSpace X] [PolishSpace X] (Y : Set X) :
    Nonempty (PolishSpace Y) ↔ IsGδ Y := by
  constructor
  · rintro ⟨hY⟩
    letI := hY
    letI := upgradeIsCompletelyMetrizable X
    exact isGDelta_of_polishSubspace Y
  · intro hY
    exact ⟨polishSpace_of_isGDelta hY⟩

end Thesis.Foundations.Preliminary.DoctoralPolish
