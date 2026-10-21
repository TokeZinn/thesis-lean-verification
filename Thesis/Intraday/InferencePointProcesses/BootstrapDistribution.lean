import Thesis.Intraday.InferencePointProcesses.BlockBootstrap
import Thesis.Intraday.InferencePointProcesses.PointProcessBootstrap
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Order.Interval.Set.Union

/-! # Distributional invariance of the literal point-process bootstrap

This supplies the path-to-array independence, counting-measure decomposition,
and independent random-selector steps of `prop:block-bootstrap-invariance`.
Random selector coordinates may have any joint law.
-/

noncomputable section
namespace Thesis.Intraday.BootstrapDistribution

open MeasureTheory ProbabilityTheory Set Function
open Foundations.Stochastic.PointProcesses
open PointProcessBootstrap
open scoped BigOperators

variable {Ω X K J : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Independence of whole paths and of the restrictions within every path
implies independence of the full array of restrictions. -/
theorem restriction_array_independent (μ : Measure Ω)
    (paths : K → Ω → FiniteIntegerMeasures X)
    (hp : ∀ k, Measurable (paths k)) (hind : iIndepFun paths μ)
    (blocks : J → Set X) (hb : ∀ j, MeasurableSet (blocks j))
    (hrow : ∀ k, iIndepFun (fun j ω => restrict (paths k ω) (blocks j) (hb j)) μ) :
    iIndepFun (fun kj : K × J => fun ω =>
      restrict (paths kj.1 ω) (blocks kj.2) (hb kj.2)) μ := by
  apply iIndepFun_uncurry'
    (X := fun k j ω => restrict (paths k ω) (blocks j) (hb j))
  · intro k j
    exact (measurable_restrict (blocks j) (hb j)).comp (hp k)
  · exact hind.comp (fun _ x j => restrict x (blocks j) (hb j))
      (fun _ => measurable_pi_lambda _ (fun j => measurable_restrict (blocks j) (hb j)))
  · exact hrow

/-- Disjoint restrictions recover a finite counting measure whenever the
discarded complement has zero mass. This is equality of measures. -/
theorem sum_restrict_eq [Fintype J] (ν : FiniteIntegerMeasures X)
    (blocks : J → Set X) (hb : ∀ j, MeasurableSet (blocks j))
    (hd : Pairwise (Disjoint on blocks))
    (hzero : (ν.1 : Measure X) (⋃ j, blocks j)ᶜ = 0) :
    PointProcessBootstrap.sum (fun j => restrict ν (blocks j) (hb j)) = ν := by
  unfold PointProcessBootstrap.sum
  apply Subtype.ext
  apply Subtype.ext
  change ((∑ j, (restrict ν (blocks j) (hb j)).1 : FiniteMeasure X) : Measure X) = _
  simp only [FiniteMeasure.toMeasure_sum]
  change (∑ j, (ν.1 : Measure X).restrict (blocks j)) = _
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd hb]
  exact Measure.restrict_eq_self_of_ae_mem (by simpa only [ae_iff] using hzero)

/-- Original label: `prop:block-bootstrap-invariance`.
The deterministic selector theorem uses the source's whole-path independence,
equal path laws, within-path block independence, and zero discarded mass. -/
theorem deterministic_same_law [Fintype J] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (paths : K → Ω → FiniteIntegerMeasures X) (reference : K)
    (hp : ∀ k, Measurable (paths k)) (hind : iIndepFun paths μ)
    (hlaw : ∀ k, IdentDistrib (paths k) (paths reference) μ μ)
    (blocks : J → Set X) (hb : ∀ j, MeasurableSet (blocks j))
    (hd : Pairwise (Disjoint on blocks))
    (hrow : ∀ k, iIndepFun (fun j ω => restrict (paths k ω) (blocks j) (hb j)) μ)
    (hzero : ∀ᵐ ω ∂μ, ((paths reference ω).1 : Measure X) (⋃ j, blocks j)ᶜ = 0)
    (choose : J → K) :
    IdentDistrib (fun ω => bootstrap (fun k => paths k ω) choose blocks hb)
      (paths reference) μ μ := by
  have ha := restriction_array_independent μ paths hp hind blocks hb hrow
  have hs := BlockBootstrap.selected_aggregate_same_law μ
    (fun kj ω => restrict (paths kj.1 ω) (blocks kj.2) (hb kj.2)) reference choose
    (fun kj => ((PointProcessBootstrap.measurable_restrict (blocks kj.2) (hb kj.2)).comp
      (hp kj.1)).aemeasurable) ha
    (fun k j => (hlaw k).comp (PointProcessBootstrap.measurable_restrict (blocks j) (hb j)))
    PointProcessBootstrap.sum measurable_sum
  apply hs.trans
  apply IdentDistrib.of_ae_eq hs.aemeasurable_snd
  filter_upwards [hzero] with ω hω
  exact sum_restrict_eq _ blocks hb hd hω

section RandomSelection

variable {S W Y : Type*} [Finite S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace W] [MeasurableSpace Y]

/-- A finite random mixture of equally distributed statistics has their
common law if the selector is independent of the underlying observations.
No independence among components of a vector-valued selector is required. -/
theorem independent_random_selection_same_law (μ : Measure Ω) [IsProbabilityMeasure μ]
    (selector : Ω → S) (observations : Ω → W) (reference : Ω → Y)
    (hs : Measurable selector) (ho : Measurable observations) (hr : Measurable reference)
    (hind : IndepFun selector observations μ)
    (statistic : S → W → Y) (hm : ∀ s, Measurable (statistic s))
    (hlaw : ∀ s, IdentDistrib (fun ω => statistic s (observations ω)) reference μ μ) :
    IdentDistrib (fun ω => statistic (selector ω) (observations ω)) reference μ μ := by
  classical
  letI := Fintype.ofFinite S
  have hmjoint : Measurable (fun p : S × W => statistic p.1 p.2) :=
    measurable_from_prod_countable_right hm
  have hselected : Measurable (fun ω => statistic (selector ω) (observations ω)) :=
    hmjoint.comp (hs.prodMk ho)
  refine ⟨hselected.aemeasurable, hr.aemeasurable, ?_⟩
  ext A hA
  rw [Measure.map_apply hselected hA, Measure.map_apply hr hA]
  let fiber : S → Set Ω := fun s => selector ⁻¹' {s}
  let event : S → Set Ω := fun s => fiber s ∩ (fun ω => statistic s (observations ω)) ⁻¹' A
  have hf : ∀ s, MeasurableSet (fiber s) := fun s => hs (measurableSet_singleton s)
  have he : ∀ s, MeasurableSet (event s) :=
    fun s => (hf s).inter (((hm s).comp ho) hA)
  have hfd : Pairwise (Disjoint on fiber) := by
    intro s t hst
    exact Disjoint.preimage selector (disjoint_singleton.mpr hst)
  have hed : Pairwise (Disjoint on event) := by
    intro s t hst
    exact (hfd hst).mono inter_subset_left inter_subset_left
  have hcover : (⋃ s, fiber s) = univ := by ext ω; simp [fiber]
  have hevent : (fun ω => statistic (selector ω) (observations ω)) ⁻¹' A = ⋃ s, event s := by
    ext ω
    simp only [mem_preimage, mem_iUnion, event, fiber, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro h
      exact ⟨selector ω, rfl, h⟩
    · rintro ⟨s, rfl, h⟩
      exact h
  have hmass : ∑ s, μ (fiber s) = 1 := by
    have h := measure_iUnion hfd hf (μ := μ)
    simpa only [hcover, measure_univ, tsum_fintype] using h.symm
  rw [hevent, measure_iUnion hed he, tsum_fintype]
  calc
    ∑ s, μ (event s) = ∑ s, μ (fiber s) * μ (reference ⁻¹' A) := by
      apply Finset.sum_congr rfl
      intro s _
      change μ (selector ⁻¹' {s} ∩ (statistic s ∘ observations) ⁻¹' A) = _
      have hi : IndepFun selector (statistic s ∘ observations) μ :=
        hind.comp measurable_id (hm s)
      rw [hi.measure_inter_preimage_eq_mul
        {s} A (measurableSet_singleton s) hA]
      change μ (fiber s) * μ ((fun ω => statistic s (observations ω)) ⁻¹' A) = _
      rw [(hlaw s).measure_mem_eq hA]
    _ = μ (reference ⁻¹' A) := by rw [← Finset.sum_mul, hmass, one_mul]

end RandomSelection

/-- Original label: `prop:block-bootstrap-invariance`.
An arbitrary random selector vector independent of the entire path vector
preserves the original point-process law. -/
theorem random_same_law [Fintype J] [Finite K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (paths : K → Ω → FiniteIntegerMeasures X) (reference : K)
    (hp : ∀ k, Measurable (paths k)) (hind : iIndepFun paths μ)
    (hlaw : ∀ k, IdentDistrib (paths k) (paths reference) μ μ)
    (blocks : J → Set X) (hb : ∀ j, MeasurableSet (blocks j))
    (hd : Pairwise (Disjoint on blocks))
    (hrow : ∀ k, iIndepFun (fun j ω => restrict (paths k ω) (blocks j) (hb j)) μ)
    (hzero : ∀ᵐ ω ∂μ, ((paths reference ω).1 : Measure X) (⋃ j, blocks j)ᶜ = 0)
    (choose : Ω → J → K) (hc : Measurable choose)
    (hcind : IndepFun choose (fun ω k => paths k ω) μ) :
    IdentDistrib (fun ω => bootstrap (fun k => paths k ω) (choose ω) blocks hb)
      (paths reference) μ μ := by
  apply independent_random_selection_same_law μ choose (fun ω k => paths k ω)
    (paths reference) hc (measurable_pi_lambda _ hp) (hp reference) hcind
    (fun c source => bootstrap source c blocks hb)
    (fun c => measurable_bootstrap c blocks hb)
  intro c
  exact deterministic_same_law μ paths reference hp hind hlaw blocks hb hd hrow hzero c

/-- The source's half-open time cells, indexed from zero in Lean. -/
def timeBlocks {L : ℕ} (τ : ℕ → ℝ) (time : X → ℝ) (j : Fin L) : Set X :=
  time ⁻¹' Ioc (τ j.val) (τ (j.val + 1))

theorem measurable_timeBlocks {L : ℕ} (τ : ℕ → ℝ) (time : X → ℝ)
    (ht : Measurable time) (j : Fin L) : MeasurableSet (timeBlocks τ time j) :=
  ht measurableSet_Ioc

omit [MeasurableSpace X] in
/-- Ordered partition endpoints make the half-open cells disjoint, including
when an endpoint is an atom of the point process. -/
theorem timeBlocks_disjoint {L : ℕ} (τ : ℕ → ℝ) (time : X → ℝ)
    (hτ : MonotoneOn τ (Icc 0 L)) :
    Pairwise (Disjoint on (timeBlocks (L := L) τ time)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  change τ i.val < time x ∧ time x ≤ τ (i.val + 1) at hi
  change τ j.val < time x ∧ time x ≤ τ (j.val + 1) at hj
  rcases lt_or_gt_of_ne hij with hij | hij
  · have he := hτ (show i.val + 1 ∈ Icc 0 L by constructor <;> omega)
      (show j.val ∈ Icc 0 L by constructor <;> omega) (Nat.succ_le_of_lt hij)
    exact (not_lt_of_ge (hi.2.trans he)) hj.1
  · have he := hτ (show j.val + 1 ∈ Icc 0 L by constructor <;> omega)
      (show i.val ∈ Icc 0 L by constructor <;> omega) (Nat.succ_le_of_lt hij)
    exact (not_lt_of_ge (hj.2.trans he)) hi.1

omit [MeasurableSpace X] in
/-- The only point of `[0,1]` omitted by the source's half-open time
partition is zero. No zero-mass condition is required at other endpoints. -/
theorem timeBlocks_compl {L : ℕ} (τ : ℕ → ℝ) (time : X → ℝ)
    (hτ : MonotoneOn τ (Icc 0 L)) (hfirst : τ 0 = 0) (hlast : τ L = 1)
    (htime : ∀ x, time x ∈ Icc (0 : ℝ) 1) :
    (⋃ j : Fin L, timeBlocks τ time j)ᶜ = time ⁻¹' {0} := by
  ext x
  simp only [mem_compl_iff, mem_iUnion, mem_preimage, mem_singleton_iff]
  constructor
  · intro hx
    by_contra hn
    have hm : time x ∈ Ioc (τ 0) (τ L) := by
      rw [hfirst, hlast]
      exact ⟨lt_of_le_of_ne (htime x).1 (Ne.symm hn), (htime x).2⟩
    have he := Ioc_subset_biUnion_Ioc L τ hm
    simp only [mem_iUnion, Finset.mem_range] at he
    obtain ⟨j, hj, hmem⟩ := he
    exact hx ⟨⟨j, hj⟩, hmem⟩
  · intro hz ⟨j, hj⟩
    change τ j.val < time x ∧ time x ≤ τ (j.val + 1) at hj
    have he := hτ (show 0 ∈ Icc 0 L by simp)
      (show j.val ∈ Icc 0 L by constructor <;> omega) (Nat.zero_le j.val)
    rw [hfirst] at he
    rw [hz] at hj
    exact (not_lt_of_ge he) hj.1

/-- Original label: `prop:block-bootstrap-invariance`.
The literal half-open time partition requires only the source's absence of
atoms at time zero; the discarded-mass condition is derived here. -/
theorem time_bootstrap_same_law {L : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (paths : K → Ω → FiniteIntegerMeasures X) (reference : K)
    (hp : ∀ k, Measurable (paths k)) (hind : iIndepFun paths μ)
    (hlaw : ∀ k, IdentDistrib (paths k) (paths reference) μ μ)
    (τ : ℕ → ℝ) (hτ : MonotoneOn τ (Icc 0 L)) (hfirst : τ 0 = 0) (hlast : τ L = 1)
    (time : X → ℝ) (ht : Measurable time) (htime : ∀ x, time x ∈ Icc (0 : ℝ) 1)
    (hrow : ∀ k, iIndepFun (fun j : Fin L => fun ω =>
      restrict (paths k ω) (timeBlocks τ time j) (measurable_timeBlocks τ time ht j)) μ)
    (hzero : ∀ᵐ ω ∂μ, ((paths reference ω).1 : Measure X) (time ⁻¹' {0}) = 0)
    (choose : Fin L → K) :
    IdentDistrib (fun ω => bootstrap (fun k => paths k ω) choose
      (timeBlocks τ time) (measurable_timeBlocks τ time ht)) (paths reference) μ μ := by
  apply deterministic_same_law μ paths reference hp hind hlaw (timeBlocks τ time)
    (measurable_timeBlocks τ time ht) (timeBlocks_disjoint τ time hτ) hrow
  simpa only [timeBlocks_compl τ time hτ hfirst hlast htime] using hzero

/-- Original label: `prop:block-bootstrap-invariance`.
Full random-selector form for the literal time cells, with no requirement
that the selector coordinates be independent. -/
theorem time_random_bootstrap_same_law {L : ℕ} [Finite K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (paths : K → Ω → FiniteIntegerMeasures X) (reference : K)
    (hp : ∀ k, Measurable (paths k)) (hind : iIndepFun paths μ)
    (hlaw : ∀ k, IdentDistrib (paths k) (paths reference) μ μ)
    (τ : ℕ → ℝ) (hτ : MonotoneOn τ (Icc 0 L)) (hfirst : τ 0 = 0) (hlast : τ L = 1)
    (time : X → ℝ) (ht : Measurable time) (htime : ∀ x, time x ∈ Icc (0 : ℝ) 1)
    (hrow : ∀ k, iIndepFun (fun j : Fin L => fun ω =>
      restrict (paths k ω) (timeBlocks τ time j) (measurable_timeBlocks τ time ht j)) μ)
    (hzero : ∀ᵐ ω ∂μ, ((paths reference ω).1 : Measure X) (time ⁻¹' {0}) = 0)
    (choose : Ω → Fin L → K) (hc : Measurable choose)
    (hcind : IndepFun choose (fun ω k => paths k ω) μ) :
    IdentDistrib (fun ω => bootstrap (fun k => paths k ω) (choose ω)
      (timeBlocks τ time) (measurable_timeBlocks τ time ht)) (paths reference) μ μ := by
  apply random_same_law μ paths reference hp hind hlaw (timeBlocks τ time)
    (measurable_timeBlocks τ time ht) (timeBlocks_disjoint τ time hτ) hrow _ choose hc hcind
  simpa only [timeBlocks_compl τ time hτ hfirst hlast htime] using hzero

end Thesis.Intraday.BootstrapDistribution
