import Thesis.Appendices.MeasureTheory.MeasureTheory

/-! # The simple-function construction of the Bochner integral

This supplies the approximation and finite-sum clauses of the manuscript's
definition, rather than linking only to the integral's name. Nonnegative L¹
errors use the extended Lebesgue integral, so nonintegrable errors cannot be
silently interpreted as zero by a totalized real integral.
-/

namespace Thesis.Foundations.Preliminary.MeasureTheory

open _root_.MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators

universe u v

variable {Ω : Type u} {V : Type v} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [TopologicalSpace.SeparableSpace V]

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- Original label: `prop:bochner-integrability`.
The literal finite-norm-integral criterion under the manuscript's measurable,
separable Banach hypotheses. -/
theorem bochnerIntegrable_iff_finite_norm_integral
    (μ : Measure Ω) (f : Ω → V) (hf : Measurable f) :
    Integrable f μ ↔ (∫⁻ ω, ‖f ω‖ₑ ∂μ) < ∞ := by
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hf.aestronglyMeasurable, h⟩⟩

/-- Original label: `defn:bochner-integral`.
Every integrable measurable Banach-valued function has integrable simple
approximants converging in integrated norm, whose integrals converge in `V`. -/
theorem bochner_simple_approximation
    (μ : Measure Ω) (f : Ω → V) (hf : Measurable f) (hfi : Integrable f μ) :
    ∃ s : ℕ → SimpleFunc Ω V, (∀ n, Integrable (s n) μ) ∧
      Tendsto (fun n ↦ ∫⁻ ω, ‖f ω - s n ω‖ₑ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ ω, s n ω ∂μ) atTop (𝓝 (bochnerIntegral μ f)) := by
  let s : ℕ → SimpleFunc Ω V :=
    SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp)
  have hsi (n : ℕ) : Integrable (s n) μ :=
    SimpleFunc.integrable_approxOn_range hf hfi n
  refine ⟨s, hsi, ?_, ?_⟩
  · simpa only [s, enorm_sub_rev] using
      SimpleFunc.tendsto_approxOn_range_L1_enorm hf hfi
  · have hlim := tendsto_integral_approxOn_of_measurable_of_range_subset
      hf hfi (range f ∪ {0}) subset_rfl
    simpa only [s, bochnerIntegral, SimpleFunc.integral_eq_integral _ (hsi _)] using hlim

/-- Original label: `defn:bochner-integral`; this equivalence is also the
content of `prop:bochner-integrability` (the simple-approximation criterion
versus the finite-norm-integral criterion).
The simple-approximation criterion is equivalent to integrability. The
converse uses a finite integrated error at one index; it does not assume
integrability of the target or of every approximation error in advance. -/
theorem bochnerIntegrable_iff_simple_approximation
    (μ : Measure Ω) (f : Ω → V) (hf : Measurable f) :
    Integrable f μ ↔ ∃ s : ℕ → SimpleFunc Ω V,
      (∀ n, Integrable (s n) μ) ∧
      Tendsto (fun n ↦ ∫⁻ ω, ‖f ω - s n ω‖ₑ ∂μ) atTop (𝓝 0) := by
  constructor
  · intro hfi
    obtain ⟨s, hs, hlim, _⟩ := bochner_simple_approximation μ f hf hfi
    exact ⟨s, hs, hlim⟩
  · rintro ⟨s, hs, hlim⟩
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))).exists
    have hsub : Integrable (fun ω ↦ f ω - s n ω) μ :=
      ⟨hf.aestronglyMeasurable.sub (s n).aestronglyMeasurable, hn.trans (by norm_num)⟩
    convert hsub.add (hs n) using 1
    funext ω
    simp

/-- Original label: `defn:bochner-integral`.
Every sequence satisfying the manuscript's approximation criterion gives the
same integral limit, so the definition is independent of the selected sequence. -/
theorem bochner_integral_tendsto_of_simple_approximation
    (μ : Measure Ω) (f : Ω → V) (hf : Measurable f)
    (s : ℕ → SimpleFunc Ω V) (hs : ∀ n, Integrable (s n) μ)
    (hlim : Tendsto (fun n ↦ ∫⁻ ω, ‖f ω - s n ω‖ₑ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ bochnerIntegral μ (s n)) atTop (𝓝 (bochnerIntegral μ f)) := by
  have hfi := (bochnerIntegrable_iff_simple_approximation μ f hf).mpr ⟨s, hs, hlim⟩
  exact tendsto_integral_of_L1 f hfi (Eventually.of_forall hs)
    (by simpa only [enorm_sub_rev] using hlim)

omit [MeasurableSpace V] [BorelSpace V] [TopologicalSpace.SeparableSpace V] in
/-- Original label: `defn:bochner-integral`.
The finite weighted-sum formula on the measurable level-set partition. Any
other integrable simple presentation defining the same function has the same
integral, as proved by `bochner_simple_integral_congr` below. -/
theorem bochner_simple_integral_eq_sum
    (μ : Measure Ω) (s : SimpleFunc Ω V) (hs : Integrable s μ) :
    bochnerIntegral μ s = ∑ v ∈ s.range, μ.real (s ⁻¹' {v}) • v := by
  exact s.integral_eq_sum hs

omit [MeasurableSpace V] [BorelSpace V] [TopologicalSpace.SeparableSpace V] in
/-- Original label: `defn:bochner-integral`.
Independence of the simple-function presentation, including equality only
almost everywhere. -/
theorem bochner_simple_integral_congr
    (μ : Measure Ω) (s t : SimpleFunc Ω V) (hs : Integrable s μ)
    (ht : Integrable t μ) (hst : (s : Ω → V) =ᵐ[μ] t) :
    (∑ v ∈ s.range, μ.real (s ⁻¹' {v}) • v) =
      ∑ v ∈ t.range, μ.real (t ⁻¹' {v}) • v := by
  rw [← bochner_simple_integral_eq_sum μ s hs, ← bochner_simple_integral_eq_sum μ t ht]
  exact integral_congr_ae hst

/-- Original label: `defn:simple-function`.
Linearity for nonnegative indicator presentations does not require disjoint
sets. Overlaps are counted in the represented function; the current source
equivalently refines the sets and combines coefficients on each cell. -/
theorem lintegral_finite_indicator_sum
    {ι : Type*} (μ : Measure Ω) (I : Finset ι) (E : ι → Set Ω) (a : ι → ℝ≥0∞)
    (hE : ∀ i ∈ I, MeasurableSet (E i)) :
    (∫⁻ ω, ∑ i ∈ I, (E i).indicator (fun _ ↦ a i) ω ∂μ) =
      ∑ i ∈ I, a i * μ (E i) := by
  rw [lintegral_finset_sum I (fun i hi ↦ measurable_const.indicator (hE i hi))]
  exact Finset.sum_congr rfl (fun i hi ↦ lintegral_indicator_const (hE i hi) (a i))

omit [MeasurableSpace V] [BorelSpace V] [TopologicalSpace.SeparableSpace V] in
/-- Original label: `defn:bochner-integral`.
The finite weighted-sum formula holds for any measurable indicator
presentation whose individual terms are integrable, including partitions.
Neither disjointness nor distinct vector values are needed for this identity. -/
theorem bochner_finite_indicator_sum
    {ι : Type*} (μ : Measure Ω) (I : Finset ι) (E : ι → Set Ω) (v : ι → V)
    (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hfi : ∀ i ∈ I, Integrable ((E i).indicator (fun _ ↦ v i)) μ) :
    bochnerIntegral μ (fun ω ↦ ∑ i ∈ I, (E i).indicator (fun _ ↦ v i) ω) =
      ∑ i ∈ I, μ.real (E i) • v i := by
  change (∫ ω, ∑ i ∈ I, (E i).indicator (fun _ ↦ v i) ω ∂μ) = _
  rw [integral_finset_sum I hfi]
  exact Finset.sum_congr rfl (fun i hi ↦ integral_indicator_const (v i) (hE i hi))

omit [MeasurableSpace V] [BorelSpace V] [TopologicalSpace.SeparableSpace V] in
/-- Original label: `defn:bochner-integral`.
The source's finite weighted norm condition suffices for each indicator term,
including zero vectors on cells of infinite measure. -/
theorem bochner_finite_indicator_sum_of_norm_sum_lt_top
    {ι : Type*} (μ : Measure Ω) (I : Finset ι) (E : ι → Set Ω) (v : ι → V)
    (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hfinite : (∑ i ∈ I, ‖v i‖ₑ * μ (E i)) < ∞) :
    Integrable (fun ω ↦ ∑ i ∈ I, (E i).indicator (fun _ ↦ v i) ω) μ ∧
      bochnerIntegral μ (fun ω ↦ ∑ i ∈ I, (E i).indicator (fun _ ↦ v i) ω) =
        ∑ i ∈ I, μ.real (E i) • v i := by
  have hfi (i : ι) (hi : i ∈ I) :
      Integrable ((E i).indicator (fun _ ↦ v i)) μ := by
    refine ⟨(aestronglyMeasurable_const).indicator (hE i hi), ?_⟩
    change (∫⁻ ω, ‖(E i).indicator (fun _ ↦ v i) ω‖ₑ ∂μ) < ∞
    simp_rw [enorm_indicator_eq_indicator_enorm]
    rw [lintegral_indicator_const (hE i hi)]
    exact (Finset.single_le_sum (fun j _ ↦ zero_le (‖v j‖ₑ * μ (E j))) hi).trans_lt hfinite
  exact ⟨integrable_finset_sum I hfi, bochner_finite_indicator_sum μ I E v hE hfi⟩

omit [MeasurableSpace V] [BorelSpace V] [TopologicalSpace.SeparableSpace V]
  [NormedSpace ℝ V] [CompleteSpace V] in
/-- Original label: `defn:bochner-integral`.
For disjoint measurable cells, the integrated norm is exactly the weighted
norm sum in the source. The cells need not exhaust the domain: outside them
the represented simple function is zero. -/
theorem bochner_partition_norm_integral
    {ι : Type*} (μ : Measure Ω) (I : Finset ι) (E : ι → Set Ω) (v : ι → V)
    (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hd : (I : Set ι).PairwiseDisjoint E) :
    (∫⁻ ω, ‖∑ i ∈ I, (E i).indicator (fun _ ↦ v i) ω‖ₑ ∂μ) =
      ∑ i ∈ I, ‖v i‖ₑ * μ (E i) := by
  classical
  have hpoint (ω : Ω) :
      ‖∑ i ∈ I, (E i).indicator (fun _ ↦ v i) ω‖ₑ =
        ∑ i ∈ I, (E i).indicator (fun _ ↦ ‖v i‖ₑ) ω := by
    by_cases hmem : ∃ i ∈ I, ω ∈ E i
    · obtain ⟨i, hi, hω⟩ := hmem
      have hz (j : ι) (hj : j ∈ I) (hji : j ≠ i) : ω ∉ E j := by
        exact fun hjω => Set.disjoint_left.mp (hd hj hi hji) hjω hω
      rw [Finset.sum_eq_single i (fun j hj hji => Set.indicator_of_notMem (hz j hj hji) _)
          (fun hni => (hni hi).elim),
        Finset.sum_eq_single i (fun j hj hji => Set.indicator_of_notMem (hz j hj hji) _)
          (fun hni => (hni hi).elim)]
      simp only [Set.indicator_of_mem hω]
    · have hz (i : ι) (hi : i ∈ I) : ω ∉ E i := fun hω => hmem ⟨i, hi, hω⟩
      simp only [Finset.sum_eq_zero (fun i hi => Set.indicator_of_notMem (hz i hi) _),
        enorm_zero]
  simp_rw [hpoint]
  exact lintegral_finite_indicator_sum μ I E (fun i => ‖v i‖ₑ) hE

/-- Original label: `prop:lp-banach`.
The representative-level inner-product formula is invariant under changes
on null sets in either argument. -/
theorem integral_inner_congr_ae
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) {f f' g g' : Ω → H}
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    (∫ ω, inner ℝ (f ω) (g ω) ∂μ) = ∫ ω, inner ℝ (f' ω) (g' ω) ∂μ := by
  apply integral_congr_ae
  filter_upwards [hf, hg] with ω hfw hgw
  rw [hfw, hgw]

end Thesis.Foundations.Preliminary.MeasureTheory
