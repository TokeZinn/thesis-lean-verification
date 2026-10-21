import Thesis.Appendices.ExtendedResearch.CDFConstraint
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.CDF
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Conditional distributions as actual L² classes

The threshold encoding is the class of `x ↦ 1{r ≤ x}` on restricted
Lebesgue measure. Clause (ii) follows the thesis proof: commute each scalar
inner-product test through conditional expectation, use the scalar
conditional-law identity and kernel Fubini, then intersect the null-set
complements for a countable dense family of tests. The kernel-barycentre form
is derived from it afterwards. No point evaluation of an arbitrary L²
representative is used.
-/

noncomputable section
namespace Thesis.Foundations.Research.CDFConditional

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal symmDiff InnerProductSpace
open CDFConstraint

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

instance intervalFinite (a b : ℝ) : IsFiniteMeasure (intervalMeasure a b) :=
  inferInstanceAs (IsFiniteMeasure (volume.restrict (Icc a b)))

/-- Original label: `prop:cdf-constraint-properties`.
The literal threshold target in the source's conditional expectation. -/
def threshold (a b r : ℝ) : ℝ →₂[intervalMeasure a b] ℝ :=
  indicatorConstLp 2 (s := Ici r) measurableSet_Ici (measure_ne_top _ _) 1

theorem threshold_ae (a b r : ℝ) :
    ⇑(threshold a b r) =ᵐ[intervalMeasure a b] (Ici r).indicator (fun _ ↦ (1 : ℝ)) :=
  indicatorConstLp_coeFn

theorem threshold_mem (a b r : ℝ) : threshold a b r ∈ constraint a b := by
  refine ⟨(Ici r).indicator (fun _ ↦ 1), ?_, ?_, (threshold_ae a b r).symm⟩
  · intro x _ y _ hxy
    by_cases hx : r ≤ x
    · simp [Set.indicator_of_mem, hx, hx.trans hxy]
    · by_cases hy : r ≤ y <;> simp [Set.indicator, hx, hy]
  · intro x _
    by_cases hx : r ≤ x <;> simp [Set.indicator, hx]

theorem continuous_threshold (a b : ℝ) : Continuous (threshold a b) := by
  unfold threshold
  apply continuous_indicatorConstLp_set (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  intro x
  have hup (y : ℝ) : intervalMeasure a b (Ici y ∆ Ici x) ≤
      ENNReal.ofReal (max x y - min x y) := by
    calc
      intervalMeasure a b (Ici y ∆ Ici x) ≤ volume (Ici y ∆ Ici x) :=
        Measure.restrict_apply_le _ _
      _ ≤ volume (Icc (min x y) (max x y)) := by
        apply measure_mono
        intro z hz
        simp only [mem_symmDiff, mem_Ici, not_le] at hz
        rcases hz with ⟨hy, hx⟩ | ⟨hx, hy⟩
        · exact ⟨(min_le_right x y).trans hy, le_max_of_le_left hx.le⟩
        · exact ⟨(min_le_left x y).trans hx, le_max_of_le_right hy.le⟩
      _ = ENNReal.ofReal (max x y - min x y) := Real.volume_Icc
  have hlim : Tendsto (fun y : ℝ ↦ ENNReal.ofReal (max x y - min x y)) (𝓝 x) (𝓝 0) := by
    convert (ENNReal.continuous_ofReal.comp
      ((continuous_const.max continuous_id).sub (continuous_const.min continuous_id))).tendsto x
      using 1
    simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) hup

theorem norm_threshold_le (a b r : ℝ) :
    ‖threshold a b r‖ ≤ (intervalMeasure a b).real univ ^ (1 / (2 : ℝ)) := by
  unfold threshold
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact measureReal_mono (subset_univ _)

theorem integrable_threshold (a b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (threshold a b) μ :=
  (integrable_const ((intervalMeasure a b).real univ ^ (1 / (2 : ℝ)))).mono'
    (continuous_threshold a b).aestronglyMeasurable
    (Eventually.of_forall (norm_threshold_le a b))

/-- The actual kernel barycentre belongs to the actual constraint set. -/
theorem kernel_average_mem (a b : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ r, threshold a b r ∂μ) ∈ constraint a b :=
  (CDFConstraint.convex a b).integral_mem (CDFConstraint.isClosed a b)
    (Eventually.of_forall (threshold_mem a b)) (integrable_threshold a b μ)

def cdfClass (a b : ℝ) (μ : Measure ℝ) : ℝ →₂[intervalMeasure a b] ℝ :=
  ((monotone_cdf μ).monotoneOn (Icc a b) |>.memLp_isCompact isCompact_Icc).toLp (cdf μ)

theorem cdfClass_ae (a b : ℝ) (μ : Measure ℝ) :
    ⇑(cdfClass a b μ) =ᵐ[intervalMeasure a b] cdf μ :=
  MemLp.coeFn_toLp _

/-- The scalar test of the thesis proof of clause (ii): for `u ∈ L²([a,b])` and the
kernel law `μ`, Fubini for `h_u(y) = ∫_a^b u(x) 1{y ≤ x} dx` gives
`∫ ⟪u, χ_r⟫ dμ(r) = ∫_a^b u(x) G(x) dx = ⟪u, [G|_{[a,b]}]⟫`. -/
theorem scalar_kernel_fubini (a b : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ →₂[intervalMeasure a b] ℝ) :
    (∫ r, ⟪u, threshold a b r⟫_ℝ ∂μ) = ⟪u, cdfClass a b μ⟫_ℝ := by
  let ν := intervalMeasure a b
  let f : ℝ × ℝ → ℝ := {z : ℝ × ℝ | z.1 ≤ z.2}.indicator (fun z ↦ u z.2)
  have hfm : StronglyMeasurable f :=
    (Lp.stronglyMeasurable u).comp_measurable measurable_snd |>.indicator
      (measurableSet_le measurable_fst measurable_snd)
  have hui : Integrable (fun x ↦ u x) ν := (Lp.memLp u).integrable (by norm_num)
  have hfi : Integrable f (μ.prod ν) := (hui.norm.comp_snd μ).mono' hfm.aestronglyMeasurable
    (Eventually.of_forall fun z ↦ by
      dsimp [f]
      by_cases hz : z.1 ≤ z.2 <;> simp [Set.indicator, hz])
  have htest (r : ℝ) : ⟪u, threshold a b r⟫_ℝ = ∫ x, f (r, x) ∂ν := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [threshold_ae a b r] with x hx
    rw [hx]
    dsimp [f]
    by_cases h : r ≤ x <;> simp [Set.indicator, h, inner]
  have hkernel (x : ℝ) : (∫ r, f (r, x) ∂μ) = u x * cdf μ x := by
    have hf : (fun r ↦ f (r, x)) = (Iic x).indicator (fun _ ↦ u x) := by
      funext r
      simp [f, Set.indicator]
    rw [hf, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, cdf_eq_real, mul_comm]
  calc
    (∫ r, ⟪u, threshold a b r⟫_ℝ ∂μ) = ∫ r, ∫ x, f (r, x) ∂ν ∂μ :=
      integral_congr_ae (Eventually.of_forall htest)
    _ = ∫ x, ∫ r, f (r, x) ∂μ ∂ν := integral_integral_swap hfi
    _ = ∫ x, u x * cdf μ x ∂ν := integral_congr_ae (Eventually.of_forall hkernel)
    _ = ⟪u, cdfClass a b μ⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [cdfClass_ae a b μ] with x hx
      simp [hx, inner, mul_comm]

/-- Fubini identifies the Hilbert barycentre with the CDF's actual restriction
class, rather than with an arbitrary pointwise version of a conditional mean. -/
theorem kernel_average_eq_cdfClass (a b : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ r, threshold a b r ∂μ) = cdfClass a b μ := by
  apply ext_inner_left ℝ
  intro u
  rw [← scalar_kernel_fubini a b μ u]
  exact (integral_inner (integrable_threshold a b μ) u).symm

/-- Each `G(ω, ·)` is a distribution function, so its restriction class lies in `𝒞`. -/
theorem cdfClass_mem (a b : ℝ) (μ : Measure ℝ) : cdfClass a b μ ∈ constraint a b :=
  ⟨cdf μ, (monotone_cdf μ).monotoneOn _,
    fun x _ ↦ ⟨cdf_nonneg μ x, cdf_le_one μ x⟩, (cdfClass_ae a b μ).symm⟩

/-- One scalar test `u` of the thesis proof: `⟪E[χ_t | 𝓕_s], u⟫ = E[⟪χ_t, u⟫ | 𝓕_s]`
almost surely (conditional expectation commutes with the continuous linear functional
`⟪u, ·⟫`), then the scalar conditional-law identity and `scalar_kernel_fubini`. -/
theorem scalar_conditional_cdf
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y) (a b : ℝ)
    (u : ℝ →₂[intervalMeasure a b] ℝ) :
    (fun ω ↦ ⟪u, P[fun ω ↦ threshold a b (X ω) |
      (inferInstance : MeasurableSpace T).comap Y] ω⟫_ℝ) =ᵐ[P]
      fun ω ↦ ⟪u, cdfClass a b (condDistrib X Y P (Y ω))⟫_ℝ := by
  letI : MeasurableSpace (ℝ →₂[intervalMeasure a b] ℝ) := borel _
  letI : BorelSpace (ℝ →₂[intervalMeasure a b] ℝ) := ⟨rfl⟩
  have hi : Integrable (fun ω ↦ threshold a b (X ω)) P :=
    (integrable_const ((intervalMeasure a b).real univ ^ (1 / (2 : ℝ)))).mono'
      ((continuous_threshold a b).measurable.comp hX).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ norm_threshold_le a b (X ω))
  have htest : Continuous (fun r ↦ ⟪u, threshold a b r⟫_ℝ) :=
    continuous_const.inner (continuous_threshold a b)
  have hs := condExp_ae_eq_integral_condDistrib hY hX.aemeasurable htest.stronglyMeasurable
    ((innerSL ℝ u).integrable_comp hi)
  have hc := (innerSL ℝ u).comp_condExp_comm (m := (inferInstance : MeasurableSpace T).comap Y) hi
  filter_upwards [hc, hs] with ω hcω hsω
  change ⟪u, P[fun ω ↦ threshold a b (X ω) |
    (inferInstance : MeasurableSpace T).comap Y] ω⟫_ℝ =
      P[fun ω ↦ ⟪u, threshold a b (X ω)⟫_ℝ |
        (inferInstance : MeasurableSpace T).comap Y] ω at hcω
  rw [hcω, hsω, scalar_kernel_fubini]

/-- Original label: `prop:cdf-constraint-properties`, clause (ii).
The thesis route: apply the scalar test identity to a countable dense subset of
`L²([a,b])`, discard the countably many null sets, and conclude
`E[χ_t | 𝓕_s] = [G_s(·,·)|_{[a,b]}]` almost surely; since each `G_s(ω, ·)` is a
distribution function, the conditional expectation lies in `𝒞` almost surely.
The same fixed conditional law supplies the CDF class at every outcome outside a
single null set; there is no family of pointwise exceptional sets. -/
theorem conditional_cdf
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y) (a b : ℝ) :
    P[fun ω ↦ threshold a b (X ω) | (inferInstance : MeasurableSpace T).comap Y] =ᵐ[P]
      (fun ω ↦ cdfClass a b (condDistrib X Y P (Y ω))) ∧
    ∀ᵐ ω ∂P, P[fun ω ↦ threshold a b (X ω) |
      (inferInstance : MeasurableSpace T).comap Y] ω ∈ constraint a b := by
  let H := ℝ →₂[intervalMeasure a b] ℝ
  obtain ⟨test : ℕ → H, hdense⟩ := TopologicalSpace.exists_dense_seq H
  have htests : ∀ n, (fun ω ↦ ⟪test n, P[fun ω ↦ threshold a b (X ω) |
      (inferInstance : MeasurableSpace T).comap Y] ω⟫_ℝ) =ᵐ[P]
      fun ω ↦ ⟪test n, cdfClass a b (condDistrib X Y P (Y ω))⟫_ℝ :=
    fun n ↦ scalar_conditional_cdf P X Y hX hY a b (test n)
  have hclass : P[fun ω ↦ threshold a b (X ω) |
      (inferInstance : MeasurableSpace T).comap Y] =ᵐ[P]
      (fun ω ↦ cdfClass a b (condDistrib X Y P (Y ω))) := by
    filter_upwards [ae_all_iff.mpr htests] with ω hω
    apply ext_inner_left ℝ
    have hall := hdense.equalizer (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const) (funext hω)
    exact congrFun hall
  refine ⟨hclass, ?_⟩
  filter_upwards [hclass] with ω hω
  rw [hω]
  exact cdfClass_mem a b _

/-- Original label: `prop:cdf-constraint-properties`, clause (ii), kernel-barycentre form.
The L²-valued conditional expectation is the barycentre of the single regular
conditional-law kernel. This is `conditional_cdf` (the scalar-test proof) combined
with the Fubini identification `kernel_average_eq_cdfClass` of that barycentre with
the CDF class; membership in the original constraint is inherited, without selecting
values of an L² representative at individual arguments. -/
theorem conditional_threshold
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y) (a b : ℝ) :
    P[fun ω ↦ threshold a b (X ω) | (inferInstance : MeasurableSpace T).comap Y] =ᵐ[P]
      (fun ω ↦ ∫ r, threshold a b r ∂condDistrib X Y P (Y ω)) ∧
    ∀ᵐ ω ∂P, P[fun ω ↦ threshold a b (X ω) |
      (inferInstance : MeasurableSpace T).comap Y] ω ∈ constraint a b := by
  simpa only [kernel_average_eq_cdfClass] using conditional_cdf P X Y hX hY a b

/-- Original label: `prop:cdf-constraint-properties`, clause (ii) for an
arbitrary information sigma-algebra, using its identity conditioning map. -/
theorem conditional_cdf_subsigma
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (P : @Measure Ω m₀) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : @Measurable Ω ℝ m₀ _ X) (a b : ℝ) :
    ∃ G : Ω → (ℝ →₂[intervalMeasure a b] ℝ),
      P[fun ω ↦ threshold a b (X ω) | m] =ᵐ[P] G ∧
      (∀ ω, ∃ κ : Measure ℝ, IsProbabilityMeasure κ ∧ G ω = cdfClass a b κ) ∧
      ∀ᵐ ω ∂P, P[fun ω ↦ threshold a b (X ω) | m] ω ∈ constraint a b := by
  have hid : @Measurable Ω Ω m₀ m id := fun _ hs ↦ hm _ hs
  have h := @conditional_cdf Ω Ω m₀ m P _ X id hX hid a b
  refine ⟨fun ω ↦ cdfClass a b (condDistrib X id P ω), ?_, ?_, ?_⟩
  · simpa only [MeasurableSpace.comap_id] using h.1
  · intro ω
    exact ⟨_, inferInstance, rfl⟩
  · simpa only [MeasurableSpace.comap_id] using h.2

end Thesis.Foundations.Research.CDFConditional
