import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Prokhorov topology for finite measures

The probability-measure topology theorem extends to finite measures by
continuous rescaling, continuity of total mass, and normalization away from
the zero measure. The zero measure is handled by its total mass directly.
-/

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace Thesis.Foundations.Stochastic.FiniteMeasureProkhorov

universe u

variable {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X] [OpensMeasurableSpace X]

abbrev LP (X : Type u) [MeasurableSpace X] := LevyProkhorov (FiniteMeasure X)

def scale (a : ℝ≥0) (μ : LP X) : LP X := LevyProkhorov.ofMeasure (a • μ.toMeasure)

theorem scale_coefficient_lipschitz (μ : LP X) :
    LipschitzWith μ.toMeasure.mass (fun a : ℝ≥0 => scale a μ) := by
  intro a b
  change levyProkhorovEDist (a • (μ.toMeasure : Measure X)) (b • (μ.toMeasure : Measure X)) ≤ _
  rw [edist_nndist, mul_comm, FiniteMeasure.ennreal_mass]
  apply levyProkhorovEDist_le_of_forall
  intro ε B hε hεtop hB
  have hpos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε.bot_lt) hεtop.ne
  have bound (a b : ℝ≥0) (hab : (nndist a b : ℝ≥0∞) * (μ.toMeasure : Measure X) univ < ε) :
      (a • (μ.toMeasure : Measure X)) B ≤
        (b • (μ.toMeasure : Measure X)) (thickening ε.toReal B) + ε := by
    simp only [Measure.coe_nnreal_smul_apply]
    calc
      (a : ℝ≥0∞) * (μ.toMeasure : Measure X) B ≤
          ((b : ℝ≥0∞) + nndist a b) * (μ.toMeasure : Measure X) B := by
        gcongr
        exact_mod_cast NNReal.le_add_nndist a b
      _ = b * (μ.toMeasure : Measure X) B +
          nndist a b * (μ.toMeasure : Measure X) B := add_mul _ _ _
      _ ≤ b * (μ.toMeasure : Measure X) (thickening ε.toReal B) +
          nndist a b * (μ.toMeasure : Measure X) univ := by
        gcongr
        · exact self_subset_thickening hpos B
        · exact subset_univ B
      _ ≤ _ := add_le_add le_rfl hab.le
  exact ⟨bound a b hε, bound b a (by simpa [nndist_comm] using hε)⟩

theorem scale_measure_lipschitz (a : ℝ≥0) :
    LipschitzWith (max a 1) (scale (X := X) a) := by
  intro μ ν
  change levyProkhorovEDist (a • (μ.toMeasure : Measure X)) (a • (ν.toMeasure : Measure X)) ≤ _
  let C : ℝ≥0 := max a 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCzero : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hC
  have hCtop : (C : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  apply levyProkhorovEDist_le_of_forall
  intro ε B hε hεtop hB
  have hsmall : edist μ ν < ε / C :=
    (ENNReal.lt_div_iff_mul_lt (.inl hCzero) (.inl hCtop)).mpr (by simpa [mul_comm, C] using hε)
  have hrad : ε / (C : ℝ≥0∞) ≤ ε := by
    calc
      ε / (C : ℝ≥0∞) ≤ ε / 1 := ENNReal.div_le_div_left (by exact_mod_cast le_max_right a 1) _
      _ = ε := div_one _
  have hthick : thickening (ε / (C : ℝ≥0∞)).toReal B ⊆ thickening ε.toReal B :=
    thickening_mono (ENNReal.toReal_mono hεtop.ne hrad) B
  have herror : (a : ℝ≥0∞) * (ε / C) ≤ ε := by
    calc
      (a : ℝ≥0∞) * (ε / C) ≤ (C : ℝ≥0∞) * (ε / C) := by
        gcongr
        exact_mod_cast le_max_left a 1
      _ = ε := ENNReal.mul_div_cancel hCzero hCtop
  have bound (μ ν : LP X)
      (h : (μ.toMeasure : Measure X) B ≤
        (ν.toMeasure : Measure X) (thickening (ε / (C : ℝ≥0∞)).toReal B) + ε / C) :
      (a • (μ.toMeasure : Measure X)) B ≤
        (a • (ν.toMeasure : Measure X)) (thickening ε.toReal B) + ε := by
    simp only [Measure.coe_nnreal_smul_apply]
    calc
      (a : ℝ≥0∞) * (μ.toMeasure : Measure X) B ≤
          a * ((ν.toMeasure : Measure X) (thickening (ε / (C : ℝ≥0∞)).toReal B) + ε / C) :=
        mul_le_mul_right h _
      _ = _ := mul_add _ _ _
      _ ≤ _ := add_le_add (mul_le_mul_right (measure_mono hthick) _) herror
  exact ⟨bound μ ν (left_measure_le_of_levyProkhorovEDist_lt hsmall hB),
    bound ν μ (right_measure_le_of_levyProkhorovEDist_lt hsmall hB)⟩

theorem mass_lipschitz : LipschitzWith 1 (fun μ : LP X => μ.toMeasure.mass) := by
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  simp only [NNReal.coe_one, one_mul, NNReal.dist_eq]
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hrpos : 0 < r := lt_of_le_of_lt dist_nonneg hr
  have hρ : levyProkhorovEDist (μ.toMeasure : Measure X) (ν.toMeasure : Measure X) <
      ENNReal.ofReal r := by
    change edist μ ν < ENNReal.ofReal r
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff hrpos |>.mpr hr
  have left := left_measure_le_of_levyProkhorovEDist_lt hρ MeasurableSet.univ
  have right := right_measure_le_of_levyProkhorovEDist_lt hρ MeasurableSet.univ
  have bound (μ ν : LP X)
      (h : (μ.toMeasure : Measure X) univ ≤
        (ν.toMeasure : Measure X) (thickening r univ) + ENNReal.ofReal r) :
      (μ.toMeasure.mass : ℝ) ≤ ν.toMeasure.mass + r := by
    have h' : (μ.toMeasure.mass : ℝ≥0∞) ≤ ν.toMeasure.mass + ENNReal.ofReal r := by
      rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
      exact h.trans (add_le_add (measure_mono (subset_univ _)) le_rfl)
    have hreal := ENNReal.toReal_mono (by finiteness) h'
    simpa [ENNReal.toReal_add, hrpos.le] using hreal
  have hleft := bound μ ν (by simpa [ENNReal.toReal_ofReal hrpos.le] using left)
  have hright := bound ν μ (by simpa [ENNReal.toReal_ofReal hrpos.le] using right)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Rescaling finite measures is jointly continuous in the coefficient and
the Prokhorov metric. -/
theorem continuous_scale : Continuous (fun p : ℝ≥0 × LP X => scale p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hcoeff := ((scale_coefficient_lipschitz p.2).continuous.tendsto p.1).comp
    continuous_fst.continuousAt
  have hcoeffdist := tendsto_iff_dist_tendsto_zero.mp hcoeff
  have hmeasure : Tendsto (fun q : ℝ≥0 × LP X => dist q.2 p.2) (𝓝 p) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp continuous_snd.continuousAt
  have hmax : Tendsto (fun q : ℝ≥0 × LP X => (max q.1 1 : ℝ≥0)) (𝓝 p) (𝓝 (max p.1 1)) :=
    continuous_fst.continuousAt.max tendsto_const_nhds
  have hbound := ((NNReal.continuous_coe.tendsto _).comp hmax).mul hmeasure |>.add hcoeffdist
  simp only [mul_zero, zero_add] at hbound
  apply squeeze_zero (fun _ => dist_nonneg) ?_ hbound
  intro q
  exact (dist_triangle (scale q.1 q.2) (scale q.1 p.2) (scale p.1 p.2)).trans
    (add_le_add ((scale_measure_lipschitz q.1).dist_le_mul q.2 p.2) le_rfl)

def probabilityInclusion (P : LevyProkhorov (ProbabilityMeasure X)) : LP X :=
  LevyProkhorov.ofMeasure P.toMeasure.toFiniteMeasure

theorem probabilityInclusion_isometry : Isometry (probabilityInclusion (X := X)) :=
  fun _ _ => rfl

theorem tendsto_normalize_prokhorov [Nonempty X] {ι : Type*} {L : Filter ι}
    {μs : ι → LP X} {μ : LP X} (h : Tendsto μs L (𝓝 μ)) (hne : μ.toMeasure ≠ 0) :
    Tendsto (fun i => LevyProkhorov.ofMeasure (μs i).toMeasure.normalize) L
      (𝓝 (LevyProkhorov.ofMeasure μ.toMeasure.normalize)) := by
  have hm := (mass_lipschitz.continuous.tendsto μ).comp h
  have hmne := μ.toMeasure.mass_nonzero_iff.mpr hne
  have hinv := hm.inv₀ hmne
  have hscale := (continuous_scale.tendsto (μ.toMeasure.mass⁻¹, μ)).comp (hinv.prodMk_nhds h)
  have hevent : ∀ᶠ i in L, (μs i).toMeasure ≠ 0 := by
    filter_upwards [hm.eventually (isOpen_ne.mem_nhds hmne)] with i hi
    exact (μs i).toMeasure.mass_nonzero_iff.mp hi
  have heq : (fun i => probabilityInclusion (LevyProkhorov.ofMeasure (μs i).toMeasure.normalize))
      =ᶠ[L] (fun i => scale (μs i).toMeasure.mass⁻¹ (μs i)) := by
    filter_upwards [hevent] with i hi
    change LevyProkhorov.ofMeasure _ = LevyProkhorov.ofMeasure _
    rw [FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero _ hi]
  have hlim : probabilityInclusion (LevyProkhorov.ofMeasure μ.toMeasure.normalize) =
      scale μ.toMeasure.mass⁻¹ μ := by
    change LevyProkhorov.ofMeasure _ = LevyProkhorov.ofMeasure _
    rw [FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero _ hne]
  apply (probabilityInclusion_isometry (X := X)).tendsto_nhds_iff.mpr
  rw [hlim]
  exact hscale.congr' heq.symm

/-- Metric convergence to zero is controlled exactly by total mass. -/
theorem dist_zero_le_mass (μ : LP X) :
    dist μ (LevyProkhorov.ofMeasure (0 : FiniteMeasure X)) ≤ μ.toMeasure.mass := by
  have h := levyProkhorovEDist_le_max_measure_univ
    (μ.toMeasure : Measure X) (0 : Measure X)
  simp only [Measure.coe_zero, Pi.zero_apply, max_eq_left (zero_le _)] at h
  have h' := ENNReal.toReal_mono (measure_ne_top (μ.toMeasure : Measure X) univ) h
  simpa [LevyProkhorov.dist_finiteMeasure_def, levyProkhorovDist,
    ← FiniteMeasure.ennreal_mass] using h'

/-- The Prokhorov metric topology is at least as fine as weak convergence. -/
theorem continuous_toMeasure : Continuous (LevyProkhorov.toMeasure (α := FiniteMeasure X)) := by
  rw [continuous_iff_continuousAt]
  intro μ
  have hm := mass_lipschitz.continuous.tendsto μ
  by_cases hzero : μ.toMeasure = 0
  · rw [ContinuousAt, hzero]
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa [hzero] using hm
  · haveI : Nonempty X := nonempty_of_measure_ne_zero
      (μ := (μ.toMeasure : Measure X)) (s := univ) (by
        rw [← FiniteMeasure.ennreal_mass]
        exact ENNReal.coe_ne_zero.mpr (μ.toMeasure.mass_nonzero_iff.mpr hzero)) |>.nonempty
    apply (FiniteMeasure.tendsto_normalize_iff_tendsto hzero).mp
    exact ⟨(LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp
      (tendsto_normalize_prokhorov tendsto_id hzero), hm⟩

/-- On a separable space, weak convergence also implies Prokhorov convergence. -/
theorem continuous_ofMeasure [TopologicalSpace.SeparableSpace X] :
    Continuous (LevyProkhorov.ofMeasure (α := FiniteMeasure X)) := by
  rw [continuous_iff_continuousAt]
  intro μ
  by_cases hzero : μ = 0
  · subst μ
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun ν => dist_zero_le_mass (LevyProkhorov.ofMeasure ν))
    exact (NNReal.continuous_coe.tendsto 0).comp (FiniteMeasure.continuous_mass.tendsto 0)
  · haveI : Nonempty X := nonempty_of_measure_ne_zero
      (μ := (μ : Measure X)) (s := univ) (by
        rw [← FiniteMeasure.ennreal_mass]
        exact ENNReal.coe_ne_zero.mpr (μ.mass_nonzero_iff.mpr hzero)) |>.nonempty
    have hn := FiniteMeasure.tendsto_normalize_of_tendsto tendsto_id hzero
    have hprob := (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto _).comp hn
    have hprob' := (probabilityInclusion_isometry.continuous.tendsto _).comp hprob
    have hscale := (continuous_scale.tendsto
      (μ.mass, probabilityInclusion (LevyProkhorov.ofMeasure μ.normalize))).comp
      ((FiniteMeasure.continuous_mass.tendsto μ).prodMk_nhds hprob')
    simpa only [Function.comp_def, scale, probabilityInclusion, id_eq,
      ← FiniteMeasure.self_eq_mass_smul_normalize] using hscale

/-- The actual identity homeomorphism between weak and Prokhorov topologies. -/
def finiteMeasureHomeomorph [TopologicalSpace.SeparableSpace X] : FiniteMeasure X ≃ₜ LP X where
  toFun := LevyProkhorov.ofMeasure
  invFun := LevyProkhorov.toMeasure
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_ofMeasure
  continuous_invFun := continuous_toMeasure

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`.
Weak and Prokhorov convergence coincide for arbitrary filters, and hence
for the sequences in the thesis. Completeness of the base is not needed. -/
theorem tendsto_iff [TopologicalSpace.SeparableSpace X] {ι : Type*} {L : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} :
    Tendsto (fun i => LevyProkhorov.ofMeasure (μs i)) L (𝓝 (LevyProkhorov.ofMeasure μ)) ↔
      Tendsto μs L (𝓝 μ) :=
  (finiteMeasureHomeomorph (X := X)).isEmbedding.tendsto_nhds_iff.symm

/-- Original label: `thm:prokhorov-metric`.
The finite-measure Prokhorov pseudometric separates Borel measures. -/
theorem dist_eq_zero_iff [BorelSpace X] [TopologicalSpace.SeparableSpace X]
    (μ ν : LP X) : dist μ ν = 0 ↔ μ = ν := by
  letI : T2Space (LP X) := (finiteMeasureHomeomorph (X := X)).symm.isEmbedding.t2Space
  constructor
  · intro h
    exact (Metric.inseparable_iff.mpr h).eq
  · rintro rfl
    exact dist_self _

end Thesis.Foundations.Stochastic.FiniteMeasureProkhorov
