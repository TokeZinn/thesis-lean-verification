import Thesis.Appendices.ExtendedResearch.PITCalibration
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.IsLUB

/-! # The randomized distribution transform, including atoms

The auxiliary uniform coordinate spreads an atom over its whole CDF jump.
The generalized inverse used in the proof is constructed from the infimum of
a CDF superlevel set; it is not an extra assumption on the distribution.
-/

noncomputable section
namespace Thesis.Foundations.Research.RandomizedCDF

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open PITCalibration

def leftCDF (μ : Measure ℝ) (x : ℝ) : ℝ := Function.leftLim (cdf μ) x

/-- The literal randomized CDF formula from the thesis. -/
def transform (μ : Measure ℝ) (y v : ℝ) : ℝ :=
  leftCDF μ y + v * (cdf μ y - leftCDF μ y)

theorem leftCDF_nonneg (μ : Measure ℝ) (x : ℝ) : 0 ≤ leftCDF μ x := by
  exact (cdf_nonneg μ (x - 1)).trans ((monotone_cdf μ).le_leftLim (by linarith))

theorem leftCDF_le (μ : Measure ℝ) (x : ℝ) : leftCDF μ x ≤ cdf μ x :=
  (monotone_cdf μ).leftLim_le le_rfl

theorem transform_mem (μ : Measure ℝ) (y : ℝ) {v : ℝ} (hv : v ∈ Icc 0 1) :
    transform μ y v ∈ Icc 0 1 := by
  have hA := leftCDF_nonneg μ y
  have hAB := leftCDF_le μ y
  have hB := cdf_le_one μ y
  dsimp [transform]
  constructor <;> nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hAB),
    mul_nonneg (sub_nonneg.mpr hv.2) (sub_nonneg.mpr hAB)]

theorem transform_bounds (μ : Measure ℝ) (y : ℝ) {v : ℝ} (hv : v ∈ Icc 0 1) :
    leftCDF μ y ≤ transform μ y v ∧ transform μ y v ≤ cdf μ y := by
  have hAB := leftCDF_le μ y
  dsimp [transform]
  constructor <;> nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hAB),
    mul_nonneg (sub_nonneg.mpr hv.2) (sub_nonneg.mpr hAB)]

theorem measurable_transform (μ : Measure ℝ) :
    Measurable (fun z : ℝ × ℝ => transform μ z.1 z.2) := by
  have hA : Measurable (leftCDF μ) := (monotone_cdf μ).leftLim.measurable
  exact (hA.comp measurable_fst).add
    (measurable_snd.mul (((monotone_cdf μ).measurable.comp measurable_fst).sub
      (hA.comp measurable_fst)))

theorem measure_Iio [IsProbabilityMeasure μ] (x : ℝ) :
    μ (Iio x) = ENNReal.ofReal (leftCDF μ x) := by
  calc
    μ (Iio x) = (cdf μ).measure (Iio x) := by rw [measure_cdf]
    _ = ENNReal.ofReal (leftCDF μ x) := by
      rw [StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot μ)]
      simp [leftCDF]

theorem measure_singleton [IsProbabilityMeasure μ] (x : ℝ) :
    μ {x} = ENNReal.ofReal (cdf μ x - leftCDF μ x) := by
  calc
    μ {x} = (cdf μ).measure {x} := by rw [measure_cdf]
    _ = ENNReal.ofReal (cdf μ x - leftCDF μ x) :=
      StieltjesFunction.measure_singleton _ x

theorem uniformLaw_Iio {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    uniformLaw (Iio u) = ENNReal.ofReal u := by
  have he : Iio u ∩ Icc (0 : ℝ) 1 = Ico 0 u := by
    ext v
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨hvu, h0v, _⟩
      exact ⟨h0v, hvu⟩
    · rintro ⟨h0v, hvu⟩
      exact ⟨hvu, h0v, hvu.le.trans hu.2⟩
  simp [uniformLaw, Measure.restrict_apply measurableSet_Iio, he]

/-- Every interior probability level has a real generalized inverse, with the
two one-sided CDF values bracketing that level. -/
theorem exists_cut (μ : Measure ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ q : ℝ, (∀ y < q, cdf μ y < t) ∧ leftCDF μ q ≤ t ∧ t ≤ cdf μ q := by
  let S : Set ℝ := {y | t ≤ cdf μ y}
  have hS : S.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds ht.2)).exists
    exact ⟨y, hy.le⟩
  have hSb : BddBelow S := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds ht.1)).exists
    refine ⟨y, fun x hx => ?_⟩
    by_contra h
    exact (not_le_of_gt hy) ((monotone_cdf μ (le_of_not_ge h)).trans' hx)
  let q := sInf S
  have hbelow : ∀ y < q, cdf μ y < t := by
    intro y hy
    by_contra h
    exact (not_le_of_gt hy) (csInf_le hSb (show y ∈ S from le_of_not_gt h))
  have hleft : leftCDF μ q ≤ t := by
    apply le_of_tendsto ((monotone_cdf μ).tendsto_leftLim q)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hbelow y hy).le
  obtain ⟨u, _, hu, huS⟩ := exists_seq_tendsto_sInf hS hSb
  have huq : ∀ n, q ≤ u n := fun n => csInf_le hSb (huS n)
  have hright := (cdf μ).right_continuous q
  have hlim : Tendsto (fun n => cdf μ (u n)) atTop (𝓝 (cdf μ q)) :=
    hright.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      _ hu (Eventually.of_forall huq))
  exact ⟨q, hbelow, hleft, ge_of_tendsto hlim (Eventually.of_forall huS)⟩

theorem uniform_affine_Iio {A B t : ℝ} (hAB : A < B) (hAt : A ≤ t) (htB : t ≤ B) :
    uniformLaw {v | A + v * (B - A) < t} = ENNReal.ofReal ((t - A) / (B - A)) := by
  have hd : 0 < B - A := sub_pos.mpr hAB
  have hr : (t - A) / (B - A) ∈ Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr hAt) hd.le, (div_le_one hd).mpr (by linarith)⟩
  have he : {v : ℝ | A + v * (B - A) < t} = Iio ((t - A) / (B - A)) := by
    ext v
    simp only [mem_setOf_eq, mem_Iio, lt_div_iff₀ hd]
    constructor <;> intro h <;> linarith
  rw [he, uniformLaw_Iio hr]

theorem transform_prod_Iio_at_cut (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q t : ℝ} (hbelow : ∀ y < q, cdf μ y < t) (hright : t ≤ cdf μ q) :
    (μ.prod uniformLaw) ((fun z : ℝ × ℝ => transform μ z.1 z.2) ⁻¹' Iio t) =
      μ (Iio q) + uniformLaw {v | transform μ q v < t} * μ {q} := by
  classical
  rw [Measure.prod_apply ((measurable_transform μ) measurableSet_Iio)]
  have hfiber (y : ℝ) :
      uniformLaw {v | transform μ y v < t} =
        (Iio q).indicator (fun _ => (1 : ℝ≥0∞)) y +
          ({q} : Set ℝ).indicator (fun _ => uniformLaw {v | transform μ q v < t}) y := by
    have hm : MeasurableSet {v | transform μ y v < t} :=
      measurableSet_lt ((measurable_transform μ).comp measurable_prodMk_left) measurable_const
    rcases lt_trichotomy y q with hy | rfl | hy
    · have he : {v | transform μ y v < t} ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
        ext v
        constructor
        · exact fun h => h.2
        · intro hv
          exact ⟨(transform_bounds μ y hv).2.trans_lt (hbelow y hy), hv⟩
      simp [Set.indicator, hy, ne_of_lt hy, uniformLaw, Measure.restrict_apply hm, he]
    · simp [Set.indicator]
    · have he : {v | transform μ y v < t} ∩ Icc (0 : ℝ) 1 = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro v ⟨hvt, hv⟩
        exact (not_lt_of_ge (hright.trans
          (((monotone_cdf μ).le_leftLim hy).trans (transform_bounds μ y hv).1))) hvt
      simp [Set.indicator, not_lt.mpr hy.le, ne_of_gt hy, uniformLaw,
        Measure.restrict_apply hm, he]
  calc
    (∫⁻ y, uniformLaw (Prod.mk y ⁻¹'
        ((fun z : ℝ × ℝ => transform μ z.1 z.2) ⁻¹' Iio t)) ∂μ) =
        ∫⁻ y, (Iio q).indicator (fun _ => (1 : ℝ≥0∞)) y +
          ({q} : Set ℝ).indicator (fun _ => uniformLaw {v | transform μ q v < t}) y ∂μ :=
      lintegral_congr fun y => hfiber y
    _ = μ (Iio q) + uniformLaw {v | transform μ q v < t} * μ {q} := by
      rw [lintegral_add_left (measurable_const.indicator measurableSet_Iio),
        lintegral_indicator_const measurableSet_Iio,
        lintegral_indicator_const (measurableSet_singleton q), one_mul]

theorem transform_prod_Iio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (μ.prod uniformLaw) ((fun z : ℝ × ℝ => transform μ z.1 z.2) ⁻¹' Iio t) =
      ENNReal.ofReal t := by
  obtain ⟨q, hbelow, hleft, hright⟩ := exists_cut μ ht
  rw [transform_prod_Iio_at_cut μ hbelow hright, measure_Iio, measure_singleton]
  by_cases hzero : cdf μ q - leftCDF μ q = 0
  · have he : leftCDF μ q = t := by linarith
    rw [hzero, ENNReal.ofReal_zero, mul_zero, add_zero, he]
  · have hpos : leftCDF μ q < cdf μ q :=
      lt_of_le_of_ne (leftCDF_le μ q) (fun he => hzero (by linarith))
    rw [show {v | transform μ q v < t} =
      {v | leftCDF μ q + v * (cdf μ q - leftCDF μ q) < t} from rfl,
      uniform_affine_Iio hpos hleft hright, ← ENNReal.ofReal_mul
        (div_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr (leftCDF_le μ q))),
      div_mul_cancel₀ _ hzero, ← ENNReal.ofReal_add (leftCDF_nonneg μ q)
        (sub_nonneg.mpr hleft)]
    congr 1
    ring

theorem probability_Iic_zero_of_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Icc (0 : ℝ) 1) = 1) {t : ℝ} (ht : t < 0) : ν (Iic t) = 0 := by
  have hc : ν (Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (measure_ne_top _ _)]
    simp [hν]
  apply le_antisymm _ (zero_le _)
  rw [← hc]
  apply measure_mono
  intro x hx hmem
  exact (not_le_of_gt ht) (hmem.1.trans hx)

theorem probability_Iic_one_of_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Icc (0 : ℝ) 1) = 1) {t : ℝ} (ht : 1 ≤ t) : ν (Iic t) = 1 := by
  apply le_antisymm (prob_le_one)
  rw [← hν]
  exact measure_mono (fun _ hx => hx.2.trans ht)

/-- A probability measure supported on the unit interval is determined by its
strict lower-tail probabilities at interior levels. -/
theorem eq_uniformLaw_of_Iio (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Icc (0 : ℝ) 1) = 1)
    (htail : ∀ t ∈ Ioo (0 : ℝ) 1, ν (Iio t) = ENNReal.ofReal t) : ν = uniformLaw := by
  have huni : uniformLaw (Icc (0 : ℝ) 1) = 1 := by simp [uniformLaw]
  apply Measure.ext_of_Iic
  intro t
  by_cases ht0 : t < 0
  · rw [probability_Iic_zero_of_support ν hν ht0,
      probability_Iic_zero_of_support uniformLaw huni ht0]
  by_cases ht1 : 1 ≤ t
  · rw [probability_Iic_one_of_support ν hν ht1,
      probability_Iic_one_of_support uniformLaw huni ht1]
  have ht : t ∈ Ico (0 : ℝ) 1 := ⟨le_of_not_gt ht0, lt_of_not_ge ht1⟩
  have hlower : t ≤ cdf ν t := by
    by_cases hzero : t = 0
    · simpa [hzero] using cdf_nonneg ν t
    have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    have hm := ENNReal.toReal_mono (measure_ne_top ν (Iic t))
      (measure_mono (Iio_subset_Iic_self : Iio t ⊆ Iic t))
    rw [htail t ⟨htp, ht.2⟩, ENNReal.toReal_ofReal ht.1] at hm
    exact hm.trans_eq (cdf_eq_real ν t).symm
  have hupper : cdf ν t ≤ t := by
    by_contra h
    have hlt : t < cdf ν t := lt_of_not_ge h
    let u := (t + cdf ν t) / 2
    have htu : t < u := by dsimp [u]; linarith
    have huF : u < cdf ν t := by dsimp [u]; linarith
    have hu : u ∈ Ioo (0 : ℝ) 1 :=
      ⟨ht.1.trans_lt htu, huF.trans_le (cdf_le_one ν t)⟩
    have hm := ENNReal.toReal_mono (measure_ne_top ν (Iio u))
      (measure_mono (Iic_subset_Iio.mpr htu))
    have : cdf ν t ≤ u := by
      rw [htail u hu, ENNReal.toReal_ofReal hu.1.le] at hm
      exact (cdf_eq_real ν t).trans_le hm
    exact (not_le_of_gt huF) this
  rw [← ofReal_cdf, le_antisymm hupper hlower, uniformLaw_Iic t ⟨ht.1, ht.2.le⟩]

/-- Randomization by an independent uniform coordinate makes the full
distribution transform exactly uniform, including all atoms. -/
theorem map_transform (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (μ.prod uniformLaw).map (fun z : ℝ × ℝ => transform μ z.1 z.2) = uniformLaw := by
  let ν := (μ.prod uniformLaw).map (fun z : ℝ × ℝ => transform μ z.1 z.2)
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map
    (measurable_transform μ).aemeasurable
  apply eq_uniformLaw_of_Iio ν
  · rw [Measure.map_apply (measurable_transform μ) measurableSet_Icc]
    apply le_antisymm prob_le_one
    calc
      1 = (μ.prod uniformLaw) (univ ×ˢ Icc (0 : ℝ) 1) := by simp [uniformLaw]
      _ ≤ (μ.prod uniformLaw)
          ((fun z : ℝ × ℝ => transform μ z.1 z.2) ⁻¹' Icc 0 1) :=
        measure_mono (fun z hz => transform_mem μ z.1 hz.2)
  · intro t ht
    rw [Measure.map_apply (measurable_transform μ) measurableSet_Iio]
    exact transform_prod_Iio μ ht

end Thesis.Foundations.Research.RandomizedCDF
