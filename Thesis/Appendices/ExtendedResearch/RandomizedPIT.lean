import Thesis.Appendices.ExtendedResearch.RandomizedCDF
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Conditional randomized PIT from a fresh uniform variable

The forecast is the actual regular conditional distribution of the outcome.
The auxiliary uniform is independent of the pair consisting of the forecast
information and the outcome. Disintegration and the atom-inclusive randomized
distribution transform give the conditional uniform law.
-/

noncomputable section
namespace Thesis.Foundations.Research.RandomizedPIT

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open PITCalibration RandomizedCDF

variable {T : Type*} [MeasurableSpace T]

theorem measurable_kernel_leftCDF (κ : Kernel T ℝ) [IsMarkovKernel κ] :
    Measurable (fun z : T × ℝ => leftCDF (κ z.1) z.2) := by
  have hm := Kernel.measurable_kernel_prodMk_left
    (κ := κ.comap Prod.fst measurable_fst)
    (measurableSet_lt measurable_snd measurable_fst.snd :
      MeasurableSet {p : (T × ℝ) × ℝ | p.2 < p.1.2})
  have he : (fun z : T × ℝ => leftCDF (κ z.1) z.2) =
      (fun z => (κ z.1 (Iio z.2)).toReal) := by
    funext z
    rw [RandomizedCDF.measure_Iio, ENNReal.toReal_ofReal (leftCDF_nonneg _ _)]
  rw [he]
  exact hm.ennreal_toReal

theorem measurable_kernel_cdf (κ : Kernel T ℝ) [IsMarkovKernel κ] :
    Measurable (fun z : T × ℝ => cdf (κ z.1) z.2) := by
  have hm := Kernel.measurable_kernel_prodMk_left
    (κ := κ.comap Prod.fst measurable_fst)
    (measurableSet_le measurable_snd measurable_fst.snd :
      MeasurableSet {p : (T × ℝ) × ℝ | p.2 ≤ p.1.2})
  have he : (fun z : T × ℝ => cdf (κ z.1) z.2) =
      (fun z => (κ z.1 (Iic z.2)).toReal) := by
    funext z
    exact cdf_eq_real _ _
  rw [he]
  exact hm.ennreal_toReal

theorem measurable_kernel_transform (κ : Kernel T ℝ) [IsMarkovKernel κ] :
    Measurable (fun z : (T × ℝ) × ℝ => transform (κ z.1.1) z.1.2 z.2) := by
  exact ((measurable_kernel_leftCDF κ).comp measurable_fst).add
    (measurable_snd.mul (((measurable_kernel_cdf κ).comp measurable_fst).sub
      ((measurable_kernel_leftCDF κ).comp measurable_fst)))

theorem kernel_transform_event (ν : Measure T) [SFinite ν]
    (κ : Kernel T ℝ) [IsMarkovKernel κ]
    (A : Set T) (B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((ν ⊗ₘ κ).prod uniformLaw)
      {z : (T × ℝ) × ℝ | z.1.1 ∈ A ∧ transform (κ z.1.1) z.1.2 z.2 ∈ B} =
        ν A * uniformLaw B := by
  classical
  let S : Set ((T × ℝ) × ℝ) :=
    {z | z.1.1 ∈ A ∧ transform (κ z.1.1) z.1.2 z.2 ∈ B}
  have hS : MeasurableSet S :=
    (hA.preimage measurable_fst.fst).inter ((measurable_kernel_transform κ) hB)
  change ((ν ⊗ₘ κ).prod uniformLaw) S = _
  rw [Measure.prod_apply hS,
    Measure.lintegral_compProd (measurable_measure_prodMk_left hS)]
  have hfiber (a : T) :
      (∫⁻ x, uniformLaw (Prod.mk (a, x) ⁻¹' S) ∂κ a) =
        A.indicator (fun _ => uniformLaw B) a := by
    by_cases ha : a ∈ A
    · rw [Set.indicator_of_mem ha]
      calc
        (∫⁻ x, uniformLaw (Prod.mk (a, x) ⁻¹' S) ∂κ a) =
            ((κ a).prod uniformLaw)
              ((fun z : ℝ × ℝ => transform (κ a) z.1 z.2) ⁻¹' B) := by
          rw [Measure.prod_apply ((measurable_transform (κ a)) hB)]
          apply lintegral_congr
          intro x
          congr 1
          ext v
          simp [S, ha]
        _ = uniformLaw B := by
          rw [← Measure.map_apply (measurable_transform (κ a)) hB, map_transform]
    · have he (x : ℝ) : Prod.mk (a, x) ⁻¹' S = ∅ := by
        ext v
        simp [S, ha]
      simp [he, Set.indicator_of_notMem ha]
  calc
    (∫⁻ a, ∫⁻ x, uniformLaw (Prod.mk (a, x) ⁻¹' S) ∂κ a ∂ν) =
        ∫⁻ a, A.indicator (fun _ => uniformLaw B) a ∂ν := lintegral_congr hfiber
    _ = ν A * uniformLaw B := by
      rw [lintegral_indicator_const hA, mul_comm]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The actual regular conditional CDF, randomized by a fresh uniform,
has constant conditional uniform law at the forecast origin. The independence
hypothesis concerns the raw uniform and `(information,outcome)`, not the PIT. -/
theorem conditionalLaw_randomizedCDF_of_kernel (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : Ω → T) (V : Ω → ℝ)
    (κ : Kernel T ℝ) [IsMarkovKernel κ]
    (hX : Measurable X) (hY : Measurable Y) (hV : Measurable V)
    (forecast : P.map (fun ω => (Y ω, X ω)) = (P.map Y) ⊗ₘ κ)
    (fresh : IndepFun (fun ω => (Y ω, X ω)) V P)
    (uniform : P.map V = uniformLaw) :
    ConditionalLaw P ((inferInstance : MeasurableSpace T).comap Y)
      (fun ω => transform (κ (Y ω)) (X ω) (V ω)) uniformLaw := by
  have hj : Measurable (fun ω => ((Y ω, X ω), V ω)) := (hY.prodMk hX).prodMk hV
  have hJoint : P.map (fun ω => ((Y ω, X ω), V ω)) =
      ((P.map Y) ⊗ₘ κ).prod uniformLaw := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map
      (hY.prodMk hX).aemeasurable hV.aemeasurable).mp fresh, uniform,
      forecast]
  intro A B hA hB
  obtain ⟨A', hA', rfl⟩ := hA
  let S : Set ((T × ℝ) × ℝ) :=
    {z | z.1.1 ∈ A' ∧ transform (κ z.1.1) z.1.2 z.2 ∈ B}
  have hS : MeasurableSet S :=
    (hA'.preimage measurable_fst.fst).inter ((measurable_kernel_transform κ) hB)
  calc
    P (Y ⁻¹' A' ∩
        (fun ω => transform (κ (Y ω)) (X ω) (V ω)) ⁻¹' B) =
        (P.map (fun ω => ((Y ω, X ω), V ω))) S :=
      (Measure.map_apply hj hS).symm
    _ = (((P.map Y) ⊗ₘ κ).prod uniformLaw) S := by rw [hJoint]
    _ = (P.map Y) A' * uniformLaw B := kernel_transform_event _ κ A' B hA' hB
    _ = P (Y ⁻¹' A') * uniformLaw B := by rw [Measure.map_apply hY hA']

theorem conditionalLaw_randomizedCDF (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : Ω → T) (V : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hV : Measurable V)
    (fresh : IndepFun (fun ω => (Y ω, X ω)) V P)
    (uniform : P.map V = uniformLaw) :
    ConditionalLaw P ((inferInstance : MeasurableSpace T).comap Y)
      (fun ω => transform (condDistrib X Y P (Y ω)) (X ω) (V ω)) uniformLaw := by
  exact conditionalLaw_randomizedCDF_of_kernel P X Y V (condDistrib X Y P)
    hX hY hV (compProd_map_condDistrib hX.aemeasurable).symm fresh uniform

set_option maxHeartbeats 800000 in
-- Comparing the composed measurable maps unfolds the regular conditional kernel's instances.
theorem measurable_randomizedCDF (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : Ω → T) (V : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hV : Measurable V) :
    Measurable (fun ω => transform (condDistrib X Y P (Y ω)) (X ω) (V ω)) := by
  let κ : Kernel T ℝ := condDistrib X Y P
  have hm : Measurable (fun z : (T × ℝ) × ℝ => transform (κ z.1.1) z.1.2 z.2) :=
    measurable_kernel_transform κ
  exact hm.comp ((hY.prodMk hX).prodMk hV)

/-- Arbitrary forecast-origin information, without a countable-generation
assumption on that sigma algebra. Freshness is independence of the auxiliary
uniform from the sigma algebra generated jointly by that information and X. -/
def originKernel (information : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (X : Ω → ℝ) :
    @Kernel Ω ℝ information (inferInstance : MeasurableSpace ℝ) :=
  @condDistrib Ω Ω ℝ inferInstance inferInstance inferInstance mΩ information X id P inferInstance

instance originKernel_isMarkov (information : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (X : Ω → ℝ) :
    @IsMarkovKernel Ω ℝ information inferInstance (originKernel (mΩ := mΩ) information P X) := by
  unfold originKernel
  infer_instance

theorem conditionalLaw_randomizedCDF_subsigma
    (information : MeasurableSpace Ω) (hi : information ≤ mΩ)
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P] (X V : Ω → ℝ)
    (hX : @Measurable Ω ℝ mΩ inferInstance X) (hV : @Measurable Ω ℝ mΩ inferInstance V)
    (fresh : @IndepFun Ω (Ω × ℝ) ℝ mΩ
      (information.prod (inferInstance : MeasurableSpace ℝ)) inferInstance
      (fun ω => (ω, X ω)) V P)
    (uniform : @Measure.map Ω ℝ mΩ inferInstance V P = uniformLaw) :
    @ConditionalLaw Ω ℝ mΩ inferInstance P information
      (fun ω => transform (originKernel (mΩ := mΩ) information P X ω) (X ω) (V ω))
      uniformLaw := by
  have hid : @Measurable Ω Ω mΩ information id := fun A hA => hi A hA
  have h := @conditionalLaw_randomizedCDF Ω information Ω mΩ P _ X id V
    hX hid hV fresh uniform
  simpa only [MeasurableSpace.comap_id] using h

theorem randomizedCDF_map (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : Ω → T) (V : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hV : Measurable V)
    (fresh : IndepFun (fun ω => (Y ω, X ω)) V P)
    (uniform : P.map V = uniformLaw) :
    P.map (fun ω => transform (condDistrib X Y P (Y ω)) (X ω) (V ω)) = uniformLaw :=
  (conditionalLaw_randomizedCDF P X Y V hX hY hV fresh uniform).map_eq
    (measurable_randomizedCDF P X Y V hX hY hV)

set_option maxHeartbeats 800000 in
-- Measurability compares kernel maps whose domain uses two filtration sigma algebras.
/-- The corrected thesis's horizon-spaced conclusion, now derived from actual
conditional CDFs and fresh uniforms. Only the raw outcomes and uniforms are
assumed to be observed by origin plus horizon. -/
theorem horizon_spaced_randomizedCDF
    (P : Measure Ω) [IsProbabilityMeasure P] (information : Filtration ℕ mΩ)
    (X V : ℕ → Ω → ℝ) (horizon : ℕ) (hh : 0 < horizon)
    (observedX : ∀ n, Measurable[information (n + horizon)] (X n))
    (observedV : ∀ n, Measurable[information (n + horizon)] (V n))
    (fresh : ∀ n, @IndepFun Ω (Ω × ℝ) ℝ mΩ
      ((information n).prod (inferInstance : MeasurableSpace ℝ)) inferInstance
      (fun ω => (ω, X n ω)) (V n) P)
    (uniform : ∀ n, P.map (V n) = uniformLaw) (residue : ℕ) :
    let U : ℕ → Ω → ℝ := fun n ω =>
      transform (originKernel (information n) P (X n) ω) (X n ω) (V n ω)
    iIndepFun (fun k => U (residue + k * horizon)) P ∧
      ∀ k, P.map (U (residue + k * horizon)) = uniformLaw := by
  let U : ℕ → Ω → ℝ := fun n ω =>
    transform (originKernel (information n) P (X n) ω) (X n ω) (V n ω)
  change iIndepFun (fun k => U (residue + k * horizon)) P ∧
    ∀ k, P.map (U (residue + k * horizon)) = uniformLaw
  have hX (n : ℕ) : Measurable (X n) := (observedX n).mono (information.le _) le_rfl
  have hV (n : ℕ) : Measurable (V n) := (observedV n).mono (information.le _) le_rfl
  have observedU (n : ℕ) : Measurable[information (n + horizon)] (U n) := by
    let κ : @Kernel Ω ℝ (information n) inferInstance := originKernel (information n) P (X n)
    have hid : @Measurable Ω Ω (information (n + horizon)) (information n) id :=
      fun A hA => information.mono (Nat.le_add_right n horizon) A hA
    have hm := @measurable_kernel_transform Ω (information n) κ inferInstance
    exact hm.comp ((hid.prodMk (observedX n)).prodMk (observedV n))
  exact horizon_spaced_uniform P information U horizon hh observedU
    (fun n => conditionalLaw_randomizedCDF_subsigma (information n) (information.le n)
      P (X n) (V n) (hX n) (hV n) (fresh n) (uniform n)) residue

end Thesis.Foundations.Research.RandomizedPIT
