import Thesis.DayAhead.ForecastingImpact.Shapley
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! # A well-defined squared-loss SAGE game

Forecasting chapter, lines 565–577. This construction requires square
integrability of both the response and full prediction. Its loss functions
carry integrability proofs, so infinite-risk subtraction is excluded. The
local attribution endpoint identities distinguish chosen pointwise versions
from arbitrary versions that agree almost surely.
-/

noncomputable section
namespace Thesis.DayAhead.SAGE

open MeasureTheory Finset
open scoped BigOperators

variable {Ω α H : Type*} [MeasurableSpace Ω] [DecidableEq α]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Zero padding is an injective encoding of the retained coordinate vector. -/
def maskedPredictor (X : Ω → α → ℝ) (S : Finset α) (ω : Ω) (i : α) : ℝ :=
  if i ∈ S then X ω i else 0

abbrev information (X : Ω → α → ℝ) (S : Finset α) : MeasurableSpace Ω :=
  MeasurableSpace.comap (maskedPredictor X S) inferInstance

theorem information_le {X : Ω → α → ℝ} (hX : Measurable X) (S : Finset α) :
    information X S ≤ (inferInstance : MeasurableSpace Ω) := by
  apply measurable_iff_comap_le.mp
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ S
  · simpa only [maskedPredictor, if_pos hi] using (measurable_pi_apply i).comp hX
  · simpa only [maskedPredictor, if_neg hi] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))

omit [MeasurableSpace Ω] in
theorem information_empty (X : Ω → α → ℝ) : information X ∅ = ⊥ := by
  have h : maskedPredictor X ∅ = fun _ => (0 : α → ℝ) := by
    funext ω i
    simp [maskedPredictor]
  simp only [information, h, MeasurableSpace.comap_const]

omit [MeasurableSpace Ω] in
theorem information_full [Fintype α] (X : Ω → α → ℝ) :
    information X univ = MeasurableSpace.comap X inferInstance := by
  have h : maskedPredictor X univ = X := by funext ω i; simp [maskedPredictor]
  rw [information, h]

omit [MeasurableSpace Ω] in
/-- Zero padding generates exactly the sigma-algebra of the coordinate projection. -/
theorem information_eq_projection (X : Ω → α → ℝ) (S : Finset α) :
    information X S = MeasurableSpace.comap (fun ω => fun i : S => X ω i) inferInstance := by
  apply le_antisymm
  · apply measurable_iff_comap_le.mp
    letI : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω => fun i : S => X ω i) inferInstance
    have hr : Measurable (fun ω => fun i : S => X ω i) := measurable_iff_comap_le.mpr le_rfl
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ S
    · simpa only [maskedPredictor, if_pos hi] using (measurable_pi_apply (⟨i, hi⟩ : S)).comp hr
    · simpa only [maskedPredictor, if_neg hi] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  · apply measurable_iff_comap_le.mp
    letI : MeasurableSpace Ω := information X S
    have hm : Measurable (maskedPredictor X S) := measurable_iff_comap_le.mpr le_rfl
    apply measurable_pi_lambda
    intro i
    simpa only [Function.comp_def, maskedPredictor, if_pos i.property] using
      (measurable_pi_apply i.val).comp hm

def conditionalMean (μ : Measure Ω) (F : Ω → H) (X : Ω → α → ℝ) (S : Finset α) : Ω → H :=
  μ[F | information X S]

theorem conditionalMean_empty (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → H) (X : Ω → α → ℝ) :
    conditionalMean μ F X ∅ = fun _ => ∫ ω, F ω ∂μ := by
  simp only [conditionalMean, information_empty, condExp_bot]

theorem conditionalMean_memLp (μ : Measure Ω) {F : Ω → H}
    (hF : MemLp F 2 μ) (X : Ω → α → ℝ) (S : Finset α) :
    MemLp (conditionalMean μ F X S) 2 μ := hF.condExp

/-- This is a specific full-information version. Arbitrary versions agree only almost surely. -/
theorem conditionalMean_full [Fintype α] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → α → ℝ} (hX : Measurable X) {f : (α → ℝ) → H} (hf : Measurable f)
    (hF : Integrable (fun ω => f (X ω)) μ) :
    conditionalMean μ (fun ω => f (X ω)) X univ = fun ω => f (X ω) := by
  have hm := information_le hX univ
  have ha : StronglyMeasurable[information X univ] (fun ω => f (X ω)) := by
    letI : MeasurableSpace Ω := information X univ
    have hXm : Measurable X := measurable_iff_comap_le.mpr (information_full X).ge
    exact (hf.comp hXm).stronglyMeasurable
  exact condExp_of_stronglyMeasurable hm ha hF

/-- The retained loss is a genuinely integrable function, not just a totalized integral. -/
def conditionalLoss (μ : Measure Ω) {Y F : Ω → H} (hY : MemLp Y 2 μ) (hF : MemLp F 2 μ)
    (X : Ω → α → ℝ) (S : Finset α) : {g : Ω → ℝ // Integrable g μ} :=
  ⟨fun ω => ‖Y ω - conditionalMean μ F X S ω‖ ^ 2,
    (hY.sub (conditionalMean_memLp μ hF X S)).integrable_norm_pow (by decide)⟩

def risk (μ : Measure Ω) {Y F : Ω → H} (hY : MemLp Y 2 μ) (hF : MemLp F 2 μ)
    (X : Ω → α → ℝ) (S : Finset α) : ℝ :=
  ∫ ω, (conditionalLoss μ hY hF X S).1 ω ∂μ

def lossGame (μ : Measure Ω) {Y F : Ω → H} (hY : MemLp Y 2 μ) (hF : MemLp F 2 μ)
    (X : Ω → α → ℝ) (S : Finset α) : ℝ :=
  risk μ hY hF X ∅ - risk μ hY hF X S

theorem risk_nonneg (μ : Measure Ω) {Y F : Ω → H} (hY : MemLp Y 2 μ) (hF : MemLp F 2 μ)
    (X : Ω → α → ℝ) (S : Finset α) : 0 ≤ risk μ hY hF X S :=
  integral_nonneg fun _ => sq_nonneg _

theorem lossGame_empty (μ : Measure Ω) {Y F : Ω → H}
    (hY : MemLp Y 2 μ) (hF : MemLp F 2 μ) (X : Ω → α → ℝ) :
    lossGame μ hY hF X ∅ = 0 := sub_self _

theorem risk_empty (μ : Measure Ω) [IsProbabilityMeasure μ] {Y F : Ω → H}
    (hY : MemLp Y 2 μ) (hF : MemLp F 2 μ) (X : Ω → α → ℝ) :
    risk μ hY hF X ∅ = ∫ ω, ‖Y ω - ∫ u, F u ∂μ‖ ^ 2 ∂μ := by
  simp only [risk, conditionalLoss, conditionalMean_empty]

theorem risk_full [Fintype α] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → H} (hY : MemLp Y 2 μ) {X : Ω → α → ℝ} (hX : Measurable X)
    {f : (α → ℝ) → H} (hf : Measurable f) (hF : MemLp (fun ω => f (X ω)) 2 μ) :
    risk μ hY hF X univ = ∫ ω, ‖Y ω - f (X ω)‖ ^ 2 ∂μ := by
  simp only [risk, conditionalLoss,
    conditionalMean_full μ hX hf (hF.integrable (by norm_num))]

end Thesis.DayAhead.SAGE
