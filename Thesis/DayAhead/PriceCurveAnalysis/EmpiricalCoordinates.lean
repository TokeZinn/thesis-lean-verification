import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveHilbert
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Current empirical scales and causal rolling coordinate operators

These are definitions and analytic identities. Positivity of the observed
sample scales remains a data claim; inverse operators require it explicitly.
-/

noncomputable section
namespace Thesis.DayAhead.EmpiricalCoordinates

open MeasureTheory
open scoped BigOperators
open PriceCurveHilbert

/-- Original label: `defn:empirical-coordinate-scales`. -/
def empiricalMean {ι H : Type*} [AddCommGroup H] [Module ℝ H]
    (s : Finset ι) (Z : ι → H) : H := (s.card : ℝ)⁻¹ • ∑ i ∈ s, Z i

def empiricalScale {ι H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (s : Finset ι) (Z : ι → H) (coordinate : H →L[ℝ] G) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ i ∈ s, ‖coordinate (Z i - empiricalMean s Z)‖

theorem empiricalScale_nonneg {ι H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (s : Finset ι) (Z : ι → H) (coordinate : H →L[ℝ] G) :
    0 ≤ empiricalScale s Z coordinate := by
  unfold empiricalScale
  positivity

def coordinate (i : Fin 2) : PricePair →L[ℝ] ℝ :=
  (if i = 0 then ContinuousLinearMap.fst ℝ ℝ ℝ else ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    pairEquiv.symm.toContinuousLinearMap

def coordinateLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (i : Fin 2) :
    PriceHilbertSpace μ →L[ℝ] Lp ℝ 2 μ := (coordinate i).compLpL 2 μ

def pairScaling (a b : ℝ) : PricePair →L[ℝ] PricePair :=
  pairEquiv.toContinuousLinearMap.comp
    (((a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (b • ContinuousLinearMap.snd ℝ ℝ ℝ)).comp pairEquiv.symm.toContinuousLinearMap)

theorem pairScaling_apply (a b : ℝ) (x : ℝ × ℝ) :
    pairScaling a b (pairEquiv x) = pairEquiv (a * x.1, b * x.2) := by
  change pairEquiv (a * (pairEquiv.symm (pairEquiv x)).1,
    b * (pairEquiv.symm (pairEquiv x)).2) = pairEquiv (a * x.1, b * x.2)
  rw [pairEquiv.symm_apply_apply]

theorem pairScaling_inverse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (x : PricePair) :
    pairScaling a⁻¹ b⁻¹ (pairScaling a b x) = x := by
  obtain ⟨y, rfl⟩ := pairEquiv.surjective x
  simp only [pairScaling_apply]
  congr 1
  ext <;> simp [ha, hb]

/-- Original label: `defn:coordinate-scaling-operators`.
This is an operator on the actual Euclidean-valued L² carrier. -/
def scalingLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (a b : ℝ) :
    PriceHilbertSpace μ →L[ℝ] PriceHilbertSpace μ := (pairScaling a b).compLpL 2 μ

theorem scalingLp_inverse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (f : PriceHilbertSpace μ) :
    scalingLp μ a⁻¹ b⁻¹ (scalingLp μ a b f) = f := by
  apply Lp.ext
  filter_upwards [(pairScaling a b).coeFn_compLpL f,
    (pairScaling a⁻¹ b⁻¹).coeFn_compLpL (scalingLp μ a b f)] with ω hi ho
  calc
    scalingLp μ a⁻¹ b⁻¹ (scalingLp μ a b f) ω =
      pairScaling a⁻¹ b⁻¹ (scalingLp μ a b f ω) := ho
    _ = pairScaling a⁻¹ b⁻¹ (pairScaling a b (f ω)) := congrArg _ hi
    _ = f ω := pairScaling_inverse a b ha hb _

/-- The daily mean squared coordinate norm uses all 24 hours. -/
def dailySquaredScale {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (difference : Fin 24 → H) (coordinate : H →L[ℝ] G) : ℝ :=
  (1 / 24 : ℝ) * ∑ h, ‖coordinate (difference h)‖ ^ 2

def rollingWeight (α : ℝ) (lag : Fin 5) : ℝ := (1 - α) ^ (lag.val + 1)

theorem rollingWeight_pos {α : ℝ} (hα : α < 1) (lag : Fin 5) :
    0 < rollingWeight α lag := pow_pos (sub_pos.mpr hα) _

theorem rolling_denominator_pos {α : ℝ} (hα : α < 1) :
    0 < ∑ lag : Fin 5, rollingWeight α lag :=
  Finset.sum_pos (fun lag _ => rollingWeight_pos hα lag) Finset.univ_nonempty

/-- Original label: `defn:rolling-coordinate-scales`.
Only the five strictly preceding dates enter this formula. At missing dates
the thesis uses the formula only when every referenced observation exists. -/
def rollingSquaredScale (α : ℝ) (dailySquared : ℤ → ℝ) (d : ℤ) : ℝ :=
  (∑ lag : Fin 5, rollingWeight α lag * dailySquared (d - (lag.val + 1))) /
    ∑ lag : Fin 5, rollingWeight α lag

def rollingScale (α : ℝ) (dailySquared : ℤ → ℝ) (d : ℤ) : ℝ :=
  Real.sqrt (rollingSquaredScale α dailySquared d)

theorem rollingSquaredScale_nonneg {α : ℝ} (hα : α < 1)
    (dailySquared : ℤ → ℝ) (hdata : ∀ d, 0 ≤ dailySquared d) (d : ℤ) :
    0 ≤ rollingSquaredScale α dailySquared d := by
  apply div_nonneg _ (rolling_denominator_pos hα).le
  exact Finset.sum_nonneg fun lag _ => mul_nonneg (rollingWeight_pos hα lag).le (hdata _)

end Thesis.DayAhead.EmpiricalCoordinates
