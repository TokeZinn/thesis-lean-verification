import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space

/-! # Euclidean values for price-curve Hilbert encodings

The ordinary product `ℝ × ℝ` has the maximum norm. Its `L²` space is not
the Euclidean-valued Hilbert space in the thesis. This module explicitly
converts coordinates to `WithLp 2 (ℝ × ℝ)` before taking the `L²` norm.
-/

noncomputable section

namespace Thesis.DayAhead.PriceCurveHilbert

open MeasureTheory

abbrev PricePair := WithLp 2 (ℝ × ℝ)

def pairEquiv : (ℝ × ℝ) ≃L[ℝ] PricePair :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm

@[simp] theorem pairEquiv_apply (x : ℝ × ℝ) : pairEquiv x = WithLp.toLp 2 x := rfl

theorem pricePair_norm_sq (x : PricePair) : ‖x‖ ^ 2 = x.fst ^ 2 + x.snd ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using WithLp.prod_norm_sq_eq_of_L2 x

/-- FA-003: the ordinary pair norm and the Euclidean norm differ. -/
theorem pair_norms_differ :
    ‖((1, 1) : ℝ × ℝ)‖ ^ 2 = 1 ∧ ‖pairEquiv (1, 1)‖ ^ 2 = 2 := by
  constructor
  · norm_num [Prod.norm_def]
  · rw [pricePair_norm_sq]
    norm_num [pairEquiv]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

abbrev PriceHilbertSpace := Lp PricePair 2 μ

/-- The corrected carrier has the required complete Hilbert structure. -/
abbrev priceHilbertSpace_innerProductSpace : InnerProductSpace ℝ (PriceHilbertSpace μ) :=
  inferInstance

theorem priceHilbertSpace_complete : CompleteSpace (PriceHilbertSpace μ) := inferInstance

def liftLp : Lp (ℝ × ℝ) 2 μ →L[ℝ] PriceHilbertSpace μ :=
  pairEquiv.toContinuousLinearMap.compLpL 2 μ

theorem coeFn_liftLp (f : Lp (ℝ × ℝ) 2 μ) :
    liftLp μ f =ᵐ[μ] fun u => pairEquiv (f u) :=
  pairEquiv.toContinuousLinearMap.coeFn_compLpL f

theorem liftLp_injective : Function.Injective (liftLp μ) := by
  intro f g h
  apply Lp.ext
  filter_upwards [coeFn_liftLp μ f, coeFn_liftLp μ g] with u hf hg
  apply pairEquiv.injective
  rw [← hf, ← hg, h]

theorem coeFn_liftLp_toLp {f : Ω → ℝ × ℝ} (hf : MemLp f 2 μ) :
    liftLp μ (hf.toLp f) =ᵐ[μ] fun u => pairEquiv (f u) := by
  filter_upwards [coeFn_liftLp μ (hf.toLp f), hf.coeFn_toLp] with u hu hv
  simpa only [hv] using hu

end Thesis.DayAhead.PriceCurveHilbert
