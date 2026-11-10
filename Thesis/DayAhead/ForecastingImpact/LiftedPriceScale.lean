import Thesis.DayAhead.PriceCurveAnalysis.PriceScale
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # The source's genuine infinite-dimensional lifted price transform

The carrier is L² of Euclidean two-vectors. Both maps respect almost-everywhere
equality. The nonlinear inverse is defined only on its stated L² domain.
-/

noncomputable section
namespace Thesis.DayAhead.LiftedPriceScale

open MeasureTheory Filter
open scoped ENNReal BigOperators
open PriceScale

abbrev Point := EuclideanSpace ℝ (Fin 2)

def pointInverse (c : ℝ) (v : Point) : Point :=
  WithLp.toLp 2 (fun i ↦ if i = 0 then v i else inverse c (v i))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The source's inverse domain, expressed using genuine L² membership. -/
def InverseDomain (c : ℝ) :=
  {f : Ω →₂[μ] Point // MemLp (fun x ↦ pointInverse c (f x)) 2 μ}

theorem inverseDomain_iff (c : ℝ) (f : Ω →₂[μ] Point) :
    MemLp (fun x ↦ pointInverse c (f x)) 2 μ ↔
      MemLp (fun x ↦ inverse c (f x 1)) 2 μ := by
  constructor
  · intro h
    simpa [pointInverse, PiLp.toLp_apply] using h.eval_piLp 1
  · intro h
    apply MemLp.of_eval_piLp
    intro i
    fin_cases i
    · simpa [pointInverse, PiLp.toLp_apply] using (Lp.memLp f).eval_piLp 0
    · simpa [pointInverse, PiLp.toLp_apply] using h

def coordinate (i : Fin 2) : (Ω →₂[μ] Point) →L[ℝ] (Ω →₂[μ] ℝ) :=
  (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i).compLpL 2 μ

theorem coordinate_ae (i : Fin 2) (f : Ω →₂[μ] Point) :
    ⇑(coordinate i f) =ᵐ[μ] fun x ↦ f x i :=
  ContinuousLinearMap.coeFn_compLp _ _

end Thesis.DayAhead.LiftedPriceScale
