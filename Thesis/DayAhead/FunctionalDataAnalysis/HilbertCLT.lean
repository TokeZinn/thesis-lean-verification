import Thesis.DayAhead.FunctionalDataAnalysis.HilbertCLTInfinite

namespace Thesis.DayAhead.LimitTheorems

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

universe u

/--
Thesis source:
`2 - day-ahead/3_functional_data_analysis.tex`, central-limit clause of
Theorem `thm:lln-clt-mean`.

Original label: `thm:lln-clt-mean`.

The complete separable Hilbert-space theorem follows from uniform tightness,
scalar projection CLTs, and uniqueness of the Gaussian characteristic
function. No project-specific axiom is used. -/
theorem hilbert_central_limit
    {Ω : Type u} {H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∃ ν : ProbabilityMeasure H,
      IsGaussian (ν : Measure H) ∧
      FunctionalData.hilbertExpectation (ν : Measure H) id = 0 ∧
      FunctionalData.covarianceOperator (ν : Measure H) id =
        FunctionalData.covarianceOperator μ (X 0) ∧
      TendstoInDistribution
        (normalizedHilbertSum μ X) atTop id (fun _ : ℕ => μ)
          (ν : Measure H) := by
  exact separable_hilbert_central_limit μ X hX hindep hident

end Thesis.DayAhead.LimitTheorems
