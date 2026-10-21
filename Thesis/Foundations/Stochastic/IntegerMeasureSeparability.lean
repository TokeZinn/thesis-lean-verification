import Thesis.Foundations.Stochastic.AtomicDecomposition

/-! # Separability of finite integer measures in the Prokhorov metric

For fixed natural multiplicities, moving every atom by at most a given distance
moves the atomic measure by at most that Prokhorov distance. All integer measures
are covered by countably many such finite-product layers.
-/

noncomputable section

open Set MeasureTheory Topology Metric
open scoped ENNReal NNReal BigOperators

namespace Thesis.Foundations.Stochastic.IntegerMeasureSeparability

open PointProcesses

universe u

variable {X : Type u} [MeasurableSpace X] [PseudoEMetricSpace X]
    [OpensMeasurableSpace X]

def atomicMeasure {n : ℕ} (b : Fin n → ℕ) (x : Fin n → X) :
    ProkhorovFiniteIntegerMeasures X :=
  ⟨LevyProkhorov.ofMeasure (finiteAtomicMeasure x b), finiteAtomicMeasure_integerValued x b⟩

theorem measure_le_thickening {n : ℕ} (b : Fin n → ℕ) {x y : Fin n → X}
    {ε : ℝ≥0∞} (hε : ε < ∞) (hxy : ∀ i, edist (y i) (x i) < ε)
    {B : Set X} (hB : MeasurableSet B) :
    (finiteAtomicMeasure x b : Measure X) B ≤
      (finiteAtomicMeasure y b : Measure X) (thickening ε.toReal B) := by
  rw [finiteAtomicMeasure_toMeasure_apply _ _ hB,
    finiteAtomicMeasure_toMeasure_apply _ _ isOpen_thickening.measurableSet]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x i ∈ B
  · have hy : y i ∈ thickening ε.toReal B := by
      rw [mem_thickening_iff_exists_edist_lt]
      exact ⟨x i, hx, by simpa [ENNReal.ofReal_toReal hε.ne] using hxy i⟩
    simp [hx, hy]
  · simp [hx]

theorem atomicMeasure_lipschitz {n : ℕ} (b : Fin n → ℕ) :
    LipschitzWith 1 (atomicMeasure (X := X) b) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul]
  change levyProkhorovEDist (finiteAtomicMeasure x b : Measure X)
    (finiteAtomicMeasure y b : Measure X) ≤ edist x y
  apply levyProkhorovEDist_le_of_forall
  intro ε B hxy hε hB
  refine ⟨(measure_le_thickening b hε ?_ hB).trans (le_add_right le_rfl),
    (measure_le_thickening b hε ?_ hB).trans (le_add_right le_rfl)⟩
  · intro i
    rw [edist_comm]
    exact (edist_le_pi_edist x y i).trans_lt hxy
  · intro i
    exact (edist_le_pi_edist x y i).trans_lt hxy

/-- Original label: `thm:prokhorov-metric-weak-convergence-polish`.
Separability of the integer-valued subspace follows directly from its atomic
parameterization and does not require finite-measure Prokhorov completeness. -/
theorem separableSpace [StandardBorelSpace X] [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (ProkhorovFiniteIntegerMeasures X) := by
  let F : (Σ n : ℕ, Σ b : Fin n → ℕ, Fin n → X) → ProkhorovFiniteIntegerMeasures X :=
    fun p => atomicMeasure p.2.1 p.2.2
  have hF : Continuous F := by
    apply continuous_sigma
    intro n
    apply continuous_sigma
    intro b
    exact (atomicMeasure_lipschitz b).continuous
  have hsurj : Function.Surjective F := by
    intro μ
    let ν : FiniteIntegerMeasures X := ⟨μ.val.toMeasure, μ.property⟩
    obtain ⟨d⟩ := AtomicDecompositionProof.exists_atomicDecomposition ν
    refine ⟨⟨d.length, d.multiplicity, d.atom⟩, ?_⟩
    apply Subtype.ext
    change LevyProkhorov.ofMeasure (finiteAtomicMeasure d.atom d.multiplicity) = μ.val
    rw [d.represents]
  exact hsurj.denseRange.separableSpace hF

end Thesis.Foundations.Stochastic.IntegerMeasureSeparability
