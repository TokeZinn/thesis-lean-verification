import Thesis.Foundations.Stochastic.PointProcessAlignment

/-! # Independence of the measurable enumeration in the permutation kernel -/

noncomputable section
namespace Thesis.Foundations.Stochastic.DoctoralPointProcesses

universe u

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open MarketRepresentation MarketRepresentation.TuplesBasic
open MarketRepresentation.TuplesSorting MarketRepresentation.TuplesMetricTopology
open PointProcesses TupleMeasures PermutedTuples PointProcessAlignment

/-- Original label: `thm:point-process-tuple`.
The entire permutation-average measure is unchanged by reordering its input,
including input tuples with repeated values and the empty tuple. -/
theorem uniformPermutationMeasure_permute {X : Type*}
    [MeasurableSpace (Tuple X)] (x : Tuple X) (σ : FinitePermutation x.length) :
    uniformPermutationMeasure (permute x σ) = uniformPermutationMeasure x := by
  cases x with
  | mk n x =>
    ext B hB
    rw [uniformPermutationMeasure_apply _ hB, uniformPermutationMeasure_apply _ hB]
    change ((Fintype.card (FinitePermutation n) : ℝ≥0∞)⁻¹) *
        ∑ π : FinitePermutation n,
          B.indicator (fun _ => (1 : ℝ≥0∞)) (Sigma.mk n (fun i => x (σ (π i)))) =
      ((Fintype.card (FinitePermutation n) : ℝ≥0∞)⁻¹) *
        ∑ π : FinitePermutation n,
          B.indicator (fun _ => (1 : ℝ≥0∞)) (Sigma.mk n (fun i => x (π i)))
    congr 1
    exact Equiv.sum_comp (Equiv.mulLeft σ)
      (fun π : FinitePermutation n =>
        B.indicator (fun _ => (1 : ℝ≥0∞)) (Sigma.mk n (fun i => x (π i))))

/-- Original label: `thm:point-process-tuple`.
The averaging law depends only on the counting measure, which proves the
source's independence of the selected measurable enumeration. -/
theorem uniformPermutationMeasure_eq_of_countingMeasure_eq {X : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace (Tuple X)]
    {x y : Tuple X} (h : tupleInducedIntegerMeasure x = tupleInducedIntegerMeasure y) :
    uniformPermutationMeasure x = uniformPermutationMeasure y := by
  obtain ⟨σ, rfl⟩ := tupleInducedIntegerMeasure_eq_iff_permutativeEquality.mp h
  exact (uniformPermutationMeasure_permute x σ).symm

/-- Original label: `thm:point-process-tuple`.
Any two representative rules give exactly the same measure for every input. -/
theorem pointProcessTupleMeasure_independent {Ω X : Type u}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace (Tuple X)]
    (ξ : Ω → FiniteIntegerMeasures X) (τ υ : FiniteIntegerMeasures X → Tuple X)
    (hτ : ∀ μ, tupleInducedIntegerMeasure (τ μ) = μ)
    (hυ : ∀ μ, tupleInducedIntegerMeasure (υ μ) = μ) (ω : Ω) :
    pointProcessTupleMeasure ξ τ ω = pointProcessTupleMeasure ξ υ ω :=
  uniformPermutationMeasure_eq_of_countingMeasure_eq ((hτ _).trans (hυ _).symm)

/-- Original label: `thm:point-process-tuple`.
The theorem's clauses, consolidated, for the kernel `K_perm` built from a
point process `ξ` and a measurable enumeration `τ` with `m(τ μ) = μ`
(`lem:measurable-enumeration`), on tuple space with its Borel σ-algebra:

1. `K_perm` is a Markov kernel from `Ω` to `T(X)` (probability measure in
   `B`, measurable in `ω`);
2. the length of the enumerated tuple is the total mass `N(ω) = ξ(ω)(X)`;
3. `K_perm(ω, B) = (1 / N(ω)!) Σ_{σ ∈ P_{N(ω)}} 1_B(τ(ξ(ω)) ∘ σ)`, the
   displayed formula;
4. `K_perm(ω, m⁻¹({ξ(ω)})) = 1`: every reordering induces the same point
   measure (`cor:tuple-induced-measure-permutation-invariant`);
5. `K_perm(ω, ·)` is the uniform distribution on the class
   `(m^π)⁻¹(ξ(ω))`: each tuple of the class has mass `1 / |class|`
   (`prop:finite-equivalence-classes`: every class member is produced by the
   same number of permutations);
6. the kernel does not depend on the choice of the enumeration `τ`.

Each clause is the corresponding named lemma of `TupleMeasures`,
`PointProcessAlignment` and this module; the existence statement
`TupleMeasures.pointProcessTuple_markovKernel` is the special case of (1) for
the enumeration `measurableEnumeration`. -/
theorem pointProcessTuple_kernel_clauses {Ω X : Type u}
    [MeasurableSpace Ω] [MeasurableSpace X] [EMetricSpace X] [MeasurableSingletonClass X]
    (ξ : Ω → FiniteIntegerMeasures X) (hξ : Measurable ξ)
    (τ : FiniteIntegerMeasures X → Tuple X)
    (hτ : @Measurable (FiniteIntegerMeasures X) (Tuple X)
      inferInstance (tupleHausdorffBorel (X := X)) τ)
    (hτm : ∀ μ, tupleInducedIntegerMeasure (τ μ) = μ) :
    letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
    IsMarkovKernel (pointProcessTupleKernel ξ hξ τ hτ) ∧
    (∀ ω, ((τ (ξ ω)).length : ℝ≥0) = (ξ ω).val univ) ∧
    (∀ ω (B : Set (Tuple X)), MeasurableSet B →
      pointProcessTupleKernel ξ hξ τ hτ ω B =
        (((τ (ξ ω)).length.factorial : ℝ≥0∞)⁻¹) *
          ∑ π : FinitePermutation (τ (ξ ω)).length,
            B.indicator (fun _ => (1 : ℝ≥0∞)) (permute (τ (ξ ω)) π)) ∧
    (∀ ω, pointProcessTupleKernel ξ hξ τ hτ ω
      {y | tupleInducedIntegerMeasure y = ξ ω} = 1) ∧
    (∀ ω (y : Tuple X), y ∈ permutativeClass (τ (ξ ω)) →
      pointProcessTupleKernel ξ hξ τ hτ ω {y} =
        ((permutativeClass (τ (ξ ω))).ncard : ℝ≥0∞)⁻¹) ∧
    (∀ (υ : FiniteIntegerMeasures X → Tuple X)
      (hυ : @Measurable (FiniteIntegerMeasures X) (Tuple X)
        inferInstance (tupleHausdorffBorel (X := X)) υ),
      (∀ μ, tupleInducedIntegerMeasure (υ μ) = μ) →
      ∀ ω, pointProcessTupleKernel ξ hξ τ hτ ω = pointProcessTupleKernel ξ hξ υ hυ ω) := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : TopologicalSpace (Tuple X) := PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  haveI : OpensMeasurableSpace (Tuple X) := ⟨le_rfl⟩
  haveI : MeasurableSingletonClass (Tuple X) := inferInstance
  refine ⟨pointProcessTupleKernel_isMarkovKernel ξ hξ τ hτ,
    fun ω => enumeration_length_eq_totalMass τ hτm (ξ ω),
    fun ω B hB => pointProcessTupleKernel_apply_formula ξ hξ τ hτ ω B hB,
    fun ω => ?_, fun ω y hy => ?_, fun υ hυ hυm ω => ?_⟩
  · change uniformPermutationMeasure (τ (ξ ω)) _ = 1
    have hs : {y : Tuple X | tupleInducedIntegerMeasure y = ξ ω} =
        {y | tupleInducedIntegerMeasure y = tupleInducedIntegerMeasure (τ (ξ ω))} := by
      rw [hτm]
    rw [hs]
    exact uniformPermutationMeasure_preserves_countingMeasure (τ (ξ ω))
  · change uniformPermutationMeasure (τ (ξ ω)) {y} = _
    exact uniformPermutationMeasure_singleton_eq_inv_ncard (τ (ξ ω)) y hy
  · exact pointProcessTupleMeasure_independent ξ τ υ hτm hυm ω

end Thesis.Foundations.Stochastic.DoctoralPointProcesses
