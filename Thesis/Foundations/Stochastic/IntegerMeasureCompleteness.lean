import Thesis.Foundations.Stochastic.FiniteMeasureCompleteness
import Thesis.Foundations.Stochastic.IntegerMeasureSeparability

/-! # Completeness of finite integer measures

Uniform tightness traps all positive integer atoms in a single compact set:
a mass tail smaller than one must be zero. Bounded total mass also bounds
the number of distinct atoms and every multiplicity. The measures in the
sequence therefore lie in a compact image of finitely many finite products
of that compact set.
-/

noncomputable section

open Set Filter MeasureTheory Topology Metric TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace Thesis.Foundations.Stochastic.IntegerMeasureCompleteness

open PointProcesses FiniteMeasureProkhorov

universe u

variable {X : Type u} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]

def Parameters (N : ℕ) (K : Set X) :=
  Σ n : Fin (N + 1), Σ _b : Fin n.val → Fin (N + 1), Fin n.val → K

instance parametersTopologicalSpace (N : ℕ) (K : Set X) :
    TopologicalSpace (Parameters N K) := inferInstanceAs (TopologicalSpace (Σ n : Fin (N + 1),
      Σ _b : Fin n.val → Fin (N + 1), Fin n.val → K))

instance parametersCompactSpace (N : ℕ) (K : Set X) [CompactSpace K] :
    CompactSpace (Parameters N K) := inferInstanceAs (CompactSpace (Σ n : Fin (N + 1),
      Σ _b : Fin n.val → Fin (N + 1), Fin n.val → K))

def parameterMeasure {N : ℕ} {K : Set X} (p : Parameters N K) :
    ProkhorovFiniteIntegerMeasures X :=
  IntegerMeasureSeparability.atomicMeasure (fun i => (p.2.1 i).val) (fun i => (p.2.2 i).val)

theorem continuous_parameterMeasure (N : ℕ) (K : Set X) :
    Continuous (parameterMeasure (X := X) (N := N) (K := K)) := by
  apply continuous_sigma
  intro n
  apply continuous_sigma
  intro b
  exact (IntegerMeasureSeparability.atomicMeasure_lipschitz (fun i => (b i).val)).continuous.comp
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))

omit [MetricSpace X] [BorelSpace X] in
theorem represents_in_parameters [StandardBorelSpace X] {N : ℕ} {K : Set X}
    (μ : ProkhorovFiniteIntegerMeasures X) (hmass : μ.val.toMeasure.mass ≤ N)
    (htail : (μ.val.toMeasure : Measure X) Kᶜ < 1) :
    ∃ p : Parameters N K, parameterMeasure p = μ := by
  classical
  let ν : FiniteIntegerMeasures X := ⟨μ.val.toMeasure, μ.property⟩
  obtain ⟨d⟩ := AtomicDecompositionProof.exists_atomicDecomposition ν
  have hsum : ∑ i, d.multiplicity i ≤ N := by
    have hmass' : (∑ i, (d.multiplicity i : ℝ≥0)) ≤ N := by
      rw [← finiteAtomicMeasure_univ d.atom d.multiplicity, d.represents]
      exact hmass
    exact_mod_cast hmass'
  have hlength : d.length ≤ N := by
    calc
      d.length = ∑ _ : Fin d.length, 1 := by simp
      _ ≤ ∑ i, d.multiplicity i := Finset.sum_le_sum fun i _ => d.multiplicity_pos i
      _ ≤ N := hsum
  have hweight (i : Fin d.length) : d.multiplicity i ≤ N :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsum
  have hatom (i : Fin d.length) : d.atom i ∈ K := by
    by_contra hi
    have hsingle := atomicDecomposition_toMeasure_singleton d i
    have hle : (ν.val : Measure X) {d.atom i} ≤ (ν.val : Measure X) Kᶜ :=
      measure_mono (singleton_subset_iff.mpr hi)
    rw [hsingle] at hle
    have hpos : (1 : ℝ≥0∞) ≤ d.multiplicity i := by exact_mod_cast d.multiplicity_pos i
    exact (hpos.trans hle).not_gt htail
  refine ⟨⟨⟨d.length, Nat.lt_succ_of_le hlength⟩,
    (fun i => ⟨d.multiplicity i, Nat.lt_succ_of_le (hweight i)⟩),
    (fun i => ⟨d.atom i, hatom i⟩)⟩, ?_⟩
  apply Subtype.ext
  change LevyProkhorov.ofMeasure (finiteAtomicMeasure d.atom d.multiplicity) = μ.val
  rw [d.represents]

/-- Original label: integer-measure completeness clause of
`thm:prokhorov-metric-weak-convergence-polish`. -/
theorem completeSpace [SeparableSpace X] [CompleteSpace X] :
    CompleteSpace (ProkhorovFiniteIntegerMeasures X) := by
  cases isEmpty_or_nonempty X with
  | inl h =>
    haveI : Subsingleton (LP X) := ⟨fun μ ν => by
      cases μ
      cases ν
      congr 1
      ext B
      rw [show B = ∅ from Set.eq_empty_of_isEmpty B]
      simp⟩
    infer_instance
  | inr h =>
    apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    have huval : CauchySeq (fun n => (u n).val) :=
      uniformContinuous_subtype_val.comp_cauchySeq hu
    have hmass := mass_lipschitz.uniformContinuous.comp_cauchySeq huval
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hmass
    obtain ⟨C, hC⟩ := ha.bddAbove_range
    obtain ⟨N, hN⟩ := exists_nat_ge C
    have htight := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (FiniteMeasureCompleteness.cauchySeq_isTight (fun n => (u n).val) huval)
    obtain ⟨K, hK, htail⟩ := htight (1 / 2) (by norm_num)
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hcompact : IsCompact (range (parameterMeasure (X := X) (N := N) (K := K))) :=
      isCompact_range (continuous_parameterMeasure N K)
    have hmem (n : ℕ) : u n ∈ range (parameterMeasure (X := X) (N := N) (K := K)) := by
      exact represents_in_parameters (u n) ((hC (mem_range_self n)).trans hN)
        ((htail _ (mem_range_self n)).trans_lt (by norm_num))
    obtain ⟨ν, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
    exact ⟨ν, tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hlim⟩

end Thesis.Foundations.Stochastic.IntegerMeasureCompleteness
