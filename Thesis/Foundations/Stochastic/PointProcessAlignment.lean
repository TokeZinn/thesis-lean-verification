import Thesis.Context.ThesisContext
import Thesis.Foundations.Stochastic.MatchingTuples
import Thesis.Foundations.Stochastic.FiniteMeasureBorel

/-! Exact partition, metric carriers, and sampling laws for the point-process chapter. -/

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal BigOperators

namespace Thesis.Foundations.Stochastic.PointProcessAlignment

open PointProcesses TupleMeasures PermutedTuples MatchingTuples
open MarketRepresentation MarketRepresentation.TuplesBasic
open MarketRepresentation.TuplesMetricTopology

universe u v

/-- Original label: `lem:disintegration-lemma`.
All four conclusions, including nonempty blocks, their strict maximum-distance
bound, and exact coverage of the nearby measure's atoms. -/
theorem atomicDecomposition_disintegration_full {X : Type u}
    [MeasurableSpace X] [EMetricSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X] {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hεγ : ε < atomicDecompositionSeparationGamma dξ)
    (hρ : prokhorovEDistance ξ.val η.val < ε) :
    (∀ k, dξ.multiplicity k =
      ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε, dη.multiplicity l) ∧
    (∀ k k', k ≠ k' → Disjoint (nearbyAtomIndices dη (dξ.atom k) ε)
      (nearbyAtomIndices dη (dξ.atom k') ε)) ∧
    (∀ k, (nearbyAtomIndices dη (dξ.atom k) ε).Nonempty ∧
      (nearbyAtomIndices dη (dξ.atom k) ε).sup
        (fun l => edist (dξ.atom k) (dη.atom l)) < ε) ∧
    (∀ l, ∃! k, l ∈ nearbyAtomIndices dη (dξ.atom k) ε) := by
  classical
  obtain ⟨hcount, hdisj, hnear⟩ :=
    atomicDecomposition_disintegration_of_lt_separationGamma dξ dη hε hεγ hρ
  have htotal := atomicDecomposition_totalMultiplicity_eq_of_prokhorovEDistance_lt_one
    dξ dη (hρ.trans (hεγ.trans_le (atomicDecompositionSeparationGamma_le_one dξ)))
  refine ⟨hcount, hdisj, fun k => ⟨?_, ?_⟩,
    nearbyAtomIndices_unique_cover_of_disintegration dξ dη hcount hdisj htotal⟩
  · by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    have hc := hcount k
    rw [hz, Finset.sum_empty] at hc
    exact (Nat.ne_of_gt (dξ.multiplicity_pos k)) hc
  · exact (Finset.sup_lt_iff hε).mpr (fun l hl => hnear k l hl)

/-- Original label: `thm:sufficient-decomposition`.
For at most one atom, uniqueness needs no reordering at all. -/
theorem atomicDecomposition_unique_of_length_le_one {X : Type u}
    [MeasurableSpace X] [StandardBorelSpace X] {μ : FiniteIntegerMeasures X}
    (d e : AtomicDecomposition μ) (hd : d.length ≤ 1) :
    ∃ hlen : d.length = e.length, ∀ i,
      e.atom (Fin.cast hlen i) = d.atom i ∧
        e.multiplicity (Fin.cast hlen i) = d.multiplicity i := by
  obtain ⟨hlen, σ, hσ⟩ :=
    AtomicDecompositionProof.unique_up_to_permutation d e
  refine ⟨hlen, fun i => ?_⟩
  have hi : σ i = i := Fin.ext (by have h1 := (σ i).isLt; have h2 := i.isLt; omega)
  simpa [hi] using hσ i

def fromProkhorovInteger {X : Type u} [MeasurableSpace X]
    (μ : ProkhorovFiniteIntegerMeasures X) : FiniteIntegerMeasures X :=
  ⟨μ.val.toMeasure, μ.property⟩

def toProkhorovInteger {X : Type u} [MeasurableSpace X]
    (μ : FiniteIntegerMeasures X) : ProkhorovFiniteIntegerMeasures X :=
  ⟨LevyProkhorov.ofMeasure μ.val, μ.property⟩

@[simp] theorem from_toProkhorovInteger {X : Type u} [MeasurableSpace X]
    (μ : FiniteIntegerMeasures X) : fromProkhorovInteger (toProkhorovInteger μ) = μ := rfl

@[simp] theorem to_fromProkhorovInteger {X : Type u} [MeasurableSpace X]
    (μ : ProkhorovFiniteIntegerMeasures X) : toProkhorovInteger (fromProkhorovInteger μ) = μ := rfl

theorem prokhorovInteger_edist_eq {X : Type u} [MeasurableSpace X]
    [EMetricSpace X] [OpensMeasurableSpace X]
    (μ ν : ProkhorovFiniteIntegerMeasures X) :
    edist μ ν = prokhorovEDistance (fromProkhorovInteger μ).val
      (fromProkhorovInteger ν).val := rfl

/-- Original label: `thm:integer-measures-tuples-homeomorphic`.
An actual homeomorphism with the current matching metric on the quotient and
the Prokhorov metric on finite integer measures. -/
def matchingIntegerMeasuresHomeomorph {X : Type u}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    letI := matchingMetricSpace X
    letI : TopologicalSpace (PermutedTupleQuotientSpace X) :=
      (matchingMetricSpace X).toUniformSpace.toTopologicalSpace
    PermutedTupleQuotientSpace X ≃ₜ ProkhorovFiniteIntegerMeasures X := by
  haveI : StandardBorelSpace X := by
    letI := Preliminary.BoundedMetric.truncatedMetricSpace X
    infer_instance
  let H := integerMeasuresPermutedTuples_homeomorphismData (X := X)
  letI := matchingMetricSpace X
  letI : TopologicalSpace (PermutedTupleQuotientSpace X) :=
    (matchingMetricSpace X).toUniformSpace.toTopologicalSpace
  refine {
    toFun := fun q => toProkhorovInteger (permutedTupleInducedIntegerMeasure q)
    invFun := fun μ => inversePermutedTupleMeasure (fromProkhorovInteger μ)
    left_inv := fun q => inversePermutedTupleMeasure_permutedTupleInducedIntegerMeasure q
    right_inv := fun μ => ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · change toProkhorovInteger
      (permutedTupleInducedIntegerMeasure (inversePermutedTupleMeasure _)) = μ
    rw [permutedTupleInducedIntegerMeasure_inversePermutedTupleMeasure]
    rfl
  · rw [continuous_iff_continuousAt]
    intro q
    rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := H.forward_epsilon_delta_at q ε hε
    -- Truncation preserves the old uniformity, so its epsilon criterion applies.
    refine ⟨δ, hδ, fun r hr => ?_⟩
    rw [prokhorovInteger_edist_eq]
    simpa [H, fromProkhorovInteger, toProkhorovInteger, prokhorovEDistance,
      levyProkhorovEDist_comm] using hclose r (by simpa [edist_comm] using hr)
  · rw [continuous_iff_continuousAt]
    intro μ
    rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := H.inverse_epsilon_delta_at (fromProkhorovInteger μ) ε hε
    refine ⟨δ, hδ, fun ν hν => ?_⟩
    have hraw := hclose (fromProkhorovInteger ν)
      (by simpa [prokhorovInteger_edist_eq, prokhorovEDistance,
        levyProkhorovEDist_comm] using hν)
    simpa [H, edist_comm] using hraw

/-- Original label: `prop:permuted-tuple-measure-continuous`.
The induced counting-measure map with the actual current matching topology. -/
theorem continuous_matchingIntegerMeasure {X : Type u}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    letI := matchingMetricSpace X
    letI : TopologicalSpace (PermutedTupleQuotientSpace X) :=
      (matchingMetricSpace X).toUniformSpace.toTopologicalSpace
    Continuous (fun q : PermutedTupleQuotientSpace X =>
      toProkhorovInteger (permutedTupleInducedIntegerMeasure q)) := by
  letI := matchingMetricSpace X
  letI : TopologicalSpace (PermutedTupleQuotientSpace X) :=
    (matchingMetricSpace X).toUniformSpace.toTopologicalSpace
  exact (matchingIntegerMeasuresHomeomorph (X := X)).continuous

/-- Original label: `lem:measurable-enumeration`.
Convert the actual Prokhorov Borel structure to the evaluation measurable structure. -/
theorem measurable_fromProkhorovInteger {X : Type u}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace.SeparableSpace X] :
    @Measurable (ProkhorovFiniteIntegerMeasures X) (FiniteIntegerMeasures X)
      (borel _) inferInstance fromProkhorovInteger := by
  letI : BorelSpace (FiniteMeasure X) := FiniteMeasureBorel.weak_borelSpace
  letI : MeasurableSpace (ProkhorovFiniteMeasures X) := borel _
  letI : BorelSpace (ProkhorovFiniteMeasures X) := ⟨rfl⟩
  letI : MeasurableSpace (ProkhorovFiniteIntegerMeasures X) := borel _
  letI : BorelSpace (ProkhorovFiniteIntegerMeasures X) := ⟨rfl⟩
  have h := (FiniteMeasureProkhorov.finiteMeasureHomeomorph (X := X)).symm.continuous.measurable
  exact (h.comp continuous_subtype_val.measurable).subtype_mk

/-- Original label: `lem:measurable-enumeration`.
The selected tuple measurably represents every measure in the stated metric Borel domain. -/
theorem measurableEnumeration_prokhorovBorel {X : Type u}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    ∃ τ : ProkhorovFiniteIntegerMeasures X → Tuple X,
      @Measurable _ _ (borel _) (tupleHausdorffBorel (X := X)) τ ∧
      ∀ μ, tupleInducedIntegerMeasure (τ μ) = fromProkhorovInteger μ := by
  refine ⟨fun μ => measurableEnumeration (fromProkhorovInteger μ),
    (measurable_measurableEnumeration (X := X)).comp measurable_fromProkhorovInteger, ?_⟩
  exact fun μ => tupleInducedIntegerMeasure_measurableEnumeration _

theorem permute_mul_eq_iff {X : Type u} (x : Tuple X)
    (π σ : FinitePermutation x.length) :
    permute x (π * σ) = permute x σ ↔ permute x π = x := by
  rcases x with ⟨n, x⟩
  constructor
  · intro h
    have hf := eq_of_heq (Sigma.mk.inj h).2
    apply congrArg (Sigma.mk n)
    funext i
    have hh := congrFun hf (σ.symm i)
    change x (π (σ (σ.symm i))) = x (σ (σ.symm i)) at hh
    rw [σ.apply_symm_apply] at hh
    exact hh
  · intro h
    have hf := eq_of_heq (Sigma.mk.inj h).2
    apply congrArg (Sigma.mk n)
    funext i
    exact congrFun hf (σ i)

/-- Original label: `thm:point-process-tuple`.
The actual permutation-average measure assigns the same mass to each tuple
in the orbit, including tuples with repeated entries. -/
theorem uniformPermutationMeasure_singleton_permute {X : Type u}
    [MeasurableSpace (Tuple X)] [MeasurableSingletonClass (Tuple X)]
    (x : Tuple X) (σ : FinitePermutation x.length) :
    uniformPermutationMeasure x {permute x σ} = uniformPermutationMeasure x {x} := by
  classical
  rw [uniformPermutationMeasure_apply x (measurableSet_singleton _),
    uniformPermutationMeasure_apply x (measurableSet_singleton _)]
  congr 1
  have he := Equiv.sum_comp (Equiv.mulRight σ)
    (fun π : FinitePermutation x.length =>
      ({permute x σ} : Set (Tuple X)).indicator (fun _ => (1 : ℝ≥0∞)) (permute x π))
  simpa [Equiv.mulRight, Set.indicator_apply, permute_mul_eq_iff] using he.symm

/-- Original label: `thm:point-process-tuple`.
The complete mass is supported on the finite permutation class. -/
theorem uniformPermutationMeasure_class {X : Type u}
    [MeasurableSpace (Tuple X)] [MeasurableSingletonClass (Tuple X)] (x : Tuple X) :
    uniformPermutationMeasure x (permutativeClass x) = 1 := by
  classical
  rw [uniformPermutationMeasure_apply x (finite_permutativeClass x).measurableSet]
  have hm (π : FinitePermutation x.length) : permute x π ∈ permutativeClass x :=
    ⟨π, rfl⟩
  simp [hm, ENNReal.inv_mul_cancel, Fintype.card_ne_zero]

/-- Original label: `thm:point-process-tuple`.
Every distinct tuple has probability exactly the reciprocal of the orbit size. -/
theorem uniformPermutationMeasure_singleton_eq_inv_ncard {X : Type u}
    [MeasurableSpace (Tuple X)] [MeasurableSingletonClass (Tuple X)]
    (x y : Tuple X) (hy : y ∈ permutativeClass x) :
    uniformPermutationMeasure x {y} = ((permutativeClass x).ncard : ℝ≥0∞)⁻¹ := by
  classical
  have heq (z : Tuple X) (hz : z ∈ permutativeClass x) :
      uniformPermutationMeasure x {z} = uniformPermutationMeasure x {x} := by
    obtain ⟨π, rfl⟩ := hz
    exact uniformPermutationMeasure_singleton_permute x π
  rw [heq y hy]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  let s := (finite_permutativeClass x).toFinset
  have hs : (s : Set (Tuple X)) = permutativeClass x := Set.Finite.coe_toFinset _
  have hcard : s.card = (permutativeClass x).ncard :=
    (Set.ncard_eq_toFinset_card _ (finite_permutativeClass x)).symm
  have hsum := MeasureTheory.sum_measure_singleton (μ := uniformPermutationMeasure x) (s := s)
  rw [hs, uniformPermutationMeasure_class] at hsum
  have hc : (∑ z ∈ s, uniformPermutationMeasure x {z}) =
      (s.card : ℝ≥0∞) * uniformPermutationMeasure x {x} := by
    rw [Finset.sum_congr rfl (fun z hz => heq z (by simpa [← hs] using hz))]
    simp
  rw [hc, hcard, mul_comm] at hsum
  exact hsum

/-- Original label: `thm:point-process-tuple`.
An enumeration's length is exactly the point process's total mass, so the
permutation measure's factorial is the stated `n(ω)!`. -/
theorem enumeration_length_eq_totalMass {X : Type u} [MeasurableSpace X]
    (τ : FiniteIntegerMeasures X → Tuple X)
    (hτ : ∀ μ, tupleInducedIntegerMeasure (τ μ) = μ) (μ : FiniteIntegerMeasures X) :
    ((τ μ).length : ℝ≥0) = μ.val univ := by
  calc
    _ = (tupleInducedIntegerMeasure (τ μ)).val univ :=
      (tupleInducedIntegerMeasure_univ (τ μ)).symm
    _ = μ.val univ := congrArg (fun ν : FiniteIntegerMeasures X => ν.val univ) (hτ μ)

/-- Original label: `thm:point-process-tuple`.
The constructed kernel is the displayed factorial-normalized permutation average. -/
theorem pointProcessTupleKernel_apply_formula {Ω X : Type u}
    [MeasurableSpace Ω] [MeasurableSpace X] [EMetricSpace X]
    (ξ : Ω → FiniteIntegerMeasures X) (hξ : Measurable ξ)
    (τ : FiniteIntegerMeasures X → Tuple X)
    (hτ : @Measurable _ _ inferInstance (tupleHausdorffBorel (X := X)) τ)
    (ω : Ω) (B : Set (Tuple X))
    (hB : @MeasurableSet _ (tupleHausdorffBorel (X := X)) B) :
    (pointProcessTupleKernel ξ hξ τ hτ) ω B =
      (((τ (ξ ω)).length.factorial : ℝ≥0∞)⁻¹) *
        ∑ π : FinitePermutation (τ (ξ ω)).length,
          B.indicator (fun _ => (1 : ℝ≥0∞)) (permute (τ (ξ ω)) π) := by
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  change uniformPermutationMeasure (τ (ξ ω)) B = _
  rw [uniformPermutationMeasure_apply _ hB, uniformPermutationMeasure_card_eq_factorial]

/-- Original label: `thm:point-process-tuple`.
Sampling an order never changes the underlying point measure. -/
theorem uniformPermutationMeasure_preserves_countingMeasure {X : Type u}
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (Tuple X)] [MeasurableSingletonClass (Tuple X)]
    (x : Tuple X) :
    uniformPermutationMeasure x
      {y | tupleInducedIntegerMeasure y = tupleInducedIntegerMeasure x} = 1 := by
  have hs : {y | tupleInducedIntegerMeasure y = tupleInducedIntegerMeasure x} =
      permutativeClass x := by
    ext y
    exact eq_comm.trans tupleInducedIntegerMeasure_eq_iff_permutativeEquality
  rw [hs]
  exact uniformPermutationMeasure_class x

/-- Original label: `thm:point-process-tuple`.
UV006: for the empty event every length-layer term is zero. The corrected source
proof says "at most one nonzero term"; this guards against the old wording. -/
theorem empty_event_all_permutation_layers_zero {X : Type u} (x : Tuple X) (n : ℕ) :
    ((n.factorial : ℝ≥0∞)⁻¹) *
      ∑ π : FinitePermutation n,
        (if x.length = n then (1 : ℝ≥0∞) else 0) *
          (∅ : Set (Tuple X)).indicator (fun _ => (1 : ℝ≥0∞))
            (TuplesMeasurableSorting.permutationMap x ⟨n, π⟩) = 0 := by
  simp

end Thesis.Foundations.Stochastic.PointProcessAlignment
