import Thesis.Foundations.Stochastic.PointProcesses
import Thesis.Foundations.Stochastic.AtomicDecomposition
import Thesis.Foundations.Stochastic.IntegerMeasureSeparability
import Thesis.Foundations.Stochastic.FiniteMeasureProkhorov
import Thesis.Foundations.Stochastic.FiniteMeasureDensity
import Thesis.Foundations.Stochastic.FiniteMeasureCompleteness
import Thesis.Foundations.Stochastic.IntegerMeasureCompleteness

/-!
# Proved Background Results

This module preserves the background-result interfaces used throughout the
formalization. Atomic decomposition, finite- and integer-measure separability
and completeness, and the finite-measure Prokhorov topology theorem are proved
internally. The historical module name is retained for interface compatibility.

Policy for this project:

* first search/adapt mathlib;
* if feasible, prove the result locally;
* otherwise introduce an explicit, citation-bearing axiom here;
* never use placeholder proof terms in compiled theorem declarations.
-/

namespace Thesis
namespace Foundations
namespace External

open Thesis.Foundations.Stochastic.PointProcesses

universe u

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: convergence clause of
`thm:prokhorov-metric-weak-convergence-polish`.

Informal statement: on a Polish Borel space, weak convergence of finite
measures is equivalent to convergence to zero in the Prokhorov metric.

Proof: total mass is 1-Lipschitz in the Prokhorov metric and rescaling is
jointly continuous. Away from zero, normalize and use Mathlib's probability
topology theorem. At zero, total mass controls convergence directly. The
helper establishes an identity homeomorphism and arbitrary-filter convergence;
this wrapper preserves the thesis's sequence formulation and Polish hypotheses.
-/
theorem finiteMeasure_prokhorov_metrizes_weakConvergence_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    {μ : ℕ → FiniteMeasures X} {ν : FiniteMeasures X} :
    WeakConvergesFiniteMeasures μ ν ↔
      ProkhorovConvergesFiniteMeasures μ ν :=
  (Stochastic.FiniteMeasureProkhorov.tendsto_iff (μs := μ) (μ := ν)).symm.trans
    tendsto_iff_dist_tendsto_zero

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: complete/separable clause for `\mathcal{M}(X)`.

Informal statement: if `X` is Polish, then the finite-measure space
`(\mathcal{M}(X),ρ)` is complete.

Proof: finite atomic approximations give uniform finite mass covers for
a Cauchy sequence. Intersections of closed covers at decreasing scales are
compact on the complete base and prove tightness. Bounded total masses and
Mathlib's finite-measure Prokhorov compactness theorem give a weakly
convergent subsequence. The proved topology equivalence and the Cauchy
property give convergence of the whole sequence in the Prokhorov metric.
-/
theorem prokhorovFiniteMeasures_complete_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    CompleteSpace (ProkhorovFiniteMeasures X) :=
  Stochastic.FiniteMeasureCompleteness.completeSpace

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: complete/separable clause for `\mathcal{M}(X)`.

Informal statement: if `X` is Polish, then the finite-measure space
`(\mathcal{M}(X),ρ)` is separable.

Proof: finite atomic measures are dense by a measurable small-diameter
partition and a finite truncation with a small mass tail. Their parameter
spaces form a countable union of separable finite products, and the atomic
maps are continuous. No completeness assumption is used by the helper.
-/
theorem prokhorovFiniteMeasures_separable_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (ProkhorovFiniteMeasures X) :=
  Stochastic.FiniteMeasureDensity.separableSpace

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: complete/separable clause for `\mathcal{N}(X)`.

Informal statement: if `X` is Polish, then the finite integer-valued measure
space `(\mathcal{N}(X),ρ)` is complete.

Proof: a Cauchy sequence is uniformly tight. A common compact set with mass
tail less than one contains every positive integer atom. Bounded total mass
bounds both the number of atoms and their multiplicities. Atomic decompositions
place the whole sequence in a compact image of finitely many finite products
of that compact set. A convergent subsequence and the Cauchy property give
convergence in the integer-valued subspace.
-/
theorem prokhorovFiniteIntegerMeasures_complete_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    CompleteSpace (ProkhorovFiniteIntegerMeasures X) :=
  Stochastic.IntegerMeasureCompleteness.completeSpace

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: complete/separable clause for `\mathcal{N}(X)`.

Informal statement: if `X` is Polish, then the finite integer-valued measure
space `(\mathcal{N}(X),ρ)` is separable.

Proof: fixed natural multiplicities define a Lipschitz map from each finite
product of the base space. The countable union of these separable layers maps
onto every finite integer measure by the proved atomic decomposition.
-/
theorem prokhorovFiniteIntegerMeasures_separable_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (ProkhorovFiniteIntegerMeasures X) :=
  Stochastic.IntegerMeasureSeparability.separableSpace

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: full summary of
`thm:prokhorov-metric-weak-convergence-polish`.

Informal statement: under Polish Borel hypotheses, the Prokhorov metric
metrizes weak convergence of finite measures, and the Prokhorov finite-measure
and finite-integer-measure spaces are complete and separable.

Lean strategy / thesis strategy note: the Prokhorov distance definition, metric carrier, and
distance-identification theorem are in `Stochastic.PointProcesses`.
All clauses, including both completeness conclusions, are proved above.
This wrapper records the theorem as one audit-friendly declaration while
keeping each dependency separately named. Its historical name is retained.
-/
theorem prokhorovMetricWeakConvergencePolish_externalSummary
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    {μ : ℕ → FiniteMeasures X} {ν : FiniteMeasures X} :
    (WeakConvergesFiniteMeasures μ ν ↔
      ProkhorovConvergesFiniteMeasures μ ν) ∧
    CompleteSpace (ProkhorovFiniteMeasures X) ∧
    TopologicalSpace.SeparableSpace (ProkhorovFiniteMeasures X) ∧
    CompleteSpace (ProkhorovFiniteIntegerMeasures X) ∧
    TopologicalSpace.SeparableSpace (ProkhorovFiniteIntegerMeasures X) :=
  ⟨finiteMeasure_prokhorov_metrizes_weakConvergence_polish,
    prokhorovFiniteMeasures_complete_polish,
    prokhorovFiniteMeasures_separable_polish,
    prokhorovFiniteIntegerMeasures_complete_polish,
    prokhorovFiniteIntegerMeasures_separable_polish⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: `thm:sufficient-decomposition`.

Informal statement: on a standard Borel space, every finite integer-valued
measure has a finite atomic representation
`\sum_{k \leq \kappa} β_k δ_{x_k}`, with positive natural multiplicities and
distinct atoms; such representations are unique up to permutation of the finite
atom index set.

Proof note: `AtomicDecompositionProof.exists_atomicDecomposition` proves
that integer-valued mass and outer regularity concentrate the measure on
finitely many positive-mass singletons. Classical choice selects one of the
proved decompositions. This declaration no longer introduces an axiom.

Lean strategy / thesis relation note: `StandardBorelSpace X` is mathlib's measurable-space analogue
of the thesis' standard Borel hypothesis. The conclusion is the previously
defined `AtomicDecomposition`, so the result is aligned with the
formal target used in `prop:tuple-measure-surjective`.
-/
noncomputable def finiteIntegerMeasure_atomicDecomposition
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : FiniteIntegerMeasures X) :
    AtomicDecomposition μ :=
  Classical.choice (Stochastic.AtomicDecompositionProof.exists_atomicDecomposition μ)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: uniqueness clause of `thm:sufficient-decomposition`.

Informal statement: two finite atomic decompositions of the same finite
integer-valued measure have the same number of atoms, and after reindexing one
finite atom list by a permutation, the atoms and multiplicities agree.

Proof note: singleton masses identify corresponding atoms and their weights.
The atom correspondence is a bijection of the finite index sets, hence a
permutation after identifying their cardinalities.

Lean strategy / thesis strategy note: the thesis treats uniqueness as equality
up to permutation of `{1, ..., κ}`. Lean represents the finite index set as
`Fin d.length`; once the two lengths are equal, `Fin.cast` transports a
permuted index into the second decomposition's domain.
-/
theorem finiteIntegerMeasure_atomicDecomposition_unique_up_to_permutation
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    {μ : FiniteIntegerMeasures X} (d e : AtomicDecomposition μ) :
    ∃ length_equality : d.length = e.length,
      ∃ atom_index_permutation : Equiv.Perm (Fin d.length),
        ∀ i : Fin d.length,
          e.atom (Fin.cast length_equality (atom_index_permutation i)) = d.atom i ∧
          e.multiplicity (Fin.cast length_equality (atom_index_permutation i)) =
            d.multiplicity i :=
  Stochastic.AtomicDecompositionProof.unique_up_to_permutation d e

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: existence clause of `thm:sufficient-decomposition`.

Informal statement: every finite integer-valued measure on a standard Borel
space admits a finite atomic decomposition with positive integer
multiplicities and distinct atoms.

Lean strategy / thesis strategy note: existence and uniqueness are both proved
in `Stochastic.AtomicDecompositionProof`; the older interface names are kept
so downstream theorem statements remain stable.
-/
theorem finiteIntegerMeasure_exists_atomicDecomposition
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : FiniteIntegerMeasures X) :
    Nonempty (AtomicDecomposition μ) :=
  ⟨finiteIntegerMeasure_atomicDecomposition μ⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: full checked summary of `thm:sufficient-decomposition`.

Informal statement: every finite integer-valued measure on a standard Borel
space admits an atomic decomposition, and any two such decompositions are the
same after a finite permutation of the atom index set.

Lean strategy / thesis strategy note: the proved existence and uniqueness
clauses are bundled here for trace review. The historical declaration name is
retained, but this theorem no longer depends on a project-specific axiom.
-/
theorem finiteIntegerMeasure_atomicDecomposition_externalSummary
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : FiniteIntegerMeasures X) :
    Nonempty (AtomicDecomposition μ) ∧
      ∀ d e : AtomicDecomposition μ,
        ∃ length_equality : d.length = e.length,
          ∃ atom_index_permutation : Equiv.Perm (Fin d.length),
            ∀ i : Fin d.length,
              e.atom (Fin.cast length_equality (atom_index_permutation i)) =
                d.atom i ∧
              e.multiplicity (Fin.cast length_equality (atom_index_permutation i)) =
                d.multiplicity i := by
  exact ⟨finiteIntegerMeasure_exists_atomicDecomposition μ,
    fun d e => finiteIntegerMeasure_atomicDecomposition_unique_up_to_permutation d e⟩

end External
end Foundations
end Thesis
