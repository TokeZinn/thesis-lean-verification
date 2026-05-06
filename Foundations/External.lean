import Foundations.Stochastic.PointProcesses

/-!
# External Background Results

This module is reserved for cited background results that are not yet available
in mathlib in the form needed by the thesis formalization.

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

External reference note: mathlib provides the Lévy-Prokhorov edistance and
the corresponding topology theorem for probability measures. The thesis uses
the standard finite-measure version from the point-process literature: the
original metrizability theorem of Prokhorov
(`prokhorov1956convergence`), the point-process presentation in
Daley--Vere-Jones (`daley2003introduction`), and Billingsley's convergence
text (`billingsley2013convergence`). We externalize precisely the
finite-measure metrizability clause needed to align the manuscript's
Prokhorov topology with mathlib's weak topology on `FiniteMeasure`.

Lean strategy / thesis relation note: the formal statement uses mathlib's `MetricSpace`,
`CompleteSpace`, `TopologicalSpace.SeparableSpace`, and `BorelSpace`
typeclasses for the Polish Borel hypotheses, `WeakConvergesFiniteMeasures`
for the thesis' bounded-continuous-test-function topology, and
`ProkhorovConvergesFiniteMeasures` for the metric convergence statement.
The Prokhorov distance `ρ` itself, the metric carrier
`ProkhorovFiniteMeasures X`, and the theorem identifying its distance with
`ρ` are formalized in `Stochastic.PointProcesses`; this external axiom records
only the cited metrizability theorem. It is deliberately stated with Polish
hypotheses, so it is narrower than the thesis' displayed item (i) if that item
is read without the theorem's later complete/separable assumptions.
-/
axiom finiteMeasure_prokhorov_metrizes_weakConvergence_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    {μ : ℕ → FiniteMeasures X} {ν : FiniteMeasures X} :
    WeakConvergesFiniteMeasures μ ν ↔
      ProkhorovConvergesFiniteMeasures μ ν

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: complete/separable clause for `\mathcal{M}(X)`.

Informal statement: if `X` is Polish, then the finite-measure space
`(\mathcal{M}(X),ρ)` is complete.

External reference note: this is the finite-measure Polish-space clause of the
same cited Prokhorov theorem used above; see Prokhorov
(`prokhorov1956convergence`), Daley--Vere-Jones
(`daley2003introduction`), and Billingsley
(`billingsley2013convergence`). Mathlib supplies the Lévy-Prokhorov metric and
related Prokhorov compactness machinery, but not this exact global
completeness instance for finite measures in the form needed here.

Lean strategy / thesis relation note: the formal carrier is `ProkhorovFiniteMeasures X`, the
`LevyProkhorov` metric synonym for `FiniteMeasures X`, defined in
`Stochastic.PointProcesses`. Thus the metric-space construction is not an
external assumption here; only this global completeness theorem is
externalized.
-/
axiom prokhorovFiniteMeasures_complete_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    CompleteSpace (ProkhorovFiniteMeasures X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: complete/separable clause for `\mathcal{M}(X)`.

Informal statement: if `X` is Polish, then the finite-measure space
`(\mathcal{M}(X),ρ)` is separable.

External reference note: same cited finite-measure Prokhorov theorem as above.
-/
axiom prokhorovFiniteMeasures_separable_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (ProkhorovFiniteMeasures X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: complete/separable clause for `\mathcal{N}(X)`.

Informal statement: if `X` is Polish, then the finite integer-valued measure
space `(\mathcal{N}(X),ρ)` is complete.

External reference note: this is the integer-valued subspace clause stated in
the thesis after the finite-measure Prokhorov theorem. It is background point-
process theory rather than a thesis contribution, so the formalization records
it as a cited external theorem.

Lean strategy / thesis relation note: the formal carrier is the subtype
`ProkhorovFiniteIntegerMeasures X` of the metric finite-measure space.
-/
axiom prokhorovFiniteIntegerMeasures_complete_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    CompleteSpace (ProkhorovFiniteIntegerMeasures X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: complete/separable clause for `\mathcal{N}(X)`.

Informal statement: if `X` is Polish, then the finite integer-valued measure
space `(\mathcal{N}(X),ρ)` is separable.

External reference note: same cited point-process/Prokhorov background theorem
as above.
-/
axiom prokhorovFiniteIntegerMeasures_separable_polish
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (ProkhorovFiniteIntegerMeasures X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: full external summary of
`thm:prokhorov-metric-weak-convergence-polish`.

Informal statement: under Polish Borel hypotheses, the Prokhorov metric
metrizes weak convergence of finite measures, and the Prokhorov finite-measure
and finite-integer-measure spaces are complete and separable.

Lean strategy / thesis strategy note: the Prokhorov distance definition, metric carrier, and
distance-identification theorem are in `Stochastic.PointProcesses`. The five
large background conclusions are the cited axioms immediately above; this
wrapper records the theorem as one audit-friendly Lean declaration while
keeping each external dependency separately named.
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

External reference note: this is standard point-process/random-measure
background rather than a thesis contribution. It is the finite version of the
usual representation of integer-valued random measures as counting measures
with multiplicities; see for example Kallenberg, *Random Measures, Theory and
Applications*, and Daley--Vere-Jones, *An Introduction to the Theory of Point
Processes*. This existence axiom records finite support, positive integer
weights, injective atom list, and exact equality with the finite measure. The
uniqueness-up-to-permutation clause is recorded separately below so each
external dependency remains independently named.

Lean strategy / thesis relation note: `StandardBorelSpace X` is mathlib's measurable-space analogue
of the thesis' standard Borel hypothesis. The conclusion is the previously
defined `AtomicDecomposition`, so the external theorem is aligned with the
formal target used in `prop:tuple-measure-surjective`.
-/
axiom finiteIntegerMeasure_atomicDecomposition
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : FiniteIntegerMeasures X) :
    AtomicDecomposition μ

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: uniqueness clause of `thm:sufficient-decomposition`.

Informal statement: two finite atomic decompositions of the same finite
integer-valued measure have the same number of atoms, and after reindexing one
finite atom list by a permutation, the atoms and multiplicities agree.

External reference note: this is the uniqueness half of the same standard
atomic-decomposition theorem cited above. It is stated as a separate axiom
because downstream proofs only need the existence half, while audit faithfulness
requires the thesis theorem's uniqueness-up-to-permutation clause to be visible.

Lean strategy / thesis strategy note: the thesis treats uniqueness as equality
up to permutation of `{1, ..., κ}`. Lean represents the finite index set as
`Fin d.length`; once the two lengths are equal, `Fin.cast` transports a
permuted index into the second decomposition's domain.
-/
axiom finiteIntegerMeasure_atomicDecomposition_unique_up_to_permutation
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    {μ : FiniteIntegerMeasures X} (d e : AtomicDecomposition μ) :
    ∃ length_equality : d.length = e.length,
      ∃ atom_index_permutation : Equiv.Perm (Fin d.length),
        ∀ i : Fin d.length,
          e.atom (Fin.cast length_equality (atom_index_permutation i)) = d.atom i ∧
          e.multiplicity (Fin.cast length_equality (atom_index_permutation i)) =
            d.multiplicity i

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: existence clause of `thm:sufficient-decomposition`.

Informal statement: every finite integer-valued measure on a standard Borel
space admits a finite atomic decomposition with positive integer
multiplicities and distinct atoms.

Lean strategy / thesis strategy note: this is a theorem wrapper around the external axiom
`finiteIntegerMeasure_atomicDecomposition`. The companion uniqueness axiom above
records the remaining clause of the thesis theorem.
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

Original label: full external summary of `thm:sufficient-decomposition`.

Informal statement: every finite integer-valued measure on a standard Borel
space admits an atomic decomposition, and any two such decompositions are the
same after a finite permutation of the atom index set.

Lean strategy / thesis strategy note: the existence and uniqueness clauses are
kept as separate external axioms, then bundled here for trace review so the
Lean audit block mirrors the thesis theorem as a two-part result.
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
