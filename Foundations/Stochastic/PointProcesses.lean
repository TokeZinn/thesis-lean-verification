import Foundations.MarketClearing.Equilibrium
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Stochastic Markets: Point Processes

Blueprint module for
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Point Processes".

Planned formal content:

* weak convergence;
* Prokhorov metric;
* the atomic-decomposition predicate used by `thm:sufficient-decomposition`;
* `lem:helpful-point-process`;
* `cor:measures-coincide`;
* `lem:disintegration-lemma`.

External-result note: cited Prokhorov/finite-integer-measure facts that are
not available in mathlib are stated in `Foundations.External`, which imports
this module after the relevant target predicates have been defined. In
particular, this file defines the `AtomicDecomposition` object; the universal
standard-Borel existence theorem and the thesis uniqueness-up-to-permutation
clause are supplied externally to avoid an import cycle.
-/

namespace Thesis
namespace Foundations
namespace Stochastic
namespace PointProcesses

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal NNReal

/-! ## Finite Measures and Weak Convergence -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Point Processes", display `eq:finite-measures`.

Original label: `eq:finite-measures`.

Informal statement: `\mathcal{M}(X)` is the space of finite measures on the
measurable space `X`.

Lean strategy / thesis relation note: mathlib already packages this as
`MeasureTheory.FiniteMeasure`. The type is a subtype of `Measure X` carrying the
proof that total mass is finite, and it carries mathlib's weak-convergence
topology when `X` is a Borel topological space.
-/
abbrev FiniteMeasures (X : Type u) [MeasurableSpace X] : Type u :=
  FiniteMeasure X

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Point Processes", display `eq:finite-integer-measures`.

Original label: `eq:finite-integer-measures`.

Informal statement: a finite measure is integer-valued when every measurable
set has mass in `\mathbb{N}_0`.

Lean strategy / thesis relation note: `FiniteMeasure X` evaluates sets in `ℝ≥0`; the Lean predicate
therefore says that each measurable-set value is equal to the coercion of a
natural number.
-/
def IsIntegerValuedFiniteMeasure {X : Type u} [MeasurableSpace X]
    (μ : FiniteMeasures X) : Prop :=
  ∀ B : Set X, MeasurableSet B → ∃ n : ℕ, μ B = n

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
section "Tuples and Point Processes", display `eq:finite-integer-measures`.

Original label: `eq:finite-integer-measures`.

Informal statement: `\mathcal{N}(X)` is the subset of finite measures whose
measurable-set values are natural numbers.
-/
abbrev FiniteIntegerMeasures (X : Type u) [MeasurableSpace X] : Type u :=
  {μ : FiniteMeasures X // IsIntegerValuedFiniteMeasure μ}

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:weak-convergence-finite-measures`.

Original label: `defn:weak-convergence-finite-measures`.

Informal statement: a sequence of finite measures converges weakly if it
converges against every bounded continuous real-valued test function.

Lean strategy / thesis relation note: mathlib defines the topology on `FiniteMeasure X` by weak
convergence. This predicate is the sequence-specialized spelling used in the
thesis; the following theorem identifies it with the displayed integral
condition.
-/
def WeakConvergesFiniteMeasures {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : ℕ → FiniteMeasures X) (ν : FiniteMeasures X) : Prop :=
  Tendsto μ atTop (𝓝 ν)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:weak-convergence-finite-measures`.

Original label: `defn:weak-convergence-finite-measures`.

Informal statement: the Lean weak-convergence topology on finite measures is
equivalent to the thesis' integral convergence condition for every bounded
continuous real-valued function.

Lean strategy / thesis relation note: this is a direct use of mathlib's theorem
`FiniteMeasure.tendsto_iff_forall_integral_tendsto`, so no external axiom is
needed for the definition of weak convergence.
-/
theorem weakConvergesFiniteMeasures_iff_forall_integral_tendsto
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    {μ : ℕ → FiniteMeasures X} {ν : FiniteMeasures X} :
    WeakConvergesFiniteMeasures μ ν ↔
      ∀ f : BoundedContinuousFunction X ℝ,
        Tendsto (fun n : ℕ => ∫ x, f x ∂(μ n : Measure X))
          atTop (𝓝 (∫ x, f x ∂(ν : Measure X))) :=
  FiniteMeasure.tendsto_iff_forall_integral_tendsto

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
display `eq:epsilon-extension`.

Original label: `eq:epsilon-extension`.

Informal statement: the `ε`-extension of a set consists of all points within
distance `< ε` of some point of the set.
-/
def epsilonExtension {X : Type u} [PseudoMetricSpace X]
    (A : Set X) (ε : ℝ) : Set X :=
  {x | ∃ a ∈ A, dist x a < ε}

/-! ## Prokhorov Distance -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: Prokhorov distance `ρ` in
`thm:prokhorov-metric-weak-convergence-polish`.

Informal statement: the Prokhorov extended distance between two finite
measures is the infimum of all radii `ε` for which each measure of a
measurable set is bounded by the other measure of the `ε`-extension, plus
`ε`.

Lean strategy / thesis relation note: mathlib calls this the Lévy-Prokhorov edistance and defines it
using `Metric.thickening`, the same set operation as the thesis'
`ε`-extension. We keep the thesis name `prokhorovEDistance` as a wrapper so
later theorem statements read like the manuscript. The cited external
metrizability/completeness/separability facts are tracked in
`Foundations.External` with references to Prokhorov, Daley--Vere-Jones, and
Billingsley.
-/
noncomputable def prokhorovEDistance {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ ν : FiniteMeasures X) : ℝ≥0∞ :=
  MeasureTheory.levyProkhorovEDist (μ : Measure X) (ν : Measure X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: Prokhorov metric `ρ`.

Informal statement: the real-valued Prokhorov distance on finite measures.

Lean strategy / thesis relation note: because finite measures are finite, mathlib's extended
Lévy-Prokhorov distance is never `∞`; the real-valued version is its
`toReal`, packaged by mathlib as `levyProkhorovDist`.
-/
noncomputable def prokhorovDistance {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ ν : FiniteMeasures X) : ℝ :=
  MeasureTheory.levyProkhorovDist (μ : Measure X) (ν : Measure X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: metric-space carrier `(\mathcal{M}(X),ρ)`.

Informal statement: `\mathcal{M}(X)` equipped with the Prokhorov metric.

Lean strategy / thesis relation note: `FiniteMeasures X` already has mathlib's weak-convergence
topology. The thesis theorem also uses the metric topology generated by
`ρ`, so Lean names the metric version with mathlib's `LevyProkhorov` type
synonym rather than replacing the existing finite-measure topology.
-/
abbrev ProkhorovFiniteMeasures (X : Type u) [MeasurableSpace X] : Type u :=
  MeasureTheory.LevyProkhorov (FiniteMeasures X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: metric-space carrier `(\mathcal{N}(X),ρ)`.

Informal statement: `\mathcal{N}(X)` is the integer-valued finite-measure
subspace of `(\mathcal{M}(X),ρ)`.
-/
abbrev ProkhorovFiniteIntegerMeasures (X : Type u) [MeasurableSpace X] :
    Type u :=
  {μ : ProkhorovFiniteMeasures X // IsIntegerValuedFiniteMeasure μ.toMeasure}

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: Prokhorov metric `ρ`.

Informal statement: the distance on `ProkhorovFiniteMeasures X` is exactly the
previously named thesis Prokhorov distance.
-/
theorem prokhorovFiniteMeasures_dist_eq {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    (μ ν : ProkhorovFiniteMeasures X) :
    dist μ ν = prokhorovDistance μ.toMeasure ν.toMeasure := by
  simpa [ProkhorovFiniteMeasures, prokhorovDistance] using
    MeasureTheory.LevyProkhorov.dist_finiteMeasure_def μ ν

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: finite-valuedness implicit in the Prokhorov metric theorem.

Informal statement: the Prokhorov edistance between finite measures is finite.
-/
theorem prokhorovEDistance_lt_top {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ ν : FiniteMeasures X) :
    prokhorovEDistance μ ν < ∞ := by
  simp [prokhorovEDistance,
    (MeasureTheory.levyProkhorovEDist_lt_top
      (μ := (μ : Measure X)) (ν := (ν : Measure X)))]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:prokhorov-metric-weak-convergence-polish`.

Original label: convergence clause of
`thm:prokhorov-metric-weak-convergence-polish`.

Informal statement: convergence in the Prokhorov metric means the
Prokhorov distances to the limit tend to zero.
-/
def ProkhorovConvergesFiniteMeasures {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ : ℕ → FiniteMeasures X) (ν : FiniteMeasures X) : Prop :=
  Tendsto (fun n : ℕ => prokhorovDistance (μ n) ν) atTop (𝓝 0)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:helpful-point-process`.

Original label: integer rounding step in
`lem:helpful-point-process`.

Informal statement: if two natural-number masses satisfy
`a ≤ b + δ` with `δ < 1`, then actually `a ≤ b`.

Lean strategy / thesis relation note: the thesis uses this as the key discrete step after applying
the Prokhorov inequality. Lean states it for natural numbers embedded in
`ℝ≥0∞`, matching mathlib's measure values.
-/
theorem nat_le_of_ennreal_nat_le_add_lt_one {a b : ℕ} {δ : ℝ≥0∞}
    (hδ : δ < 1) (h : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) + δ) :
    a ≤ b := by
  by_contra hnot
  have hlt : b < a := Nat.lt_of_not_ge hnot
  have hsucc : b + 1 ≤ a := Nat.succ_le_of_lt hlt
  have hsuccE : ((b + 1 : ℕ) : ℝ≥0∞) ≤ (a : ℝ≥0∞) := by
    exact_mod_cast hsucc
  have hle : ((b + 1 : ℕ) : ℝ≥0∞) ≤ (b : ℝ≥0∞) + δ :=
    hsuccE.trans h
  have hbδ_ne_top : (b : ℝ≥0∞) + δ ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨by simp, hδ.ne_top⟩
  have hreal := ENNReal.toReal_mono hbδ_ne_top hle
  have hδreal : δ.toReal < 1 := by
    have h1_ne : (1 : ℝ≥0∞) ≠ ∞ := by simp
    simpa using (ENNReal.toReal_lt_toReal hδ.ne_top h1_ne).2 hδ
  rw [ENNReal.toReal_add (by simp : (b : ℝ≥0∞) ≠ ∞) hδ.ne_top,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hreal
  norm_num at hreal
  nlinarith

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:helpful-point-process`, first displayed implication.

Original label: `eq:lem-helpful-point-process-1`.

Informal statement: if two finite integer-valued measures have Prokhorov
distance less than `ε < 1`, then
`ξ(B) ≤ η(B^ε)` for every measurable `B`.

Lean strategy / thesis relation note: mathlib's `thickening ε.toReal B` is the formal `B^ε`.
The proof follows the thesis: Prokhorov inequality with `+ ε`, then integer
rounding removes the additive error.
-/
theorem helpfulPointProcess_left {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    {ξ η : FiniteIntegerMeasures X} {ε : ℝ≥0∞}
    (_hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε)
    {B : Set X} (hB : MeasurableSet B) :
    (ξ.1 : Measure X) B ≤ (η.1 : Measure X) (thickening ε.toReal B) := by
  have hprox :
      (ξ.1 : Measure X) B ≤
        (η.1 : Measure X) (thickening ε.toReal B) + ε := by
    simpa [prokhorovEDistance] using
      (MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt
        (μ := (ξ.1 : Measure X)) (ν := (η.1 : Measure X))
        (c := ε) hρ (B := B) hB)
  rcases ξ.2 B hB with ⟨m, hm⟩
  have hBt : MeasurableSet (thickening ε.toReal B) :=
    isOpen_thickening.measurableSet
  rcases η.2 (thickening ε.toReal B) hBt with ⟨n, hn⟩
  have hmE : (ξ.1 : Measure X) B = (m : ℝ≥0∞) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa using congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) hm
  have hnE : (η.1 : Measure X) (thickening ε.toReal B) = (n : ℝ≥0∞) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa using congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) hn
  have hmn_le_add : (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) + ε := by
    simpa [hmE, hnE] using hprox
  have hmn : m ≤ n :=
    nat_le_of_ennreal_nat_le_add_lt_one hε_lt_one hmn_le_add
  calc
    (ξ.1 : Measure X) B = (m : ℝ≥0∞) := hmE
    _ ≤ (n : ℝ≥0∞) := by exact_mod_cast hmn
    _ = (η.1 : Measure X) (thickening ε.toReal B) := hnE.symm

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:helpful-point-process`, second displayed implication.

Original label: `eq:lem-helpful-point-process-2`.

Informal statement: the symmetric Prokhorov-thickening inequality
`η(B) ≤ ξ(B^ε)` for finite integer-valued measures.
-/
theorem helpfulPointProcess_right {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    {ξ η : FiniteIntegerMeasures X} {ε : ℝ≥0∞}
    (_hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε)
    {B : Set X} (hB : MeasurableSet B) :
    (η.1 : Measure X) B ≤ (ξ.1 : Measure X) (thickening ε.toReal B) := by
  have hprox :
      (η.1 : Measure X) B ≤
        (ξ.1 : Measure X) (thickening ε.toReal B) + ε := by
    simpa [prokhorovEDistance] using
      (MeasureTheory.right_measure_le_of_levyProkhorovEDist_lt
        (μ := (ξ.1 : Measure X)) (ν := (η.1 : Measure X))
        (c := ε) hρ (B := B) hB)
  rcases η.2 B hB with ⟨m, hm⟩
  have hBt : MeasurableSet (thickening ε.toReal B) :=
    isOpen_thickening.measurableSet
  rcases ξ.2 (thickening ε.toReal B) hBt with ⟨n, hn⟩
  have hmE : (η.1 : Measure X) B = (m : ℝ≥0∞) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa using congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) hm
  have hnE : (ξ.1 : Measure X) (thickening ε.toReal B) = (n : ℝ≥0∞) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa using congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) hn
  have hmn_le_add : (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) + ε := by
    simpa [hmE, hnE] using hprox
  have hmn : m ≤ n :=
    nat_le_of_ennreal_nat_le_add_lt_one hε_lt_one hmn_le_add
  calc
    (η.1 : Measure X) B = (m : ℝ≥0∞) := hmE
    _ ≤ (n : ℝ≥0∞) := by exact_mod_cast hmn
    _ = (ξ.1 : Measure X) (thickening ε.toReal B) := hnE.symm

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:helpful-point-process`.

Original label: `eq:lem-helpful-point-process-3`.

Informal statement: if two finite integer-valued measures are at Prokhorov
distance less than `ε < 1`, then their total masses agree.
-/
theorem helpfulPointProcess_totalMass_eq {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    {ξ η : FiniteIntegerMeasures X} {ε : ℝ≥0∞}
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε) :
    (ξ.1 : Measure X) Set.univ = (η.1 : Measure X) Set.univ := by
  have hε_toReal_pos : 0 < ε.toReal :=
    ENNReal.toReal_pos hε_pos.ne' hε_lt_one.ne_top
  have huniv : thickening ε.toReal (Set.univ : Set X) = Set.univ :=
    eq_univ_of_univ_subset (self_subset_thickening hε_toReal_pos Set.univ)
  have hleft := helpfulPointProcess_left
    (ξ := ξ) (η := η) hε_pos hε_lt_one hρ
    (B := Set.univ) MeasurableSet.univ
  have hright := helpfulPointProcess_right
    (ξ := ξ) (η := η) hε_pos hε_lt_one hρ
    (B := Set.univ) MeasurableSet.univ
  rw [huniv] at hleft hright
  exact le_antisymm hleft hright

/-! ## Finite Atomic Integer Measures -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
the atomic-measure notation used in `thm:sufficient-decomposition`.

Original label: Dirac atom `\delta_x`.

Informal statement: the Dirac mass at `x`, regarded as a finite measure.
-/
noncomputable def diracFiniteMeasure {X : Type u} [MeasurableSpace X]
    (x : X) : FiniteMeasures X :=
  ⟨Measure.dirac x, inferInstance⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
the atomic-measure notation used in `thm:sufficient-decomposition`.

Original label: Dirac atom `\delta_x`.

Informal statement: the Dirac mass of a measurable set is `1` if the atom is
inside the set and `0` otherwise.
-/
theorem diracFiniteMeasure_apply {X : Type u} [MeasurableSpace X]
    (x : X) {B : Set X} (hB : MeasurableSet B) :
    diracFiniteMeasure x B =
      B.indicator (fun _ : X => (1 : ℝ≥0)) x := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  by_cases hx : x ∈ B
  · simp [diracFiniteMeasure, Measure.dirac_apply' x hB, hx]
  · simp [diracFiniteMeasure, Measure.dirac_apply' x hB, hx]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
display `eq:finite-integer-measures`.

Original label: auxiliary Dirac example for `eq:finite-integer-measures`.

Informal statement: every Dirac finite measure is integer-valued.
-/
theorem diracFiniteMeasure_integerValued {X : Type u} [MeasurableSpace X]
    (x : X) :
    IsIntegerValuedFiniteMeasure (diracFiniteMeasure x) := by
  intro B hB
  by_cases hx : x ∈ B
  · exact ⟨1, by simp [diracFiniteMeasure_apply x hB, hx]⟩
  · exact ⟨0, by simp [diracFiniteMeasure_apply x hB, hx]⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
the atomic-measure notation used in `thm:sufficient-decomposition`.

Original label: weighted atom `\beta_k \delta_{x_k}`.

Informal statement: a natural-number multiple of a Dirac finite measure.
-/
noncomputable def weightedDiracFiniteMeasure {X : Type u}
    [MeasurableSpace X] (β : ℕ) (x : X) : FiniteMeasures X :=
  (β : ℝ≥0) • diracFiniteMeasure x

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
the atomic-measure notation used in `thm:sufficient-decomposition`.

Original label: weighted atom `\beta_k \delta_{x_k}`.

Informal statement: a weighted Dirac atom assigns mass `β` to measurable sets
containing the atom and `0` to measurable sets not containing it.
-/
theorem weightedDiracFiniteMeasure_apply {X : Type u}
    [MeasurableSpace X] (β : ℕ) (x : X) {B : Set X}
    (hB : MeasurableSet B) :
    weightedDiracFiniteMeasure β x B =
      B.indicator (fun _ : X => (β : ℝ≥0)) x := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  by_cases hx : x ∈ B
  · simp only [weightedDiracFiniteMeasure, FiniteMeasure.toMeasure_smul,
      diracFiniteMeasure, FiniteMeasure.toMeasure_mk,
      Measure.smul_apply, Measure.dirac_apply_of_mem hx,
      Set.indicator_of_mem hx]
    rw [ENNReal.smul_def, smul_eq_mul, mul_one]
  · simp only [weightedDiracFiniteMeasure, FiniteMeasure.toMeasure_smul,
      diracFiniteMeasure, FiniteMeasure.toMeasure_mk,
      Measure.smul_apply, Measure.dirac_apply' x hB,
      Set.indicator_of_notMem hx, smul_zero]
    norm_num

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
display `eq:finite-integer-measures`.

Original label: auxiliary weighted-Dirac example for
`eq:finite-integer-measures`.

Informal statement: every natural-number weighted Dirac finite measure is
integer-valued.
-/
theorem weightedDiracFiniteMeasure_integerValued {X : Type u}
    [MeasurableSpace X] (β : ℕ) (x : X) :
    IsIntegerValuedFiniteMeasure (weightedDiracFiniteMeasure β x) := by
  intro B hB
  by_cases hx : x ∈ B
  · exact ⟨β, by simp [weightedDiracFiniteMeasure_apply β x hB, hx]⟩
  · exact ⟨0, by simp [weightedDiracFiniteMeasure_apply β x hB, hx]⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: finite atomic sum `\sum_{k \leq \kappa} \beta_k\delta_{x_k}`.

Informal statement: a finite list of atoms with natural multiplicities
defines a finite measure.

Lean strategy / thesis relation note: the thesis indexes atoms by `k ≤ κ`; Lean uses an arbitrary
finite index type `ι`, with the important special case `ι = Fin κ`.
-/
noncomputable def finiteAtomicMeasure {X : Type u} [MeasurableSpace X]
    {ι : Type v} [Fintype ι] (x : ι → X) (β : ι → ℕ) :
    FiniteMeasures X :=
  ∑ i : ι, weightedDiracFiniteMeasure (β i) (x i)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: finite atomic sum `\sum_{k \leq \kappa} \beta_k\delta_{x_k}`.

Informal statement: evaluating a finite atomic measure on a measurable set is
the sum of the multiplicities of atoms lying in that set.
-/
theorem finiteAtomicMeasure_apply {X : Type u} [MeasurableSpace X]
    {ι : Type v} [Fintype ι] (x : ι → X) (β : ι → ℕ)
    {B : Set X} (hB : MeasurableSet B) :
    finiteAtomicMeasure x β B =
      ∑ i : ι, B.indicator (fun _ : X => (β i : ℝ≥0)) (x i) := by
  classical
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  simp only [finiteAtomicMeasure, FiniteMeasure.toMeasure_sum,
    Measure.finset_sum_apply, weightedDiracFiniteMeasure,
    FiniteMeasure.toMeasure_smul, diracFiniteMeasure,
    FiniteMeasure.toMeasure_mk, Measure.smul_apply,
    Measure.dirac_apply' _ hB, ENNReal.coe_finset_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hxi : x i ∈ B
  · simp only [Set.indicator_of_mem hxi, Pi.one_apply]
    rw [ENNReal.smul_def, smul_eq_mul, mul_one]
  · simp only [Set.indicator_of_notMem hxi, smul_zero]
    norm_num

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition` and Lemma
`lem:disintegration-lemma`.

Original label: finite atomic evaluation used in
`lem:disintegration-lemma`.

Informal statement: evaluating the underlying measure of a finite atomic
measure on a measurable set gives the finite sum of the atom multiplicities
lying in that set.

Lean strategy / thesis relation note: `finiteAtomicMeasure_apply` is stated for `FiniteMeasure`
values in `ℝ≥0`; this version is the same statement after coercion to the
underlying `Measure`, whose values lie in `ℝ≥0∞`. This is the form needed by
mathlib's Prokhorov inequalities.
-/
theorem finiteAtomicMeasure_toMeasure_apply {X : Type u} [MeasurableSpace X]
    {ι : Type v} [Fintype ι] (x : ι → X) (β : ι → ℕ)
    {B : Set X} (hB : MeasurableSet B) :
    ((finiteAtomicMeasure x β : FiniteMeasures X) : Measure X) B =
      ∑ i : ι,
        ((B.indicator (fun _ : X => (β i : ℝ≥0)) (x i) : ℝ≥0) : ℝ≥0∞) := by
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [finiteAtomicMeasure_apply x β hB]
  simp

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
display `eq:finite-integer-measures` and
Theorem `thm:sufficient-decomposition`.

Original label: finite atomic sums are elements of `\mathcal{N}(X)`.

Informal statement: every finite atomic measure with natural multiplicities is
integer-valued.
-/
theorem finiteAtomicMeasure_integerValued {X : Type u} [MeasurableSpace X]
    {ι : Type v} [Fintype ι] (x : ι → X) (β : ι → ℕ) :
    IsIntegerValuedFiniteMeasure (finiteAtomicMeasure x β) := by
  classical
  intro B hB
  refine ⟨∑ i : ι, B.indicator (fun _ : X => β i) (x i), ?_⟩
  rw [finiteAtomicMeasure_apply x β hB]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hxi : x i ∈ B
  · simp [hxi]
  · simp [hxi]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: finite atomic sums as finite integer-valued measures.

Informal statement: package a finite atomic natural-multiplicity measure as an
element of `\mathcal{N}(X)`.
-/
noncomputable def finiteAtomicIntegerMeasure {X : Type u}
    [MeasurableSpace X] {ι : Type v} [Fintype ι]
    (x : ι → X) (β : ι → ℕ) : FiniteIntegerMeasures X :=
  ⟨finiteAtomicMeasure x β, finiteAtomicMeasure_integerValued x β⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: total mass of the atomic decomposition.

Informal statement: the total mass of a finite atomic measure is the sum of
its multiplicities.
-/
theorem finiteAtomicMeasure_univ {X : Type u} [MeasurableSpace X]
    {ι : Type v} [Fintype ι] (x : ι → X) (β : ι → ℕ) :
    finiteAtomicMeasure x β Set.univ = ∑ i : ι, (β i : ℝ≥0) := by
  simpa using finiteAtomicMeasure_apply x β (MeasurableSet.univ : MeasurableSet (Set.univ : Set X))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:sufficient-decomposition`.

Original label: decomposition predicate for
`thm:sufficient-decomposition`.

Informal statement: a finite integer-valued measure admits an atomic
decomposition when it is equal to a finite sum of natural-multiplicity Dirac
masses.

Lean strategy / thesis relation note: the full theorem that every finite
integer-valued measure on a standard Borel space admits such a decomposition,
and that the decomposition is unique up to permutation, is a substantial
background result. This structure records exactly the representation produced
by the existence half; `Foundations.External` supplies the universal existence
and uniqueness-up-to-permutation clauses once this target type is available.
-/
structure AtomicDecomposition {X : Type u} [MeasurableSpace X]
    (μ : FiniteIntegerMeasures X) where
  length : ℕ
  atom : Fin length → X
  multiplicity : Fin length → ℕ
  multiplicity_pos : ∀ i, 0 < multiplicity i
  atom_injective : Function.Injective atom
  represents : finiteAtomicMeasure atom multiplicity = μ.1

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: singleton-mass identity used in
`lem:disintegration-lemma`.

Informal statement: in an injective atomic decomposition, the measure of the
singleton containing atom `k` is exactly its multiplicity `β_k`.

Lean strategy / thesis relation note: singleton measurability is explicit in Lean via
`MeasurableSingletonClass`; in the thesis' metric Borel setting this is
automatic.
-/
theorem atomicDecomposition_toMeasure_singleton {X : Type u}
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : FiniteIntegerMeasures X} (d : AtomicDecomposition μ)
    (k : Fin d.length) :
    (μ.1 : Measure X) ({d.atom k} : Set X) =
      (d.multiplicity k : ℝ≥0∞) := by
  rw [← d.represents]
  rw [finiteAtomicMeasure_toMeasure_apply d.atom d.multiplicity
    (measurableSet_singleton (d.atom k))]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _hi hik
    have hne : d.atom i ≠ d.atom k := by
      intro h
      exact hik (d.atom_injective h)
    simp [hne]
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: the index set `L_k` in `lem:disintegration-lemma`.

Informal statement: for an atomic decomposition of `η`, a center `x`, and a
radius `ε`, `nearbyAtomIndices dη x ε` is the finite set of atom indices of
`η` whose atoms lie in the `ε`-ball around `x`.

Lean strategy / thesis relation note: the thesis defines `L_k` by
`\delta_{y_l}(B_ε(x_k)) = 1`. Lean uses the equivalent membership predicate
`y_l ∈ thickening ε.toReal {x}`.
-/
noncomputable def nearbyAtomIndices {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {η : FiniteIntegerMeasures X} (dη : AtomicDecomposition η)
    (x : X) (ε : ℝ≥0∞) : Finset (Fin dη.length) := by
  classical
  exact Finset.univ.filter fun l : Fin dη.length =>
    dη.atom l ∈ thickening ε.toReal ({x} : Set X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: construction of `L_k` in `lem:disintegration-lemma`.

Informal statement: the mass assigned by an atomic decomposition to the
`ε`-ball around `x` is the sum of multiplicities over exactly the nearby
indices.

Lean strategy / thesis relation note: this is the formal finite-sum version of the thesis line
`\eta(B_\varepsilon(x_k)) =
\sum_{l \leq \lambda}\alpha_l\delta_{y_l}(B_\varepsilon(x_k))`.
-/
theorem atomicDecomposition_toMeasure_thickening_singleton_eq_sum_nearbyAtomIndices
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    {η : FiniteIntegerMeasures X} (dη : AtomicDecomposition η)
    (x : X) (ε : ℝ≥0∞) :
    (η.1 : Measure X) (thickening ε.toReal ({x} : Set X)) =
      ∑ l ∈ nearbyAtomIndices dη x ε, (dη.multiplicity l : ℝ≥0∞) := by
  rw [← dη.represents]
  rw [finiteAtomicMeasure_toMeasure_apply dη.atom dη.multiplicity
    isOpen_thickening.measurableSet]
  classical
  unfold nearbyAtomIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hmem : dη.atom l ∈ thickening ε.toReal ({x} : Set X)
  · simp [hmem]
  · simp [hmem]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: distance property of the sets `L_k` in
`lem:disintegration-lemma`.

Informal statement: membership in the nearby-index set means that the
corresponding atom lies within `ε` of the center atom.

Lean strategy / thesis relation note: the thesis states this using real-valued balls. Lean keeps the
radius as `ℝ≥0∞`, because the Prokhorov layer is extended-valued; finiteness
of `ε` converts `ENNReal.ofReal ε.toReal` back to `ε`.
-/
theorem edist_atom_lt_of_mem_nearbyAtomIndices {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {η : FiniteIntegerMeasures X} (dη : AtomicDecomposition η)
    {x : X} {ε : ℝ≥0∞} (hε_top : ε < ∞)
    {l : Fin dη.length} (hl : l ∈ nearbyAtomIndices dη x ε) :
    edist (dη.atom l) x < ε := by
  classical
  unfold nearbyAtomIndices at hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  rw [Metric.mem_thickening_iff_exists_edist_lt] at hl
  rcases hl with ⟨z, hz, hlz⟩
  rw [Set.mem_singleton_iff] at hz
  subst z
  simpa [ENNReal.ofReal_toReal hε_top.ne] using hlz

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: the equality
`\xi((B_\varepsilon(x_k))^\varepsilon) = \beta_k`.

Informal statement: if the double `ε`-thickening of atom `x_k` contains no
other atom from the decomposition of `ξ`, then `ξ` assigns that double
thickening exactly the multiplicity of atom `k`.

Lean strategy / thesis relation note: the thesis obtains the isolation hypothesis from
`ε < γ`. This lemma isolates the measure-theoretic finite-sum argument; the
finite-minimum `γ` bookkeeping is a separate geometric step.
-/
theorem atomicDecomposition_toMeasure_double_thickening_singleton_eq
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    {ξ : FiniteIntegerMeasures X} (dξ : AtomicDecomposition ξ)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε) (hε_top : ε < ∞)
    (k : Fin dξ.length)
    (hiso : ∀ i : Fin dξ.length, i ≠ k →
      dξ.atom i ∉ thickening ε.toReal
        (thickening ε.toReal ({dξ.atom k} : Set X))) :
    (ξ.1 : Measure X)
      (thickening ε.toReal (thickening ε.toReal ({dξ.atom k} : Set X))) =
        (dξ.multiplicity k : ℝ≥0∞) := by
  have hε_real_pos : 0 < ε.toReal :=
    ENNReal.toReal_pos hε_pos.ne' hε_top.ne
  rw [← dξ.represents]
  rw [finiteAtomicMeasure_toMeasure_apply dξ.atom dξ.multiplicity
    isOpen_thickening.measurableSet]
  rw [Finset.sum_eq_single k]
  · have hinner :
        dξ.atom k ∈ thickening ε.toReal ({dξ.atom k} : Set X) :=
      self_subset_thickening hε_real_pos ({dξ.atom k} : Set X) rfl
    have houter : dξ.atom k ∈
        thickening ε.toReal (thickening ε.toReal ({dξ.atom k} : Set X)) :=
      self_subset_thickening hε_real_pos
        (thickening ε.toReal ({dξ.atom k} : Set X)) hinner
    simp [houter]
  · intro i _hi hik
    have hnot := hiso i hik
    simp [hnot]
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`, part `(i)`.

Original label: multiplicity equality
`\beta_k = \sum_{l\in L_k}\alpha_l`.

Informal statement: under the same isolation condition that the thesis gets
from `ε < γ`, the multiplicity of atom `x_k` in `ξ` equals the total
multiplicity of all atoms of `η` that lie in the `ε`-ball around `x_k`.

Lean strategy / thesis relation note: this is exactly the thesis' inequality sandwich:
`\xi({x_k}) ≤ η(B_ε(x_k)) ≤ ξ((B_ε(x_k))^ε)`, with both ends identified as
`\beta_k`.
-/
theorem atomicDecomposition_multiplicity_eq_sum_nearbyAtomIndices_of_isolated
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε)
    (k : Fin dξ.length)
    (hiso : ∀ i : Fin dξ.length, i ≠ k →
      dξ.atom i ∉ thickening ε.toReal
        (thickening ε.toReal ({dξ.atom k} : Set X))) :
    dξ.multiplicity k =
      ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε, dη.multiplicity l := by
  have hε_top : ε < ∞ :=
    lt_trans hε_lt_one (by norm_num : (1 : ℝ≥0∞) < ∞)
  let B : Set X := {dξ.atom k}
  let T : Set X := thickening ε.toReal B
  have hleft_measure : (ξ.1 : Measure X) B ≤ (η.1 : Measure X) T := by
    exact helpfulPointProcess_left (ξ := ξ) (η := η)
      hε_pos hε_lt_one hρ (B := B)
        (measurableSet_singleton (dξ.atom k))
  have hright_measure : (η.1 : Measure X) T ≤
      (ξ.1 : Measure X) (thickening ε.toReal T) := by
    exact helpfulPointProcess_right (ξ := ξ) (η := η)
      hε_pos hε_lt_one hρ (B := T)
        isOpen_thickening.measurableSet
  have hsingle : (ξ.1 : Measure X) B =
      (dξ.multiplicity k : ℝ≥0∞) := by
    simpa [B] using atomicDecomposition_toMeasure_singleton dξ k
  have hsum : (η.1 : Measure X) T =
      ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
        (dη.multiplicity l : ℝ≥0∞) := by
    simpa [B, T] using
      atomicDecomposition_toMeasure_thickening_singleton_eq_sum_nearbyAtomIndices
        dη (dξ.atom k) ε
  have hdouble : (ξ.1 : Measure X) (thickening ε.toReal T) =
      (dξ.multiplicity k : ℝ≥0∞) := by
    simpa [B, T] using
      atomicDecomposition_toMeasure_double_thickening_singleton_eq
        dξ hε_pos hε_top k hiso
  have heqE : (dξ.multiplicity k : ℝ≥0∞) =
      ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
        (dη.multiplicity l : ℝ≥0∞) := by
    apply le_antisymm
    · calc
        (dξ.multiplicity k : ℝ≥0∞) = (ξ.1 : Measure X) B :=
          hsingle.symm
        _ ≤ (η.1 : Measure X) T := hleft_measure
        _ = ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
              (dη.multiplicity l : ℝ≥0∞) := hsum
    · calc
        (∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
              (dη.multiplicity l : ℝ≥0∞)) = (η.1 : Measure X) T :=
          hsum.symm
        _ ≤ (ξ.1 : Measure X) (thickening ε.toReal T) :=
          hright_measure
        _ = (dξ.multiplicity k : ℝ≥0∞) := hdouble
  have heqE' : (dξ.multiplicity k : ℝ≥0∞) =
      ((∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
        dη.multiplicity l : ℕ) : ℝ≥0∞) := by
    simpa [Nat.cast_sum] using heqE
  exact_mod_cast heqE'

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`, part `(ii)`.

Original label: disjointness of the sets `L_k`.

Informal statement: if two ambient `ε`-balls around distinct atoms of `ξ` are
disjoint, then the corresponding nearby-index sets for atoms of `η` are
disjoint.
-/
theorem nearbyAtomIndices_disjoint_of_disjoint_thickenings {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {η : FiniteIntegerMeasures X} (dη : AtomicDecomposition η)
    {x x' : X} {ε : ℝ≥0∞}
    (hdisj : Disjoint (thickening ε.toReal ({x} : Set X))
      (thickening ε.toReal ({x'} : Set X))) :
    Disjoint (nearbyAtomIndices dη x ε)
      (nearbyAtomIndices dη x' ε) := by
  classical
  rw [Finset.disjoint_left]
  intro l hl hl'
  unfold nearbyAtomIndices at hl hl'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl hl'
  exact hdisj.le_bot ⟨hl, hl'⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: geometric disjointness step following the definition of
`\gamma`.

Informal statement: if `2ε` is smaller than the distance between two centers,
then their open `ε`-thickenings are disjoint.

Lean strategy / thesis relation note: the thesis proves this by the triangle inequality after
choosing `ε < γ`. Lean states the operational consequence directly using
extended distances; the finite-minimum `γ` is exactly a way to secure this
hypothesis for every distinct pair of atoms.
-/
theorem disjoint_thickenings_of_add_lt_edist {X : Type u}
    [PseudoEMetricSpace X] {x x' : X} {ε : ℝ≥0∞}
    (hε_top : ε < ∞) (hsep : ε + ε < edist x x') :
    Disjoint (thickening ε.toReal ({x} : Set X))
      (thickening ε.toReal ({x'} : Set X)) := by
  rw [Set.disjoint_iff]
  intro y hyboth
  rcases hyboth with ⟨hy, hx'⟩
  rw [Metric.mem_thickening_iff_exists_edist_lt] at hy hx'
  rcases hy with ⟨z, hz, hyz⟩
  rcases hx' with ⟨z', hz', hyz'⟩
  rw [Set.mem_singleton_iff] at hz hz'
  subst z
  subst z'
  have hxy : edist x y < ε := by
    simpa [edist_comm, ENNReal.ofReal_toReal hε_top.ne] using hyz
  have hyx' : edist y x' < ε := by
    simpa [ENNReal.ofReal_toReal hε_top.ne] using hyz'
  have hlt : edist x x' < ε + ε :=
    lt_of_le_of_lt (edist_triangle x y x')
      (ENNReal.add_lt_add hxy hyx')
  exact False.elim ((not_lt_of_ge hsep.le) hlt)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: double-thickening isolation following the definition of
`\gamma`.

Informal statement: if `2ε` is smaller than the distance between atoms
`x_k` and `x_i`, then atom `x_i` is not in
`(B_ε(x_k))^ε`.

Lean strategy / thesis relation note: this is the precise geometric fact used in the thesis line
`\xi((B_\varepsilon(x_k))^\varepsilon) = \xi(B_{2\varepsilon}(x_k)) =
\beta_k`.
-/
theorem atom_notMem_double_thickening_of_add_lt_edist {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ : FiniteIntegerMeasures X} (dξ : AtomicDecomposition ξ)
    {ε : ℝ≥0∞} (hε_top : ε < ∞)
    {k i : Fin dξ.length}
    (hsep : ε + ε < edist (dξ.atom k) (dξ.atom i)) :
    dξ.atom i ∉ thickening ε.toReal
      (thickening ε.toReal ({dξ.atom k} : Set X)) := by
  intro hi
  rw [Metric.mem_thickening_iff_exists_edist_lt] at hi
  rcases hi with ⟨y, hyinner, hiy⟩
  rw [Metric.mem_thickening_iff_exists_edist_lt] at hyinner
  rcases hyinner with ⟨z, hz, hyz⟩
  rw [Set.mem_singleton_iff] at hz
  subst z
  have hiy' : edist (dξ.atom i) y < ε := by
    simpa [ENNReal.ofReal_toReal hε_top.ne] using hiy
  have hyk : edist y (dξ.atom k) < ε := by
    simpa [ENNReal.ofReal_toReal hε_top.ne] using hyz
  have hik : edist (dξ.atom i) (dξ.atom k) < ε + ε :=
    lt_of_le_of_lt (edist_triangle (dξ.atom i) y (dξ.atom k))
      (ENNReal.add_lt_add hiy' hyk)
  have hsep' : ε + ε < edist (dξ.atom i) (dξ.atom k) := by
    simpa [edist_comm] using hsep
  exact (not_lt_of_ge hsep'.le) hik

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: finite pair set used in the definition of `\gamma`.

Informal statement: the finite set of ordered pairs of distinct atoms in an
atomic decomposition.

Lean strategy / thesis relation note: the thesis writes this as a finite collection of index pairs.
Lean uses the finite type `Fin dξ.length` and filters the finite product by
the predicate `k ≠ k'`.
-/
noncomputable def distinctAtomPairs {X : Type u}
    [MeasurableSpace X] {ξ : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) :
    Finset (Fin dξ.length × Fin dξ.length) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun p => p.1 ≠ p.2

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: finite pair set used in the definition of `\gamma`.

Informal statement: membership in the finite pair set is exactly inequality of
the two indices.
-/
theorem mem_distinctAtomPairs_iff {X : Type u}
    [MeasurableSpace X] {ξ : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ)
    (p : Fin dξ.length × Fin dξ.length) :
    p ∈ distinctAtomPairs dξ ↔ p.1 ≠ p.2 := by
  classical
  simp [distinctAtomPairs]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: finite minimum `\gamma` in `lem:disintegration-lemma`.

Informal statement: `\gamma` is `1` when there are no distinct atom pairs;
otherwise it is the minimum of `1` and half the smallest distance between two
distinct atoms in the reference decomposition.

Lean strategy / thesis relation note: the thesis defines a positive real radius. Lean keeps the
radius in `ℝ≥0∞`, matching the Prokhorov distance layer. The value is finite
because it is bounded by `1`.
-/
noncomputable def atomicDecompositionSeparationGamma {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ : FiniteIntegerMeasures X} (dξ : AtomicDecomposition ξ) :
    ℝ≥0∞ := by
  classical
  by_cases h : (distinctAtomPairs dξ).Nonempty
  · exact min (1 : ℝ≥0∞)
      ((distinctAtomPairs dξ).inf' h fun p =>
        edist (dξ.atom p.1) (dξ.atom p.2) / 2)
  · exact 1

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: finite minimum `\gamma` in `lem:disintegration-lemma`.

Informal statement: the separation radius is at most `1`, so any
`ε < \gamma` also satisfies the thesis' standing `ε < 1` hypothesis.
-/
theorem atomicDecompositionSeparationGamma_le_one {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ : FiniteIntegerMeasures X} (dξ : AtomicDecomposition ξ) :
    atomicDecompositionSeparationGamma dξ ≤ 1 := by
  classical
  unfold atomicDecompositionSeparationGamma
  by_cases h : (distinctAtomPairs dξ).Nonempty
  · simp [h]
  · simp [h]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: positivity of the finite minimum `\gamma`.

Informal statement: in a genuine extended metric space, the separation radius
of an injective finite atomic decomposition is positive.

Lean strategy / thesis relation note: the manuscript defines `\gamma > 0` as the minimum of finitely
many positive pair distances, or `1` if there are no distinct pairs. Lean
requires `EMetricSpace`, not merely `PseudoEMetricSpace`, for distinct atoms
to have positive edistance.
-/
theorem atomicDecompositionSeparationGamma_pos {X : Type u}
    [MeasurableSpace X] [EMetricSpace X]
    {ξ : FiniteIntegerMeasures X} (dξ : AtomicDecomposition ξ) :
    0 < atomicDecompositionSeparationGamma dξ := by
  classical
  unfold atomicDecompositionSeparationGamma
  by_cases h : (distinctAtomPairs dξ).Nonempty
  · rw [dif_pos h]
    apply lt_min
    · exact zero_lt_one
    · apply (Finset.lt_inf'_iff _).2
      intro p hp
      have hp_ne : p.1 ≠ p.2 := (mem_distinctAtomPairs_iff dξ p).mp hp
      have hatom_ne : dξ.atom p.1 ≠ dξ.atom p.2 := by
        intro hatom
        exact hp_ne (dξ.atom_injective hatom)
      exact ENNReal.half_pos (edist_pos.2 hatom_ne).ne'
  · rw [dif_neg h]
    exact zero_lt_one

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: geometric consequence of `ε < \gamma`.

Informal statement: if `ε` is below the finite separation radius, then
`2ε` is smaller than the distance between every distinct pair of atoms.

Lean strategy / thesis relation note: this is the formal version of the thesis step where the
definition of `\gamma` makes the `ε`-balls around distinct atoms disjoint and
prevents other atoms from entering the double thickening of a singleton.
-/
theorem add_self_lt_edist_of_lt_atomicDecompositionSeparationGamma
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X]
    {ξ : FiniteIntegerMeasures X} (dξ : AtomicDecomposition ξ)
    {ε : ℝ≥0∞}
    (hεγ : ε < atomicDecompositionSeparationGamma dξ)
    {k k' : Fin dξ.length} (hkk' : k ≠ k') :
    ε + ε < edist (dξ.atom k) (dξ.atom k') := by
  classical
  have hp_mem : (k, k') ∈ distinctAtomPairs dξ := by
    rw [mem_distinctAtomPairs_iff]
    exact hkk'
  have hpairs : (distinctAtomPairs dξ).Nonempty := ⟨(k, k'), hp_mem⟩
  unfold atomicDecompositionSeparationGamma at hεγ
  by_cases hnon : (distinctAtomPairs dξ).Nonempty
  · rw [dif_pos hnon] at hεγ
    have hε_inf :
        ε <
          (distinctAtomPairs dξ).inf' hnon
            (fun p => edist (dξ.atom p.1) (dξ.atom p.2) / 2) :=
      (lt_min_iff.mp hεγ).2
    have hinf_le_pair :
        (distinctAtomPairs dξ).inf' hnon
            (fun p => edist (dξ.atom p.1) (dξ.atom p.2) / 2) ≤
          edist (dξ.atom k) (dξ.atom k') / 2 := by
      simpa using
        (Finset.inf'_le
          (s := distinctAtomPairs dξ)
          (f := fun p => edist (dξ.atom p.1) (dξ.atom p.2) / 2)
          hp_mem)
    have hε_half : ε < edist (dξ.atom k) (dξ.atom k') / 2 :=
      lt_of_lt_of_le hε_inf hinf_le_pair
    have hsum :
        ε + ε <
          edist (dξ.atom k) (dξ.atom k') / 2 +
            edist (dξ.atom k) (dξ.atom k') / 2 :=
      ENNReal.add_lt_add hε_half hε_half
    simpa [ENNReal.add_halves] using hsum
  · exact False.elim (hnon hpairs)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: conditional geometric core of `lem:disintegration-lemma`.

Informal statement: once the radius `ε` is small enough to isolate each atom
of `ξ` under double thickening and to make the distinct `ε`-balls disjoint,
the three conclusions of the thesis disintegration lemma hold.

Lean strategy / thesis relation note: the manuscript gets the two geometric hypotheses from the
finite separation radius `γ`. Lean records this theorem as the measure-
theoretic core, with the remaining `γ`-to-isolation verification separated
out so downstream inverse-continuity can use the same `L_k` object.
-/
theorem atomicDecomposition_disintegration_of_isolated_radius
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε)
    (hiso : ∀ k i : Fin dξ.length, i ≠ k →
      dξ.atom i ∉ thickening ε.toReal
        (thickening ε.toReal ({dξ.atom k} : Set X)))
    (hballs : ∀ k k' : Fin dξ.length, k ≠ k' →
      Disjoint (thickening ε.toReal ({dξ.atom k} : Set X))
        (thickening ε.toReal ({dξ.atom k'} : Set X))) :
    (∀ k : Fin dξ.length,
      dξ.multiplicity k =
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l) ∧
    (∀ k k' : Fin dξ.length, k ≠ k' →
      Disjoint (nearbyAtomIndices dη (dξ.atom k) ε)
        (nearbyAtomIndices dη (dξ.atom k') ε)) ∧
    (∀ k : Fin dξ.length, ∀ l : Fin dη.length,
      l ∈ nearbyAtomIndices dη (dξ.atom k) ε →
        edist (dξ.atom k) (dη.atom l) < ε) := by
  have hε_top : ε < ∞ :=
    lt_trans hε_lt_one (by norm_num : (1 : ℝ≥0∞) < ∞)
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact
      atomicDecomposition_multiplicity_eq_sum_nearbyAtomIndices_of_isolated
        dξ dη hε_pos hε_lt_one hρ k (hiso k)
  · intro k k' hkk'
    exact nearbyAtomIndices_disjoint_of_disjoint_thickenings dη
      (hballs k k' hkk')
  · intro k l hl
    simpa [edist_comm] using
      edist_atom_lt_of_mem_nearbyAtomIndices dη hε_top hl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: pairwise-distance form of `lem:disintegration-lemma`.

Informal statement: if `ε < 1`, the Prokhorov distance from `ξ` to `η` is
less than `ε`, and every pair of distinct atoms of the reference measure `ξ`
has distance greater than `2ε`, then the nearby sets `L_k` satisfy the three
conclusions of the thesis disintegration lemma.

Lean strategy / thesis relation note: this is the thesis lemma with the finite minimum `γ` unfolded
to its operative pairwise consequence. The thesis-shaped `ε < γ` theorem
below derives this hypothesis from the finite separation radius.
-/
theorem atomicDecomposition_disintegration_of_pairwise_add_lt_edist
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε)
    (hsep : ∀ k k' : Fin dξ.length, k ≠ k' →
      ε + ε < edist (dξ.atom k) (dξ.atom k')) :
    (∀ k : Fin dξ.length,
      dξ.multiplicity k =
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l) ∧
    (∀ k k' : Fin dξ.length, k ≠ k' →
      Disjoint (nearbyAtomIndices dη (dξ.atom k) ε)
        (nearbyAtomIndices dη (dξ.atom k') ε)) ∧
    (∀ k : Fin dξ.length, ∀ l : Fin dη.length,
      l ∈ nearbyAtomIndices dη (dξ.atom k) ε →
        edist (dξ.atom k) (dη.atom l) < ε) := by
  have hε_top : ε < ∞ :=
    lt_trans hε_lt_one (by norm_num : (1 : ℝ≥0∞) < ∞)
  apply atomicDecomposition_disintegration_of_isolated_radius
    dξ dη hε_pos hε_lt_one hρ
  · intro k i hik
    exact atom_notMem_double_thickening_of_add_lt_edist
      dξ hε_top (hsep k i hik.symm)
  · intro k k' hkk'
    exact disjoint_thickenings_of_add_lt_edist hε_top (hsep k k' hkk')

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Lemma `lem:disintegration-lemma`.

Original label: `lem:disintegration-lemma`.

Informal statement: if `ε` is below the finite separation radius `\gamma` of
the reference finite integer-valued measure `ξ`, and `η` is within
Prokhorov distance `< ε` of `ξ`, then the atoms of `η` decompose into finite
sets `L_k` around the atoms of `ξ`; these sets preserve multiplicity, are
pairwise disjoint, and every selected atom lies within `ε` of its reference
atom.

Lean strategy / thesis relation note: this is the thesis statement with `\gamma` represented by
`atomicDecompositionSeparationGamma`. The proof follows the manuscript: the
finite minimum gives the pairwise `2ε` separation, and the previously proved
Prokhorov sandwich gives the multiplicity equality.
-/
theorem atomicDecomposition_disintegration_of_lt_separationGamma
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    {ε : ℝ≥0∞} (hε_pos : 0 < ε)
    (hεγ : ε < atomicDecompositionSeparationGamma dξ)
    (hρ : prokhorovEDistance ξ.1 η.1 < ε) :
    (∀ k : Fin dξ.length,
      dξ.multiplicity k =
        ∑ l ∈ nearbyAtomIndices dη (dξ.atom k) ε,
          dη.multiplicity l) ∧
    (∀ k k' : Fin dξ.length, k ≠ k' →
      Disjoint (nearbyAtomIndices dη (dξ.atom k) ε)
        (nearbyAtomIndices dη (dξ.atom k') ε)) ∧
    (∀ k : Fin dξ.length, ∀ l : Fin dη.length,
      l ∈ nearbyAtomIndices dη (dξ.atom k) ε →
        edist (dξ.atom k) (dη.atom l) < ε) := by
  have hε_lt_one : ε < 1 :=
    lt_of_lt_of_le hεγ (atomicDecompositionSeparationGamma_le_one dξ)
  exact atomicDecomposition_disintegration_of_pairwise_add_lt_edist
    dξ dη hε_pos hε_lt_one hρ
      (fun k k' hkk' =>
        add_self_lt_edist_of_lt_atomicDecompositionSeparationGamma
          dξ hεγ hkk')

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Corollary `cor:measures-coincide`.

Original label: `cor:measures-coincide`.

Informal statement: if two finite integer-valued measures are within
Prokhorov distance `< 1`, then the sums of the multiplicities in any atomic
decompositions are equal.

Lean strategy / thesis relation note: the thesis applies `lem:helpful-point-process` with a radius
strictly between `ρ(ξ,η)` and `1`. Lean obtains this intermediate radius by
density of `ℝ≥0∞`.
-/
theorem atomicDecomposition_totalMultiplicity_eq_of_prokhorovEDistance_lt_one
    {X : Type u}
    [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]
    {ξ η : FiniteIntegerMeasures X}
    (dξ : AtomicDecomposition ξ) (dη : AtomicDecomposition η)
    (hρ : prokhorovEDistance ξ.1 η.1 < 1) :
    (∑ k : Fin dξ.length, dξ.multiplicity k) =
      ∑ l : Fin dη.length, dη.multiplicity l := by
  rcases exists_between hρ with ⟨ε, hρε, hε_one⟩
  have hε_pos : 0 < ε := lt_of_le_of_lt bot_le hρε
  have htotalE :
      (ξ.1 : Measure X) Set.univ = (η.1 : Measure X) Set.univ :=
    helpfulPointProcess_totalMass_eq
      (ξ := ξ) (η := η) hε_pos hε_one hρε
  have htotalNN : ξ.1 Set.univ = η.1 Set.univ := by
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact htotalE
  have hξ :
      ξ.1 Set.univ = ∑ k : Fin dξ.length, (dξ.multiplicity k : ℝ≥0) := by
    rw [← dξ.represents]
    exact finiteAtomicMeasure_univ dξ.atom dξ.multiplicity
  have hη :
      η.1 Set.univ = ∑ l : Fin dη.length, (dη.multiplicity l : ℝ≥0) := by
    rw [← dη.represents]
    exact finiteAtomicMeasure_univ dη.atom dη.multiplicity
  have hsumsNN :
      (∑ k : Fin dξ.length, (dξ.multiplicity k : ℝ≥0)) =
        ∑ l : Fin dη.length, (dη.multiplicity l : ℝ≥0) := by
    rw [← hξ, ← hη]
    exact htotalNN
  exact_mod_cast hsumsNN

end PointProcesses
end Stochastic
end Foundations
end Thesis
