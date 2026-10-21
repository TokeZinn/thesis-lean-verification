import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Disintegration.Unique
import Thesis.Appendices.Analysis.RegularPaths
import Thesis.Appendices.MeasureTheory.AtomicMeasures
import Thesis.Foundations.Stochastic.FiniteMeasureBorel
import Thesis.Context.External

/-!
# Preliminary Measure Theory

Formal statements linked to `A - appendices/measure.tex`.

The Prokhorov topology, completeness, and separability are proved internally.
The Prokhorov Borel structure is proved to agree with evaluation
measurability. The diffuse/atomic decomposition is proved on arbitrary
sigma-finite measurable spaces in `AtomicMeasures`, with a countable
point-mass formula on Polish Borel spaces. Compact-interval càdlàg/càglàd
`L²` membership is proved using one-sided continuity and limits.
-/

noncomputable section

open Filter Set Topology
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory RealInnerProductSpace Topology

universe u v w

/-- Original label: `defn:standard-borel-space`.
Being standard Borel asserts existence of a compatible Polish topology; it
does not equip the measurable space with a preferred topology. -/
theorem standardBorel_iff_exists_polish (X : Type u) [m : MeasurableSpace X] :
    StandardBorelSpace X ↔ ∃ t : TopologicalSpace X,
      @PolishSpace X t ∧ m = @borel X t := by
  constructor
  · intro h
    obtain ⟨t, hb, hp⟩ := h.polish
    exact ⟨t, hp, hb.measurable_eq⟩
  · rintro ⟨t, hp, hm⟩
    exact ⟨⟨t, ⟨hm⟩, hp⟩⟩

namespace Thesis
namespace Foundations
namespace Preliminary
namespace MeasureTheory

/-- Original label: `thm:borel-subset-standard-borel`.
The subtype measurable space is exactly the trace sigma algebra. -/
theorem borelSubset_standardBorel {X : Type u} [MeasurableSpace X]
    [StandardBorelSpace X] {Y : Set X} (hY : MeasurableSet Y) : StandardBorelSpace Y :=
  hY.standardBorel

/--
Original label: `defn:measurable-space`.

Informal statement: a measurable space on a nonempty set `Ω` is a collection
of subsets containing `Ω` and closed under complements and countable unions;
that collection is its sigma-algebra.

Lean strategy / thesis relation note: Mathlib's `MeasurableSpace Ω` packages
exactly this sigma-algebra.  Its primitive fields use the equivalent axioms
`∅` measurable, complement closure, and countable-union closure; `univ` follows
from the first two.  The thesis's nonemptiness assumption is retained at use
sites when probability mass one is needed, but is not required to define a
sigma-algebra.
-/
abbrev SigmaAlgebra (Ω : Type u) := MeasurableSpace Ω

/--
Original label: `defn:measure`.

Informal statement: a measure is an extended-nonnegative-valued, countably
additive set function that vanishes on the empty set; it is a probability
measure exactly when its total mass is one.

Lean strategy / thesis relation note: `Measure Ω` already bundles the empty-set
and disjoint-countable-additivity axioms.  The displayed equivalence records
the thesis's additional probability clause using Mathlib's
`IsProbabilityMeasure` class.
-/
theorem probabilityMeasure_iff
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) :
    IsProbabilityMeasure μ ↔ μ univ = 1 :=
  _root_.MeasureTheory.isProbabilityMeasure_iff

/--
Original label: `defn:measurable-function`.

Informal statement: a function `f : Ω → S` is measurable when the inverse
image of every measurable subset of `S` is measurable in `Ω`; on a probability
space it is a random element, and a real-valued one is a random variable.

Lean strategy / thesis relation note: Mathlib's `Measurable f` is exactly the
inverse-image condition.  The probability measure changes terminology, not
the underlying predicate, so no additional field is needed for random
elements or variables.
-/
abbrev MeasurableFunction
    {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
    (f : Ω → S) : Prop :=
  Measurable f

/--
Original label: `defn:trace-sigma-algebra`.

Informal statement: the trace sigma-algebra on a subset `E ⊆ Ω` consists of
the intersections `F ∩ E` with measurable `F ⊆ Ω`.

Lean strategy / thesis relation note: Mathlib represents the restricted set
as the subtype `E` and equips it with the pullback (`comap`) of the ambient
measurable space along `Subtype.val`.  Its measurable subsets are precisely
the thesis traces, including when `E` itself is not measurable.
-/
abbrev traceSigmaAlgebra
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (E : Set Ω) : MeasurableSpace E :=
  MeasurableSpace.comap (fun x : E => (x : Ω)) mΩ

/--
Original label: `prop:measurable-restrictions`.

Informal statement: if measurable sets `E n` cover `Ω`, then `f : Ω → S` is
measurable if and only if every restriction `f|E n : E n → S` is measurable
for the trace sigma-algebra.

Lean strategy / thesis relation note: the forward direction composes with the
measurable subtype inclusion.  For the converse, the preimage of a measurable
set is reconstructed as the countable union of its intersections with `E n`;
`MeasurableSet.subtype_image` is the Lean counterpart of the thesis sets
`A_n ∩ E_n`.  This follows the manuscript proof rather than invoking a
black-box pasting theorem.
-/
theorem measurable_iff_restrictions
    {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
    (f : Ω → S) (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
    (hcover : ⋃ n, E n = univ) :
    Measurable f ↔ ∀ n, Measurable (fun x : E n => f x) := by
  constructor
  · intro hf n
    exact hf.comp measurable_subtype_coe
  · intro hf B hB
    have hpiece : ∀ n, MeasurableSet (f ⁻¹' B ∩ E n) := by
      intro n
      have hsub : MeasurableSet ((fun x : E n => f x) ⁻¹' B) := hf n hB
      have himage := (hE n).subtype_image hsub
      have heq :
          Subtype.val '' ((fun x : E n => f x) ⁻¹' B) = f ⁻¹' B ∩ E n := by
        ext x
        simp
      rw [heq] at himage
      exact himage
    have hpreimage : f ⁻¹' B = ⋃ n, (f ⁻¹' B ∩ E n) := by
      rw [← inter_iUnion, hcover, inter_univ]
    rw [hpreimage]
    exact MeasurableSet.iUnion hpiece

/--
Original label: `prop:push-forward`.

Informal statement: a measurable map `f : Ω → S` transports a measure `μ` to
the measure `μ ∘ f⁻¹`, whose value on measurable `B` is `μ (f⁻¹ B)`; for a
probability measure this push-forward is the law of `f`.

Lean strategy / thesis relation note: Mathlib calls the push-forward
`Measure.map f μ`.  `Measure.map_apply` proves the displayed evaluation
identity, and Mathlib automatically transports `IsProbabilityMeasure` through
a measurable map.
-/
theorem pushForward_apply
    {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) {f : Ω → S} (hf : Measurable f)
    {B : Set S} (hB : MeasurableSet B) :
    μ.map f B = μ (f ⁻¹' B) :=
  Measure.map_apply hf hB

/--
Original label: `defn:product-measure`.

Informal statement: for finite measures `μ` and `ν`, their product is the
unique measure on the product sigma-algebra satisfying
`(μ ⊗ ν)(A × B) = μ(A)ν(B)` for measurable rectangles.

Lean strategy / thesis relation note: choose Mathlib's `μ.prod ν`; its theorem
`Measure.prod_prod` supplies the rectangle identity.  Uniqueness is proved
with `Measure.ext_prod`.  The candidate measure is finite because its mass on
`univ × univ` is the product of two finite masses.
-/
theorem productMeasure_existsUnique
    {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T)
    [SigmaFinite μ] [SigmaFinite ν] :
    ∃! ρ : Measure (S × T),
      ∀ A : Set S, ∀ B : Set T, MeasurableSet A → MeasurableSet B →
        ρ (A ×ˢ B) = μ A * ν B := by
  refine ⟨μ.prod ν, ?_, ?_⟩
  · intro A B _ _
    exact Measure.prod_prod A B
  · intro ρ hρ
    exact (Measure.prod_eq fun A B hA hB => hρ A B hA hB).symm

/--
Original label: `thm:tonelli-fubini`.

Informal statement: a nonnegative measurable function on a product has
measurable partial integrals and equal product and iterated integrals in both
orders; an integrable real function has integrable sections almost everywhere
and satisfies the analogous two Fubini identities.

Lean strategy / thesis relation note: the nonnegative clause is Mathlib's
`lintegral_prod` and `lintegral_prod_symm` for `ℝ≥0∞`, together with the two
partial-integral measurability theorems.  The signed clause uses the Bochner
integral specialised to `ℝ`, `Integrable.prod_right_ae`,
`Integrable.prod_left_ae`, `integral_prod`, and `integral_prod_symm`.
The full extended-real-valued statement, including infinite values on null
sets, is proved separately in `ExtendedFubini.lean`.
-/
theorem tonelliFubini
    {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T)
    [SigmaFinite μ] [SigmaFinite ν]
    (g : S × T → ℝ≥0∞) (hg : Measurable g)
    (f : S × T → ℝ) (hf : Integrable f (μ.prod ν)) :
    (Measurable (fun s => ∫⁻ t, g (s, t) ∂ν) ∧
      Measurable (fun t => ∫⁻ s, g (s, t) ∂μ) ∧
      (∫⁻ z, g z ∂μ.prod ν) = ∫⁻ s, ∫⁻ t, g (s, t) ∂ν ∂μ ∧
      (∫⁻ z, g z ∂μ.prod ν) = ∫⁻ t, ∫⁻ s, g (s, t) ∂μ ∂ν) ∧
    ((∀ᵐ s ∂μ, Integrable (fun t => f (s, t)) ν) ∧
      (∀ᵐ t ∂ν, Integrable (fun s => f (s, t)) μ) ∧
      (∫ z, f z ∂μ.prod ν) = ∫ s, ∫ t, f (s, t) ∂ν ∂μ ∧
      (∫ z, f z ∂μ.prod ν) = ∫ t, ∫ s, f (s, t) ∂μ ∂ν) := by
  refine ⟨⟨hg.lintegral_prod_right', hg.lintegral_prod_left', ?_, ?_⟩,
    ⟨hf.prod_right_ae, hf.prod_left_ae, ?_, ?_⟩⟩
  · exact _root_.MeasureTheory.lintegral_prod g hg.aemeasurable
  · exact _root_.MeasureTheory.lintegral_prod_symm g hg.aemeasurable
  · exact _root_.MeasureTheory.integral_prod f hf
  · exact _root_.MeasureTheory.integral_prod_symm f hf

/--
Original label: `defn:markov-kernel`.

Informal statement: a Markov kernel from `S` to `T` is a measurable family
`s ↦ Q(s, ·)` of probability measures on `T`.

Lean strategy / thesis relation note: Mathlib's `Kernel S T` makes every
evaluation `s ↦ Q s B` measurable for measurable `B`, and
`IsMarkovKernel Q` asserts that every fibre is a probability measure.  The
subtype below bundles exactly those two thesis clauses.
-/
abbrev MarkovKernel
    (S : Type u) (T : Type v) [MeasurableSpace S] [MeasurableSpace T] :=
  {Q : Kernel S T // IsMarkovKernel Q}

/--
Original label: `thm:measure-disintegration`.

Informal statement: a finite measure `Λ` on `S × T`, with standard-Borel
target `T`, admits a Markov kernel `Q` such that the first marginal composed
with `Q` recovers `Λ`; the kernel is unique almost everywhere for the first
marginal.

Lean strategy / thesis relation note: Mathlib constructs `Λ.condKernel` for a
finite product measure with standard-Borel second coordinate.  Its
`disintegrate` theorem is equality of whole measures, stronger than checking
rectangles one at a time.  `eq_condKernel_of_measure_eq_compProd` supplies the
thesis's almost-everywhere uniqueness clause.
-/
theorem measureDisintegration
    {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]
    (Λ : Measure (S × T)) [IsFiniteMeasure Λ] :
    IsMarkovKernel Λ.condKernel ∧
      Λ.fst ⊗ₘ Λ.condKernel = Λ ∧
      ∀ Q : Kernel S T, IsFiniteKernel Q →
        Λ.fst ⊗ₘ Q = Λ → Q =ᵐ[Λ.fst] Λ.condKernel := by
  refine ⟨inferInstance, Λ.disintegrate Λ.condKernel, ?_⟩
  intro Q hQ hdis
  letI : IsFiniteKernel Q := hQ
  exact ProbabilityTheory.eq_condKernel_of_measure_eq_compProd Q hdis.symm

/--
Original label: `thm:regular-conditional-distribution`.

Informal statement: standard-Borel random elements `X : Ω → S` and
`Y : Ω → T` have a regular conditional distribution of `X` given `Y`, unique
up to the law of `Y`; its kernel disintegrates the joint law of `(Y, X)`.

Lean strategy / thesis relation note: apply Mathlib's standard-Borel
conditional-kernel construction to the pushed-forward joint law
`P.map (Y, X)`.  The resulting equality of measures implies the thesis's
rectangle probability formula and, by integration, the bounded-measurable
conditional-expectation identity. `ConditionalDistribution.lean` proves those
two consequences explicitly together with almost-everywhere uniqueness.
-/
theorem regularConditionalDistribution
    {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y) :
    ∃ Q : Kernel T S, IsMarkovKernel Q ∧
      (P.map fun ω => (Y ω, X ω)).fst ⊗ₘ Q = P.map fun ω => (Y ω, X ω) := by
  letI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  letI : Nonempty S := Nonempty.map X inferInstance
  let ρ : Measure (T × S) := P.map fun ω => (Y ω, X ω)
  have hpair : Measurable fun ω => (Y ω, X ω) := hY.prodMk hX
  letI : IsFiniteMeasure ρ := by
    dsimp [ρ]
    infer_instance
  refine ⟨ρ.condKernel, inferInstance, ?_⟩
  simpa only [ρ] using ρ.disintegrate ρ.condKernel

/--
Original label: `defn:simple-function`.

Informal statement: a simple measurable function takes finitely many vector
values on measurable fibres, equivalently it can be written as a finite sum of
measurable-set indicators times those values.

Lean strategy / thesis relation note: Mathlib's `SimpleFunc Ω V` is a
measurable function with finite range.  Its fibre decomposition gives the
indicator-sum representation in the thesis, while repeated values or
overlapping presentations are canonically refined to measurable fibres.
-/
abbrev SimpleMeasurableFunction
    (Ω : Type u) (V : Type v) [MeasurableSpace Ω] :=
  SimpleFunc Ω V

/--
Original label: `defn:bochner-integral`.

Informal statement: the Bochner integral of an integrable Banach-valued
function is the limit of the integrals of simple functions converging in
integrated norm; for a simple partition it is the corresponding weighted
finite sum.

Lean strategy / thesis relation note: Mathlib's `MeasureTheory.integral` is
the Bochner integral.  Its implementation passes through `L¹`, built as the
completion of integrable simple functions, and proves partition independence
and convergence.  The wrapper keeps the thesis name; Mathlib totalises it to
zero outside `Integrable f`, while the thesis uses it only under integrability.
`BochnerConstruction.lean` proves the simple-approximation criterion, existence
and independence of the limit, and the finite indicator-sum formulas explicitly.
-/
noncomputable def bochnerIntegral
    {Ω : Type u} {V : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure Ω) (f : Ω → V) : V :=
  ∫ ω, f ω ∂μ

/--
Original label: `prop:bochner-integrability`.

Informal statement: for a measurable function into a separable Banach space,
Bochner integrability is equivalent to scalar integrability of its norm.

Lean strategy / thesis relation note: `AEStronglyMeasurable f μ` is the exact
measurability hypothesis used in Mathlib's Bochner theory; ordinary Borel
measurability into a separable Banach space implies it.  Mathlib's
`integrable_norm_iff` then gives the norm criterion directly, with scalar
`Integrable` equivalent to finiteness of the integral of the nonnegative norm.
-/
theorem bochnerIntegrable_iff_norm
    {Ω : Type u} {V : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup V]
    (μ : Measure Ω) {f : Ω → V} (hf : AEStronglyMeasurable f μ) :
    Integrable f μ ↔ Integrable (fun ω => ‖f ω‖) μ :=
  (_root_.MeasureTheory.integrable_norm_iff hf).symm

/--
Original label: `defn:expected-value`.

Informal statement: the expected value of a Bochner-integrable Banach-valued
random element `X` is its Bochner integral with respect to the probability
measure.

Lean strategy / thesis relation note: expectation is definitionally the same
Mathlib Bochner integral used above, specialised to a measure carrying
`IsProbabilityMeasure`.  The `Integrable X P` hypothesis is accepted to retain
the thesis's domain of definition even though Mathlib totalises the integral.
-/
noncomputable def expectedValue
    {Ω : Type u} {V : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → V) (_hX : Integrable X P) : V :=
  ∫ ω, X ω ∂P

/-- Original label: `defn:lp-spaces`.
Mathlib's carrier is the a.e. quotient; it uses the essential supremum at
exponent infinity and inherits pointwise linear operations. -/
abbrev LpSpace {Ω : Type u} {V : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup V] (μ : Measure Ω) (p : ℝ≥0∞) := Lp V p μ

/--
Original label: `prop:lp-banach`.

Informal statement: `L^p(Ω, μ; V)` is Banach for every `1 ≤ p ≤ ∞` when `V`
is Banach; if `H` is a real Hilbert space, then `L²(Ω, μ; H)` is Hilbert with
inner product equal to the integral of the pointwise inner product.

Lean strategy / thesis relation note: Mathlib's `Lp V p μ` is already the
almost-everywhere quotient from the thesis.  Its `CompleteSpace` instance
proves the Banach clause for every extended exponent with `1 ≤ p`, including
`∞`.  `MeasureTheory.L2.innerProductSpace` and `L2.inner_def` give the Hilbert
structure and exact displayed inner-product formula.
-/
theorem lpBanach_l2Hilbert
    {Ω : Type u} {V : Type v} {H : Type w} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (Lp V p μ) ∧
      ∀ f g : Lp H 2 μ,
        inner ℝ f g = ∫ ω, inner ℝ (f ω) (g ω) ∂μ := by
  refine ⟨inferInstance, ?_⟩
  intro f g
  exact _root_.MeasureTheory.L2.inner_def f g

/-- Right-continuity with left limits on a set, the path regularity called càdlàg. -/
def IsCadlagOn {V : Type v} [TopologicalSpace V]
    (f : ℝ → V) (s : Set ℝ) : Prop :=
  (∀ x ∈ s, ContinuousWithinAt f (s ∩ Ici x) x) ∧
    ∀ x ∈ s, ∃ y : V, Tendsto f (𝓝[s ∩ Iio x] x) (𝓝 y)

/-- Left-continuity with right limits on a set, the path regularity called càglàd. -/
def IsCagladOn {V : Type v} [TopologicalSpace V]
    (f : ℝ → V) (s : Set ℝ) : Prop :=
  (∀ x ∈ s, ContinuousWithinAt f (s ∩ Iic x) x) ∧
    ∀ x ∈ s, ∃ y : V, Tendsto f (𝓝[s ∩ Ioi x] x) (𝓝 y)

/--
Original label: `prop:cadlag-caglad-l2`.

Informal statement: a continuous, càdlàg, or càglàd path with values in a
separable real Banach space belongs to `L²` on every compact real interval.

Lean strategy / thesis relation note: `MemLp f 2 (volume.restrict (Icc a b))`
is the thesis membership statement, expressed on `ℝ` with the measure
restricted to `[a,b]` rather than changing to a subtype. One-sided continuity
makes inverse images of open sets measurable. The two one-sided limits give
local boundedness, and compactness gives a uniform bound. These facts imply
`MemLp` for any exponent on this finite measure space. The càglàd case uses
the same argument with the order reversed.
-/
theorem regularPath_memLp_two
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V]
    {a b : ℝ} (_hab : a < b) (f : ℝ → V) :
    (ContinuousOn f (Icc a b) ∨ IsCadlagOn f (Icc a b) ∨ IsCagladOn f (Icc a b)) →
      MemLp f 2 (volume.restrict (Icc a b)) := by
  intro h
  rcases h with hc | hr | hl
  · exact RegularPaths.memLp_restrict_of_right_continuous_left_limits
      isCompact_Icc measurableSet_Icc
      (fun x hx => (hc x hx).mono inter_subset_left)
      (fun x hx => ⟨f x, (hc x hx).mono inter_subset_left⟩) 2
  · exact RegularPaths.memLp_restrict_of_right_continuous_left_limits
      isCompact_Icc measurableSet_Icc hr.1 hr.2 2
  · exact RegularPaths.memLp_restrict_of_left_continuous_right_limits
      isCompact_Icc measurableSet_Icc hl.1 hl.2 2

/--
Original label: `defn:finite-integer-valued-measures`.

Informal statement: `𝓜(X)` is the type of finite Borel measures, `𝓝(X)` its
integer-valued subspace, `𝓟(X)` the probability measures, and a Borel measure
is locally finite when every point has an open neighbourhood of finite mass.

Lean strategy / thesis relation note: Mathlib's `FiniteMeasure X` and
`ProbabilityMeasure X` are the first and third spaces.  The companion
definitions immediately below form the natural-number-valued subtype and
alias `IsLocallyFiniteMeasure`, whose neighbourhood definition is exactly the
thesis clause and which has an equivalent open-neighbourhood theorem.
-/
abbrev FiniteMeasures (X : Type u) [MeasurableSpace X] := FiniteMeasure X

/-- A finite measure whose value on every measurable set is a natural number. -/
def IsIntegerValuedFiniteMeasure
    {X : Type u} [MeasurableSpace X] (μ : FiniteMeasures X) : Prop :=
  ∀ B : Set X, MeasurableSet B → ∃ n : ℕ, (μ : Measure X) B = n

/-- The thesis space `𝓝(X)` of finite integer-valued measures. -/
abbrev FiniteIntegerMeasures (X : Type u) [MeasurableSpace X] :=
  {μ : FiniteMeasures X // IsIntegerValuedFiniteMeasure μ}

/-- The thesis space `𝓟(X)` of probability measures. -/
abbrev ProbabilityMeasures (X : Type u) [MeasurableSpace X] := ProbabilityMeasure X

/-- Mathlib's neighbourhood formulation of local finiteness. -/
abbrev IsLocallyFiniteBorelMeasure
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) :=
  IsLocallyFiniteMeasure μ

/-- The finite-measure space equipped with Mathlib's Lévy--Prokhorov distance. -/
abbrev ProkhorovFiniteMeasures (X : Type u) [MeasurableSpace X] :=
  _root_.MeasureTheory.LevyProkhorov (FiniteMeasures X)

/--
Original label: `thm:prokhorov-metric`.

Informal statement: on a complete separable metric space, the Prokhorov
distance is a genuine complete separable metric on finite Borel measures and
metrises weak convergence; it restricts to probability and integer-valued
finite measures.

Lean strategy / thesis relation note: the exact Prokhorov distance separates
finite Borel measures, metrizes weak convergence, and has a separable space
of finite measures. Uniform tightness of Cauchy sequences and Prokhorov
compactness prove completeness. This wrapper combines the four proved
clauses without any project-specific axioms.
-/
theorem prokhorovMetricTheorem
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    (∀ μ ν : ProkhorovFiniteMeasures X, dist μ ν = 0 ↔ μ = ν) ∧
      CompleteSpace (ProkhorovFiniteMeasures X) ∧
      TopologicalSpace.SeparableSpace (ProkhorovFiniteMeasures X) ∧
      ∀ (μ : ℕ → FiniteMeasures X) (ν : FiniteMeasures X),
        Tendsto (fun n =>
          _root_.MeasureTheory.LevyProkhorov.ofMeasure (μ n)) atTop
            (𝓝 (_root_.MeasureTheory.LevyProkhorov.ofMeasure ν)) ↔
          Tendsto μ atTop (𝓝 ν) :=
  ⟨Stochastic.FiniteMeasureProkhorov.dist_eq_zero_iff,
    External.prokhorovFiniteMeasures_complete_polish,
    Stochastic.FiniteMeasureDensity.separableSpace,
    fun _ _ => Stochastic.FiniteMeasureProkhorov.tendsto_iff⟩

/-- Original label: `thm:prokhorov-metric`, restrictions to probability and
integer-valued finite measures. The probability subspace is the closed
mass-one level set; the integer subspace uses compact atomic parameters. -/
theorem prokhorovMetricTheorem_restrictions
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    CompleteSpace (_root_.MeasureTheory.LevyProkhorov (ProbabilityMeasure X)) ∧
      TopologicalSpace.SeparableSpace
        (_root_.MeasureTheory.LevyProkhorov (ProbabilityMeasure X)) ∧
      CompleteSpace (Stochastic.PointProcesses.ProkhorovFiniteIntegerMeasures X) ∧
      TopologicalSpace.SeparableSpace
        (Stochastic.PointProcesses.ProkhorovFiniteIntegerMeasures X) :=
  ⟨Stochastic.FiniteMeasureCompleteness.probability_completeSpace,
    Stochastic.FiniteMeasureCompleteness.probability_separableSpace,
    Stochastic.IntegerMeasureCompleteness.completeSpace,
    Stochastic.IntegerMeasureSeparability.separableSpace⟩

/--
Original label: `defn:kallenberg-random-measure`.

Informal statement: a finite random measure is a family of finite measures
`ω ↦ ξ(ω, ·)` whose evaluation `ω ↦ ξ(ω,B)` is measurable for every measurable
`B`; it is integer-valued when every fibre has natural-number set masses.

Lean strategy / thesis relation note: a Mathlib `Kernel Ω X` is exactly a
measurable family of measures, and its `measurable_coe` theorem is the first
thesis clause.  The field `finite` imposes pointwise finiteness without the
stronger uniform bound required by Mathlib's `IsFiniteKernel`.  The companion
predicate below records integer-valuedness fibre by fibre.
-/
structure RandomFiniteMeasure
    (Ω : Type u) (X : Type v) [MeasurableSpace Ω] [MeasurableSpace X] where
  toKernel : Kernel Ω X
  finite : ∀ ω, IsFiniteMeasure (toKernel ω)

/-- A random finite measure whose every fibre is integer-valued. -/
def IsIntegerValuedRandomMeasure
    {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (ξ : RandomFiniteMeasure Ω X) : Prop :=
  ∀ ω B, MeasurableSet B → ∃ n : ℕ, ξ.toKernel ω B = n

/-- Pointwise conversion of a random finite measure into `FiniteMeasure X`. -/
def RandomFiniteMeasure.toFiniteMeasure
    {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (ξ : RandomFiniteMeasure Ω X) (ω : Ω) : FiniteMeasure X :=
  ⟨ξ.toKernel ω, ξ.finite ω⟩

/-- Evaluation measurability of a finite-measure-valued function. -/
def IsEvaluationMeasurable
    {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Ω → FiniteMeasure X) : Prop :=
  ∀ B : Set X, MeasurableSet B → Measurable fun ω => ((Ξ ω : FiniteMeasure X) : Measure X) B

/-- Measurability into the Borel space generated by the Prokhorov metric. -/
def IsProkhorovBorelMeasurable
    {Ω : Type u} {X : Type v} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Ξ : Ω → FiniteMeasure X) : Prop :=
  @Measurable Ω (ProkhorovFiniteMeasures X) _
    (borel (ProkhorovFiniteMeasures X))
    (fun ω => _root_.MeasureTheory.LevyProkhorov.ofMeasure (Ξ ω))

/--
Original block id: `source:A - appendices/measure.tex:438:prop:25`.

Informal statement: on finite Borel measures over a Polish space, a
measure-valued map is measurable for the Prokhorov Borel sigma-algebra if and
only if every measurable-set evaluation is measurable; hence the kernel and
random-element formulations of a finite random measure are equivalent.

Lean strategy / thesis relation note: `IsEvaluationMeasurable` is the Giry
evaluation sigma-algebra used by Mathlib's `FiniteMeasure`, while
`IsProkhorovBorelMeasurable` explicitly installs the Borel sigma-algebra of
Mathlib's Lévy--Prokhorov pseudometric. The proof first identifies weak and
Prokhorov topologies and establishes separability. A basis of bounded
continuous integral tests makes weak open sets evaluation-measurable.
Portmanteau gives Borel measurability of closed-set evaluations; a pi-system
argument extends this to every Borel set.
-/
theorem randomMeasure_iff_prokhorovMeasurable
    {Ω : Type u} {X : Type v} [MeasurableSpace Ω]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (Ξ : Ω → FiniteMeasure X) :
    IsEvaluationMeasurable Ξ ↔ IsProkhorovBorelMeasurable Ξ :=
  Stochastic.FiniteMeasureBorel.measurable_iff Ξ

/--
Original label: `prop:mean-measure`.

Informal statement: if a finite random measure has integrable total mass,
then `B ↦ E[ξ(B)]` is a finite measure, called its mean measure.

Lean strategy / thesis relation note: compose the kernel `ξ.toKernel` with the
probability measure using Mathlib's measure--kernel composition `∘ₘ`.  The
`Measure.bind_apply` formula is exactly expectation of each evaluation.  The
assumed finite integral of the total mass proves finiteness at `univ`, allowing
the result to be bundled as `FiniteMeasure X`.
-/
theorem meanMeasure_exists
    {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : RandomFiniteMeasure Ω X)
    (htotal : (∫⁻ ω, ξ.toKernel ω univ ∂P) < ∞) :
    ∃ ν : FiniteMeasure X, ∀ B : Set X, MeasurableSet B →
      (ν : Measure X) B = ∫⁻ ω, ξ.toKernel ω B ∂P := by
  let ν : Measure X := ξ.toKernel ∘ₘ P
  have hν : IsFiniteMeasure ν := by
    constructor
    simpa only [ν, Measure.bind_apply MeasurableSet.univ ξ.toKernel.aemeasurable] using htotal
  refine ⟨⟨ν, hν⟩, ?_⟩
  intro B hB
  exact Measure.bind_apply hB ξ.toKernel.aemeasurable

end MeasureTheory
end Preliminary
end Foundations
end Thesis
