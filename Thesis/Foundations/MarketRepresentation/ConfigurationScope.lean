import Thesis.Context.ThesisContext
import Thesis.Foundations.MarketRepresentation.MetricSourceProofs
import Mathlib.Analysis.SpecificLimits.Basic

/-! The agent-quotient and unordered-configuration modelling remarks. -/

noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.MarketRepresentation.ConfigurationScope

open TuplesBasic FiniteSets FiniteSets.FiniteSubsets ThesisContext
open Thesis.Foundations.MarketClearing.Sorting
universe u v

/-- Original block id:
`source:1 - theoretical foundations/2_chapter_market_representations.tex:350:rem:18`.
Different submitting agents have the same visible order and the same kernel
class. Pulling back a reflexive quotient order is therefore not antisymmetric
on the original labelled submissions. -/
theorem equal_view_distinct_agents {A : Type u} (o : OrderSide × (ℝ × Quantity))
    (a b : A) (hab : a ≠ b) (r : (OrderSide × (ℝ × Quantity)) →
      (OrderSide × (ℝ × Quantity)) → Prop) (hr : ∀ o, r o o) :
    marketView (o, a) = marketView (o, b) ∧
    (o, a) ≠ (o, b) ∧ r (marketView (o, a)) (marketView (o, b)) ∧
      r (marketView (o, b)) (marketView (o, a)) := by
  exact ⟨rfl, fun h ↦ hab (congrArg Prod.snd h), hr o, hr o⟩

/-- Equal visible submissions with distinct agents collapse to a single
visible set element; the original two-element set still has cardinality two. -/
theorem quotient_forgets_multiplicity {A : Type u} (o : OrderSide × (ℝ × Quantity))
    (a b : A) (hab : a ≠ b) :
    ({(o, a), (o, b)} : Set (AgentLabelledOrder A)).ncard = 2 ∧
      marketView '' ({(o, a), (o, b)} : Set (AgentLabelledOrder A)) = {o} := by
  constructor
  · exact Set.ncard_pair (fun h ↦ hab (congrArg Prod.snd h))
  · ext z
    simp [marketView, eq_comm]

/-- Institutional priority can retain the agent coordinate in a lexicographic
total order, rather than identifying its fibres. -/
theorem agent_priority_lex_total {Y : Type u} {A : Type v}
    [LinearOrder Y] [LinearOrder A] (x y : Y × A) :
    toLex x ≤ toLex y ∨ toLex y ≤ toLex x := le_total _ _

theorem agent_priority_lex_antisymm {Y : Type u} {A : Type v}
    [LinearOrder Y] [LinearOrder A] {x y : Y × A}
    (hxy : toLex x ≤ toLex y) (hyx : toLex y ≤ toLex x) : x = y := by
  exact congrArg ofLex (le_antisymm hxy hyx)

/-- The union of authorisations does not determine which agent is allowed
to submit a given visible payload. -/
theorem authorization_union_loses_agent_information :
    ∃ S T : Bool → Set Unit, (⋃ a, S a) = (⋃ a, T a) ∧ S false ≠ T false := by
  refine ⟨fun _ ↦ Set.univ, fun a ↦ if a then Set.univ else ∅, ?_, ?_⟩
  · ext x
    simp
  · simp

/-- Ordered configurations contain distinct points; the kernel of range
forgets exactly their enumeration, and hence multiplicity is not introduced. -/
def OrderedConfiguration (X : Type u) (n : ℕ) := {f : Fin n → X // Function.Injective f}

def configurationRange {X : Type u} {n : ℕ} (f : OrderedConfiguration X n) :
    FiniteSubsets X := ⟨Set.range f.val, Set.finite_range _⟩

def UnorderedConfiguration (X : Type u) (n : ℕ) :=
  Quotient (Setoid.ker (configurationRange (X := X) (n := n)))

/-- Equality of unordered ranges of distinct configurations is exactly
equality up to a finite permutation, so this is the usual configuration
quotient, rather than a new quotient relation. -/
theorem configuration_same_range_iff_permutation {X : Type u} {n : ℕ}
    (f g : OrderedConfiguration X n) :
    configurationRange f = configurationRange g ↔
      ∃ π : Equiv.Perm (Fin n), ∀ i, g.val (π i) = f.val i := by
  constructor
  · intro h
    have hr : Set.range f.val = Set.range g.val := congrArg Subtype.val h
    let ef := Equiv.ofInjective f.val f.property
    let eg := Equiv.ofInjective g.val g.property
    let π := (ef.trans (Equiv.setCongr hr)).trans eg.symm
    refine ⟨π, fun i ↦ ?_⟩
    have he := eg.apply_symm_apply ((Equiv.setCongr hr) (ef i))
    exact congrArg Subtype.val he
  · rintro ⟨π, hπ⟩
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨π i, hπ i⟩
    · rintro ⟨j, rfl⟩
      exact ⟨π.symm j, by simpa only [π.apply_symm_apply] using (hπ (π.symm j)).symm⟩

def configurationToFinite {X : Type u} : (Σ n, UnorderedConfiguration X n) → FiniteSubsets X
  | ⟨_, q⟩ => Quotient.lift configurationRange (fun _ _ h ↦ h) q

theorem configurationToFinite_bijective {X : Type u} :
    Function.Bijective (configurationToFinite (X := X)) := by
  constructor
  · rintro ⟨n, q⟩ ⟨m, r⟩ h
    induction q using Quotient.inductionOn with | h q =>
      induction r using Quotient.inductionOn with | h r =>
        have hcq : (configurationRange q : Set X).ncard = n := by
          simpa only [configurationRange, Nat.card_fin] using
            Set.ncard_range_of_injective q.property
        have hcr : (configurationRange r : Set X).ncard = m := by
          simpa only [configurationRange, Nat.card_fin] using
            Set.ncard_range_of_injective r.property
        have hnm : n = m := hcq.symm.trans ((congrArg (fun s : FiniteSubsets X ↦
          (s : Set X).ncard) h).trans hcr)
        subst m
        congr 1
        exact Quotient.sound h
  · intro s
    obtain ⟨n, f, hf, hfs⟩ := s.2.fin_param
    refine ⟨⟨n, Quotient.mk _ ⟨f, hf⟩⟩, ?_⟩
    exact Subtype.ext hfs

/-- Original label: `rem:unordered-configuration-space`.
As a set the finite-subset space is exactly the disjoint union of the
quotients of distinct configurations by equality of their unordered ranges. -/
def finiteSubsetsEquivConfigurations (X : Type u) :
    FiniteSubsets X ≃ Σ n, UnorderedConfiguration X n :=
  (Equiv.ofBijective configurationToFinite configurationToFinite_bijective).symm

/-- The displayed collision example, including its exact distance. -/
theorem collision_hausdorff_distance (a : ℝ) :
    Metric.hausdorffEDist ({0, a} : Set ℝ) {0} = edist a 0 := by
  apply le_antisymm
  · apply Metric.hausdorffEDist_le_of_mem_edist
    · intro x hx
      refine ⟨0, rfl, ?_⟩
      rcases hx with rfl | hx
      · simp
      · simp only [Set.mem_singleton_iff] at hx
        rw [hx]
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨0, by simp, by simp⟩
  · simpa only [Metric.infEDist_singleton] using
      (Metric.infEDist_le_hausdorffEDist_of_mem (t := ({0} : Set ℝ))
        (by simp : a ∈ ({0, a} : Set ℝ)))

def collisionSet (k : ℕ) : FiniteSubsets ℝ :=
  ⟨{0, 1 / ((k : ℝ) + 1)}, Set.toFinite _⟩

def singletonZero : FiniteSubsets ℝ := ⟨{0}, Set.finite_singleton 0⟩

/-- Original label: `rem:unordered-configuration-space`.
Distinct two-point configurations converge in Hausdorff distance to a
one-point configuration. Zero-based `k` uses the source sequence `1/(k+1)`. -/
theorem collision_converges : Tendsto collisionSet atTop (nhds singletonZero) := by
  rw [EMetric.tendsto_atTop]
  intro ε hε
  have hc : Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := (EMetric.tendsto_atTop.mp hc) ε hε
  refine ⟨N, fun k hk ↦ ?_⟩
  change Metric.hausdorffEDist ({0, _} : Set ℝ) {0} < ε
  rw [collision_hausdorff_distance]
  exact hN k hk

theorem collision_cardinality (k : ℕ) :
    (collisionSet k : Set ℝ).ncard = 2 ∧ (singletonZero : Set ℝ).ncard = 1 := by
  constructor
  · apply Set.ncard_pair
    have hp : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
    exact ne_of_lt hp
  · exact Set.ncard_singleton 0

/-- Cardinality is not locally constant for the Hausdorff topology, unlike
the configuration coproduct where the cardinality is the discrete tag. -/
theorem hausdorff_cardinality_not_continuous :
    ¬ Continuous (fun s : FiniteSubsets ℝ ↦ (s : Set ℝ).ncard) := by
  intro h
  have ht := h.continuousAt.tendsto.comp collision_converges
  have hevent : ∀ᶠ k : ℕ in atTop, (collisionSet k : Set ℝ).ncard = 1 := by
    have hopen : ({1} : Set ℕ) ∈ nhds (singletonZero : Set ℝ).ncard := by
      exact (isOpen_discrete ({1} : Set ℕ)).mem_nhds (by simp [singletonZero])
    exact ht hopen
  obtain ⟨k, hk⟩ := hevent.exists
  have hc := (collision_cardinality k).1
  omega

theorem configuration_cardinality_continuous {X : Type u}
    [∀ n, TopologicalSpace (UnorderedConfiguration X n)] :
    Continuous (Sigma.fst : (Σ n, UnorderedConfiguration X n) → ℕ) := by
  apply continuous_sigma
  intro n
  exact continuous_const

/-- Two copies of the same point remain different from one copy in the
multiset model (and hence in the symmetric-product model), but have the same
underlying finite set. -/
theorem set_erases_symmetric_product_multiplicity :
    ({(0 : ℝ), 0} : Multiset ℝ).card = 2 ∧
    ({(0 : ℝ)} : Multiset ℝ).card = 1 ∧
    ({(0 : ℝ), 0} : Multiset ℝ).toFinset = ({(0 : ℝ)} : Multiset ℝ).toFinset := by
  simp

end Thesis.Foundations.MarketRepresentation.ConfigurationScope
