import Thesis.Foundations.MarketRepresentation.FiniteSets
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite-set boundary examples from the representation chapter -/

noncomputable section

namespace Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets

open Set Filter Topology

universe u

/-- Original label: `defn:uniformly-discrete`.
Allowing an extended-real isolation bound is equivalent to a finite positive
real bound, as used in the manuscript. -/
theorem isolative_iff_real_bound {α : Type u} [EDist α] :
    Isolative α ↔ ∃ B : ℝ, 0 < B ∧
      ∀ x y : α, x ≠ y → ENNReal.ofReal B ≤ edist x y := by
  constructor
  · rintro ⟨B, hBpos, hB⟩
    obtain ⟨δ, hδ, hδ1, hδB⟩ := exists_pos_le_one_lt_ennreal hBpos
    have hδtop : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hδ1
    refine ⟨δ.toReal, ENNReal.toReal_pos (ne_of_gt hδ) hδtop, ?_⟩
    intro x y hxy
    rw [ENNReal.ofReal_toReal hδtop]
    exact hδB.le.trans (hB x y hxy)
  · rintro ⟨B, hBpos, hB⟩
    exact ⟨ENNReal.ofReal B, ENNReal.ofReal_pos.mpr hBpos, hB⟩

/-- Original label: `prop:finite-hausdorff-uniformly-discrete`.
The exact supplied bound is retained, not just existence of some new bound. -/
theorem finiteSubsets_same_isolation_bound {α : Type u} [PseudoEMetricSpace α]
    {B : ENNReal} (hB : ∀ x y : α, x ≠ y → B ≤ edist x y)
    (s t : FiniteSubsets α) (hne : s ≠ t) : B ≤ edist s t := by
  have hset : (s : Set α) ≠ (t : Set α) := fun h => hne (Subtype.ext h)
  by_cases hst : (s : Set α) ⊆ (t : Set α)
  · have hts : ¬ (t : Set α) ⊆ (s : Set α) := fun h => hset (Subset.antisymm hst h)
    obtain ⟨x, hxt, hxs⟩ := Set.not_subset.mp hts
    rw [edist_comm]
    exact hausdorffEDistance_lower_bound_of_mem_notMem hB hxt hxs
  · obtain ⟨x, hxs, hxt⟩ := Set.not_subset.mp hst
    exact hausdorffEDistance_lower_bound_of_mem_notMem hB hxs hxt

/-- Original label: `rem:hausdorff-infinite-values`.
On nonempty finite subsets of a finite-valued metric space, the Hausdorff
distance gives an ordinary metric with the same topology and uniformity. -/
@[implicit_reducible]
def nonemptyFiniteSubsetsMetricSpace (α : Type u) [MetricSpace α] :
    MetricSpace {s : FiniteSubsets α // (s : Set α).Nonempty} :=
  EMetricSpace.toMetricSpace fun s t =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded s.property t.property
      s.val.property.isBounded t.val.property.isBounded

/-- Original label: `prop:finite-sets-over-finite-set`.
Literal equality of families in the finite-base proposition. -/
theorem finite_subsets_eq_powerset {α : Type u} {s : Set α} (hs : s.Finite) :
    {t : Set α | t ⊆ s ∧ t.Finite} = 𝒫 s := by
  ext t
  exact ⟨fun h => h.1, fun h => ⟨h, hs.subset h⟩⟩

/-- A point occurring in every sufficiently late prefix belongs to any finite
Hausdorff limit. -/
theorem range_subset_of_finitePrefix_tendsto {α : Type u} [EMetricSpace α]
    (x : ℕ → α) (s : FiniteSubsets α)
    (hs : Tendsto (finitePrefix x) atTop (𝓝 s)) : range x ⊆ (s : Set α) := by
  rintro _ ⟨i, rfl⟩
  apply (Metric.mem_iff_infEDist_zero_of_closed (isClosed_coe s)).mpr
  apply le_antisymm _ bot_le
  have hd : Tendsto (fun n => edist (finitePrefix x n) s) atTop (𝓝 0) := by
    simpa using hs.edist (tendsto_const_nhds : Tendsto (fun _ : ℕ => s) atTop (𝓝 s))
  apply ge_of_tendsto hd
  filter_upwards [eventually_ge_atTop i] with n hn
  exact Metric.infEDist_le_hausdorffEDist_of_mem (finitePrefix_mem_of_le x hn)

theorem injective_finitePrefix_has_no_limit {α : Type u} [EMetricSpace α]
    (x : ℕ → α) (hx : Function.Injective x) :
    ¬ ∃ s : FiniteSubsets α, Tendsto (finitePrefix x) atTop (𝓝 s) := by
  rintro ⟨s, hs⟩
  exact (Set.infinite_range_of_injective hx)
    (s.property.subset (range_subset_of_finitePrefix_tendsto x s hs))

def reciprocalSequence (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem reciprocalSequence_injective : Function.Injective reciprocalSequence := by
  intro n m h
  have hnm : (n : ℝ) + 1 = (m : ℝ) + 1 := by
    simpa only [reciprocalSequence, one_div, inv_inj] using h
  exact_mod_cast (add_right_cancel hnm)

/-- The manuscript's reciprocal-prefix example is Cauchy but has no finite-set limit. -/
theorem reciprocalPrefixes_cauchy_without_limit :
    CauchySeq (finitePrefix reciprocalSequence) ∧
      ¬ ∃ s : FiniteSubsets ℝ, Tendsto (finitePrefix reciprocalSequence) atTop (𝓝 s) := by
  constructor
  · apply finitePrefix_cauchySeq
    exact (show Tendsto reciprocalSequence atTop (𝓝 0) from
      tendsto_one_div_add_atTop_nhds_zero_nat).cauchySeq
  · exact injective_finitePrefix_has_no_limit reciprocalSequence reciprocalSequence_injective

theorem real_finiteSubsets_not_complete : ¬ CompleteSpace (FiniteSubsets ℝ) := by
  intro h
  letI := h
  exact reciprocalPrefixes_cauchy_without_limit.2
    (cauchySeq_tendsto_of_complete reciprocalPrefixes_cauchy_without_limit.1)

end Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
