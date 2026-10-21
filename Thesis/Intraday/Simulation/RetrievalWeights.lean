import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-! # Exact normalized finite-library retrieval laws

Generic finite positive-weight laws used by the current softmax policy.
The finite type indexes a supplied library support; nonnegative weights can
encode optional filtering. An empty library cannot pass the positive-mass
guard. `AnalogueAttention` supplies the current full-gate biased Euclidean
softmax; no obsolete nearest-neighbour truncation or fallback is installed.
-/

noncomputable section
namespace Thesis.Intraday.RetrievalWeights

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι]

def raw (distance gate : ι → ℝ) (offset : ℝ) (i : ι) : ℝ :=
  gate i * Real.exp (offset - distance i)

def mass (distance gate : ι → ℝ) (offset : ℝ) : ℝ := ∑ i, raw distance gate offset i

def weight (distance gate : ι → ℝ) (offset : ℝ) (i : ι) : ℝ :=
  raw distance gate offset i / mass distance gate offset

omit [Fintype ι] in
theorem raw_nonneg (distance gate : ι → ℝ) (offset : ℝ)
    (hg : ∀ i, 0 ≤ gate i) (i : ι) : 0 ≤ raw distance gate offset i :=
  mul_nonneg (hg i) (Real.exp_pos _).le

theorem mass_nonneg (distance gate : ι → ℝ) (offset : ℝ)
    (hg : ∀ i, 0 ≤ gate i) : 0 ≤ mass distance gate offset :=
  Finset.sum_nonneg fun i _ => raw_nonneg distance gate offset hg i

theorem mass_pos_iff (distance gate : ι → ℝ) (offset : ℝ)
    (hg : ∀ i, 0 ≤ gate i) : 0 < mass distance gate offset ↔ ∃ i, 0 < gate i := by
  rw [mass, Finset.sum_pos_iff_of_nonneg (fun i _ => raw_nonneg distance gate offset hg i)]
  simp only [Finset.mem_univ, true_and, raw, mul_pos_iff_of_pos_right (Real.exp_pos _)]

theorem weight_nonneg (distance gate : ι → ℝ) (offset : ℝ)
    (hg : ∀ i, 0 ≤ gate i) (i : ι) : 0 ≤ weight distance gate offset i :=
  div_nonneg (raw_nonneg distance gate offset hg i) (mass_nonneg distance gate offset hg)

theorem sum_weight (distance gate : ι → ℝ) (offset : ℝ)
    (hm : 0 < mass distance gate offset) : ∑ i, weight distance gate offset i = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (ne_of_gt hm)

theorem weight_le_one (distance gate : ι → ℝ) (offset : ℝ)
    (hg : ∀ i, 0 ≤ gate i) (hm : 0 < mass distance gate offset) (i : ι) :
    weight distance gate offset i ≤ 1 := by
  rw [← sum_weight distance gate offset hm]
  exact Finset.single_le_sum (fun j _ => weight_nonneg distance gate offset hg j)
    (Finset.mem_univ i)

omit [Fintype ι] in
theorem raw_shift (distance gate : ι → ℝ) (offset : ℝ) (i : ι) :
    raw distance gate offset i = Real.exp offset * raw distance gate 0 i := by
  simp only [raw, sub_eq_add_neg, Real.exp_add, Real.exp_zero, one_mul]
  ring

theorem mass_shift (distance gate : ι → ℝ) (offset : ℝ) :
    mass distance gate offset = Real.exp offset * mass distance gate 0 := by
  simp only [mass, raw_shift distance gate offset, Finset.mul_sum]

/-- Subtracting the minimum distance stabilizes exponents and leaves the exact
probabilities unchanged. The identity holds for every common offset. -/
theorem weight_shift (distance gate : ι → ℝ) (offset : ℝ) (i : ι) :
    weight distance gate offset i = weight distance gate 0 i := by
  rw [weight, raw_shift, mass_shift]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero offset)

omit [Fintype ι] in
theorem stable_exponential_bounds (distance : ι → ℝ) (offset : ℝ)
    (hmin : ∀ i, offset ≤ distance i) (i : ι) :
    0 < Real.exp (-(distance i - offset)) ∧ Real.exp (-(distance i - offset)) ≤ 1 := by
  exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith [hmin i])⟩

def law (distance gate : ι → ℝ) (offset : ℝ) (hg : ∀ i, 0 ≤ gate i)
    (hm : 0 < mass distance gate offset) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (weight distance gate offset i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => weight_nonneg distance gate offset hg i),
      sum_weight distance gate offset hm, ENNReal.ofReal_one])

theorem law_apply (distance gate : ι → ℝ) (offset : ℝ) (hg : ∀ i, 0 ≤ gate i)
    (hm : 0 < mass distance gate offset) (i : ι) :
    law distance gate offset hg hm i = ENNReal.ofReal (weight distance gate offset i) := rfl

def checkedLaw (distance gate : ι → ℝ) (offset : ℝ) (hg : ∀ i, 0 ≤ gate i) :
    Option (PMF ι) :=
  if hm : 0 < mass distance gate offset then some (law distance gate offset hg hm) else none

theorem checkedLaw_none_iff (distance gate : ι → ℝ) (offset : ℝ) (hg : ∀ i, 0 ≤ gate i) :
    checkedLaw distance gate offset hg = none ↔ ∀ i, gate i = 0 := by
  simp only [checkedLaw]
  split_ifs with h
  · simp only [false_iff]
    obtain ⟨i, hi⟩ := (mass_pos_iff distance gate offset hg).mp h
    intro hz
    exact (ne_of_gt hi) (hz i)
  · simp only [true_iff]
    intro i
    have hn : ¬ ∃ i, 0 < gate i := by rwa [← mass_pos_iff distance gate offset hg]
    exact le_antisymm (le_of_not_gt (fun hi => hn ⟨i, hi⟩)) (hg i)

theorem empty_library_fails [IsEmpty ι] (distance gate : ι → ℝ) (offset : ℝ)
    (hg : ∀ i, 0 ≤ gate i) : checkedLaw distance gate offset hg = none :=
  (checkedLaw_none_iff distance gate offset hg).mpr fun i => isEmptyElim i

/-- The weighted expectation of any finite-library statistic; no moment
assumption is needed for finitely many finite-valued observations. -/
theorem expectation [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (distance gate : ι → ℝ) (offset : ℝ) (hg : ∀ i, 0 ≤ gate i)
    (hm : 0 < mass distance gate offset) (f : ι → E) :
    ∫ i, f i ∂(law distance gate offset hg hm).toMeasure =
      ∑ i, weight distance gate offset i • f i := by
  rw [PMF.integral_eq_sum]
  simp only [law_apply, ENNReal.toReal_ofReal (weight_nonneg distance gate offset hg _)]

theorem empty_burst_allowed {Action : Type*} (distance gate : ι → ℝ) (offset : ℝ)
    (hg : ∀ i, 0 ≤ gate i) (hm : 0 < mass distance gate offset)
    (burst : ι → List Action) (i : ι) (hi : 0 < gate i) (hb : burst i = []) :
    [] ∈ ((law distance gate offset hg hm).map burst).support := by
  rw [PMF.mem_support_map_iff]
  refine ⟨i, ?_, hb⟩
  change ENNReal.ofReal (weight distance gate offset i) ≠ 0
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (mul_pos hi (Real.exp_pos _)) hm

section Measurable

variable {S : Type*} [MeasurableSpace S]
variable (distance gate : S → ι → ℝ) (offset : S → ℝ)
variable (hd : ∀ i, Measurable (fun s => distance s i))
variable (hg : ∀ i, Measurable (fun s => gate s i)) (ho : Measurable offset)

include hd hg ho in
theorem measurable_weight (i : ι) :
    Measurable (fun s => weight (distance s) (gate s) (offset s) i) := by
  have hraw (j : ι) : Measurable (fun s => raw (distance s) (gate s) (offset s) j) :=
    (hg j).mul ((ho.sub (hd j)).exp)
  exact (hraw i).div (Finset.measurable_sum Finset.univ (fun j _ => hraw j))

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (hn : ∀ s i, 0 ≤ gate s i)
variable (hp : ∀ s, 0 < mass (distance s) (gate s) (offset s))

/-- A genuine measurable probability kernel for state-dependent finite-library
resampling on its positive-mass domain. -/
def indexKernel : Kernel S ι where
  toFun s := (law (distance s) (gate s) (offset s) (hn s) (hp s)).toMeasure
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro A _
    simp_rw [PMF.toMeasure_apply_fintype]
    apply Finset.measurable_sum
    intro i _
    by_cases hi : i ∈ A
    · simp only [Set.indicator_of_mem hi, law_apply]
      exact (measurable_weight distance gate offset hd hg ho i).ennreal_ofReal
    · simp only [Set.indicator_of_notMem hi]
      exact measurable_const

instance indexKernel_isMarkov : IsMarkovKernel (indexKernel distance gate offset hd hg ho hn hp) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

def markedKernel {Mark : Type*} [MeasurableSpace Mark] (atom : ι → Mark) : Kernel S Mark :=
  (indexKernel distance gate offset hd hg ho hn hp).map atom

instance markedKernel_isMarkov {Mark : Type*} [MeasurableSpace Mark] (atom : ι → Mark) :
    IsMarkovKernel (markedKernel distance gate offset hd hg ho hn hp atom) := by
  exact Kernel.IsMarkovKernel.map _ (measurable_of_finite atom)

end Measurable

end Thesis.Intraday.RetrievalWeights
