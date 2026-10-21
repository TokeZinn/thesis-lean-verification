import Thesis.Foundations.Stochastic.PointProcesses
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Regular

/-! # Finite integer measures are finite sums of point masses

Integer-valued mass is separated from zero. Outer regularity therefore puts
every support point at a singleton of mass at least one. Finiteness of the
total mass makes this support finite; evaluating its singletons supplies the
positive integer weights.
-/

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal BigOperators

namespace Thesis.Foundations.Stochastic.AtomicDecompositionProof

open PointProcesses

universe u

theorem toMeasure_nat {X : Type u} [MeasurableSpace X]
    (μ : FiniteIntegerMeasures X) {B : Set X} (hB : MeasurableSet B) :
    ∃ n : ℕ, (μ.1 : Measure X) B = n := by
  obtain ⟨n, hn⟩ := μ.property B hB
  refine ⟨n, ?_⟩
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hn]
  simp

theorem one_le_of_pos {X : Type u} [MeasurableSpace X]
    (μ : FiniteIntegerMeasures X) {B : Set X} (hB : MeasurableSet B)
    (hpos : 0 < (μ.1 : Measure X) B) : 1 ≤ (μ.1 : Measure X) B := by
  obtain ⟨n, hn⟩ := toMeasure_nat μ hB
  rw [hn] at hpos ⊢
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hpos))

theorem finite_positive_singletons {X : Type u} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : FiniteIntegerMeasures X) :
    {x : X | 0 < (μ.1 : Measure X) {x}}.Finite := by
  by_contra h
  have hi : {x : X | 0 < (μ.1 : Measure X) {x}}.Infinite := h
  have htop := hi.meas_eq_top (μ := (μ.1 : Measure X))
    ⟨1, one_ne_zero, fun x hx => one_le_of_pos μ (measurableSet_singleton x) hx⟩
  exact measure_ne_top (μ.1 : Measure X) _ htop

theorem ae_positive_singletons {X : Type u} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : FiniteIntegerMeasures X) :
    ∀ᵐ x ∂(μ.1 : Measure X), 0 < (μ.1 : Measure X) {x} := by
  letI := upgradeStandardBorel X
  filter_upwards [(μ.1 : Measure X).support_mem_ae] with x hx
  by_contra hn
  have hz : (μ.1 : Measure X) {x} = 0 := le_antisymm (not_lt.mp hn) (zero_le _)
  obtain ⟨U, hxU, hU, hmass⟩ := ({x} : Set X).exists_isOpen_lt_of_lt
    (μ := (μ.1 : Measure X)) 1 (by simp [hz])
  have hpos := (Measure.mem_support_iff_forall x).mp hx U
    (hU.mem_nhds (hxU (mem_singleton x)))
  exact (not_le_of_gt hmass) (one_le_of_pos μ hU.measurableSet hpos)

/-- Original label: `thm:sufficient-decomposition`.
Existence with finite support, positive natural weights, and distinct atoms. -/
theorem exists_atomicDecomposition {X : Type u} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : FiniteIntegerMeasures X) :
    Nonempty (AtomicDecomposition μ) := by
  classical
  let S : Finset X := (finite_positive_singletons μ).toFinset
  have hS (x : X) : x ∈ S ↔ 0 < (μ.1 : Measure X) {x} := by
    simp [S]
  have hae : ∀ᵐ x ∂(μ.1 : Measure X), x ∈ S :=
    (ae_positive_singletons μ).mono fun x hx => (hS x).mpr hx
  have hsum := Measure.ae_mem_finset_iff.mp hae
  choose w hw using fun x : S => toMeasure_nat μ (measurableSet_singleton x.val)
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨{
    length := Fintype.card S
    atom := fun i => (e i).val
    multiplicity := fun i => w (e i)
    multiplicity_pos := ?_
    atom_injective := ?_
    represents := ?_ }⟩
  · intro i
    have hpos := (hS (e i).val).mp (e i).property
    rw [hw] at hpos
    exact_mod_cast hpos
  · exact Subtype.val_injective.comp e.injective
  · apply FiniteMeasure.eq_of_forall_toMeasure_apply_eq
    intro B hB
    rw [finiteAtomicMeasure_toMeasure_apply _ _ hB]
    calc
      (∑ i, (↑(B.indicator (fun _ => (w (e i) : ℝ≥0)) (e i).val) : ℝ≥0∞)) =
          ∑ x : S, if x.val ∈ B then (μ.1 : Measure X) {x.val} else 0 := by
        rw [← e.sum_comp]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : (e i).val ∈ B <;> simp [hi, hw]
      _ = (μ.1 : Measure X) B := by
        calc
          _ = (∑ a ∈ S, (μ.1 : Measure X) {a} • Measure.dirac a) B := by
            rw [Measure.finset_sum_apply,
              Finset.sum_coe_sort S (fun x => if x ∈ B then (μ.1 : Measure X) {x} else 0)]
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x ∈ B <;> simp [Measure.smul_apply, Measure.dirac_apply' _ hB, hx]
          _ = _ := congrArg (fun ν : Measure X => ν B) hsum.symm

theorem exists_matching_atom {X : Type u} [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : FiniteIntegerMeasures X}
    (d e : AtomicDecomposition μ) (i : Fin d.length) :
    ∃ j : Fin e.length, e.atom j = d.atom i := by
  classical
  by_contra h
  push Not at h
  have hz : (μ.1 : Measure X) {d.atom i} = 0 := by
    rw [← e.represents, finiteAtomicMeasure_toMeasure_apply _ _ (measurableSet_singleton _)]
    apply Finset.sum_eq_zero
    intro j _
    simp [h j]
  have hi := atomicDecomposition_toMeasure_singleton d i
  rw [hz] at hi
  exact (Nat.ne_of_gt (d.multiplicity_pos i)) (by exact_mod_cast hi.symm)

/-- Original label: `thm:sufficient-decomposition`.
Singleton evaluation proves uniqueness of both the atoms and their weights. -/
theorem unique_up_to_permutation {X : Type u} [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : FiniteIntegerMeasures X}
    (d e : AtomicDecomposition μ) :
    ∃ hlen : d.length = e.length, ∃ σ : Equiv.Perm (Fin d.length),
      ∀ i, e.atom (Fin.cast hlen (σ i)) = d.atom i ∧
        e.multiplicity (Fin.cast hlen (σ i)) = d.multiplicity i := by
  classical
  choose g hg using exists_matching_atom d e
  have hginj : Function.Injective g := by
    intro i j hij
    apply d.atom_injective
    rw [← hg i, ← hg j, hij]
  have hgsurj : Function.Surjective g := by
    intro j
    obtain ⟨i, hi⟩ := exists_matching_atom e d j
    exact ⟨i, e.atom_injective ((hg i).trans hi)⟩
  let E : Fin d.length ≃ Fin e.length := Equiv.ofBijective g ⟨hginj, hgsurj⟩
  have hlen : d.length = e.length := by simpa using Fintype.card_congr E
  let σ : Equiv.Perm (Fin d.length) := E.trans (finCongr hlen).symm
  have hcast (i : Fin d.length) : Fin.cast hlen (σ i) = g i := by simp [σ, E]
  refine ⟨hlen, σ, fun i => ⟨by rw [hcast]; exact hg i, ?_⟩⟩
  have hw : (e.multiplicity (g i) : ℝ≥0∞) = d.multiplicity i := by
    rw [← atomicDecomposition_toMeasure_singleton e (g i), hg i,
      atomicDecomposition_toMeasure_singleton d i]
  rw [hcast]
  exact_mod_cast hw

end Thesis.Foundations.Stochastic.AtomicDecompositionProof
