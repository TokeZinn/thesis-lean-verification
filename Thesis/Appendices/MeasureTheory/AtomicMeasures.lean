import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-! # Diffuse and purely atomic measures on arbitrary measurable spaces

Atoms here are measurable sets, not necessarily singletons. This distinction
is necessary for the general sigma-finite decomposition in the thesis.
-/

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace Thesis.Foundations.Preliminary.MeasureTheory

universe u

/-- Original label: `defn:atom-diffuse`.
A positive measurable set is an atom if every measurable cut has a null side. -/
def IsMeasureAtom {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ 0 < μ A ∧
    ∀ E : Set Ω, MeasurableSet E → min (μ (A ∩ E)) (μ (A \ E)) = 0

/-- Every positive measurable set contains a measurable atom. -/
def IsPurelyAtomic {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ∀ E : Set Ω, MeasurableSet E → 0 < μ E →
    ∃ A : Set Ω, A ⊆ E ∧ IsMeasureAtom μ A

/-- A diffuse measure has no measurable positive-mass atom. -/
def IsDiffuse {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ¬ ∃ A : Set Ω, IsMeasureAtom μ A

/-- The distinct support points and their positive singleton weights. -/
def HasCountablePointMassRepresentation
    {Ω : Type u} [MeasurableSpace Ω] (β : Measure Ω) : Prop := by
  classical
  exact ∃ I : Set Ω, I.Countable ∧
    (∀ x : I, 0 < β ({x.1} : Set Ω)) ∧
    ∀ B : Set Ω, MeasurableSet B →
      β B = ∑' x : I, if x.1 ∈ B then β ({x.1} : Set Ω) else 0

variable {Ω : Type u} [MeasurableSpace Ω] {μ ν : Measure Ω} {A B s : Set Ω}

theorem IsMeasureAtom.cut_zero (hA : IsMeasureAtom μ A) (hB : MeasurableSet B) :
    μ (A ∩ B) = 0 ∨ μ (A \ B) = 0 := by
  by_contra h
  push Not at h
  exact (ne_of_gt (lt_min (pos_iff_ne_zero.mpr h.1) (pos_iff_ne_zero.mpr h.2)))
    (hA.2.2 B hB)

theorem IsMeasureAtom.of_absolutelyContinuous (hA : IsMeasureAtom μ A)
    (hνμ : ν ≪ μ) (hpos : 0 < ν A) : IsMeasureAtom ν A := by
  refine ⟨hA.1, hpos, fun E hE => ?_⟩
  rcases hA.cut_zero hE with h | h
  · simp [hνμ h]
  · simp [hνμ h]

theorem IsMeasureAtom.subset (hA : IsMeasureAtom μ A)
    (hBA : B ⊆ A) (hB : MeasurableSet B) (hpos : 0 < μ B) : IsMeasureAtom μ B := by
  refine ⟨hB, hpos, fun E hE => ?_⟩
  rcases hA.cut_zero hE with h | h
  · have hz := measure_mono_null (inter_subset_inter_left E hBA) h
    simp [hz]
  · have hz := measure_mono_null (diff_subset_diff_left hBA) h
    simp [hz]

theorem IsMeasureAtom.of_restrict (hA : IsMeasureAtom (μ.restrict s) A)
    (hs : MeasurableSet s) : IsMeasureAtom μ (A ∩ s) := by
  refine ⟨hA.1.inter hs, ?_, fun E hE => ?_⟩
  · simpa [Measure.restrict_apply hA.1] using hA.2.1
  · have h := hA.2.2 E hE
    have hset : (A \ E) ∩ s = (A ∩ s) \ E := by ext x; simp [and_assoc, and_comm, and_left_comm]
    simpa only [Measure.restrict_apply (hA.1.inter hE),
      Measure.restrict_apply (hA.1.diff hE), inter_right_comm, hset] using h

theorem IsDiffuse.restrict (hμ : IsDiffuse μ) (hs : MeasurableSet s) :
    IsDiffuse (μ.restrict s) := by
  rintro ⟨A, hA⟩
  exact hμ ⟨A ∩ s, hA.of_restrict hs⟩

theorem IsPurelyAtomic.restrict (hμ : IsPurelyAtomic μ) (hs : MeasurableSet s) :
    IsPurelyAtomic (μ.restrict s) := by
  intro E hE hpos
  have hpos' : 0 < μ (E ∩ s) := by simpa [Measure.restrict_apply hE] using hpos
  obtain ⟨A, hAE, hA⟩ := hμ (E ∩ s) (hE.inter hs) hpos'
  refine ⟨A, hAE.trans inter_subset_left, hA.of_absolutelyContinuous
    Measure.restrict_le_self.absolutelyContinuous ?_⟩
  simpa [Measure.restrict_apply hA.1, inter_eq_left.mpr (hAE.trans inter_subset_right)]
    using hA.2.1

theorem IsPurelyAtomic.eq_zero_of_diffuse (hμ : IsPurelyAtomic μ) (hd : IsDiffuse μ) : μ = 0 := by
  by_contra h
  obtain ⟨A, _, hA⟩ := hμ univ MeasurableSet.univ (Measure.measure_univ_pos.mpr h)
  exact hd ⟨A, hA⟩

/-- Diffuseness descends along absolute continuity. The density's positive set
allows a hypothetical atom to be transferred back to the reference measure. -/
theorem IsDiffuse.of_absolutelyContinuous [SigmaFinite μ] [SigmaFinite ν]
    (hμ : IsDiffuse μ) (hνμ : ν ≪ μ) : IsDiffuse ν := by
  rintro ⟨A, hA⟩
  let R : Set Ω := {x | ν.rnDeriv μ x ≠ 0}
  have hR : MeasurableSet R := (Measure.measurable_rnDeriv ν μ)
    (measurableSet_singleton 0).compl
  have hRae : ∀ᵐ x ∂ν, x ∈ R := (Measure.rnDeriv_pos hνμ).mono fun _ hx => ne_of_gt hx
  have hmass : ν (A ∩ R) = ν A := measure_congr (by
    filter_upwards [hRae] with x hx
    apply propext
    change (x ∈ A ∧ x ∈ R) ↔ x ∈ A
    simp only [hx, and_true])
  have hnull (E : Set Ω) (hE : ν E = 0) : μ (R ∩ E) = 0 := by
    apply (withDensity_apply_eq_zero (Measure.measurable_rnDeriv ν μ)).mp
    rwa [Measure.withDensity_rnDeriv_eq ν μ hνμ]
  refine hμ ⟨A ∩ R, hA.1.inter hR, ?_, fun E hE => ?_⟩
  · apply pos_iff_ne_zero.mpr
    intro hz
    exact (ne_of_gt hA.2.1) (hmass ▸ hνμ hz)
  · rcases hA.cut_zero hE with h | h
    · have hz := hnull (A ∩ E) h
      have heq : (A ∩ R) ∩ E = R ∩ (A ∩ E) := by ext x; simp [and_assoc, and_comm, and_left_comm]
      simp [heq, hz]
    · have hz := hnull (A \ E) h
      have heq : (A ∩ R) \ E = R ∩ (A \ E) := by ext x; simp [and_assoc, and_comm, and_left_comm]
      simp [heq, hz]

/-- A countable measurable union captures every atom up to a null set. Its
complement is diffuse and its restriction is purely atomic. -/
theorem exists_atomic_support [SFinite μ] :
    ∃ B : Set Ω, MeasurableSet B ∧ IsDiffuse (μ.restrict Bᶜ) ∧
      IsPurelyAtomic (μ.restrict B) ∧
      ∀ ν : Measure Ω, ν ≪ μ → IsDiffuse ν → ν B = 0 := by
  obtain ⟨D, hDatom, hDcount, hDcover⟩ :=
    Measure.exists_ae_subset_biUnion_countable (μ := μ)
      (C := {A | IsMeasureAtom μ A}) (fun _ hA => hA.1)
  let B := ⋃₀ D
  have hB : MeasurableSet B := MeasurableSet.sUnion hDcount fun A hA => (hDatom hA).1
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · rintro ⟨A, hA⟩
    have hatom := hA.of_restrict hB.compl
    have hcover := hDcover (A ∩ Bᶜ) hatom
    have hz : μ (A ∩ Bᶜ) = 0 := by
      apply measure_mono_null (t := (A ∩ Bᶜ) \ B)
      · intro x hx
        exact ⟨hx, hx.2⟩
      · exact ae_le_set.mp hcover
    exact (ne_of_gt hatom.2.1) hz
  · intro E hE hpos
    have hpos' : 0 < μ (E ∩ B) := by simpa [Measure.restrict_apply hE] using hpos
    have hex : ∃ A ∈ D, 0 < μ (E ∩ A) := by
      by_contra hn
      push Not at hn
      have hz : μ (⋃ A ∈ D, E ∩ A) = 0 :=
        measure_biUnion_null_iff hDcount |>.mpr (fun A hA => nonpos_iff_eq_zero.mp (hn A hA))
      have heq : (⋃ A ∈ D, E ∩ A) = E ∩ B := by ext x; simp [B]
      exact (ne_of_gt hpos') (heq ▸ hz)
    obtain ⟨A, hAD, hEA⟩ := hex
    have hatom : IsMeasureAtom μ (E ∩ A) :=
      (hDatom hAD).subset inter_subset_right (hE.inter (hDatom hAD).1) hEA
    have hsub : E ∩ A ⊆ B := inter_subset_right.trans (subset_sUnion_of_mem hAD)
    refine ⟨E ∩ A, inter_subset_left, hatom.of_absolutelyContinuous
      Measure.restrict_le_self.absolutelyContinuous ?_⟩
    simpa [Measure.restrict_apply hatom.1, inter_eq_left.mpr hsub] using hEA
  · intro ν hνμ hν
    apply (measure_sUnion_null_iff hDcount).mpr
    intro A hAD
    by_contra hpos
    exact hν ⟨A, (hDatom hAD).of_absolutelyContinuous hνμ (pos_iff_ne_zero.mpr hpos)⟩

/-- Original label: `thm:atomic`.
Every sigma-finite measure on an arbitrary measurable space has a unique
decomposition into a diffuse measure and a purely atomic measure. -/
theorem atomicDecomposition_general (μ : Measure Ω) [SigmaFinite μ] :
    ∃! p : Measure Ω × Measure Ω,
      μ = p.1 + p.2 ∧ IsDiffuse p.1 ∧ IsPurelyAtomic p.2 := by
  obtain ⟨B, hB, hd, hp, hnull⟩ := exists_atomic_support (μ := μ)
  refine ⟨(μ.restrict Bᶜ, μ.restrict B),
    ⟨(Measure.restrict_compl_add_restrict hB).symm, hd, hp⟩, ?_⟩
  rintro ⟨α, β⟩ ⟨hsum, hα, hβ⟩
  have hαle : α ≤ μ := by rw [hsum]; exact Measure.le_add_right le_rfl
  have hβle : β ≤ μ := by rw [hsum]; exact Measure.le_add_left le_rfl
  haveI : SigmaFinite β := Measure.sigmaFinite_of_le μ hβle
  have hαB : α.restrict B = 0 := Measure.restrict_eq_zero.mpr
    (hnull α hαle.absolutelyContinuous hα)
  have hβBc : β.restrict Bᶜ = 0 :=
    (hβ.restrict hB.compl).eq_zero_of_diffuse
      (hd.of_absolutelyContinuous (Measure.restrict_mono_measure hβle Bᶜ).absolutelyContinuous)
  have hαeq : α.restrict Bᶜ = α := by
    simpa [hαB] using (Measure.restrict_add_restrict_compl (μ := α) hB)
  have hβeq : β.restrict B = β := by
    simpa [hβBc] using (Measure.restrict_add_restrict_compl (μ := β) hB)
  apply Prod.ext
  · simpa [Measure.restrict_add, hβBc, hαeq] using
      (congrArg (fun ν : Measure Ω => ν.restrict Bᶜ) hsum).symm
  · simpa [Measure.restrict_add, hαB, hβeq] using
      (congrArg (fun ν : Measure Ω => ν.restrict B) hsum).symm

/-- On a countably separated measurable space, a measurable atom contains
a point of positive mass. -/
theorem IsMeasureAtom.exists_positive_singleton [MeasurableSpace.CountablySeparated Ω]
    [MeasurableSingletonClass Ω] (hA : IsMeasureAtom μ A) :
    ∃ x ∈ A, 0 < μ ({x} : Set Ω) := by
  haveI : HasCountableSeparatingOn Ω MeasurableSet A :=
    HasCountableSeparatingOn.mono (fun _ h => h) (subset_univ A)
  have halt : ∀ E : Set Ω, MeasurableSet E → E ∈ ae (μ.restrict A) ∨ Eᶜ ∈ ae (μ.restrict A) := by
    intro E hE
    rcases hA.cut_zero hE with h | h
    · right
      apply mem_ae_iff.mpr
      simpa [Measure.restrict_apply hE, inter_comm] using h
    · left
      apply mem_ae_iff.mpr
      simpa [Measure.restrict_apply hE.compl, inter_comm, diff_eq] using h
  obtain ⟨x, hxA, hx⟩ :=
    Filter.exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating
      MeasurableSet (s := A) (l := ae (μ.restrict A)) (ae_restrict_mem hA.1)
      (nonempty_of_measure_ne_zero (ne_of_gt hA.2.1)) halt
  refine ⟨x, hxA, ?_⟩
  have hm : (μ.restrict A) ({x} : Set Ω) = (μ.restrict A) univ :=
    measure_congr (ae_eq_univ.mpr hx)
  have hm' : μ ({x} : Set Ω) = μ A := by
    simpa [Measure.restrict_apply (measurableSet_singleton x),
      inter_eq_left.mpr (singleton_subset_iff.mpr hxA)] using hm
  rw [hm']
  exact hA.2.1

/-- Purely atomic s-finite measures on countably separated spaces are
countable weighted sums of their positive singleton masses. -/
theorem IsPurelyAtomic.countablePointMassRepresentation [SFinite μ]
    [MeasurableSpace.CountablySeparated Ω] [MeasurableSingletonClass Ω]
    (hμ : IsPurelyAtomic μ) : HasCountablePointMassRepresentation μ := by
  classical
  let I : Set Ω := {x | 0 < μ ({x} : Set Ω)}
  have hI : I.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (fun x : Ω => measurableSet_singleton x) (fun _ _ h => disjoint_singleton.mpr h)
  have hIae : μ Iᶜ = 0 := by
    by_contra hz
    obtain ⟨A, hAI, hA⟩ := hμ Iᶜ hI.measurableSet.compl (pos_iff_ne_zero.mpr hz)
    obtain ⟨x, hxA, hx⟩ := hA.exists_positive_singleton
    exact hAI hxA hx
  refine ⟨I, hI, fun x => x.2, fun B hB => ?_⟩
  have hBI : B ∩ I = ⋃ x ∈ I, B ∩ {x} := by ext x; simp
  rw [← measure_inter_conull hIae, hBI,
    measure_biUnion hI (fun x _ y _ hxy =>
      (disjoint_singleton.mpr hxy).mono inter_subset_right inter_subset_right)
      (fun x _ => hB.inter (measurableSet_singleton x))]
  apply tsum_congr
  intro x
  by_cases hx : x.1 ∈ B
  · simp [hx, inter_eq_right.mpr (singleton_subset_iff.mpr hx)]
  · have hempty : B ∩ {x.1} = ∅ := by ext y; simp; aesop
    simp [hx, hempty]

/-- Original label: `thm:atomic`.
The coefficients are finite positive real weights, not extended-real infinities;
the indexing subtype makes the support points pairwise distinct. -/
theorem IsPurelyAtomic.exists_countable_dirac_sum [SigmaFinite μ]
    [MeasurableSpace.CountablySeparated Ω] [MeasurableSingletonClass Ω]
    (hμ : IsPurelyAtomic μ) :
    ∃ (I : Set Ω) (a : I → ℝ≥0), I.Countable ∧ (∀ x, 0 < a x) ∧
      (∀ x : I, IsMeasureAtom μ ({x.1} : Set Ω)) ∧
      μ = Measure.sum (fun x : I => a x • Measure.dirac x.1) := by
  classical
  obtain ⟨I, hI, hpos, hsum⟩ := hμ.countablePointMassRepresentation
  let a : I → ℝ≥0 := fun x => (μ ({x.1} : Set Ω)).toNNReal
  have hcoe (x : I) : (a x : ℝ≥0∞) = μ ({x.1} : Set Ω) :=
    ENNReal.coe_toNNReal (ne_of_lt measure_singleton_lt_top)
  refine ⟨I, a, hI, ?_, ?_, ?_⟩
  · intro x
    exact ENNReal.coe_pos.mp ((hcoe x).symm ▸ hpos x)
  · intro x
    refine ⟨measurableSet_singleton x.1, hpos x, fun E _ => ?_⟩
    by_cases hx : x.1 ∈ E
    · simp [diff_eq_empty.mpr (singleton_subset_iff.mpr hx)]
    · simp [(disjoint_singleton_left.mpr hx).inter_eq]
  · ext B hB
    rw [hsum B hB, Measure.sum_apply _ hB]
    apply tsum_congr
    intro x
    simp only [Measure.coe_nnreal_smul_apply, Measure.dirac_apply, Set.indicator_apply,
      Pi.one_apply, hcoe, mul_ite, mul_one, mul_zero]

/-- Original label: `thm:atomic`.
The Polish Borel specialization includes the countable point-mass formula. -/
theorem atomicDecomposition
    {Ω : Type u} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] :
    ∃! p : Measure Ω × Measure Ω,
      μ = p.1 + p.2 ∧ IsDiffuse p.1 ∧ IsPurelyAtomic p.2 ∧
        HasCountablePointMassRepresentation p.2 := by
  obtain ⟨p, hp, huniq⟩ := atomicDecomposition_general μ
  have hp2le : p.2 ≤ μ := by rw [hp.1]; exact Measure.le_add_left le_rfl
  haveI : SigmaFinite p.2 := Measure.sigmaFinite_of_le μ hp2le
  refine ⟨p, ⟨hp.1, hp.2.1, hp.2.2, hp.2.2.countablePointMassRepresentation⟩, ?_⟩
  intro q hq
  exact huniq q ⟨hq.1, hq.2.1, hq.2.2.1⟩

/-- Original label: `thm:atomic`.
The revised statement's literal indexing by a subset of the natural numbers,
with distinct support points and coefficients equal to singleton masses.
The empty atomic part is included without adding a dummy support point. -/
theorem IsPurelyAtomic.exists_nat_dirac_sum [SigmaFinite μ]
    [MeasurableSpace.CountablySeparated Ω] [MeasurableSingletonClass Ω]
    (hμ : IsPurelyAtomic μ) :
    ∃ (I : Set ℕ) (x : I → Ω) (a : I → ℝ≥0), Function.Injective x ∧
      (∀ i, 0 < a i) ∧ (∀ i, (a i : ℝ≥0∞) = μ ({x i} : Set Ω)) ∧
      (∀ i, IsMeasureAtom μ ({x i} : Set Ω)) ∧
      μ = Measure.sum (fun i => a i • Measure.dirac (x i)) := by
  classical
  obtain ⟨S, hS, hpos, hsum⟩ := hμ.countablePointMassRepresentation
  letI : Encodable S := hS.toEncodable
  let e := Encodable.equivRangeEncode S
  let I : Set ℕ := Set.range (Encodable.encode (α := S))
  let x : I → Ω := fun i => (e.symm i).val
  let a : I → ℝ≥0 := fun i => (μ ({x i} : Set Ω)).toNNReal
  have hcoe (i : I) : (a i : ℝ≥0∞) = μ ({x i} : Set Ω) :=
    ENNReal.coe_toNNReal (ne_of_lt measure_singleton_lt_top)
  have hxpos (i : I) : 0 < μ ({x i} : Set Ω) := hpos (e.symm i)
  refine ⟨I, x, a, Subtype.val_injective.comp e.symm.injective,
    fun i => ENNReal.coe_pos.mp ((hcoe i).symm ▸ hxpos i), hcoe, ?_, ?_⟩
  · intro i
    refine ⟨measurableSet_singleton (x i), hxpos i, fun E _ => ?_⟩
    by_cases hx : x i ∈ E
    · simp [diff_eq_empty.mpr (singleton_subset_iff.mpr hx)]
    · simp [(disjoint_singleton_left.mpr hx).inter_eq]
  · ext B hB
    rw [hsum B hB, Measure.sum_apply _ hB, ← e.tsum_eq]
    apply tsum_congr
    intro i
    simp only [Measure.coe_nnreal_smul_apply, Measure.dirac_apply,
      Set.indicator_apply, Pi.one_apply, hcoe, mul_ite, mul_one, mul_zero]
    simp [x]

end Thesis.Foundations.Preliminary.MeasureTheory
