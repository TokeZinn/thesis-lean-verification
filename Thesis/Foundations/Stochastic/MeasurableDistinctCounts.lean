import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Measurable counts of distinct values in a countable family

Choosing the first encoded index for each value avoids equipping a set of real
values with a discrete measurable structure. This is used to count the actual
essential price blocks from rational evaluations.
-/

noncomputable section
namespace Thesis.Foundations.Stochastic.MeasurableDistinctCounts

open Set MeasureTheory

variable {ι β Ω : Type*} [Encodable ι]

def firstRepresentatives (s : Set ι) (f : ι → β) : Set ι :=
  {i | i ∈ s ∧ ∀ j, Encodable.encode j < Encodable.encode i → j ∈ s → f j ≠ f i}

theorem firstRepresentatives_injOn (s : Set ι) (f : ι → β) :
    InjOn f (firstRepresentatives s f) := by
  intro i hi j hj hij
  rcases lt_trichotomy (Encodable.encode i) (Encodable.encode j) with h | h | h
  · exact (hj.2 i h hi.1 hij).elim
  · exact Encodable.encode_injective h
  · exact (hi.2 j h hj.1 hij.symm).elim

theorem image_firstRepresentatives (s : Set ι) (f : ι → β) :
    f '' firstRepresentatives s f = f '' s := by
  classical
  apply Subset.antisymm (image_mono fun _ h => h.1)
  rintro _ ⟨i, hi, rfl⟩
  have hex : ∃ n : ℕ, ∃ j, Encodable.encode j = n ∧ j ∈ s ∧ f j = f i :=
    ⟨Encodable.encode i, i, rfl, hi, rfl⟩
  obtain ⟨j, hj, hjs, hji⟩ := Nat.find_spec hex
  refine ⟨j, ⟨hjs, ?_⟩, hji⟩
  intro k hk hks hkj
  have hmin := Nat.find_min' hex ⟨k, rfl, hks, hkj.trans hji⟩
  rw [← hj] at hmin
  exact (not_lt_of_ge hmin) hk

theorem ncard_firstRepresentatives (s : Set ι) (f : ι → β) :
    (firstRepresentatives s f).ncard = (f '' s).ncard := by
  rw [← image_firstRepresentatives s f]
  exact (firstRepresentatives_injOn s f).ncard_image.symm

variable [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableEq β]

theorem measurable_firstRepresentatives {s : Ω → Set ι} {f : Ω → ι → β}
    (hs : Measurable s) (hf : ∀ i, Measurable (fun ω => f ω i)) :
    Measurable (fun ω => firstRepresentatives (s ω) (f ω)) := by
  apply measurable_set_iff.mpr
  intro i
  apply ((measurable_set_iff.mp hs) i).and
  apply Measurable.forall
  intro j
  apply Measurable.imp measurable_const
  apply ((measurable_set_iff.mp hs) j).imp
  exact (measurableSet_setOf.mp (measurableSet_eq_fun (hf j) (hf i))).not

theorem measurable_ncard_image {s : Ω → Set ι} {f : Ω → ι → β}
    (hs : Measurable s) (hf : ∀ i, Measurable (fun ω => f ω i)) :
    Measurable (fun ω => (f ω '' s ω).ncard) := by
  simp_rw [← ncard_firstRepresentatives]
  exact measurable_ncard.comp (measurable_firstRepresentatives hs hf)

end Thesis.Foundations.Stochastic.MeasurableDistinctCounts
