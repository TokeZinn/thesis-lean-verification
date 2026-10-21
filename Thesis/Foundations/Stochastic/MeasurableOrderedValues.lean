import Thesis.Foundations.Stochastic.MeasurableDistinctCounts
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.Interval.Finset.Fin

/-! # Measurable increasing enumeration of a finite real image

A countable family may contain arbitrarily many repeated evaluations. Its
distinct-value ranks and ordered levels are still measurable. The bounded
infimum formula below equals the actual finite increasing enumeration.
-/

noncomputable section
namespace Thesis.Foundations.Stochastic.MeasurableDistinctCounts

open Set MeasureTheory

variable {ι Ω : Type*}

def countBelow (s : Set ι) (f : ι → ℝ) (p : ℝ) : ℕ :=
  (f '' {i | i ∈ s ∧ f i < p}).ncard

theorem countBelow_eq (s : Set ι) (f : ι → ℝ) (p : ℝ) :
    countBelow s f p = (f '' s ∩ Iio p).ncard := by
  unfold countBelow
  congr 1
  ext x
  simp only [mem_image, mem_setOf_eq, mem_inter_iff, mem_Iio]
  constructor
  · rintro ⟨i, ⟨hi, hp⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, hp⟩
  · rintro ⟨⟨i, hi, rfl⟩, hp⟩
    exact ⟨i, ⟨hi, hp⟩, rfl⟩

theorem countBelow_ordered {n : ℕ} (v : Fin n → ℝ) (hv : StrictMono v)
    (s : Set ι) (f : ι → ℝ) (hrange : range v = f '' s) (i : Fin n) :
    countBelow s f (v i) = i.val := by
  rw [countBelow_eq, ← hrange]
  have hs : range v ∩ Iio (v i) = v '' Iio i := by
    ext x
    simp only [mem_inter_iff, mem_range, mem_Iio, mem_image]
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, hv.lt_iff_lt.mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, hv hj⟩
  rw [hs, hv.injective.injOn.ncard_image, ← Finset.coe_Iio, ncard_coe_finset, Fin.card_Iio]

def orderedValue (upper : ℝ) (s : Set ι) (f : ι → ℝ) (j : ℕ) : ℝ := by
  classical
  exact ⨅ r : ι, if r ∈ s ∧ j ≤ countBelow s f (f r) then f r else upper

theorem orderedValue_eq [Nonempty ι] {n : ℕ} (v : Fin n → ℝ) (hv : StrictMono v)
    (upper : ℝ) (s : Set ι) (f : ι → ℝ) (hrange : range v = f '' s)
    (hupper : ∀ r ∈ s, f r ≤ upper) (i : Fin n) :
    orderedValue upper s f i.val = v i := by
  classical
  obtain ⟨r, hrs, hri⟩ := hrange ▸ mem_range_self (f := v) i
  have hiupper : v i ≤ upper := hri ▸ hupper r hrs
  have hall (t : ι) : v i ≤
      (if t ∈ s ∧ i.val ≤ countBelow s f (f t) then f t else upper) := by
    split_ifs with ht
    · obtain ⟨k, hk⟩ := (hrange.symm ▸ (show f t ∈ f '' s from ⟨t, ht.1, rfl⟩))
      rw [← hk] at ht ⊢
      rw [countBelow_ordered v hv s f hrange k] at ht
      exact hv.monotone ht.2
    · exact hiupper
  apply le_antisymm
  · have hb : BddBelow (range fun t : ι =>
        if t ∈ s ∧ i.val ≤ countBelow s f (f t) then f t else upper) := by
      refine ⟨v i, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hall t
    have hrank : countBelow s f (f r) = i.val := by
      rw [hri]
      exact countBelow_ordered v hv s f hrange i
    have h := ciInf_le hb r
    rw [if_pos (show r ∈ s ∧ i.val ≤ countBelow s f (f r) from ⟨hrs, hrank.ge⟩), hri] at h
    exact h
  · exact le_ciInf hall

variable [Encodable ι] [MeasurableSpace Ω]

theorem measurable_countBelow {s : Ω → Set ι} {f : Ω → ι → ℝ} {p : Ω → ℝ}
    (hs : Measurable s) (hf : ∀ i, Measurable (fun ω => f ω i)) (hp : Measurable p) :
    Measurable (fun ω => countBelow (s ω) (f ω) (p ω)) := by
  apply measurable_ncard_image
  · apply measurable_set_iff.mpr
    intro i
    exact ((measurable_set_iff.mp hs) i).and
      (measurableSet_setOf.mp (measurableSet_lt (hf i) hp))
  · exact hf

theorem measurable_orderedValue (upper : ℝ) (j : ℕ)
    {s : Ω → Set ι} {f : Ω → ι → ℝ}
    (hs : Measurable s) (hf : ∀ i, Measurable (fun ω => f ω i)) :
    Measurable (fun ω => orderedValue upper (s ω) (f ω) j) := by
  apply Measurable.iInf
  intro r
  apply (hf r).ite _ measurable_const
  exact ((measurable_set_iff.mp hs) r).setOf.inter
    (measurableSet_le measurable_const (measurable_countBelow hs hf (hf r)))

end Thesis.Foundations.Stochastic.MeasurableDistinctCounts
