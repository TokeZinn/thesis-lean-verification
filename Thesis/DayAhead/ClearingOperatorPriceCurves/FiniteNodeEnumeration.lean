import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalEncoding
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Finite comparison cells for distinct-node enumeration

An enumeration pattern chooses original coordinate indices, in strict
increasing value order, covering every original value. Its cell is a finite
combination of equality and order comparisons. These explicit cells cover
all nonempty finite coordinate arrays; no measurability of an intrinsic
node enumeration is postulated.
-/
noncomputable section
namespace Thesis.DayAhead.FiniteNodeEnumeration

open Set MeasureTheory PLCanonicalEncoding

abbrev Pattern (n : ℕ) := Σ k : Fin n, Fin (k.val + 1) → Fin n

def values {n : ℕ} (v : Fin n → ℝ) : Finset ℝ := Finset.univ.image v

def cell {A : Type*} {n : ℕ} (v : A → Fin n → ℝ) (p : Pattern n) : Set A :=
  {a | StrictMono (fun j => v a (p.2 j)) ∧ ∀ i, ∃ j, v a i = v a (p.2 j)}

theorem measurableSet_cell {A : Type*} [MeasurableSpace A] {n : ℕ}
    (v : A → Fin n → ℝ) (hv : Measurable v) (p : Pattern n) :
    MeasurableSet (cell v p) := by
  have hc : MeasurableSet {a | StrictMono (fun j => v a (p.2 j))} := by
    change MeasurableSet {a | ∀ i j, i < j → v a (p.2 i) < v a (p.2 j)}
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_lt
        ((measurable_pi_apply _).comp hv) ((measurable_pi_apply _).comp hv)
  have he : MeasurableSet {a | ∀ i, ∃ j, v a i = v a (p.2 j)} := by
    simp only [setOf_forall, setOf_exists]
    exact MeasurableSet.iInter fun i => MeasurableSet.iUnion fun j =>
      measurableSet_eq_fun ((measurable_pi_apply i).comp hv)
        ((measurable_pi_apply _).comp hv)
  exact hc.inter he

theorem selected_values_eq {A : Type*} {n : ℕ} (v : A → Fin n → ℝ)
    (p : Pattern n) {a : A} (ha : a ∈ cell v p) :
    (Finset.univ.image (fun j => v a (p.2 j))) = values (v a) := by
  ext x
  constructor
  · rintro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨p.2 j, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj⟩ := ha.2 i
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩

theorem cardinal_on_cell {A : Type*} {n : ℕ} (v : A → Fin n → ℝ)
    (p : Pattern n) {a : A} (ha : a ∈ cell v p) :
    (values (v a)).card = p.1.val + 1 := by
  rw [← selected_values_eq v p ha, Finset.card_image_of_injective _ ha.1.injective]
  simp

/-- Every nonempty array has an actual finite comparison pattern: enumerate
its distinct values and choose one original coordinate for each value. -/
theorem cell_cover {A : Type*} {n : ℕ} (hn : 0 < n) (v : A → Fin n → ℝ) (a : A) :
    ∃ p : Pattern n, a ∈ cell v p := by
  have hne : (values (v a)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  let k := count (values (v a))
  have hcard : (values (v a)).card ≤ n := by
    exact (Finset.card_image_le).trans (by simp)
  have hk : k < n := by
    dsimp [k, count]
    have := hne.card_pos
    omega
  let e := enumeration (values (v a)) hne
  have hex (j : Fin (k + 1)) : ∃ i, v a i = e j := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (enumeration_mem (values (v a)) hne j)
    exact ⟨i, hi⟩
  choose idx hidx using hex
  refine ⟨⟨⟨k, hk⟩, idx⟩, ?_, ?_⟩
  · intro i j hij
    change v a (idx i) < v a (idx j)
    rw [hidx, hidx]
    exact e.strictMono hij
  · intro i
    have hv : v a i ∈ (values (v a) : Set ℝ) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [← enumeration_range (values (v a)) hne] at hv
    obtain ⟨j, hj⟩ := hv
    exact ⟨j, hj.symm.trans (hidx j).symm⟩

/-- On each comparison cell the distinct-node set is literally the image
of the selected original coordinates, with its exact cardinality. -/
theorem enumeration_on_cell {A : Type*} {n : ℕ} (v : A → Fin n → ℝ)
    (p : Pattern n) {a : A} (ha : a ∈ cell v p)
    (hne : (values (v a)).Nonempty) :
    ∃ h : count (values (v a)) = p.1.val,
      ∀ j : Fin (p.1.val + 1),
        enumeration (values (v a)) hne (Fin.cast (by omega) j) = v a (p.2 j) := by
  have hc := cardinal_on_cell v p ha
  have hk : count (values (v a)) = p.1.val := by dsimp [count]; omega
  refine ⟨hk, ?_⟩
  intro j
  have heq : (fun i : Fin (p.1.val + 1) => v a (p.2 i)) =
      (values (v a)).orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc
      (fun i => Finset.mem_image.mpr ⟨p.2 i, Finset.mem_univ _, rfl⟩) ha.1
  change enumeration (values (v a)) hne (Fin.cast _ j) =
    (fun i : Fin (p.1.val + 1) => v a (p.2 i)) j
  rw [heq]
  exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl

end Thesis.DayAhead.FiniteNodeEnumeration
