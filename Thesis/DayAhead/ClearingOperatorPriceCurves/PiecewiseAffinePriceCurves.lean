import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedSide
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurves

/-! # The full current piecewise-affine price-curve carrier

The finite-level carrier in `PriceCurves` is a simple-curve submodel. This
carrier includes nonconstant affine pieces and isolates the values at jump
points in singleton cells. Empty partition cells may be removed; allowing them
in the witness avoids introducing arbitrary choices when a zero-volume order
is present.
-/

noncomputable section
namespace Thesis.DayAhead.PiecewiseAffinePriceCurves

open Set

/-- A finite disjoint interval partition on which every piece is affine.
Singleton cells are allowed, so midpoint-selected jumps are represented. -/
structure AffinePartition (domain : Set ℝ) (f : ℝ → ℝ) where
  count : ℕ
  piece : Fin count → Set ℝ
  interval : ∀ i, OrdConnected (piece i)
  disjoint : ∀ i j, i ≠ j → Disjoint (piece i) (piece j)
  cover : ∀ x, x ∈ domain ↔ ∃ i, x ∈ piece i
  affine : ∀ i, ∃ a b : ℝ, ∀ x ∈ piece i, f x = a * x + b

namespace AffinePartition

theorem piece_subset {domain : Set ℝ} {f : ℝ → ℝ}
    (P : AffinePartition domain f) (i : Fin P.count) : P.piece i ⊆ domain :=
  fun _ hx => (P.cover _).mpr ⟨i, hx⟩

/-- Restricting a finite affine partition to an interval introduces no new
non-affine pieces. Empty intersections are harmless witness cells. -/
def restrict {domain : Set ℝ} {f : ℝ → ℝ} (P : AffinePartition domain f)
    (s : Set ℝ) (hs : OrdConnected s) : AffinePartition (domain ∩ s) f where
  count := P.count
  piece := fun i => P.piece i ∩ s
  interval := fun i => (P.interval i).inter hs
  disjoint := fun i j hij => (P.disjoint i j hij).mono inter_subset_left inter_subset_left
  cover := by
    intro x
    constructor
    · rintro ⟨hx, hsx⟩
      obtain ⟨i, hi⟩ := (P.cover x).mp hx
      exact ⟨i, hi, hsx⟩
    · rintro ⟨i, hi, hsx⟩
      exact ⟨(P.cover x).mpr ⟨i, hi⟩, hsx⟩
  affine := fun i => by
    obtain ⟨a, b, h⟩ := P.affine i
    exact ⟨a, b, fun x hx => h x hx.1⟩

/-- Affine changes of the quantity coordinate preserve finite affinity. -/
def compAffine {domain : Set ℝ} {f : ℝ → ℝ} (P : AffinePartition domain f)
    (a b : ℝ) (ha : 0 ≤ a) :
    AffinePartition ((fun x => a * x + b) ⁻¹' domain) (fun x => f (a * x + b)) where
  count := P.count
  piece := fun i => (fun x => a * x + b) ⁻¹' P.piece i
  interval := fun i => (P.interval i).preimage_mono (fun _ _ h => by nlinarith)
  disjoint := by
    intro i j hij
    exact (P.disjoint i j hij).preimage _
  cover := fun x => P.cover (a * x + b)
  affine := fun i => by
    obtain ⟨c, d, h⟩ := P.affine i
    refine ⟨c * a, c * b + d, fun x hx => ?_⟩
    rw [h _ hx]
    ring

/-- Common refinement proves finite affinity of linear combinations. No
bound on the number of distinct output levels is imposed. -/
def combine {D E : Set ℝ} {f g : ℝ → ℝ} (P : AffinePartition D f)
    (Q : AffinePartition E g) (a b : ℝ) :
    AffinePartition (D ∩ E) (fun x => a * f x + b * g x) where
  count := Fintype.card (Fin P.count × Fin Q.count)
  piece := fun k =>
    let ij := (Fintype.equivFin (Fin P.count × Fin Q.count)).symm k
    P.piece ij.1 ∩ Q.piece ij.2
  interval := fun k =>
    let ij := (Fintype.equivFin (Fin P.count × Fin Q.count)).symm k
    (P.interval ij.1).inter (Q.interval ij.2)
  disjoint := by
    intro i j hij
    let e := Fintype.equivFin (Fin P.count × Fin Q.count)
    have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    apply Set.disjoint_left.mpr
    intro x hi hj
    by_cases hfst : (e.symm i).1 = (e.symm j).1
    · exact (Set.disjoint_left.mp (Q.disjoint _ _ (fun h => hne (Prod.ext hfst h))))
        hi.2 hj.2
    · exact (Set.disjoint_left.mp (P.disjoint _ _ hfst)) hi.1 hj.1
  cover := by
    intro x
    constructor
    · rintro ⟨hx, hy⟩
      obtain ⟨i, hi⟩ := (P.cover x).mp hx
      obtain ⟨j, hj⟩ := (Q.cover x).mp hy
      refine ⟨Fintype.equivFin _ (i, j), ?_⟩
      simpa using And.intro hi hj
    · rintro ⟨k, hk⟩
      exact ⟨(P.cover x).mpr ⟨_, hk.1⟩, (Q.cover x).mpr ⟨_, hk.2⟩⟩
  affine := by
    intro k
    let ij := (Fintype.equivFin (Fin P.count × Fin Q.count)).symm k
    obtain ⟨c, d, hc⟩ := P.affine ij.1
    obtain ⟨e, h, he⟩ := Q.affine ij.2
    refine ⟨a * c + b * e, a * d + b * h, fun x hx => ?_⟩
    rw [hc x hx.1, he x hx.2]
    ring

end AffinePartition

/-- Original label: `defn:space-of-price-curves`, with the current affine
scope rather than the obsolete finite-range restriction. Values of `price`
outside its recorded domain have no mathematical meaning. -/
structure Curve where
  leftEndpoint : ℝ
  rightEndpoint : ℝ
  left_nonpos : leftEndpoint ≤ 0
  right_nonneg : 0 ≤ rightEndpoint
  price : ℝ → ℝ
  monotone : MonotoneOn price (Icc leftEndpoint rightEndpoint)
  pieces : Nonempty (AffinePartition (Icc leftEndpoint rightEndpoint) price)

def Curve.graph (f : Curve) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc f.leftEndpoint f.rightEndpoint ∧ z.2 = f.price z.1}

def Curve.IsSimple (f : Curve) : Prop :=
  (f.price '' Icc f.leftEndpoint f.rightEndpoint).Finite

namespace Side

open InterpolatedSide

theorem zero_disjoint_cell {n : ℕ} (Q : Fin (n + 1) → ℝ)
    (hQ : Monotone Q) (hzero : Q 0 = 0) (j : Fin n) :
    Disjoint ({0} : Set ℝ) (cell Q j) := by
  apply Set.disjoint_left.mpr
  intro x hx hj
  have hx0 : x = 0 := mem_singleton_iff.mp hx
  have hnonneg : 0 ≤ Q j.castSucc := hzero ▸ hQ (Fin.zero_le _)
  rw [hx0] at hj
  linarith [hj.1]

def partition {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hQ : Monotone Q) (hzero : Q 0 = 0) :
    AffinePartition (Icc 0 (Q (Fin.last n))) (curve p Q) where
  count := n + 1
  piece := Fin.cases {0} (cell Q)
  interval := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Set.ordConnected_singleton
    · exact Set.ordConnected_Ioc
  disjoint := by
    intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b _ => zero_disjoint_cell Q hQ hzero b) j
      exact fun h => False.elim (h rfl)
    · refine Fin.cases ?_ (fun b hab => ?_) j
      · exact fun _ => (zero_disjoint_cell Q hQ hzero a).symm
      · exact disjoint_cells Q hQ (fun h => hab (congrArg Fin.succ h))
  cover := by
    intro x
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · exact ⟨0, by simp [hx0]⟩
      · obtain ⟨i, hi⟩ := exists_cell Q hzero (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hx.2
        exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.cases ?_ (fun j hj => ?_) i
      · intro hx
        have hx0 : x = 0 := mem_singleton_iff.mp hx
        rw [hx0]
        exact ⟨le_rfl, hzero ▸ hQ (Fin.zero_le _)⟩
      · exact ⟨(hzero ▸ hQ (Fin.zero_le j.castSucc)).trans hj.1.le,
          hj.2.trans (hQ (Fin.le_last j.succ))⟩
  affine := by
    intro i
    refine Fin.cases ?_ (fun j => curve_on_cell_affine p Q hQ hzero j) i
    refine ⟨0, p 0, ?_⟩
    intro x hx
    rw [mem_singleton_iff.mp hx, curve_zero]
    ring

/-- Supply is an actual member of the new affine price-curve class. This
derives monotonicity and the affine partition from the interpolation formula. -/
def supplyCurve {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hzero : Q 0 = 0) : Curve where
  leftEndpoint := 0
  rightEndpoint := Q (Fin.last n)
  left_nonpos := le_rfl
  right_nonneg := hzero ▸ hQ (Fin.zero_le _)
  price := curve p Q
  monotone := curve_monotoneOn p Q hp hQ hzero
  pieces := ⟨partition p Q hQ hzero⟩

end Side

/-- A nonconstant affine curve is admitted without a finite-range premise. -/
def unitRamp : Curve where
  leftEndpoint := 0
  rightEndpoint := 1
  left_nonpos := le_rfl
  right_nonneg := zero_le_one
  price := id
  monotone := monotone_id.monotoneOn _
  pieces := ⟨{
    count := 1
    piece := fun _ => Icc 0 1
    interval := fun _ => Set.ordConnected_Icc
    disjoint := by intro i j h; exact False.elim (h (Subsingleton.elim _ _))
    cover := by intro x; simp
    affine := by intro _; exact ⟨1, 0, fun x _ => by simp⟩ }⟩

theorem unitRamp_not_simple : ¬unitRamp.IsSimple := by
  change ¬(id '' Icc (0 : ℝ) 1).Finite
  simpa using (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num)).not_finite

end Thesis.DayAhead.PiecewiseAffinePriceCurves
