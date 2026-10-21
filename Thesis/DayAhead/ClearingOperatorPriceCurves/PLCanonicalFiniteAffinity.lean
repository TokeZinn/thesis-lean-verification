import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalEncoding
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLGraphTracing

/-! # Finite-affine coordinates of the intrinsic sided encoding -/

noncomputable section
namespace Thesis.DayAhead.PLCanonicalFiniteAffinity

open Set PiecewiseAffinePriceCurves SidedParametrisation
open PLCanonicalEncoding PLLinearCone

def constantPartition (c : ℝ) : AffinePartition univ (fun _ : ℝ => c) where
  count := 1
  piece := fun _ => univ
  interval := fun _ => ordConnected_univ
  disjoint := fun i j h => False.elim (h (Subsingleton.elim _ _))
  cover := by intro x; simp
  affine := fun _ => ⟨0, c, fun _ _ => by simp⟩

def clampPartition : AffinePartition univ clampUnit where
  count := 3
  piece := fun i => if i = 0 then Iic 0 else if i = 1 then Ioo 0 1 else Ici 1
  interval := by
    intro i
    fin_cases i
    · exact ordConnected_Iic
    · exact ordConnected_Ioo
    · exact ordConnected_Ici
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals linarith
  cover := by
    intro x
    simp only [mem_univ, true_iff]
    by_cases hx : x ≤ 0
    · exact ⟨0, hx⟩
    by_cases hx1 : x < 1
    · exact ⟨1, ⟨lt_of_not_ge hx, hx1⟩⟩
    · exact ⟨2, le_of_not_gt hx1⟩
  affine := by
    intro i
    fin_cases i
    · exact ⟨0, 0, fun x hx => by simpa using clampUnit_of_nonpos hx⟩
    · exact ⟨1, 0, fun x hx => by simpa using clampUnit_eq_self hx.1.le hx.2.le⟩
    · exact ⟨0, 1, fun x hx => by simpa using clampUnit_of_one_le hx⟩

theorem finiteSumPartition {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Nonempty (AffinePartition univ (f i))) :
    Nonempty (AffinePartition univ (fun x => ∑ i, f i x)) := by
  induction n with
  | zero => simpa using Nonempty.intro (constantPartition 0)
  | succ n ih =>
    obtain ⟨P⟩ := hf 0
    obtain ⟨Q⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    simpa only [univ_inter, one_mul, Fin.sum_univ_succ] using Nonempty.intro (P.combine Q 1 1)

def uniformPartition {n : ℕ} (knot : Fin (n + 1) → ℝ) :
    AffinePartition univ (uniformInterpolation knot) := by
  have hterm : ∀ j : Fin n, Nonempty (AffinePartition univ (fun x =>
      (knot j.succ - knot j.castSucc) * clampUnit ((n : ℝ) * x - (j : ℝ)))) := by
    intro j
    have P := clampPartition.compAffine (n : ℝ) (-(j : ℝ)) (Nat.cast_nonneg n)
    have Q := P.combine (constantPartition 0) (knot j.succ - knot j.castSucc) 0
    simpa only [preimage_univ, univ_inter, zero_mul, add_zero, sub_eq_add_neg] using
      Nonempty.intro Q
  let P := Classical.choice (finiteSumPartition _ hterm)
  have Q := (constantPartition (knot 0)).combine P 1 1
  simpa only [univ_inter, one_mul, uniformInterpolation] using Q

def quantityPartition (f : Curve) : AffinePartition univ (quantityReal f) := by
  have P := (uniformPartition (leftKnot f)).compAffine 1 1 (by norm_num)
  have P' : AffinePartition univ (fun x => uniformInterpolation (leftKnot f) (x + 1)) := by
    simpa only [preimage_univ, one_mul] using P
  have L := Partition.restrictTo P' ordConnected_Iic (subset_univ (Iic (0 : ℝ)))
  have R := Partition.restrictTo (uniformPartition (rightKnot f)) ordConnected_Ioi
    (subset_univ (Ioi (0 : ℝ)))
  have L' := Partition.congrPrice L (g := quantityReal f) (fun x hx => by
    have hx' : x ≤ 0 := hx
    simp only [quantityReal, if_pos hx'])
  have R' := Partition.congrPrice R (g := quantityReal f) (fun x hx => by
    have hx' : 0 < x := hx
    simp only [quantityReal, if_neg (not_le.mpr hx')])
  have Q := Partition.join L' R' (Iic_disjoint_Ioi le_rfl)
  simpa only [Iic_union_Ioi] using Q

def quantityPartitionOnParameter (f : Curve) :
    AffinePartition (Icc (-1 : ℝ) 1) (quantityReal f) :=
  Partition.restrictTo (quantityPartition f) ordConnected_Icc (subset_univ _)

def pricePartitionOnParameter (f : Curve) :
    AffinePartition (Icc (-1 : ℝ) 1) (fun x => f.price (quantityReal f x)) :=
  PLGraphTracing.composePartition (quantityPartitionOnParameter f)
    (Classical.choice f.pieces) ((quantityReal_monotone f).monotoneOn _)
    (fun x hx => (parametriser f ⟨x, hx⟩).property)

end Thesis.DayAhead.PLCanonicalFiniteAffinity
