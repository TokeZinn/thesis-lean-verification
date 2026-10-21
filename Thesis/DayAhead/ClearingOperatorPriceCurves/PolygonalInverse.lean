import Thesis.DayAhead.ClearingOperatorPriceCurves.CompletedInverse
import Thesis.DayAhead.ClearingOperatorPriceCurves.PiecewiseAffinePriceCurves

/-! # Finite affine partitions for midpoint inverses of completed graphs

Each source interval is split into its open core and at most two endpoints.
On a core the completed graph agrees with the actual affine graph. Pulling
the cells back along the monotone selected inverse gives a finite interval
partition of levels. This derives inverse affinity rather than assuming it.
-/

noncomputable section
namespace Thesis.DayAhead.PolygonalInverse

open Set Filter Topology
open CompletedInverse PiecewiseAffinePriceCurves

variable {lo hi : ℝ} {E : ℝ → ℝ}

def sourceCell (P : AffinePartition (Icc lo hi) E) (i : Fin P.count)
    (k : Fin 3) : Set ℝ :=
  if k = 0 then P.piece i ∩ Ioo (sInf (P.piece i)) (sSup (P.piece i))
  else if k = 1 then P.piece i ∩ {sInf (P.piece i)}
  else if sInf (P.piece i) = sSup (P.piece i) then ∅
  else P.piece i ∩ {sSup (P.piece i)}

theorem sourceCell_subset (P : AffinePartition (Icc lo hi) E)
    (i : Fin P.count) (k : Fin 3) : sourceCell P i k ⊆ P.piece i := by
  unfold sourceCell
  split_ifs
  · exact inter_subset_left
  · exact inter_subset_left
  · exact empty_subset _
  · exact inter_subset_left

theorem piece_bddBelow (P : AffinePartition (Icc lo hi) E) (i : Fin P.count) :
    BddBelow (P.piece i) := ⟨lo, fun _ hx => (P.piece_subset i hx).1⟩

theorem piece_bddAbove (P : AffinePartition (Icc lo hi) E) (i : Fin P.count) :
    BddAbove (P.piece i) := ⟨hi, fun _ hx => (P.piece_subset i hx).2⟩

theorem sourceCell_interval (P : AffinePartition (Icc lo hi) E)
    (i : Fin P.count) (k : Fin 3) : OrdConnected (sourceCell P i k) := by
  unfold sourceCell
  split_ifs
  · exact (P.interval i).inter ordConnected_Ioo
  · exact (P.interval i).inter ordConnected_singleton
  · exact ordConnected_empty
  · exact (P.interval i).inter ordConnected_singleton

theorem sourceCell_disjoint_same (P : AffinePartition (Icc lo hi) E)
    (i : Fin P.count) (k l : Fin 3) (hkl : k ≠ l) :
    Disjoint (sourceCell P i k) (sourceCell P i l) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  fin_cases k <;> fin_cases l <;>
    by_cases h : sInf (P.piece i) = sSup (P.piece i) <;>
    simp_all [sourceCell]

theorem sourceCell_disjoint (P : AffinePartition (Icc lo hi) E)
    (i j : Fin P.count) (k l : Fin 3) (h : (i, k) ≠ (j, l)) :
    Disjoint (sourceCell P i k) (sourceCell P j l) := by
  by_cases hij : i = j
  · subst j
    exact sourceCell_disjoint_same P i k l (fun hkl => h (Prod.ext rfl hkl))
  · exact (P.disjoint i j hij).mono (sourceCell_subset P i k) (sourceCell_subset P j l)

theorem sourceCell_cover (P : AffinePartition (Icc lo hi) E) (x : ℝ) :
    x ∈ Icc lo hi ↔ ∃ i k, x ∈ sourceCell P i k := by
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := (P.cover x).mp hx
    have hlow := csInf_le (piece_bddBelow P i) hxi
    have hupp := le_csSup (piece_bddAbove P i) hxi
    by_cases hl : x = sInf (P.piece i)
    · exact ⟨i, 1, by change x ∈ P.piece i ∩ {sInf (P.piece i)}; exact ⟨hxi, hl⟩⟩
    · by_cases hu : x = sSup (P.piece i)
      · refine ⟨i, 2, ?_⟩
        have hne : sInf (P.piece i) ≠ sSup (P.piece i) := fun h => hl (hu.trans h.symm)
        change x ∈ (if sInf (P.piece i) = sSup (P.piece i) then ∅
          else P.piece i ∩ {sSup (P.piece i)})
        rw [if_neg hne]
        exact ⟨hxi, hu⟩
      · refine ⟨i, 0, ?_⟩
        simp only [sourceCell, Fin.isValue, ↓reduceIte, mem_inter_iff, mem_Ioo]
        exact ⟨hxi, lt_of_le_of_ne hlow (Ne.symm hl), lt_of_le_of_ne hupp hu⟩
  · rintro ⟨i, k, hx⟩
    exact P.piece_subset i (sourceCell_subset P i k hx)

theorem continuousAt_core (P : AffinePartition (Icc lo hi) E) (i : Fin P.count)
    {p : ℝ} (hp : p ∈ sourceCell P i 0) : ContinuousAt E p := by
  change p ∈ P.piece i ∩ Ioo (sInf (P.piece i)) (sSup (P.piece i)) at hp
  obtain ⟨l, hl, hlp⟩ := (csInf_lt_iff (piece_bddBelow P i) ⟨p, hp.1⟩).mp hp.2.1
  obtain ⟨r, hr, hpr⟩ := (lt_csSup_iff (piece_bddAbove P i) ⟨p, hp.1⟩).mp hp.2.2
  obtain ⟨a, b, h⟩ := P.affine i
  apply ((continuous_const.mul continuous_id).add continuous_const).continuousAt
    |>.congr_of_eventuallyEq (f := fun x : ℝ => a * x + b)
  filter_upwards [Ioo_mem_nhds hlp hpr] with x hx
  exact h x ((P.interval i).out hl hr ⟨hx.1.le, hx.2.le⟩)

theorem level_eq_affine_on_core (P : AffinePartition (Icc lo hi) E) (i : Fin P.count)
    {p q a b : ℝ} (hp : p ∈ sourceCell P i 0)
    (he : ∀ x ∈ P.piece i, E x = a * x + b)
    (hq : p ∈ levelSet lo hi E q) : q = a * p + b := by
  have hc := continuousAt_core P i hp
  have hl := hc.continuousWithinAt.leftLim_eq
  have hr := hc.continuousWithinAt.rightLim_eq
  have hep := he p (sourceCell_subset P i 0 hp)
  change p ∈ Icc lo hi ∧ E.leftLim p ≤ q ∧ q ≤ E.rightLim p at hq
  rw [hl, hr, hep] at hq
  exact le_antisymm hq.2.2 hq.2.1

theorem interval_preimage_monotoneOn {D S : Set ℝ} {f : ℝ → ℝ}
    (hD : OrdConnected D) (hS : OrdConnected S) (hf : MonotoneOn f D) :
    OrdConnected (D ∩ f ⁻¹' S) := by
  constructor
  intro x hx y hy z hz
  have hzD := hD.out hx.1 hy.1 hz
  exact ⟨hzD, hS.out hx.2 hy.2 ⟨hf hx.1 hzD hz.1, hf hzD hy.1 hz.2⟩⟩

theorem inverse_affine_on_sourceCell (P : AffinePartition (Icc lo hi) E)
    (hE : Monotone E) (D : Set ℝ)
    (hne : ∀ q ∈ D, (levelSet lo hi E q).Nonempty)
    (i : Fin P.count) (k : Fin 3) :
    ∃ a b : ℝ, ∀ q ∈ D ∩ (midpointPrice lo hi E) ⁻¹' sourceCell P i k,
      midpointPrice lo hi E q = a * q + b := by
  let f := midpointPrice lo hi E
  fin_cases k
  · obtain ⟨a, b, h⟩ := P.affine i
    by_cases ha : a = 0
    · refine ⟨0, f b, ?_⟩
      intro q hq
      have he := level_eq_affine_on_core P i hq.2 h
        (midpointPrice_mem_levelSet lo hi E hE q (hne q hq.1))
      have hqb : q = b := by simpa only [ha, zero_mul, zero_add] using he
      simp only [zero_mul, zero_add, hqb, f]
    · refine ⟨a⁻¹, -b / a, ?_⟩
      intro q hq
      have he := level_eq_affine_on_core P i hq.2 h
        (midpointPrice_mem_levelSet lo hi E hE q (hne q hq.1))
      field_simp
      nlinarith
  · refine ⟨0, sInf (P.piece i), ?_⟩
    intro q hq
    have h := hq.2
    change f q ∈ P.piece i ∩ {sInf (P.piece i)} at h
    simpa only [zero_mul, zero_add] using h.2
  · refine ⟨0, sSup (P.piece i), ?_⟩
    intro q hq
    have h := hq.2
    change f q ∈ (if sInf (P.piece i) = sSup (P.piece i) then ∅
      else P.piece i ∩ {sSup (P.piece i)}) at h
    split_ifs at h
    · exact False.elim h
    · simpa only [zero_mul, zero_add] using h.2

/-- Original label: `prop:price-impact-curve-properties`, clause (ii).
The actual midpoint inverse of a completed monotone finite polygonal graph
has a finite disjoint interval partition of affine pieces, along the thesis's
clause-(ii) argument: on the open core of a piece the completed graph is the
affine graph, so the inverse is its affine inverse (or constant on a flat); the
piece endpoints contribute singleton cells.  Nonemptiness of the level sets is a
hypothesis here; on the thesis route it comes from the finite polygonal segment
cover of the completed graph (`FinitePricePathSource.actual_levelSet_nonempty`
for the actual book), while `CompletedInverse.levelSet_nonempty` is an alternative
sup-based route.  No inverse-affinity assumption occurs in this theorem. -/
def inversePartition (P : AffinePartition (Icc lo hi) E) (hE : Monotone E)
    (D : Set ℝ) (hD : OrdConnected D)
    (hne : ∀ q ∈ D, (levelSet lo hi E q).Nonempty) :
    AffinePartition D (midpointPrice lo hi E) where
  count := Fintype.card (Fin P.count × Fin 3)
  piece := fun k =>
    let ik := (Fintype.equivFin (Fin P.count × Fin 3)).symm k
    D ∩ (midpointPrice lo hi E) ⁻¹' sourceCell P ik.1 ik.2
  interval := fun k =>
    let ik := (Fintype.equivFin (Fin P.count × Fin 3)).symm k
    interval_preimage_monotoneOn hD (sourceCell_interval P ik.1 ik.2)
      (midpointPrice_monotoneOn lo hi E hE D hne)
  disjoint := by
    intro k l hkl
    let e := Fintype.equivFin (Fin P.count × Fin 3)
    exact ((sourceCell_disjoint P (e.symm k).1 (e.symm l).1
      (e.symm k).2 (e.symm l).2 (fun h => hkl (e.symm.injective h))).preimage _).mono
      inter_subset_right inter_subset_right
  cover := by
    intro q
    constructor
    · intro hq
      have hp := (midpointPrice_mem_levelSet lo hi E hE q (hne q hq)).1
      obtain ⟨i, k, hik⟩ := (sourceCell_cover P _).mp hp
      refine ⟨Fintype.equivFin _ (i, k), ?_⟩
      simpa using And.intro hq hik
    · rintro ⟨k, hk⟩
      exact hk.1
  affine := fun k =>
    let ik := (Fintype.equivFin (Fin P.count × Fin 3)).symm k
    inverse_affine_on_sourceCell P hE D hne ik.1 ik.2

/-- Alternative route for `prop:price-impact-curve-properties` (not the mapped
proof): for the endpoint-tail hypotheses of the actual auction construction, the
partition covers the entire available-depth interval, including both endpoints.
The nonempty level sets are supplied by the sup-based
`CompletedInverse.levelSet_nonempty` rather than by the thesis's finite polygonal
segment cover (`FinitePricePathSource.actual_levelSet_nonempty`). -/
def inversePartition_of_constantTails (lower upper : ℝ)
    (P : AffinePartition (Icc lo hi) E) (hE : Monotone E) (hlohi : lo ≤ hi)
    (hlower : ∀ p < lo, E p = lower) (hupper : ∀ p, hi < p → E p = upper) :
    AffinePartition (Icc lower upper) (midpointPrice lo hi E) :=
  inversePartition P hE (Icc lower upper) ordConnected_Icc
    (fun q hq => levelSet_nonempty lo hi lower upper E hlohi hE hlower hupper q hq)

end Thesis.DayAhead.PolygonalInverse
