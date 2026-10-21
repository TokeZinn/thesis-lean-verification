import Thesis.Appendices.DayAheadNumerical.NumericalDecoding
import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedSide

/-! # The current collapsed-point forecast price reader

Each of the 1000 price cells contributes its mean endpoint quantity. Equal
abscissas are grouped and carry the least and greatest associated prices.
The selected value at such a point is their midpoint. Between points the
reader joins the greater left price to the lesser right price. Within the
quantity domain, exterior continuation uses the selected outer midpoint;
this makes explicit the value of the source's constant-continuation rule.
-/

noncomputable section
namespace Thesis.DayAhead.ForecastReader

set_option maxRecDepth 4096

open Set NumericalDecoding

def abscissa (z : GridValues) (i : Fin 1000) : ℝ :=
  (z.quantity i.castSucc + z.quantity i.succ) / 2

def abscissas (z : GridValues) : Finset ℝ := Finset.univ.image (abscissa z)

theorem abscissas_nonempty (z : GridValues) : (abscissas z).Nonempty :=
  Finset.image_nonempty.mpr Finset.univ_nonempty

abbrev Point (z : GridValues) := {x : ℝ // x ∈ abscissas z}

def cellPrices (z : GridValues) (x : Point z) : Finset ℝ :=
  (Finset.univ.filter fun i => abscissa z i = x.val).image z.price

theorem cellPrices_nonempty (z : GridValues) (x : Point z) : (cellPrices z x).Nonempty := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
  exact ⟨z.price i, Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩⟩

attribute [local irreducible] abscissas

def lowerPrice (z : GridValues) (x : Point z) : ℝ :=
  (cellPrices z x).min' (cellPrices_nonempty z x)

def upperPrice (z : GridValues) (x : Point z) : ℝ :=
  (cellPrices z x).max' (cellPrices_nonempty z x)

def selectedPrice (z : GridValues) (x : Point z) : ℝ :=
  (lowerPrice z x + upperPrice z x) / 2

def firstPoint (z : GridValues) : Point z :=
  ⟨(abscissas z).min' (abscissas_nonempty z), Finset.min'_mem _ _⟩

def lastPoint (z : GridValues) : Point z :=
  ⟨(abscissas z).max' (abscissas_nonempty z), Finset.max'_mem _ _⟩

def leftPoints (z : GridValues) (x : ℝ) : Finset ℝ :=
  (abscissas z).filter fun q => q < x

def rightPoints (z : GridValues) (x : ℝ) : Finset ℝ :=
  (abscissas z).filter fun q => x < q

def leftPoint (z : GridValues) (x : ℝ) (h : (leftPoints z x).Nonempty) : Point z :=
  ⟨(leftPoints z x).max' h, (Finset.mem_filter.mp (Finset.max'_mem _ _)).1⟩

def rightPoint (z : GridValues) (x : ℝ) (h : (rightPoints z x).Nonempty) : Point z :=
  ⟨(rightPoints z x).min' h, (Finset.mem_filter.mp (Finset.min'_mem _ _)).1⟩

def quantityDomain (z : GridValues) : Set ℝ := Icc (z.quantity 0) (z.quantity (Fin.last 1000))

def read (z : GridValues) (x : ℝ) : Option ℝ := by
  classical
  exact if x ∈ quantityDomain z then
    if hx : x ∈ abscissas z then some (selectedPrice z ⟨x, hx⟩) else
    if hl : (leftPoints z x).Nonempty then
      if hr : (rightPoints z x).Nonempty then
        some (InterpolatedSide.interpolate (leftPoint z x hl) (rightPoint z x hr)
          (upperPrice z (leftPoint z x hl)) (lowerPrice z (rightPoint z x hr)) x)
      else some (selectedPrice z (lastPoint z))
    else some (selectedPrice z (firstPoint z))
  else none

def readDecoded (lo hi : ℝ) (h : lo ≤ hi) (forecast : GridValues) (x : ℝ) : Option ℝ :=
  read (decoded lo hi h forecast) x

theorem read_none_iff (z : GridValues) (x : ℝ) : read z x = none ↔ x ∉ quantityDomain z := by
  classical
  unfold read
  split_ifs <;> simp_all

theorem read_at_point (z : GridValues) (x : Point z) (hx : x.val ∈ quantityDomain z) :
    read z x = some ((lowerPrice z x + upperPrice z x) / 2) := by
  classical
  simp [read, hx, x.property, selectedPrice]

theorem read_between (z : GridValues) (x : ℝ) (hx : x ∈ quantityDomain z)
    (hn : x ∉ abscissas z) (hl : (leftPoints z x).Nonempty)
    (hr : (rightPoints z x).Nonempty) :
    read z x = some (InterpolatedSide.interpolate (leftPoint z x hl) (rightPoint z x hr)
      (upperPrice z (leftPoint z x hl)) (lowerPrice z (rightPoint z x hr)) x) := by
  classical
  simp only [read, if_pos hx, dif_neg hn, dif_pos hl, dif_pos hr]

theorem neighbouring_points (z : GridValues) (x : ℝ) (hn : x ∉ abscissas z)
    (hl : (leftPoints z x).Nonempty) (hr : (rightPoints z x).Nonempty) :
    ∀ y ∈ abscissas z, ¬((leftPoint z x hl : ℝ) < y ∧ y < (rightPoint z x hr : ℝ)) := by
  intro y hy hbetween
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have hmem : y ∈ leftPoints z x := by simp [leftPoints, hy, hyx]
    exact (not_lt_of_ge (Finset.le_max' _ y hmem)) hbetween.1
  · exact hn hy
  · have hmem : y ∈ rightPoints z x := by simp [rightPoints, hy, hxy]
    exact (not_lt_of_ge (Finset.min'_le _ y hmem)) hbetween.2

theorem read_before_first (z : GridValues) (x : ℝ) (hx : x ∈ quantityDomain z)
    (hfirst : x < (firstPoint z : ℝ)) : read z x = some (selectedPrice z (firstPoint z)) := by
  classical
  have hn : x ∉ abscissas z := fun h =>
    (not_lt_of_ge (Finset.min'_le _ x h)) hfirst
  have hl : ¬(leftPoints z x).Nonempty := by
    rintro ⟨y, hy⟩
    have hy' := Finset.mem_filter.mp hy
    exact (not_lt_of_ge (Finset.min'_le _ y hy'.1)) (hy'.2.trans hfirst)
  simp only [read, if_pos hx, dif_neg hn, dif_neg hl]

theorem read_after_last (z : GridValues) (x : ℝ) (hx : x ∈ quantityDomain z)
    (hlast : (lastPoint z : ℝ) < x) : read z x = some (selectedPrice z (lastPoint z)) := by
  classical
  have hn : x ∉ abscissas z := fun h =>
    (not_lt_of_ge (Finset.le_max' _ x h)) hlast
  have hl : (leftPoints z x).Nonempty :=
    ⟨lastPoint z, by
      simp only [leftPoints, Finset.mem_filter]
      exact ⟨(lastPoint z).property, hlast⟩⟩
  have hr : ¬(rightPoints z x).Nonempty := by
    rintro ⟨y, hy⟩
    have hy' := Finset.mem_filter.mp hy
    exact (not_lt_of_ge (Finset.le_max' _ y hy'.1)) (hlast.trans hy'.2)
  simp only [read, if_pos hx, dif_neg hn, dif_pos hl, dif_neg hr]

theorem abscissa_monotone (z : GridValues) (hq : Monotone z.quantity) :
    Monotone (abscissa z) := by
  intro i j hij
  have hleft := hq (Fin.castSucc_le_castSucc_iff.mpr hij)
  have hright := hq (Fin.succ_le_succ_iff.mpr hij)
  unfold abscissa
  linarith

/-- Distinct cells are grouped together only on a zero-quantity plateau.
Thus equality-grouping implements the specified collapsed-cell rule. -/
theorem equal_abscissas_zero_width (z : GridValues) (hq : Monotone z.quantity)
    (i j : Fin 1000) (hij : i < j) (heq : abscissa z i = abscissa z j) :
    z.quantity i.castSucc = z.quantity i.succ ∧
      z.quantity j.castSucc = z.quantity j.succ := by
  have hidx : i.succ ≤ j.castSucc := by exact_mod_cast hij
  have h₁ := hq (Fin.castSucc_le_succ i)
  have h₂ := hq hidx
  have h₃ := hq (Fin.castSucc_le_succ j)
  unfold abscissa at heq
  constructor <;> linarith

theorem abscissa_mem_domain (z : GridValues) (hq : Monotone z.quantity) (i : Fin 1000) :
    abscissa z i ∈ quantityDomain z := by
  have hl := hq (Fin.zero_le i.castSucc)
  have hr := hq (Fin.le_last i.succ)
  have hi := hq (Fin.castSucc_le_succ i)
  change z.quantity 0 ≤ _ ∧ _ ≤ z.quantity (Fin.last 1000)
  unfold abscissa
  constructor <;> linarith

theorem lowerPrice_le_upperPrice (z : GridValues) (x : Point z) :
    lowerPrice z x ≤ upperPrice z x :=
  (cellPrices z x).min'_le _ ((cellPrices z x).max'_mem _)

theorem group_price_bounds (z : GridValues) (lo hi : ℝ)
    (hb : ∀ i, z.price i ∈ Icc lo hi) (x : Point z) :
    lowerPrice z x ∈ Icc lo hi ∧ upperPrice z x ∈ Icc lo hi := by
  have hset : ∀ p ∈ cellPrices z x, p ∈ Icc lo hi := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hb i
  exact ⟨hset _ (Finset.min'_mem _ _), hset _ (Finset.max'_mem _ _)⟩

theorem selectedPrice_bounds (z : GridValues) (lo hi : ℝ)
    (hb : ∀ i, z.price i ∈ Icc lo hi) (x : Point z) : selectedPrice z x ∈ Icc lo hi := by
  obtain ⟨hl, hr⟩ := group_price_bounds z lo hi hb x
  unfold selectedPrice
  constructor <;> linarith [hl.1, hl.2, hr.1, hr.2]

theorem read_bounds (z : GridValues) (lo hi : ℝ) (hb : ∀ i, z.price i ∈ Icc lo hi)
    (x p : ℝ) (hp : read z x = some p) : p ∈ Icc lo hi := by
  classical
  unfold read at hp
  split_ifs at hp with hx hn hl hr
  · cases hp
    exact selectedPrice_bounds z lo hi hb _
  · cases hp
    have hlx : (leftPoint z x hl : ℝ) < x :=
      (Finset.mem_filter.mp (Finset.max'_mem (leftPoints z x) hl)).2
    have hrx : x < (rightPoint z x hr : ℝ) :=
      (Finset.mem_filter.mp (Finset.min'_mem (rightPoints z x) hr)).2
    exact InterpolatedSide.interpolate_bounded (hlx.trans hrx) ⟨hlx.le, hrx.le⟩
      (group_price_bounds z lo hi hb _).2 (group_price_bounds z lo hi hb _).1
  · cases hp
    exact selectedPrice_bounds z lo hi hb _
  · cases hp
    exact selectedPrice_bounds z lo hi hb _

theorem readDecoded_bounds (lo hi : ℝ) (h : lo ≤ hi) (forecast : GridValues)
    (x p : ℝ) (hp : readDecoded lo hi h forecast x = some p) : p ∈ Icc lo hi :=
  read_bounds _ lo hi (prices_bounded lo hi h forecast) x p hp

end Thesis.DayAhead.ForecastReader
