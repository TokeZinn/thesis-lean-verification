import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLQuantityCells

/-! # Positive terminal depths of the literal vendor parser

Sorting preserves the maximum cumulative volume. Running maxima and
differencing therefore give exactly that maximum as the parsed depth.
The source's positive-volume restriction is a Borel subtype, and maps from
it extend measurably by a fixed default on the remaining bounded data. -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Thesis.DayAhead.VendorPLPositiveDepth

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLQuantityCells
open scoped NNReal

theorem runningMax_last {n : ℕ} (v : Fin n → ℝ≥0) :
    runningMax v (Fin.last n) = Finset.univ.sup v := by
  have hfilter : (Finset.univ.filter fun j : Fin n ↦ j.val < (Fin.last n).val) =
      Finset.univ := by
    ext j
    simp
  simp only [runningMax, hfilter]

theorem sorted_volume_sup {n : ℕ} (buy : Bool) (x : RawSide n) :
    Finset.univ.sup (fun i ↦ (sorted buy x i).2) =
      Finset.univ.sup (fun i ↦ (x i).2) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    exact Finset.le_sup (f := fun j : Fin n ↦ (x j).2)
      (Finset.mem_univ (sortPermutation buy x i))
  · apply Finset.sup_le
    intro i _
    let j := (sortPermutation buy x).symm i
    have hj : (sorted buy x j).2 = (x i).2 := by
      simp only [sorted, j, Equiv.apply_symm_apply]
    rw [← hj]
    exact Finset.le_sup (f := fun i : Fin n ↦ (sorted buy x i).2) (Finset.mem_univ j)

/-- Terminal cumulative volume after the literal sorting/running-max parser
is the maximum of the original vendor cumulative volumes. -/
theorem cumulative_last_eq_raw_max {n : ℕ} (buy : Bool) (x : RawSide n) :
    cumulative buy x (Fin.last n) =
      (Finset.univ.sup (fun i ↦ (x i).2) : ℝ≥0) := by
  rw [cumulative, runningMax_last, sorted_volume_sup]

theorem cumulative_last_pos_iff {n : ℕ} (buy : Bool) (x : RawSide n) :
    0 < cumulative buy x (Fin.last n) ↔ ∃ i, 0 < (x i).2 := by
  rw [cumulative_last_eq_raw_max]
  norm_cast
  simp only [Finset.lt_sup_iff, Finset.mem_univ, true_and]

theorem parsed_buyDepth_eq_raw_max {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}
    (x : BoundedLayer lo hi ns nb) :
    (book hlohi x).buyDepth =
      (Finset.univ.sup (fun i ↦ (x.val.2 i).2) : ℝ≥0) := by
  change InterpolatedSide.cumulative (parsedBook lo hi hlohi x.val x.property).buyVolume
    (Fin.last (nb + 1)) = _
  rw [parsedBook_buy_cumulative]
  exact cumulative_last_eq_raw_max true x.val.2

theorem parsed_sellDepth_eq_raw_max {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}
    (x : BoundedLayer lo hi ns nb) :
    (book hlohi x).sellDepth =
      (Finset.univ.sup (fun i ↦ (x.val.1 i).2) : ℝ≥0) := by
  change InterpolatedSide.cumulative (parsedBook lo hi hlohi x.val x.property).sellVolume
    (Fin.last (ns + 1)) = _
  rw [parsedBook_sell_cumulative]
  exact cumulative_last_eq_raw_max false x.val.1

/-- The source raw positive-volume condition is exactly positive parsed
buy-side depth, even when there are repeated prices or zero increments. -/
theorem buyDepth_pos_iff_raw_positive {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}
    (x : BoundedLayer lo hi ns nb) :
    0 < (book hlohi x).buyDepth ↔ ∃ i, 0 < (x.val.2 i).2 := by
  rw [parsed_buyDepth_eq_raw_max]
  norm_cast
  simp only [Finset.lt_sup_iff, Finset.mem_univ, true_and]

theorem sellDepth_pos_iff_raw_positive {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}
    (x : BoundedLayer lo hi ns nb) :
    0 < (book hlohi x).sellDepth ↔ ∃ i, 0 < (x.val.1 i).2 := by
  rw [parsed_sellDepth_eq_raw_max]
  norm_cast
  simp only [Finset.lt_sup_iff, Finset.mem_univ, true_and]

abbrev PositiveLayer {lo hi : ℝ} (hlohi : lo ≤ hi) (ns nb : ℕ) :=
  {x : BoundedLayer lo hi ns nb //
    0 < (book hlohi x).buyDepth ∧ 0 < (book hlohi x).sellDepth}

theorem measurableSet_positive {lo hi : ℝ} (hlohi : lo ≤ hi) (ns nb : ℕ) :
    MeasurableSet {x : BoundedLayer lo hi ns nb |
      0 < (book hlohi x).buyDepth ∧ 0 < (book hlohi x).sellDepth} :=
  (measurableSet_lt measurable_const (measurable_buyDepth hlohi)).inter
    (measurableSet_lt measurable_const (measurable_sellDepth hlohi))

def positiveExtension {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ} {Y : Type*}
    (defaultValue : Y) (f : PositiveLayer hlohi ns nb → Y)
    (x : BoundedLayer lo hi ns nb) : Y :=
  if h : 0 < (book hlohi x).buyDepth ∧ 0 < (book hlohi x).sellDepth then
    f ⟨x, h⟩ else defaultValue

theorem measurable_positiveExtension {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}
    {Y : Type*} [MeasurableSpace Y] (defaultValue : Y)
    (f : PositiveLayer hlohi ns nb → Y) (hf : Measurable f) :
    Measurable (positiveExtension hlohi defaultValue f) := by
  apply measurable_of_restrict_of_restrict_compl (measurableSet_positive hlohi ns nb)
  · convert hf using 1
    funext x
    simp only [Set.restrict_apply, positiveExtension]
    split_ifs with hx
    · rfl
    · exact False.elim (hx x.property)
  · convert (measurable_const : Measurable (fun _ :
      {x : BoundedLayer lo hi ns nb //
        ¬(0 < (book hlohi x).buyDepth ∧ 0 < (book hlohi x).sellDepth)} ↦ defaultValue)) using 1
    funext x
    simp only [Set.restrict_apply, positiveExtension]
    split_ifs with hx
    · exact False.elim (x.property hx)
    · rfl

@[simp] theorem positiveExtension_on_positive {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}
    {Y : Type*} (defaultValue : Y) (f : PositiveLayer hlohi ns nb → Y)
    (x : PositiveLayer hlohi ns nb) :
    positiveExtension hlohi defaultValue f x.val = f x := by
  simp only [positiveExtension, dif_pos x.property]

end Thesis.DayAhead.VendorPLPositiveDepth
