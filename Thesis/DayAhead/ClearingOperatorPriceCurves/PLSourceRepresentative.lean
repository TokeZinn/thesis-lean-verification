import Thesis.DayAhead.ClearingOperatorPriceCurves.PLBreakpointGrid
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalFiniteAffinity
import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedInterpolation
import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedImpactCurve
import Mathlib.Order.Interval.Set.Infinite

/-! # The source representative of a monotone finite-affine price curve

The thesis selects the right limit before the terminal endpoint and the left
limit at that endpoint. A singleton domain retains its original value. This
module constructs that representative from the actual curve and compares its
intrinsic nodes and canonical encoding with those of a midpoint selection.
-/

noncomputable section
namespace Thesis.DayAhead.PLSourceRepresentative

open Set Filter Topology MeasureTheory PiecewiseAffinePriceCurves PLCanonicalEncoding
open SidedParametrisation PriceCurves PriceCurveHilbert

def clampPoint (f : Curve) (x : ℝ) : Icc f.leftEndpoint f.rightEndpoint :=
  ⟨max f.leftEndpoint (min f.rightEndpoint x), le_max_left _ _,
    max_le (f.left_nonpos.trans f.right_nonneg) (min_le_left _ _)⟩

def boundedPrice (f : Curve) (x : ℝ) : ℝ := f.price (clampPoint f x)

theorem boundedPrice_monotone (f : Curve) : Monotone (boundedPrice f) := by
  intro x y hxy
  exact f.monotone (clampPoint f x).property (clampPoint f y).property
    (max_le_max le_rfl (min_le_min le_rfl hxy))

theorem boundedPrice_eq (f : Curve) {x : ℝ} (hx : x ∈ Icc f.leftEndpoint f.rightEndpoint) :
    boundedPrice f x = f.price x := by
  simp [boundedPrice, clampPoint, min_eq_right hx.2, max_eq_right hx.1]

theorem boundedPrice_eventually_eq (f : Curve) {x : ℝ}
    (hx : x ∈ Ioo f.leftEndpoint f.rightEndpoint) :
    boundedPrice f =ᶠ[𝓝 x] f.price := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact boundedPrice_eq f ⟨hy.1.le, hy.2.le⟩

def selectedPrice (f : Curve) (x : ℝ) : ℝ :=
  if f.leftEndpoint = f.rightEndpoint then f.price x
  else if x < f.rightEndpoint then (boundedPrice f).rightLim x
  else (boundedPrice f).leftLim f.rightEndpoint

theorem selectedPrice_monotone (f : Curve) (h : f.leftEndpoint ≠ f.rightEndpoint) :
    Monotone (selectedPrice f) := by
  intro x y hxy
  simp only [selectedPrice, if_neg h]
  by_cases hx : x < f.rightEndpoint
  · by_cases hy : y < f.rightEndpoint
    · simp only [if_pos hx, if_pos hy]
      exact (boundedPrice_monotone f).rightLim hxy
    · simp only [if_pos hx, if_neg hy]
      exact (boundedPrice_monotone f).rightLim_le_leftLim hx
  · have hy : ¬y < f.rightEndpoint := fun hy => hx (hxy.trans_lt hy)
    simp only [if_neg hx, if_neg hy, le_refl]

theorem core_interior (f : Curve)
    (P : AffinePartition (Icc f.leftEndpoint f.rightEndpoint) f.price)
    (i : Fin P.count) {x : ℝ} (hx : x ∈ PolygonalInverse.sourceCell P i 0) :
    x ∈ Ioo f.leftEndpoint f.rightEndpoint := by
  change x ∈ P.piece i ∩ Ioo (sInf (P.piece i)) (sSup (P.piece i)) at hx
  obtain ⟨l, hl, hlx⟩ := (csInf_lt_iff (PolygonalInverse.piece_bddBelow P i) ⟨x, hx.1⟩).mp hx.2.1
  obtain ⟨r, hr, hxr⟩ := (lt_csSup_iff (PolygonalInverse.piece_bddAbove P i) ⟨x, hx.1⟩).mp hx.2.2
  exact ⟨(P.piece_subset i hl).1.trans_lt hlx, hxr.trans_le (P.piece_subset i hr).2⟩

theorem selectedPrice_eq_on_core (f : Curve)
    (P : AffinePartition (Icc f.leftEndpoint f.rightEndpoint) f.price)
    (i : Fin P.count) {x : ℝ} (hx : x ∈ PolygonalInverse.sourceCell P i 0) :
    selectedPrice f x = f.price x := by
  have hi := core_interior f P i hx
  have hne : f.leftEndpoint ≠ f.rightEndpoint := ne_of_lt (hi.1.trans hi.2)
  have hc : ContinuousAt (boundedPrice f) x :=
    (PolygonalInverse.continuousAt_core P i hx).congr_of_eventuallyEq
      (boundedPrice_eventually_eq f hi)
  rw [selectedPrice, if_neg hne, if_pos hi.2, hc.continuousWithinAt.rightLim_eq,
    boundedPrice_eq f ⟨hi.1.le, hi.2.le⟩]

def selectedPartition (f : Curve)
    (P : AffinePartition (Icc f.leftEndpoint f.rightEndpoint) f.price) :
    AffinePartition (Icc f.leftEndpoint f.rightEndpoint) (selectedPrice f) where
  count := Fintype.card (Fin P.count × Fin 3)
  piece := fun k =>
    let ik := (Fintype.equivFin (Fin P.count × Fin 3)).symm k
    PolygonalInverse.sourceCell P ik.1 ik.2
  interval := fun k => PolygonalInverse.sourceCell_interval P _ _
  disjoint := by
    intro i j hij
    apply PolygonalInverse.sourceCell_disjoint
    exact fun h => hij ((Fintype.equivFin (Fin P.count × Fin 3)).symm.injective h)
  cover := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, k, hik⟩ := (PolygonalInverse.sourceCell_cover P x).mp hx
      exact ⟨Fintype.equivFin _ (i, k), by simpa using hik⟩
    · rintro ⟨k, hk⟩
      exact (PolygonalInverse.sourceCell_cover P x).mpr ⟨_, _, hk⟩
  affine := by
    intro k
    generalize (Fintype.equivFin (Fin P.count × Fin 3)).symm k = ik
    obtain ⟨i, j⟩ := ik
    fin_cases j
    · obtain ⟨a, b, hab⟩ := P.affine i
      exact ⟨a, b, fun x hx => (selectedPrice_eq_on_core f P i hx).trans
        (hab x (PolygonalInverse.sourceCell_subset P i 0 hx))⟩
    · refine ⟨0, selectedPrice f (sInf (P.piece i)), fun x hx => ?_⟩
      change x ∈ P.piece i ∩ {sInf (P.piece i)} at hx
      simp [mem_singleton_iff.mp hx.2]
    · refine ⟨0, selectedPrice f (sSup (P.piece i)), fun x hx => ?_⟩
      by_cases he : sInf (P.piece i) = sSup (P.piece i)
      · simp [PolygonalInverse.sourceCell, he] at hx
      · have hxs : x = sSup (P.piece i) := by
          simp only [PolygonalInverse.sourceCell, Fin.reduceFinMk, Fin.isValue,
            if_false, Fin.reduceEq, if_neg he] at hx
          exact hx.2
        simp [hxs]

def representative (f : Curve) : Curve where
  leftEndpoint := f.leftEndpoint
  rightEndpoint := f.rightEndpoint
  left_nonpos := f.left_nonpos
  right_nonneg := f.right_nonneg
  price := selectedPrice f
  monotone := by
    by_cases he : f.leftEndpoint = f.rightEndpoint
    · intro x hx y hy hxy
      simp only [selectedPrice, if_pos he]
      exact f.monotone hx hy hxy
    · exact (selectedPrice_monotone f he).monotoneOn _
  pieces := ⟨selectedPartition f (Classical.choice f.pieces)⟩

@[simp] theorem representative_left (f : Curve) :
    (representative f).leftEndpoint = f.leftEndpoint := rfl
@[simp] theorem representative_right (f : Curve) :
    (representative f).rightEndpoint = f.rightEndpoint := rfl
@[simp] theorem representative_price (f : Curve) : (representative f).price = selectedPrice f := rfl

def LocallyAffine (g : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ a b : ℝ, ∀ᶠ y in 𝓝 x, g y = a * y + b

theorem locallyAffine_congr {g h : ℝ → ℝ} {x : ℝ} (he : g =ᶠ[𝓝 x] h) :
    LocallyAffine g x ↔ LocallyAffine h x := by
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, he.symm.trans hab⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, he.trans hab⟩

/-- A monotone point selection cannot create or erase a locally affine join
when it is replaced by its right limit. If both limits coincide, monotonicity
forces the original point value to equal that common limit. -/
theorem locallyAffine_rightLim_iff (g : ℝ → ℝ) (hg : Monotone g) (x : ℝ) :
    LocallyAffine g.rightLim x ↔ LocallyAffine g x := by
  constructor
  · rintro ⟨a, b, hab⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hab
    refine ⟨a, b, ?_⟩
    filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    have he : g.rightLim =ᶠ[𝓝 y] (fun t => a * t + b) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with t ht
      exact hball ht
    have hc : ContinuousAt g.rightLim y :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt
        |>.congr_of_eventuallyEq he
    have hl : g.leftLim y = g.rightLim y :=
      (leftLim_rightLim (hg.tendsto_leftLim y)).symm.trans
        hc.continuousWithinAt.leftLim_eq
    have hv : g y = g.rightLim y := le_antisymm (hg.le_rightLim le_rfl) (by
      rw [← hl]
      exact hg.leftLim_le le_rfl)
    exact hv.trans (hball hy)
  · rintro ⟨a, b, hab⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hab
    refine ⟨a, b, ?_⟩
    filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    have he : g =ᶠ[𝓝 y] (fun t => a * t + b) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with t ht
      exact hball ht
    have hc : ContinuousAt g y :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt
        |>.congr_of_eventuallyEq he
    exact hc.continuousWithinAt.rightLim_eq.trans (hball hy)

theorem affineNear_representative_iff (f : Curve) {x : ℝ}
    (hx : x ∈ Ioo f.leftEndpoint f.rightEndpoint) :
    AffineNear (representative f) x ↔ AffineNear f x := by
  have hne : f.leftEndpoint ≠ f.rightEndpoint := ne_of_lt (hx.1.trans hx.2)
  have he : selectedPrice f =ᶠ[𝓝 x] (boundedPrice f).rightLim := by
    filter_upwards [isOpen_Iio.mem_nhds hx.2] with y hy
    change y < f.rightEndpoint at hy
    simp only [selectedPrice, if_neg hne, if_pos hy]
  change LocallyAffine (selectedPrice f) x ↔ LocallyAffine f.price x
  exact (locallyAffine_congr he).trans
    ((locallyAffine_rightLim_iff _ (boundedPrice_monotone f) x).trans
      (locallyAffine_congr (boundedPrice_eventually_eq f hx)))

theorem breakpoints_representative (f : Curve) :
    breakpoints (representative f) = breakpoints f := by
  ext x
  by_cases hx : x ∈ Ioo f.leftEndpoint f.rightEndpoint
  · simp only [breakpoints, representative_left, representative_right, mem_setOf_eq,
      affineNear_representative_iff f hx]
  · simp only [breakpoints, representative_left, representative_right, mem_setOf_eq]
    tauto

theorem leftNodes_representative (f : Curve) :
    leftNodes (representative f) = leftNodes f := by
  simp [leftNodes, breakpoints_representative]

theorem rightNodes_representative (f : Curve) :
    rightNodes (representative f) = rightNodes f := by
  simp [rightNodes, breakpoints_representative]

theorem interpolation_enumeration_congr {s t : Finset ℝ} (h : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) (u : ℝ) :
    uniformInterpolation (enumeration s hs) u = uniformInterpolation (enumeration t ht) u := by
  subst t
  rfl

theorem quantityReal_representative (f : Curve) :
    quantityReal (representative f) = quantityReal f := by
  funext u
  by_cases hu : u ≤ 0
  · simp only [quantityReal, if_pos hu]
    exact interpolation_enumeration_congr (leftNodes_representative f) _ _ (u + 1)
  · simp only [quantityReal, if_neg hu]
    exact interpolation_enumeration_congr (rightNodes_representative f) _ _ u

theorem parametriser_representative (f : Curve) :
    parametriser (representative f) = parametriser f := by
  funext u
  apply Subtype.ext
  exact congrFun (quantityReal_representative f) u

theorem selectedPrice_eq_rightLim (f : Curve) {x : ℝ}
    (hx : x ∈ Ico f.leftEndpoint f.rightEndpoint) :
    selectedPrice f x = f.price.rightLim x := by
  have hne : f.leftEndpoint ≠ f.rightEndpoint := ne_of_lt (hx.1.trans_lt hx.2)
  have he : boundedPrice f =ᶠ[𝓝[>] x] f.price := by
    filter_upwards [Ioo_mem_nhdsGT hx.2] with y hy
    exact boundedPrice_eq f ⟨hx.1.trans hy.1.le, hy.2.le⟩
  have hl : f.price.rightLim x = (boundedPrice f).rightLim x :=
    rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
      (((boundedPrice_monotone f).tendsto_rightLim x).congr' he)
  simp only [selectedPrice, if_neg hne, if_pos hx.2, hl]

theorem selectedPrice_eq_terminal_leftLim (f : Curve)
    (h : f.leftEndpoint < f.rightEndpoint) :
    selectedPrice f f.rightEndpoint = f.price.leftLim f.rightEndpoint := by
  have he : boundedPrice f =ᶠ[𝓝[<] f.rightEndpoint] f.price := by
    filter_upwards [Ioo_mem_nhdsLT h] with y hy
    exact boundedPrice_eq f ⟨hy.1.le, hy.2.le⟩
  have hl : f.price.leftLim f.rightEndpoint = (boundedPrice f).leftLim f.rightEndpoint :=
    leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
      (((boundedPrice_monotone f).tendsto_leftLim f.rightEndpoint).congr' he)
  simp only [selectedPrice, if_neg (ne_of_lt h), lt_self_iff_false, if_false, hl]

theorem selectedPrice_singleton (f : Curve) (h : f.leftEndpoint = f.rightEndpoint) :
    selectedPrice f = f.price := by funext x; simp [selectedPrice, h]

theorem selectedPrice_right_continuous (f : Curve) {x : ℝ}
    (hx : x ∈ Ico f.leftEndpoint f.rightEndpoint) :
    ContinuousWithinAt (selectedPrice f) (Ici x) x := by
  have hne : f.leftEndpoint ≠ f.rightEndpoint := ne_of_lt (hx.1.trans_lt hx.2)
  have he : selectedPrice f =ᶠ[𝓝 x] (boundedPrice f).rightLim := by
    filter_upwards [isOpen_Iio.mem_nhds hx.2] with y hy
    change y < f.rightEndpoint at hy
    simp only [selectedPrice, if_neg hne, if_pos hy]
  exact (continuousWithinAt_rightLim_Ici
    ((boundedPrice_monotone f).tendsto_rightLim x)).congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds

theorem selectedPrice_terminal_left_continuous (f : Curve)
    (h : f.leftEndpoint < f.rightEndpoint) :
    ContinuousWithinAt (selectedPrice f) (Iic f.rightEndpoint) f.rightEndpoint := by
  apply continuousWithinAt_Iio_iff_Iic.mp
  have he : (boundedPrice f).rightLim =ᶠ[𝓝[<] f.rightEndpoint] selectedPrice f := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    change y < f.rightEndpoint at hy
    simp only [selectedPrice, if_neg (ne_of_lt h), if_pos hy]
  have hl := (boundedPrice_monotone f).rightLim.tendsto_leftLim f.rightEndpoint
  rw [leftLim_rightLim ((boundedPrice_monotone f).tendsto_leftLim _)] at hl
  change Tendsto (selectedPrice f) (𝓝[<] f.rightEndpoint)
    (𝓝 (selectedPrice f f.rightEndpoint))
  simpa only [selectedPrice, if_neg (ne_of_lt h), lt_self_iff_false, if_false] using hl.congr' he

def exceptional (f : Curve) : Set ℝ :=
  breakpoints f ∪ {f.leftEndpoint, 0, f.rightEndpoint}

theorem exceptional_finite (f : Curve) : (exceptional f).Finite :=
  (breakpoints_finite f).union (by simp)

theorem selectedPrice_eq_off_exceptional (f : Curve) {x : ℝ}
    (hx : x ∈ Icc f.leftEndpoint f.rightEndpoint) (hnot : x ∉ exceptional f) :
    selectedPrice f x = f.price x := by
  have hneL : x ≠ f.leftEndpoint := fun he => hnot (Or.inr (by simp [he]))
  have hneR : x ≠ f.rightEndpoint := fun he => hnot (Or.inr (by simp [he]))
  have hne0 : x ≠ 0 := fun he => hnot (Or.inr (by simp [he]))
  have hi : x ∈ Ioo f.leftEndpoint f.rightEndpoint :=
    ⟨lt_of_le_of_ne hx.1 hneL.symm, lt_of_le_of_ne hx.2 hneR⟩
  have ha : AffineNear f x := by
    by_contra ha
    exact hnot (Or.inl ⟨hi, hne0, ha⟩)
  have hc : ContinuousAt (boundedPrice f) x :=
    (PLBreakpointCollinearity.affineNear_continuousAt f x ha).congr_of_eventuallyEq
      (boundedPrice_eventually_eq f hi)
  rw [selectedPrice, if_neg (ne_of_lt (hi.1.trans hi.2)), if_pos hi.2,
    hc.continuousWithinAt.rightLim_eq, boundedPrice_eq f hx]

/-- Strict knots give a strictly increasing uniform interpolant on its
noncollapsed parameter interval. A finite grid argument finds an open ramp
inside any nonempty interval, avoiding a floor-function convention. -/
theorem uniformInterpolation_strictMonoOn {n : ℕ} (hn : 0 < n)
    (knot : Fin (n + 1) → ℝ) (hk : StrictMono knot) :
    StrictMonoOn (uniformInterpolation knot) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let grid : Fin (n + 1) → ℝ := fun j => (j : ℝ) / n
  have hfirst : grid 0 = 0 := by simp [grid]
  have hlast : grid (Fin.last n) = 1 := by simp [grid, hn.ne']
  obtain ⟨w, hw, hnot⟩ := (Set.Ioo_infinite hxy).exists_notMem_finite (Set.finite_range grid)
  obtain ⟨i, hi⟩ := OfferedPartition.piece_cover grid w
  have hgap : ∃ j : Fin n, w ∈ Ioo (grid j.castSucc) (grid j.succ) := by
    cases i with
    | inl v =>
      have he : w = v.val := hi
      exact False.elim (hnot (he.symm ▸ v.property))
    | inr k =>
      cases k with
      | inl j => exact ⟨j, hi⟩
      | inr k =>
        fin_cases k
        · have hh : w < 0 := by simpa [OfferedPartition.piece, hfirst] using hi
          exact False.elim (not_lt_of_ge (hx.1.trans hw.1.le) hh)
        · have hh : 1 < w := by simpa [OfferedPartition.piece, hlast] using hi
          exact False.elim (not_lt_of_ge (hw.2.le.trans hy.2) hh)
  obtain ⟨j, hj⟩ := hgap
  obtain ⟨z₁, hz₁, hz₁w⟩ := exists_between (max_lt hw.1 hj.1)
  obtain ⟨z₂, hwz₂, hz₂⟩ := exists_between (lt_min hw.2 hj.2)
  have hxz₁ : x < z₁ := (le_max_left _ _).trans_lt hz₁
  have hz₁l : grid j.castSucc < z₁ := (le_max_right _ _).trans_lt hz₁
  have hz₂y : z₂ < y := hz₂.trans_le (min_le_left _ _)
  have hz₂r : z₂ < grid j.succ := hz₂.trans_le (min_le_right _ _)
  have hzz : z₁ < z₂ := hz₁w.trans hwz₂
  have h₁ := uniformInterpolation_on_block knot j hz₁l.le
    (by simpa [grid] using (hz₁w.trans hj.2).le)
  have h₂ := uniformInterpolation_on_block knot j (hj.1.trans hwz₂).le
    (by simpa [grid] using hz₂r.le)
  have hstrict : uniformInterpolation knot z₁ < uniformInterpolation knot z₂ := by
    rw [h₁, h₂]
    have harg : (n : ℝ) * z₁ - j < (n : ℝ) * z₂ - j := by nlinarith
    have hterm := mul_lt_mul_of_pos_left harg
      (sub_pos.mpr (hk (Fin.castSucc_lt_succ (i := j))))
    linarith
  exact ((monotone_uniformInterpolation knot hk.monotone hxz₁.le).trans_lt hstrict).trans_le
    (monotone_uniformInterpolation knot hk.monotone hz₂y.le)

theorem leftCount_pos (f : Curve) (hl : f.leftEndpoint < 0) : 0 < leftCount f := by
  have hc : 1 < (leftNodes f).card := Finset.one_lt_card.mpr
    ⟨f.leftEndpoint, by simp [leftNodes], 0, by simp [leftNodes], ne_of_lt hl⟩
  unfold leftCount count
  omega

theorem rightCount_pos (f : Curve) (hr : 0 < f.rightEndpoint) : 0 < rightCount f := by
  have hc : 1 < (rightNodes f).card := Finset.one_lt_card.mpr
    ⟨0, by simp [rightNodes], f.rightEndpoint, by simp [rightNodes], ne_of_lt hr⟩
  unfold rightCount count
  omega

theorem quantityReal_strictMonoOn (f : Curve) (hl : f.leftEndpoint < 0)
    (hr : 0 < f.rightEndpoint) : StrictMonoOn (quantityReal f) (Icc (-1 : ℝ) 1) := by
  have hleft := uniformInterpolation_strictMonoOn (leftCount_pos f hl) (leftKnot f)
    (enumeration _ (leftNodes_nonempty f)).strictMono
  have hright := uniformInterpolation_strictMonoOn (rightCount_pos f hr) (rightKnot f)
    (enumeration _ (rightNodes_nonempty f)).strictMono
  intro u hu v hv huv
  by_cases hu0 : u ≤ 0
  · by_cases hv0 : v ≤ 0
    · simp only [quantityReal, if_pos hu0, if_pos hv0]
      exact hleft ⟨by linarith [hu.1], by linarith⟩
        ⟨by linarith [hv.1], by linarith⟩ (by linarith)
    · have hvp : 0 < v := lt_of_not_ge hv0
      calc
        quantityReal f u ≤ quantityReal f 0 := quantityReal_monotone f hu0
        _ < quantityReal f v := by
          rw [quantityReal_zero, quantityReal, if_neg hv0]
          simpa only [uniformInterpolation_zero, rightKnot_first] using
            hright (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) ⟨hvp.le, hv.2⟩ hvp
  · have hv0 : ¬v ≤ 0 := fun h => hu0 (huv.le.trans h)
    simp only [quantityReal, if_neg hu0, if_neg hv0]
    exact hright ⟨(lt_of_not_ge hu0).le, hu.2⟩ ⟨(lt_of_not_ge hv0).le, hv.2⟩ huv

theorem quantity_injective (f : Curve) (hl : f.leftEndpoint < 0) (hr : 0 < f.rightEndpoint) :
    Function.Injective (fun u : Parameter => quantityReal f u) := by
  intro u v huv
  exact Subtype.ext ((quantityReal_strictMonoOn f hl hr).injOn u.property v.property huv)

theorem encoding_eq_off_exceptional (f : Curve) (u : Parameter)
    (hu : quantityReal f u ∉ exceptional f) :
    encoding (representative f) u = encoding f u := by
  change (quantityReal (representative f) u,
      selectedPrice f (quantityReal (representative f) u)) =
    (quantityReal f u, f.price (quantityReal f u))
  rw [quantityReal_representative]
  exact Prod.ext rfl (selectedPrice_eq_off_exceptional f (parametriser f u).property hu)

/-- A source representative changes only finitely many canonical parameter
values on a noncollapsed two-sided domain. Consequently every atomless
parameter measure gives the same encoded equivalence class. -/
theorem encoding_ae_representative (μ : Measure Parameter) [NoAtoms μ]
    (f : Curve) (hl : f.leftEndpoint < 0) (hr : 0 < f.rightEndpoint) :
    encoding (representative f) =ᵐ[μ] encoding f := by
  have hfin : ((fun u : Parameter => quantityReal f u) ⁻¹' exceptional f).Finite :=
    (exceptional_finite f).preimage
      (fun _ _ _ _ h => quantity_injective f hl hr h)
  filter_upwards [hfin.countable.ae_notMem μ] with u hu
  exact encoding_eq_off_exceptional f u hu

theorem encodingLp_representative (μ : Measure Parameter) [IsFiniteMeasure μ] [NoAtoms μ]
    (f : Curve) (hl : f.leftEndpoint < 0) (hr : 0 < f.rightEndpoint) :
    encodingLp μ (representative f) = encodingLp μ f := by
  apply Lp.ext
  filter_upwards [PLParametrisation.coeFn_encodingLp μ (representative f)
      (admissible (representative f)), PLParametrisation.coeFn_encodingLp μ f (admissible f),
      encoding_ae_representative μ f hl hr] with u hrep hf he
  exact hrep.trans ((congrArg pairEquiv he).trans hf.symm)

theorem encoding_representative_singleton (f : Curve)
    (h : f.leftEndpoint = f.rightEndpoint) : encoding (representative f) = encoding f := by
  funext u
  change (quantityReal (representative f) u,
      selectedPrice f (quantityReal (representative f) u)) =
    (quantityReal f u, f.price (quantityReal f u))
  rw [quantityReal_representative, selectedPrice_singleton f h]

/-- The vendor's positive sell and buy terminal volumes ensure that neither
parameter side collapses. Thus its raw midpoint inverse and source-selected
representative give exactly the same Hilbert-valued encoding. The companion
crossing-price coordinate remains the raw `m.price 0`. -/
theorem book_encodingLp_representative (μ : Measure Parameter)
    [IsFiniteMeasure μ] [NoAtoms μ] {lo hi : ℝ} (m : ExcessSupply.Book lo hi)
    (hbuy : 0 < m.buyDepth) (hsell : 0 < m.sellDepth) :
    encodingLp μ (representative (InterpolatedImpactCurve.Book.impactCurve m)) =
      encodingLp μ (InterpolatedImpactCurve.Book.impactCurve m) := by
  apply encodingLp_representative
  · change -m.buyDepth < 0
    linarith
  · exact hsell

end Thesis.DayAhead.PLSourceRepresentative
