import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurves
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr

/-!
# Equal-block sided parametrisation

The canonical sided construction is built from uniform piecewise-linear
interpolation.  The interpolation is written as a sum of clamped ramps; this
avoids floor functions and makes continuity and monotonicity transparent.
-/

namespace Thesis
namespace DayAhead
namespace SidedParametrisation

open MeasureTheory PriceCurves
open scoped BigOperators

noncomputable section

/-- Clamp a real number to the unit interval. -/
def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)

@[simp] theorem clampUnit_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    clampUnit x = 0 := by simp [clampUnit, hx]

@[simp] theorem clampUnit_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    clampUnit x = 1 := by simp [clampUnit, hx]

@[simp] theorem clampUnit_eq_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    clampUnit x = x := by simp [clampUnit, hx0, hx1]

@[fun_prop]
theorem continuous_clampUnit : Continuous clampUnit := by
  unfold clampUnit
  fun_prop

theorem monotone_clampUnit : Monotone clampUnit := by
  intro x y hxy
  simp only [clampUnit]
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

/-- Uniform piecewise-linear interpolation of `n + 1` ordered knots on
`[0,1]`.  The `j`th ramp turns on over `[j/n,(j+1)/n]`. -/
def uniformInterpolation {n : ℕ} (knot : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  knot 0 + ∑ j : Fin n,
    (knot j.succ - knot j.castSucc) *
      clampUnit ((n : ℝ) * t - (j : ℝ))

theorem continuous_uniformInterpolation {n : ℕ}
    (knot : Fin (n + 1) → ℝ) :
    Continuous (uniformInterpolation knot) := by
  unfold uniformInterpolation
  fun_prop

theorem monotone_uniformInterpolation {n : ℕ}
    (knot : Fin (n + 1) → ℝ) (hknot : Monotone knot) :
    Monotone (uniformInterpolation knot) := by
  intro x y hxy
  unfold uniformInterpolation
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left
  · apply monotone_clampUnit
    gcongr
  · exact sub_nonneg.mpr (hknot (Fin.castSucc_le_succ j))

@[simp]
theorem uniformInterpolation_zero {n : ℕ} (knot : Fin (n + 1) → ℝ) :
    uniformInterpolation knot 0 = knot 0 := by
  simp only [uniformInterpolation, mul_zero, zero_sub]
  simp [clampUnit]

@[simp]
theorem sum_adjacent_knot_differences {n : ℕ}
    (knot : Fin (n + 1) → ℝ) :
    (∑ j : Fin n, (knot j.succ - knot j.castSucc)) =
      knot (Fin.last n) - knot 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        simp
      have htail :
          (∑ i : Fin n,
            (knot i.succ.succ - knot i.succ.castSucc)) =
            knot (Fin.last (n + 1)) - knot (Fin.succ 0) := by
        calc
          _ = ∑ i : Fin n,
              (knot i.succ.succ - knot i.castSucc.succ) := by
            apply Finset.sum_congr rfl
            intro i _hi
            congr 2
          _ = knot (Fin.last n).succ - knot (Fin.succ 0) :=
            ih (fun i : Fin (n + 1) => knot i.succ)
          _ = _ := by rw [hlast]
      rw [htail]
      simp only [Fin.succ_zero_eq_one]
      have hzero : Fin.castSucc (0 : Fin (n + 1)) = (0 : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      rw [hzero]
      ring

@[simp]
theorem uniformInterpolation_one {n : ℕ} (knot : Fin (n + 1) → ℝ) :
    uniformInterpolation knot 1 = knot (Fin.last n) := by
  have hclamp : ∀ j : Fin n,
      clampUnit ((n : ℝ) * 1 - (j : ℝ)) = 1 := by
    intro j
    apply clampUnit_of_one_le
    have hj : (j : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast j.isLt
    linarith
  unfold uniformInterpolation
  simp_rw [hclamp]
  simp only [mul_one, sum_adjacent_knot_differences]
  ring

/-! ## Two-sided interpolation -/

/-- Equal-block knot data for a particular price-curve domain.  The left
knots run from the left endpoint to zero; the right knots run from zero to the
right endpoint. -/
structure SidedKnotData (f : PriceCurve) where
  leftCount : ℕ
  rightCount : ℕ
  leftKnot : Fin (leftCount + 1) → ℝ
  rightKnot : Fin (rightCount + 1) → ℝ
  leftKnot_monotone : Monotone leftKnot
  rightKnot_monotone : Monotone rightKnot
  left_first : leftKnot 0 = f.leftEndpoint
  left_last : leftKnot (Fin.last leftCount) = 0
  right_first : rightKnot 0 = 0
  right_last : rightKnot (Fin.last rightCount) = f.rightEndpoint
  leftLevel : Fin leftCount → ℝ
  rightLevel : Fin rightCount → ℝ
  left_block_interior : ∀ j (x : Set.Icc f.leftEndpoint f.rightEndpoint),
    leftKnot j.castSucc < (x : ℝ) → (x : ℝ) < leftKnot j.succ →
      f.price x = leftLevel j
  right_block_interior : ∀ j (x : Set.Icc f.leftEndpoint f.rightEndpoint),
    rightKnot j.castSucc < (x : ℝ) → (x : ℝ) < rightKnot j.succ →
      f.price x = rightLevel j
  leftLevel_strictMono : StrictMono leftLevel
  rightLevel_strictMono : StrictMono rightLevel

/-- Piecewise interpolation on the full real line.  Only its restriction to
`[-1,1]` is used by the sided encoder. -/
def sidedVolumeReal {f : PriceCurve} (data : SidedKnotData f) (u : ℝ) : ℝ :=
  if u ≤ 0 then uniformInterpolation data.leftKnot (u + 1)
  else uniformInterpolation data.rightKnot u

theorem continuous_sidedVolumeReal {f : PriceCurve}
    (data : SidedKnotData f) : Continuous (sidedVolumeReal data) := by
  have hleft : Continuous
      (fun u : ℝ => uniformInterpolation data.leftKnot (u + 1)) :=
    (continuous_uniformInterpolation data.leftKnot).comp
      (continuous_id.add continuous_const)
  have hright : Continuous
      (fun u : ℝ => uniformInterpolation data.rightKnot u) :=
    continuous_uniformInterpolation data.rightKnot
  apply hleft.if_le hright continuous_id continuous_const
  intro u hu
  have hu0 : u = 0 := by simpa using hu
  subst u
  simp only [zero_add, uniformInterpolation_one, uniformInterpolation_zero,
    data.left_last, data.right_first]

theorem monotone_sidedVolumeReal {f : PriceCurve}
    (data : SidedKnotData f) : Monotone (sidedVolumeReal data) := by
  have hleft := monotone_uniformInterpolation data.leftKnot
    data.leftKnot_monotone
  have hright := monotone_uniformInterpolation data.rightKnot
    data.rightKnot_monotone
  intro u v huv
  by_cases hv : v ≤ 0
  · have hu : u ≤ 0 := huv.trans hv
    simp only [sidedVolumeReal, if_pos hu, if_pos hv]
    exact hleft (by linarith)
  · by_cases hu : u ≤ 0
    · simp only [sidedVolumeReal, if_pos hu, if_neg hv]
      calc
        uniformInterpolation data.leftKnot (u + 1) ≤
            uniformInterpolation data.leftKnot 1 :=
          hleft (by linarith)
        _ = 0 := by rw [uniformInterpolation_one, data.left_last]
        _ = uniformInterpolation data.rightKnot 0 := by
          rw [uniformInterpolation_zero, data.right_first]
        _ ≤ uniformInterpolation data.rightKnot v :=
          hright (le_of_not_ge hv)
    · simp only [sidedVolumeReal, if_neg hu, if_neg hv]
      exact hright huv

@[simp]
theorem sidedVolumeReal_left {f : PriceCurve} (data : SidedKnotData f) :
    sidedVolumeReal data (-1) = f.leftEndpoint := by
  simp [sidedVolumeReal, data.left_first]

@[simp]
theorem sidedVolumeReal_zero {f : PriceCurve} (data : SidedKnotData f) :
    sidedVolumeReal data 0 = 0 := by
  simp [sidedVolumeReal, data.left_last]

@[simp]
theorem sidedVolumeReal_right {f : PriceCurve} (data : SidedKnotData f) :
    sidedVolumeReal data 1 = f.rightEndpoint := by
  simp [sidedVolumeReal, data.right_last]

/-- The two-sided interpolation, restricted to the common parameter interval,
lands in the curve's own domain. -/
def sidedDomainMap {f : PriceCurve} (data : SidedKnotData f) :
    Parameter → Set.Icc f.leftEndpoint f.rightEndpoint := fun u =>
  ⟨sidedVolumeReal data u,
    by
      calc
        f.leftEndpoint = sidedVolumeReal data (-1) :=
          (sidedVolumeReal_left data).symm
        _ ≤ sidedVolumeReal data u :=
          monotone_sidedVolumeReal data u.2.1,
    by
      calc
        sidedVolumeReal data u ≤ sidedVolumeReal data 1 :=
          monotone_sidedVolumeReal data u.2.2
        _ = f.rightEndpoint := sidedVolumeReal_right data⟩

theorem continuous_sidedDomainMap {f : PriceCurve}
    (data : SidedKnotData f) : Continuous (sidedDomainMap data) := by
  exact Continuous.subtype_mk
    ((continuous_sidedVolumeReal data).comp continuous_subtype_val) _

theorem monotone_sidedDomainMap {f : PriceCurve}
    (data : SidedKnotData f) : Monotone (sidedDomainMap data) := by
  intro u v huv
  exact monotone_sidedVolumeReal data huv

theorem surjective_sidedDomainMap {f : PriceCurve}
    (data : SidedKnotData f) : Function.Surjective (sidedDomainMap data) := by
  intro x
  have himage : (x : ℝ) ∈ sidedVolumeReal data '' Set.Icc (-1 : ℝ) 1 := by
    apply intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
      (continuous_sidedVolumeReal data).continuousOn
    simpa only [sidedVolumeReal_left, sidedVolumeReal_right] using x.2
  obtain ⟨u, hu, hux⟩ := himage
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  exact hux

/-- Equal-block sided knot data produces an admissible parametrisation in the
precise sense used by the corrected manuscript. -/
def sidedAdmissibleParametrisation {f : PriceCurve}
    (data : SidedKnotData f) : AdmissibleParametrisation f where
  toFun := sidedDomainMap data
  continuous := continuous_sidedDomainMap data
  monotone := monotone_sidedDomainMap data
  surjective := surjective_sidedDomainMap data
  map_zero := by
    apply Subtype.ext
    exact sidedVolumeReal_zero data

/-! ## The actual sided operator -/

/-- A price curve together with its minimal sided block endpoints.  Once this
finite data is fixed, the equal-block interpolation above is canonical. -/
structure CanonicalSidedCurve where
  curve : PriceCurve
  knots : SidedKnotData curve

/--
Thesis source: Definition `defn:parametrisation-operator` in
`2 - day-ahead/2_clearing_operator_price_curves.tex`.

Original label: `defn:parametrisation-operator`.

The Lean domain carries the finite minimal-sided-decomposition certificate
explicitly; the underlying curve is `c.curve`.
-/
def sidedParametrisationOperator (c : CanonicalSidedCurve) :
    ActualRepresentative :=
  parametrisedGraph c.curve (sidedAdmissibleParametrisation c.knots)

/-! ## Concrete non-convexity witness -/

def twoBlockPrice (x : Set.Icc (0 : ℝ) 2) : ℝ :=
  if (x : ℝ) ≤ 1 then 0 else 2

def twoBlockCurve : PriceCurve where
  leftEndpoint := 0
  rightEndpoint := 2
  leftEndpoint_nonpos := le_rfl
  rightEndpoint_nonneg := by norm_num
  price := twoBlockPrice
  price_monotone := by
    intro x y hxy
    have hxyReal : (x : ℝ) ≤ (y : ℝ) := hxy
    by_cases hx : (x : ℝ) ≤ 1
    · by_cases hy : (y : ℝ) ≤ 1 <;>
        simp [twoBlockPrice, hx, hy]
    · have hy : ¬(y : ℝ) ≤ 1 := fun hy => hx (hxyReal.trans hy)
      simp [twoBlockPrice, hx, hy]
  price_finite := by
    refine ((Set.finite_singleton (2 : ℝ)).insert 0).subset ?_
    rintro z ⟨x, rfl⟩
    by_cases hx : (x : ℝ) ≤ 1 <;> simp [twoBlockPrice, hx]

def zeroLeftKnot (_i : Fin 1) : ℝ := 0
def twoRightKnot (i : Fin 3) : ℝ := i
def twoRightLevel (i : Fin 2) : ℝ := 2 * i

def twoBlockKnotData : SidedKnotData twoBlockCurve where
  leftCount := 0
  rightCount := 2
  leftKnot := zeroLeftKnot
  rightKnot := twoRightKnot
  leftKnot_monotone := by
    intro i j hij
    fin_cases i
    fin_cases j
    exact le_rfl
  rightKnot_monotone := by
    intro i j hij
    change (i : ℝ) ≤ (j : ℝ)
    exact_mod_cast hij
  left_first := by rfl
  left_last := by rfl
  right_first := by norm_num [twoRightKnot]
  right_last := by norm_num [twoRightKnot, twoBlockCurve]
  leftLevel := Fin.elim0
  rightLevel := twoRightLevel
  left_block_interior := by
    intro j
    exact Fin.elim0 j
  right_block_interior := by
    intro j x hleft hright
    fin_cases j
    · norm_num [twoRightKnot] at hleft hright
      dsimp only [twoBlockCurve, twoRightLevel]
      simp [twoBlockPrice]
      linarith
    · norm_num [twoRightKnot] at hleft hright
      dsimp only [twoBlockCurve, twoRightLevel]
      simp [twoBlockPrice]
      linarith
  leftLevel_strictMono := by
    intro i
    exact Fin.elim0 i
  rightLevel_strictMono := by
    intro i j hij
    dsimp only [twoRightLevel]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) (by norm_num)

def canonicalTwoBlockCurve : CanonicalSidedCurve :=
  ⟨twoBlockCurve, twoBlockKnotData⟩

theorem uniformInterpolation_twoRightKnot
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    uniformInterpolation twoRightKnot u = 2 * u := by
  by_cases hu : u ≤ 1 / 2
  · have hfirst : clampUnit (2 * u) = 2 * u :=
      clampUnit_eq_self (by linarith) (by linarith)
    have hsecond : clampUnit (2 * u - 1) = 0 :=
      clampUnit_of_nonpos (by linarith)
    simp [uniformInterpolation, twoRightKnot, Fin.sum_univ_succ,
      hfirst, hsecond]
  · have hfirst : clampUnit (2 * u) = 1 :=
      clampUnit_of_one_le (by linarith)
    have hsecond : clampUnit (2 * u - 1) = 2 * u - 1 :=
      clampUnit_eq_self (by linarith) (by linarith)
    simp [uniformInterpolation, twoRightKnot, Fin.sum_univ_succ,
      hfirst, hsecond]

theorem canonicalTwoBlock_volume (u : Parameter) (hu : 0 ≤ (u : ℝ)) :
    (sidedParametrisationOperator canonicalTwoBlockCurve u).1 = 2 * (u : ℝ) := by
  change sidedVolumeReal twoBlockKnotData u = 2 * (u : ℝ)
  by_cases hu0 : (u : ℝ) ≤ 0
  · have huz : (u : ℝ) = 0 := le_antisymm hu0 hu
    rw [huz, sidedVolumeReal_zero]
    ring
  · rw [sidedVolumeReal, if_neg hu0]
    exact uniformInterpolation_twoRightKnot hu u.2.2

def threeBlockPrice (x : Set.Icc (0 : ℝ) 3) : ℝ :=
  if (x : ℝ) ≤ 1 then 0 else if (x : ℝ) ≤ 2 then 1 else 3

def threeBlockCurve : PriceCurve where
  leftEndpoint := 0
  rightEndpoint := 3
  leftEndpoint_nonpos := le_rfl
  rightEndpoint_nonneg := by norm_num
  price := threeBlockPrice
  price_monotone := by
    intro x y hxy
    have hxyReal : (x : ℝ) ≤ (y : ℝ) := hxy
    by_cases hx1 : (x : ℝ) ≤ 1
    · by_cases hy1 : (y : ℝ) ≤ 1
      · simp [threeBlockPrice, hx1, hy1]
      · by_cases hy2 : (y : ℝ) ≤ 2 <;>
          simp [threeBlockPrice, hx1, hy1, hy2]
    · have hy1 : ¬(y : ℝ) ≤ 1 := fun hy => hx1 (hxyReal.trans hy)
      by_cases hx2 : (x : ℝ) ≤ 2
      · by_cases hy2 : (y : ℝ) ≤ 2 <;>
          simp [threeBlockPrice, hx1, hx2, hy1, hy2]
      · have hy2 : ¬(y : ℝ) ≤ 2 := fun hy => hx2 (hxyReal.trans hy)
        simp [threeBlockPrice, hx1, hx2, hy1, hy2]
  price_finite := by
    refine (((Set.finite_singleton (3 : ℝ)).insert 1).insert 0).subset ?_
    rintro z ⟨x, rfl⟩
    by_cases hx1 : (x : ℝ) ≤ 1
    · simp [threeBlockPrice, hx1]
    · by_cases hx2 : (x : ℝ) ≤ 2 <;> simp [threeBlockPrice, hx1, hx2]

def threeRightKnot (i : Fin 4) : ℝ := i
def threeRightLevel : Fin 3 → ℝ := ![0, 1, 3]

def threeBlockKnotData : SidedKnotData threeBlockCurve where
  leftCount := 0
  rightCount := 3
  leftKnot := zeroLeftKnot
  rightKnot := threeRightKnot
  leftKnot_monotone := by
    intro i j hij
    fin_cases i
    fin_cases j
    exact le_rfl
  rightKnot_monotone := by
    intro i j hij
    change (i : ℝ) ≤ (j : ℝ)
    exact_mod_cast hij
  left_first := by rfl
  left_last := by rfl
  right_first := by norm_num [threeRightKnot]
  right_last := by norm_num [threeRightKnot, threeBlockCurve]
  leftLevel := Fin.elim0
  rightLevel := threeRightLevel
  left_block_interior := by
    intro j
    exact Fin.elim0 j
  right_block_interior := by
    intro j x hleft hright
    fin_cases j
    · norm_num [threeRightKnot] at hleft hright
      dsimp only [threeBlockCurve, threeRightLevel]
      simp [threeBlockPrice, le_of_lt hright]
    · norm_num [threeRightKnot] at hleft hright
      dsimp only [threeBlockCurve, threeRightLevel]
      simp [threeBlockPrice, not_le.mpr hleft, le_of_lt hright]
    · norm_num [threeRightKnot] at hleft hright
      dsimp only [threeBlockCurve, threeRightLevel]
      have hx1 : ¬(x : ℝ) ≤ 1 := not_le.mpr (hleft.trans' (by norm_num))
      simp [threeBlockPrice, hx1, not_le.mpr hleft]
  leftLevel_strictMono := by
    intro i
    exact Fin.elim0 i
  rightLevel_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [threeRightLevel]

def canonicalThreeBlockCurve : CanonicalSidedCurve :=
  ⟨threeBlockCurve, threeBlockKnotData⟩

theorem uniformInterpolation_threeRightKnot
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    uniformInterpolation threeRightKnot u = 3 * u := by
  by_cases hu1third : u ≤ 1 / 3
  · have h0 : clampUnit (3 * u) = 3 * u :=
      clampUnit_eq_self (by linarith) (by linarith)
    have h1 : clampUnit (3 * u - 1) = 0 :=
      clampUnit_of_nonpos (by linarith)
    have h2 : clampUnit (3 * u - 2) = 0 :=
      clampUnit_of_nonpos (by linarith)
    have h2' : clampUnit (3 * u - (1 + 1)) = 0 := by
      norm_num
      exact h2
    simp [uniformInterpolation, threeRightKnot, Fin.sum_univ_succ, h0, h1, h2']
  · by_cases hu2third : u ≤ 2 / 3
    · have h0 : clampUnit (3 * u) = 1 :=
        clampUnit_of_one_le (by linarith)
      have h1 : clampUnit (3 * u - 1) = 3 * u - 1 :=
        clampUnit_eq_self (by linarith) (by linarith)
      have h2 : clampUnit (3 * u - 2) = 0 :=
        clampUnit_of_nonpos (by linarith)
      have h2' : clampUnit (3 * u - (1 + 1)) = 0 := by
        norm_num
        exact h2
      simp [uniformInterpolation, threeRightKnot, Fin.sum_univ_succ, h0, h1, h2']
    · have h0 : clampUnit (3 * u) = 1 :=
        clampUnit_of_one_le (by linarith)
      have h1 : clampUnit (3 * u - 1) = 1 :=
        clampUnit_of_one_le (by linarith)
      have h2 : clampUnit (3 * u - 2) = 3 * u - 2 :=
        clampUnit_eq_self (by linarith) (by linarith)
      have h2' : clampUnit (3 * u - (1 + 1)) = 3 * u - 2 := by
        norm_num
        exact h2
      simp [uniformInterpolation, threeRightKnot, Fin.sum_univ_succ, h0, h1, h2']
      ring

theorem canonicalThreeBlock_volume (u : Parameter) (hu : 0 ≤ (u : ℝ)) :
    (sidedParametrisationOperator canonicalThreeBlockCurve u).1 = 3 * (u : ℝ) := by
  change sidedVolumeReal threeBlockKnotData u = 3 * (u : ℝ)
  by_cases hu0 : (u : ℝ) ≤ 0
  · have huz : (u : ℝ) = 0 := le_antisymm hu0 hu
    rw [huz, sidedVolumeReal_zero]
    ring
  · rw [sidedVolumeReal, if_neg hu0]
    exact uniformInterpolation_threeRightKnot hu u.2.2

/-! ## Positive-side ranges of the concrete witnesses -/

/-- The positive half of the common parameter interval. -/
abbrev PositiveParameter := Set.Icc (0 : ℝ) 1

/-- Regard a positive parameter as an element of the full parameter interval. -/
def positiveParameter (u : PositiveParameter) : Parameter :=
  ⟨u, by
    constructor
    · linarith [u.2.1]
    · exact u.2.2⟩

theorem canonicalTwoBlock_price (u : PositiveParameter) :
    (sidedParametrisationOperator canonicalTwoBlockCurve (positiveParameter u)).2 =
      if (u : ℝ) ≤ 1 / 2 then 0 else 2 := by
  have hvolume := canonicalTwoBlock_volume (positiveParameter u) u.2.1
  change twoBlockPrice (sidedDomainMap twoBlockKnotData (positiveParameter u)) = _
  have hiff : 2 * (u : ℝ) ≤ 1 ↔ (u : ℝ) ≤ 1 / 2 := by
    constructor <;> intro h <;> linarith
  simp only [twoBlockPrice]
  rw [show ((sidedDomainMap twoBlockKnotData (positiveParameter u) :
    Set.Icc twoBlockCurve.leftEndpoint twoBlockCurve.rightEndpoint) : ℝ) =
      2 * (u : ℝ) by exact hvolume]
  simp only [hiff]

theorem canonicalThreeBlock_price (u : PositiveParameter) :
    (sidedParametrisationOperator canonicalThreeBlockCurve (positiveParameter u)).2 =
      if (u : ℝ) ≤ 1 / 3 then 0 else if (u : ℝ) ≤ 2 / 3 then 1 else 3 := by
  have hvolume := canonicalThreeBlock_volume (positiveParameter u) u.2.1
  change threeBlockPrice (sidedDomainMap threeBlockKnotData (positiveParameter u)) = _
  have hiff1 : 3 * (u : ℝ) ≤ 1 ↔ (u : ℝ) ≤ 1 / 3 := by
    constructor <;> intro h <;> linarith
  have hiff2 : 3 * (u : ℝ) ≤ 2 ↔ (u : ℝ) ≤ 2 / 3 := by
    constructor <;> intro h <;> linarith
  simp only [threeBlockPrice]
  rw [show ((sidedDomainMap threeBlockKnotData (positiveParameter u) :
    Set.Icc threeBlockCurve.leftEndpoint threeBlockCurve.rightEndpoint) : ℝ) =
      3 * (u : ℝ) by exact hvolume]
  simp only [hiff1, hiff2]

/-- Pointwise midpoint of the two explicit canonical sided representatives. -/
noncomputable def twoThreeAverage : ActualRepresentative :=
  representativeCombination (1 / 2) (1 / 2)
    (sidedParametrisationOperator canonicalTwoBlockCurve)
    (sidedParametrisationOperator canonicalThreeBlockCurve)

theorem twoThreeAverage_price (u : PositiveParameter) :
    (twoThreeAverage (positiveParameter u)).2 =
      if (u : ℝ) ≤ 1 / 3 then 0
      else if (u : ℝ) ≤ 1 / 2 then 1 / 2
      else if (u : ℝ) ≤ 2 / 3 then 3 / 2
      else 5 / 2 := by
  rw [show (twoThreeAverage (positiveParameter u)).2 =
      (1 / 2 : ℝ) *
          (sidedParametrisationOperator canonicalTwoBlockCurve
            (positiveParameter u)).2 +
        (1 / 2 : ℝ) *
          (sidedParametrisationOperator canonicalThreeBlockCurve
            (positiveParameter u)).2 by
        rfl]
  rw [canonicalTwoBlock_price, canonicalThreeBlock_price]
  split_ifs <;> norm_num at * <;> linarith

/-- The four prices taken by the midpoint on the positive parameter side. -/
def fourPriceLevels : Set ℝ := {0, 1 / 2, 3 / 2, 5 / 2}

theorem range_twoThreeAverage_price :
    Set.range (fun u : PositiveParameter =>
      (twoThreeAverage (positiveParameter u)).2) = fourPriceLevels := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    change (twoThreeAverage (positiveParameter u)).2 ∈ fourPriceLevels
    rw [twoThreeAverage_price]
    split_ifs <;> simp [fourPriceLevels]
  · intro hy
    simp only [fourPriceLevels, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h
    · subst y
      refine ⟨⟨1 / 6, by constructor <;> norm_num⟩, ?_⟩
      change (twoThreeAverage
        (positiveParameter (⟨1 / 6, by constructor <;> norm_num⟩ : PositiveParameter))).2 = 0
      rw [twoThreeAverage_price]
      norm_num
    · subst y
      refine ⟨⟨5 / 12, by constructor <;> norm_num⟩, ?_⟩
      change (twoThreeAverage
        (positiveParameter (⟨5 / 12, by constructor <;> norm_num⟩ : PositiveParameter))).2 =
          1 / 2
      rw [twoThreeAverage_price]
      norm_num
    · subst y
      refine ⟨⟨7 / 12, by constructor <;> norm_num⟩, ?_⟩
      change (twoThreeAverage
        (positiveParameter (⟨7 / 12, by constructor <;> norm_num⟩ : PositiveParameter))).2 =
          3 / 2
      rw [twoThreeAverage_price]
      norm_num
    · subst y
      refine ⟨⟨5 / 6, by constructor <;> norm_num⟩, ?_⟩
      change (twoThreeAverage
        (positiveParameter (⟨5 / 6, by constructor <;> norm_num⟩ : PositiveParameter))).2 =
          5 / 2
      rw [twoThreeAverage_price]
      norm_num

/-! ## Minimal canonical sided certificates -/

/-- The price values attained on the positive parameter half by a raw sided
certificate. -/
def rightPriceRange (c : CanonicalSidedCurve) : Set ℝ :=
  Set.range (fun u : PositiveParameter =>
    (sidedParametrisationOperator c (positiveParameter u)).2)

/-- A raw sided certificate is genuinely canonical on the positive side when
its blocks have positive width and its listed levels are exactly the values
attained there.  These conditions exclude redundant zero-width blocks. -/
structure MinimalCanonicalSidedCurve where
  raw : CanonicalSidedCurve
  rightCount_pos : 0 < raw.knots.rightCount
  rightKnot_strictMono : StrictMono raw.knots.rightKnot
  right_price_range : rightPriceRange raw = Set.range raw.knots.rightLevel
  right_parameter_block : ∀ (j : Fin raw.knots.rightCount)
      (u : PositiveParameter),
    (j : ℝ) / (raw.knots.rightCount : ℝ) < (u : ℝ) →
    (u : ℝ) < ((j : ℝ) + 1) / (raw.knots.rightCount : ℝ) →
      (sidedParametrisationOperator raw (positiveParameter u)).2 =
        raw.knots.rightLevel j

/-- The sided operator restricted to genuinely minimal canonical data. -/
def minimalSidedParametrisationOperator (c : MinimalCanonicalSidedCurve) :
    ActualRepresentative :=
  sidedParametrisationOperator c.raw

theorem range_canonicalTwoBlock_price :
    rightPriceRange canonicalTwoBlockCurve = Set.range twoRightLevel := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    change ∃ j, twoRightLevel j = (sidedParametrisationOperator
      canonicalTwoBlockCurve (positiveParameter u)).2
    rw [canonicalTwoBlock_price]
    split_ifs
    · refine ⟨⟨0, by decide⟩, ?_⟩
      norm_num [twoRightLevel]
    · refine ⟨⟨1, by decide⟩, ?_⟩
      norm_num [twoRightLevel]
  · rintro ⟨j, rfl⟩
    fin_cases j
    · refine ⟨⟨1 / 4, by constructor <;> norm_num⟩, ?_⟩
      change (sidedParametrisationOperator canonicalTwoBlockCurve
        (positiveParameter (⟨1 / 4, by constructor <;> norm_num⟩ :
          PositiveParameter))).2 = twoRightLevel 0
      rw [canonicalTwoBlock_price]
      norm_num [twoRightLevel]
    · refine ⟨⟨3 / 4, by constructor <;> norm_num⟩, ?_⟩
      change (sidedParametrisationOperator canonicalTwoBlockCurve
        (positiveParameter (⟨3 / 4, by constructor <;> norm_num⟩ :
          PositiveParameter))).2 = twoRightLevel 1
      rw [canonicalTwoBlock_price]
      norm_num [twoRightLevel]

theorem range_canonicalThreeBlock_price :
    rightPriceRange canonicalThreeBlockCurve = Set.range threeRightLevel := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    change ∃ j, threeRightLevel j = (sidedParametrisationOperator
      canonicalThreeBlockCurve (positiveParameter u)).2
    rw [canonicalThreeBlock_price]
    split_ifs
    · refine ⟨⟨0, by decide⟩, ?_⟩
      rfl
    · refine ⟨⟨1, by decide⟩, ?_⟩
      rfl
    · refine ⟨⟨2, by decide⟩, ?_⟩
      rfl
  · rintro ⟨j, rfl⟩
    fin_cases j
    · refine ⟨⟨1 / 6, by constructor <;> norm_num⟩, ?_⟩
      change (sidedParametrisationOperator canonicalThreeBlockCurve
        (positiveParameter (⟨1 / 6, by constructor <;> norm_num⟩ :
          PositiveParameter))).2 = 0
      rw [canonicalThreeBlock_price]
      norm_num
    · refine ⟨⟨1 / 2, by constructor <;> norm_num⟩, ?_⟩
      change (sidedParametrisationOperator canonicalThreeBlockCurve
        (positiveParameter (⟨1 / 2, by constructor <;> norm_num⟩ :
          PositiveParameter))).2 = 1
      rw [canonicalThreeBlock_price]
      norm_num
    · refine ⟨⟨5 / 6, by constructor <;> norm_num⟩, ?_⟩
      change (sidedParametrisationOperator canonicalThreeBlockCurve
        (positiveParameter (⟨5 / 6, by constructor <;> norm_num⟩ :
          PositiveParameter))).2 = 3
      rw [canonicalThreeBlock_price]
      norm_num

def minimalTwoBlockCurve : MinimalCanonicalSidedCurve where
  raw := canonicalTwoBlockCurve
  rightCount_pos := by change 0 < 2; norm_num
  rightKnot_strictMono := by
    intro i j hij
    change (i : ℝ) < (j : ℝ)
    exact_mod_cast hij
  right_price_range := range_canonicalTwoBlock_price
  right_parameter_block := by
    intro j u hleft hright
    change (j : ℝ) / 2 < (u : ℝ) at hleft
    change (u : ℝ) < ((j : ℝ) + 1) / 2 at hright
    fin_cases j
    · rw [canonicalTwoBlock_price]
      norm_num at hleft hright
      dsimp only [canonicalTwoBlockCurve, twoBlockKnotData, twoRightLevel]
      norm_num at ⊢
      linarith
    · rw [canonicalTwoBlock_price]
      norm_num at hleft hright
      dsimp only [canonicalTwoBlockCurve, twoBlockKnotData, twoRightLevel]
      norm_num at ⊢
      linarith

def minimalThreeBlockCurve : MinimalCanonicalSidedCurve where
  raw := canonicalThreeBlockCurve
  rightCount_pos := by change 0 < 3; norm_num
  rightKnot_strictMono := by
    intro i j hij
    change (i : ℝ) < (j : ℝ)
    exact_mod_cast hij
  right_price_range := range_canonicalThreeBlock_price
  right_parameter_block := by
    intro j u hleft hright
    change (j : ℝ) / 3 < (u : ℝ) at hleft
    change (u : ℝ) < ((j : ℝ) + 1) / 3 at hright
    fin_cases j
    · change (sidedParametrisationOperator canonicalThreeBlockCurve
        (positiveParameter u)).2 = 0
      rw [canonicalThreeBlock_price]
      norm_num at hleft hright
      split_ifs <;> norm_num at * <;> linarith
    · change (sidedParametrisationOperator canonicalThreeBlockCurve
        (positiveParameter u)).2 = 1
      rw [canonicalThreeBlock_price]
      norm_num at hleft hright
      split_ifs <;> norm_num at * <;> linarith
    · change (sidedParametrisationOperator canonicalThreeBlockCurve
        (positiveParameter u)).2 = 3
      rw [canonicalThreeBlock_price]
      norm_num at hleft hright
      split_ifs <;> norm_num at * <;> linarith

theorem ncard_fourPriceLevels : fourPriceLevels.ncard = 4 := by
  rw [fourPriceLevels]
  norm_num [Set.ncard_insert_of_notMem]

theorem rightPriceRange_ncard (c : MinimalCanonicalSidedCurve) :
    (rightPriceRange c.raw).ncard = c.raw.knots.rightCount := by
  rw [c.right_price_range,
    Set.ncard_range_of_injective c.raw.knots.rightLevel_strictMono.injective]
  simp

/-- A point halfway through the first of four equal parameter blocks maps
strictly inside the first volume block. -/
theorem uniformInterpolation_four_firstInterior
    (knot : Fin 5 → ℝ) (hknot : StrictMono knot) :
    knot 0 < uniformInterpolation knot (1 / 8) ∧
      uniformInterpolation knot (1 / 8) < knot 1 := by
  have h01 : knot 0 < knot 1 := hknot (by decide)
  norm_num [uniformInterpolation, Fin.sum_univ_succ, clampUnit]
  constructor <;> linarith

/-- The parameter `7/24` lies strictly inside the second of four equal
parameter blocks. -/
theorem uniformInterpolation_four_secondInterior
    (knot : Fin 5 → ℝ) (hknot : StrictMono knot) :
    knot 1 < uniformInterpolation knot (7 / 24) ∧
      uniformInterpolation knot (7 / 24) < knot 2 := by
  have h12 : knot 1 < knot 2 := hknot (by decide)
  norm_num [uniformInterpolation, Fin.sum_univ_succ, clampUnit]
  constructor <;> linarith

theorem uniformInterpolation_firstInterior_of_count_eq_four
    {n : ℕ} (hn : n = 4) (knot : Fin (n + 1) → ℝ)
    (hknot : StrictMono knot) :
    knot 0 < uniformInterpolation knot (1 / 8) ∧
      uniformInterpolation knot (1 / 8) < knot ⟨1, by omega⟩ := by
  subst n
  simpa using uniformInterpolation_four_firstInterior knot hknot

theorem uniformInterpolation_secondInterior_of_count_eq_four
    {n : ℕ} (hn : n = 4) (knot : Fin (n + 1) → ℝ)
    (hknot : StrictMono knot) :
    knot ⟨1, by omega⟩ < uniformInterpolation knot (7 / 24) ∧
      uniformInterpolation knot (7 / 24) < knot ⟨2, by omega⟩ := by
  subst n
  simpa using uniformInterpolation_four_secondInterior knot hknot

theorem rightCount_eq_four_of_eq_average
    (c : MinimalCanonicalSidedCurve)
    (heq : minimalSidedParametrisationOperator c = twoThreeAverage) :
    c.raw.knots.rightCount = 4 := by
  have hfun :
      (fun u : PositiveParameter =>
          (sidedParametrisationOperator c.raw (positiveParameter u)).2) =
        fun u : PositiveParameter => (twoThreeAverage (positiveParameter u)).2 := by
    funext u
    exact congrArg Prod.snd (congrFun heq (positiveParameter u))
  have hrange : rightPriceRange c.raw = fourPriceLevels := by
    unfold rightPriceRange
    rw [hfun, range_twoThreeAverage_price]
  calc
    c.raw.knots.rightCount = (rightPriceRange c.raw).ncard :=
      (rightPriceRange_ncard c).symm
    _ = fourPriceLevels.ncard := congrArg Set.ncard hrange
    _ = 4 := ncard_fourPriceLevels

/-- The explicit midpoint is not the equal-block canonical encoding of any
minimal sided curve. -/
theorem twoThreeAverage_not_in_minimal_range :
    ¬ ∃ c : MinimalCanonicalSidedCurve,
      minimalSidedParametrisationOperator c = twoThreeAverage := by
  rintro ⟨c, heq⟩
  have hcount : c.raw.knots.rightCount = 4 :=
    rightCount_eq_four_of_eq_average c heq
  let u₀ : PositiveParameter := ⟨1 / 8, by constructor <;> norm_num⟩
  let u₁ : PositiveParameter := ⟨7 / 24, by constructor <;> norm_num⟩
  let j₀ : Fin c.raw.knots.rightCount := ⟨0, by omega⟩
  let j₁ : Fin c.raw.knots.rightCount := ⟨1, by omega⟩
  let x₀ := sidedDomainMap c.raw.knots (positiveParameter u₀)
  let x₁ := sidedDomainMap c.raw.knots (positiveParameter u₁)
  have hinterior₀ := uniformInterpolation_firstInterior_of_count_eq_four
    hcount c.raw.knots.rightKnot c.rightKnot_strictMono
  have hinterior₁ := uniformInterpolation_secondInterior_of_count_eq_four
    hcount c.raw.knots.rightKnot c.rightKnot_strictMono
  have hx₀left : c.raw.knots.rightKnot j₀.castSucc < (x₀ : ℝ) := by
    change c.raw.knots.rightKnot j₀.castSucc <
      sidedVolumeReal c.raw.knots (1 / 8)
    rw [sidedVolumeReal, if_neg (by norm_num)]
    simpa [j₀] using hinterior₀.1
  have hx₀right : (x₀ : ℝ) < c.raw.knots.rightKnot j₀.succ := by
    change sidedVolumeReal c.raw.knots (1 / 8) <
      c.raw.knots.rightKnot j₀.succ
    rw [sidedVolumeReal, if_neg (by norm_num)]
    simpa [j₀] using hinterior₀.2
  have hx₁left : c.raw.knots.rightKnot j₁.castSucc < (x₁ : ℝ) := by
    change c.raw.knots.rightKnot j₁.castSucc <
      sidedVolumeReal c.raw.knots (7 / 24)
    rw [sidedVolumeReal, if_neg (by norm_num)]
    simpa [j₁] using hinterior₁.1
  have hx₁right : (x₁ : ℝ) < c.raw.knots.rightKnot j₁.succ := by
    change sidedVolumeReal c.raw.knots (7 / 24) <
      c.raw.knots.rightKnot j₁.succ
    rw [sidedVolumeReal, if_neg (by norm_num)]
    simpa [j₁] using hinterior₁.2
  have hx₀price : c.raw.curve.price x₀ = c.raw.knots.rightLevel j₀ :=
    c.raw.knots.right_block_interior j₀ x₀ hx₀left hx₀right
  have hx₁price : c.raw.curve.price x₁ = c.raw.knots.rightLevel j₁ :=
    c.raw.knots.right_block_interior j₁ x₁ hx₁left hx₁right
  have heq₀ : c.raw.curve.price x₀ =
      (twoThreeAverage (positiveParameter u₀)).2 := by
    simpa [minimalSidedParametrisationOperator, sidedParametrisationOperator,
      parametrisedGraph, sidedAdmissibleParametrisation, x₀] using
      congrArg Prod.snd (congrFun heq (positiveParameter u₀))
  have heq₁ : c.raw.curve.price x₁ =
      (twoThreeAverage (positiveParameter u₁)).2 := by
    simpa [minimalSidedParametrisationOperator, sidedParametrisationOperator,
      parametrisedGraph, sidedAdmissibleParametrisation, x₁] using
      congrArg Prod.snd (congrFun heq (positiveParameter u₁))
  have havg₀ : (twoThreeAverage (positiveParameter u₀)).2 = 0 := by
    rw [twoThreeAverage_price]
    norm_num [u₀]
  have havg₁ : (twoThreeAverage (positiveParameter u₁)).2 = 0 := by
    rw [twoThreeAverage_price]
    norm_num [u₁]
  have hlevel₀ : c.raw.knots.rightLevel j₀ = 0 := by
    calc
      c.raw.knots.rightLevel j₀ = c.raw.curve.price x₀ := hx₀price.symm
      _ = (twoThreeAverage (positiveParameter u₀)).2 := heq₀
      _ = 0 := havg₀
  have hlevel₁ : c.raw.knots.rightLevel j₁ = 0 := by
    calc
      c.raw.knots.rightLevel j₁ = c.raw.curve.price x₁ := hx₁price.symm
      _ = (twoThreeAverage (positiveParameter u₁)).2 := heq₁
      _ = 0 := havg₁
  have hstrict : c.raw.knots.rightLevel j₀ < c.raw.knots.rightLevel j₁ :=
    c.raw.knots.rightLevel_strictMono (by simp [j₀, j₁])
  rw [hlevel₀, hlevel₁] at hstrict
  exact (lt_irrefl 0 hstrict)

/--
Alternative route for `cor:sided-parametrisation-not-weakly-convex` (not the
mapped proof): representative clause of the corollary in
`2 - day-ahead/2_clearing_operator_price_curves.tex`, proved here by an exhaustive
case split over the possible block counts.  The mapped proof, which follows the
thesis's explicit two-block/three-block example with the continuity and
graph-recovery argument (quarter knot `5/6` versus `5/8`), is
`SidedSourceExclusion.canonical_not_weaklyConvex_source` /
`canonical_not_weaklyConvexAE_source` in `CanonicalSidedSourceExclusion.lean`.

This is the raw-knot helper for the current nonconvexity result.
The actual essential-curve and Hilbert-image statements are proved in
`CanonicalSidedExample.lean`; no historical replacement source is used.

The raw knot carrier is restricted to `MinimalCanonicalSidedCurve`; its
positive-width and exact-range fields formalise the manuscript's *minimal*
sided decomposition and rule out redundant zero-width blocks.  The explicit
two-block/three-block midpoint has four distinct price levels, but its first level
persists past the first of four equal parameter blocks. -/
theorem sidedParametrisation_not_weaklyConvex :
    ¬ IsWeaklyConvex minimalSidedParametrisationOperator := by
  intro hweak
  obtain ⟨c, hc⟩ := hweak minimalTwoBlockCurve minimalThreeBlockCurve
    (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  apply twoThreeAverage_not_in_minimal_range
  refine ⟨c, ?_⟩
  simpa [twoThreeAverage, minimalSidedParametrisationOperator,
    minimalTwoBlockCurve, minimalThreeBlockCurve] using hc

/-- Clamp a real argument to the common parameter interval.  On `[-1,1]`
this is the identity, while the total definition makes the restricted
Lebesgue-measure statement below convenient to state. -/
def clampParameter (x : ℝ) : Parameter :=
  ⟨max (-1) (min 1 x), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩

@[simp]
theorem clampParameter_positiveParameter (u : PositiveParameter) :
    clampParameter (u : ℝ) = positiveParameter u := by
  apply Subtype.ext
  have hminus : (-1 : ℝ) ≤ (u : ℝ) := le_trans (by norm_num) u.2.1
  simp [clampParameter, positiveParameter, hminus, u.2.2]

theorem twoThreeAverage_clamp_price_eq_zero {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxthird : x ≤ 1 / 3) :
    (twoThreeAverage (clampParameter x)).2 = 0 := by
  let u : PositiveParameter := ⟨x, hx0, hx1⟩
  rw [show clampParameter x = positiveParameter u by
    simpa [u] using clampParameter_positiveParameter u]
  rw [twoThreeAverage_price, if_pos (by simpa [u] using hxthird)]

theorem twoThreeAverage_clamp_price_eq_half {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hthird : 1 / 3 < x) (hxhalf : x ≤ 1 / 2) :
    (twoThreeAverage (clampParameter x)).2 = 1 / 2 := by
  let u : PositiveParameter := ⟨x, hx0, hx1⟩
  rw [show clampParameter x = positiveParameter u by
    simpa [u] using clampParameter_positiveParameter u]
  rw [twoThreeAverage_price,
    if_neg (by simpa [u] using (not_le.mpr hthird)),
    if_pos (by simpa [u] using hxhalf)]

theorem twoThreeAverage_clamp_price_eq_threeHalves {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hhalf : 1 / 2 < x) (hxtwothirds : x ≤ 2 / 3) :
    (twoThreeAverage (clampParameter x)).2 = 3 / 2 := by
  have hthird : 1 / 3 < x := lt_trans (by norm_num) hhalf
  let u : PositiveParameter := ⟨x, hx0, hx1⟩
  rw [show clampParameter x = positiveParameter u by
    simpa [u] using clampParameter_positiveParameter u]
  rw [twoThreeAverage_price,
    if_neg (by simpa [u] using (not_le.mpr hthird)),
    if_neg (by simpa [u] using (not_le.mpr hhalf)),
    if_pos (by simpa [u] using hxtwothirds)]

theorem twoThreeAverage_clamp_price_eq_fiveHalves {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (htwothirds : 2 / 3 < x) :
    (twoThreeAverage (clampParameter x)).2 = 5 / 2 := by
  have hhalf : 1 / 2 < x := lt_trans (by norm_num) htwothirds
  have hthird : 1 / 3 < x := lt_trans (by norm_num) hhalf
  let u : PositiveParameter := ⟨x, hx0, hx1⟩
  rw [show clampParameter x = positiveParameter u by
    simpa [u] using clampParameter_positiveParameter u]
  rw [twoThreeAverage_price,
    if_neg (by simpa [u] using (not_le.mpr hthird)),
    if_neg (by simpa [u] using (not_le.mpr hhalf)),
    if_neg (by simpa [u] using (not_le.mpr htwothirds))]

/-- Weak convexity after quotienting actual representatives by equality almost
everywhere on the common parameter interval. -/
def IsWeaklyConvexAE {Curve : Type*}
    (encode : Curve → ActualRepresentative) : Prop :=
  ∀ f g α β, 0 ≤ α → 0 ≤ β →
    ∃ h, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)),
      encode h (clampParameter x) =
        representativeCombination α β (encode f) (encode g) (clampParameter x)

/-- If two functions agree almost everywhere on the common parameter interval
and are respectively constant on a nonempty open subinterval, their constants
coincide. -/
theorem constants_eq_of_ae_eq_on_Ioo
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E} {a b : ℝ} {c d : E}
    (hae : f =ᵐ[MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)] g)
    (hsub : Set.Ioo a b ⊆ Set.Icc (-1 : ℝ) 1)
    (hf : ∀ x ∈ Set.Ioo a b, f x = c)
    (hg : ∀ x ∈ Set.Ioo a b, g x = d)
    (hab : a < b) : c = d := by
  have hae' : f =ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] g :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hae
  have hconstants :
      (fun _ : ℝ => c) =ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)]
        fun _ : ℝ => d := by
    filter_upwards [hae', MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx hxab
    calc
      c = f x := (hf x hxab).symm
      _ = g x := hx
      _ = d := hg x hxab
  have heqOn := MeasureTheory.Measure.eqOn_open_of_ae_eq
    (μ := MeasureTheory.volume) hconstants isOpen_Ioo
    continuous_const.continuousOn continuous_const.continuousOn
  simpa using heqOn (show (a + b) / 2 ∈ Set.Ioo a b by
    constructor <;> linarith)

theorem minimalCanonical_price_on_rightParameterBlock
    (c : MinimalCanonicalSidedCurve) (j : Fin c.raw.knots.rightCount)
    {x : ℝ}
    (hleft : (j : ℝ) / (c.raw.knots.rightCount : ℝ) < x)
    (hright : x < ((j : ℝ) + 1) / (c.raw.knots.rightCount : ℝ))
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (minimalSidedParametrisationOperator c (clampParameter x)).2 =
      c.raw.knots.rightLevel j := by
  let u : PositiveParameter := ⟨x, hx0, hx1⟩
  change (sidedParametrisationOperator c.raw (clampParameter x)).2 = _
  rw [show clampParameter x = positiveParameter u by
    simpa [u] using clampParameter_positiveParameter u]
  exact c.right_parameter_block j u hleft hright

theorem rightLevel_mem_fourPriceLevels_of_ae_eq_average
    (c : MinimalCanonicalSidedCurve)
    (hae :
      (fun x : ℝ =>
          minimalSidedParametrisationOperator c (clampParameter x)) =ᵐ[
        MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)]
        fun x : ℝ => twoThreeAverage (clampParameter x))
    (j : Fin c.raw.knots.rightCount) :
    c.raw.knots.rightLevel j ∈ fourPriceLevels := by
  have haePrice :
      (fun x : ℝ =>
          (minimalSidedParametrisationOperator c (clampParameter x)).2) =ᵐ[
        MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)]
        fun x : ℝ => (twoThreeAverage (clampParameter x)).2 :=
    hae.mono fun _ hx => congrArg Prod.snd hx
  let n := c.raw.knots.rightCount
  let a : ℝ := (j : ℝ) / (n : ℝ)
  let b : ℝ := ((j : ℝ) + 1) / (n : ℝ)
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast c.rightCount_pos
  have ha0 : 0 ≤ a := by
    exact div_nonneg (by positivity) hnpos.le
  have hjlt : (j : ℝ) < (n : ℝ) := by
    exact_mod_cast j.isLt
  have hab : a < b := by
    change (j : ℝ) / (n : ℝ) < ((j : ℝ) + 1) / (n : ℝ)
    rw [div_lt_div_iff₀ hnpos hnpos]
    linarith
  have hb1 : b ≤ 1 := by
    change ((j : ℝ) + 1) / (n : ℝ) ≤ 1
    rw [div_le_iff₀ hnpos]
    have hjSucc : j.val + 1 ≤ n := Nat.succ_le_iff.mpr j.isLt
    have hjSuccReal : (j : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hjSucc
    simpa using hjSuccReal
  by_cases hthird : a < 1 / 3
  · have hnonempty : a < min b (1 / 3) := lt_min hab hthird
    have hsub : Set.Ioo a (min b (1 / 3)) ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro x hx
      have hxb : x < b := (lt_min_iff.mp hx.2).1
      have hx0 : 0 ≤ x := ha0.trans hx.1.le
      have hx1 : x ≤ 1 := hxb.le.trans hb1
      exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hx0, hx1⟩
    have hcanonical : ∀ x ∈ Set.Ioo a (min b (1 / 3)),
        (minimalSidedParametrisationOperator c (clampParameter x)).2 =
          c.raw.knots.rightLevel j := by
      intro x hx
      have hxb : x < b := (lt_min_iff.mp hx.2).1
      have hx0 : 0 ≤ x := ha0.trans hx.1.le
      have hx1 : x ≤ 1 := hxb.le.trans hb1
      apply minimalCanonical_price_on_rightParameterBlock c j
      · change a < x
        exact hx.1
      · change x < b
        exact hxb
      · exact hx0
      · exact hx1
    have havg : ∀ x ∈ Set.Ioo a (min b (1 / 3)),
        (twoThreeAverage (clampParameter x)).2 = 0 := by
      intro x hx
      have hxb : x < b := (lt_min_iff.mp hx.2).1
      have hx0 : 0 ≤ x := ha0.trans hx.1.le
      have hx1 : x ≤ 1 := hxb.le.trans hb1
      have hxthird : x ≤ 1 / 3 :=
        le_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _))
      let u : PositiveParameter := ⟨x, hx0, hx1⟩
      rw [show clampParameter x = positiveParameter u by
        simpa [u] using clampParameter_positiveParameter u]
      rw [twoThreeAverage_price, if_pos (by simpa [u] using hxthird)]
    have hlevel : c.raw.knots.rightLevel j = 0 :=
      constants_eq_of_ae_eq_on_Ioo haePrice hsub hcanonical havg hnonempty
    rw [hlevel]
    simp [fourPriceLevels]
  · by_cases hhalf : a < 1 / 2
    · have hnonempty : a < min b (1 / 2) := lt_min hab hhalf
      have hthird_le : 1 / 3 ≤ a := le_of_not_gt hthird
      have hsub : Set.Ioo a (min b (1 / 2)) ⊆ Set.Icc (-1 : ℝ) 1 := by
        intro x hx
        have hxb : x < b := (lt_min_iff.mp hx.2).1
        have hx0 : 0 ≤ x := ha0.trans hx.1.le
        have hx1 : x ≤ 1 := hxb.le.trans hb1
        exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hx0, hx1⟩
      have hcanonical : ∀ x ∈ Set.Ioo a (min b (1 / 2)),
          (minimalSidedParametrisationOperator c (clampParameter x)).2 =
            c.raw.knots.rightLevel j := by
        intro x hx
        have hxb : x < b := (lt_min_iff.mp hx.2).1
        have hx0 : 0 ≤ x := ha0.trans hx.1.le
        have hx1 : x ≤ 1 := hxb.le.trans hb1
        apply minimalCanonical_price_on_rightParameterBlock c j
        · change a < x
          exact hx.1
        · change x < b
          exact hxb
        · exact hx0
        · exact hx1
      have havg : ∀ x ∈ Set.Ioo a (min b (1 / 2)),
          (twoThreeAverage (clampParameter x)).2 = 1 / 2 := by
        intro x hx
        have hxb : x < b := (lt_min_iff.mp hx.2).1
        have hx0 : 0 ≤ x := ha0.trans hx.1.le
        have hx1 : x ≤ 1 := hxb.le.trans hb1
        have hxthird : ¬x ≤ 1 / 3 :=
          not_le.mpr (hthird_le.trans_lt hx.1)
        have hxhalf : x ≤ 1 / 2 :=
          le_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _))
        let u : PositiveParameter := ⟨x, hx0, hx1⟩
        rw [show clampParameter x = positiveParameter u by
          simpa [u] using clampParameter_positiveParameter u]
        rw [twoThreeAverage_price, if_neg (by simpa [u] using hxthird),
          if_pos (by simpa [u] using hxhalf)]
      have hlevel : c.raw.knots.rightLevel j = 1 / 2 :=
        constants_eq_of_ae_eq_on_Ioo haePrice hsub hcanonical havg hnonempty
      rw [hlevel]
      simp [fourPriceLevels]
    · by_cases htwothirds : a < 2 / 3
      · have hnonempty : a < min b (2 / 3) := lt_min hab htwothirds
        have hthird_le : 1 / 3 ≤ a := le_of_not_gt hthird
        have hhalf_le : 1 / 2 ≤ a := le_of_not_gt hhalf
        have hsub : Set.Ioo a (min b (2 / 3)) ⊆ Set.Icc (-1 : ℝ) 1 := by
          intro x hx
          have hxb : x < b := (lt_min_iff.mp hx.2).1
          have hx0 : 0 ≤ x := ha0.trans hx.1.le
          have hx1 : x ≤ 1 := hxb.le.trans hb1
          exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hx0, hx1⟩
        have hcanonical : ∀ x ∈ Set.Ioo a (min b (2 / 3)),
            (minimalSidedParametrisationOperator c (clampParameter x)).2 =
              c.raw.knots.rightLevel j := by
          intro x hx
          have hxb : x < b := (lt_min_iff.mp hx.2).1
          have hx0 : 0 ≤ x := ha0.trans hx.1.le
          have hx1 : x ≤ 1 := hxb.le.trans hb1
          apply minimalCanonical_price_on_rightParameterBlock c j
          · change a < x
            exact hx.1
          · change x < b
            exact hxb
          · exact hx0
          · exact hx1
        have havg : ∀ x ∈ Set.Ioo a (min b (2 / 3)),
            (twoThreeAverage (clampParameter x)).2 = 3 / 2 := by
          intro x hx
          have hxb : x < b := (lt_min_iff.mp hx.2).1
          have hx0 : 0 ≤ x := ha0.trans hx.1.le
          have hx1 : x ≤ 1 := hxb.le.trans hb1
          have hxthird : ¬x ≤ 1 / 3 :=
            not_le.mpr (hthird_le.trans_lt hx.1)
          have hxhalf : ¬x ≤ 1 / 2 :=
            not_le.mpr (hhalf_le.trans_lt hx.1)
          have hxtwothirds : x ≤ 2 / 3 :=
            le_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _))
          let u : PositiveParameter := ⟨x, hx0, hx1⟩
          rw [show clampParameter x = positiveParameter u by
            simpa [u] using clampParameter_positiveParameter u]
          rw [twoThreeAverage_price, if_neg (by simpa [u] using hxthird),
            if_neg (by simpa [u] using hxhalf),
            if_pos (by simpa [u] using hxtwothirds)]
        have hlevel : c.raw.knots.rightLevel j = 3 / 2 :=
          constants_eq_of_ae_eq_on_Ioo haePrice hsub hcanonical havg hnonempty
        rw [hlevel]
        simp [fourPriceLevels]
      · have hsub : Set.Ioo a b ⊆ Set.Icc (-1 : ℝ) 1 := by
          intro x hx
          have hx0 : 0 ≤ x := ha0.trans hx.1.le
          have hx1 : x ≤ 1 := hx.2.le.trans hb1
          exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hx0, hx1⟩
        have hcanonical : ∀ x ∈ Set.Ioo a b,
            (minimalSidedParametrisationOperator c (clampParameter x)).2 =
              c.raw.knots.rightLevel j := by
          intro x hx
          have hx0 : 0 ≤ x := ha0.trans hx.1.le
          have hx1 : x ≤ 1 := hx.2.le.trans hb1
          apply minimalCanonical_price_on_rightParameterBlock c j
          · change a < x
            exact hx.1
          · change x < b
            exact hx.2
          · exact hx0
          · exact hx1
        have havg : ∀ x ∈ Set.Ioo a b,
            (twoThreeAverage (clampParameter x)).2 = 5 / 2 := by
          intro x hx
          have hthird_le : 1 / 3 ≤ a := le_of_not_gt hthird
          have hhalf_le : 1 / 2 ≤ a := le_of_not_gt hhalf
          have htwothirds_le : 2 / 3 ≤ a := le_of_not_gt htwothirds
          have hx0 : 0 ≤ x := ha0.trans hx.1.le
          have hx1 : x ≤ 1 := hx.2.le.trans hb1
          have hxthird : ¬x ≤ 1 / 3 :=
            not_le.mpr (hthird_le.trans_lt hx.1)
          have hxhalf : ¬x ≤ 1 / 2 :=
            not_le.mpr (hhalf_le.trans_lt hx.1)
          have hxtwothirds : ¬x ≤ 2 / 3 :=
            not_le.mpr (htwothirds_le.trans_lt hx.1)
          let u : PositiveParameter := ⟨x, hx0, hx1⟩
          rw [show clampParameter x = positiveParameter u by
            simpa [u] using clampParameter_positiveParameter u]
          rw [twoThreeAverage_price, if_neg (by simpa [u] using hxthird),
            if_neg (by simpa [u] using hxhalf),
            if_neg (by simpa [u] using hxtwothirds)]
        have hlevel : c.raw.knots.rightLevel j = 5 / 2 :=
          constants_eq_of_ae_eq_on_Ioo haePrice hsub hcanonical havg hab
        rw [hlevel]
        simp [fourPriceLevels]

theorem rightCount_le_four_of_ae_eq_average
    (c : MinimalCanonicalSidedCurve)
    (hae :
      (fun x : ℝ =>
          minimalSidedParametrisationOperator c (clampParameter x)) =ᵐ[
        MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)]
        fun x : ℝ => twoThreeAverage (clampParameter x)) :
    c.raw.knots.rightCount ≤ 4 := by
  have hsubset : Set.range c.raw.knots.rightLevel ⊆ fourPriceLevels := by
    rintro y ⟨j, rfl⟩
    exact rightLevel_mem_fourPriceLevels_of_ae_eq_average c hae j
  have hfinite : fourPriceLevels.Finite := by
    simp [fourPriceLevels]
  have hcard := Set.ncard_le_ncard hsubset hfinite
  rw [Set.ncard_range_of_injective
      c.raw.knots.rightLevel_strictMono.injective,
    ncard_fourPriceLevels] at hcard
  simpa using hcard

/-- On an open interval contained in one canonical parameter block, almost-
everywhere equality with the explicit midpoint identifies that block's level
with the midpoint's constant value on the interval. -/
theorem rightLevel_eq_of_ae_eq_average_on_Ioo
    (c : MinimalCanonicalSidedCurve)
    (hae :
      (fun x : ℝ =>
          minimalSidedParametrisationOperator c (clampParameter x)) =ᵐ[
        MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)]
        fun x : ℝ => twoThreeAverage (clampParameter x))
    (j : Fin c.raw.knots.rightCount) {a b d : ℝ}
    (hunit : Set.Ioo a b ⊆ Set.Icc (0 : ℝ) 1)
    (hblock : ∀ x ∈ Set.Ioo a b,
      (j : ℝ) / (c.raw.knots.rightCount : ℝ) < x ∧
        x < ((j : ℝ) + 1) / (c.raw.knots.rightCount : ℝ))
    (havg : ∀ x ∈ Set.Ioo a b,
      (twoThreeAverage (clampParameter x)).2 = d)
    (hab : a < b) :
    c.raw.knots.rightLevel j = d := by
  have haePrice :
      (fun x : ℝ =>
          (minimalSidedParametrisationOperator c (clampParameter x)).2) =ᵐ[
        MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)]
        fun x : ℝ => (twoThreeAverage (clampParameter x)).2 :=
    hae.mono fun _ hx => congrArg Prod.snd hx
  have hsub : Set.Ioo a b ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    have hx01 := hunit hx
    exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hx01.1, hx01.2⟩
  have hcanonical : ∀ x ∈ Set.Ioo a b,
      (minimalSidedParametrisationOperator c (clampParameter x)).2 =
        c.raw.knots.rightLevel j := by
    intro x hx
    have hx01 := hunit hx
    have hbounds := hblock x hx
    exact minimalCanonical_price_on_rightParameterBlock c j
      hbounds.1 hbounds.2 hx01.1 hx01.2
  exact constants_eq_of_ae_eq_on_Ioo haePrice hsub hcanonical havg hab

/-- No minimal equal-parameter-block sided curve represents the explicit
two/three-block midpoint, even after quotienting by equality almost everywhere
on the common parameter interval. -/
theorem twoThreeAverage_not_ae_in_minimal_range :
    ¬ ∃ c : MinimalCanonicalSidedCurve,
      (fun x : ℝ =>
          minimalSidedParametrisationOperator c (clampParameter x)) =ᵐ[
        MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)]
        fun x : ℝ => twoThreeAverage (clampParameter x) := by
  rintro ⟨c, hae⟩
  have hle : c.raw.knots.rightCount ≤ 4 :=
    rightCount_le_four_of_ae_eq_average c hae
  have hpos : 0 < c.raw.knots.rightCount := c.rightCount_pos
  have hcases :
      c.raw.knots.rightCount = 1 ∨
      c.raw.knots.rightCount = 2 ∨
      c.raw.knots.rightCount = 3 ∨
      c.raw.knots.rightCount = 4 := by
    omega
  rcases hcases with hcount | hcount | hcount | hcount
  · let j₀ : Fin c.raw.knots.rightCount := ⟨0, by omega⟩
    have hlevel₀ : c.raw.knots.rightLevel j₀ = 0 :=
      rightLevel_eq_of_ae_eq_average_on_Ioo c hae j₀
        (a := 1 / 6) (b := 1 / 4) (d := 0)
        (by
          intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by
          intro x hx
          have hblock : (0 : ℝ) < x ∧ x < 1 := by
            constructor <;> linarith [hx.1, hx.2]
          simpa [j₀, hcount] using hblock)
        (by
          intro x hx
          exact twoThreeAverage_clamp_price_eq_zero
            (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.2]))
        (by norm_num)
    have hlevel₁ : c.raw.knots.rightLevel j₀ = 5 / 2 :=
      rightLevel_eq_of_ae_eq_average_on_Ioo c hae j₀
        (a := 3 / 4) (b := 5 / 6) (d := 5 / 2)
        (by
          intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by
          intro x hx
          have hblock : (0 : ℝ) < x ∧ x < 1 := by
            constructor <;> linarith [hx.1, hx.2]
          simpa [j₀, hcount] using hblock)
        (by
          intro x hx
          exact twoThreeAverage_clamp_price_eq_fiveHalves
            (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1]))
        (by norm_num)
    have hbad : (0 : ℝ) = 5 / 2 := hlevel₀.symm.trans hlevel₁
    norm_num at hbad
  · let j₀ : Fin c.raw.knots.rightCount := ⟨0, by omega⟩
    have hlevel₀ : c.raw.knots.rightLevel j₀ = 0 :=
      rightLevel_eq_of_ae_eq_average_on_Ioo c hae j₀
        (a := 1 / 4) (b := 3 / 10) (d := 0)
        (by
          intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by
          intro x hx
          have hblock : (0 : ℝ) < x ∧ x < 1 / 2 := by
            constructor <;> linarith [hx.1, hx.2]
          simpa [j₀, hcount] using hblock)
        (by
          intro x hx
          exact twoThreeAverage_clamp_price_eq_zero
            (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.2]))
        (by norm_num)
    have hlevel₁ : c.raw.knots.rightLevel j₀ = 1 / 2 :=
      rightLevel_eq_of_ae_eq_average_on_Ioo c hae j₀
        (a := 2 / 5) (b := 9 / 20) (d := 1 / 2)
        (by
          intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by
          intro x hx
          have hblock : (0 : ℝ) < x ∧ x < 1 / 2 := by
            constructor <;> linarith [hx.1, hx.2]
          simpa [j₀, hcount] using hblock)
        (by
          intro x hx
          exact twoThreeAverage_clamp_price_eq_half
            (by linarith [hx.1]) (by linarith [hx.2])
            (by linarith [hx.1]) (by linarith [hx.2]))
        (by norm_num)
    have hbad : (0 : ℝ) = 1 / 2 := hlevel₀.symm.trans hlevel₁
    norm_num at hbad
  · let j₁ : Fin c.raw.knots.rightCount := ⟨1, by omega⟩
    have hlevel₀ : c.raw.knots.rightLevel j₁ = 1 / 2 :=
      rightLevel_eq_of_ae_eq_average_on_Ioo c hae j₁
        (a := 2 / 5) (b := 9 / 20) (d := 1 / 2)
        (by
          intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by
          intro x hx
          have hblock : (1 / 3 : ℝ) < x ∧ x < 2 / 3 := by
            constructor <;> linarith [hx.1, hx.2]
          norm_num [j₁, hcount] at ⊢
          exact hblock)
        (by
          intro x hx
          exact twoThreeAverage_clamp_price_eq_half
            (by linarith [hx.1]) (by linarith [hx.2])
            (by linarith [hx.1]) (by linarith [hx.2]))
        (by norm_num)
    have hlevel₁ : c.raw.knots.rightLevel j₁ = 3 / 2 :=
      rightLevel_eq_of_ae_eq_average_on_Ioo c hae j₁
        (a := 11 / 20) (b := 3 / 5) (d := 3 / 2)
        (by
          intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by
          intro x hx
          have hblock : (1 / 3 : ℝ) < x ∧ x < 2 / 3 := by
            constructor <;> linarith [hx.1, hx.2]
          norm_num [j₁, hcount] at ⊢
          exact hblock)
        (by
          intro x hx
          exact twoThreeAverage_clamp_price_eq_threeHalves
            (by linarith [hx.1]) (by linarith [hx.2])
            (by linarith [hx.1]) (by linarith [hx.2]))
        (by norm_num)
    have hbad : (1 / 2 : ℝ) = 3 / 2 := hlevel₀.symm.trans hlevel₁
    norm_num at hbad
  · let j₁ : Fin c.raw.knots.rightCount := ⟨1, by omega⟩
    have hlevel₀ : c.raw.knots.rightLevel j₁ = 0 :=
      rightLevel_eq_of_ae_eq_average_on_Ioo c hae j₁
        (a := 3 / 10) (b := 8 / 25) (d := 0)
        (by
          intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by
          intro x hx
          have hblock : (1 / 4 : ℝ) < x ∧ x < 1 / 2 := by
            constructor <;> linarith [hx.1, hx.2]
          norm_num [j₁, hcount] at ⊢
          exact hblock)
        (by
          intro x hx
          exact twoThreeAverage_clamp_price_eq_zero
            (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.2]))
        (by norm_num)
    have hlevel₁ : c.raw.knots.rightLevel j₁ = 1 / 2 :=
      rightLevel_eq_of_ae_eq_average_on_Ioo c hae j₁
        (a := 7 / 20) (b := 2 / 5) (d := 1 / 2)
        (by
          intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by
          intro x hx
          have hblock : (1 / 4 : ℝ) < x ∧ x < 1 / 2 := by
            constructor <;> linarith [hx.1, hx.2]
          norm_num [j₁, hcount] at ⊢
          exact hblock)
        (by
          intro x hx
          exact twoThreeAverage_clamp_price_eq_half
            (by linarith [hx.1]) (by linarith [hx.2])
            (by linarith [hx.1]) (by linarith [hx.2]))
        (by norm_num)
    have hbad : (0 : ℝ) = 1 / 2 := hlevel₀.symm.trans hlevel₁
    norm_num at hbad

/--
Alternative route for `cor:sided-parametrisation-not-weakly-convex` (not the
mapped proof): Hilbert-valued (almost-everywhere quotient) clause of the corollary
in `2 - day-ahead/2_clearing_operator_price_curves.tex`, proved here by an
exhaustive case split over the possible block counts.  The mapped proof, which
follows the thesis's explicit example with the continuity and graph-recovery
argument (quarter knot `5/6` versus `5/8`), is
`SidedSourceExclusion.canonicalLp_not_weaklyConvex_source` /
`canonical_not_weaklyConvexAE_source` in `CanonicalSidedSourceExclusion.lean`.

Proof note: equality in the `L²([-1,1]; ℝ × ℝ)` quotient is represented by
equality almost everywhere with respect to restricted Lebesgue measure.  The
two/three-block midpoint has four positive-measure price levels.  Any canonical
encoding equal to it almost everywhere therefore has at most four strictly
ordered positive-side blocks.  The possible block counts `1`, `2`, `3`, and
`4` each place one midpoint breakpoint strictly inside a canonical parameter
block, forcing that block to carry two distinct price levels. -/
theorem sidedParametrisationHilbert_not_weaklyConvex :
    ¬ IsWeaklyConvexAE minimalSidedParametrisationOperator := by
  intro hweak
  obtain ⟨c, hc⟩ := hweak minimalTwoBlockCurve minimalThreeBlockCurve
    (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  apply twoThreeAverage_not_ae_in_minimal_range
  refine ⟨c, ?_⟩
  simpa [twoThreeAverage, minimalSidedParametrisationOperator,
    minimalTwoBlockCurve, minimalThreeBlockCurve] using hc

end

end SidedParametrisation
end DayAhead
end Thesis
