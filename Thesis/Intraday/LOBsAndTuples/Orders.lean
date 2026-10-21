import Thesis.Intraday.LOBsAndTuples.Retagging
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # The bounded intraday order space

The quantity coordinate is stored logarithmically. `physical` and `ofPhysical`
give inverse translations to the manuscript's `(price, positive quantity, time)`.
This realizes its precise sum metric and makes completeness explicit.
-/

noncomputable section

namespace Thesis.Intraday

open Set

abbrev Price := Icc (-9999 : ℝ) 9999
abbrev Time := Icc (0 : ℝ) 1
abbrev PositiveQuantity := Ioi (0 : ℝ)
abbrev Order := WithLp 1 (Price × WithLp 1 (ℝ × Time))

def price (x : Order) : ℝ := x.fst.val
def logQuantity (x : Order) : ℝ := x.snd.fst
def quantity (x : Order) : ℝ := Real.exp (logQuantity x)
def time (x : Order) : ℝ := x.snd.snd.val

def physical (x : Order) : Price × PositiveQuantity × Time :=
  (x.fst, ⟨quantity x, Real.exp_pos _⟩, x.snd.snd)

def ofPhysical (x : Price × PositiveQuantity × Time) : Order :=
  WithLp.toLp 1 (x.1, WithLp.toLp 1 (Real.log x.2.1.val, x.2.2))

@[simp] theorem physical_ofPhysical (x : Price × PositiveQuantity × Time) :
    physical (ofPhysical x) = x := by
  rcases x with ⟨p, ⟨q, hq⟩, t⟩
  simp [physical, ofPhysical, quantity, logQuantity, Real.exp_log hq]

@[simp] theorem ofPhysical_physical (x : Order) : ofPhysical (physical x) = x := by
  simp only [physical, ofPhysical, quantity, logQuantity, Real.log_exp]
  rfl

/-- The exact metric from the intraday chapter on one side of the market. -/
theorem order_dist (x y : Order) :
    dist x y = |price x - price y| +
      |Real.log (quantity x) - Real.log (quantity y)| + |time x - time y| := by
  simp [WithLp.prod_dist_eq_add, price, quantity, logQuantity, time,
    Subtype.dist_eq, Real.dist_eq, add_assoc]

theorem order_complete : CompleteSpace Order := inferInstance
theorem order_separable : TopologicalSpace.SeparableSpace Order := inferInstance

theorem continuous_price : Continuous price :=
  continuous_subtype_val.comp (WithLp.continuous_fst ..)
theorem continuous_logQuantity : Continuous logQuantity :=
  (WithLp.continuous_fst ..).comp (WithLp.continuous_snd ..)
theorem continuous_quantity : Continuous quantity :=
  Real.continuous_exp.comp continuous_logQuantity
theorem continuous_time : Continuous time :=
  continuous_subtype_val.comp
    ((WithLp.continuous_snd ..).comp (WithLp.continuous_snd ..))

instance : MeasurableSpace Order := borel Order
instance : BorelSpace Order := ⟨rfl⟩

theorem quantity_pos (x : Order) : 0 < quantity x := Real.exp_pos _
theorem price_bounds (x : Order) : -9999 ≤ price x ∧ price x ≤ 9999 := x.fst.property

/-- A total Borel helper. Only strictly positive new quantities are used in
execution branches, where `withQuantity_quantity` gives the literal update. -/
def withQuantity (x : Order) (q : ℝ) : Order :=
  WithLp.toLp 1 (x.fst, WithLp.toLp 1 (Real.log q, x.snd.snd))

@[simp] theorem withQuantity_price (x : Order) (q : ℝ) :
    price (withQuantity x q) = price x := rfl
@[simp] theorem withQuantity_time (x : Order) (q : ℝ) :
    time (withQuantity x q) = time x := rfl
theorem withQuantity_quantity (x : Order) {q : ℝ} (hq : 0 < q) :
    quantity (withQuantity x q) = q := Real.exp_log hq

theorem measurable_withQuantity : Measurable (fun x : Order × ℝ => withQuantity x.1 x.2) := by
  unfold withQuantity
  apply (WithLp.prod_continuous_toLp 1 _ _).measurable.comp
  apply Measurable.prodMk
  · exact (WithLp.continuous_fst ..).measurable.comp measurable_fst
  · apply (WithLp.prod_continuous_toLp 1 _ _).measurable.comp
    exact (Real.measurable_log.comp measurable_snd).prodMk
      (((WithLp.continuous_snd ..).comp (WithLp.continuous_snd ..)).measurable.comp
        measurable_fst)

end Thesis.Intraday
