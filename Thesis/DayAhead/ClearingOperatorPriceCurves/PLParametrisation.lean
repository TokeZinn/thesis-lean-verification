import Thesis.DayAhead.ClearingOperatorPriceCurves.PiecewiseAffinePriceCurves
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveHilbert
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Admissible and linear encodings of the full affine price-curve class

The analytic argument uses monotonicity on the recorded compact domain. It
therefore applies to nonconstant affine pieces, without a finite-range
assumption. This module does not construct the canonical breakpoint-based
sided encoding from an order book.
-/

noncomputable section
namespace Thesis.DayAhead.PLParametrisation

open Set MeasureTheory PriceCurves PriceCurveHilbert
open PiecewiseAffinePriceCurves

def value (f : Curve) : Icc f.leftEndpoint f.rightEndpoint → ℝ :=
  fun x => f.price x

theorem value_monotone (f : Curve) : Monotone (value f) :=
  fun x y hxy => f.monotone x.property y.property hxy

/-- Original label: `defn:admissible-price-curve-parametrisation`.
The parametriser data for the current unrestricted affine curve class. -/
structure Admissible (f : Curve) where
  toFun : Parameter → Icc f.leftEndpoint f.rightEndpoint
  continuous : Continuous toFun
  monotone : Monotone toFun
  surjective : Function.Surjective toFun
  zero : (toFun parameterZero : ℝ) = 0

instance (f : Curve) : CoeFun (Admissible f)
    (fun _ => Parameter → Icc f.leftEndpoint f.rightEndpoint) := ⟨Admissible.toFun⟩

def graphRepresentative (f : Curve) (a : Admissible f) : Parameter → ℝ × ℝ :=
  fun u => (a u, f.price (a u))

theorem graphRepresentative_measurable (f : Curve) (a : Admissible f) :
    Measurable (graphRepresentative f a) :=
  Measurable.prod
    (continuous_subtype_val.comp a.continuous).measurable
    ((value_monotone f).measurable.comp a.continuous.measurable)

theorem price_norm_le (f : Curve) (x : Icc f.leftEndpoint f.rightEndpoint) :
    ‖f.price x‖ ≤ max |f.price f.leftEndpoint| |f.price f.rightEndpoint| := by
  rw [Real.norm_eq_abs]
  apply abs_le_max_abs_abs
  · exact f.monotone ⟨le_rfl, f.left_nonpos.trans f.right_nonneg⟩ x.property x.property.1
  · exact f.monotone x.property ⟨f.left_nonpos.trans f.right_nonneg, le_rfl⟩ x.property.2

theorem graphRepresentative_memLp (μ : Measure Parameter) [IsFiniteMeasure μ]
    (f : Curve) (a : Admissible f) : MemLp (graphRepresentative f a) 2 μ := by
  let quantityBound := max |f.leftEndpoint| |f.rightEndpoint|
  let priceBound := max |f.price f.leftEndpoint| |f.price f.rightEndpoint|
  refine MemLp.of_bound (graphRepresentative_measurable f a).aestronglyMeasurable
    (max quantityBound priceBound) (Filter.Eventually.of_forall fun u => ?_)
  rw [graphRepresentative, Prod.norm_def]
  apply max_le
  · exact (abs_le_max_abs_abs (a u).property.1 (a u).property.2).trans (le_max_left _ _)
  · exact (price_norm_le f (a u)).trans (le_max_right _ _)

/-- Original label: `eq:parametrised-graph-recovers-curve`.
This is a pointwise graph identity before passing to equivalence classes. -/
theorem range_graphRepresentative (f : Curve) (a : Admissible f) :
    Set.range (graphRepresentative f a) = f.graph := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(a u).property, rfl⟩
  · rintro ⟨hz, he⟩
    obtain ⟨u, hu⟩ := a.surjective ⟨z.1, hz⟩
    refine ⟨u, ?_⟩
    apply Prod.ext
    · exact congrArg Subtype.val hu
    · change f.price (a u) = z.2
      rw [hu]
      exact he.symm

/-- The actual Euclidean-valued Hilbert encoding; ordinary product norms
are used only as a boundedness bridge. -/
def encodingLp (μ : Measure Parameter) [IsFiniteMeasure μ] (f : Curve) (a : Admissible f) :
    PriceHilbertSpace μ :=
  liftLp μ ((graphRepresentative_memLp μ f a).toLp (graphRepresentative f a))

theorem coeFn_encodingLp (μ : Measure Parameter) [IsFiniteMeasure μ]
    (f : Curve) (a : Admissible f) :
    encodingLp μ f a =ᵐ[μ] fun u => pairEquiv (graphRepresentative f a u) :=
  coeFn_liftLp_toLp μ (graphRepresentative_memLp μ f a)

/-- Original label: `defn:linear-parametrisation-operator`.
The source formula on the full current affine carrier. -/
def linearQuantity (f : Curve) (u : ℝ) : ℝ :=
  if u ≤ 0 then -f.leftEndpoint * u else f.rightEndpoint * u

theorem linearQuantity_continuous (f : Curve) : Continuous (linearQuantity f) := by
  apply (continuous_const.mul continuous_id).if_le
    (continuous_const.mul continuous_id) continuous_id continuous_const
  intro u hu
  have hu0 : u = 0 := by simpa using hu
  simp [hu0]

theorem linearQuantity_monotone (f : Curve) : Monotone (linearQuantity f) := by
  intro u v huv
  simp only [linearQuantity]
  split_ifs with hu hv
  · nlinarith [f.left_nonpos]
  · nlinarith [f.left_nonpos, f.right_nonneg]
  · nlinarith
  · nlinarith [f.right_nonneg]

@[simp] theorem linearQuantity_left (f : Curve) :
    linearQuantity f (-1) = f.leftEndpoint := by simp [linearQuantity]

@[simp] theorem linearQuantity_right (f : Curve) :
    linearQuantity f 1 = f.rightEndpoint := by simp [linearQuantity]

@[simp] theorem linearQuantity_zero (f : Curve) : linearQuantity f 0 = 0 := by
  simp [linearQuantity]

def linearDomainMap (f : Curve) : Parameter → Icc f.leftEndpoint f.rightEndpoint :=
  fun u => ⟨linearQuantity f u, by
    constructor
    · simpa using linearQuantity_monotone f u.property.1
    · simpa using linearQuantity_monotone f u.property.2⟩

theorem linearDomainMap_continuous (f : Curve) : Continuous (linearDomainMap f) :=
  Continuous.subtype_mk ((linearQuantity_continuous f).comp continuous_subtype_val) _

theorem linearDomainMap_surjective (f : Curve) : Function.Surjective (linearDomainMap f) := by
  intro x
  have hx : (x : ℝ) ∈ linearQuantity f '' Icc (-1 : ℝ) 1 := by
    apply intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
      (linearQuantity_continuous f).continuousOn
    simp only [linearQuantity_left, linearQuantity_right]
    exact x.property
  obtain ⟨u, hu, hux⟩ := hx
  exact ⟨⟨u, hu⟩, Subtype.ext hux⟩

def linearAdmissible (f : Curve) : Admissible f where
  toFun := linearDomainMap f
  continuous := linearDomainMap_continuous f
  monotone := fun _ _ h => linearQuantity_monotone f h
  surjective := linearDomainMap_surjective f
  zero := linearQuantity_zero f

def linearEncoding (f : Curve) : Parameter → ℝ × ℝ :=
  graphRepresentative f (linearAdmissible f)

def linearEncodingLp (μ : Measure Parameter) [IsFiniteMeasure μ] (f : Curve) :
    PriceHilbertSpace μ := encodingLp μ f (linearAdmissible f)

end Thesis.DayAhead.PLParametrisation
