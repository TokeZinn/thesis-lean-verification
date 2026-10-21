import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! # The current joint-law condition for avoiding priority ties

Source: market representations, paragraph at line 290. Independence is used
to obtain the product law; nonatomic marginal laws alone do not do this.
-/

open Set MeasureTheory ProbabilityTheory

namespace Thesis.Foundations.MarketRepresentation.OrderTies

/-- Independent attributes with a nonatomic second marginal cannot tie.
The measurable-diagonal hypothesis holds in the standard Borel attribute
spaces used for price, quantity and time. -/
theorem independent_attributes_ne_ae
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableEq E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → E)
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) [NoAtoms (μ.map Y)] : ∀ᵐ ω ∂μ, X ω ≠ Y ω := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map
    hX.aemeasurable hY.aemeasurable).mp hXY
  have hd : μ {ω | X ω = Y ω} = 0 := by
    change μ ((fun ω => (X ω, Y ω)) ⁻¹' diagonal E) = 0
    rw [← Measure.map_apply (μ := μ) (hX.prodMk hY) measurableSet_diagonal, hprod,
      Measure.prod_apply measurableSet_diagonal]
    simp only [diagonal, preimage_setOf_eq]
    have hset (x : E) : {y : E | x = y} = {x} := by ext y; simp [eq_comm]
    simp only [hset, measure_singleton, lintegral_zero]
  rw [ae_iff]
  simpa only [not_not] using hd

/-- The pairwise no-tie condition holds simultaneously over a countable
family. This conclusion needs the joint condition, not independence of the
whole family. -/
theorem countable_attributes_injective_ae
    {Ω E A : Type*} [MeasurableSpace Ω] [Countable A]
    (μ : Measure Ω) (U : A → Ω → E)
    (h : ∀ a b, a ≠ b → ∀ᵐ ω ∂μ, U a ω ≠ U b ω) :
    ∀ᵐ ω ∂μ, Function.Injective (fun a => U a ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ a b, a ≠ b → U a ω ≠ U b ω := by
    simpa only [ae_all_iff] using h
  filter_upwards [hall] with ω hω
  intro a b he
  by_contra hab
  exact hω a b hab he

end Thesis.Foundations.MarketRepresentation.OrderTies
