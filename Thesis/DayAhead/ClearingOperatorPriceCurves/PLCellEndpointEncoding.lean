import Thesis.DayAhead.ClearingOperatorPriceCurves.PLParametrisation
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCanonicalEncoding
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Continuous L² assembly from fixed-cell endpoint data

This is the last analytic step of the proof of `prop:pl-encoding-measurable`.
After the combinatorial comparison cells fix the numbers of left/right
segments, their parameter boundaries are fixed. Each segment records both
one-sided price endpoints, as well as its quantity endpoints. Their affine
interpolant is a linear continuous function of this finite endpoint data.

This module does not assert that the comparison cells for vendor lists have
already been constructed. That separate finite-branch argument must supply
the measurable endpoint functions and identify the canonical representative.
-/

noncomputable section
namespace Thesis.DayAhead.PLCellEndpointEncoding

open Set MeasureTheory PriceCurves PriceCurveHilbert
open scoped BigOperators

abbrev Endpoints (n : ℕ) := Fin n → (PricePair × PricePair)

def cell {n : ℕ} (left right : Fin n → ℝ) (i : Fin n) : Set Parameter :=
  (Subtype.val : Parameter → ℝ) ⁻¹' Ioc (left i) (right i)

theorem cell_measurable {n : ℕ} (left right : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (cell left right i) :=
  measurableSet_Ioc.preimage measurable_subtype_coe

def graph {n : ℕ} (left right : Fin n → ℝ) (z : Endpoints n)
    (i : Fin n) (u : Parameter) : PricePair :=
  (1 - ((u : ℝ) - left i) / (right i - left i)) • (z i).1 +
    (((u : ℝ) - left i) / (right i - left i)) • (z i).2

theorem graph_continuous {n : ℕ} (left right : Fin n → ℝ) (z : Endpoints n)
    (i : Fin n) : Continuous (graph left right z i) := by
  unfold graph
  fun_prop

def representative {n : ℕ} (left right : Fin n → ℝ) (z : Endpoints n) :
    Parameter → PricePair :=
  fun u => ∑ i, (cell left right i).indicator (graph left right z i) u

variable (μ : Measure Parameter) [IsFiniteMeasure μ]

theorem graph_memLp {n : ℕ} (left right : Fin n → ℝ) (z : Endpoints n)
    (i : Fin n) : MemLp (graph left right z i) 2 μ := by
  have hc := graph_continuous left right z i
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hc.norm.continuousOn
  exact MemLp.of_bound hc.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun u => hC ⟨u, mem_univ _, rfl⟩)

theorem representative_memLp {n : ℕ} (left right : Fin n → ℝ) (z : Endpoints n) :
    MemLp (representative left right z) 2 μ :=
  memLp_finset_sum Finset.univ (fun i _ =>
    (graph_memLp μ left right z i).indicator (cell_measurable left right i))

theorem representative_add {n : ℕ} (left right : Fin n → ℝ) (z w : Endpoints n) :
    representative left right (z + w) =
      representative left right z + representative left right w := by
  funext u
  simp only [representative, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : u ∈ cell left right i
  · simp only [indicator_of_mem hu, graph, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      smul_add, add_add_add_comm]
  · simp only [indicator_of_notMem hu, add_zero]

theorem representative_smul {n : ℕ} (left right : Fin n → ℝ) (c : ℝ) (z : Endpoints n) :
    representative left right (c • z) = c • representative left right z := by
  funext u
  simp only [representative, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : u ∈ cell left right i
  · simp only [indicator_of_mem hu]
    let t := ((u : ℝ) - left i) / (right i - left i)
    change (1 - t) • (c • (z i).1) + t • (c • (z i).2) =
      c • ((1 - t) • (z i).1 + t • (z i).2)
    rw [smul_add, smul_comm c (1 - t), smul_comm c t]
  · simp only [indicator_of_notMem hu, smul_zero]

def endpointLinearMap {n : ℕ} (left right : Fin n → ℝ) :
    Endpoints n →ₗ[ℝ] PriceHilbertSpace μ where
  toFun z := (representative_memLp μ left right z).toLp (representative left right z)
  map_add' z w := by
    apply Lp.ext
    filter_upwards [(representative_memLp μ left right (z + w)).coeFn_toLp,
      (representative_memLp μ left right z).coeFn_toLp,
      (representative_memLp μ left right w).coeFn_toLp,
      Lp.coeFn_add ((representative_memLp μ left right z).toLp _)
        ((representative_memLp μ left right w).toLp _)] with u hzw hz hw hadd
    simp only [Pi.add_apply] at hadd
    rw [hadd, hzw, hz, hw]
    exact congrFun (representative_add left right z w) u
  map_smul' c z := by
    apply Lp.ext
    filter_upwards [(representative_memLp μ left right (c • z)).coeFn_toLp,
      (representative_memLp μ left right z).coeFn_toLp,
      Lp.coeFn_smul c ((representative_memLp μ left right z).toLp _)] with u hcz hz hsmul
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hsmul
    rw [hsmul, hcz, hz]
    exact congrFun (representative_smul left right c z) u

/-- Fixed-cell reconstruction is linear and continuous in all quantity and
one-sided price endpoints. No continuity of the price graph at a jump is used. -/
def endpointContinuousLinearMap {n : ℕ} (left right : Fin n → ℝ) :
    Endpoints n →L[ℝ] PriceHilbertSpace μ :=
  ⟨endpointLinearMap μ left right, (endpointLinearMap μ left right).continuous_of_finiteDimensional⟩

theorem measurable_endpoint_assembly {A : Type*} [MeasurableSpace A] {n : ℕ}
    (left right : Fin n → ℝ) (data : A → Endpoints n) (hdata : Measurable data) :
    @Measurable A (PriceHilbertSpace μ) _ (borel (PriceHilbertSpace μ))
      (fun a => endpointContinuousLinearMap μ left right (data a)) := by
  letI : MeasurableSpace (PriceHilbertSpace μ) := borel (PriceHilbertSpace μ)
  letI : BorelSpace (PriceHilbertSpace μ) := ⟨rfl⟩
  exact (endpointContinuousLinearMap μ left right).continuous.measurable.comp hdata

theorem coeFn_endpoint_assembly {n : ℕ} (left right : Fin n → ℝ) (z : Endpoints n) :
    endpointContinuousLinearMap μ left right z =ᵐ[μ] representative left right z :=
  (representative_memLp μ left right z).coeFn_toLp

/-- The actual canonical encoding equals an endpoint assembly whenever their
Euclidean representatives agree almost everywhere. -/
theorem canonical_eq_endpoint_of_ae {n : ℕ} (f : PiecewiseAffinePriceCurves.Curve)
    (left right : Fin n → ℝ) (z : Endpoints n)
    (h : (fun u => pairEquiv (PLCanonicalEncoding.encoding f u)) =ᵐ[μ]
      representative left right z) :
    PLCanonicalEncoding.encodingLp μ f = endpointContinuousLinearMap μ left right z := by
  apply Lp.ext
  filter_upwards [PLParametrisation.coeFn_encodingLp μ f (PLCanonicalEncoding.admissible f),
    coeFn_endpoint_assembly μ left right z, h] with u hf hz hu
  exact hf.trans (hu.trans hz.symm)

/-- Different selected values at finitely many parameter knots do not change
the canonical L² class under the source's atomless parameter measure. -/
theorem canonical_eq_endpoint_off_finite [NoAtoms μ] {n : ℕ}
    (f : PiecewiseAffinePriceCurves.Curve) (left right : Fin n → ℝ) (z : Endpoints n)
    (bad : Set Parameter) (hbad : bad.Finite)
    (h : ∀ u ∉ bad, pairEquiv (PLCanonicalEncoding.encoding f u) =
      representative left right z u) :
    PLCanonicalEncoding.encodingLp μ f = endpointContinuousLinearMap μ left right z := by
  apply canonical_eq_endpoint_of_ae
  filter_upwards [hbad.countable.ae_notMem μ] with u hu
  exact h u hu

theorem measurable_of_countable_cells {A ι H : Type*} [MeasurableSpace A]
    [MeasurableSpace H] [Countable ι] (cells : ι → Set A)
    (hmeas : ∀ i, MeasurableSet (cells i)) (hcover : ∀ a, ∃ i, a ∈ cells i)
    (f : A → H) (hf : ∀ i, Measurable (fun a : cells i => f a)) : Measurable f := by
  intro t ht
  have he : f ⁻¹' t = ⋃ i, (Subtype.val : cells i → A) ''
      ((fun a : cells i => f a) ⁻¹' t) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi⟩ := hcover a
      exact mem_iUnion.mpr ⟨i, ⟨⟨a, hi⟩, ha, rfl⟩⟩
    · intro ha
      obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp ha
      exact hx
  rw [he]
  exact MeasurableSet.iUnion fun i => MeasurableSet.subtype_image (hmeas i) (hf i ht)

/-- The source's final countable-pasting step, with every finite-comparison
cell, its measurable endpoint data and its canonical identification explicit.
Constructing those data from the literal vendor lists remains a separate
premise of this helper; it is not assumed to have been discharged here. -/
theorem canonical_measurable_of_endpoint_cells {A ι : Type*} [MeasurableSpace A]
    [Countable ι] (cells : ι → Set A) (hmeas : ∀ i, MeasurableSet (cells i))
    (hcover : ∀ a, ∃ i, a ∈ cells i) (count : ι → ℕ)
    (left right : ∀ i, Fin (count i) → ℝ)
    (data : ∀ i, cells i → Endpoints (count i)) (hdata : ∀ i, Measurable (data i))
    (f : A → PiecewiseAffinePriceCurves.Curve)
    (heq : ∀ i (a : cells i), PLCanonicalEncoding.encodingLp μ (f a) =
      endpointContinuousLinearMap μ (left i) (right i) (data i a)) :
    @Measurable A (PriceHilbertSpace μ) _ (borel (PriceHilbertSpace μ))
      (fun a => PLCanonicalEncoding.encodingLp μ (f a)) := by
  letI : MeasurableSpace (PriceHilbertSpace μ) := borel (PriceHilbertSpace μ)
  apply measurable_of_countable_cells cells hmeas hcover
  intro i
  have hm := measurable_endpoint_assembly μ (left i) (right i) (data i) (hdata i)
  have hfun : (fun a : cells i => PLCanonicalEncoding.encodingLp μ (f a)) =
      (fun a => endpointContinuousLinearMap μ (left i) (right i) (data i a)) :=
    funext (heq i)
  rw [hfun]
  exact hm

end Thesis.DayAhead.PLCellEndpointEncoding
