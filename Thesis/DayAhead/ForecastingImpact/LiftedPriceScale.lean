import Thesis.DayAhead.PriceCurveAnalysis.PriceScale
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # The source's genuine infinite-dimensional lifted price transform

The carrier is L² of Euclidean two-vectors. Both maps respect almost-everywhere
equality. The nonlinear inverse is defined only on its stated L² domain.
-/

noncomputable section
namespace Thesis.DayAhead.LiftedPriceScale

open MeasureTheory Filter
open scoped ENNReal BigOperators
open PriceScale

abbrev Point := EuclideanSpace ℝ (Fin 2)

def pointLift (c : ℝ) (v : Point) : Point :=
  WithLp.toLp 2 (fun i ↦ if i = 0 then v i else transform c (v i))

def pointInverse (c : ℝ) (v : Point) : Point :=
  WithLp.toLp 2 (fun i ↦ if i = 0 then v i else inverse c (v i))

theorem pointInverse_lift (c : ℝ) (hc : c ≠ 0) (v : Point) :
    pointInverse c (pointLift c v) = v := by
  ext i
  by_cases hi : i = 0 <;> simp [pointInverse, pointLift, PiLp.toLp_apply, hi,
    inverse_transform c hc]

theorem pointLift_inverse (c : ℝ) (hc : c ≠ 0) (v : Point) :
    pointLift c (pointInverse c v) = v := by
  ext i
  by_cases hi : i = 0 <;> simp [pointInverse, pointLift, PiLp.toLp_apply, hi,
    transform_inverse c hc]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem pointLift_memLp (c : ℝ) (hc : 0 < c) (f : Ω →₂[μ] Point) :
    MemLp (fun x ↦ pointLift c (f x)) 2 μ := by
  apply MemLp.of_eval_piLp
  intro i
  by_cases hi : i = 0
  · simpa only [pointLift, PiLp.toLp_apply, if_pos hi] using (Lp.memLp f).eval_piLp i
  · simpa only [pointLift, PiLp.toLp_apply, if_neg hi] using
      transform_memLp c hc (fun x ↦ f x i) ((Lp.memLp f).eval_piLp i)

/-- Original label: `defn:lifted-price-scale-smearing`.
The actual lifted operator on L² equivalence classes. -/
def lift (c : ℝ) (hc : 0 < c) (f : Ω →₂[μ] Point) : Ω →₂[μ] Point :=
  (pointLift_memLp c hc f).toLp (fun x ↦ pointLift c (f x))

theorem lift_ae (c : ℝ) (hc : 0 < c) (f : Ω →₂[μ] Point) :
    ⇑(lift c hc f) =ᵐ[μ] fun x ↦ pointLift c (f x) := MemLp.coeFn_toLp _

/-- The source's inverse domain, expressed using genuine L² membership. -/
def InverseDomain (c : ℝ) :=
  {f : Ω →₂[μ] Point // MemLp (fun x ↦ pointInverse c (f x)) 2 μ}

theorem inverseDomain_iff (c : ℝ) (f : Ω →₂[μ] Point) :
    MemLp (fun x ↦ pointInverse c (f x)) 2 μ ↔
      MemLp (fun x ↦ inverse c (f x 1)) 2 μ := by
  constructor
  · intro h
    simpa [pointInverse, PiLp.toLp_apply] using h.eval_piLp 1
  · intro h
    apply MemLp.of_eval_piLp
    intro i
    fin_cases i
    · simpa [pointInverse, PiLp.toLp_apply] using (Lp.memLp f).eval_piLp 0
    · simpa [pointInverse, PiLp.toLp_apply] using h

/-- Original label: `defn:lifted-price-scale-smearing`.
The inverse is available precisely on the domain stated by the source. -/
def inverseLift (c : ℝ) (f : InverseDomain (μ := μ) c) : Ω →₂[μ] Point :=
  f.property.toLp (fun x ↦ pointInverse c (f.val x))

theorem inverseLift_ae (c : ℝ) (f : InverseDomain (μ := μ) c) :
    ⇑(inverseLift c f) =ᵐ[μ] fun x ↦ pointInverse c (f.val x) := MemLp.coeFn_toLp _

theorem lift_in_inverseDomain (c : ℝ) (hc : 0 < c) (f : Ω →₂[μ] Point) :
    MemLp (fun x ↦ pointInverse c (lift c hc f x)) 2 μ := by
  apply (Lp.memLp f).ae_eq
  filter_upwards [lift_ae c hc f] with x hx
  rw [hx, pointInverse_lift c hc.ne']

theorem inverseLift_lift (c : ℝ) (hc : 0 < c) (f : Ω →₂[μ] Point) :
    inverseLift c ⟨lift c hc f, lift_in_inverseDomain c hc f⟩ = f := by
  apply Lp.ext
  filter_upwards [inverseLift_ae c ⟨lift c hc f, lift_in_inverseDomain c hc f⟩,
    lift_ae c hc f] with x hinv hlift
  rw [hinv, hlift, pointInverse_lift c hc.ne']

theorem lift_inverseLift (c : ℝ) (hc : 0 < c) (f : InverseDomain (μ := μ) c) :
    lift c hc (inverseLift c f) = f.val := by
  apply Lp.ext
  filter_upwards [lift_ae c hc (inverseLift c f), inverseLift_ae c f] with x hlift hinv
  rw [hlift, hinv, pointLift_inverse c hc.ne']

def coordinate (i : Fin 2) : (Ω →₂[μ] Point) →L[ℝ] (Ω →₂[μ] ℝ) :=
  (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i).compLpL 2 μ

theorem coordinate_ae (i : Fin 2) (f : Ω →₂[μ] Point) :
    ⇑(coordinate i f) =ᵐ[μ] fun x ↦ f x i :=
  ContinuousLinearMap.coeFn_compLp _ _

theorem inverseLift_quantity (c : ℝ) (f : InverseDomain (μ := μ) c) :
    coordinate 0 (inverseLift c f) = coordinate 0 f.val := by
  apply Lp.ext
  filter_upwards [coordinate_ae 0 (inverseLift c f), coordinate_ae 0 f.val,
    inverseLift_ae c f] with x h0 h1 hinv
  rw [h0, h1, hinv]
  simp [pointInverse, PiLp.toLp_apply]

theorem lift_quantity (c : ℝ) (hc : 0 < c) (f : Ω →₂[μ] Point) :
    coordinate 0 (lift c hc f) = coordinate 0 f := by
  apply Lp.ext
  filter_upwards [coordinate_ae 0 (lift c hc f), coordinate_ae 0 f,
    lift_ae c hc f] with x h0 h1 hlift
  rw [h0, h1, hlift]
  simp [pointLift, PiLp.toLp_apply]

/-- Original label: `defn:lifted-price-scale-smearing`.
The finite Hilbert-valued smearing estimator, with every shifted residual
required to belong to the actual nonlinear inverse domain. -/
def smear {n : ℕ} (c : ℝ) (z : Ω →₂[μ] Point) (e : Fin (n + 1) → Ω →₂[μ] Point)
    (hd : ∀ i, MemLp (fun x ↦ pointInverse c ((z + e i) x)) 2 μ) : Ω →₂[μ] Point :=
  (n + 1 : ℝ)⁻¹ • ∑ i, inverseLift c ⟨z + e i, hd i⟩

theorem smear_quantity {n : ℕ} (c : ℝ) (z : Ω →₂[μ] Point)
    (e : Fin (n + 1) → Ω →₂[μ] Point)
    (hd : ∀ i, MemLp (fun x ↦ pointInverse c ((z + e i) x)) 2 μ)
    (he : ∀ i, coordinate 0 (e i) = 0) : coordinate 0 (smear c z e hd) = coordinate 0 z := by
  simp only [smear, map_smul, map_sum, inverseLift_quantity, map_add, he, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [inv_mul_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0), one_smul]

end Thesis.DayAhead.LiftedPriceScale
