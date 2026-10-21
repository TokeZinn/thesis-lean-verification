import Thesis.DayAhead.FunctionalDataAnalysis.FunctionalData
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib

/-! # Second moments for the Hilbert-space central limit theorem

Independence makes centered Hilbert-valued summands orthogonal in L².
Consequently their squared-norm second moments add. This supplies the
uniform bounds for the normalized sums and their finite-dimensional tails.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ENNReal NNReal

namespace Thesis.DayAhead.HilbertCLTMoments

variable {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] [IsProbabilityMeasure μ] in
theorem memLp_integrable_inner {X Y : Ω → H} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => inner ℝ (X ω) (Y ω)) μ :=
  (hX.norm.integrable_mul hY.norm).mono' (hX.1.inner hY.1)
    (Eventually.of_forall fun ω => norm_inner_le_norm (X ω) (Y ω))

theorem integral_inner_of_indep {X Y : Ω → H} (hX : Integrable X μ) (hY : Integrable Y μ)
    (hindep : IndepFun X Y μ) :
    (∫ ω, inner ℝ (X ω) (Y ω) ∂μ) = inner ℝ (∫ ω, X ω ∂μ) (∫ ω, Y ω ∂μ) := by
  have hXid : Integrable id (μ.map X) :=
    (integrable_map_measure (by fun_prop) hX.aestronglyMeasurable.aemeasurable).mpr hX
  have hYid : Integrable id (μ.map Y) :=
    (integrable_map_measure (by fun_prop) hY.aestronglyMeasurable.aemeasurable).mpr hY
  have hprod : Integrable (fun p : H × H => inner ℝ p.1 p.2)
      ((μ.map X).prod (μ.map Y)) :=
    (hXid.norm.mul_prod hYid.norm).mono' (by fun_prop)
      (Eventually.of_forall fun p => norm_inner_le_norm p.1 p.2)
  change (∫ ω, (fun p : H × H => inner ℝ p.1 p.2) (X ω, Y ω) ∂μ) = _
  rw [← integral_map (f := fun p : H × H => inner ℝ p.1 p.2)
      (hX.aestronglyMeasurable.aemeasurable.prodMk
      hY.aestronglyMeasurable.aemeasurable) (by fun_prop),
    (indepFun_iff_map_prod_eq_prod_map_map hX.aestronglyMeasurable.aemeasurable
      hY.aestronglyMeasurable.aemeasurable).mp hindep,
    integral_prod _ hprod]
  change (∫ x : H, ∫ y : H, inner ℝ x (id y) ∂μ.map Y ∂μ.map X) = _
  simp_rw [integral_inner hYid]
  rw [show (fun x : H => inner ℝ x (∫ y, id y ∂μ.map Y)) =
      (fun x : H => inner ℝ (∫ y, id y ∂μ.map Y) x) from funext fun x => real_inner_comm _ _]
  change Integrable (fun x : H => x) (μ.map X) at hXid
  rw [integral_inner hXid, real_inner_comm]
  rw [integral_map hX.aestronglyMeasurable.aemeasurable (by fun_prop),
    integral_map hY.aestronglyMeasurable.aemeasurable (by fun_prop)]
  rfl

theorem integral_norm_sq_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → H)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hindep : (s : Set ι).Pairwise fun i j => IndepFun (X i) (X j) μ) :
    (∫ ω, ‖∑ i ∈ s, X i ω‖ ^ 2 ∂μ) = ∑ i ∈ s, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  classical
  simp_rw [← real_inner_self_eq_norm_sq, inner_sum, sum_inner]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finset_sum]
    · apply Finset.sum_eq_single i
      · intro j hj hji
        rw [integral_inner_of_indep ((hX j hj).integrable (by norm_num))
          ((hX i hi).integrable (by norm_num)) (hindep hj hi hji), hmean i hi]
        simp
      · simp [hi]
    · intro j hj
      exact memLp_integrable_inner (hX j hj) (hX i hi)
  · intro i hi
    exact integrable_finset_sum _ fun j hj => memLp_integrable_inner (hX j hj) (hX i hi)

def normalizedSum (X : ℕ → Ω → H) (n : ℕ) (ω : Ω) : H :=
  (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, X i ω

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] [IsProbabilityMeasure μ] in
theorem normalizedSum_memLp (X : ℕ → Ω → H) (hX : ∀ i, MemLp (X i) 2 μ) (n : ℕ) :
    MemLp (normalizedSum X n) 2 μ := by
  exact (memLp_finset_sum _ fun i _ => hX i).const_smul _

theorem normalizedSum_secondMoment (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {n : ℕ} (hn : n ≠ 0) :
    (∫ ω, ‖normalizedSum X n ω‖ ^ 2 ∂μ) = ∫ ω, ‖X 0 ω‖ ^ 2 ∂μ := by
  have hXi (i : ℕ) : MemLp (X i) 2 μ := (hident i).memLp_iff.mpr hX
  have hmeani (i : ℕ) : ∫ ω, X i ω ∂μ = 0 := (hident i).integral_eq.trans hmean
  have hsecond (i : ℕ) : (∫ ω, ‖X i ω‖ ^ 2 ∂μ) = ∫ ω, ‖X 0 ω‖ ^ 2 ∂μ :=
    ((hident i).comp (by fun_prop : Measurable (fun x : H => ‖x‖ ^ 2))).integral_eq
  have hsum := integral_norm_sq_sum (Finset.range n) X (fun i _ => hXi i)
    (fun i _ => hmeani i) (fun _ _ _ _ hij => hindep.indepFun hij)
  simp_rw [normalizedSum, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    mul_pow]
  rw [integral_const_mul, hsum]
  simp_rw [hsecond]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hn), one_mul]

theorem normalizedSum_secondMoment_le (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    (∫ ω, ‖normalizedSum X n ω‖ ^ 2 ∂μ) ≤ ∫ ω, ‖X 0 ω‖ ^ 2 ∂μ := by
  by_cases hn : n = 0
  · subst n
    simpa [normalizedSum] using integral_nonneg (fun ω => sq_nonneg ‖X 0 ω‖)
  · exact (normalizedSum_secondMoment X hX hmean hindep hident hn).le

theorem normalizedSum_linear_secondMoment_le (X : ℕ → Ω → H) (hX : MemLp (X 0) 2 μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (A : H →L[ℝ] H) (n : ℕ) :
    (∫ ω, ‖A (normalizedSum X n ω)‖ ^ 2 ∂μ) ≤ ∫ ω, ‖A (X 0 ω)‖ ^ 2 ∂μ := by
  have hAX : MemLp (fun ω => A (X 0 ω)) 2 μ := hX.of_le_mul
    (A.continuous.comp_aestronglyMeasurable hX.1)
    (Eventually.of_forall fun ω => A.le_opNorm (X 0 ω))
  have hmeanA : (∫ ω, A (X 0 ω) ∂μ) = 0 := by
    rw [A.integral_comp_comm (hX.integrable (by norm_num)), hmean, map_zero]
  have hAindep : iIndepFun (fun i ω => A (X i ω)) μ :=
    hindep.comp (fun _ => A) (fun _ => A.continuous.measurable)
  have hAident (i : ℕ) : IdentDistrib (fun ω => A (X i ω))
      (fun ω => A (X 0 ω)) μ μ := (hident i).comp A.continuous.measurable
  simpa only [normalizedSum, map_smul, map_sum] using
    normalizedSum_secondMoment_le (fun i ω => A (X i ω)) hAX hmeanA hAindep hAident n

end Thesis.DayAhead.HilbertCLTMoments
