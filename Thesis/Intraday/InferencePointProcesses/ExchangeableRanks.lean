import Thesis.Intraday.InferencePointProcesses.StrictRanks
import Thesis.Intraday.InferencePointProcesses.EnsembleCalibration
import Mathlib.Probability.IdentDistrib
import Mathlib.Order.Interval.Finset.Fin

/-! # Expected functions of strict ranks under exchangeability

Current `prop:midrank-coverage-expectations`: finite-dimensional exchangeability
is expressed by invariance in law under every permutation. For almost-surely
tie-free samples, the expected value of every function of one member's rank
is its uniform finite average. No independence between delivery days is used.
-/

noncomputable section
namespace Thesis.Intraday.ExchangeableRanks
open MeasureTheory ProbabilityTheory StrictRanks
open scoped BigOperators

theorem measurable_rank {N : ℕ} (i : Fin N) :
    Measurable (fun values : Fin N → ℝ => rank values i) := by
  have hm : Measurable (fun values : Fin N → ℝ => (below values i).card) := by
    have he : (fun values : Fin N → ℝ => (below values i).card) =
        fun values => ∑ j : Fin N, if values j < values i then (1 : ℕ) else 0 := by
      funext values
      simp [below]
    rw [he]
    apply Finset.measurable_sum
    intro j _
    exact measurable_const.ite (measurableSet_lt (measurable_pi_apply j)
      (measurable_pi_apply i)) measurable_const
  apply measurable_to_countable'
  intro r
  have he : (fun values : Fin N → ℝ => rank values i) ⁻¹' {r} =
      {values | (below values i).card = r.val} := by
    ext values
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff, rank, Set.mem_setOf_eq]
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

def SymmetricLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (values : Ω → Fin N → ℝ) : Prop :=
  ∀ permutation : Equiv.Perm (Fin N),
    IdentDistrib values (fun ω => values ω ∘ permutation) μ μ

theorem rank_identDistrib {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (values : Ω → Fin N → ℝ) (hsymm : SymmetricLaw μ values) (i j : Fin N) :
    IdentDistrib (fun ω => rank (values ω) i) (fun ω => rank (values ω) j) μ μ := by
  have h := (hsymm (Equiv.swap i j)).comp (measurable_rank i)
  change IdentDistrib (fun ω => rank (values ω) i)
    (fun ω => rank (values ω ∘ Equiv.swap i j) i) μ μ at h
  simpa only [rank_precomp, Equiv.swap_apply_left] using h

theorem rank_function_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (values : Ω → Fin N → ℝ) (hm : Measurable values)
    (i : Fin N) (f : Fin N → ℝ) : Integrable (fun ω => f (rank (values ω) i)) μ := by
  refine Integrable.of_bound
    (((measurable_of_countable f).comp ((measurable_rank i).comp hm)).aestronglyMeasurable)
    (∑ j, |f j|) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ _)

/-- A full finite uniform-rank expectation theorem. The reference member can
be any index; only permutation invariance and absence of ties are required. -/
theorem expected_rank_function {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (values : Ω → Fin N → ℝ) (hm : Measurable values)
    (hsymm : SymmetricLaw μ values) (hties : ∀ᵐ ω ∂μ, Function.Injective (values ω))
    (i : Fin N) (f : Fin N → ℝ) :
    ∫ ω, f (rank (values ω) i) ∂μ = (∑ j, f j) / N := by
  have he : ∀ j : Fin N, (∫ ω, f (rank (values ω) j) ∂μ) =
      ∫ ω, f (rank (values ω) i) ∂μ := by
    intro j
    exact ((rank_identDistrib μ values hsymm j i).comp (measurable_of_countable f)).integral_eq
  have hpoint : ∀ᵐ ω ∂μ, (∑ j, f (rank (values ω) j)) = ∑ j, f j :=
    hties.mono fun ω hω => rank_sum (values ω) hω f
  have hi := integral_eq_const hpoint
  rw [integral_finset_sum _ (fun j _ => rank_function_integrable μ values hm j f)] at hi
  simp_rw [he] at hi
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hi
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  apply (eq_div_iff hn).mpr
  nlinarith

theorem midrank_eq_strict_rank {B : ℕ} (values : Fin (B + 1) → ℝ)
    (hvalues : Function.Injective values) :
    EnsembleRanks.midrank (values 0) (fun j : Fin B => values j.succ) =
      ((rank values 0).val : ℝ) / B := by
  have ht : ∀ j : Fin B, values j.succ ≠ values 0 := by
    intro j he
    have := hvalues he
    exact Fin.succ_ne_zero j this
  have he : ((below values 0).card : ℝ) =
      ∑ j : Fin (B + 1), if values j < values 0 then (1 : ℝ) else 0 := by
    simp [below]
  rw [Fin.sum_univ_succ] at he
  simp only [lt_self_iff_false, ↓reduceIte, zero_add] at he
  simp only [EnsembleRanks.midrank, ht, ↓reduceIte, add_zero]
  exact congrArg (fun v : ℝ => v / B) he.symm

/-- The thesis's actual tie-adjusted statistic has precisely its displayed
central expectation under its exchangeability and no-ties hypotheses. -/
theorem expected_central_midrank {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {B : ℕ} (values : Ω → Fin (B + 1) → ℝ)
    (hm : Measurable values) (hsymm : SymmetricLaw μ values)
    (hties : ∀ᵐ ω ∂μ, Function.Injective (values ω)) (alpha : ℝ) :
    ∫ ω, (if EnsembleCalibration.central alpha
      (EnsembleRanks.midrank (values ω 0) (fun j : Fin B => values ω j.succ))
      then (1 : ℝ) else 0) ∂μ = EnsembleCalibration.centralReference B alpha := by
  have he := expected_rank_function μ values hm hsymm hties (0 : Fin (B + 1))
    (fun r => if EnsembleCalibration.central alpha ((r.val : ℝ) / B) then (1 : ℝ) else 0)
  change (∫ ω, (if EnsembleCalibration.central alpha
    (((rank (values ω) 0).val : ℝ) / B) then (1 : ℝ) else 0) ∂μ) = _ at he
  have he' : (∫ ω, (if EnsembleCalibration.central alpha
      (((rank (values ω) 0).val : ℝ) / B) then (1 : ℝ) else 0) ∂μ) =
      EnsembleCalibration.centralReference B alpha := by
    simpa only [EnsembleCalibration.centralReference, Nat.cast_add, Nat.cast_one] using he
  rw [← he']
  apply integral_congr_ae
  filter_upwards [hties] with ω hω
  rw [midrank_eq_strict_rank _ hω]

theorem upper_reference_count (B : ℕ) (hB : 0 < B) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    (∑ j : Fin (B + 1), if (j.val : ℝ) / B ≤ 1 - alpha then (1 : ℝ) else 0) =
      (Nat.floor ((B : ℝ) * (1 - alpha)) : ℝ) + 1 := by
  have hbr : (0 : ℝ) < B := by exact_mod_cast hB
  have ht0 : 0 ≤ (B : ℝ) * (1-alpha) :=
    mul_nonneg hbr.le (sub_nonneg.mpr ha1)
  have htB : (B : ℝ) * (1-alpha) ≤ B := by nlinarith
  have hf : Nat.floor ((B : ℝ) * (1-alpha)) < B+1 :=
    Nat.lt_succ_of_le (Nat.floor_le_of_le htB)
  let last : Fin (B + 1) := ⟨Nat.floor ((B : ℝ) * (1-alpha)), hf⟩
  have hset : (Finset.univ.filter fun j : Fin (B + 1) => (j.val : ℝ) / B ≤ 1-alpha) =
      Finset.Iic last := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    rw [div_le_iff₀ hbr]
    change (j.val : ℝ) ≤ (1-alpha) * B ↔ j.val ≤ Nat.floor ((B : ℝ) * (1-alpha))
    simpa only [mul_comm] using (Nat.le_floor_iff ht0).symm
  have hcard : (∑ j : Fin (B + 1), if (j.val : ℝ) / B ≤ 1-alpha then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun j : Fin (B + 1) => (j.val : ℝ) / B ≤ 1-alpha).card : ℝ) := by
    simp
  rw [hcard, hset, Fin.card_Iic]
  simp only [Nat.cast_add, Nat.cast_one]
  rfl

theorem expected_upper_midrank {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {B : ℕ} (hB : 0 < B) (values : Ω → Fin (B + 1) → ℝ)
    (hm : Measurable values) (hsymm : SymmetricLaw μ values)
    (hties : ∀ᵐ ω ∂μ, Function.Injective (values ω)) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    ∫ ω, (if EnsembleRanks.midrank (values ω 0) (fun j : Fin B => values ω j.succ) ≤
        1-alpha then (1 : ℝ) else 0) ∂μ =
      ((Nat.floor ((B : ℝ) * (1-alpha)) : ℝ) + 1) / (B + 1) := by
  have he := expected_rank_function μ values hm hsymm hties (0 : Fin (B + 1))
    (fun r => if (r.val : ℝ) / B ≤ 1-alpha then (1 : ℝ) else 0)
  rw [upper_reference_count B hB alpha ha0 ha1] at he
  have h := integral_congr_ae (hties.mono fun ω hω =>
    congrArg (fun u : ℝ => if u ≤ 1-alpha then (1 : ℝ) else 0)
      (midrank_eq_strict_rank (values ω) hω))
  exact h.trans (by simpa only [Nat.cast_add, Nat.cast_one] using he)

/-- Original label: `prop:midrank-coverage-expectations`.
Averaging over days requires no independence between days. -/
theorem expected_central_fraction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {B D : ℕ} (hD : 0 < D)
    (values : Fin D → Ω → Fin (B + 1) → ℝ) (hm : ∀ d, Measurable (values d))
    (hsymm : ∀ d, SymmetricLaw μ (values d))
    (hties : ∀ d, ∀ᵐ ω ∂μ, Function.Injective (values d ω)) (alpha : ℝ) :
    ∫ ω, EnsembleCalibration.centralFraction alpha
      (fun d => EnsembleRanks.midrank (values d ω 0) (fun j : Fin B => values d ω j.succ)) ∂μ =
      EnsembleCalibration.centralReference B alpha := by
  have hi : ∀ d : Fin D, Integrable (fun ω => if EnsembleCalibration.central alpha
      (EnsembleRanks.midrank (values d ω 0) (fun j : Fin B => values d ω j.succ))
      then (1 : ℝ) else 0) μ := by
    intro d
    have hr := rank_function_integrable μ (values d) (hm d) (0 : Fin (B + 1))
      (fun r => if EnsembleCalibration.central alpha ((r.val : ℝ) / B) then (1 : ℝ) else 0)
    apply hr.congr
    filter_upwards [hties d] with ω hω
    rw [midrank_eq_strict_rank _ hω]
  unfold EnsembleCalibration.centralFraction
  rw [integral_div, integral_finset_sum _ (fun d _ => hi d)]
  simp_rw [expected_central_midrank μ _ (hm _) (hsymm _) (hties _) alpha]
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  simp [hd]

theorem expected_upper_fraction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {B D : ℕ} (hB : 0 < B) (hD : 0 < D)
    (values : Fin D → Ω → Fin (B + 1) → ℝ) (hm : ∀ d, Measurable (values d))
    (hsymm : ∀ d, SymmetricLaw μ (values d))
    (hties : ∀ d, ∀ᵐ ω ∂μ, Function.Injective (values d ω)) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    ∫ ω, EnsembleCalibration.upperFraction alpha
      (fun d => EnsembleRanks.midrank (values d ω 0) (fun j : Fin B => values d ω j.succ)) ∂μ =
      ((Nat.floor ((B : ℝ) * (1-alpha)) : ℝ) + 1) / (B + 1) := by
  have hi : ∀ d : Fin D, Integrable (fun ω => if
      EnsembleRanks.midrank (values d ω 0) (fun j : Fin B => values d ω j.succ) ≤ 1-alpha
      then (1 : ℝ) else 0) μ := by
    intro d
    have hr := rank_function_integrable μ (values d) (hm d) (0 : Fin (B + 1))
      (fun r => if (r.val : ℝ) / B ≤ 1-alpha then (1 : ℝ) else 0)
    apply hr.congr
    filter_upwards [hties d] with ω hω
    rw [midrank_eq_strict_rank _ hω]
  unfold EnsembleCalibration.upperFraction
  rw [integral_div, integral_finset_sum _ (fun d _ => hi d)]
  simp_rw [expected_upper_midrank μ hB _ (hm _) (hsymm _) (hties _) alpha ha0 ha1]
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  simp [hd]

theorem lower_reference_count (B : ℕ) (hB : 0 < B) (a : ℝ)
    (ha1 : a ≤ 1) :
    (∑ j : Fin (B + 1), if (j.val : ℝ) / B < a then (1 : ℝ) else 0) =
      (Nat.ceil ((B : ℝ) * a) : ℝ) := by
  have hbr : (0 : ℝ) < B := by exact_mod_cast hB
  have htB : (B : ℝ) * a ≤ B := by nlinarith
  have hf : Nat.ceil ((B : ℝ) * a) < B+1 :=
    Nat.lt_succ_of_le (Nat.ceil_le.mpr htB)
  let last : Fin (B + 1) := ⟨Nat.ceil ((B : ℝ) * a), hf⟩
  have hset : (Finset.univ.filter fun j : Fin (B + 1) => (j.val : ℝ) / B < a) =
      Finset.Iio last := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    rw [div_lt_iff₀ hbr]
    change (j.val : ℝ) < a * B ↔ j.val < Nat.ceil ((B : ℝ) * a)
    simpa only [mul_comm] using (Nat.lt_ceil).symm
  have hcard : (∑ j : Fin (B + 1), if (j.val : ℝ) / B < a then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun j : Fin (B + 1) => (j.val : ℝ) / B < a).card : ℝ) := by simp
  rw [hcard, hset, Fin.card_Iio]

theorem central_reference_formula (B : ℕ) (hB : 0 < B) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    EnsembleCalibration.centralReference B alpha =
      ((Nat.floor ((B : ℝ) * (1-alpha/2)) : ℝ) + 1 -
        (Nat.ceil ((B : ℝ) * (alpha/2)) : ℝ)) / (B + 1) := by
  have he : ∀ u : ℝ, (if EnsembleCalibration.central alpha u then (1 : ℝ) else 0) =
      (if u ≤ 1-alpha/2 then (1 : ℝ) else 0) - (if u < alpha/2 then (1 : ℝ) else 0) := by
    intro u
    by_cases hl : u < alpha/2
    · have hlow : ¬alpha/2 ≤ u := not_le.mpr hl
      have hu : u ≤ 1-alpha/2 := by linarith
      simp [EnsembleCalibration.central, hl, hlow, hu]
    · have hlow : alpha/2 ≤ u := le_of_not_gt hl
      by_cases hu : u ≤ 1-alpha/2 <;> simp [EnsembleCalibration.central, hl, hlow, hu]
  unfold EnsembleCalibration.centralReference
  simp_rw [he, Finset.sum_sub_distrib]
  rw [upper_reference_count B hB (alpha/2) (by linarith) (by linarith),
    lower_reference_count B hB (alpha/2) (by linarith)]

end Thesis.Intraday.ExchangeableRanks
