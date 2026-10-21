import Thesis.Intraday.Applications.Mandate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-! # Gaussian mandate law and natural information

The source's Gaussian inputs and natural filtration are explicit, as are
denominator positivity and the joint sign-reflection law. These hypotheses
are derived from the iid standard-normal assumptions, rather than postulated
as a substitute for them.
-/

noncomputable section
namespace Thesis.Intraday.MandateGaussian
open scoped BigOperators
open MeasureTheory ProbabilityTheory Mandate

abbrev Noise (K : ℕ) := Fin K → ℝ

def gaussianLaw (K : ℕ) : Measure (Noise K) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (K : ℕ) : IsProbabilityMeasure (gaussianLaw K) := by
  unfold gaussianLaw
  infer_instance

def process {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (TV : ℝ) (xi : Fin K → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  walk TV (fun j => xi j ω) k

theorem measurable_process {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (TV : ℝ) (xi : Fin K → Ω → ℝ) (hxi : ∀ j, Measurable (xi j)) (k : ℕ) :
    Measurable (process TV xi k) := by
  unfold process walk totalVariation
  fun_prop

/-- Original label: `defn:se-mandate`.
The actual natural filtration of the source's finite checkpoint process.
Gaussian inputs below supply its iid standard-normal probability law. -/
def information {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (TV : ℝ) (xi : Fin K → Ω → ℝ) (hxi : ∀ j, Measurable (xi j)) :
    Filtration (Fin (K + 1)) ‹MeasurableSpace Ω› :=
  Filtration.natural (fun k : Fin (K + 1) => process TV xi k.val)
    (fun k => (measurable_process TV xi hxi k.val).stronglyMeasurable)

theorem process_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (TV : ℝ) (xi : Fin K → Ω → ℝ) (hxi : ∀ j, Measurable (xi j)) :
    StronglyAdapted (information TV xi hxi)
      (fun k : Fin (K + 1) => process TV xi k.val) :=
  Filtration.stronglyAdapted_natural _

structure GaussianInput (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (K : ℕ) where
  noise : Fin K → Ω → ℝ
  measurable_noise : ∀ j, Measurable (noise j)
  independent : iIndepFun noise μ
  normal_law : ∀ j, HasLaw (noise j) (gaussianReal 0 1) μ

theorem GaussianInput.joint_law {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℕ} (g : GaussianInput Ω μ K) :
    HasLaw (fun ω j => g.noise j ω) (gaussianLaw K) μ := by
  refine ⟨(measurable_pi_lambda _ g.measurable_noise).aemeasurable, ?_⟩
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun j => (g.normal_law j).aemeasurable)).1
    g.independent]
  simp only [gaussianLaw, (g.normal_law _).map_eq]

theorem GaussianInput.denominator_pos_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {K : ℕ} (g : GaussianInput Ω μ K) (hK : 0 < K) :
    ∀ᵐ ω ∂μ, 0 < totalVariation (fun j => g.noise j ω) := by
  let j : Fin K := ⟨0, hK⟩
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have hn : ∀ᵐ ω ∂μ, g.noise j ω ≠ 0 := by
    apply ae_of_ae_map (p := fun x : ℝ => x ≠ 0) (g.normal_law j).aemeasurable
    rw [(g.normal_law j).map_eq]
    exact Measure.ae_ne _ 0
  filter_upwards [hn] with ω hω
  exact lt_of_lt_of_le (abs_pos.mpr hω)
    (Finset.single_le_sum (fun i _ => abs_nonneg (g.noise i ω)) (Finset.mem_univ j))

def reflection {K : ℕ} (j : Fin K) : Noise K ≃ᵐ Noise K where
  toFun := fun xi => reflect xi j
  invFun := fun xi => reflect xi j
  left_inv := by intro xi; funext i; by_cases h : i = j <;> simp [reflect, h]
  right_inv := by intro xi; funext i; by_cases h : i = j <;> simp [reflect, h]
  measurable_toFun := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun xi : Noise K => if i = j then -xi i else xi i)
    by_cases h : i = j <;> simp only [h, ↓reduceIte] <;> fun_prop
  measurable_invFun := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun xi : Noise K => if i = j then -xi i else xi i)
    by_cases h : i = j <;> simp only [h, ↓reduceIte] <;> fun_prop

theorem reflection_preserves_gaussian {K : ℕ} (j : Fin K) :
    MeasurePreserving (reflection j) (gaussianLaw K) (gaussianLaw K) := by
  have hc (i : Fin K) : MeasurePreserving (fun x : ℝ => if i = j then -x else x)
      (gaussianReal 0 1) (gaussianReal 0 1) := by
    by_cases h : i = j
    · simp only [h, ↓reduceIte]
      refine ⟨measurable_neg, ?_⟩
      simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
    · simpa only [h, ↓reduceIte] using (MeasurePreserving.id (gaussianReal 0 1))
  simpa only [reflection, reflect, gaussianLaw] using
    measurePreserving_pi (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1) hc

theorem walk_bound_all {K : ℕ} (TV : ℝ) (hTV : 0 ≤ TV) (xi : Noise K) (k : ℕ) :
    |walk TV xi k| ≤ TV := by
  by_cases hs : totalVariation xi = 0
  · simpa [walk, hs] using hTV
  · exact walk_bound TV hTV xi (lt_of_le_of_ne (totalVariation_nonneg xi) (Ne.symm hs)) k

theorem process_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {K : ℕ} (TV : ℝ) (hTV : 0 ≤ TV) (xi : Fin K → Ω → ℝ)
    (hxi : ∀ j, Measurable (xi j)) (k : ℕ) : Integrable (process TV xi k) μ := by
  apply Integrable.of_bound (measurable_process TV xi hxi k).aestronglyMeasurable TV
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [process, Real.norm_eq_abs] using walk_bound_all TV hTV (fun j => xi j ω) k

theorem walk_succ_sub {K : ℕ} (TV : ℝ) (xi : Noise K) (j : Fin K) :
    walk TV xi (j.val + 1) - walk TV xi j.val = increment TV xi j := by
  have hset : Finset.univ.filter (fun i : Fin K => i.val < j.val + 1) =
      insert j (Finset.univ.filter (fun i : Fin K => i.val < j.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases he : i = j
      · exact Or.inl he
      · right
        have : i.val ≠ j.val := fun h => he (Fin.ext h)
        omega
    · rintro (rfl | hi) <;> omega
  have hnot : j ∉ Finset.univ.filter (fun i : Fin K => i.val < j.val) := by simp
  simp only [walk, hset, Finset.sum_insert hnot, increment]
  ring

theorem GaussianInput.total_variation_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {K : ℕ} (g : GaussianInput Ω μ K) (hK : 0 < K)
    (TV : ℝ) (hTV : 0 ≤ TV) :
    ∀ᵐ ω ∂μ, ∑ j : Fin K,
      |process TV g.noise (j.val + 1) ω - process TV g.noise j.val ω| = TV := by
  filter_upwards [g.denominator_pos_ae hK] with ω hω
  simpa only [process, walk_succ_sub] using
    total_variation_normalised TV hTV (fun j => g.noise j ω) (ne_of_gt hω)

def informationNat {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (TV : ℝ) (xi : Fin K → Ω → ℝ) (hxi : ∀ j, Measurable (xi j)) :
    Filtration ℕ ‹MeasurableSpace Ω› :=
  Filtration.natural (process TV xi)
    (fun k => (measurable_process TV xi hxi k).stronglyMeasurable)

theorem measurable_walk_invariants {K : ℕ} (TV : ℝ) (j : Fin K) (k : ℕ)
    (hk : k ≤ j.val) :
    Measurable[MeasurableSpace.invariants (reflection j)] (fun xi => walk TV xi k) := by
  refine MeasurableSpace.measurable_invariants_dom.2 ⟨?_, ?_⟩
  · exact measurable_process TV (fun i (xi : Noise K) => xi i)
      (fun i => measurable_pi_apply i) k
  · intro s _
    have he : (fun xi => walk TV xi k) ∘ reflection j = fun xi => walk TV xi k := by
      funext xi
      exact reflection_preserves_past TV xi j k hk
    rw [he]

theorem informationNat_le_invariants {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (TV : ℝ) (xi : Fin K → Ω → ℝ) (hxi : ∀ i, Measurable (xi i)) (j : Fin K) :
    informationNat TV xi hxi j.val ≤
      (MeasurableSpace.invariants (reflection j)).comap (fun ω i => xi i ω) := by
  change (⨆ k ≤ j.val, MeasurableSpace.comap (process TV xi k) _) ≤ _
  refine iSup₂_le fun k hk => ?_
  have h := MeasurableSpace.comap_mono (g := fun ω i => xi i ω)
    (measurable_iff_comap_le.1 (measurable_walk_invariants TV j k hk))
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, process] using h

theorem GaussianInput.setIntegral_increment_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℕ} (g : GaussianInput Ω μ K)
    (TV : ℝ) (j : Fin K) (s : Set Ω)
    (hs : MeasurableSet[informationNat TV g.noise g.measurable_noise j.val] s) :
    ∫ ω in s, increment TV (fun i => g.noise i ω) j ∂μ = 0 := by
  obtain ⟨t, ht, he⟩ := informationNat_le_invariants TV g.noise g.measurable_noise j s hs
  let f : Noise K → ℝ := t.indicator (fun xi => increment TV xi j)
  have hfm : Measurable f := by
    apply Measurable.indicator _ ht.1
    unfold increment totalVariation
    fun_prop
  have hodd (xi : Noise K) : f (reflection j xi) = -f xi := by
    have hinv : reflection j xi ∈ t ↔ xi ∈ t := by
      change xi ∈ (reflection j) ⁻¹' t ↔ xi ∈ t
      rw [ht.2]
    by_cases hx : xi ∈ t
    · simp only [f, Set.indicator_of_mem hx, Set.indicator_of_mem (hinv.mpr hx)]
      exact reflection_increment TV xi j
    · simp only [f, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (mt hinv.mp hx), neg_zero]
  have hz := reflection_mean_zero (gaussianLaw K) (reflection j)
    (reflection_preserves_gaussian j) f hodd
  have hc := g.joint_law.integral_comp hfm.aestronglyMeasurable
  simp only [Function.comp_def] at hc
  have heq : (fun ω => f (fun i => g.noise i ω)) =
      s.indicator (fun ω => increment TV (fun i => g.noise i ω) j) := by
    rw [← he]
    rfl
  rw [heq, integral_indicator ((informationNat TV g.noise g.measurable_noise).le j.val s hs)]
    at hc
  exact hc.trans hz

theorem walk_constant_after {K : ℕ} (TV : ℝ) (xi : Noise K) (k : ℕ) (hk : K ≤ k) :
    walk TV xi k = walk TV xi K := by
  have hf (n : ℕ) (hn : K ≤ n) :
      Finset.univ.filter (fun i : Fin K => i.val < n) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    exact i.isLt.trans_le hn
  simp only [walk, hf k hk, hf K le_rfl]

theorem GaussianInput.martingale_nat {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℕ} (g : GaussianInput Ω μ K)
    (TV : ℝ) (hTV : 0 ≤ TV) :
    Martingale (process TV g.noise) (informationNat TV g.noise g.measurable_noise) μ := by
  apply martingale_of_setIntegral_eq_succ
    (Filtration.stronglyAdapted_natural _)
    (process_integrable TV hTV g.noise g.measurable_noise)
  intro k s hs
  by_cases hk : k < K
  · let j : Fin K := ⟨k, hk⟩
    have hz := g.setIntegral_increment_zero TV j s hs
    have heq : (fun ω => increment TV (fun i => g.noise i ω) j) =
        fun ω => process TV g.noise (k + 1) ω - process TV g.noise k ω := by
      funext ω
      exact (walk_succ_sub TV (fun i => g.noise i ω) j).symm
    rw [heq, integral_sub
      (process_integrable TV hTV g.noise g.measurable_noise (k + 1)).integrableOn
      (process_integrable TV hTV g.noise g.measurable_noise k).integrableOn] at hz
    linarith
  · have heq : process TV g.noise k = process TV g.noise (k + 1) := by
      funext ω
      exact (walk_constant_after TV _ k (Nat.le_of_not_gt hk)).trans
        (walk_constant_after TV _ (k + 1) (by omega)).symm
    rw [heq]

theorem information_eq_nat {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (TV : ℝ) (xi : Fin K → Ω → ℝ) (hxi : ∀ j, Measurable (xi j)) (k : Fin (K + 1)) :
    information TV xi hxi k = informationNat TV xi hxi k.val := by
  change (⨆ j : Fin (K + 1), ⨆ (_ : j ≤ k),
      MeasurableSpace.comap (process TV xi j.val) _) =
    ⨆ j : ℕ, ⨆ (_ : j ≤ k.val), MeasurableSpace.comap (process TV xi j) _
  apply le_antisymm
  · exact iSup₂_le fun j hj => le_iSup₂_of_le j.val hj le_rfl
  · refine iSup₂_le fun j hj => ?_
    exact le_iSup₂_of_le (⟨j, lt_of_le_of_lt hj k.isLt⟩ : Fin (K + 1)) hj le_rfl

/-- Original label: `prop:mandate-martingale`.
The complete natural-filtration martingale clause for arbitrary iid
standard-normal inputs, not just the canonical Gaussian sample space.
`GaussianInput.total_variation_ae` and `walk_bound_all` give the other clauses. -/
theorem GaussianInput.martingale {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℕ} (g : GaussianInput Ω μ K)
    (TV : ℝ) (hTV : 0 ≤ TV) :
    Martingale (fun k : Fin (K + 1) => process TV g.noise k.val)
      (information TV g.noise g.measurable_noise) μ := by
  refine ⟨process_stronglyAdapted TV g.noise g.measurable_noise, fun i j hij => ?_⟩
  rw [information_eq_nat]
  exact (g.martingale_nat TV hTV).condExp_ae_eq hij

/-- The source proposition as a conjunction: exact total variation almost
surely, a uniformly bounded path, and its actual natural-filtration martingale.
Both strict source positivity hypotheses are stronger than those needed here. -/
theorem GaussianInput.specification {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℕ} (g : GaussianInput Ω μ K)
    (hK : 0 < K) (TV : ℝ) (hTV : 0 ≤ TV) :
    (∀ᵐ ω ∂μ, ∑ j : Fin K,
      |process TV g.noise (j.val + 1) ω - process TV g.noise j.val ω| = TV) ∧
    (∀ (k : Fin (K + 1)) (ω : Ω), |process TV g.noise k.val ω| ≤ TV) ∧
    Martingale (fun k : Fin (K + 1) => process TV g.noise k.val)
      (information TV g.noise g.measurable_noise) μ := by
  exact ⟨g.total_variation_ae hK TV hTV,
    (fun k ω => walk_bound_all TV hTV (fun j => g.noise j ω) k.val), g.martingale TV hTV⟩

end Thesis.Intraday.MandateGaussian
