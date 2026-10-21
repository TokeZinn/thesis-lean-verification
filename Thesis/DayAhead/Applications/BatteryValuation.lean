import Thesis.DayAhead.Applications.BatteryControl
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Lemmas

/-! # Current battery scaling and cycle-budget results

The general finite grids below supplement the numerical 400 MWh grid in
`BatteryControl`. The scaling theorem acts on the actual feasibility constraints
and objective, for arbitrary finite grids and hourly price functions that are
non-decreasing only on their declared interval domains, as in the thesis; the
globally monotone versions are kept as corollaries. The Lagrangian theorem does
not require convexity or finiteness.
-/

noncomputable section
namespace Thesis.DayAhead.BatteryValuation

open scoped BigOperators
open BatteryControl

abbrev Schedule (n : ℕ) := Fin n → ℝ

def stored {n : ℕ} (start : ℝ) (a : Schedule n) (k : ℕ) : ℝ :=
  start + ∑ h ∈ Finset.univ.filter (fun h : Fin n => h.val < k), a h

/-- Original label: `defn:battery-schedule-set`. -/
def Feasible {n : ℕ} (G R : Finset ℝ) (η : Efficiency) (start stop : ℝ)
    (domain : Fin n → Set ℝ) (a : Schedule n) : Prop :=
  (∀ h, a h ∈ R) ∧ (∀ h : Fin n, stored start a (h.val + 1) ∈ G) ∧
    stored start a n = stop ∧ ∀ h, gridEnergy η (a h) ∈ domain h

theorem feasible_finite {n : ℕ} (G R : Finset ℝ) (η : Efficiency) (start stop : ℝ)
    (domain : Fin n → Set ℝ) : {a | Feasible G R η start stop domain a}.Finite := by
  apply (Set.Finite.pi' (fun _ : Fin n => R.finite_toSet)).subset
  intro a ha
  exact ha.1

def scale {n : ℕ} (α : ℝ) (a : Schedule n) : Schedule n := fun h => α * a h

def scaledGrid (α : ℝ) (G : Finset ℝ) : Finset ℝ := G.image (fun q => α * q)

theorem gridEnergy_scale (η : Efficiency) {α : ℝ} (hα : 0 < α) (r : ℝ) :
    gridEnergy η (α * r) = α * gridEnergy η r := by
  by_cases hr : r < 0
  · rw [gridEnergy_of_discharge η (mul_neg_of_pos_of_neg hα hr),
      gridEnergy_of_discharge η hr]
    ring
  · have hr' := le_of_not_gt hr
    rw [gridEnergy_of_charge η (mul_nonneg hα.le hr'), gridEnergy_of_charge η hr']
    ring

theorem stored_scale {n : ℕ} (α start : ℝ) (a : Schedule n) (k : ℕ) :
    stored (α * start) (scale α a) k = α * stored start a k := by
  simp only [stored, scale, mul_add, Finset.mul_sum]

theorem rescale_mem_grid {α q : ℝ} (hα : α ≠ 0) (G : Finset ℝ)
    (hq : q ∈ scaledGrid α G) : α⁻¹ * q ∈ G := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  simpa [← mul_assoc, hα] using hr

/-- Every feasible enlarged schedule rescales to a feasible original one.
The interval and zero assumptions on each price domain are essential. -/
theorem feasible_rescale {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (start stop : ℝ) (domain : Fin n → Set ℝ) (α : ℝ) (hα : 1 < α)
    (hd : ∀ h, Convex ℝ (domain h)) (hz : ∀ h, 0 ∈ domain h)
    (a : Schedule n)
    (ha : Feasible (scaledGrid α G) (scaledGrid α R) η (α * start) (α * stop)
      domain a) : Feasible G R η start stop domain (scale α⁻¹ a) := by
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hαne := ne_of_gt hαpos
  have hinv : 0 < α⁻¹ := inv_pos.mpr hαpos
  have hinvle : α⁻¹ ≤ 1 := (inv_le_one₀ hαpos).mpr hα.le
  have hstored (k : ℕ) : stored start (scale α⁻¹ a) k =
      α⁻¹ * stored (α * start) a k := by
    simpa [← mul_assoc, hαne] using stored_scale α⁻¹ (α * start) a k
  refine ⟨fun h => rescale_mem_grid hαne R (ha.1 h), ?_, ?_, ?_⟩
  · intro h
    rw [hstored]
    exact rescale_mem_grid hαne G (ha.2.1 h)
  · rw [hstored, ha.2.2.1]
    simp [hαne]
  · intro h
    rw [scale, gridEnergy_scale η hinv]
    have hmem := hd h (hz h) (ha.2.2.2 h)
      (sub_nonneg.mpr hinvle) hinv.le (sub_add_cancel 1 α⁻¹)
    simpa only [smul_eq_mul, mul_zero, zero_add] using hmem

/-- Original label: `defn:battery-value-functions`, objective for any horizon. -/
def payoff {n : ℕ} (η : Efficiency) (cost : ℝ) (P : Fin n → ℝ → ℝ)
    (a : Schedule n) : ℝ :=
  ∑ h, (-gridEnergy η (a h) * P h (gridEnergy η (a h)) - cost * |a h|)

/-- A nonempty feasible transition attains its plug-in value for arbitrary
finite grids, without any continuity assumption on its price functions. -/
theorem exists_optimal_schedule {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ) (P : Fin n → ℝ → ℝ)
    (hne : ∃ a, Feasible G R η start stop domain a) :
    ∃ a, Feasible G R η start stop domain a ∧
      ∀ b, Feasible G R η start stop domain b → payoff η cost P b ≤ payoff η cost P a :=
  Set.exists_max_image _ _ (feasible_finite G R η start stop domain) hne

/-- The hourly cash comparison of the thesis proof, with the price function only
non-decreasing on its declared interval domain `D`: the comparison involves the two
feasible points `q = τ(Δq̃_h)` and `α q = τ(Δq_h)` of `D` and nothing else. The
sign split on `q` is exactly the thesis's two cases. -/
theorem cash_scale_le_of_monotoneOn (P : ℝ → ℝ) (D : Set ℝ) (hP : MonotoneOn P D)
    (q α : ℝ) (hα : 1 ≤ α) (hqD : q ∈ D) (haD : α * q ∈ D) :
    -(α * q) * P (α * q) ≤ α * (-q * P q) := by
  have hα0 : 0 ≤ α := zero_le_one.trans hα
  by_cases hq : 0 ≤ q
  · have hqq : q ≤ α * q := by nlinarith
    have h := mul_le_mul_of_nonpos_left (hP hqD haD hqq)
      (neg_nonpos.mpr (mul_nonneg hα0 hq))
    nlinarith
  · have hq' := le_of_not_ge hq
    have hqq : α * q ≤ q := by nlinarith
    have h := mul_le_mul_of_nonneg_left (hP haD hqD hqq)
      (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hα0 hq'))
    nlinarith

/-- Globally monotone special case of `cash_scale_le_of_monotoneOn`. -/
theorem monotone_cash_scale (P : ℝ → ℝ) (hP : Monotone P)
    (q α : ℝ) (hα : 1 ≤ α) : -(α * q) * P (α * q) ≤ α * (-q * P q) :=
  cash_scale_le_of_monotoneOn P Set.univ (hP.monotoneOn _) q α hα (Set.mem_univ _)
    (Set.mem_univ _)

/-- Original label: `prop:battery-sublinear-scaling`, schedule inequality.
Thesis proof, hourly inequality: for a schedule `a` whose grid energies lie in the
declared interval domains, and whose `α`-scaled grid energies do too, compare the two
feasible interval points, split by sign, cancel the positively homogeneous throughput
cost `λ|·|`, then sum over the hours. -/
theorem payoff_scale_le_of_monotoneOn {n : ℕ} (η : Efficiency) (cost : ℝ)
    (P : Fin n → ℝ → ℝ) (domain : Fin n → Set ℝ)
    (hP : ∀ h, MonotoneOn (P h) (domain h))
    (a : Schedule n) (α : ℝ) (hα : 1 < α)
    (ha : ∀ h, gridEnergy η (a h) ∈ domain h)
    (hlarge : ∀ h, gridEnergy η (scale α a h) ∈ domain h) :
    payoff η cost P (scale α a) ≤ α * payoff η cost P a := by
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  simp only [payoff, scale, gridEnergy_scale η hαpos, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  rw [abs_mul, abs_of_pos hαpos]
  have hdom : α * gridEnergy η (a h) ∈ domain h := by
    simpa only [scale, gridEnergy_scale η hαpos] using hlarge h
  have hcash := cash_scale_le_of_monotoneOn (P h) (domain h) (hP h)
    (gridEnergy η (a h)) α hα.le (ha h) hdom
  nlinarith

/-- Special case of `payoff_scale_le_of_monotoneOn` under global monotonicity of every
hourly price function (kept for downstream users); not the mapped proof of
`prop:battery-sublinear-scaling`. -/
theorem payoff_scale_le {n : ℕ} (η : Efficiency) (cost : ℝ)
    (P : Fin n → ℝ → ℝ) (hP : ∀ h, Monotone (P h))
    (a : Schedule n) (α : ℝ) (hα : 1 < α) :
    payoff η cost P (scale α a) ≤ α * payoff η cost P a :=
  payoff_scale_le_of_monotoneOn η cost P (fun _ => Set.univ)
    (fun h => (hP h).monotoneOn _) a α hα (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _)

/-- Original label: `prop:battery-sublinear-scaling`.
Thesis proof, for arbitrary finite state and increment grids `G`, `R` and hourly price
functions that are non-decreasing on interval domains containing `0`: rescale the
enlarged feasible schedule by `α⁻¹` (interval convexity and `0 ∈ domain` give its
feasibility for the original grids), bound its payoff by the hourly sign comparison,
and conclude with the attained small-grid maximum. -/
theorem optimalValue_scale_le_of_monotoneOn {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ)
    (P : Fin n → ℝ → ℝ) (hP : ∀ h, MonotoneOn (P h) (domain h))
    (hd : ∀ h, Convex ℝ (domain h)) (hz : ∀ h, 0 ∈ domain h)
    (α : ℝ) (hα : 1 < α) (aLarge aSmall : Schedule n)
    (hlarge : Feasible (scaledGrid α G) (scaledGrid α R) η
      (α * start) (α * stop) domain aLarge)
    (hsmallmax : ∀ a, Feasible G R η start stop domain a →
      payoff η cost P a ≤ payoff η cost P aSmall) :
    payoff η cost P aLarge ≤ α * payoff η cost P aSmall := by
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hαne := ne_of_gt hαpos
  have hfeasible := feasible_rescale G R η start stop domain α hα hd hz aLarge hlarge
  have hcancel : scale α (scale α⁻¹ aLarge) = aLarge := by
    funext h
    simp [scale, hαne]
  have hdom : ∀ h, gridEnergy η (scale α (scale α⁻¹ aLarge) h) ∈ domain h := by
    rw [hcancel]
    exact hlarge.2.2.2
  have hscale := payoff_scale_le_of_monotoneOn η cost P domain hP (scale α⁻¹ aLarge) α hα
    hfeasible.2.2.2 hdom
  rw [hcancel] at hscale
  exact hscale.trans (mul_le_mul_of_nonneg_left (hsmallmax _ hfeasible) hαpos.le)

/-- Original label: `prop:battery-sublinear-scaling`.
The proposition as stated: if the enlarged feasible set is non-empty, then the original
feasible set is non-empty (by rescaling), its maximum is attained, and every enlarged
schedule is bounded by `α` times that maximum. -/
theorem sublinear_scaling_of_monotoneOn {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ)
    (P : Fin n → ℝ → ℝ) (hP : ∀ h, MonotoneOn (P h) (domain h))
    (hd : ∀ h, Convex ℝ (domain h)) (hz : ∀ h, 0 ∈ domain h)
    (α : ℝ) (hα : 1 < α)
    (hne : ∃ a, Feasible (scaledGrid α G) (scaledGrid α R) η
      (α * start) (α * stop) domain a) :
    ∃ aSmall, Feasible G R η start stop domain aSmall ∧
      (∀ a, Feasible G R η start stop domain a →
        payoff η cost P a ≤ payoff η cost P aSmall) ∧
      ∀ aLarge, Feasible (scaledGrid α G) (scaledGrid α R) η
          (α * start) (α * stop) domain aLarge →
        payoff η cost P aLarge ≤ α * payoff η cost P aSmall := by
  obtain ⟨a, ha⟩ := hne
  have hsmall := feasible_rescale G R η start stop domain α hα hd hz a ha
  obtain ⟨b, hb, hmax⟩ := exists_optimal_schedule G R η cost start stop domain P ⟨_, hsmall⟩
  exact ⟨b, hb, hmax, fun aLarge hlarge =>
    optimalValue_scale_le_of_monotoneOn G R η cost start stop domain P hP hd hz α hα
      aLarge b hlarge hmax⟩

/-- Special case of `optimalValue_scale_le_of_monotoneOn` under global monotonicity of
every hourly price function (kept for downstream users); not the mapped proof of
`prop:battery-sublinear-scaling`. -/
theorem optimalValue_scale_le {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ)
    (P : Fin n → ℝ → ℝ) (hP : ∀ h, Monotone (P h))
    (hd : ∀ h, Convex ℝ (domain h)) (hz : ∀ h, 0 ∈ domain h)
    (α : ℝ) (hα : 1 < α) (aLarge aSmall : Schedule n)
    (hlarge : Feasible (scaledGrid α G) (scaledGrid α R) η
      (α * start) (α * stop) domain aLarge)
    (hsmallmax : ∀ a, Feasible G R η start stop domain a →
      payoff η cost P a ≤ payoff η cost P aSmall) :
    payoff η cost P aLarge ≤ α * payoff η cost P aSmall :=
  optimalValue_scale_le_of_monotoneOn G R η cost start stop domain P
    (fun h => (hP h).monotoneOn _) hd hz α hα aLarge aSmall hlarge hsmallmax

/-- Original label: `prop:everett-lagrangian-separation`.
No convexity, compactness, or duality-gap assumption is needed. -/
theorem everett_lagrangian_separation {X : Type*} (R T : X → ℝ)
    (cost : ℝ) (hcost : 0 ≤ cost) (selected : X)
    (hmax : ∀ x, R x - cost * T x ≤ R selected - cost * T selected)
    (x : X) (hx : T x ≤ T selected) : R x ≤ R selected := by
  have h := hmax x
  have hcost := mul_le_mul_of_nonneg_left hx hcost
  linarith

end Thesis.DayAhead.BatteryValuation
