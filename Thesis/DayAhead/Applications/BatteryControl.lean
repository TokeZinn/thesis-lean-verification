import Mathlib.Order.PiLex
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # The current finite battery control problem

Applications chapter, lines 356–495 and 552–581. Internal energy changes have
51 possible values, and the 24-hour action space uses chronological lexicographic
order. Feasibility checks every stored-energy state and each price-curve domain.
The selected action is the lexicographically first actual maximizer. The
construction proves finite attainment; it does not certify archived solver runs.
-/

noncomputable section
namespace Thesis.DayAhead.BatteryControl

set_option maxRecDepth 2048

open Finset
open scoped BigOperators

structure Efficiency where
  charge : ℝ
  discharge : ℝ
  charge_pos : 0 < charge
  discharge_pos : 0 < discharge
  charge_le_one : charge ≤ 1
  discharge_le_one : discharge ≤ 1

def gridEnergy (η : Efficiency) (change : ℝ) : ℝ :=
  if change < 0 then η.discharge * change else change / η.charge

theorem gridEnergy_zero (η : Efficiency) : gridEnergy η 0 = 0 := by simp [gridEnergy]

theorem gridEnergy_of_charge (η : Efficiency) {change : ℝ} (h : 0 ≤ change) :
    gridEnergy η change = change / η.charge := if_neg (not_lt.mpr h)

theorem gridEnergy_of_discharge (η : Efficiency) {change : ℝ} (h : change < 0) :
    gridEnergy η change = η.discharge * change := if_pos h

theorem gridEnergy_pos_iff (η : Efficiency) (change : ℝ) :
    0 < gridEnergy η change ↔ 0 < change := by
  by_cases h : change < 0
  · rw [gridEnergy_of_discharge η h]
    have := mul_neg_of_pos_of_neg η.discharge_pos h
    constructor <;> intro hh <;> linarith
  · rw [gridEnergy_of_charge η (le_of_not_gt h)]
    exact div_pos_iff_of_pos_right η.charge_pos

theorem gridEnergy_parts (η : Efficiency) (change : ℝ) :
    gridEnergy η change = max change 0 / η.charge - η.discharge * max (-change) 0 := by
  by_cases h : change < 0
  · rw [gridEnergy_of_discharge η h, max_eq_right h.le, max_eq_left (by linarith)]
    ring
  · rw [gridEnergy_of_charge η (le_of_not_gt h), max_eq_left (le_of_not_gt h),
      max_eq_right (by linarith)]
    ring

def increment (a : Fin 51) : ℝ := 4 * (a.val : ℝ) - 100

theorem increment_bounds (a : Fin 51) : -100 ≤ increment a ∧ increment a ≤ 100 := by
  have h0 : (0 : ℝ) ≤ a.val := by positivity
  have h1 : (a.val : ℝ) ≤ 50 := by exact_mod_cast (show a.val ≤ 50 by omega)
  unfold increment
  constructor <;> linarith

theorem increment_strictMono : StrictMono increment := by
  intro a b hab
  have : (a.val : ℝ) < b.val := by exact_mod_cast hab
  unfold increment
  linarith

/-- Exactly `4 ℤ ∩ [-100,100]`, including both endpoints and idle. -/
theorem increment_range (r : ℝ) :
    (∃ a : Fin 51, increment a = r) ↔
      (∃ k : ℤ, r = 4 * (k : ℝ)) ∧ -100 ≤ r ∧ r ≤ 100 := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨⟨(a.val : ℤ) - 25, ?_⟩, increment_bounds a⟩
    simp only [increment, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
    ring
  · rintro ⟨⟨k, rfl⟩, hlo, hhi⟩
    have hklo : (-25 : ℤ) ≤ k := by
      have : (-25 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    have hkhi : k ≤ (25 : ℤ) := by
      have : (k : ℝ) ≤ 25 := by linarith
      exact_mod_cast this
    let a : Fin 51 := ⟨(k + 25).toNat, by omega⟩
    refine ⟨a, ?_⟩
    have ha : (a.val : ℤ) = k + 25 := Int.toNat_of_nonneg (by omega)
    have har : (a.val : ℝ) = (k : ℝ) + 25 := by exact_mod_cast ha
    unfold increment
    rw [har]
    ring

abbrev Action := Lex (Fin 24 → Fin 51)

def storageGrid : Finset ℝ := univ.image (fun i : Fin 101 => 4 * (i.val : ℝ))

theorem storageGrid_bounds {q : ℝ} (hq : q ∈ storageGrid) : 0 ≤ q ∧ q ≤ 400 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hq
  have hi : (i.val : ℝ) ≤ 100 := by exact_mod_cast (show i.val ≤ 100 by omega)
  constructor
  · positivity
  · linarith

def storedAfter (start : ℝ) (a : Action) (k : ℕ) : ℝ :=
  start + ∑ h ∈ (univ : Finset (Fin 24)).filter (fun h => h.val < k), increment (a h)

theorem storedAfter_zero (start : ℝ) (a : Action) : storedAfter start a 0 = start := by
  simp [storedAfter]

theorem storedAfter_full (start : ℝ) (a : Action) :
    storedAfter start a 24 = start + ∑ h, increment (a h) := by
  simp [storedAfter]

def feasible (η : Efficiency) (start stop : ℝ) (domain : Fin 24 → Set ℝ) : Finset Action := by
  classical
  exact univ.filter fun a =>
    (∀ h : Fin 24, storedAfter start a (h.val + 1) ∈ storageGrid) ∧
    storedAfter start a 24 = stop ∧
    ∀ h : Fin 24, gridEnergy η (increment (a h)) ∈ domain h

theorem mem_feasible (η : Efficiency) (start stop : ℝ) (domain : Fin 24 → Set ℝ)
    (a : Action) : a ∈ feasible η start stop domain ↔
      (∀ h : Fin 24, storedAfter start a (h.val + 1) ∈ storageGrid) ∧
      storedAfter start a 24 = stop ∧
      ∀ h : Fin 24, gridEnergy η (increment (a h)) ∈ domain h := by
  simp only [feasible, mem_filter, mem_univ, true_and]

def payoff (η : Efficiency) (cost : ℝ) (P : Fin 24 → ℝ → ℝ) (a : Action) : ℝ :=
  ∑ h, (-gridEnergy η (increment (a h)) * P h (gridEnergy η (increment (a h))) -
    cost * |increment (a h)|)

def maximizers (s : Finset Action) (f : Action → ℝ) : Finset Action :=
  s.filter fun a => ∀ b ∈ s, f b ≤ f a

theorem maximizers_nonempty {s : Finset Action} (hs : s.Nonempty) (f : Action → ℝ) :
    (maximizers s f).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image s f hs
  exact ⟨a, mem_filter.mpr ⟨ha, hmax⟩⟩

def select (s : Finset Action) (hs : s.Nonempty) (f : Action → ℝ) : Action :=
  (maximizers s f).min' (maximizers_nonempty hs f)

theorem select_mem_maximizers (s : Finset Action) (hs : s.Nonempty) (f : Action → ℝ) :
    select s hs f ∈ maximizers s f := min'_mem _ _

theorem select_mem (s : Finset Action) (hs : s.Nonempty) (f : Action → ℝ) :
    select s hs f ∈ s := (mem_filter.mp (select_mem_maximizers s hs f)).1

theorem select_max (s : Finset Action) (hs : s.Nonempty) (f : Action → ℝ)
    {b : Action} (hb : b ∈ s) : f b ≤ f (select s hs f) :=
  (mem_filter.mp (select_mem_maximizers s hs f)).2 b hb

theorem select_lex_first (s : Finset Action) (hs : s.Nonempty) (f : Action → ℝ)
    {b : Action} (hb : b ∈ s) (hbmax : ∀ a ∈ s, f a ≤ f b) : select s hs f ≤ b :=
  min'_le _ _ (mem_filter.mpr ⟨hb, hbmax⟩)

def predictedAction (η : Efficiency) (cost start stop : ℝ) (P : Fin 24 → ℝ → ℝ)
    (domain : Fin 24 → Set ℝ) (hne : (feasible η start stop domain).Nonempty) : Action :=
  select (feasible η start stop domain) hne (payoff η cost P)

theorem predictedAction_optimal (η : Efficiency) (cost start stop : ℝ)
    (P : Fin 24 → ℝ → ℝ) (domain : Fin 24 → Set ℝ)
    (hne : (feasible η start stop domain).Nonempty) :
    predictedAction η cost start stop P domain hne ∈ feasible η start stop domain ∧
    ∀ a ∈ feasible η start stop domain,
      payoff η cost P a ≤ payoff η cost P (predictedAction η cost start stop P domain hne) :=
  ⟨select_mem _ _ _, fun _ ha => select_max _ _ _ ha⟩

/-- Evaluation against realized curves requires a fresh domain check on the selected schedule. -/
def realizedPayoff (η : Efficiency) (cost : ℝ) (P : Fin 24 → ℝ → ℝ)
    (domain : Fin 24 → Set ℝ) (a : Action)
    (_hreal : ∀ h, gridEnergy η (increment (a h)) ∈ domain h) : ℝ := payoff η cost P a

theorem payoff_congr_on_submission (η : Efficiency) (cost : ℝ)
    (P R : Fin 24 → ℝ → ℝ) (a : Action)
    (h : ∀ j, P j (gridEnergy η (increment (a j))) = R j (gridEnergy η (increment (a j)))) :
    payoff η cost P a = payoff η cost R a := by
  unfold payoff
  simp_rw [h]

/-- Internal-throughput costs cancel when comparing the same selected schedule. -/
theorem payoff_forecast_error (η : Efficiency) (cost : ℝ)
    (P predicted : Fin 24 → ℝ → ℝ) (a : Action) :
    payoff η cost P a - payoff η cost predicted a =
      ∑ h, (-gridEnergy η (increment (a h)) *
        (P h (gridEnergy η (increment (a h))) -
          predicted h (gridEnergy η (increment (a h))))) := by
  simp only [payoff, ← sum_sub_distrib]
  apply sum_congr rfl
  intro h _
  ring

theorem net_internal_change (η : Efficiency) (start stop : ℝ) (domain : Fin 24 → Set ℝ)
    {a : Action} (ha : a ∈ feasible η start stop domain) :
    ∑ h, increment (a h) = stop - start := by
  have h := ((mem_feasible η start stop domain a).mp ha).2.1
  rw [storedAfter_full] at h
  linarith

def charged (a : Action) : ℝ := ∑ h, max (increment (a h)) 0
def discharged (a : Action) : ℝ := ∑ h, max (-increment (a h)) 0

theorem charged_sub_discharged (a : Action) :
    charged a - discharged a = ∑ h, increment (a h) := by
  simp only [charged, discharged, ← sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self]

theorem net_grid_withdrawal (η : Efficiency) (a : Action) :
    ∑ h, gridEnergy η (increment (a h)) = charged a / η.charge - η.discharge * discharged a := by
  simp only [gridEnergy_parts, sum_sub_distrib, sum_div, ← mul_sum, charged, discharged]

theorem payoff_common_shift (η : Efficiency) (cost c : ℝ) (P : Fin 24 → ℝ → ℝ)
    (a : Action) : payoff η cost (fun h q => P h q + c) a =
      payoff η cost P a - c * (charged a / η.charge - η.discharge * discharged a) := by
  rw [← net_grid_withdrawal]
  simp only [payoff, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro h _
  ring

/-- The source's upper bound on the extra cycling margin at the declared settings. -/
theorem illustrated_cycle_margin {buy sell : ℝ} (hbuy : 40 ≤ buy) (hsell : sell ≤ 80) :
    sell * (0.925 : ℝ) - buy / (0.925 : ℝ) - 2 * 25 ≤ -(712 / 37 : ℝ) := by
  norm_num
  linarith

end Thesis.DayAhead.BatteryControl
