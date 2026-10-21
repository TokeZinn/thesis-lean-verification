import Thesis.DayAhead.Applications.BatteryValuation

/-! # Finite-grid battery selection and interval-domain scaling

The definition `defn:battery-value-functions` permits arbitrary finite state and
increment grids; the lexicographically first maximiser, the plug-in and realised
values, and the transition value error are defined here.  The source proof of
`prop:battery-sublinear-scaling`, which compares prices only at two feasible
points of each declared interval and assumes no extension of the price function
to a globally monotone one, now lives on the primary module `BatteryValuation`
(`cash_scale_le_of_monotoneOn`, `payoff_scale_le_of_monotoneOn`,
`optimalValue_scale_le_of_monotoneOn`, `sublinear_scaling_of_monotoneOn`); its
former names are kept here as aliases.
-/

noncomputable section
namespace Thesis.DayAhead.BatterySourceScope

open scoped BigOperators
open BatteryControl BatteryValuation

abbrev OrderedSchedule (n : ℕ) := Lex (Schedule n)

def schedules {n : ℕ} (G R : Finset ℝ) (η : Efficiency) (start stop : ℝ)
    (domain : Fin n → Set ℝ) : Finset (OrderedSchedule n) :=
  (feasible_finite G R η start stop domain).toFinset

@[simp] theorem mem_schedules {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (start stop : ℝ) (domain : Fin n → Set ℝ) (a : OrderedSchedule n) :
    a ∈ schedules G R η start stop domain ↔ Feasible G R η start stop domain a := by
  exact (feasible_finite G R η start stop domain).mem_toFinset

def maximizers {n : ℕ} (s : Finset (OrderedSchedule n))
    (f : OrderedSchedule n → ℝ) : Finset (OrderedSchedule n) :=
  s.filter fun a => ∀ b ∈ s, f b ≤ f a

theorem maximizers_nonempty {n : ℕ} {s : Finset (OrderedSchedule n)}
    (hs : s.Nonempty) (f : OrderedSchedule n → ℝ) : (maximizers s f).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s f hs
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, hmax⟩⟩

def select {n : ℕ} (s : Finset (OrderedSchedule n)) (hs : s.Nonempty)
    (f : OrderedSchedule n → ℝ) : OrderedSchedule n :=
  (maximizers s f).min' (maximizers_nonempty hs f)

theorem select_mem_maximizers {n : ℕ} (s : Finset (OrderedSchedule n))
    (hs : s.Nonempty) (f : OrderedSchedule n → ℝ) :
    select s hs f ∈ maximizers s f := Finset.min'_mem _ _

theorem select_mem {n : ℕ} (s : Finset (OrderedSchedule n))
    (hs : s.Nonempty) (f : OrderedSchedule n → ℝ) : select s hs f ∈ s :=
  (Finset.mem_filter.mp (select_mem_maximizers s hs f)).1

theorem select_max {n : ℕ} (s : Finset (OrderedSchedule n))
    (hs : s.Nonempty) (f : OrderedSchedule n → ℝ)
    {b : OrderedSchedule n} (hb : b ∈ s) : f b ≤ f (select s hs f) :=
  (Finset.mem_filter.mp (select_mem_maximizers s hs f)).2 b hb

theorem select_lex_first {n : ℕ} (s : Finset (OrderedSchedule n))
    (hs : s.Nonempty) (f : OrderedSchedule n → ℝ)
    {b : OrderedSchedule n} (hb : b ∈ s) (hbmax : ∀ a ∈ s, f a ≤ f b) :
    select s hs f ≤ b := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hbmax⟩)

/-- The chronological lexicographically first maximizer, for arbitrary finite
grids and arbitrary horizon (the source uses `n = 24`). -/
def predictedAction {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ) (P : Fin n → ℝ → ℝ)
    (hne : (schedules G R η start stop domain).Nonempty) : OrderedSchedule n :=
  select (schedules G R η start stop domain) hne (BatteryValuation.payoff η cost P)

theorem predictedAction_optimal {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ) (P : Fin n → ℝ → ℝ)
    (hne : (schedules G R η start stop domain).Nonempty) :
    Feasible G R η start stop domain (predictedAction G R η cost start stop domain P hne) ∧
    ∀ a, Feasible G R η start stop domain a →
      BatteryValuation.payoff η cost P a ≤
        BatteryValuation.payoff η cost P (predictedAction G R η cost start stop domain P hne) := by
  refine ⟨(mem_schedules ..).mp (select_mem _ _ _), ?_⟩
  intro a ha
  exact select_max _ _ _ ((mem_schedules ..).mpr ha)

theorem predictedAction_lex_first {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ) (P : Fin n → ℝ → ℝ)
    (hne : (schedules G R η start stop domain).Nonempty) (b : OrderedSchedule n)
    (hb : Feasible G R η start stop domain b)
    (hbmax : ∀ a, Feasible G R η start stop domain a →
      BatteryValuation.payoff η cost P a ≤ BatteryValuation.payoff η cost P b) :
    predictedAction G R η cost start stop domain P hne ≤ b :=
  select_lex_first _ _ _ ((mem_schedules ..).mpr hb)
    (fun a ha => hbmax a ((mem_schedules ..).mp ha))

def unpenalizedValue {n : ℕ} (η : Efficiency) (P : Fin n → ℝ → ℝ)
    (a : Schedule n) : ℝ := ∑ h, -gridEnergy η (a h) * P h (gridEnergy η (a h))

def totalVariation {n : ℕ} (a : Schedule n) : ℝ := ∑ h, |a h|

def plugInValue {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ) (P : Fin n → ℝ → ℝ)
    (hne : (schedules G R η start stop domain).Nonempty) : ℝ :=
  BatteryValuation.payoff η cost P (predictedAction G R η cost start stop domain P hne)

/-- Evaluation on realized curves has its own feasibility check, as in the
source definition; forecast-domain feasibility is insufficient. -/
def realizedValue {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ) (P : Fin n → ℝ → ℝ)
    (a : Schedule n) (_hreal : Feasible G R η start stop domain a) : ℝ :=
  BatteryValuation.payoff η cost P a

theorem realizedValue_eq_cash_sub_throughput {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (domain : Fin n → Set ℝ) (P : Fin n → ℝ → ℝ)
    (a : Schedule n) (hreal : Feasible G R η start stop domain a) :
    realizedValue G R η cost start stop domain P a hreal =
      unpenalizedValue η P a - cost * totalVariation a := by
  simp only [realizedValue, BatteryValuation.payoff, unpenalizedValue, totalVariation,
    Finset.sum_sub_distrib, Finset.mul_sum]

def transitionValueError {n : ℕ} (η : Efficiency) (cost : ℝ)
    (realized predicted : Fin n → ℝ → ℝ) (a : Schedule n) : ℝ :=
  BatteryValuation.payoff η cost realized a - BatteryValuation.payoff η cost predicted a

def realizedSelectedValue {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (forecastDomain realizedDomain : Fin n → Set ℝ)
    (predicted realized : Fin n → ℝ → ℝ)
    (hne : (schedules G R η start stop forecastDomain).Nonempty)
    (hreal : Feasible G R η start stop realizedDomain
      (predictedAction G R η cost start stop forecastDomain predicted hne)) : ℝ :=
  realizedValue G R η cost start stop realizedDomain realized
    (predictedAction G R η cost start stop forecastDomain predicted hne) hreal

theorem selected_transition_error {n : ℕ} (G R : Finset ℝ) (η : Efficiency)
    (cost start stop : ℝ) (forecastDomain realizedDomain : Fin n → Set ℝ)
    (predicted realized : Fin n → ℝ → ℝ)
    (hne : (schedules G R η start stop forecastDomain).Nonempty)
    (hreal : Feasible G R η start stop realizedDomain
      (predictedAction G R η cost start stop forecastDomain predicted hne)) :
    realizedSelectedValue G R η cost start stop forecastDomain realizedDomain
        predicted realized hne hreal -
      plugInValue G R η cost start stop forecastDomain predicted hne =
    transitionValueError η cost realized predicted
      (predictedAction G R η cost start stop forecastDomain predicted hne) := rfl

theorem transitionValueError_eq {n : ℕ} (η : Efficiency) (cost : ℝ)
    (realized predicted : Fin n → ℝ → ℝ) (a : Schedule n) :
    transitionValueError η cost realized predicted a =
      ∑ h, -gridEnergy η (a h) *
        (realized h (gridEnergy η (a h)) - predicted h (gridEnergy η (a h))) := by
  simp only [transitionValueError, BatteryValuation.payoff, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Moved to `BatteryValuation` as `cash_scale_le_of_monotoneOn`; kept as an alias. -/
alias monotoneOn_cash_scale := BatteryValuation.cash_scale_le_of_monotoneOn

/-- Moved to `BatteryValuation` as `payoff_scale_le_of_monotoneOn`; kept as an alias. -/
alias payoff_scale_le_on := BatteryValuation.payoff_scale_le_of_monotoneOn

/-- Moved to `BatteryValuation` as `optimalValue_scale_le_of_monotoneOn` (the labelled proof
of `prop:battery-sublinear-scaling`); kept as an alias. -/
alias optimalValue_scale_le_on := BatteryValuation.optimalValue_scale_le_of_monotoneOn

/-- Moved to `BatteryValuation` as `sublinear_scaling_of_monotoneOn`; kept as an alias. -/
alias sublinear_scaling := BatteryValuation.sublinear_scaling_of_monotoneOn

end Thesis.DayAhead.BatterySourceScope
