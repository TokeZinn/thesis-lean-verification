import Thesis.DayAhead.ForecastingImpact.GreedyTree

/-! # Greedy Hilbert trees inside the actual squared-loss boosting recursion

Chapter 5, lines 264–279 and 412–421. Each fitted tree uses the retained rows
and finite retained-feature histogram cuts for that round. The line search
uses the specified training rows and the true residual, while the tree is
fitted to the negative gradient (twice the residual). The shrinkage update
does not increase training squared loss when its factor lies in [0, 1].
Validation-based checkpoint selection and random subsample generation are
separate algorithms; no assertion about held-out generalization is made.
-/

noncomputable section
namespace Thesis.DayAhead.GreedyBoosting

open RecursiveTrees GreedyTree BoostingLoss
open scoped BigOperators

variable {ι H : Type*} {p : ℕ}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

structure Settings where
  minimum : ℕ
  maxLeaves : ℕ
  maxDepth : ℕ
  threshold : ℝ
  minimum_pos : 0 < minimum
  maxLeaves_pos : 0 < maxLeaves
  threshold_nonneg : 0 ≤ threshold

def fitDirection (cfg : Settings) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (fitRows : Finset ι)
    (current : (Fin p → ℝ) → H) : Tree p H :=
  train cfg.minimum cfg.maxLeaves cfg.maxDepth cfg.threshold cuts x
    (fun i => pseudoResidual (y i) (current (x i))) fitRows

theorem fitDirection_spec (cfg : Settings) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (fitRows : Finset ι)
    (current : (Fin p → ℝ) → H) (hrows : cfg.minimum ≤ fitRows.card) :
    let t := fitDirection cfg cuts x y fitRows current
    t.leafCount ≤ cfg.maxLeaves ∧ t.depth ≤ cfg.maxDepth ∧
      t.ValidOn Set.univ ∧ SplitsIn cuts t ∧
      FitsOn cfg.minimum x (fun i => (2 : ℝ) • (y i - current (x i))) fitRows t := by
  have h := train_spec cfg.minimum cfg.maxLeaves cfg.maxDepth cfg.threshold
    cfg.threshold_nonneg cfg.maxLeaves_pos cuts x
    (fun i => pseudoResidual (y i) (current (x i))) fitRows hrows
  refine ⟨h.2.1, h.2.2.1, ?_, ?_, ?_⟩
  · exact train_validOn cfg.minimum cfg.maxLeaves cfg.maxDepth cfg.threshold
      cfg.threshold_nonneg cfg.minimum_pos cfg.maxLeaves_pos cuts x _ fitRows hrows
  · exact train_splitsIn cfg.minimum cfg.maxLeaves cfg.maxDepth cfg.threshold cuts x _ fitRows
  · simpa only [fitDirection, pseudoResidual_eq] using h.1

/-- Moving any fraction of the way to a squared-loss line-search minimizer
does not increase the loss. This also covers a zero fitted direction. -/
theorem lineLoss_shrink_le (s : Finset ι) (residual direction : ι → H)
    (ν : ℝ) (hν : 0 ≤ ν) (hν1 : ν ≤ 1) :
    lineLoss s residual direction (ν * lineSearchStep s residual direction) ≤
      lineLoss s residual direction 0 := by
  let γ := lineSearchStep s residual direction
  let a := ∑ i ∈ s, ‖direction i‖ ^ 2
  have ha : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbest := lineSearchStep_minimal s residual direction 0
  rw [lineLoss_quadratic, lineLoss_quadratic] at hbest ⊢
  have hscaled := mul_le_mul_of_nonneg_left hbest hν
  have hcorrection : 0 ≤ ν * (1 - ν) * (γ ^ 2 * a) :=
    mul_nonneg (mul_nonneg hν (sub_nonneg.mpr hν1)) (mul_nonneg (sq_nonneg γ) ha)
  dsimp [γ, a] at hcorrection
  nlinarith

def update (current direction : (Fin p → ℝ) → H) (step : ℝ) : (Fin p → ℝ) → H :=
  fun z => current z + step • direction z

theorem empiricalRisk_update (s : Finset ι) (x : ι → Fin p → ℝ) (y : ι → H)
    (current direction : (Fin p → ℝ) → H) (γ : ℝ) :
    empiricalRisk s x y (update current direction γ) = (s.card : ℝ)⁻¹ *
      lineLoss s (fun i => y i - current (x i)) (fun i => direction (x i)) γ := by
  unfold empiricalRisk squaredLoss update lineLoss
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sub_add_eq_sub_sub]

def roundStep (cfg : Settings) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (fitRows lineRows : Finset ι)
    (current : (Fin p → ℝ) → H) : ℝ :=
  lineSearchStep lineRows (fun i => y i - current (x i))
    (fun i => (fitDirection cfg cuts x y fitRows current).eval (x i))

def roundUpdate (cfg : Settings) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (fitRows lineRows : Finset ι)
    (ν : ℝ) (current : (Fin p → ℝ) → H) : (Fin p → ℝ) → H :=
  update current (fitDirection cfg cuts x y fitRows current).eval
    (ν * roundStep cfg cuts x y fitRows lineRows current)

theorem roundUpdate_nonincrease (cfg : Settings) (cuts : Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (fitRows lineRows : Finset ι)
    (ν : ℝ) (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (current : (Fin p → ℝ) → H) :
    empiricalRisk lineRows x y (roundUpdate cfg cuts x y fitRows lineRows ν current) ≤
      empiricalRisk lineRows x y current := by
  unfold roundUpdate
  rw [empiricalRisk_update]
  have h := lineLoss_shrink_le lineRows (fun i => y i - current (x i))
    (fun i => (fitDirection cfg cuts x y fitRows current).eval (x i)) ν hν hν1
  have hs := mul_le_mul_of_nonneg_left h (show 0 ≤ (lineRows.card : ℝ)⁻¹ by positivity)
  simpa only [roundStep, lineLoss, zero_smul, sub_zero, empiricalRisk, squaredLoss] using hs

def boost (cfg : Settings) (cuts : ℕ → Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (fitRows : ℕ → Finset ι) (lineRows : Finset ι)
    (ν : ℝ) (initial : (Fin p → ℝ) → H) : ℕ → (Fin p → ℝ) → H
  | 0 => initial
  | n + 1 => roundUpdate cfg (cuts n) x y (fitRows n) lineRows ν
      (boost cfg cuts x y fitRows lineRows ν initial n)

theorem boost_risk_antitone (cfg : Settings) (cuts : ℕ → Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (fitRows : ℕ → Finset ι) (lineRows : Finset ι)
    (ν : ℝ) (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (initial : (Fin p → ℝ) → H) :
    Antitone (fun n =>
      empiricalRisk lineRows x y (boost cfg cuts x y fitRows lineRows ν initial n)) := by
  apply antitone_nat_of_succ_le
  intro n
  exact roundUpdate_nonincrease cfg (cuts n) x y (fitRows n) lineRows ν hν hν1 _

/-- The stored directions are fitted to each current ensemble, not supplied
independently in advance. Their sum is the exact resulting prediction. -/
theorem boost_eq_sum (cfg : Settings) (cuts : ℕ → Finset (Fin p × ℝ))
    (x : ι → Fin p → ℝ) (y : ι → H) (fitRows : ℕ → Finset ι) (lineRows : Finset ι)
    (ν : ℝ) (initial : (Fin p → ℝ) → H) (n : ℕ) (z : Fin p → ℝ) :
    boost cfg cuts x y fitRows lineRows ν initial n z = initial z +
      ∑ k ∈ Finset.range n,
        (ν * roundStep cfg (cuts k) x y (fitRows k) lineRows
          (boost cfg cuts x y fitRows lineRows ν initial k)) •
        (fitDirection cfg (cuts k) x y (fitRows k)
          (boost cfg cuts x y fitRows lineRows ν initial k)).eval z := by
  induction n with
  | zero => simp [boost]
  | succ n ih =>
    simpa only [boost, roundUpdate, update, Finset.sum_range_succ, add_assoc] using
      congrArg (fun value => value +
        (ν * roundStep cfg (cuts n) x y (fitRows n) lineRows
          (boost cfg cuts x y fitRows lineRows ν initial n)) •
        (fitDirection cfg (cuts n) x y (fitRows n)
          (boost cfg cuts x y fitRows lineRows ν initial n)).eval z) ih

end Thesis.DayAhead.GreedyBoosting
