import Thesis.Appendices.Analysis.SkorokhodRegularity
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # Time changes and uniform limits of regular paths

Regularity is preserved by increasing interval bijections. On a complete
state space it is also preserved by uniform limits; in particular the
supremum metric on regular paths is complete.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal UniformConvergence

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ} {X : Type*} [MetricSpace X] {f : ClosedInterval a b → X}

theorem isRightContinuousOnIcc_of_continuousWithinAt
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t) : IsRightContinuousOnIcc f := by
  intro t _ ε hε
  obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousWithinAt_iff.mp (hf t) ε hε
  refine ⟨δ, hδ, fun x htx hxt => hlocal htx.le ?_⟩
  change |(x : ℝ) - t| < δ
  rw [abs_of_pos (sub_pos.mpr htx)]
  linarith [(lt_min_iff.mp hxt).1]

theorem isLeftContinuousOnIcc_of_continuousWithinAt
    (hf : ∀ t, ContinuousWithinAt f (Iic t) t) : IsLeftContinuousOnIcc f := by
  intro t _ ε hε
  obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousWithinAt_iff.mp (hf t) ε hε
  refine ⟨δ, hδ, fun x htx hxt => hlocal hxt.le ?_⟩
  change |(x : ℝ) - t| < δ
  rw [abs_of_neg (sub_neg.mpr hxt)]
  linarith [(max_lt_iff.mp htx).2]

theorem hasLeftLimitsOnIcc_of_tendsto
    (hf : ∀ t, ∃ L, Tendsto f (𝓝[Iio t] t) (𝓝 L)) : HasLeftLimitsOnIcc f := by
  intro t _
  obtain ⟨L, hL⟩ := hf t
  refine ⟨L, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hlocal⟩ := Metric.tendsto_nhdsWithin_nhds.mp hL ε hε
  refine ⟨δ, hδ, fun x htx hxt => hlocal hxt ?_⟩
  change |(x : ℝ) - t| < δ
  rw [abs_of_neg (sub_neg.mpr hxt)]
  linarith [(max_lt_iff.mp htx).2]

theorem hasRightLimitsOnIcc_of_tendsto
    (hf : ∀ t, ∃ L, Tendsto f (𝓝[Ioi t] t) (𝓝 L)) : HasRightLimitsOnIcc f := by
  intro t _
  obtain ⟨L, hL⟩ := hf t
  refine ⟨L, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hlocal⟩ := Metric.tendsto_nhdsWithin_nhds.mp hL ε hε
  refine ⟨δ, hδ, fun x htx hxt => hlocal htx ?_⟩
  change |(x : ℝ) - t| < δ
  rw [abs_of_pos (sub_pos.mpr htx)]
  linarith [(lt_min_iff.mp hxt).1]

theorem isOneSidedRegularPath_comp {side : PathOrientation}
    (hf : IsOneSidedRegularPath side f) (e : IncreasingIntervalBijection a b) :
    IsOneSidedRegularPath side (fun t => f (e t)) := by
  cases side with
  | cadlag =>
      constructor
      · apply isRightContinuousOnIcc_of_continuousWithinAt
        intro t
        exact (hf.1.continuousWithinAt (e t)).comp e.continuous.continuousWithinAt
          (fun _ hx => e.strictMono.monotone hx)
      · apply hasLeftLimitsOnIcc_of_tendsto
        intro t
        obtain ⟨L, hL⟩ := hf.2.tendsto (e t)
        exact ⟨L, hL.comp (e.continuous.continuousWithinAt.tendsto_nhdsWithin
          (fun _ hx => e.strictMono hx))⟩
  | caglad =>
      constructor
      · apply isLeftContinuousOnIcc_of_continuousWithinAt
        intro t
        exact (hf.1.continuousWithinAt (e t)).comp e.continuous.continuousWithinAt
          (fun _ hx => e.strictMono.monotone hx)
      · apply hasRightLimitsOnIcc_of_tendsto
        intro t
        obtain ⟨L, hL⟩ := hf.2.tendsto (e t)
        exact ⟨L, hL.comp (e.continuous.continuousWithinAt.tendsto_nhdsWithin
          (fun _ hx => e.strictMono hx))⟩

def RegularPath.compTimeChange {side : PathOrientation} (f : RegularPath a b X side)
    (e : IncreasingIntervalBijection a b) : RegularPath a b X side :=
  ⟨fun t => f.val (e t), isOneSidedRegularPath_comp f.property e⟩

theorem cauchy_map_of_uniform_limit {α : Type*} {p : Filter α} [NeBot p]
    {F : ℕ → α → X} {g : α → X} (hF : TendstoUniformly F g atTop)
    (hlimits : ∀ n, ∃ L, Tendsto (F n) p (𝓝 L)) : Cauchy (p.map g) := by
  refine Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.mp hF (ε / 5) (by positivity)).exists
  obtain ⟨L, hL⟩ := hlimits n
  have hnear : ∀ᶠ x in p, dist (F n x) L < ε / 5 :=
    hL.eventually (Metric.ball_mem_nhds L (by positivity))
  refine ⟨g '' {x | dist (F n x) L < ε / 5}, ?_, ?_⟩
  · change g ⁻¹' (g '' {x | dist (F n x) L < ε / 5}) ∈ p
    filter_upwards [hnear] with x hx
    exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h1 := dist_triangle (g x) (F n x) (g y)
    have h2 := dist_triangle (F n x) L (g y)
    have h3 := dist_triangle L (F n y) (g y)
    rw [dist_comm L (F n y), dist_comm (F n y) (g y)] at h3
    dsimp only [mem_setOf_eq] at hx hy
    linarith [hn x, hn y]

theorem exists_limit_of_uniform_limit [CompleteSpace X] {α : Type*} {p : Filter α}
    {F : ℕ → α → X} {g : α → X} (x₀ : X) (hF : TendstoUniformly F g atTop)
    (hlimits : ∀ n, ∃ L, Tendsto (F n) p (𝓝 L)) :
    ∃ L, Tendsto g p (𝓝 L) := by
  rcases p.eq_or_neBot with rfl | hp
  · exact ⟨x₀, tendsto_bot⟩
  · exact cauchy_map_iff_exists_tendsto.mp (cauchy_map_of_uniform_limit hF hlimits)

theorem isOneSidedRegularPath_of_uniform_limit [CompleteSpace X] {side : PathOrientation}
    (F : ℕ → RegularPath a b X side) {g : ClosedInterval a b → X}
    (hF : TendstoUniformly (fun n => (F n).val) g atTop) : IsOneSidedRegularPath side g := by
  cases side with
  | cadlag =>
      constructor
      · apply isRightContinuousOnIcc_of_continuousWithinAt
        intro t
        exact hF.tendsto_of_eventually_tendsto
          (Eventually.of_forall fun n => (F n).property.1.continuousWithinAt t)
          (hF.tendsto_at t)
      · apply hasLeftLimitsOnIcc_of_tendsto
        intro t
        exact exists_limit_of_uniform_limit (g t) hF (fun n => (F n).property.2.tendsto t)
  | caglad =>
      constructor
      · apply isLeftContinuousOnIcc_of_continuousWithinAt
        intro t
        exact hF.tendsto_of_eventually_tendsto
          (Eventually.of_forall fun n => (F n).property.1.continuousWithinAt t)
          (hF.tendsto_at t)
      · apply hasRightLimitsOnIcc_of_tendsto
        intro t
        exact exists_limit_of_uniform_limit (g t) hF (fun n => (F n).property.2.tendsto t)

theorem supPathEDistance_tendsto_zero_iff {ι : Type*} {p : Filter ι}
    (F : ι → ClosedInterval a b → X) (g : ClosedInterval a b → X) :
    Tendsto (fun i => supPathEDistance (F i) g) p (𝓝 0) ↔ TendstoUniformly F g p := by
  constructor
  · intro h
    rw [EMetric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [h.eventually (gt_mem_nhds hε)] with i hi t
    rw [edist_comm]
    exact (edist_le_supPathEDistance (F i) g t).trans_lt hi
  · intro h
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [EMetric.tendstoUniformly_iff.mp h ε hε] with i hi
    rw [supPathEDistance_le_iff]
    intro t
    rw [edist_comm]
    exact (hi t).le

theorem regularPath_sup_complete [CompleteSpace X] (side : PathOrientation) :
    IsCompleteFor (fun f g : RegularPath a b X side => supPathEDistance f.val g.val) := by
  intro F hF
  let G : ℕ → ClosedInterval a b →ᵤ X := fun n => UniformFun.ofFun (F n).val
  have hG : CauchySeq G := by
    rw [EMetric.cauchySeq_iff]
    simpa only [G, UniformFun.edist_def, UniformFun.toFun_ofFun,
      ← supPathEDistance_eq_iSup] using hF
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hG
  have huniform : TendstoUniformly (fun n => (F n).val) (UniformFun.toFun g) atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.mp hg
  let limit : RegularPath a b X side :=
    ⟨UniformFun.toFun g, isOneSidedRegularPath_of_uniform_limit F huniform⟩
  refine ⟨limit, ?_⟩
  exact (convergesFor_iff_tendsto _ _ _).mpr
    ((supPathEDistance_tendsto_zero_iff _ _).mpr huniform)

end Thesis.Foundations.Preliminary.Analysis
