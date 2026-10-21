import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! # The actual monotone bounded L² constraint

These are representative-independent classes on the restricted Lebesgue
interval. This module proves non-emptiness, convexity, closedness and the unique
nonexpansive Hilbert projection for this actual set. The right-continuous CDF
selector and Cramér isometry are proved in `CDFSelection`; conditional-law
identification is a separate kernel statement.
-/

noncomputable section
namespace Thesis.Foundations.Research.CDFConstraint

open Set MeasureTheory Filter Topology
open scoped ENNReal

def intervalMeasure (a b : ℝ) : Measure ℝ := volume.restrict (Icc a b)

/-- Original label: `defn:cdf-constraint-selection`.
The constraint part of the definition, with actual L² equivalence classes.
Endpoint values of the bounded monotone representative can be selected within
[0,1]; the a.e. equality identifies precisely the represented class. -/
def constraint (a b : ℝ) : Set (ℝ →₂[intervalMeasure a b] ℝ) :=
  {f | ∃ g : ℝ → ℝ, MonotoneOn g (Icc a b) ∧
    (∀ x ∈ Icc a b, 0 ≤ g x ∧ g x ≤ 1) ∧ g =ᵐ[intervalMeasure a b] f}

theorem zero_mem (a b : ℝ) : (0 : ℝ →₂[intervalMeasure a b] ℝ) ∈ constraint a b := by
  refine ⟨fun _ ↦ 0, fun _ _ _ _ _ ↦ le_rfl, ?_, ?_⟩
  · intro x hx
    exact ⟨le_rfl, zero_le_one⟩
  · exact (Lp.coeFn_zero ℝ 2 (intervalMeasure a b)).symm

/-- Original label: `prop:cdf-constraint-properties`.
Non-emptiness of the literal constraint set. -/
theorem nonempty (a b : ℝ) : (constraint a b).Nonempty := ⟨0, zero_mem a b⟩

/-- Original label: `prop:cdf-constraint-properties`.
Convexity of the actual monotone representative constraint, without assuming
closedness or defining it to be the closure of a smaller substitute. -/
theorem convex (a b : ℝ) : Convex ℝ (constraint a b) := by
  intro f hf h hh α β hα hβ hab
  rcases hf with ⟨g, hg, hgb, hgf⟩
  rcases hh with ⟨k, hk, hkb, hkh⟩
  refine ⟨fun x ↦ α * g x + β * k x, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hg hx hy hxy) hα)
      (mul_le_mul_of_nonneg_left (hk hx hy hxy) hβ)
  · intro x hx
    rcases hgb x hx with ⟨hg0, hg1⟩
    rcases hkb x hx with ⟨hk0, hk1⟩
    constructor
    · exact add_nonneg (mul_nonneg hα hg0) (mul_nonneg hβ hk0)
    · calc
        α * g x + β * k x ≤ α * 1 + β * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hg1 hα) (mul_le_mul_of_nonneg_left hk1 hβ)
        _ = 1 := by simpa using hab
  · filter_upwards [hgf, hkh, Lp.coeFn_smul α f, Lp.coeFn_smul β h,
      Lp.coeFn_add (α • f) (β • h)] with x hfg hhk hαf hβh hadd
    rw [hadd]
    change α * g x + β * k x = (α • f) x + (β • h) x
    rw [hαf, hβh]
    simp only [Pi.smul_apply, smul_eq_mul, hfg, hhk]

/-- Extend a bounded monotone function on an arbitrary subset, without
requiring that subset to be closed or contain either interval endpoint. -/
def monotoneExtension (f : ℝ → ℝ) (S : Set ℝ) (x : ℝ) : ℝ :=
  sSup (insert 0 (f '' (S ∩ Iic x)))

theorem monotoneExtension_properties {f : ℝ → ℝ} {S : Set ℝ}
    (hmono : MonotoneOn f S) (hb : ∀ x ∈ S, 0 ≤ f x ∧ f x ≤ 1) :
    Monotone (monotoneExtension f S) ∧
      (∀ x, 0 ≤ monotoneExtension f S x ∧ monotoneExtension f S x ≤ 1) ∧
      (∀ x ∈ S, monotoneExtension f S x = f x) := by
  have hbounded (x : ℝ) : BddAbove (insert 0 (f '' (S ∩ Iic x))) := by
    refine ⟨1, ?_⟩
    rintro z (rfl | ⟨y, hy, rfl⟩)
    · exact zero_le_one
    · exact (hb y hy.1).2
  have hnonempty (x : ℝ) : (insert 0 (f '' (S ∩ Iic x))).Nonempty :=
    ⟨0, Set.mem_insert _ _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply csSup_le (hnonempty x)
    intro z hz
    apply le_csSup (hbounded y)
    rcases hz with rfl | ⟨t, ht, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨t, ⟨ht.1, ht.2.trans hxy⟩, rfl⟩
  · intro x
    refine ⟨le_csSup (hbounded x) (Set.mem_insert _ _), csSup_le (hnonempty x) ?_⟩
    rintro z (rfl | ⟨y, hy, rfl⟩)
    · exact zero_le_one
    · exact (hb y hy.1).2
  · intro x hx
    apply le_antisymm
    · apply csSup_le (hnonempty x)
      rintro z (rfl | ⟨y, hy, rfl⟩)
      · exact (hb x hx).1
      · exact hmono hy.1 hx hy.2
    · exact le_csSup (hbounded x) (Set.mem_insert_of_mem _ ⟨x, ⟨hx, by simp⟩, rfl⟩)

/-- Original label: `defn:cdf-constraint-selection`.
The pointwise-bounded representative interface is exactly equivalent to the
source's a.e. bounds together with an arbitrary monotone representative.
Clamping changes no L² class and preserves monotonicity. -/
theorem mem_constraint_iff {a b : ℝ} (f : ℝ →₂[intervalMeasure a b] ℝ) :
    f ∈ constraint a b ↔
      (∀ᵐ x ∂intervalMeasure a b, 0 ≤ f x ∧ f x ≤ 1) ∧
        ∃ g : ℝ → ℝ, MonotoneOn g (Icc a b) ∧ g =ᵐ[intervalMeasure a b] f := by
  constructor
  · rintro ⟨g, hm, hb, he⟩
    refine ⟨?_, g, hm, he⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc, he] with x hx heq
    exact heq ▸ hb x hx
  · rintro ⟨hb, g, hm, he⟩
    refine ⟨fun x => max 0 (min (g x) 1), ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact max_le_max le_rfl (min_le_min (hm hx hy hxy) le_rfl)
    · intro x _
      exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    · filter_upwards [hb, he] with x hx heq
      simp only [heq, min_eq_left hx.2, max_eq_right hx.1]

/-- Original label: `prop:cdf-constraint-properties`, closedness in clause (i).
The proof uses a genuinely convergent L² subsequence and a bounded monotone
extension of its full-measure pointwise limit, rather than replacing the
source's constraint by its closure. -/
theorem isClosed (a b : ℝ) : IsClosed (constraint a b) := by
  apply IsSeqClosed.isClosed
  intro F f hF hconv
  have hrep (n : ℕ) : ∃ g : ℝ → ℝ, MonotoneOn g (Icc a b) ∧
      (∀ x ∈ Icc a b, 0 ≤ g x ∧ g x ≤ 1) ∧ g =ᵐ[intervalMeasure a b] F n := hF n
  choose g hmono hbounded heq using hrep
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂intervalMeasure a b, ∀ n, g n x = F n x := by
    simpa only [ae_all_iff] using heq
  have hlim : ∀ᵐ x ∂intervalMeasure a b,
      Tendsto (fun n => g (φ n) x) atTop (𝓝 (f x)) := by
    filter_upwards [hall, hφ] with x hx hφx
    simpa only [hx] using hφx
  let S : Set ℝ := {x | x ∈ Icc a b ∧
    Tendsto (fun n => g (φ n) x) atTop (𝓝 (f x))}
  have hS : ∀ᵐ x ∂intervalMeasure a b, x ∈ S := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hlim] with x hx hlimx
    exact ⟨hx, hlimx⟩
  have hfm : MonotoneOn (fun x => f x) S := by
    intro x hx y hy hxy
    exact le_of_tendsto_of_tendsto hx.2 hy.2
      (Filter.Eventually.of_forall (fun n => hmono (φ n) hx.1 hy.1 hxy))
  have hfb : ∀ x ∈ S, 0 ≤ f x ∧ f x ≤ 1 := by
    intro x hx
    exact isClosed_Icc.mem_of_tendsto hx.2
      (Filter.Eventually.of_forall (fun n => hbounded (φ n) x hx.1))
  obtain ⟨hm, hb, hext⟩ := monotoneExtension_properties hfm hfb
  refine ⟨monotoneExtension (fun x => f x) S, hm.monotoneOn _, fun x _ => hb x, ?_⟩
  filter_upwards [hS] with x hx
  exact hext x hx

theorem minimizers_nonexpansive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {C : Set H} (hC : Convex ℝ C)
    {u v p q : H} (hp : p ∈ C) (hq : q ∈ C)
    (hpmin : ‖u - p‖ = ⨅ w : C, ‖u - (w : H)‖)
    (hqmin : ‖v - q‖ = ⨅ w : C, ‖v - (w : H)‖) :
    ‖p - q‖ ≤ ‖u - v‖ := by
  have hpu := (norm_eq_iInf_iff_real_inner_le_zero hC hp).mp hpmin q hq
  have hqv := (norm_eq_iInf_iff_real_inner_le_zero hC hq).mp hqmin p hp
  have hpu' : 0 ≤ inner ℝ (u - p) (p - q) := by
    have heq : q - p = -(p - q) := by abel
    rw [heq, inner_neg_right] at hpu
    linarith
  have hdecomp : (u - p) - (v - q) = (u - v) - (p - q) := by abel
  have heq : inner ℝ (u - p) (p - q) - inner ℝ (v - q) (p - q) =
      inner ℝ (u - v) (p - q) - ‖p - q‖ ^ 2 := by
    rw [← inner_sub_left, hdecomp, inner_sub_left, real_inner_self_eq_norm_sq]
  have hbound := real_inner_le_norm (u - v) (p - q)
  have hn := norm_nonneg (p - q)
  by_cases hzero : ‖p - q‖ = 0
  · simpa only [hzero] using norm_nonneg (u - v)
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne hn (Ne.symm hzero)
    nlinarith

/-- Original label: `prop:cdf-constraint-properties`, clause (i). -/
theorem projection_existsUnique (a b : ℝ) (f : ℝ →₂[intervalMeasure a b] ℝ) :
    ∃! p, p ∈ constraint a b ∧
      ‖f - p‖ = ⨅ w : constraint a b, ‖f - (w : ℝ →₂[intervalMeasure a b] ℝ)‖ := by
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (nonempty a b) (isClosed a b).isComplete (convex a b) f
  refine ⟨p, ⟨hp, hmin⟩, ?_⟩
  intro q hq
  have h := minimizers_nonexpansive (convex a b) hq.1 hp hq.2 hmin
  simpa only [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] using h

/-- Original label: `prop:cdf-constraint-properties`, clause (i). -/
def projection (a b : ℝ) (f : ℝ →₂[intervalMeasure a b] ℝ) : constraint a b :=
  ⟨(projection_existsUnique a b f).choose,
    (projection_existsUnique a b f).choose_spec.1.1⟩

theorem projection_spec (a b : ℝ) (f : ℝ →₂[intervalMeasure a b] ℝ) :
    ‖f - (projection a b f : ℝ →₂[intervalMeasure a b] ℝ)‖ =
      ⨅ w : constraint a b, ‖f - (w : ℝ →₂[intervalMeasure a b] ℝ)‖ :=
  (projection_existsUnique a b f).choose_spec.1.2

/-- Original label: `prop:cdf-constraint-properties`, clause (i).
The projection is nonexpansive in the actual L² metric. -/
theorem projection_lipschitz (a b : ℝ) : LipschitzWith 1 (projection a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have h := minimizers_nonexpansive (convex a b)
    (projection a b f).property (projection a b g).property
    (projection_spec a b f) (projection_spec a b g)
  simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm] using h

end Thesis.Foundations.Research.CDFConstraint
