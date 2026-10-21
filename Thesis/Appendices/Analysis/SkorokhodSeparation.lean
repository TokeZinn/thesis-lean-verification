import Thesis.Appendices.Analysis.SkorokhodMetricCore

/-! # Separation for the Skorokhod metric

One-sided continuity lets a path be recovered from arbitrarily accurate
matches under uniformly small time changes. The endpoint values are kept
because every increasing interval bijection fixes both endpoints.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ} {X : Type*} [MetricSpace X]

theorem rightContinuous_paths_eq_of_small_timeChanges (hab : a ≤ b)
    (f g : ClosedInterval a b → X)
    (hf : IsRightContinuousOnIcc f) (hg : IsRightContinuousOnIcc g)
    (hmatch : ∀ r > 0, ∀ ε > 0, ∃ e : IncreasingIntervalBijection a b,
      (∀ t, |(e t : ℝ) - t| < r) ∧ ∀ t, dist (f (e t)) (g t) < ε) : f = g := by
  funext t
  apply eq_of_forall_dist_le
  intro ε hε
  by_cases ht : (t : ℝ) = b
  · obtain ⟨e, _, he⟩ := hmatch 1 zero_lt_one ε hε
    have ht' : t = ⟨b, hab, le_rfl⟩ := Subtype.ext ht
    have het : e t = t := by rw [ht', e.apply_right hab]
    simpa only [het] using (he t).le
  have htb : (t : ℝ) < b := lt_of_le_of_ne t.property.2 ht
  obtain ⟨δf, hδf, hflocal⟩ := hf t htb (ε / 3) (by positivity)
  obtain ⟨δg, hδg, hglocal⟩ := hg t htb (ε / 3) (by positivity)
  obtain ⟨r, hr, hrb⟩ := exists_between
    (show 0 < min δf (min δg (b - t)) from lt_min hδf (lt_min hδg (sub_pos.mpr htb)))
  have hrf : r < δf := (lt_min_iff.mp hrb).1
  have hrg : r < δg := (lt_min_iff.mp (lt_min_iff.mp hrb).2).1
  have hrend : r < b - t := (lt_min_iff.mp (lt_min_iff.mp hrb).2).2
  let u : ClosedInterval a b := ⟨t + r / 2, by constructor <;> linarith [t.property.1]⟩
  obtain ⟨e, he, herr⟩ := hmatch (r / 4) (by positivity) (ε / 3) (by positivity)
  have heu := abs_lt.mp (he u)
  have hfe : dist (f (e u)) (f t) < ε / 3 := by
    apply hflocal (e u)
    · dsimp [u] at heu
      linarith [heu.1]
    · apply lt_min
      · dsimp [u] at heu
        linarith [heu.2]
      · dsimp [u] at heu
        linarith [heu.2]
  have hgu : dist (g u) (g t) < ε / 3 := by
    apply hglocal u
    · dsimp [u]
      linarith
    · dsimp [u]
      apply lt_min <;> linarith
  have h1 := dist_triangle (f t) (f (e u)) (g t)
  have h2 := dist_triangle (f (e u)) (g u) (g t)
  rw [dist_comm (f t) (f (e u))] at h1
  linarith [herr u]

theorem leftContinuous_paths_eq_of_small_timeChanges (hab : a ≤ b)
    (f g : ClosedInterval a b → X)
    (hf : IsLeftContinuousOnIcc f) (hg : IsLeftContinuousOnIcc g)
    (hmatch : ∀ r > 0, ∀ ε > 0, ∃ e : IncreasingIntervalBijection a b,
      (∀ t, |(e t : ℝ) - t| < r) ∧ ∀ t, dist (f (e t)) (g t) < ε) : f = g := by
  funext t
  apply eq_of_forall_dist_le
  intro ε hε
  by_cases ht : (t : ℝ) = a
  · obtain ⟨e, _, he⟩ := hmatch 1 zero_lt_one ε hε
    have ht' : t = ⟨a, le_rfl, hab⟩ := Subtype.ext ht
    have het : e t = t := by rw [ht', e.apply_left hab]
    simpa only [het] using (he t).le
  have hta : a < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  obtain ⟨δf, hδf, hflocal⟩ := hf t hta (ε / 3) (by positivity)
  obtain ⟨δg, hδg, hglocal⟩ := hg t hta (ε / 3) (by positivity)
  obtain ⟨r, hr, hrb⟩ := exists_between
    (show 0 < min δf (min δg (t - a)) from lt_min hδf (lt_min hδg (sub_pos.mpr hta)))
  have hrf : r < δf := (lt_min_iff.mp hrb).1
  have hrg : r < δg := (lt_min_iff.mp (lt_min_iff.mp hrb).2).1
  have hrend : r < t - a := (lt_min_iff.mp (lt_min_iff.mp hrb).2).2
  let u : ClosedInterval a b := ⟨t - r / 2, by constructor <;> linarith [t.property.2]⟩
  obtain ⟨e, he, herr⟩ := hmatch (r / 4) (by positivity) (ε / 3) (by positivity)
  have heu := abs_lt.mp (he u)
  have hfe : dist (f (e u)) (f t) < ε / 3 := by
    apply hflocal (e u)
    · apply max_lt
      · dsimp [u] at heu
        linarith [heu.1]
      · dsimp [u] at heu
        linarith [heu.1]
    · dsimp [u] at heu
      linarith [heu.2]
  have hgu : dist (g u) (g t) < ε / 3 := by
    apply hglocal u
    · dsimp [u]
      apply max_lt <;> linarith
    · dsimp [u]
      linarith
  have h1 := dist_triangle (f t) (f (e u)) (g t)
  have h2 := dist_triangle (f (e u)) (g u) (g t)
  rw [dist_comm (f t) (f (e u))] at h1
  linarith [herr u]

theorem skorokhodEDistance_eq_zero_iff (hab : a ≤ b) {side : PathOrientation}
    (f g : RegularPath a b X side) : skorokhodEDistance f g = 0 ↔ f = g := by
  refine ⟨fun hd => ?_, fun h => h ▸ skorokhodEDistance_self g⟩
  have hconv : ConvergesFor skorokhodEDistance (fun _ : ℕ => f) g := by
    intro ε hε
    exact ⟨0, fun _ _ => by simpa only [hd] using hε⟩
  obtain ⟨e, hshift, herr⟩ := skorokhodConvergence_has_timeChanges hab (fun _ => f) g hconv
  have hmatch : ∀ r > 0, ∀ ε > 0, ∃ d : IncreasingIntervalBijection a b,
      (∀ t, |(d t : ℝ) - t| < r) ∧ ∀ t, dist (f.val (d t)) (g.val t) < ε := by
    intro r hr ε hε
    have h1 := hshift.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hr))
    have h2 := herr.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    refine ⟨e n, fun t => ?_, fun t => ?_⟩
    · apply (ENNReal.ofReal_lt_ofReal_iff hr).mp
      exact (le_sSup (show ENNReal.ofReal |(e n t : ℝ) - t| ∈
        range (fun t => ENNReal.ofReal |(e n t : ℝ) - t|) from mem_range_self t)).trans_lt hn1
    · apply edist_lt_ofReal.mp
      exact (le_sSup (show edist (f.val (e n t)) (g.val t) ∈
        range (fun t => edist (f.val (e n t)) (g.val t)) from mem_range_self t)).trans_lt hn2
  apply Subtype.ext
  cases side with
  | cadlag =>
      exact rightContinuous_paths_eq_of_small_timeChanges hab f.val g.val
        f.property.1 g.property.1 hmatch
  | caglad =>
      exact leftContinuous_paths_eq_of_small_timeChanges hab f.val g.val
        f.property.1 g.property.1 hmatch

/-- Original label: `prop:skorokhod-metric`.
The complete metric-axiom clause, valid without completeness or separability
assumptions on the state space. Finiteness and the Polish clauses are separate. -/
theorem skorokhodEDistance_isExtendedMetric (hab : a ≤ b) (side : PathOrientation) :
    IsExtendedMetric (@skorokhodEDistance a b X _ side) :=
  ⟨skorokhodEDistance_eq_zero_iff hab, skorokhodEDistance_symm, skorokhodEDistance_triangle⟩

end Thesis.Foundations.Preliminary.Analysis
