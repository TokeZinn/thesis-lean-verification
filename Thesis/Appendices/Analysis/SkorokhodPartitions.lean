import Thesis.Appendices.Analysis.SkorokhodUniform

/-! # Finite partitions with small path oscillation

Finite cut sets encode the half-open cells of a step function without choosing
an enumeration. A supremum argument constructs enough cuts for a càdlàg
path: left limits reach the supremum, and right continuity extends beyond it.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ} {X : Type*} [MetricSpace X]

def SameCutCell (S : Finset ℝ) (u v : ℝ) : Prop := ∀ s ∈ S, s ≤ u ↔ s ≤ v

def SmallCutOscillationBefore (f : ClosedInterval a b → X) (ε : ℝ)
    (S : Finset ℝ) (t : ℝ) : Prop :=
  ∀ u v : ClosedInterval a b, (u : ℝ) < t → (v : ℝ) < t →
    SameCutCell S u v → dist (f u) (f v) < ε

theorem smallCutOscillationBefore_extend (f : ClosedInterval a b → X) {ε t z : ℝ}
    {S : Finset ℝ} (hS : SmallCutOscillationBefore f ε S t)
    (hlocal : ∀ u v : ClosedInterval a b, t ≤ (u : ℝ) → (u : ℝ) < z →
      t ≤ (v : ℝ) → (v : ℝ) < z → dist (f u) (f v) < ε) :
    SmallCutOscillationBefore f ε (insert t S) z := by
  classical
  intro u v huz hvz hcell
  have ht := hcell t (Finset.mem_insert_self _ _)
  by_cases hu : (u : ℝ) < t
  · have hv : (v : ℝ) < t := not_le.mp (fun hv => (not_le.mpr hu) (ht.mpr hv))
    exact hS u v hu hv (fun s hs => hcell s (Finset.mem_insert_of_mem hs))
  · exact hlocal u v (not_lt.mp hu) huz (ht.mp (not_lt.mp hu)) hvz

theorem cadlag_finite_cuts_before (hab : a ≤ b) (f : RegularPath a b X .cadlag)
    {ε : ℝ} (hε : 0 < ε) : ∃ S : Finset ℝ, SmallCutOscillationBefore f.val ε S b := by
  classical
  let D : Set ℝ := {t | t ∈ Icc a b ∧ ∃ S : Finset ℝ, SmallCutOscillationBefore f.val ε S t}
  have ha : a ∈ D := ⟨⟨le_rfl, hab⟩, ∅, fun u _ hu _ _ =>
    False.elim (not_lt_of_ge u.property.1 hu)⟩
  have hDne : D.Nonempty := ⟨a, ha⟩
  have hDbdd : BddAbove D := ⟨b, fun _ ht => ht.1.2⟩
  let x := sSup D
  have hax : a ≤ x := le_csSup hDbdd ha
  have hxb : x ≤ b := csSup_le hDne (fun _ ht => ht.1.2)
  let xt : ClosedInterval a b := ⟨x, hax, hxb⟩
  have hxgood : ∃ S : Finset ℝ, SmallCutOscillationBefore f.val ε S x := by
    by_cases hxa : x = a
    · simpa only [hxa] using ha.2
    have hax' : a < x := lt_of_le_of_ne hax (Ne.symm hxa)
    obtain ⟨L, hL⟩ := f.property.2 xt hax'
    obtain ⟨δ, hδ, hlocal⟩ := hL (ε / 2) (by positivity)
    have hcut : max a (x - δ) < x := max_lt hax' (by linarith)
    obtain ⟨t, htD, ht⟩ := exists_lt_of_lt_csSup hDne hcut
    obtain ⟨S, hS⟩ := htD.2
    refine ⟨insert t S, smallCutOscillationBefore_extend f.val hS ?_⟩
    intro u v htu hux htv hvx
    have hu := hlocal u (lt_of_lt_of_le ht htu) hux
    have hv := hlocal v (lt_of_lt_of_le ht htv) hvx
    have hdist := dist_triangle (f.val u) L (f.val v)
    rw [dist_comm L (f.val v)] at hdist
    linarith
  have hxeqb : x = b := by
    by_contra hxbne
    have hxb' : x < b := lt_of_le_of_ne hxb hxbne
    obtain ⟨δ, hδ, hlocal⟩ := f.property.1 xt hxb' (ε / 2) (by positivity)
    obtain ⟨z, hxz, hz⟩ := exists_between (lt_min (show x < x + δ by linarith) hxb')
    obtain ⟨S, hS⟩ := hxgood
    have hlocal' (u : ClosedInterval a b) (hxu : x ≤ u) (huz : (u : ℝ) < z) :
        dist (f.val u) (f.val xt) < ε / 2 := by
      rcases hxu.eq_or_lt with hu | hu
      · have heq : u = xt := Subtype.ext hu.symm
        simpa only [heq, dist_self] using (show 0 < ε / 2 by positivity)
      · exact hlocal u hu (huz.trans hz)
    have hzgood : SmallCutOscillationBefore f.val ε (insert x S) z := by
      apply smallCutOscillationBefore_extend f.val hS
      intro u v hxu huz hxv hvz
      have hu := hlocal' u hxu huz
      have hv := hlocal' v hxv hvz
      have hdist := dist_triangle (f.val u) (f.val xt) (f.val v)
      rw [dist_comm (f.val xt) (f.val v)] at hdist
      linarith
    have hzD : z ∈ D := ⟨⟨hax.trans hxz.le, (hz.trans_le (min_le_right _ _)).le⟩,
      insert x S, hzgood⟩
    exact (not_lt_of_ge (le_csSup hDbdd hzD)) hxz
  simpa only [hxeqb] using hxgood

theorem cadlag_finite_cuts (hab : a ≤ b) (f : RegularPath a b X .cadlag)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, a ∈ S ∧ b ∈ S ∧ (∀ s ∈ S, s ∈ Icc a b) ∧
      ∀ u v : ClosedInterval a b, SameCutCell S u v → dist (f.val u) (f.val v) < ε := by
  classical
  obtain ⟨S, hS⟩ := cadlag_finite_cuts_before hab f hε
  let T := insert a (insert b (S.filter fun s => s ∈ Icc a b))
  refine ⟨T, by simp [T], by simp [T], ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact ⟨le_rfl, hab⟩
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact ⟨hab, le_rfl⟩
    exact (Finset.mem_filter.mp hs).2
  · intro u v hcell
    have hcellS : SameCutCell S u v := by
      intro s hs
      by_cases hsa : a ≤ s
      · by_cases hsb : s ≤ b
        · exact hcell s (by simp [T, hs, hsa, hsb])
        · have hsu : ¬ s ≤ (u : ℝ) := by linarith [u.property.2]
          have hsv : ¬ s ≤ (v : ℝ) := by linarith [v.property.2]
          simp only [hsu, hsv]
      · have hsu : s ≤ (u : ℝ) := by linarith [u.property.1]
        have hsv : s ≤ (v : ℝ) := by linarith [v.property.1]
        simp only [hsu, hsv]
    by_cases hu : (u : ℝ) = b
    · have hv : (v : ℝ) = b := le_antisymm v.property.2
        ((hcell b (by simp [T])).mp hu.ge)
      have huv : u = v := Subtype.ext (hu.trans hv.symm)
      simpa only [huv, dist_self] using hε
    · have hub : (u : ℝ) < b := lt_of_le_of_ne u.property.2 hu
      have hvb : (v : ℝ) < b := not_le.mp (fun hv =>
        (not_le.mpr hub) ((hcell b (by simp [T])).mpr hv))
      exact hS u v hub hvb hcellS

theorem cadlag_small_error_of_fixes_cuts (hab : a ≤ b) (f : RegularPath a b X .cadlag)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, (∀ s ∈ S, s ∈ Icc a b) ∧
      ∀ e : IncreasingIntervalBijection a b,
        (∀ s : ClosedInterval a b, (s : ℝ) ∈ S → e s = s) →
        supPathEDistance f.val (fun t => f.val (e t)) ≤ ENNReal.ofReal ε := by
  obtain ⟨S, _, _, hS, hosc⟩ := cadlag_finite_cuts hab f hε
  refine ⟨S, hS, fun e he => ?_⟩
  rw [supPathEDistance_le_iff]
  intro t
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  apply (hosc t (e t) ?_).le
  intro s hs
  let st : ClosedInterval a b := ⟨s, hS s hs⟩
  have hfix := he st hs
  have hiff := e.strictMono.le_iff_le (a := st) (b := t)
  rw [hfix] at hiff
  exact hiff.symm

end Thesis.Foundations.Preliminary.Analysis
