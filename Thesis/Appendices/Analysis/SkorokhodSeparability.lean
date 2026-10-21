import Thesis.Appendices.Analysis.SkorokhodStepPaths

/-! # Separability of the logarithmic-distortion Skorokhod metric

Finite step paths with cuts and values in fixed countable dense sets form a
countable family. Small-distortion interpolation moves the cuts of a finite
oscillation partition into the chosen dense set of times.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ} {X : Type*} [MetricSpace X]

theorem exists_timeChange_to_dense_cuts (hab : a ≤ b) (S : Finset ℝ)
    (ha : a ∈ S) (hb : b ∈ S) {B : Set ℝ} (hB : Dense B)
    (haB : a ∈ B) (hbB : b ∈ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : IncreasingIntervalBijection a b, timeDistortion d ≤ ENNReal.ofReal ε ∧
      ∀ t : ClosedInterval a b, (t : ℝ) ∈ S → (d t : ℝ) ∈ B := by
  classical
  obtain ⟨η, hη, hinterp⟩ := finite_timeChange_interpolation_data hab S ha hb hε
  have hchoose (s : ℝ) : ∃ x ∈ B, dist s x < η := hB.exists_dist_lt s hη
  choose w hwB hw using hchoose
  let v : ℝ → ℝ := fun s => if s = a then a else if s = b then b else w s
  have va : v a = a := by simp [v]
  have vb : v b = b := by by_cases h : b = a <;> simp [v, h]
  have hv (s : ℝ) : v s ∈ B := by
    dsimp [v]
    split_ifs
    · exact haB
    · exact hbB
    · exact hwB s
  have hclose (s : ℝ) : |v s - s| ≤ η := by
    dsimp [v]
    split_ifs with hsa hsb
    · simp [hsa, hη.le]
    · simp [hsb, hη.le]
    · simpa only [Real.dist_eq, abs_sub_comm] using (hw s).le
  obtain ⟨d, hd, hvalues⟩ := hinterp v va vb (fun s _ => hclose s)
  exact ⟨d, hd, fun t ht => (hvalues t ht) ▸ hv t⟩

theorem finiteStepPaths_transport {side : PathOrientation} {S : Finset ℝ}
    {D : Set X} (g : RegularPath a b X side)
    (hg : g ∈ FiniteStepPaths a b X side S D)
    (hS : ∀ s ∈ S, s ∈ Icc a b) (d : IncreasingIntervalBijection a b)
    {C : Set ℝ} (hC : ∀ t : ClosedInterval a b, (t : ℝ) ∈ S → (d t : ℝ) ∈ C) :
    g.compTimeChange d.symm ∈ CountableStepPaths a b X side C D := by
  classical
  let T : Finset ℝ := S.attach.image fun (s : S) => (d ⟨s, hS s s.property⟩ : ℝ)
  refine ⟨T, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hy
    exact hC _ s.property
  · rintro _ ⟨t, rfl⟩
    exact hg.1 (mem_range_self _)
  · intro u v hcell
    apply hg.2
    cases side with
    | cadlag =>
        intro s hs
        let st : ClosedInterval a b := ⟨s, hS s hs⟩
        have hmem : (d st : ℝ) ∈ T :=
          Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩
        have h := hcell (d st) hmem
        have hu := d.strictMono.le_iff_le (a := st) (b := d.symm u)
        have hv := d.strictMono.le_iff_le (a := st) (b := d.symm v)
        simp only [IncreasingIntervalBijection.apply_symm_apply] at hu hv
        exact hu.symm.trans (h.trans hv)
    | caglad =>
        intro s hs
        let st : ClosedInterval a b := ⟨s, hS s hs⟩
        have hmem : (d st : ℝ) ∈ T :=
          Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩
        have h := hcell (d st) hmem
        have hu := d.strictMono.lt_iff_lt (a := st) (b := d.symm u)
        have hv := d.strictMono.lt_iff_lt (a := st) (b := d.symm v)
        simp only [IncreasingIntervalBijection.apply_symm_apply] at hu hv
        exact hu.symm.trans (h.trans hv)

theorem countableStepPaths_dense (hab : a ≤ b) {side : PathOrientation}
    {B : Set ℝ} {D : Set X} (hB : Dense B) (haB : a ∈ B) (hbB : b ∈ B)
    (hD : Dense D) (f : RegularPath a b X side) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g ∈ CountableStepPaths a b X side B D, skorokhodEDistance f g < ε := by
  obtain ⟨r, _, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp hr
  obtain ⟨S, ha, hb, hS, hosc⟩ := regularPath_finite_cuts hab f
    (show 0 < r / 4 by positivity)
  obtain ⟨g, hg, hfg⟩ := finiteStepPaths_approximation f S hD
    (show 0 < r / 4 by positivity) hosc
  obtain ⟨d, hd, hvalues⟩ := exists_timeChange_to_dense_cuts hab S ha hb hB haB hbB
    (show 0 < r / 2 by positivity)
  let k := g.compTimeChange d.symm
  have hk : k ∈ CountableStepPaths a b X side B D :=
    finiteStepPaths_transport g hg hS d hvalues
  refine ⟨k, hk, lt_of_le_of_lt (skorokhodEDistance_le f k d) ?_⟩
  have halign : (fun t => k.val (d t)) = g.val := by
    funext t
    exact congrArg g.val (d.symm_apply_apply t)
  rw [halign]
  apply lt_of_le_of_lt (max_le ?_ ?_) hrε
  · exact hd.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · exact hfg.trans (ENNReal.ofReal_le_ofReal (by linarith))

/-- Separability holds for every separable metric state space, without a
completeness assumption on the state space. -/
theorem skorokhodDistance_separable_core (hab : a ≤ b)
    [TopologicalSpace.SeparableSpace X] (side : PathOrientation) :
    IsSeparableFor (@skorokhodEDistance a b X _ side) := by
  obtain ⟨B, hBc, hBd⟩ := TopologicalSpace.exists_countable_dense ℝ
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  let C := insert a (insert b B)
  have hCc : C.Countable := (hBc.insert b).insert a
  have hCd : Dense C := hBd.mono (fun _ hx => mem_insert_of_mem _ (mem_insert_of_mem _ hx))
  refine ⟨CountableStepPaths a b X side C D, countableStepPaths_countable hCc hDc, ?_⟩
  intro f ε hε
  exact countableStepPaths_dense hab hCd (by simp [C]) (by simp [C]) hDd f hε

end Thesis.Foundations.Preliminary.Analysis
