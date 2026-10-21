import Thesis.DayAhead.ClearingOperatorPriceCurves.FinitePricePathSource
import Thesis.DayAhead.ClearingOperatorPriceCurves.FinitePolygonInverse

/-! # Affinity between consecutive transposed vertex quantities

The finite polygon is transposed as in the supplied proof. Away from every
vertex quantity, one positive-width segment covers the whole quantity gap.
The monotonicity of the completed graph pins its selected inverse to that
segment's affine formula.
-/

noncomputable section
namespace Thesis.DayAhead.FinitePolygonInverseAffinity

open Set Filter Topology CompletedInverse FinitePricePathSource
open FinitePolygonInverse InterpolatedSide

theorem level_strict_order {lo hi q r p s : ℝ} {E : ℝ → ℝ}
    (hE : Monotone E) (hp : p ∈ levelSet lo hi E q)
    (hs : s ∈ levelSet lo hi E r) (hqr : q < r) : p ≤ s := by
  by_contra h
  have hh := hE.rightLim_le_leftLim (lt_of_not_ge h)
  linarith [hp.2.1, hs.2.2]

/-- On the interior of a segment of positive quantity width, the actual
midpoint inverse is precisely the transposed affine interpolation. -/
theorem midpoint_eq_interpolate {lo hi : ℝ} {E : ℝ → ℝ}
    (hE : Monotone E) {a b : ℝ × ℝ} (hp : a.1 ≤ b.1) (hq : a.2 < b.2)
    (hsub : segment ℝ a b ⊆ completedGraph lo hi E)
    {q : ℝ} (hqq : q ∈ Ioo a.2 b.2) :
    midpointPrice lo hi E q = interpolate a.2 b.2 a.1 b.1 q := by
  let line := interpolate a.2 b.2 a.1 b.1
  have hline : ∀ r ∈ Ioo a.2 b.2, line r ∈ levelSet lo hi E r := by
    intro r hr
    have hh := (segment_endpoints_mem hp hq.le ⟨hr.1.le, hr.2.le⟩).1
    simp only [segmentLeft, if_pos hq] at hh
    exact hsub hh
  have hselected : midpointPrice lo hi E q ∈ levelSet lo hi E q :=
    midpointPrice_mem_levelSet lo hi E hE q ⟨line q, hline q hqq⟩
  have hcont : Continuous line := by unfold line interpolate; fun_prop
  have hl : line q ≤ midpointPrice lo hi E q := by
    apply le_of_tendsto (show Tendsto line (𝓝[<] q) (𝓝 (line q)) from
      hcont.continuousAt.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsLT_of_mem ⟨hqq.1, hqq.2.le⟩,
      self_mem_nhdsWithin] with r hr hrq
    exact level_strict_order hE (hline r hr) hselected hrq
  have hu : midpointPrice lo hi E q ≤ line q := by
    apply ge_of_tendsto (show Tendsto line (𝓝[>] q) (𝓝 (line q)) from
      hcont.continuousAt.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT_of_mem ⟨hqq.1.le, hqq.2⟩,
      self_mem_nhdsWithin] with r hr hqr
    exact level_strict_order hE hselected (hline r hr) hqr
  exact le_antisymm hu hl

/-- A quantity interval containing no polygon vertex lies on one transposed
positive-width piece. The hypotheses refer to the actual completed graph,
not to a certificate assuming the inverse is affine. -/
theorem midpoint_affine_on_vertex_gap {ι : Type*}
    {lo hi u v : ℝ} {E : ℝ → ℝ} (hE : Monotone E)
    (a b : ι → ℝ × ℝ)
    (hp : ∀ i, (a i).1 ≤ (b i).1) (hq : ∀ i, (a i).2 ≤ (b i).2)
    (hgraph : completedGraph lo hi E = ⋃ i, segment ℝ (a i) (b i))
    (huv : u < v)
    (hvertices : ∀ i, (a i).2 ∉ Ioo u v ∧ (b i).2 ∉ Ioo u v)
    (hne : (levelSet lo hi E ((u + v) / 2)).Nonempty) :
    ∃ A B : ℝ, ∀ q ∈ Ioo u v, midpointPrice lo hi E q = A * q + B := by
  let q₀ := (u + v) / 2
  have hq₀ : q₀ ∈ Ioo u v := ⟨by dsimp [q₀]; linarith, by dsimp [q₀]; linarith⟩
  obtain ⟨p₀, hp₀⟩ := hne
  have hm : (p₀, q₀) ∈ ⋃ i, segment ℝ (a i) (b i) := by
    rw [← hgraph]
    exact hp₀
  obtain ⟨i, hsegment⟩ := mem_iUnion.mp hm
  have hvol := ((mem_segment_iff (hp i) (hq i) p₀ q₀).mp hsegment).1
  have ha : (a i).2 ≤ u := by
    by_contra h
    exact (hvertices i).1 ⟨lt_of_not_ge h, hvol.1.trans_lt hq₀.2⟩
  have hb : v ≤ (b i).2 := by
    by_contra h
    exact (hvertices i).2 ⟨hq₀.1.trans_le hvol.2, lt_of_not_ge h⟩
  have hw : (a i).2 < (b i).2 := ha.trans_lt (huv.trans_le hb)
  have hsub : segment ℝ (a i) (b i) ⊆ completedGraph lo hi E := by
    rw [hgraph]
    exact fun _ hz => mem_iUnion.mpr ⟨i, hz⟩
  refine ⟨((b i).1 - (a i).1) / ((b i).2 - (a i).2),
    ((b i).2 * (a i).1 - (a i).2 * (b i).1) / ((b i).2 - (a i).2), ?_⟩
  intro q hqq
  rw [midpoint_eq_interpolate hE (hp i) hw hsub ⟨ha.trans_lt hqq.1, hqq.2.trans_le hb⟩]
  unfold interpolate
  ring

end Thesis.DayAhead.FinitePolygonInverseAffinity
