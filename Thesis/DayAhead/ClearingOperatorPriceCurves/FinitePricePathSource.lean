import Thesis.DayAhead.ClearingOperatorPriceCurves.CompletedInverse
import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedSide
import Thesis.DayAhead.ClearingOperatorPriceCurves.MergedPriceNodes
import Mathlib.Analysis.Convex.PathConnected

/-! # The finite polygonal-path argument for completed excess supply

Original label: `prop:price-impact-curve-properties`.
Every nodal price contributes its vertical completed segment; consecutive
prices contribute the segment joining the previous upper and next lower
vertex. Compactness and connectedness below are proved by this finite path,
rather than an infimum-cut existence theorem.
-/

noncomputable section
namespace Thesis.DayAhead.FinitePricePathSource

open Set Filter Topology

def lower (E : ℝ → ℝ) (p : ℝ) : ℝ × ℝ := (p, E.leftLim p)
def upper (E : ℝ → ℝ) (p : ℝ) : ℝ × ℝ := (p, E.rightLim p)

def polygon : {n : ℕ} → (Fin (n + 1) → ℝ) → (ℝ → ℝ) → Set (ℝ × ℝ)
  | 0, x, E => segment ℝ (lower E (x 0)) (upper E (x 0))
  | n + 1, x, E =>
    (polygon (fun i : Fin (n + 1) => x i.castSucc) E ∪
      segment ℝ (upper E (x (Fin.last n).castSucc)) (lower E (x (Fin.last (n + 1))))) ∪
      segment ℝ (lower E (x (Fin.last (n + 1)))) (upper E (x (Fin.last (n + 1))))

theorem polygon_eq_iUnion {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) :
    polygon x E =
      (⋃ i : Fin (n + 1), segment ℝ (lower E (x i)) (upper E (x i))) ∪
      ⋃ j : Fin n, segment ℝ (upper E (x j.castSucc)) (lower E (x j.succ)) := by
  induction n with
  | zero =>
    simp only [polygon, iUnion_of_empty, union_empty]
    ext z
    simp only [mem_iUnion]
    constructor
    · intro hz
      exact ⟨0, hz⟩
    · rintro ⟨i, hi⟩
      have he : i = 0 := by apply Fin.ext; omega
      simpa only [he] using hi
  | succ n ih =>
    rw [polygon, ih]
    rw [iUnion_fin_add_one_eq_iUnion_castSucc
      (fun i : Fin (n + 1 + 1) => segment ℝ (lower E (x i)) (upper E (x i)))]
    rw [iUnion_fin_add_one_eq_iUnion_castSucc
      (fun j : Fin (n + 1) => segment ℝ (upper E (x j.castSucc)) (lower E (x j.succ)))]
    simp only [Fin.castSucc_succ, Fin.succ_last]
    ext z
    simp only [mem_union, mem_iUnion]
    aesop

theorem lower_first_mem {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) :
    lower E (x 0) ∈ polygon x E := by
  induction n with
  | zero => exact left_mem_segment _ _ _
  | succ n ih => exact Or.inl (Or.inl (ih _))

theorem upper_last_mem {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) :
    upper E (x (Fin.last n)) ∈ polygon x E := by
  cases n with
  | zero => exact right_mem_segment _ _ _
  | succ n => exact Or.inr (right_mem_segment _ _ _)

theorem lower_last_mem {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) :
    lower E (x (Fin.last n)) ∈ polygon x E := by
  cases n with
  | zero => exact left_mem_segment _ _ _
  | succ n => exact Or.inr (left_mem_segment _ _ _)

theorem compact_segment (a b : ℝ × ℝ) : IsCompact (segment ℝ a b) := by
  rw [← Path.range_segment]
  exact isCompact_range (Path.segment a b).continuous

theorem polygon_compact {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) :
    IsCompact (polygon x E) := by
  induction n with
  | zero => exact compact_segment _ _
  | succ n ih => exact ((ih _).union (compact_segment _ _)).union (compact_segment _ _)

theorem polygon_preconnected {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) :
    IsPreconnected (polygon x E) := by
  induction n with
  | zero => exact (convex_segment _ _).isPreconnected
  | succ n ih =>
    have hc : IsPreconnected
        (polygon (fun i : Fin (n + 1) => x i.castSucc) E ∪
          segment ℝ (upper E (x (Fin.last n).castSucc))
            (lower E (x (Fin.last (n + 1))))) :=
      (ih (fun i => x i.castSucc)).union
      (upper E (x (Fin.last n).castSucc)) (upper_last_mem _ _)
      (left_mem_segment _ _ _) (convex_segment _ _).isPreconnected
    exact hc.union (lower E (x (Fin.last (n + 1))))
      (Or.inr (right_mem_segment _ _ _)) (left_mem_segment _ _ _)
      (convex_segment _ _).isPreconnected

def fiber {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {p | (p, q) ∈ polygon x E}

/-- Horizontal slices of the actual finite polygon are compact. -/
theorem fiber_compact {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) (q : ℝ) :
    IsCompact (fiber x E q) := by
  have hc : IsCompact (polygon x E ∩ {z : ℝ × ℝ | z.2 = q}) :=
    (polygon_compact x E).inter_right
      (isClosed_eq continuous_snd
        (continuous_const : Continuous (fun _ : ℝ × ℝ => q)))
  have he : fiber x E q = Prod.fst '' (polygon x E ∩ {z | z.2 = q}) := by
    ext p
    constructor
    · intro hp
      exact ⟨(p, q), ⟨hp, rfl⟩, rfl⟩
    · rintro ⟨⟨p, r⟩, ⟨hp, hr⟩, rfl⟩
      change r = q at hr
      subst r
      exact hp
  rw [he]
  exact hc.image continuous_fst

/-- Connectedness of the polygon and its endpoint volumes give every
intermediate completed inverse level, exactly the source IVT argument. -/
theorem fiber_nonempty {n : ℕ} (x : Fin (n + 1) → ℝ) (E : ℝ → ℝ) (q : ℝ)
    (hq : q ∈ Icc (E.leftLim (x 0)) (E.rightLim (x (Fin.last n)))) :
    (fiber x E q).Nonempty := by
  have hc := (polygon_preconnected x E).image
    Prod.snd (continuous_snd.continuousOn)
  have hl : E.leftLim (x 0) ∈ Prod.snd '' polygon x E :=
    ⟨lower E (x 0), lower_first_mem x E, rfl⟩
  have hr : E.rightLim (x (Fin.last n)) ∈ Prod.snd '' polygon x E :=
    ⟨upper E (x (Fin.last n)), upper_last_mem x E, rfl⟩
  obtain ⟨⟨p, r⟩, hp, hrq⟩ := hc.ordConnected.out hl hr hq
  exact ⟨p, by simpa only [Prod.snd] using hrq ▸ hp⟩

theorem mem_vertical {a l u p q : ℝ} (hlu : l ≤ u) :
    (p, q) ∈ segment ℝ (a, l) (a, u) ↔ p = a ∧ q ∈ Icc l u := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, he⟩
    have hp : s*a+t*a=p := congrArg Prod.fst he
    have hq : s*l+t*u=q := congrArg Prod.snd he
    constructor
    · calc
        p = (s + t) * a := by rw [← hp]; ring
        _ = a := by rw [hst, one_mul]
    · have hmem : q ∈ segment ℝ l u := ⟨s, t, hs, ht, hst, hq⟩
      rwa [segment_eq_Icc hlu] at hmem
  · rintro ⟨hp, hq⟩
    rw [hp]
    have hmem : q ∈ segment ℝ l u := by rwa [segment_eq_Icc hlu]
    obtain ⟨s, t, hs, ht, hst, he⟩ := hmem
    refine ⟨s, t, hs, ht, hst, Prod.ext ?_ ?_⟩
    · change s*a+t*a=a
      calc
        s * a + t * a = (s + t) * a := by ring
        _ = a := by rw [hst, one_mul]
    · exact he

theorem mem_affine_segment {a b A B p q : ℝ} (hab : a ≤ b) :
    (p, q) ∈ segment ℝ (a, A*a+B) (b, A*b+B) ↔
      p ∈ Icc a b ∧ q = A*p+B := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, he⟩
    have hp : s*a+t*b=p := congrArg Prod.fst he
    have hq : s*(A*a+B)+t*(A*b+B)=q := congrArg Prod.snd he
    have hmem : p ∈ segment ℝ a b := ⟨s, t, hs, ht, hst, hp⟩
    refine ⟨by rwa [segment_eq_Icc hab] at hmem, ?_⟩
    calc
      q = s * (A * a + B) + t * (A * b + B) := hq.symm
      _ = A * (s * a + t * b) + (s + t) * B := by ring
      _ = A * p + B := by rw [hp, hst, one_mul]
  · rintro ⟨hp, rfl⟩
    have hmem : p ∈ segment ℝ a b := by rwa [segment_eq_Icc hab]
    obtain ⟨s, t, hs, ht, hst, he⟩ := hmem
    refine ⟨s, t, hs, ht, hst, Prod.ext he ?_⟩
    change s*(A*a+B)+t*(A*b+B)=A*p+B
    change s*a+t*b=p at he
    calc
      s * (A * a + B) + t * (A * b + B) =
          A * (s * a + t * b) + (s + t) * B := by ring
      _ = A * p + B := by rw [he, hst, one_mul]

/-- The affine open piece determines its genuine one-sided endpoint limits. -/
theorem affine_gap_limits (E : ℝ → ℝ) {a b A B : ℝ} (hab : a < b)
    (hgap : ∀ p ∈ Ioo a b, E p = A * p + B) :
    E.rightLim a = A*a+B ∧ E.leftLim b = A*b+B ∧
      ∀ p ∈ Ioo a b, E.leftLim p = A*p+B ∧ E.rightLim p = A*p+B := by
  have hcont : Continuous (fun p : ℝ => A*p+B) := by fun_prop
  have hr : E =ᶠ[𝓝[>] a] (fun p => A*p+B) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with p hp using hgap p hp
  have hl : E =ᶠ[𝓝[<] b] (fun p => A*p+B) := by
    filter_upwards [Ioo_mem_nhdsLT hab] with p hp using hgap p hp
  refine ⟨rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    ((hcont.continuousAt.mono_left nhdsWithin_le_nhds).congr' hr.symm),
    leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    ((hcont.continuousAt.mono_left nhdsWithin_le_nhds).congr' hl.symm), ?_⟩
  intro p hp
  have he : E =ᶠ[𝓝 p] (fun t => A*t+B) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with t ht using hgap t ht
  have hc : ContinuousAt E p := hcont.continuousAt.congr_of_eventuallyEq he
  exact ⟨by rw [hc.continuousWithinAt.leftLim_eq, hgap p hp],
    by rw [hc.continuousWithinAt.rightLim_eq, hgap p hp]⟩

def completedGraph (a b : ℝ) (E : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc a b ∧ E.leftLim z.1 ≤ z.2 ∧ z.2 ≤ E.rightLim z.1}

theorem completedGraph_singleton (a : ℝ) (E : ℝ → ℝ) (hE : Monotone E) :
    completedGraph a a E = segment ℝ (lower E a) (upper E a) := by
  ext ⟨p, q⟩
  rw [lower, upper, mem_vertical (hE.leftLim_le_rightLim le_rfl)]
  change (p ∈ Icc a a ∧ E.leftLim p ≤ q ∧ q ≤ E.rightLim p) ↔ _
  constructor
  · rintro ⟨⟨hl, hr⟩, hq⟩
    have hp : p = a := le_antisymm hr hl
    exact ⟨hp, hp ▸ hq⟩
  · rintro ⟨rfl, hq⟩
    exact ⟨⟨le_rfl, le_rfl⟩, hq⟩

theorem slant_mem_completedGraph (E : ℝ → ℝ) (hE : Monotone E)
    {a b A B p q : ℝ} (hab : a < b)
    (hgap : ∀ t ∈ Ioo a b, E t = A * t + B)
    (hseg : (p, q) ∈ segment ℝ (upper E a) (lower E b)) :
    (p, q) ∈ completedGraph a b E := by
  obtain ⟨hr, hl, hinter⟩ := affine_gap_limits E hab hgap
  change (p, q) ∈ segment ℝ (a, E.rightLim a) (b, E.leftLim b) at hseg
  rw [hr, hl, mem_affine_segment hab.le] at hseg
  refine ⟨hseg.1, ?_⟩
  rcases eq_or_lt_of_le hseg.1.1 with he | ha
  · subst p
    rw [hseg.2, ← hr]
    exact ⟨hE.leftLim_le_rightLim le_rfl, le_rfl⟩
  · rcases eq_or_lt_of_le hseg.1.2 with he | hb
    · subst p
      rw [hseg.2, ← hl]
      exact ⟨le_rfl, hE.leftLim_le_rightLim le_rfl⟩
    · obtain ⟨hpl, hpr⟩ := hinter p ⟨ha, hb⟩
      rw [hpl, hpr, hseg.2]
      exact ⟨le_rfl, le_rfl⟩

/-- Appending one true affine gap adds its slant and final nodal vertical. -/
theorem completedGraph_step (E : ℝ → ℝ) (hE : Monotone E)
    {l a b A B : ℝ} (hla : l ≤ a) (hab : a < b)
    (hgap : ∀ t ∈ Ioo a b, E t = A * t + B) :
    completedGraph l b E =
      (completedGraph l a E ∪ segment ℝ (upper E a) (lower E b)) ∪
        segment ℝ (lower E b) (upper E b) := by
  obtain ⟨hr, hl, hinter⟩ := affine_gap_limits E hab hgap
  ext ⟨p, q⟩
  constructor
  · rintro ⟨hp, hq⟩
    by_cases hpa : p ≤ a
    · exact Or.inl (Or.inl ⟨⟨hp.1, hpa⟩, hq⟩)
    · by_cases hpb : p = b
      · apply Or.inr
        rw [lower, upper, mem_vertical (hE.leftLim_le_rightLim le_rfl)]
        exact ⟨hpb, hpb ▸ hq⟩
      · have ha : a < p := lt_of_not_ge hpa
        have hb : p < b := lt_of_le_of_ne hp.2 hpb
        obtain ⟨hpl, hpr⟩ := hinter p ⟨ha, hb⟩
        have hqp : q = A * p + B := le_antisymm (hpr ▸ hq.2) (hpl ▸ hq.1)
        apply Or.inl ∘ Or.inr
        change (p, q) ∈ segment ℝ (a, E.rightLim a) (b, E.leftLim b)
        rw [hr, hl, mem_affine_segment hab.le]
        exact ⟨⟨ha.le, hb.le⟩, hqp⟩
  · rintro ((hp | hseg) | hvertical)
    · exact ⟨⟨hp.1.1, hp.1.2.trans hab.le⟩, hp.2⟩
    · have hp := slant_mem_completedGraph E hE hab hgap hseg
      exact ⟨⟨hla.trans hp.1.1, hp.1.2⟩, hp.2⟩
    · rw [lower, upper, mem_vertical (hE.leftLim_le_rightLim le_rfl)] at hvertical
      rcases hvertical with ⟨rfl, hq⟩
      exact ⟨⟨hla.trans hab.le, le_rfl⟩, hq⟩

/-- The source's completed monotone graph is exactly its finite polygon. -/
theorem completedGraph_eq_polygon {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (E : ℝ → ℝ) (hE : Monotone E)
    (hgaps : ∀ j : Fin n, ∃ A B : ℝ,
      ∀ p ∈ Ioo (x j.castSucc) (x j.succ), E p = A * p + B) :
    completedGraph (x 0) (x (Fin.last n)) E = polygon x E := by
  induction n with
  | zero => exact completedGraph_singleton _ _ hE
  | succ n ih =>
    have hprefix : StrictMono (fun i : Fin (n + 1) => x i.castSucc) :=
      hx.comp (fun _ _ h => h)
    have hgprefix : ∀ j : Fin n, ∃ A B : ℝ,
        ∀ p ∈ Ioo (x j.castSucc.castSucc) (x j.succ.castSucc), E p = A * p + B := by
      intro j
      exact hgaps j.castSucc
    obtain ⟨A, B, hgap⟩ := hgaps (Fin.last n)
    have hla : x 0 ≤ x (Fin.last n).castSucc := hx.monotone (Fin.zero_le _)
    have hab : x (Fin.last n).castSucc < x (Fin.last (n + 1)) :=
      hx (Fin.castSucc_lt_succ (i := Fin.last n))
    rw [completedGraph_step E hE hla hab hgap]
    have hpre := ih _ hprefix hgprefix
    simp only [Fin.castSucc_zero] at hpre
    rw [hpre]
    rfl

open ExcessSupply

theorem book_excess_monotone {lo hi : ℝ} (m : Book lo hi) : Monotone m.excess :=
  ExcessSupply.excess_monotone _ _ m.sellDepth_nonneg m.buyDepth_nonneg _ _

/-- Instantiation at the actual sorted distinct original-price nodes. -/
theorem actual_completedGraph_eq_polygon {lo hi : ℝ} (m : Book lo hi) :
    completedGraph lo hi m.excess = polygon (MergedPriceNodes.grid m) m.excess := by
  simpa only [MergedPriceNodes.grid_first, MergedPriceNodes.grid_last] using
    completedGraph_eq_polygon (MergedPriceNodes.grid m) (MergedPriceNodes.grid m).strictMono
      m.excess (book_excess_monotone m) (MergedPriceNodes.actual_excess_affine m)

theorem actual_levelSet_eq_fiber {lo hi : ℝ} (m : Book lo hi) (q : ℝ) :
    CompletedInverse.levelSet lo hi m.excess q = fiber (MergedPriceNodes.grid m) m.excess q := by
  ext p
  change (p, q) ∈ completedGraph lo hi m.excess ↔
    (p, q) ∈ polygon (MergedPriceNodes.grid m) m.excess
  rw [actual_completedGraph_eq_polygon]

theorem actual_endpoint_volumes {lo hi : ℝ} (m : Book lo hi) :
    m.excess.leftLim lo = -m.buyDepth ∧ m.excess.rightLim hi = m.sellDepth := by
  constructor
  · apply leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => -m.buyDepth) (𝓝[<] lo)
      (𝓝 (-m.buyDepth))).congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (ExcessSupply.excess_lower_tail lo _ _ m.buyDepth_nonneg _ _
      (fun t ht => (m.supply_bounded t ⟨ht.1.le, ht.2⟩).1)
      (fun t ht => (m.demand_bounded t ⟨ht.1.le, ht.2⟩).1) p hp).symm
  · apply rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => m.sellDepth) (𝓝[>] hi)
      (𝓝 m.sellDepth)).congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (ExcessSupply.excess_upper_tail hi _ _ m.sellDepth_nonneg _ _
      (fun t ht => (m.supply_bounded t ⟨ht.1.le, ht.2⟩).2)
      (fun t ht => (m.demand_bounded t ⟨ht.1.le, ht.2⟩).2) p hp).symm

/-- Original label: `prop:price-impact-curve-properties` (closed level sets).
Compactness follows from the finite segments, then a horizontal slice — the
thesis's finite-polygon argument. -/
theorem actual_levelSet_compact {lo hi : ℝ} (m : Book lo hi) (q : ℝ) :
    IsCompact (CompletedInverse.levelSet lo hi m.excess q) := by
  rw [actual_levelSet_eq_fiber]
  exact fiber_compact _ _ _

/-- Original label: `prop:price-impact-curve-properties` (non-empty level sets).
The source proof: the finite polygon is connected and joins the depth
endpoints, so its horizontal projection contains every admissible quantity. -/
theorem actual_levelSet_nonempty {lo hi : ℝ} (m : Book lo hi) (q : ℝ)
    (hq : q ∈ m.domain) : (CompletedInverse.levelSet lo hi m.excess q).Nonempty := by
  rw [actual_levelSet_eq_fiber]
  apply fiber_nonempty
  simpa only [MergedPriceNodes.grid_first, MergedPriceNodes.grid_last,
    (actual_endpoint_volumes m).1, (actual_endpoint_volumes m).2] using hq

end Thesis.DayAhead.FinitePricePathSource
