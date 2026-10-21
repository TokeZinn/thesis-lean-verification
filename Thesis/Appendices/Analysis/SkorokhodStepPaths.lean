import Thesis.Appendices.Analysis.SkorokhodInterpolation

/-! # Finite step paths and their countability -/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ} {X : Type*} [MetricSpace X]

theorem sameCutCell_right (S : Finset ℝ) (t : ℝ) :
    ∃ δ > 0, ∀ x, t ≤ x → x < t + δ → SameCutCell S t x := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := finite_positive_lower_bound (S.filter fun s => t < s)
    (fun s => s - t) (by intro s hs; exact sub_pos.mpr (Finset.mem_filter.mp hs).2)
  refine ⟨δ, hδ, fun x htx hx s hs => ?_⟩
  constructor
  · exact fun hst => hst.trans htx
  · intro hsx
    by_contra hst
    have h := hgap s (Finset.mem_filter.mpr ⟨hs, not_le.mp hst⟩)
    linarith

theorem sameCutCell_left (S : Finset ℝ) (t : ℝ) :
    ∃ δ > 0, ∀ x y, t - δ < x → x < t → t - δ < y → y < t →
      SameCutCell S x y := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := finite_positive_lower_bound (S.filter fun s => s < t)
    (fun s => t - s) (by intro s hs; exact sub_pos.mpr (Finset.mem_filter.mp hs).2)
  refine ⟨δ, hδ, fun x y hx hxt hy hyt s hs => ?_⟩
  constructor
  · intro hsx
    have h := hgap s (Finset.mem_filter.mpr ⟨hs, hsx.trans_lt hxt⟩)
    linarith
  · intro hsy
    have h := hgap s (Finset.mem_filter.mpr ⟨hs, hsy.trans_lt hyt⟩)
    linarith

theorem isCadlag_of_finite_cut_cells (S : Finset ℝ) (f : ClosedInterval a b → X)
    (hf : ∀ u v : ClosedInterval a b, SameCutCell S u v → f u = f v) :
    IsOneSidedRegularPath .cadlag f := by
  constructor
  · intro t _ ε hε
    obtain ⟨δ, hδ, hcell⟩ := sameCutCell_right S t
    refine ⟨δ, hδ, fun x htx hx => ?_⟩
    rw [← hf t x (hcell x htx.le (hx.trans_le (min_le_left _ _))), dist_self]
    exact hε
  · intro t hat
    obtain ⟨δ, hδ, hcell⟩ := sameCutCell_left S t
    let η := min δ ((t : ℝ) - a)
    have hη : 0 < η := lt_min hδ (sub_pos.mpr hat)
    let u : ClosedInterval a b := ⟨t - η / 2, by
      constructor
      · have := min_le_right δ ((t : ℝ) - a); dsimp [η] at *; linarith
      · linarith [t.property.2]⟩
    have hu : (t : ℝ) - δ < u := by
      have := min_le_left δ ((t : ℝ) - a); dsimp [u, η] at *; linarith
    have hut : (u : ℝ) < t := by dsimp [u]; linarith
    refine ⟨f u, fun ε hε => ⟨δ, hδ, fun x hx hxt => ?_⟩⟩
    rw [hf x u (hcell x u ((le_max_right _ _).trans_lt hx) hxt hu hut), dist_self]
    exact hε

theorem cadlag_reverse_isCaglad (f : RegularPath a b X .cadlag) :
    IsOneSidedRegularPath .caglad (fun t => f.val (intervalReverse a b t)) := by
  constructor
  · apply isLeftContinuousOnIcc_of_continuousWithinAt
    intro t
    exact (f.property.1.continuousWithinAt (intervalReverse a b t)).comp
      (intervalReverseOrderIso a b).continuous.continuousWithinAt
      (fun _ hx => (intervalReverseOrderIso a b).monotone hx)
  · apply hasRightLimitsOnIcc_of_tendsto
    intro t
    obtain ⟨L, hL⟩ := f.property.2.tendsto (intervalReverse a b t)
    exact ⟨L, hL.comp
      ((intervalReverseOrderIso a b).continuous.continuousWithinAt.tendsto_nhdsWithin
        (fun _ hx => (intervalReverseOrderIso a b).strictMono hx))⟩

theorem isCaglad_of_finite_cut_cells (S : Finset ℝ) (f : ClosedInterval a b → X)
    (hf : ∀ u v : ClosedInterval a b, SameStrictCutCell S u v → f u = f v) :
    IsOneSidedRegularPath .caglad f := by
  classical
  let T := S.image fun s => a + b - s
  have hg : IsOneSidedRegularPath .cadlag (fun t => f (intervalReverse a b t)) := by
    apply isCadlag_of_finite_cut_cells T
    intro u v hcell
    apply hf
    intro s hs
    have h := hcell (a + b - s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    simp only [intervalReverse_val]
    constructor
    · intro hu
      by_contra hv
      have hv' : a + b - s ≤ (v : ℝ) := by linarith
      have hu' := h.mpr hv'
      linarith
    · intro hv
      by_contra hu
      have hu' : a + b - s ≤ (u : ℝ) := by linarith
      have hv' := h.mp hu'
      linarith
  simpa only [intervalReverse_reverse] using
    cadlag_reverse_isCaglad (⟨_, hg⟩ : RegularPath a b X .cadlag)

def SameSideCutCell (side : PathOrientation) (S : Finset ℝ) (u v : ℝ) : Prop :=
  match side with
  | .cadlag => SameCutCell S u v
  | .caglad => SameStrictCutCell S u v

theorem isRegular_of_finite_cut_cells {side : PathOrientation} (S : Finset ℝ)
    (f : ClosedInterval a b → X)
    (hf : ∀ u v : ClosedInterval a b, SameSideCutCell side S u v → f u = f v) :
    IsOneSidedRegularPath side f := by
  cases side with
  | cadlag => exact isCadlag_of_finite_cut_cells S f hf
  | caglad => exact isCaglad_of_finite_cut_cells S f hf

theorem regularPath_finite_cuts (hab : a ≤ b) {side : PathOrientation}
    (f : RegularPath a b X side) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, a ∈ S ∧ b ∈ S ∧ (∀ s ∈ S, s ∈ Icc a b) ∧
      ∀ u v : ClosedInterval a b,
        SameSideCutCell side S u v → dist (f.val u) (f.val v) < ε := by
  cases side with
  | cadlag => exact cadlag_finite_cuts hab f hε
  | caglad => exact caglad_finite_cuts hab f hε

def sideCutPattern (side : PathOrientation) (S : Finset ℝ) (t : ℝ) : S → Bool :=
  fun s => match side with
  | .cadlag => decide ((s : ℝ) ≤ t)
  | .caglad => decide ((s : ℝ) < t)

theorem sameSideCutCell_iff_pattern (side : PathOrientation) (S : Finset ℝ) (u v : ℝ) :
    SameSideCutCell side S u v ↔ sideCutPattern side S u = sideCutPattern side S v := by
  cases side <;>
    simp [SameSideCutCell, SameCutCell, SameStrictCutCell, sideCutPattern,
      funext_iff, Subtype.forall]

def CutCell (a b : ℝ) (side : PathOrientation) (S : Finset ℝ) :=
  {p : S → Bool // ∃ t : ClosedInterval a b, sideCutPattern side S t = p}

instance (a b : ℝ) (side : PathOrientation) (S : Finset ℝ) :
    Finite (CutCell a b side S) := inferInstanceAs (Finite (Subtype _))

def cutCellOf (side : PathOrientation) (S : Finset ℝ) (t : ClosedInterval a b) :
    CutCell a b side S := ⟨sideCutPattern side S t, t, rfl⟩

def cutCellRepresentative {side : PathOrientation} {S : Finset ℝ}
    (c : CutCell a b side S) : ClosedInterval a b := Classical.choose c.property

theorem cutCellRepresentative_pattern {side : PathOrientation} {S : Finset ℝ}
    (c : CutCell a b side S) : sideCutPattern side S (cutCellRepresentative c) = c.val :=
  Classical.choose_spec c.property

theorem cutCellRepresentative_same (side : PathOrientation) (S : Finset ℝ)
    (t : ClosedInterval a b) :
    SameSideCutCell side S (cutCellRepresentative (cutCellOf side S t)) t :=
  (sameSideCutCell_iff_pattern _ _ _ _).mpr (cutCellRepresentative_pattern _)

def FiniteStepPaths (a b : ℝ) (X : Type*) [MetricSpace X] (side : PathOrientation)
    (S : Finset ℝ) (D : Set X) : Set (RegularPath a b X side) :=
  {f | Set.range f.val ⊆ D ∧
    ∀ u v : ClosedInterval a b, SameSideCutCell side S u v → f.val u = f.val v}

theorem finiteStepPaths_countable {side : PathOrientation} (S : Finset ℝ)
    {D : Set X} (hD : D.Countable) : (FiniteStepPaths a b X side S D).Countable := by
  classical
  haveI := hD.to_subtype
  let encode : FiniteStepPaths a b X side S D → (CutCell a b side S → D) :=
    fun f c => ⟨f.val.val (cutCellRepresentative c), f.property.1 (mem_range_self _)⟩
  have hinj : Function.Injective encode := by
    intro f g h
    apply Subtype.ext
    apply Subtype.ext
    funext t
    have heq := congrArg Subtype.val (congrFun h (cutCellOf side S t))
    have hf := f.property.2 _ _ (cutCellRepresentative_same side S t)
    have hg := g.property.2 _ _ (cutCellRepresentative_same side S t)
    exact hf.symm.trans (heq.trans hg)
  haveI : Countable (FiniteStepPaths a b X side S D) := hinj.countable
  exact Set.to_countable _

def CountableStepPaths (a b : ℝ) (X : Type*) [MetricSpace X] (side : PathOrientation)
    (B : Set ℝ) (D : Set X) : Set (RegularPath a b X side) :=
  {f | ∃ S : Finset ℝ, (↑S : Set ℝ) ⊆ B ∧ f ∈ FiniteStepPaths a b X side S D}

theorem countableStepPaths_countable {side : PathOrientation} {B : Set ℝ} {D : Set X}
    (hB : B.Countable) (hD : D.Countable) :
    (CountableStepPaths a b X side B D).Countable := by
  classical
  haveI : Countable {T : Set ℝ // T.Finite ∧ T ⊆ B} :=
    (countable_setOf_finite_subset hB).to_subtype
  let encode : {S : Finset ℝ // (↑S : Set ℝ) ⊆ B} → {T : Set ℝ // T.Finite ∧ T ⊆ B} :=
    fun S => ⟨S.val, S.val.finite_toSet, S.property⟩
  haveI : Countable {S : Finset ℝ // (↑S : Set ℝ) ⊆ B} :=
    Function.Injective.countable (f := encode) (by
      intro S T h
      apply Subtype.ext
      exact Finset.coe_injective (congrArg Subtype.val h))
  have h := countable_iUnion (fun S : {S : Finset ℝ // (↑S : Set ℝ) ⊆ B} =>
    finiteStepPaths_countable (a := a) (b := b) (side := side) S.val hD)
  apply h.mono
  rintro f ⟨S, hS, hf⟩
  exact mem_iUnion.mpr ⟨⟨S, hS⟩, hf⟩

theorem finiteStepPaths_approximation {side : PathOrientation}
    (f : RegularPath a b X side) (S : Finset ℝ) {D : Set X} (hD : Dense D)
    {ε : ℝ} (hε : 0 < ε)
    (hosc : ∀ u v : ClosedInterval a b,
      SameSideCutCell side S u v → dist (f.val u) (f.val v) < ε) :
    ∃ g ∈ FiniteStepPaths a b X side S D,
      supPathEDistance f.val g.val ≤ ENNReal.ofReal (2 * ε) := by
  classical
  have hchoose (c : CutCell a b side S) :
      ∃ x ∈ D, dist (f.val (cutCellRepresentative c)) x < ε :=
    hD.exists_dist_lt _ hε
  choose v hvD hv using hchoose
  let raw : ClosedInterval a b → X := fun t => v (cutCellOf side S t)
  have hraw (u w : ClosedInterval a b) (hcell : SameSideCutCell side S u w) :
      raw u = raw w := by
    apply congrArg v
    apply Subtype.ext
    exact (sameSideCutCell_iff_pattern _ _ _ _).mp hcell
  let g : RegularPath a b X side := ⟨raw, isRegular_of_finite_cut_cells S raw hraw⟩
  refine ⟨g, ⟨?_, hraw⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hvD (cutCellOf side S t)
  · rw [supPathEDistance_le_iff]
    intro t
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have h₁ := hosc (cutCellRepresentative (cutCellOf side S t)) t
      (cutCellRepresentative_same side S t)
    have h₂ := hv (cutCellOf side S t)
    have htriangle := dist_triangle (f.val t)
      (f.val (cutCellRepresentative (cutCellOf side S t))) (g.val t)
    rw [dist_comm] at h₁
    change dist (f.val t) (raw t) ≤ 2 * ε
    dsimp only [g, raw] at *
    linarith

end Thesis.Foundations.Preliminary.Analysis
