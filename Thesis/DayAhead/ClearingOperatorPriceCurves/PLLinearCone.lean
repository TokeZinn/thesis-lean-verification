import Thesis.DayAhead.ClearingOperatorPriceCurves.PLParametrisation
import Thesis.Foundations.Stochastic.KernelHilbert

/-! # Conic closure of linear encodings on the full finite-affine carrier -/

noncomputable section
namespace Thesis.DayAhead.PLLinearCone

open Set MeasureTheory PiecewiseAffinePriceCurves PLParametrisation PriceCurveHilbert
open Foundations.Stochastic.KernelHilbert

namespace Partition

def restrictTo {D S : Set ℝ} {f : ℝ → ℝ} (P : AffinePartition D f)
    (hS : OrdConnected S) (hsub : S ⊆ D) : AffinePartition S f := by
  simpa only [inter_eq_right.mpr hsub] using P.restrict S hS

def congrPrice {D : Set ℝ} {f g : ℝ → ℝ} (P : AffinePartition D f)
    (h : EqOn f g D) : AffinePartition D g where
  count := P.count
  piece := P.piece
  interval := P.interval
  disjoint := P.disjoint
  cover := P.cover
  affine := fun i => by
    obtain ⟨a, b, hi⟩ := P.affine i
    exact ⟨a, b, fun x hx => (h (P.piece_subset i hx)).symm.trans (hi x hx)⟩

def join {D S : Set ℝ} {f : ℝ → ℝ} (P : AffinePartition D f)
    (Q : AffinePartition S f) (hDS : Disjoint D S) : AffinePartition (D ∪ S) f where
  count := Fintype.card (Fin P.count ⊕ Fin Q.count)
  piece := fun k => Sum.elim P.piece Q.piece ((Fintype.equivFin _).symm k)
  interval := by
    intro k
    cases (Fintype.equivFin (Fin P.count ⊕ Fin Q.count)).symm k with
    | inl i => exact P.interval i
    | inr j => exact Q.interval j
  disjoint := by
    intro k l hkl
    let e := Fintype.equivFin (Fin P.count ⊕ Fin Q.count)
    have hne : e.symm k ≠ e.symm l := fun h => hkl (e.symm.injective h)
    cases hk : e.symm k with
    | inl i =>
      cases hl : e.symm l with
      | inl j => exact P.disjoint i j (fun h => hne (by simp [hk, hl, h]))
      | inr j => exact hDS.mono (P.piece_subset i) (Q.piece_subset j)
    | inr i =>
      cases hl : e.symm l with
      | inl j => exact hDS.symm.mono (Q.piece_subset i) (P.piece_subset j)
      | inr j => exact Q.disjoint i j (fun h => hne (by simp [hk, hl, h]))
  cover := by
    intro x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i, hi⟩ := (P.cover x).mp hx
        exact ⟨Fintype.equivFin _ (.inl i), by simpa using hi⟩
      · obtain ⟨j, hj⟩ := (Q.cover x).mp hx
        exact ⟨Fintype.equivFin _ (.inr j), by simpa using hj⟩
    · rintro ⟨k, hk⟩
      cases he : (Fintype.equivFin (Fin P.count ⊕ Fin Q.count)).symm k with
      | inl i => exact Or.inl (P.piece_subset i (by simpa [he] using hk))
      | inr j => exact Or.inr (Q.piece_subset j (by simpa [he] using hk))
  affine := by
    intro k
    cases (Fintype.equivFin (Fin P.count ⊕ Fin Q.count)).symm k with
    | inl i => exact P.affine i
    | inr j => exact Q.affine j

end Partition

def pullQuantity (f : Curve) (L R x : ℝ) : ℝ :=
  if x ≤ 0 then (f.leftEndpoint / L) * x else (f.rightEndpoint / R) * x

theorem pullQuantity_monotone (f : Curve) (L R : ℝ) (hL : L ≤ 0) (hR : 0 ≤ R) :
    Monotone (pullQuantity f L R) := by
  have hl : 0 ≤ f.leftEndpoint / L := div_nonneg_of_nonpos f.left_nonpos hL
  have hr : 0 ≤ f.rightEndpoint / R := div_nonneg f.right_nonneg hR
  intro x y hxy
  simp only [pullQuantity]
  split_ifs with hx hy <;> nlinarith

theorem pullQuantity_mem (f : Curve) (L R : ℝ) (hL : L ≤ 0) (hR : 0 ≤ R)
    {x : ℝ} (hx : x ∈ Icc L R) : pullQuantity f L R x ∈ Icc f.leftEndpoint f.rightEndpoint := by
  have hl : 0 ≤ f.leftEndpoint / L := div_nonneg_of_nonpos f.left_nonpos hL
  have hr : 0 ≤ f.rightEndpoint / R := div_nonneg f.right_nonneg hR
  unfold pullQuantity
  split_ifs with hx0
  · constructor
    · by_cases hL0 : L = 0
      · have hx0' : x = 0 := by linarith [hx.1]
        simpa only [hx0', mul_zero] using f.left_nonpos
      · have h := mul_le_mul_of_nonneg_left hx.1 hl
        rwa [div_mul_cancel₀ _ hL0] at h
    · exact (mul_nonpos_of_nonneg_of_nonpos hl hx0).trans f.right_nonneg
  · constructor
    · exact f.left_nonpos.trans (mul_nonneg hr (le_of_not_ge hx0))
    · have hR0 : R ≠ 0 := by intro h; linarith [hx.2]
      have h := mul_le_mul_of_nonneg_left hx.2 hr
      rwa [div_mul_cancel₀ _ hR0] at h

def pullbackPartition (f : Curve) (L R : ℝ) (hL : L ≤ 0) (hR : 0 ≤ R) :
    AffinePartition (Icc L R) (fun x => f.price (pullQuantity f L R x)) := by
  let P := Classical.choice f.pieces
  have hl : 0 ≤ f.leftEndpoint / L := div_nonneg_of_nonpos f.left_nonpos hL
  have hr : 0 ≤ f.rightEndpoint / R := div_nonneg f.right_nonneg hR
  let A := P.compAffine (f.leftEndpoint / L) 0 hl
  let B := P.compAffine (f.rightEndpoint / R) 0 hr
  have hAsub : Icc L 0 ⊆ (fun x => (f.leftEndpoint / L) * x + 0) ⁻¹'
      Icc f.leftEndpoint f.rightEndpoint := by
    intro x hx
    simpa only [add_zero, pullQuantity, if_pos hx.2] using
      pullQuantity_mem f L R hL hR ⟨hx.1, hx.2.trans hR⟩
  have hBsub : Ioc 0 R ⊆ (fun x => (f.rightEndpoint / R) * x + 0) ⁻¹'
      Icc f.leftEndpoint f.rightEndpoint := by
    intro x hx
    simpa only [add_zero, pullQuantity, if_neg (not_le.mpr hx.1)] using
      pullQuantity_mem f L R hL hR ⟨hL.trans hx.1.le, hx.2⟩
  let A' := Partition.restrictTo A ordConnected_Icc hAsub
  let B' := Partition.restrictTo B ordConnected_Ioc hBsub
  let A'' : AffinePartition (Icc L 0) (fun x => f.price (pullQuantity f L R x)) :=
    Partition.congrPrice A' (by intro x hx; simp only [add_zero, pullQuantity, if_pos hx.2])
  let B'' : AffinePartition (Ioc 0 R) (fun x => f.price (pullQuantity f L R x)) :=
    Partition.congrPrice B' (by
      intro x hx; simp only [add_zero, pullQuantity, if_neg (not_le.mpr hx.1)])
  have hdisj : Disjoint (Icc L 0) (Ioc 0 R) := by
    exact Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1
  simpa only [Icc_union_Ioc_eq_Icc hL hR] using Partition.join A'' B'' hdisj

def combinedLeft (f g : Curve) (a b : ℝ) : ℝ := a * f.leftEndpoint + b * g.leftEndpoint
def combinedRight (f g : Curve) (a b : ℝ) : ℝ := a * f.rightEndpoint + b * g.rightEndpoint

theorem combinedLeft_nonpos (f g : Curve) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    combinedLeft f g a b ≤ 0 :=
  add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha f.left_nonpos)
    (mul_nonpos_of_nonneg_of_nonpos hb g.left_nonpos)

theorem combinedRight_nonneg (f g : Curve) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ combinedRight f g a b :=
  add_nonneg (mul_nonneg ha f.right_nonneg) (mul_nonneg hb g.right_nonneg)

def combination (f g : Curve) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Curve where
  leftEndpoint := combinedLeft f g a b
  rightEndpoint := combinedRight f g a b
  left_nonpos := combinedLeft_nonpos f g ha hb
  right_nonneg := combinedRight_nonneg f g ha hb
  price := fun x =>
    a * f.price (pullQuantity f (combinedLeft f g a b) (combinedRight f g a b) x) +
    b * g.price (pullQuantity g (combinedLeft f g a b) (combinedRight f g a b) x)
  monotone := by
    intro x hx y hy hxy
    have hL := combinedLeft_nonpos f g ha hb
    have hR := combinedRight_nonneg f g ha hb
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (f.monotone (pullQuantity_mem f _ _ hL hR hx) (pullQuantity_mem f _ _ hL hR hy)
          (pullQuantity_monotone f _ _ hL hR hxy)) ha)
      (mul_le_mul_of_nonneg_left
        (g.monotone (pullQuantity_mem g _ _ hL hR hx) (pullQuantity_mem g _ _ hL hR hy)
          (pullQuantity_monotone g _ _ hL hR hxy)) hb)
  pieces := by
    have hL := combinedLeft_nonpos f g ha hb
    have hR := combinedRight_nonneg f g ha hb
    exact ⟨by simpa only [inter_self] using
      (pullbackPartition f _ _ hL hR).combine (pullbackPartition g _ _ hL hR) a b⟩

/-- The constructed curve is simple whenever both inputs are simple, as in
the source proof, while the general construction allows nonconstant pieces. -/
theorem combination_isSimple (f g : Curve) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : f.IsSimple) (hg : g.IsSimple) : (combination f g a b ha hb).IsSimple := by
  have hL := combinedLeft_nonpos f g ha hb
  have hR := combinedRight_nonneg f g ha hb
  apply ((hf.prod hg).image (fun z : ℝ × ℝ => a * z.1 + b * z.2)).subset
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(f.price (pullQuantity f _ _ x), g.price (pullQuantity g _ _ x)), ?_, rfl⟩
  exact ⟨⟨_, pullQuantity_mem f _ _ hL hR hx, rfl⟩,
    ⟨_, pullQuantity_mem g _ _ hL hR hx, rfl⟩⟩

theorem combination_linearQuantity (f g : Curve) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : ℝ) : linearQuantity (combination f g a b ha hb) u =
      a * linearQuantity f u + b * linearQuantity g u := by
  simp only [linearQuantity, combination, combinedLeft, combinedRight]
  split_ifs <;> ring

theorem weighted_pull_linear (f : Curve) (L R a : ℝ) (hL : L ≤ 0) (hR : 0 ≤ R)
    (hflatL : L = 0 → a * f.leftEndpoint = 0)
    (hflatR : R = 0 → a * f.rightEndpoint = 0) (u : ℝ) :
    a * f.price (pullQuantity f L R (if u ≤ 0 then -L * u else R * u)) =
      a * f.price (linearQuantity f u) := by
  by_cases hu : u ≤ 0
  · have hq : -L * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hL) hu
    simp only [if_pos hu, pullQuantity, if_pos hq, linearQuantity]
    by_cases hL0 : L = 0
    · rcases mul_eq_zero.mp (hflatL hL0) with hzero | hzero <;> simp [hL0, hzero]
    · have harg : f.leftEndpoint / L * (-L * u) = -f.leftEndpoint * u := by
        field_simp
      rw [harg]
  · by_cases hR0 : R = 0
    · rcases mul_eq_zero.mp (hflatR hR0) with hzero | hzero <;>
        simp [hR0, pullQuantity, linearQuantity, hu, hzero]
    · have hq : 0 < R * u :=
        mul_pos (lt_of_le_of_ne hR (Ne.symm hR0)) (lt_of_not_ge hu)
      simp only [if_neg hu, pullQuantity, if_neg (not_le.mpr hq), linearQuantity]
      have harg : f.rightEndpoint / R * (R * u) = f.rightEndpoint * u := by
        field_simp
      rw [harg]

/-- Original label: `prop:linear-parametrisation-convex`.
This identity holds pointwise for the constructed full finite-affine curve,
including collapsed sides and zero coefficients. -/
theorem linearEncoding_combination (f g : Curve) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    linearEncoding (combination f g a b ha hb) = a • linearEncoding f + b • linearEncoding g := by
  have hL := combinedLeft_nonpos f g ha hb
  have hR := combinedRight_nonneg f g ha hb
  have hLf : combinedLeft f g a b = 0 → a * f.leftEndpoint = 0 := by
    intro h
    have hg := mul_nonpos_of_nonneg_of_nonpos hb g.left_nonpos
    have hf := mul_nonpos_of_nonneg_of_nonpos ha f.left_nonpos
    unfold combinedLeft at h
    linarith
  have hLg : combinedLeft f g a b = 0 → b * g.leftEndpoint = 0 := by
    intro h
    have hg := mul_nonpos_of_nonneg_of_nonpos hb g.left_nonpos
    have hf := mul_nonpos_of_nonneg_of_nonpos ha f.left_nonpos
    unfold combinedLeft at h
    linarith
  have hRf : combinedRight f g a b = 0 → a * f.rightEndpoint = 0 := by
    intro h
    have hg := mul_nonneg hb g.right_nonneg
    have hf := mul_nonneg ha f.right_nonneg
    unfold combinedRight at h
    linarith
  have hRg : combinedRight f g a b = 0 → b * g.rightEndpoint = 0 := by
    intro h
    have hg := mul_nonneg hb g.right_nonneg
    have hf := mul_nonneg ha f.right_nonneg
    unfold combinedRight at h
    linarith
  funext u
  apply Prod.ext
  · exact combination_linearQuantity f g a b ha hb u
  · change a * f.price (pullQuantity f (combinedLeft f g a b) (combinedRight f g a b)
        (if (u : ℝ) ≤ 0 then -(combinedLeft f g a b) * u else combinedRight f g a b * u)) +
      b * g.price (pullQuantity g (combinedLeft f g a b) (combinedRight f g a b)
        (if (u : ℝ) ≤ 0 then -(combinedLeft f g a b) * u else combinedRight f g a b * u)) =
      a * f.price (linearQuantity f u) + b * g.price (linearQuantity g u)
    rw [weighted_pull_linear f _ _ a hL hR hLf hRf,
      weighted_pull_linear g _ _ b hL hR hLg hRg]

/-- Original label: `prop:linear-parametrisation-convex`. -/
theorem linearEncoding_weaklyConvex :
    WeaklyConvexOperator Curve (PriceCurves.Parameter → ℝ × ℝ) linearEncoding := by
  intro a b ha hb f g
  exact ⟨combination f g a b ha hb, linearEncoding_combination f g a b ha hb⟩

/-- Original label: `prop:linear-parametrisation-convex`.
The literal pointwise image is a convex cone; no topological closure or
enlargement of the source image is used. -/
theorem range_linearEncoding_convexCone : ConvexCone (range linearEncoding) := by
  letI : Nonempty Curve := ⟨unitRamp⟩
  exact (weaklyConvexOperator_iff_range_convexCone linearEncoding).mp linearEncoding_weaklyConvex

/-- Original label: `prop:linear-parametrisation-convex`.
The same explicitly constructed curve realizes the combination of actual
Euclidean-valued L² classes for any finite measure on the parameter interval. -/
theorem linearEncodingLp_combination (μ : Measure PriceCurves.Parameter) [IsFiniteMeasure μ]
    (f g : Curve) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    linearEncodingLp μ (combination f g a b ha hb) =
      a • linearEncodingLp μ f + b • linearEncodingLp μ g := by
  apply Lp.ext
  filter_upwards [coeFn_encodingLp μ (combination f g a b ha hb)
      (linearAdmissible (combination f g a b ha hb)),
    coeFn_encodingLp μ f (linearAdmissible f), coeFn_encodingLp μ g (linearAdmissible g),
    Lp.coeFn_add (a • linearEncodingLp μ f) (b • linearEncodingLp μ g),
    Lp.coeFn_smul a (linearEncodingLp μ f), Lp.coeFn_smul b (linearEncodingLp μ g)] with
      u hh hf hg hsum hasmul hbsmul
  change linearEncodingLp μ (combination f g a b ha hb) u =
    pairEquiv (linearEncoding (combination f g a b ha hb) u) at hh
  change linearEncodingLp μ f u = pairEquiv (linearEncoding f u) at hf
  change linearEncodingLp μ g u = pairEquiv (linearEncoding g u) at hg
  simp only [Pi.add_apply, Pi.smul_apply] at hsum hasmul hbsmul
  rw [hh, hsum, hasmul, hbsmul, hf, hg]
  change pairEquiv (linearEncoding (combination f g a b ha hb) u) =
    a • pairEquiv (linearEncoding f u) + b • pairEquiv (linearEncoding g u)
  rw [linearEncoding_combination]
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul]

/-- Original block id:
`source:2 - day-ahead/2_clearing_operator_price_curves.tex:261:cor:11`.
Weak convexity holds on the full finite-affine curve carrier in the actual
Euclidean-valued Hilbert space. -/
theorem linearEncodingLp_weaklyConvex (μ : Measure PriceCurves.Parameter) [IsFiniteMeasure μ] :
    WeaklyConvexOperator Curve (PriceHilbertSpace μ) (linearEncodingLp μ) := by
  intro a b ha hb f g
  exact ⟨combination f g a b ha hb, linearEncodingLp_combination μ f g a b ha hb⟩

/-- Original label: `prop:linear-parametrisation-convex`.
The actual Hilbert-valued image is closed under nonnegative combinations. -/
theorem range_linearEncodingLp_convexCone (μ : Measure PriceCurves.Parameter) [IsFiniteMeasure μ] :
    ConvexCone (range (linearEncodingLp μ)) := by
  letI : Nonempty Curve := ⟨unitRamp⟩
  exact (weaklyConvexOperator_iff_range_convexCone (linearEncodingLp μ)).mp
    (linearEncodingLp_weaklyConvex μ)

end Thesis.DayAhead.PLLinearCone
