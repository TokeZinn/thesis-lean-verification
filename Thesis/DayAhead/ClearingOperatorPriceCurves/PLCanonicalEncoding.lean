import Thesis.DayAhead.ClearingOperatorPriceCurves.PLParametrisation
import Thesis.DayAhead.ClearingOperatorPriceCurves.PolygonalInverse
import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedParametrisation

/-! # Intrinsic breakpoints and sided encodings of finite-affine curves

The node sets use actual failures of local affinity, rather than arbitrary
endpoints of an input partition. Thus redundant affine subdivision does not
enter the counts. The input is the pointwise representative selected by the
source; this module does not replace isolated values by one-sided limits.
-/

noncomputable section
namespace Thesis.DayAhead.PLCanonicalEncoding

open Set Filter Topology MeasureTheory PiecewiseAffinePriceCurves
open PriceCurves PriceCurveHilbert SidedParametrisation

def AffineNear (f : Curve) (x : ℝ) : Prop :=
  ∃ a b : ℝ, ∀ᶠ y in 𝓝 x, f.price y = a * y + b

def breakpoints (f : Curve) : Set ℝ :=
  {x | x ∈ Ioo f.leftEndpoint f.rightEndpoint ∧ x ≠ 0 ∧ ¬AffineNear f x}

theorem affineNear_on_core (f : Curve) (P : AffinePartition
    (Icc f.leftEndpoint f.rightEndpoint) f.price) (i : Fin P.count) {x : ℝ}
    (hx : x ∈ PolygonalInverse.sourceCell P i 0) : AffineNear f x := by
  change x ∈ P.piece i ∩ Ioo (sInf (P.piece i)) (sSup (P.piece i)) at hx
  obtain ⟨l, hl, hlx⟩ := (csInf_lt_iff (PolygonalInverse.piece_bddBelow P i) ⟨x, hx.1⟩).mp hx.2.1
  obtain ⟨r, hr, hxr⟩ := (lt_csSup_iff (PolygonalInverse.piece_bddAbove P i) ⟨x, hx.1⟩).mp hx.2.2
  obtain ⟨a, b, hab⟩ := P.affine i
  refine ⟨a, b, ?_⟩
  filter_upwards [Ioo_mem_nhds hlx hxr] with y hy
  exact hab y ((P.interval i).out hl hr ⟨hy.1.le, hy.2.le⟩)

theorem breakpoints_finite (f : Curve) : (breakpoints f).Finite := by
  let P := Classical.choice f.pieces
  apply ((Set.finite_range (fun i : Fin P.count => sInf (P.piece i))).union
    (Set.finite_range (fun i : Fin P.count => sSup (P.piece i)))).subset
  intro x hx
  obtain ⟨i, hi⟩ := (P.cover x).mp ⟨hx.1.1.le, hx.1.2.le⟩
  by_contra h
  have hl : sInf (P.piece i) < x := by
    have hle := csInf_le (PolygonalInverse.piece_bddBelow P i) hi
    apply lt_of_le_of_ne hle
    intro heq
    exact h (Or.inl ⟨i, heq⟩)
  have hr : x < sSup (P.piece i) := by
    have hle := le_csSup (PolygonalInverse.piece_bddAbove P i) hi
    apply lt_of_le_of_ne hle
    intro heq
    exact h (Or.inr ⟨i, heq.symm⟩)
  exact hx.2.2 (affineNear_on_core f P i (by
    simpa only [PolygonalInverse.sourceCell, ↓reduceIte] using And.intro hi ⟨hl, hr⟩))

def leftNodes (f : Curve) : Finset ℝ :=
  insert f.leftEndpoint (insert 0 ((breakpoints_finite f).toFinset.filter fun x => x < 0))

def rightNodes (f : Curve) : Finset ℝ :=
  insert 0 (insert f.rightEndpoint ((breakpoints_finite f).toFinset.filter fun x => 0 < x))

theorem leftNodes_nonempty (f : Curve) : (leftNodes f).Nonempty := by simp [leftNodes]
theorem rightNodes_nonempty (f : Curve) : (rightNodes f).Nonempty := by simp [rightNodes]

theorem leftNodes_bounds (f : Curve) {x : ℝ} (hx : x ∈ leftNodes f) :
    x ∈ Icc f.leftEndpoint 0 := by
  simp only [leftNodes, Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset] at hx
  rcases hx with rfl | rfl | ⟨hx, hx0⟩
  · exact ⟨le_rfl, f.left_nonpos⟩
  · exact ⟨f.left_nonpos, le_rfl⟩
  · exact ⟨hx.1.1.le, hx0.le⟩

theorem rightNodes_bounds (f : Curve) {x : ℝ} (hx : x ∈ rightNodes f) :
    x ∈ Icc 0 f.rightEndpoint := by
  simp only [rightNodes, Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset] at hx
  rcases hx with rfl | rfl | ⟨hx, hx0⟩
  · exact ⟨le_rfl, f.right_nonneg⟩
  · exact ⟨f.right_nonneg, le_rfl⟩
  · exact ⟨hx0.le, hx.1.2.le⟩

def count (s : Finset ℝ) : ℕ := s.card - 1

def enumeration (s : Finset ℝ) (hs : s.Nonempty) : Fin (count s + 1) ↪o ℝ :=
  s.orderEmbOfFin (by dsimp [count]; have := hs.card_pos; omega)

theorem enumeration_mem (s : Finset ℝ) (hs : s.Nonempty) (i : Fin (count s + 1)) :
    enumeration s hs i ∈ s := Finset.orderEmbOfFin_mem _ _ _

theorem enumeration_range (s : Finset ℝ) (hs : s.Nonempty) :
    Set.range (enumeration s hs) = s := Finset.range_orderEmbOfFin _ _

theorem enumeration_first (s : Finset ℝ) (hs : s.Nonempty) (a : ℝ)
    (ha : IsLeast (s : Set ℝ) a) : enumeration s hs 0 = a := by
  obtain ⟨i, hi⟩ := (enumeration_range s hs).symm ▸ ha.1
  exact le_antisymm (((enumeration s hs).monotone (Fin.zero_le i)).trans_eq hi)
    (ha.2 (enumeration_mem s hs 0))

theorem enumeration_last (s : Finset ℝ) (hs : s.Nonempty) (a : ℝ)
    (ha : IsGreatest (s : Set ℝ) a) : enumeration s hs (Fin.last (count s)) = a := by
  obtain ⟨i, hi⟩ := (enumeration_range s hs).symm ▸ ha.1
  exact le_antisymm (ha.2 (enumeration_mem s hs _))
    (hi ▸ (enumeration s hs).monotone (Fin.le_last i))

def leftCount (f : Curve) : ℕ := count (leftNodes f)
def rightCount (f : Curve) : ℕ := count (rightNodes f)
def leftKnot (f : Curve) : Fin (leftCount f + 1) → ℝ := enumeration _ (leftNodes_nonempty f)
def rightKnot (f : Curve) : Fin (rightCount f + 1) → ℝ := enumeration _ (rightNodes_nonempty f)

@[simp] theorem leftKnot_first (f : Curve) : leftKnot f 0 = f.leftEndpoint :=
  enumeration_first _ _ _ ⟨by simp [leftNodes], fun _ hx => (leftNodes_bounds f hx).1⟩

@[simp] theorem leftKnot_last (f : Curve) : leftKnot f (Fin.last (leftCount f)) = 0 :=
  enumeration_last _ _ _ ⟨by simp [leftNodes], fun _ hx => (leftNodes_bounds f hx).2⟩

@[simp] theorem rightKnot_first (f : Curve) : rightKnot f 0 = 0 :=
  enumeration_first _ _ _ ⟨by simp [rightNodes], fun _ hx => (rightNodes_bounds f hx).1⟩

@[simp] theorem rightKnot_last (f : Curve) :
    rightKnot f (Fin.last (rightCount f)) = f.rightEndpoint :=
  enumeration_last _ _ _ ⟨by simp [rightNodes], fun _ hx => (rightNodes_bounds f hx).2⟩

def quantityReal (f : Curve) (u : ℝ) : ℝ :=
  if u ≤ 0 then uniformInterpolation (leftKnot f) (u + 1)
  else uniformInterpolation (rightKnot f) u

theorem quantityReal_continuous (f : Curve) : Continuous (quantityReal f) := by
  apply ((continuous_uniformInterpolation _).comp (continuous_id.add continuous_const)).if_le
    (continuous_uniformInterpolation _) continuous_id continuous_const
  intro u hu
  have hu0 : u = 0 := by simpa using hu
  simp [hu0]

theorem quantityReal_monotone (f : Curve) : Monotone (quantityReal f) := by
  have hl := monotone_uniformInterpolation (leftKnot f)
    (enumeration _ (leftNodes_nonempty f)).monotone
  have hr := monotone_uniformInterpolation (rightKnot f)
    (enumeration _ (rightNodes_nonempty f)).monotone
  intro u v huv
  by_cases hu : u ≤ 0
  · by_cases hv : v ≤ 0
    · simp only [quantityReal, if_pos hu, if_pos hv]
      exact hl (by linarith)
    · simp only [quantityReal, if_pos hu, if_neg hv]
      have hleft : uniformInterpolation (leftKnot f) (u + 1) ≤ 0 := by
        simpa only [uniformInterpolation_one, leftKnot_last] using
          hl (show u + 1 ≤ 1 by linarith)
      have hright : 0 ≤ uniformInterpolation (rightKnot f) v := by
        simpa only [uniformInterpolation_zero, rightKnot_first] using
          hr (show 0 ≤ v from (lt_of_not_ge hv).le)
      exact hleft.trans hright
  · have hv : ¬v ≤ 0 := fun hv => hu (huv.trans hv)
    simp only [quantityReal, if_neg hu, if_neg hv]
    exact hr huv

@[simp] theorem quantityReal_left (f : Curve) : quantityReal f (-1) = f.leftEndpoint := by
  simp [quantityReal]

@[simp] theorem quantityReal_zero (f : Curve) : quantityReal f 0 = 0 := by
  simp [quantityReal]

@[simp] theorem quantityReal_right (f : Curve) : quantityReal f 1 = f.rightEndpoint := by
  simp [quantityReal]

def parametriser (f : Curve) : Parameter → Icc f.leftEndpoint f.rightEndpoint :=
  fun u => ⟨quantityReal f u, by
    constructor
    · simpa using quantityReal_monotone f u.property.1
    · simpa using quantityReal_monotone f u.property.2⟩

theorem parametriser_continuous (f : Curve) : Continuous (parametriser f) :=
  Continuous.subtype_mk ((quantityReal_continuous f).comp continuous_subtype_val) _

theorem parametriser_surjective (f : Curve) : Function.Surjective (parametriser f) := by
  intro x
  have hx : (x : ℝ) ∈ quantityReal f '' Icc (-1 : ℝ) 1 := by
    apply intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
      (quantityReal_continuous f).continuousOn
    simp only [quantityReal_left, quantityReal_right]
    exact x.property
  obtain ⟨u, hu, hux⟩ := hx
  exact ⟨⟨u, hu⟩, Subtype.ext hux⟩

def admissible (f : Curve) : PLParametrisation.Admissible f where
  toFun := parametriser f
  continuous := parametriser_continuous f
  monotone := fun _ _ h => quantityReal_monotone f h
  surjective := parametriser_surjective f
  zero := quantityReal_zero f

def encoding (f : Curve) : Parameter → ℝ × ℝ :=
  PLParametrisation.graphRepresentative f (admissible f)

def encodingLp (μ : Measure Parameter) [IsFiniteMeasure μ] (f : Curve) :
    PriceHilbertSpace μ := PLParametrisation.encodingLp μ f (admissible f)

theorem encoding_range (f : Curve) : Set.range (encoding f) = f.graph :=
  PLParametrisation.range_graphRepresentative f (admissible f)

end Thesis.DayAhead.PLCanonicalEncoding
