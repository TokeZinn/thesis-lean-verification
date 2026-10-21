import Thesis.DayAhead.ClearingOperatorPriceCurves.PLLinearCone
import Thesis.DayAhead.ClearingOperatorPriceCurves.PolygonalInverse
import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialEncodingInjectivity

/-! # Graph tracing for the full finite-affine curve carrier

Unlike the older simple-curve implementation, neither coordinate is required
to have finite range. Affine partitions refer to actual functions before the
passage to almost-everywhere equivalence classes.
-/

noncomputable section
namespace Thesis.DayAhead.PLGraphTracing

open Set Filter Topology MeasureTheory PriceCurves PiecewiseAffinePriceCurves
open PriceCurveHilbert PLLinearCone
open SidedParametrisation

/-- Original label: `defn:graph-tracing-pairs`, conditions (1)--(3). -/
structure Pair where
  volume : Parameter → ℝ
  price : Parameter → ℝ
  volume_continuous : Continuous volume
  volume_monotone : Monotone volume
  volume_zero : volume parameterZero = 0
  price_monotone : Monotone price
  fiber_const : ∀ {u v}, volume u = volume v → price u = price v
  volume_pieces : Nonempty (AffinePartition (Icc (-1 : ℝ) 1)
    (fun x => volume (clampParameter x)))
  price_pieces : Nonempty (AffinePartition (Icc (-1 : ℝ) 1)
    (fun x => price (clampParameter x)))

theorem Pair.exists_terminalStart (f : Pair) :
    ∃ u : Parameter, IsLeast {u | f.volume u = f.volume parameterRight} u :=
  (isClosed_eq f.volume_continuous continuous_const).isCompact.exists_isLeast
    ⟨parameterRight, rfl⟩

def Pair.terminalStart (f : Pair) : Parameter := Classical.choose f.exists_terminalStart

theorem Pair.terminalStart_isLeast (f : Pair) :
    IsLeast {u | f.volume u = f.volume parameterRight} f.terminalStart :=
  Classical.choose_spec f.exists_terminalStart

theorem Pair.terminal_iff (f : Pair) (u : Parameter) :
    f.volume u = f.volume parameterRight ↔ f.terminalStart ≤ u := by
  constructor
  · exact fun h => f.terminalStart_isLeast.2 h
  · intro h
    exact le_antisymm (f.volume_monotone u.property.2)
      (f.terminalStart_isLeast.1 ▸ f.volume_monotone h)

theorem Pair.terminal_price (f : Pair) {u v : Parameter}
    (hu : f.terminalStart ≤ u) (hv : f.terminalStart ≤ v) : f.price u = f.price v :=
  f.fiber_const (((f.terminal_iff u).mpr hu).trans ((f.terminal_iff v).mpr hv).symm)

/-- Original label: `defn:graph-tracing-pairs`, including the actual sided
representative convention (4). Within-continuity at an extreme endpoint is
automatic, so this includes the source's conditional terminal convention. -/
structure TracingPair extends Pair where
  price_right : ∀ u, ContinuousWithinAt price (Ici u) u
  price_terminal : ContinuousWithinAt price (Iic toPair.terminalStart) toPair.terminalStart

theorem Pair.terminalStart_eq_inf (f : Pair) :
    (f.terminalStart : ℝ) = sInf {u : ℝ | ∃ hu : u ∈ Icc (-1 : ℝ) 1,
      f.volume ⟨u, hu⟩ = f.volume parameterRight} := by
  symm
  apply IsLeast.csInf_eq
  exact ⟨⟨f.terminalStart.property, f.terminalStart_isLeast.1⟩,
    fun _ ⟨_, h⟩ => f.terminalStart_isLeast.2 h⟩

theorem TracingPair.price_left_at_terminal (f : TracingPair) (u : Parameter)
    (hu : f.volume u = f.volume parameterRight) :
    ContinuousWithinAt f.price (Iic u) u := by
  have hle := (f.toPair.terminal_iff u).mp hu
  rcases hle.eq_or_lt with h | h
  · simpa only [← h] using f.price_terminal
  · apply continuousWithinAt_const.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds (s := Iic u)) (Ioi_mem_nhds h)] with v _ hv
      exact f.toPair.terminal_price hv.le hle
    · rfl

def combination (a b : ℝ) (f g : Pair) (ha : 0 ≤ a) (hb : 0 ≤ b) : Pair where
  volume u := a * f.volume u + b * g.volume u
  price u := a * f.price u + b * g.price u
  volume_continuous := (continuous_const.mul f.volume_continuous).add
    (continuous_const.mul g.volume_continuous)
  volume_monotone := (f.volume_monotone.const_mul ha).add (g.volume_monotone.const_mul hb)
  volume_zero := by simp only [f.volume_zero, g.volume_zero, mul_zero, add_zero]
  price_monotone := (f.price_monotone.const_mul ha).add (g.price_monotone.const_mul hb)
  fiber_const := by
    intro u v huv
    wlog h : u ≤ v generalizing u v
    · exact (this huv.symm (le_of_not_ge h)).symm
    have hf := f.volume_monotone h
    have hg := g.volume_monotone h
    have hfd := mul_nonneg ha (sub_nonneg.mpr hf)
    have hgd := mul_nonneg hb (sub_nonneg.mpr hg)
    have hfp : a * f.price u = a * f.price v := by
      by_cases hzero : a = 0
      · simp [hzero]
      · have he : a * (f.volume v - f.volume u) = 0 := by nlinarith
        have heq : f.volume u = f.volume v := by
          have := (mul_eq_zero.mp he).resolve_left hzero
          linarith
        rw [f.fiber_const heq]
    have hgp : b * g.price u = b * g.price v := by
      by_cases hzero : b = 0
      · simp [hzero]
      · have he : b * (g.volume v - g.volume u) = 0 := by nlinarith
        have heq : g.volume u = g.volume v := by
          have := (mul_eq_zero.mp he).resolve_left hzero
          linarith
        rw [g.fiber_const heq]
    rw [hfp, hgp]
  volume_pieces := ⟨by
    simpa only [inter_self] using
      (Classical.choice f.volume_pieces).combine (Classical.choice g.volume_pieces) a b⟩
  price_pieces := ⟨by
    simpa only [inter_self] using
      (Classical.choice f.price_pieces).combine (Classical.choice g.price_pieces) a b⟩

theorem terminal_components (a b : ℝ) (f g : Pair) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : Parameter) (hu : (combination a b f g ha hb).volume u =
      (combination a b f g ha hb).volume parameterRight) :
    (0 < a → f.volume u = f.volume parameterRight) ∧
    (0 < b → g.volume u = g.volume parameterRight) := by
  have hf := f.volume_monotone (show u ≤ parameterRight from u.property.2)
  have hg := g.volume_monotone (show u ≤ parameterRight from u.property.2)
  change a * f.volume u + b * g.volume u =
    a * f.volume parameterRight + b * g.volume parameterRight at hu
  have hfd := mul_nonneg ha (sub_nonneg.mpr hf)
  have hgd := mul_nonneg hb (sub_nonneg.mpr hg)
  constructor
  · intro ha'
    have he : a * (f.volume parameterRight - f.volume u) = 0 := by nlinarith
    have := (mul_eq_zero.mp he).resolve_left ha'.ne'
    linarith
  · intro hb'
    have he : b * (g.volume parameterRight - g.volume u) = 0 := by nlinarith
    have := (mul_eq_zero.mp he).resolve_left hb'.ne'
    linarith

/-- Original label: `prop:admissible-parametrisations-cone`.
All four graph-tracing conditions are preserved, including zero coefficients
and the first point of the terminal plateau. -/
def tracingCombination (a b : ℝ) (f g : TracingPair) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    TracingPair where
  toPair := combination a b f.toPair g.toPair ha hb
  price_right u := (continuousWithinAt_const.mul (f.price_right u)).add
    (continuousWithinAt_const.mul (g.price_right u))
  price_terminal := by
    let c := combination a b f.toPair g.toPair ha hb
    have ht := terminal_components a b f.toPair g.toPair ha hb c.terminalStart
      c.terminalStart_isLeast.1
    have hf : ContinuousWithinAt (fun u => a * f.price u)
        (Iic c.terminalStart) c.terminalStart := by
      rcases ha.eq_or_lt with h | h
      · simp only [← h, zero_mul]; exact continuousWithinAt_const
      · exact continuousWithinAt_const.mul (f.price_left_at_terminal _ (ht.1 h))
    have hg : ContinuousWithinAt (fun u => b * g.price u)
        (Iic c.terminalStart) c.terminalStart := by
      rcases hb.eq_or_lt with h | h
      · simp only [← h, zero_mul]; exact continuousWithinAt_const
      · exact continuousWithinAt_const.mul (g.price_left_at_terminal _ (ht.2 h))
    exact hf.add hg

def representative (f : TracingPair) : Parameter → ℝ × ℝ := fun u => (f.volume u, f.price u)

theorem range_representative_convexCone :
    Foundations.Stochastic.KernelHilbert.ConvexCone (range representative) := by
  rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩ a b ha hb
  exact ⟨tracingCombination a b f g ha hb, rfl⟩

def Pair.Domain (f : Pair) : Set ℝ := Icc (f.volume parameterLeft) (f.volume parameterRight)

theorem Pair.range_volume (f : Pair) : range f.volume = f.Domain := by
  apply Subset.antisymm
  · rintro x ⟨u, rfl⟩
    exact ⟨f.volume_monotone u.property.1, f.volume_monotone u.property.2⟩
  · intro x hx
    let E : ℝ → ℝ := fun u => f.volume (clampParameter u)
    have hc : Continuous E := f.volume_continuous.comp SidedCurveLp.continuous_clampParameter
    have hl : E (-1) = f.volume parameterLeft := by
      change f.volume (clampParameter (parameterLeft : ℝ)) = _
      rw [CanonicalSidedLp.clampParameter_coe]
    have hr : E 1 = f.volume parameterRight := by
      change f.volume (clampParameter (parameterRight : ℝ)) = _
      rw [CanonicalSidedLp.clampParameter_coe]
    have hxi : x ∈ E '' Icc (-1 : ℝ) 1 := by
      apply intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num) hc.continuousOn
      rwa [hl, hr]
    obtain ⟨u, _, hu⟩ := hxi
    exact ⟨clampParameter u, hu⟩

def Pair.domainPoint (f : Pair) (u : Parameter) : f.Domain :=
  ⟨f.volume u, f.volume_monotone u.property.1, f.volume_monotone u.property.2⟩

theorem Pair.preimage_nonempty (f : Pair) (x : ℝ) (hx : x ∈ f.Domain) :
    ∃ u, f.volume u = x := by
  change x ∈ range f.volume
  rwa [f.range_volume]

/-- The fiber-defined source decoder. Choice of a preimage cannot affect it. -/
def Pair.decode (f : Pair) (x : f.Domain) : ℝ :=
  f.price (Classical.choose (f.preimage_nonempty x x.property))

theorem Pair.decode_eq_of_volume (f : Pair) (x : f.Domain) (u : Parameter)
    (hu : f.volume u = x) : f.decode x = f.price u := by
  exact f.fiber_const ((Classical.choose_spec (f.preimage_nonempty x x.property)).trans hu.symm)

@[simp] theorem Pair.decode_domainPoint (f : Pair) (u : Parameter) :
    f.decode (f.domainPoint u) = f.price u := f.decode_eq_of_volume _ u rfl

theorem Pair.decode_monotone (f : Pair) : Monotone f.decode := by
  intro x y hxy
  obtain ⟨u, hu⟩ := f.preimage_nonempty x x.property
  obtain ⟨v, hv⟩ := f.preimage_nonempty y y.property
  rw [f.decode_eq_of_volume x u hu, f.decode_eq_of_volume y v hv]
  rcases le_total u v with huv | hvu
  · exact f.price_monotone huv
  · have he : (x : ℝ) = y := le_antisymm hxy (by simpa [hu, hv] using f.volume_monotone hvu)
    exact (f.fiber_const (hu.trans (he.trans hv.symm))).le

theorem Pair.decode_unique (f : Pair) (h : f.Domain → ℝ)
    (hh : ∀ u, h (f.domainPoint u) = f.price u) : h = f.decode := by
  funext x
  obtain ⟨u, hu⟩ := f.preimage_nonempty x x.property
  have hx : x = f.domainPoint u := Subtype.ext hu.symm
  rw [hx, hh, f.decode_domainPoint]

/-- Composition of finite-affine functions along a monotone inner map.
The cells are an actual disjoint common refinement, including flat pieces. -/
def composePartition {D S : Set ℝ} {f g : ℝ → ℝ}
    (P : AffinePartition D f) (Q : AffinePartition S g)
    (hf : MonotoneOn f D) (hmem : ∀ x ∈ D, f x ∈ S) :
    AffinePartition D (fun x => g (f x)) where
  count := Fintype.card (Fin P.count × Fin Q.count)
  piece := fun k =>
    let ij := (Fintype.equivFin (Fin P.count × Fin Q.count)).symm k
    P.piece ij.1 ∩ f ⁻¹' Q.piece ij.2
  interval := fun k =>
    let ij := (Fintype.equivFin (Fin P.count × Fin Q.count)).symm k
    PolygonalInverse.interval_preimage_monotoneOn (P.interval ij.1) (Q.interval ij.2)
      (hf.mono (P.piece_subset ij.1))
  disjoint := by
    intro k l hkl
    let e := Fintype.equivFin (Fin P.count × Fin Q.count)
    have hne : e.symm k ≠ e.symm l := fun h => hkl (e.symm.injective h)
    by_cases hfst : (e.symm k).1 = (e.symm l).1
    · exact ((Q.disjoint _ _ (fun h => hne (Prod.ext hfst h))).preimage _).mono
        inter_subset_right inter_subset_right
    · exact (P.disjoint _ _ hfst).mono inter_subset_left inter_subset_left
  cover := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (P.cover x).mp hx
      obtain ⟨j, hj⟩ := (Q.cover (f x)).mp (hmem x hx)
      exact ⟨Fintype.equivFin _ (i, j), by simpa using And.intro hi hj⟩
    · rintro ⟨k, hk⟩
      exact P.piece_subset _ hk.1
  affine := by
    intro k
    let ij := (Fintype.equivFin (Fin P.count × Fin Q.count)).symm k
    obtain ⟨a, b, hi⟩ := P.affine ij.1
    obtain ⟨c, d, hj⟩ := Q.affine ij.2
    refine ⟨c * a, c * b + d, fun x hx => ?_⟩
    rw [hj (f x) hx.2, hi x hx.1]
    ring

def Pair.extendedVolume (f : Pair) : ℝ → ℝ := fun x => f.volume (clampParameter x)

theorem Pair.extendedVolume_continuous (f : Pair) : Continuous f.extendedVolume :=
  f.volume_continuous.comp SidedCurveLp.continuous_clampParameter

theorem Pair.extendedVolume_monotone (f : Pair) : Monotone f.extendedVolume := by
  intro x y hxy
  apply f.volume_monotone
  change max (-1 : ℝ) (min 1 x) ≤ max (-1 : ℝ) (min 1 y)
  exact max_le_max_left _ (min_le_min_left _ hxy)

theorem Pair.levelSet_nonempty (f : Pair) (x : ℝ) (hx : x ∈ f.Domain) :
    (CompletedInverse.levelSet (-1) 1 f.extendedVolume x).Nonempty := by
  obtain ⟨u, hu⟩ := f.preimage_nonempty x hx
  refine ⟨u, u.property, ?_⟩
  have hc := f.extendedVolume_continuous.continuousAt (x := (u : ℝ))
  rw [hc.continuousWithinAt.leftLim_eq, hc.continuousWithinAt.rightLim_eq]
  have he : f.extendedVolume u = x := by
    simpa only [extendedVolume, CanonicalSidedLp.clampParameter_coe] using hu
  exact ⟨he.le, he.ge⟩

def Pair.inverseVolume (f : Pair) : ℝ → ℝ :=
  CompletedInverse.midpointPrice (-1) 1 f.extendedVolume

theorem Pair.inverseVolume_mem (f : Pair) (x : ℝ) (hx : x ∈ f.Domain) :
    f.inverseVolume x ∈ Icc (-1 : ℝ) 1 :=
  (CompletedInverse.midpointPrice_mem_levelSet (-1) 1 f.extendedVolume
    f.extendedVolume_monotone x (f.levelSet_nonempty x hx)).1

theorem Pair.inverseVolume_eq (f : Pair) (x : ℝ) (hx : x ∈ f.Domain) :
    f.volume (clampParameter (f.inverseVolume x)) = x := by
  have hm := CompletedInverse.midpointPrice_mem_levelSet (-1) 1 f.extendedVolume
    f.extendedVolume_monotone x (f.levelSet_nonempty x hx)
  have hc := f.extendedVolume_continuous.continuousAt (x := f.inverseVolume x)
  change f.extendedVolume (f.inverseVolume x) = x
  have hm' : f.extendedVolume.leftLim (f.inverseVolume x) ≤ x ∧
      x ≤ f.extendedVolume.rightLim (f.inverseVolume x) := hm.2
  rw [hc.continuousWithinAt.leftLim_eq, hc.continuousWithinAt.rightLim_eq] at hm'
  exact le_antisymm hm'.1 hm'.2

theorem Pair.inverseVolume_monotone (f : Pair) : MonotoneOn f.inverseVolume f.Domain :=
  CompletedInverse.midpointPrice_monotoneOn (-1) 1 f.extendedVolume
    f.extendedVolume_monotone f.Domain f.levelSet_nonempty

def Pair.inverseVolumePartition (f : Pair) : AffinePartition f.Domain f.inverseVolume :=
  PolygonalInverse.inversePartition (Classical.choice f.volume_pieces)
    f.extendedVolume_monotone f.Domain ordConnected_Icc f.levelSet_nonempty

def Pair.decodedReal (f : Pair) : ℝ → ℝ := fun x => f.price (clampParameter (f.inverseVolume x))

theorem Pair.decodedReal_eq_decode (f : Pair) (x : f.Domain) :
    f.decodedReal x = f.decode x :=
  (f.decode_eq_of_volume x _ (f.inverseVolume_eq x x.property)).symm

def Pair.decodedPartition (f : Pair) : AffinePartition f.Domain f.decodedReal := by
  exact composePartition (f := f.inverseVolume)
    (g := fun x => f.price (clampParameter x)) f.inverseVolumePartition
    (Classical.choice f.price_pieces) f.inverseVolume_monotone f.inverseVolume_mem

/-- Original label: `prop:admissible-parametrisations-cone`.
The fiber decoder lands in the actual full finite-affine curve carrier. -/
def Pair.decodedCurve (f : Pair) : Curve where
  leftEndpoint := f.volume parameterLeft
  rightEndpoint := f.volume parameterRight
  left_nonpos := f.volume_zero ▸ f.volume_monotone
    (show parameterLeft ≤ parameterZero by norm_num [parameterLeft, parameterZero])
  right_nonneg := f.volume_zero ▸ f.volume_monotone
    (show parameterZero ≤ parameterRight by norm_num [parameterZero, parameterRight])
  price := f.decodedReal
  monotone := by
    intro x hx y hy hxy
    rw [f.decodedReal_eq_decode ⟨x, hx⟩, f.decodedReal_eq_decode ⟨y, hy⟩]
    exact f.decode_monotone hxy
  pieces := ⟨f.decodedPartition⟩

theorem Pair.decodedCurve_graph (f : Pair) : f.decodedCurve.graph =
    range (fun u => (f.volume u, f.price u)) := by
  ext z
  constructor
  · rintro ⟨hz, he⟩
    obtain ⟨u, hu⟩ := f.preimage_nonempty z.1 hz
    refine ⟨u, Prod.ext hu ?_⟩
    have hd := f.decode_eq_of_volume ⟨z.1, hz⟩ u hu
    rw [← f.decodedReal_eq_decode] at hd
    exact hd.symm.trans he.symm
  · rintro ⟨u, rfl⟩
    refine ⟨(f.domainPoint u).property, ?_⟩
    exact ((f.decodedReal_eq_decode (f.domainPoint u)).trans (f.decode_domainPoint u)).symm

theorem Pair.decodedCurve_simple (f : Pair) (hp : (range f.price).Finite) :
    f.decodedCurve.IsSimple :=
  hp.subset (by rintro _ ⟨x, _, rfl⟩; exact ⟨_, rfl⟩)

variable (μ : Measure Parameter) [IsFiniteMeasure μ]

theorem representative_memLp (f : TracingPair) : MemLp (representative f) 2 μ := by
  let Q := max |f.volume parameterLeft| |f.volume parameterRight|
  let P := max |f.price parameterLeft| |f.price parameterRight|
  have hm : Measurable (representative f) :=
    Measurable.prod f.volume_monotone.measurable f.price_monotone.measurable
  refine MemLp.of_bound hm.aestronglyMeasurable (max Q P) (Eventually.of_forall fun u => ?_)
  rw [representative, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  apply max_le
  · exact (abs_le_max_abs_abs (f.volume_monotone u.property.1)
      (f.volume_monotone u.property.2)).trans (le_max_left Q P)
  · exact (abs_le_max_abs_abs (f.price_monotone u.property.1)
      (f.price_monotone u.property.2)).trans (le_max_right Q P)

theorem euclidean_memLp (f : TracingPair) :
    MemLp (pairEquiv ∘ representative f) 2 μ :=
  pairEquiv.toContinuousLinearMap.comp_memLp' (representative_memLp μ f)

def encodingLp (f : TracingPair) : PriceHilbertSpace μ := (euclidean_memLp μ f).toLp _

theorem representative_combination (a b : ℝ) (f g : TracingPair)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    representative (tracingCombination a b f g ha hb) =
      a • representative f + b • representative g := rfl

theorem encodingLp_combination (a b : ℝ) (f g : TracingPair)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    encodingLp μ (tracingCombination a b f g ha hb) =
      a • encodingLp μ f + b • encodingLp μ g := by
  apply Lp.ext
  filter_upwards [(euclidean_memLp μ (tracingCombination a b f g ha hb)).coeFn_toLp,
    (euclidean_memLp μ f).coeFn_toLp, (euclidean_memLp μ g).coeFn_toLp,
    Lp.coeFn_add (a • encodingLp μ f) (b • encodingLp μ g),
    Lp.coeFn_smul a (encodingLp μ f), Lp.coeFn_smul b (encodingLp μ g)]
    with u hc hf hg hadd hsmulf hsmulg
  rw [hadd, Pi.add_apply, hsmulf, hsmulg]
  change _ = a • ((euclidean_memLp μ f).toLp _) u +
    b • ((euclidean_memLp μ g).toLp _) u
  rw [hf, hg]
  change ((euclidean_memLp μ _).toLp _) u = _
  rw [hc]
  simp only [Function.comp_apply, representative_combination,
    Pi.add_apply, Pi.smul_apply, map_add, map_smul]

/-- Original label: `prop:admissible-parametrisations-cone`.
The actual full-affine representative family also forms a cone in the
Euclidean-valued L² quotient used by the thesis. -/
theorem range_encodingLp_convexCone :
    Foundations.Stochastic.KernelHilbert.ConvexCone (range (encodingLp μ)) := by
  rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩ a b ha hb
  exact ⟨tracingCombination a b f g ha hb, encodingLp_combination μ a b f g ha hb⟩

end Thesis.DayAhead.PLGraphTracing
