import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc

/-!
# Day-ahead price curves

Finite-level supporting submodel of the construction in
`2 - day-ahead/2_clearing_operator_price_curves.tex`.

The central distinction is represented directly: `GraphAdmissiblePair` is the
larger class of actual representatives that can be decoded graph-wise.  It is
closed under nonnegative combinations.  This does not assert that a canonical
sided re-encoding is closed under those combinations.
-/

namespace Thesis
namespace DayAhead
namespace PriceCurves

open Set
open scoped BigOperators

universe u

/-! ## Graph-admissible representatives -/

/-- Common parameter interval used by all price-curve representatives. -/
abbrev Parameter := Set.Icc (-1 : ℝ) 1

/-- The distinguished zero parameter. -/
def parameterZero : Parameter := ⟨0, by constructor <;> norm_num⟩

/-- Endpoints of the common parameter interval. -/
def parameterLeft : Parameter := ⟨-1, by constructor <;> norm_num⟩
def parameterRight : Parameter := ⟨1, by constructor <;> norm_num⟩

/-! ## Price curves and admissible parametrisations -/

/-!
Thesis source: the four market-derived price-curve claims immediately before
Section `sec:price-curves-as-space` in the current chapter.

The current piecewise-affine class is broader. This finite-level carrier
represents its simple elements; `claim:pw-affine` is not proved for the
current interpolated market by this module.

Lean coverage note: the abstract `PriceCurve` carrier below encodes compact
interval domains containing zero, monotonicity, and finitely many price
levels, and `exists_minimalRepresentation` derives the disjoint interval
decomposition. These carrier fields formalize the simple submodel. They are not proofs
that an actual venue or an arbitrary clearing
implementation produces such a price curve.
-/

/-- A finite-level monotone price curve on a compact interval containing
zero. The interval is part of the data, so different curves may have different
domains exactly as in the manuscript. -/
structure PriceCurve where
  leftEndpoint : ℝ
  rightEndpoint : ℝ
  leftEndpoint_nonpos : leftEndpoint ≤ 0
  rightEndpoint_nonneg : 0 ≤ rightEndpoint
  price : Set.Icc leftEndpoint rightEndpoint → ℝ
  price_monotone : Monotone price
  price_finite : (Set.range price).Finite

/-- Finite minimal-block data for a price curve.  Ordering is stated directly
pointwise, avoiding endpoint-convention choices for singleton blocks. -/
structure MinimalRepresentation (f : PriceCurve) where
  blockCount : ℕ
  blockCount_pos : 0 < blockCount
  cell : Fin blockCount → Set (Set.Icc f.leftEndpoint f.rightEndpoint)
  level : Fin blockCount → ℝ
  cell_nonempty : ∀ i, (cell i).Nonempty
  cell_disjoint : Set.PairwiseDisjoint Set.univ cell
  cell_cover : ⋃ i, cell i = Set.univ
  cell_ordConnected : ∀ i, (cell i).OrdConnected
  cell_ordered : ∀ i j, i < j → ∀ x ∈ cell i, ∀ y ∈ cell j, x ≤ y
  level_strictMono : StrictMono level
  represents : ∀ x, f.price x =
    ∑ i, (cell i).indicator (fun _ => level i) x

/--
Thesis source: equations `eq:minimal-representation` and
`eq:minimal-rep-order`.

Original labels: `eq:minimal-representation`, `eq:minimal-rep-order`.

Lean strategy / thesis relation note: order the finite range increasingly and
take the nonempty fibres of the price function. Monotonicity forces those
fibres to occur in the same order as their levels.
-/
theorem exists_minimalRepresentation (f : PriceCurve) :
    Nonempty (MinimalRepresentation f) := by
  classical
  let values : Finset ℝ := f.price_finite.toFinset
  have hmem_values (y : ℝ) : y ∈ values ↔ y ∈ Set.range f.price := by
    simp only [values, Set.Finite.mem_toFinset]
  have hvalues_nonempty : values.Nonempty := by
    let x0 : Set.Icc f.leftEndpoint f.rightEndpoint :=
      ⟨0, f.leftEndpoint_nonpos, f.rightEndpoint_nonneg⟩
    refine ⟨f.price x0, ?_⟩
    exact hmem_values _ |>.2 ⟨x0, rfl⟩
  let level : Fin values.card → ℝ := values.orderEmbOfFin rfl
  let cell : Fin values.card → Set (Set.Icc f.leftEndpoint f.rightEndpoint) :=
    fun i => {x | f.price x = level i}
  have hlevel_mem (i : Fin values.card) : level i ∈ values := by
    exact (values.orderIsoOfFin rfl i).2
  have hlevel_strict : StrictMono level := by
    exact (values.orderEmbOfFin rfl).strictMono
  refine ⟨{
    blockCount := values.card
    blockCount_pos := Finset.card_pos.mpr hvalues_nonempty
    cell := cell
    level := level
    cell_nonempty := ?_
    cell_disjoint := ?_
    cell_cover := ?_
    cell_ordConnected := ?_
    cell_ordered := ?_
    level_strictMono := hlevel_strict
    represents := ?_ }⟩
  · intro i
    obtain ⟨x, hx⟩ := hmem_values (level i) |>.1 (hlevel_mem i)
    exact ⟨x, hx⟩
  · intro i _hi j _hj hij
    change Disjoint (cell i) (cell j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    exact (values.orderEmbOfFin rfl).injective <| by
      simpa only [cell, Set.mem_setOf_eq] using hxi.symm.trans hxj
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := (values.orderIsoOfFin rfl).surjective
      ⟨f.price x, hmem_values _ |>.2 ⟨x, rfl⟩⟩
    apply Set.mem_iUnion.2
    refine ⟨i, ?_⟩
    simpa only [cell, level, Set.mem_setOf_eq] using
      (congrArg Subtype.val hi).symm
  · intro i
    apply Set.ordConnected_iff.mpr
    intro x hx y hy hxy z hz
    simp only [cell, Set.mem_setOf_eq] at hx hy ⊢
    have hxz := f.price_monotone hz.1
    have hzy := f.price_monotone hz.2
    rw [hx] at hxz
    rw [hy] at hzy
    exact le_antisymm hzy hxz
  · intro i j hij x hxi y hyj
    by_contra hxy
    have hyx : y ≤ x := le_of_not_ge hxy
    have hprice := f.price_monotone hyx
    have hlevels : level i < level j := hlevel_strict hij
    simp only [cell, Set.mem_setOf_eq] at hxi hyj
    rw [hxi, hyj] at hprice
    exact (not_le_of_gt hlevels) hprice
  · intro x
    obtain ⟨i, hi⟩ := (values.orderIsoOfFin rfl).surjective
      ⟨f.price x, hmem_values _ |>.2 ⟨x, rfl⟩⟩
    have hlevel : level i = f.price x := by
      simpa only [level] using congrArg Subtype.val hi
    rw [Finset.sum_eq_single i]
    · simp only [Set.indicator_apply, cell, Set.mem_setOf_eq, hlevel, if_pos]
    · intro j _hj hji
      have hne : f.price x ≠ level j := by
        intro heq
        apply hji
        apply (values.orderEmbOfFin rfl).injective
        change level j = level i
        rw [← heq, hlevel]
      simp only [Set.indicator_apply, cell, Set.mem_setOf_eq, hne, if_false]
    · intro hi_not
      exact (hi_not (Finset.mem_univ i)).elim

/-- The zero point in the domain of a price curve. -/
def PriceCurve.domainZero (f : PriceCurve) :
    Set.Icc f.leftEndpoint f.rightEndpoint :=
  ⟨0, f.leftEndpoint_nonpos, f.rightEndpoint_nonneg⟩

/-- The degenerate zero-domain, zero-price curve.  Besides being a useful
boundary object, it witnesses that the price-curve family is nonempty. -/
def zeroPriceCurve : PriceCurve where
  leftEndpoint := 0
  rightEndpoint := 0
  leftEndpoint_nonpos := le_rfl
  rightEndpoint_nonneg := le_rfl
  price := 0
  price_monotone := monotone_const
  price_finite := by
    change (Set.range (fun _ : Set.Icc (0 : ℝ) 0 => (0 : ℝ))).Finite
    exact Set.finite_range_const

instance : Nonempty PriceCurve := ⟨zeroPriceCurve⟩

/--
Thesis source:
`2 - day-ahead/2_clearing_operator_price_curves.tex`, Definition
`defn:admissible-price-curve-parametrisation`.

Original label: `defn:admissible-price-curve-parametrisation`.

An admissible parametrisation is a continuous monotone surjection from the
common parameter interval onto the curve's own compact domain, sending zero to
zero.
-/
structure AdmissibleParametrisation (f : PriceCurve) where
  toFun : Parameter → Set.Icc f.leftEndpoint f.rightEndpoint
  continuous : Continuous toFun
  monotone : Monotone toFun
  surjective : Function.Surjective toFun
  map_zero : toFun parameterZero = f.domainZero

instance (f : PriceCurve) : CoeFun (AdmissibleParametrisation f)
    (fun _ => Parameter → Set.Icc f.leftEndpoint f.rightEndpoint) :=
  ⟨AdmissibleParametrisation.toFun⟩

/-- The actual parametrised graph selected by an admissible parametrisation. -/
def parametrisedGraph (f : PriceCurve) (a : AdmissibleParametrisation f) :
    Parameter → ℝ × ℝ :=
  fun u => ((a u : ℝ), f.price (a u))

/--
An actual pair `(a,b)` that traces the graph of a finite-level monotone price
curve.  `fiber_const` is precisely the condition needed to decode `b` as a
function of the volume coordinate `a`.

The finite-range field is the Lean formulation of the manuscript's `simple`
condition.  Endpoint conventions are retained because these are actual
functions, not `L²` equivalence classes.
-/
structure GraphAdmissiblePair where
  volume : Parameter → ℝ
  price : Parameter → ℝ
  volume_continuous : Continuous volume
  volume_monotone : Monotone volume
  volume_zero : volume parameterZero = 0
  price_monotone : Monotone price
  price_finite : (Set.range price).Finite
  fiber_const : ∀ ⦃u v⦄, volume u = volume v → price u = price v

/-- Every admissibly parametrised price curve gives a graph-admissible pair. -/
def AdmissibleParametrisation.toGraphAdmissiblePair
    (f : PriceCurve) (a : AdmissibleParametrisation f) : GraphAdmissiblePair where
  volume u := a u
  price u := f.price (a u)
  volume_continuous := continuous_subtype_val.comp a.continuous
  volume_monotone := fun _ _ huv => a.monotone huv
  volume_zero := by simp [a.map_zero, PriceCurve.domainZero]
  price_monotone := fun _ _ huv => f.price_monotone (a.monotone huv)
  price_finite := by
    refine f.price_finite.subset ?_
    rintro y ⟨u, rfl⟩
    exact ⟨a u, rfl⟩
  fiber_const := by
    intro u v huv
    have huv' : a u = a v := Subtype.ext huv
    rw [huv']

/-- Nonnegative pointwise combination of two actual representatives. -/
def conicCombination (α β : ℝ) (f g : GraphAdmissiblePair)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : GraphAdmissiblePair where
  volume u := α * f.volume u + β * g.volume u
  price u := α * f.price u + β * g.price u
  volume_continuous :=
    (continuous_const.mul f.volume_continuous).add
      (continuous_const.mul g.volume_continuous)
  volume_monotone := by
    intro u v huv
    exact add_le_add
      (mul_le_mul_of_nonneg_left (f.volume_monotone huv) hα)
      (mul_le_mul_of_nonneg_left (g.volume_monotone huv) hβ)
  volume_zero := by simp [f.volume_zero, g.volume_zero]
  price_monotone := by
    intro u v huv
    exact add_le_add
      (mul_le_mul_of_nonneg_left (f.price_monotone huv) hα)
      (mul_le_mul_of_nonneg_left (g.price_monotone huv) hβ)
  price_finite := by
    let S : Set (ℝ × ℝ) := Set.range f.price ×ˢ Set.range g.price
    have hS : S.Finite := f.price_finite.prod g.price_finite
    refine (hS.image (fun p : ℝ × ℝ => α * p.1 + β * p.2)).subset ?_
    rintro y ⟨u, rfl⟩
    refine ⟨(f.price u, g.price u), ?_, rfl⟩
    exact ⟨⟨u, rfl⟩, ⟨u, rfl⟩⟩
  fiber_const := by
    intro u v huv
    have aux : ∀ {x y : Parameter}, x ≤ y →
        α * f.volume x + β * g.volume x =
          α * f.volume y + β * g.volume y →
        α * f.price x + β * g.price x =
          α * f.price y + β * g.price y := by
      intro x y hxy hvol
      have hfmono := f.volume_monotone hxy
      have hgmono := g.volume_monotone hxy
      have hfdiff : 0 ≤ f.volume y - f.volume x := sub_nonneg.mpr hfmono
      have hgdiff : 0 ≤ g.volume y - g.volume x := sub_nonneg.mpr hgmono
      have hαdiff : 0 ≤ α * (f.volume y - f.volume x) := mul_nonneg hα hfdiff
      have hβdiff : 0 ≤ β * (g.volume y - g.volume x) := mul_nonneg hβ hgdiff
      have hsum : α * (f.volume y - f.volume x) +
          β * (g.volume y - g.volume x) = 0 := by
        linarith
      have hαzero : α * (f.volume y - f.volume x) = 0 := by linarith
      have hβzero : β * (g.volume y - g.volume x) = 0 := by linarith
      have hfprice : α * f.price x = α * f.price y := by
        rcases mul_eq_zero.mp hαzero with hα0 | hfdiff0
        · simp [hα0]
        · have hfvol : f.volume x = f.volume y := by linarith
          rw [f.fiber_const hfvol]
      have hgprice : β * g.price x = β * g.price y := by
        rcases mul_eq_zero.mp hβzero with hβ0 | hgdiff0
        · simp [hβ0]
        · have hgvol : g.volume x = g.volume y := by linarith
          rw [g.fiber_const hgvol]
      rw [hfprice, hgprice]
    rcases le_total u v with huv_order | hvu_order
    · exact aux huv_order huv
    · exact (aux hvu_order huv.symm).symm

/--
Thesis source:
`2 - day-ahead/2_clearing_operator_price_curves.tex`,
Proposition `prop:admissible-parametrisations-cone`.

Original label: `prop:admissible-parametrisations-cone`.

Informal statement: graph-admissible actual representatives are closed under
all nonnegative pointwise combinations.

Lean strategy / thesis relation note: the theorem returns the combined
representative with every admissibility field proved.  It deliberately makes
no claim that this result is the canonical sided encoding of its decoded
curve.
-/
theorem graphAdmissible_conicCombination
    (α β : ℝ) (f g : GraphAdmissiblePair) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ h : GraphAdmissiblePair,
      h.volume = (fun u => α * f.volume u + β * g.volume u) ∧
      h.price = (fun u => α * f.price u + β * g.price u) := by
  refine ⟨conicCombination α β f g hα hβ, rfl, rfl⟩

/-! ## Sided linear parametrisations -/

/-- A graph-admissible representative whose volume coordinate is linear on
each side of zero. The endpoint fields are the left and right endpoints of the
decoded curve domain. -/
structure LinearAdmissiblePair extends GraphAdmissiblePair where
  leftEndpoint : ℝ
  rightEndpoint : ℝ
  leftEndpoint_nonpos : leftEndpoint ≤ 0
  rightEndpoint_nonneg : 0 ≤ rightEndpoint
  volume_left : ∀ u : Parameter, (u : ℝ) ≤ 0 →
    volume u = -leftEndpoint * (u : ℝ)
  volume_right : ∀ u : Parameter, 0 ≤ (u : ℝ) →
    volume u = rightEndpoint * (u : ℝ)

/-- Nonnegative pointwise combinations preserve sided linearity. -/
def linearConicCombination (α β : ℝ) (f g : LinearAdmissiblePair)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : LinearAdmissiblePair where
  toGraphAdmissiblePair :=
    conicCombination α β f.toGraphAdmissiblePair g.toGraphAdmissiblePair hα hβ
  leftEndpoint := α * f.leftEndpoint + β * g.leftEndpoint
  rightEndpoint := α * f.rightEndpoint + β * g.rightEndpoint
  leftEndpoint_nonpos :=
    add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα f.leftEndpoint_nonpos)
      (mul_nonpos_of_nonneg_of_nonpos hβ g.leftEndpoint_nonpos)
  rightEndpoint_nonneg :=
    add_nonneg (mul_nonneg hα f.rightEndpoint_nonneg)
      (mul_nonneg hβ g.rightEndpoint_nonneg)
  volume_left := by
    intro u hu
    change α * f.volume u + β * g.volume u =
      -(α * f.leftEndpoint + β * g.leftEndpoint) * (u : ℝ)
    rw [f.volume_left u hu, g.volume_left u hu]
    ring
  volume_right := by
    intro u hu
    change α * f.volume u + β * g.volume u =
      (α * f.rightEndpoint + β * g.rightEndpoint) * (u : ℝ)
    rw [f.volume_right u hu, g.volume_right u hu]
    ring

/--
Thesis source:
`2 - day-ahead/2_clearing_operator_price_curves.tex`,
Proposition `prop:linear-parametrisation-convex`.

Original label: `prop:linear-parametrisation-convex`.

Informal statement: actual sided-linear price-curve representatives are
closed under every pointwise combination with nonnegative coefficients.

Lean strategy / thesis relation note: `LinearAdmissiblePair` records both the
piecewise-linear volume coordinate and the graph conditions needed to decode
the price coordinate. The endpoint of the combination is proved to be the
same nonnegative combination of the original endpoints, matching the
manuscript construction of the decoded curve `h`.
-/
theorem linearParametrisation_conicCombination
    (α β : ℝ) (f g : LinearAdmissiblePair) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ h : LinearAdmissiblePair,
      h.volume = (fun u => α * f.volume u + β * g.volume u) ∧
      h.price = (fun u => α * f.price u + β * g.price u) ∧
      h.leftEndpoint = α * f.leftEndpoint + β * g.leftEndpoint ∧
      h.rightEndpoint = α * f.rightEndpoint + β * g.rightEndpoint := by
  refine ⟨linearConicCombination α β f g hα hβ, rfl, rfl, rfl, rfl⟩

/-! ## Graph-wise decoding -/

/-- Decode a graph-admissible pair on the image of its volume coordinate. -/
noncomputable def decode (f : GraphAdmissiblePair) (x : Set.range f.volume) : ℝ :=
  f.price (Classical.choose x.property)

/-- Decoding recovers the price component at every parameter value. -/
@[simp]
theorem decode_volume (f : GraphAdmissiblePair) (u : Parameter) :
    decode f ⟨f.volume u, ⟨u, rfl⟩⟩ = f.price u := by
  apply f.fiber_const
  exact Classical.choose_spec (show f.volume u ∈ Set.range f.volume from ⟨u, rfl⟩)

/-- Two decoded functions agreeing with a representative on every parameter
value agree everywhere on the image of its volume coordinate. -/
theorem decoder_unique (f : GraphAdmissiblePair)
    (h : Set.range f.volume → ℝ)
    (hh : ∀ u, h ⟨f.volume u, ⟨u, rfl⟩⟩ = f.price u) :
    h = decode f := by
  funext x
  let u := Classical.choose x.property
  have hu : f.volume u = x.1 := Classical.choose_spec x.property
  have hx : x = ⟨f.volume u, ⟨u, rfl⟩⟩ := Subtype.ext hu.symm
  rw [hx, hh, decode_volume]

/-- The image of the continuous monotone volume coordinate is exactly the
closed interval between its endpoint values. -/
theorem range_volume_eq_Icc (f : GraphAdmissiblePair) :
    Set.range f.volume =
      Set.Icc (f.volume parameterLeft) (f.volume parameterRight) := by
  apply Set.Subset.antisymm
  · rintro x ⟨u, rfl⟩
    exact ⟨f.volume_monotone (show parameterLeft ≤ u by exact u.2.1),
      f.volume_monotone (show u ≤ parameterRight by exact u.2.2)⟩
  · intro x hx
    let extendedVolume : ℝ → ℝ :=
      Set.IccExtend (show (-1 : ℝ) ≤ 1 by norm_num) f.volume
    have hextended : Continuous extendedVolume := by
      exact (continuous_IccExtend_iff.mpr f.volume_continuous)
    have hleft : extendedVolume (-1) = f.volume parameterLeft := by
      dsimp only [extendedVolume]
      rw [Set.IccExtend_of_mem]
      rfl
    have hright : extendedVolume 1 = f.volume parameterRight := by
      dsimp only [extendedVolume]
      rw [Set.IccExtend_of_mem]
      rfl
    have hinterval : x ∈ extendedVolume '' Set.Icc (-1 : ℝ) 1 := by
      apply intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
        hextended.continuousOn
      rwa [hleft, hright]
    obtain ⟨u, hu, hux⟩ := hinterval
    let u' : Parameter := ⟨u, hu⟩
    refine ⟨u', ?_⟩
    have hu' : extendedVolume u = f.volume u' := by
      dsimp only [extendedVolume]
      rw [Set.IccExtend_of_mem]
    rw [← hu']
    exact hux

/-- Regard a point of the endpoint interval as a point in the image of the
volume coordinate. -/
def toVolumeRange (f : GraphAdmissiblePair)
    (x : Set.Icc (f.volume parameterLeft) (f.volume parameterRight)) :
    Set.range f.volume :=
  ⟨x, by rw [range_volume_eq_Icc f]; exact x.2⟩

/-- The decoded price function on the concrete endpoint interval. -/
noncomputable def decodedPrice (f : GraphAdmissiblePair)
    (x : Set.Icc (f.volume parameterLeft) (f.volume parameterRight)) : ℝ :=
  decode f (toVolumeRange f x)

/-- Each parameter value maps to a point of the decoded curve's domain. -/
def volumeDomainPoint (f : GraphAdmissiblePair) (u : Parameter) :
    Set.Icc (f.volume parameterLeft) (f.volume parameterRight) :=
  ⟨f.volume u,
    f.volume_monotone (show parameterLeft ≤ u by exact u.2.1),
    f.volume_monotone (show u ≤ parameterRight by exact u.2.2)⟩

@[simp]
theorem decodedPrice_volumeDomainPoint (f : GraphAdmissiblePair) (u : Parameter) :
    decodedPrice f (volumeDomainPoint f u) = f.price u := by
  unfold decodedPrice
  have hpoint : toVolumeRange f (volumeDomainPoint f u) =
      ⟨f.volume u, ⟨u, rfl⟩⟩ := Subtype.ext rfl
  rw [hpoint, decode_volume]

/-- The graph-wise decoder actually lands in the manuscript's class of price
curves, not merely in an arbitrary function space. -/
noncomputable def decodePriceCurve (f : GraphAdmissiblePair) : PriceCurve where
  leftEndpoint := f.volume parameterLeft
  rightEndpoint := f.volume parameterRight
  leftEndpoint_nonpos := by
    calc
      f.volume parameterLeft ≤ f.volume parameterZero :=
        f.volume_monotone (by norm_num [parameterLeft, parameterZero])
      _ = 0 := f.volume_zero
  rightEndpoint_nonneg := by
    calc
      0 = f.volume parameterZero := f.volume_zero.symm
      _ ≤ f.volume parameterRight :=
        f.volume_monotone (by norm_num [parameterZero, parameterRight])
  price := decodedPrice f
  price_monotone := by
    intro x y hxy
    let u : Parameter := Classical.choose (toVolumeRange f x).2
    let v : Parameter := Classical.choose (toVolumeRange f y).2
    have hu : f.volume u = x := Classical.choose_spec (toVolumeRange f x).2
    have hv : f.volume v = y := Classical.choose_spec (toVolumeRange f y).2
    change f.price u ≤ f.price v
    rcases le_total u v with huv | hvu
    · exact f.price_monotone huv
    · have hyx : (y : ℝ) ≤ x := by
        calc
          (y : ℝ) = f.volume v := hv.symm
          _ ≤ f.volume u := f.volume_monotone hvu
          _ = x := hu
      have hxy' : (x : ℝ) ≤ y := hxy
      have hvol : f.volume u = f.volume v := by
        rw [hu, hv]
        exact le_antisymm hxy' hyx
      exact (f.fiber_const hvol).le
  price_finite := by
    refine f.price_finite.subset ?_
    rintro y ⟨x, rfl⟩
    exact ⟨Classical.choose (toVolumeRange f x).2, rfl⟩

/-- Decoding the representative recovers its price component pointwise. -/
@[simp]
theorem decodePriceCurve_price_volume (f : GraphAdmissiblePair) (u : Parameter) :
    (decodePriceCurve f).price (volumeDomainPoint f u) = f.price u := by
  exact decodedPrice_volumeDomainPoint f u

/--
Thesis source: equation `eq:graph-wise-decoder` and Proposition
`prop:admissible-parametrisations-cone` in the price-curve replacement.

Original labels: `eq:graph-wise-decoder`,
`prop:admissible-parametrisations-cone`.

The decoded `PriceCurve` has exactly the graph traced by the admissible pair.
-/
theorem range_representative_eq_decodePriceCurve_graph
    (f : GraphAdmissiblePair) :
    Set.range (fun u : Parameter => (f.volume u, f.price u)) =
      Set.range (fun x : Set.Icc (decodePriceCurve f).leftEndpoint
          (decodePriceCurve f).rightEndpoint =>
        ((x : ℝ), (decodePriceCurve f).price x)) := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨volumeDomainPoint f u, ?_⟩
    apply Prod.ext
    · rfl
    · exact decodePriceCurve_price_volume f u
  · rintro ⟨x, rfl⟩
    let u : Parameter := Classical.choose (toVolumeRange f x).2
    have hu : f.volume u = x := Classical.choose_spec (toVolumeRange f x).2
    refine ⟨u, ?_⟩
    have hx : x = volumeDomainPoint f u := Subtype.ext hu.symm
    rw [hx]
    apply Prod.ext
    · rfl
    · exact (decodePriceCurve_price_volume f u).symm

/-! ## Explicit sided-parametrisation witness calculations -/

/-- The actual (pre-quotient) codomain of a price-curve parametrisation
operator. -/
abbrev ActualRepresentative := Parameter → ℝ × ℝ

/-- Pointwise nonnegative combination in the actual representative space. -/
def representativeCombination (α β : ℝ)
    (f g : ActualRepresentative) : ActualRepresentative :=
  fun u => (α * (f u).1 + β * (g u).1,
    α * (f u).2 + β * (g u).2)

/-- Weak convexity of an actual parametrisation operator: every nonnegative
combination of two encoded curves must itself be an encoded curve. -/
def IsWeaklyConvex {Curve : Type*}
    (encode : Curve → ActualRepresentative) : Prop :=
  ∀ f g α β, 0 ≤ α → 0 ≤ β →
    ∃ h, encode h = representativeCombination α β (encode f) (encode g)

end PriceCurves
end DayAhead
end Thesis
