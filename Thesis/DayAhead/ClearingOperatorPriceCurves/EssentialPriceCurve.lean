import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveLp
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! # The essential representative of a price curve

At each point below the upper endpoint, select the strict right limit. At
the upper endpoint, select the strict left limit. For a singleton domain the
one-sided-limit convention retains the original price. Thus isolated knot
values are removed before allocating equal parameter blocks.
-/

noncomputable section

namespace Thesis.DayAhead.PriceCurves

open Set Filter Topology

def PriceCurve.domainRight (f : PriceCurve) : Icc f.leftEndpoint f.rightEndpoint :=
  ⟨f.rightEndpoint, f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg, le_rfl⟩

def PriceCurve.essentialPrice (f : PriceCurve)
    (x : Icc f.leftEndpoint f.rightEndpoint) : ℝ :=
  if (x : ℝ) < f.rightEndpoint then f.price.rightLim x else f.price.leftLim x

theorem PriceCurve.essentialPrice_monotone (f : PriceCurve) :
    Monotone f.essentialPrice := by
  intro x y hxy
  dsimp only [PriceCurve.essentialPrice]
  split_ifs with hx hy
  · exact f.price_monotone.rightLim hxy
  · apply f.price_monotone.rightLim_le_leftLim
    change (x : ℝ) < y
    have hy' : (y : ℝ) = f.rightEndpoint := le_antisymm y.property.2 (not_lt.mp hy)
    rwa [hy']
  · have hx' : (x : ℝ) = f.rightEndpoint := le_antisymm x.property.2 (not_lt.mp hx)
    have hxy' : (x : ℝ) ≤ y := hxy
    linarith
  · exact f.price_monotone.leftLim hxy

theorem PriceCurve.essentialPrice_mem_range (f : PriceCurve)
    (x : Icc f.leftEndpoint f.rightEndpoint) : f.essentialPrice x ∈ range f.price := by
  dsimp only [PriceCurve.essentialPrice]
  split_ifs
  · exact f.price_finite.isClosed.mem_of_mapClusterPt
      (mapClusterPt_rightLim f.price x) (Eventually.of_forall (fun _ => mem_range_self _))
  · exact f.price_finite.isClosed.mem_of_mapClusterPt
      (mapClusterPt_leftLim f.price x) (Eventually.of_forall (fun _ => mem_range_self _))

def PriceCurve.essential (f : PriceCurve) : PriceCurve where
  leftEndpoint := f.leftEndpoint
  rightEndpoint := f.rightEndpoint
  leftEndpoint_nonpos := f.leftEndpoint_nonpos
  rightEndpoint_nonneg := f.rightEndpoint_nonneg
  price := f.essentialPrice
  price_monotone := f.essentialPrice_monotone
  price_finite := f.price_finite.subset (by
    rintro _ ⟨x, rfl⟩
    exact f.essentialPrice_mem_range x)

theorem PriceCurve.essentialPrice_finite_disagreement (f : PriceCurve) :
    {x | f.essentialPrice x ≠ f.price x}.Finite := by
  let D : Set (Icc f.leftEndpoint f.rightEndpoint) :=
    {x | (x : ℝ) < f.rightEndpoint ∧ f.essentialPrice x ≠ f.price x}
  have hinj : InjOn f.price D := by
    intro x hx y hy heq
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · exfalso
      apply hx.2
      rw [PriceCurve.essentialPrice, if_pos hx.1]
      exact le_antisymm (heq ▸ f.price_monotone.rightLim_le hxy)
        (f.price_monotone.le_rightLim le_rfl)
    · exact hxy
    · exfalso
      apply hy.2
      rw [PriceCurve.essentialPrice, if_pos hy.1]
      exact le_antisymm (heq.symm ▸ f.price_monotone.rightLim_le hyx)
        (f.price_monotone.le_rightLim le_rfl)
  have hD : D.Finite :=
    (f.price_finite.subset (image_subset_range _ _)).of_finite_image hinj
  apply (hD.insert f.domainRight).subset
  intro x hx
  by_cases hxr : (x : ℝ) < f.rightEndpoint
  · exact mem_insert_of_mem _ ⟨hxr, hx⟩
  · apply mem_insert_iff.mpr
    left
    apply Subtype.ext
    exact le_antisymm x.property.2 (not_lt.mp hxr)

/-- Essential normalization changes only finitely many prices, and therefore
does not change the curve's class for any atomless measure on its domain. -/
theorem PriceCurve.essentialPrice_ae_eq (f : PriceCurve)
    (μ : MeasureTheory.Measure (Icc f.leftEndpoint f.rightEndpoint))
    [MeasureTheory.NoAtoms μ] : f.essentialPrice =ᵐ[μ] f.price := by
  apply MeasureTheory.ae_iff.mpr
  exact f.essentialPrice_finite_disagreement.measure_zero μ

theorem PriceCurve.essentialPrice_of_singleton (f : PriceCurve)
    (h : f.leftEndpoint = f.rightEndpoint) : f.essentialPrice = f.price := by
  funext x
  have hlo : f.rightEndpoint ≤ (x : ℝ) := by simpa only [h] using x.property.1
  have hxr : (x : ℝ) = f.rightEndpoint := le_antisymm x.property.2 hlo
  rw [PriceCurve.essentialPrice, hxr, if_neg (lt_irrefl _)]
  apply leftLim_eq_of_isBot
  intro y
  change (x : ℝ) ≤ y
  rw [hxr]
  simpa only [h] using y.property.1

theorem eventually_eq_of_tendsto_finite_range {α β : Type*} [TopologicalSpace β]
    [T1Space β] {l : Filter α} {g : α → β} {c : β}
    (hg : (range g).Finite) (h : Tendsto g l (𝓝 c)) : ∀ᶠ x in l, g x = c := by
  have hopen : IsOpen ((range g \ {c})ᶜ) := hg.diff.isClosed.isOpen_compl
  have hmem : (range g \ {c})ᶜ ∈ 𝓝 c := hopen.mem_nhds (by simp)
  filter_upwards [h hmem] with x hx
  by_contra hne
  exact hx ⟨mem_range_self x, hne⟩

theorem PriceCurve.essentialPrice_right_constant (f : PriceCurve)
    (x : Icc f.leftEndpoint f.rightEndpoint) (hx : (x : ℝ) < f.rightEndpoint) :
    ∃ z, x < z ∧ ∀ y, x ≤ y → y < z → f.essentialPrice y = f.essentialPrice x := by
  have hx' : x < f.domainRight := hx
  have hevent := eventually_eq_of_tendsto_finite_range f.price_finite
    (f.price_monotone.tendsto_rightLim x)
  obtain ⟨z, hxz, hz⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hx').mp hevent
  refine ⟨z, hxz, fun y hxy hyz => ?_⟩
  have hy : (y : ℝ) < f.rightEndpoint := lt_of_lt_of_le hyz z.property.2
  rw [PriceCurve.essentialPrice, if_pos hy, PriceCurve.essentialPrice, if_pos hx]
  obtain ⟨w, hyw, hwz⟩ := exists_between hyz
  have hw : f.price w = f.price.rightLim x := hz ⟨hxy.trans_lt hyw, hwz⟩
  apply le_antisymm
  · exact (f.price_monotone.rightLim_le hyw).trans_eq hw
  · exact f.price_monotone.rightLim hxy

theorem PriceCurve.essentialPrice_left_constant (f : PriceCurve)
    (hab : f.leftEndpoint < f.rightEndpoint) :
    ∃ z, z < f.domainRight ∧ ∀ y, z < y → y ≤ f.domainRight →
      f.essentialPrice y = f.essentialPrice f.domainRight := by
  let l : Icc f.leftEndpoint f.rightEndpoint := ⟨f.leftEndpoint, le_rfl, hab.le⟩
  have hl : l < f.domainRight := hab
  have hevent := eventually_eq_of_tendsto_finite_range f.price_finite
    (f.price_monotone.tendsto_leftLim f.domainRight)
  obtain ⟨z, hzr, hz⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hl).mp hevent
  refine ⟨z, hzr, fun y hzy hyr => ?_⟩
  rcases hyr.eq_or_lt with rfl | hyr
  · rfl
  have hy : (y : ℝ) < f.rightEndpoint := hyr
  rw [PriceCurve.essentialPrice, if_pos hy, PriceCurve.essentialPrice,
    if_neg (show ¬(f.domainRight : ℝ) < f.rightEndpoint from lt_irrefl _)]
  obtain ⟨w, hzw, hwy⟩ := exists_between hzy
  have hw : f.price w = f.price.leftLim f.domainRight := hz ⟨hzw, hwy.trans hyr⟩
  apply le_antisymm (f.price_monotone.rightLim_le_leftLim hyr)
  exact hw ▸ f.price_monotone.le_rightLim hwy.le

/-- Every retained price level occupies a nontrivial interval whenever the
physical domain is nondegenerate. In particular, normalization leaves no
singleton-only level to be counted as a parameter block. -/
theorem PriceCurve.essentialPrice_fiber_interval (f : PriceCurve)
    (hab : f.leftEndpoint < f.rightEndpoint) (x : Icc f.leftEndpoint f.rightEndpoint) :
    ∃ u v : Icc f.leftEndpoint f.rightEndpoint, u < v ∧
      ∀ y, u ≤ y → y ≤ v → f.essentialPrice y = f.essentialPrice x := by
  by_cases hx : (x : ℝ) < f.rightEndpoint
  · obtain ⟨z, hxz, hz⟩ := f.essentialPrice_right_constant x hx
    obtain ⟨v, hxv, hvz⟩ := exists_between hxz
    exact ⟨x, v, hxv, fun y hxy hyv => hz y hxy (hyv.trans_lt hvz)⟩
  · have hxr : x = f.domainRight :=
      Subtype.ext (le_antisymm x.property.2 (not_lt.mp hx))
    subst x
    obtain ⟨z, hzr, hz⟩ := f.essentialPrice_left_constant hab
    obtain ⟨u, hzu, hur⟩ := exists_between hzr
    exact ⟨u, f.domainRight, hur, fun y huy hyr => hz y (hzu.trans_le huy) hyr⟩

theorem PriceCurve.essentialPrice_idempotent (f : PriceCurve) :
    f.essential.essentialPrice = f.essentialPrice := by
  funext x
  by_cases hx : (x : ℝ) < f.rightEndpoint
  · change (if (x : ℝ) < f.rightEndpoint then f.essentialPrice.rightLim x
      else f.essentialPrice.leftLim x) = _
    rw [if_pos hx]
    obtain ⟨z, hxz, hz⟩ := f.essentialPrice_right_constant x hx
    haveI := nhdsGT_neBot_of_exists_gt ⟨z, hxz⟩
    apply rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hxz] with y hy
    exact (hz y hy.1.le hy.2).symm
  · have hxr : x = f.domainRight :=
      Subtype.ext (le_antisymm x.property.2 (not_lt.mp hx))
    subst x
    change (if (f.domainRight : ℝ) < f.rightEndpoint then _ else _) = _
    rw [if_neg hx]
    change f.essentialPrice.leftLim f.domainRight = f.essentialPrice f.domainRight
    by_cases hab : f.leftEndpoint < f.rightEndpoint
    · obtain ⟨z, hzr, hz⟩ := f.essentialPrice_left_constant hab
      haveI := nhdsLT_neBot_of_exists_lt ⟨z, hzr⟩
      apply leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsLT hzr] with y hy
      exact (hz y hy.1 hy.2.le).symm
    · apply leftLim_eq_of_isBot
      intro y
      change f.rightEndpoint ≤ (y : ℝ)
      exact (not_lt.mp hab).trans y.property.1

theorem PriceCurve.essential_idempotent (f : PriceCurve) : f.essential.essential = f.essential := by
  have h := f.essentialPrice_idempotent
  cases f
  simp only [PriceCurve.essential] at *
  congr 1

/-- Curves already using the thesis's convention on isolated knot values. -/
def EssentialPriceCurve := {f : PriceCurve // f.essential = f}

def PriceCurve.toEssential (f : PriceCurve) : EssentialPriceCurve :=
  ⟨f.essential, f.essential_idempotent⟩

end Thesis.DayAhead.PriceCurves
