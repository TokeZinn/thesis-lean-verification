import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedLp
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Almost-everywhere graph recovery for selected price curves

The source claims injectivity of the canonical Hilbert encoding on essential
curves. Pointwise graph recovery alone does not prove this: L² forgets null
sets. The lemmas here recover the continuous volume coordinate first, then
use the selected one-sided price values to recover the physical price curve.
-/

noncomputable section

namespace Thesis.DayAhead.CanonicalSidedLp

open Set MeasureTheory PriceCurves SidedParametrisation SidedCertificate SidedCurveLp

theorem clampParameter_coe (u : Parameter) : clampParameter (u : ℝ) = u := by
  apply Subtype.ext
  exact max_eq_right (u.property.1.trans_eq (min_eq_right u.property.2).symm) |>.trans
    (min_eq_right u.property.2)

/-- Continuous volume coordinates that agree in L² agree at both endpoints too. -/
theorem continuous_parameter_eq_of_ae {q r : Parameter → ℝ}
    (hq : Continuous q) (hr : Continuous r)
    (h : (fun x => q (clampParameter x)) =ᵐ[sidedLebesgueMeasure]
      (fun x => r (clampParameter x))) : q = r := by
  have he := Measure.eqOn_Icc_of_ae_eq (μ := volume) (by norm_num : (-1 : ℝ) ≠ 1)
    h (hq.comp continuous_clampParameter).continuousOn
      (hr.comp continuous_clampParameter).continuousOn
  funext u
  simpa only [clampParameter_coe] using he u.property

/-- A full-measure set meets the preimage of any interior physical interval. -/
theorem exists_good_parameter {a b : ℝ} (q : Parameter → Icc a b)
    (hq : Continuous q) (hsurj : Function.Surjective q)
    (hleft : (q parameterLeft : ℝ) = a) (hright : (q parameterRight : ℝ) = b)
    {p : ℝ → Prop} (hae : ∀ᵐ u ∂sidedLebesgueMeasure, p u)
    (v w : Icc a b) (hvw : v < w) :
    ∃ u : ℝ, u ∈ Ioo (-1 : ℝ) 1 ∧
      (q (clampParameter u) : ℝ) ∈ Ioo (v : ℝ) w ∧ p u := by
  obtain ⟨z, hvz, hzw⟩ := exists_between hvw
  obtain ⟨t, ht⟩ := hsurj z
  have hat : a < (q t : ℝ) := by rw [ht]; exact v.property.1.trans_lt hvz
  have htb : (q t : ℝ) < b := by
    rw [ht]
    exact (show (z : ℝ) < w from hzw).trans_le w.property.2
  have htleft : (-1 : ℝ) < t := by
    refine lt_of_le_of_ne t.property.1 ?_
    intro he
    have : t = parameterLeft := Subtype.ext he.symm
    rw [this, hleft] at hat
    exact lt_irrefl _ hat
  have htright : (t : ℝ) < 1 := by
    refine lt_of_le_of_ne t.property.2 ?_
    intro he
    have : t = parameterRight := Subtype.ext he
    rw [this, hright] at htb
    exact lt_irrefl _ htb
  let U := Ioo (-1 : ℝ) 1 ∩
    (fun u : ℝ => (q (clampParameter u) : ℝ)) ⁻¹' Ioo (v : ℝ) w
  have hU : IsOpen U := isOpen_Ioo.inter
    (isOpen_Ioo.preimage (continuous_subtype_val.comp (hq.comp continuous_clampParameter)))
  have hne : U.Nonempty := ⟨t, ⟨htleft, htright⟩, by
    simpa [clampParameter_coe, ht] using And.intro hvz hzw⟩
  obtain ⟨u, hu, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_ne_zero volume hne)
    (ae_restrict_of_ae_restrict_of_subset
      (show U ⊆ Icc (-1 : ℝ) 1 from fun _ hu => ⟨hu.1.1.le, hu.1.2.le⟩) hae)
  exact ⟨u, hu.1, hu.2, hp⟩

/-- Selected finite-step functions are determined by almost-everywhere equality
after any continuous surjective parametrisation with the correct endpoints. -/
theorem selected_price_eq_of_ae {a b : ℝ} (hab : a ≤ b)
    (q : Parameter → Icc a b) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hleft : (q parameterLeft : ℝ) = a) (hright : (q parameterRight : ℝ) = b)
    (f g : Icc a b → ℝ)
    (hf : ∀ x : Icc a b, (x : ℝ) < b →
      ∃ z, x < z ∧ ∀ y, x ≤ y → y < z → f y = f x)
    (hg : ∀ x : Icc a b, (x : ℝ) < b →
      ∃ z, x < z ∧ ∀ y, x ≤ y → y < z → g y = g x)
    (hfl : a < b → ∃ z : Icc a b, z < ⟨b, hab, le_rfl⟩ ∧
      ∀ y, z < y → y ≤ ⟨b, hab, le_rfl⟩ → f y = f ⟨b, hab, le_rfl⟩)
    (hgl : a < b → ∃ z : Icc a b, z < ⟨b, hab, le_rfl⟩ ∧
      ∀ y, z < y → y ≤ ⟨b, hab, le_rfl⟩ → g y = g ⟨b, hab, le_rfl⟩)
    (hae : (fun u => f (q (clampParameter u))) =ᵐ[sidedLebesgueMeasure]
      (fun u => g (q (clampParameter u)))) : f = g := by
  funext x
  by_cases hab' : a < b
  · by_cases hx : (x : ℝ) < b
    · obtain ⟨zf, hxf, hfz⟩ := hf x hx
      obtain ⟨zg, hxg, hgz⟩ := hg x hx
      obtain ⟨u, _, hu, he⟩ := exists_good_parameter q hq hsurj hleft hright
        hae x (min zf zg) (lt_min hxf hxg)
      exact (hfz _ hu.1.le (hu.2.trans_le (min_le_left _ _))).symm.trans
        (he.trans (hgz _ hu.1.le (hu.2.trans_le (min_le_right _ _))))
    · have hxb : x = ⟨b, hab, le_rfl⟩ :=
        Subtype.ext (le_antisymm x.property.2 (not_lt.mp hx))
      subst x
      obtain ⟨zf, hfb, hfz⟩ := hfl hab'
      obtain ⟨zg, hgb, hgz⟩ := hgl hab'
      obtain ⟨u, _, hu, he⟩ := exists_good_parameter q hq hsurj hleft hright
        hae (max zf zg) ⟨b, hab, le_rfl⟩ (max_lt hfb hgb)
      exact (hfz _ ((le_max_left _ _).trans_lt hu.1) hu.2.le).symm.trans
        (he.trans (hgz _ ((le_max_right _ _).trans_lt hu.1) hu.2.le))
  · have habEq : a = b := le_antisymm hab (not_lt.mp hab')
    obtain ⟨u, _, hu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (by norm_num : volume (Ioo (-1 : ℝ) 1) ≠ 0)
      (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hae)
    have hsingleton (y : Icc a b) : y = x := by
      apply Subtype.ext
      have hy : (y : ℝ) = a := le_antisymm (habEq ▸ y.property.2) y.property.1
      have hx : (x : ℝ) = a := le_antisymm (habEq ▸ x.property.2) x.property.1
      exact hy.trans hx.symm
    simpa only [hsingleton] using hu

theorem admissible_left (f : PriceCurve) (q : AdmissibleParametrisation f) :
    (q parameterLeft : ℝ) = f.leftEndpoint := by
  obtain ⟨u, hu⟩ := q.surjective ⟨f.leftEndpoint, le_rfl,
    f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg⟩
  apply le_antisymm _ (q parameterLeft).property.1
  have h := q.monotone (show parameterLeft ≤ u from u.property.1)
  simpa only [hu] using h

theorem admissible_right (f : PriceCurve) (q : AdmissibleParametrisation f) :
    (q parameterRight : ℝ) = f.rightEndpoint := by
  obtain ⟨u, hu⟩ := q.surjective ⟨f.rightEndpoint,
    f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg, le_rfl⟩
  apply le_antisymm (q parameterRight).property.2
  have h := q.monotone (show u ≤ parameterRight from u.property.2)
  simpa only [hu] using h

/-- Almost-everywhere equality recovers the selected physical graph even when
the two curves were parametrised by different admissible maps. -/
theorem essential_eq_of_parametrisedGraph_ae {f g : PriceCurve}
    (p : AdmissibleParametrisation f.essential)
    (q : AdmissibleParametrisation g.essential)
    (hae : (fun u => parametrisedGraph f.essential p (clampParameter u))
      =ᵐ[sidedLebesgueMeasure]
      (fun u => parametrisedGraph g.essential q (clampParameter u))) :
    f.essential = g.essential := by
  have hv : (fun u => (p u : ℝ)) = (fun u => (q u : ℝ)) := by
    apply continuous_parameter_eq_of_ae
      (continuous_subtype_val.comp p.continuous)
      (continuous_subtype_val.comp q.continuous)
    exact hae.mono (fun _ h => congrArg Prod.fst h)
  have hl : f.leftEndpoint = g.leftEndpoint := by
    change f.essential.leftEndpoint = g.essential.leftEndpoint
    rw [← admissible_left f.essential p, ← admissible_left g.essential q]
    exact congrFun hv parameterLeft
  have hr : f.rightEndpoint = g.rightEndpoint := by
    change f.essential.rightEndpoint = g.essential.rightEndpoint
    rw [← admissible_right f.essential p, ← admissible_right g.essential q]
    exact congrFun hv parameterRight
  cases f with
  | mk a b ha hb fp hfm hff =>
    cases g with
    | mk c d hc hd gp hgm hgf =>
      dsimp only at hl hr
      subst c
      subst d
      have hpq : p.toFun = q.toFun := by
        funext u
        exact Subtype.ext (congrFun hv u)
      let f : PriceCurve := ⟨a, b, ha, hb, fp, hfm, hff⟩
      let g : PriceCurve := ⟨a, b, hc, hd, gp, hgm, hgf⟩
      have hprice : f.essentialPrice = g.essentialPrice := by
        apply selected_price_eq_of_ae (ha.trans hb) p.toFun p.continuous p.surjective
          (admissible_left f.essential p) (admissible_right f.essential p)
          f.essentialPrice g.essentialPrice
          f.essentialPrice_right_constant g.essentialPrice_right_constant
          f.essentialPrice_left_constant g.essentialPrice_left_constant
        filter_upwards [hae] with u hu
        have he := congrArg Prod.snd hu
        change f.essentialPrice (p.toFun (clampParameter u)) =
          g.essentialPrice (q.toFun (clampParameter u)) at he
        rw [← hpq] at he
        exact he
      change f.essential = g.essential
      dsimp only [PriceCurve.essential]
      congr 1

/-- Original label: `defn:parametrisation-operator`.
The kernel of the literal Euclidean L² map consists exactly of curves with the
same selected essential representative. This closes the quotient-to-curve gap. -/
theorem canonicalSidedEncodingLpReal_eq_iff (f g : PriceCurve) :
    canonicalSidedEncodingLpReal f = canonicalSidedEncodingLpReal g ↔
      f.essential = g.essential := by
  constructor
  · intro h
    apply essential_eq_of_parametrisedGraph_ae
      (sidedAdmissibleParametrisation (canonicalCertificate f).knots)
      (sidedAdmissibleParametrisation (canonicalCertificate g).knots)
    filter_upwards [coeFn_canonicalSidedEncodingLpReal f,
      coeFn_canonicalSidedEncodingLpReal g] with u hf hg
    apply PriceCurveHilbert.pairEquiv.injective
    change PriceCurveHilbert.pairEquiv (canonicalSidedEncoding f (clampParameter u)) =
      PriceCurveHilbert.pairEquiv (canonicalSidedEncoding g (clampParameter u))
    exact hf.symm.trans ((congrArg (fun z => z u) h).trans hg)
  · intro h
    rw [← canonicalSidedEncodingLpReal_essential f,
      ← canonicalSidedEncodingLpReal_essential g, h]

/-- Original label: `defn:parametrisation-operator`.
The thesis's restricted Hilbert encoding is genuinely injective. -/
theorem essentialSidedEncodingLpReal_injective :
    Function.Injective essentialSidedEncodingLpReal := by
  intro f g h
  apply Subtype.ext
  have he := (canonicalSidedEncodingLpReal_eq_iff f.val g.val).mp h
  simpa only [f.property, g.property] using he

end Thesis.DayAhead.CanonicalSidedLp
