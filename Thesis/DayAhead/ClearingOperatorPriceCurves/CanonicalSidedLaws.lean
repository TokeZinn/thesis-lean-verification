import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedEncoding
import Thesis.DayAhead.ClearingOperatorPriceCurves.MinimalRepresentationUnique
import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedInterpolation

/-! # Parameter-block and range laws of the normalized canonical encoder -/

noncomputable section

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation Set

theorem chosenMinimalRepresentation_eq (f : PriceCurve) (m : MinimalRepresentation f) :
    chosenMinimalRepresentation f = m := Subsingleton.elim _ _

theorem essential_right_parameter_block (f : PriceCurve)
    (m : MinimalRepresentation f.essential) (j : Fin (rightCount m))
    (u : PositiveParameter) (hleft : (j : ℝ) / rightCount m < (u : ℝ))
    (hright : (u : ℝ) < ((j : ℝ) + 1) / rightCount m) :
    (sidedParametrisationOperator (canonicalSidedCurveOfMinimal m) (positiveParameter u)).2 =
      m.level (rightCell m j) := by
  let data := canonicalSidedKnotDataOfMinimal m
  have hu : 0 < (u : ℝ) := lt_of_le_of_lt (div_nonneg (by positivity) (by positivity)) hleft
  have hb := uniformInterpolation_block_interior (canonicalRightKnot m)
    (essential_canonicalRightKnot_strictMono f m) j hleft hright
  apply data.right_block_interior j
  · change canonicalRightKnot m j.castSucc < sidedVolumeReal data (u : ℝ)
    rw [sidedVolumeReal, if_neg (not_le.mpr hu)]
    exact hb.1
  · change sidedVolumeReal data (u : ℝ) < canonicalRightKnot m j.succ
    rw [sidedVolumeReal, if_neg (not_le.mpr hu)]
    exact hb.2

theorem essential_rightCount_pos (f : PriceCurve) (m : MinimalRepresentation f.essential)
    (hr : 0 < f.rightEndpoint) : 0 < rightCount m := by
  apply Nat.pos_of_ne_zero
  intro h
  exact hr.ne' (rightEndpoint_eq_zero_of_rightCount_eq_zero (f := f.essential) m h)

theorem essential_price_nonneg_mem_rightLevel_range (f : PriceCurve)
    (m : MinimalRepresentation f.essential) (hr : 0 < f.rightEndpoint)
    (x : Icc f.leftEndpoint f.rightEndpoint) (hx : 0 ≤ (x : ℝ)) :
    f.essentialPrice x ∈ range (fun j => m.level (rightCell m j)) := by
  have hpositive (y : Icc f.leftEndpoint f.rightEndpoint) (hy : 0 < (y : ℝ)) :
      f.essentialPrice y ∈ range (fun j => m.level (rightCell m j)) := by
    obtain ⟨i, hi⟩ := exists_cell_mem m y
    obtain ⟨j, hj⟩ := exists_rightCell_eq_of_active m ⟨y, hi, hy⟩
    refine ⟨j, ?_⟩
    change m.level (rightCell m j) = f.essentialPrice y
    rw [hj]
    exact (price_eq_level_of_mem m hi).symm
  rcases hx.eq_or_lt with hx | hx
  · have hx0 : x = f.domainZero := Subtype.ext hx.symm
    subst x
    obtain ⟨z, h0z, hz⟩ := f.essentialPrice_right_constant f.domainZero hr
    obtain ⟨y, h0y, hyz⟩ := exists_between h0z
    have heq := hz y h0y.le hyz
    rw [← heq]
    exact hpositive y h0y
  · exact hpositive x hx

theorem essential_right_price_range (f : PriceCurve) (m : MinimalRepresentation f.essential)
    (hr : 0 < f.rightEndpoint) :
    rightPriceRange (canonicalSidedCurveOfMinimal m) =
      range (fun j => m.level (rightCell m j)) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    let p := sidedAdmissibleParametrisation (canonicalSidedKnotDataOfMinimal m)
    apply essential_price_nonneg_mem_rightLevel_range f m hr (p (positiveParameter u))
    have hu : parameterZero ≤ positiveParameter u := u.property.1
    have h := p.monotone hu
    rw [p.map_zero] at h
    exact h
  · rintro ⟨j, rfl⟩
    have hn : (0 : ℝ) < rightCount m := by exact_mod_cast essential_rightCount_pos f m hr
    have hj : (j : ℝ) + 1 ≤ rightCount m := by exact_mod_cast j.isLt
    let t : ℝ := ((j : ℝ) + 1 / 2) / rightCount m
    have ht0 : 0 ≤ t := div_nonneg (by positivity) hn.le
    have ht1 : t ≤ 1 := by apply (div_le_one hn).mpr; linarith
    let u : PositiveParameter := ⟨t, ht0, ht1⟩
    refine ⟨u, essential_right_parameter_block f m j u ?_ ?_⟩
    · change (j : ℝ) / rightCount m < ((j : ℝ) + 1 / 2) / rightCount m
      exact (div_lt_div_iff_of_pos_right hn).mpr (by linarith)
    · change ((j : ℝ) + 1 / 2) / rightCount m < ((j : ℝ) + 1) / rightCount m
      exact (div_lt_div_iff_of_pos_right hn).mpr (by linarith)

/-- Every normalized canonical certificate with a noncollapsed right side
belongs to the certificate family used by the midpoint obstruction. -/
def essentialMinimalCanonicalSidedCurve (f : PriceCurve)
    (m : MinimalRepresentation f.essential) (hr : 0 < f.rightEndpoint) :
    MinimalCanonicalSidedCurve where
  raw := canonicalSidedCurveOfMinimal m
  rightCount_pos := essential_rightCount_pos f m hr
  rightKnot_strictMono := essential_canonicalRightKnot_strictMono f m
  right_price_range := essential_right_price_range f m hr
  right_parameter_block := essential_right_parameter_block f m

def canonicalMinimalSidedCertificate (f : PriceCurve) (hr : 0 < f.rightEndpoint) :
    MinimalCanonicalSidedCurve :=
  essentialMinimalCanonicalSidedCurve f (chosenMinimalRepresentation f.essential) hr

@[simp] theorem canonicalMinimalSidedCertificate_encoding (f : PriceCurve)
    (hr : 0 < f.rightEndpoint) :
    minimalSidedParametrisationOperator (canonicalMinimalSidedCertificate f hr) =
      canonicalSidedEncoding f := rfl

end Thesis.DayAhead.SidedCertificate
