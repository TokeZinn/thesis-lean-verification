import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedLaws
import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedCurveLp

/-! # Explicit witnesses in the normalized canonical sided image -/

noncomputable section

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation SidedCurveLp Set Filter Topology MeasureTheory

theorem essentialPrice_eq_of_right_constant (f : PriceCurve)
    (x z : Icc f.leftEndpoint f.rightEndpoint) (hxz : x < z) {c : ℝ}
    (hc : ∀ y, x < y → y < z → f.price y = c) : f.essentialPrice x = c := by
  have hx : (x : ℝ) < f.rightEndpoint := (show (x : ℝ) < z from hxz).trans_le z.property.2
  rw [PriceCurve.essentialPrice, if_pos hx]
  haveI := nhdsGT_neBot_of_exists_gt ⟨z, hxz⟩
  apply rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hxz] with y hy
  exact (hc y hy.1 hy.2).symm

theorem essentialPrice_rightEndpoint_eq_of_left_constant (f : PriceCurve)
    (z : Icc f.leftEndpoint f.rightEndpoint) (hz : z < f.domainRight) {c : ℝ}
    (hc : ∀ y, z < y → y < f.domainRight → f.price y = c) :
    f.essentialPrice f.domainRight = c := by
  rw [PriceCurve.essentialPrice, if_neg (show ¬(f.domainRight : ℝ) < f.rightEndpoint from
    lt_irrefl _)]
  haveI := nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
  apply leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsLT hz] with y hy
  exact (hc y hy.1 hy.2).symm

theorem essential_twoBlock_price (x : Icc (0 : ℝ) 2) :
    twoBlockCurve.essentialPrice x = if (x : ℝ) < 1 then 0 else 2 := by
  by_cases hx : (x : ℝ) < 1
  · rw [if_pos hx]
    apply essentialPrice_eq_of_right_constant twoBlockCurve x ⟨1, by norm_num [twoBlockCurve]⟩ hx
    intro y _ hy
    exact if_pos hy.le
  · rw [if_neg hx]
    by_cases hx2 : (x : ℝ) < 2
    · apply essentialPrice_eq_of_right_constant twoBlockCurve x twoBlockCurve.domainRight hx2
      intro y hxy _
      apply if_neg
      have hxy' : (x : ℝ) < y := hxy
      linarith
    · have hxr : x = twoBlockCurve.domainRight :=
        Subtype.ext (le_antisymm x.property.2 (not_lt.mp hx2))
      subst x
      apply essentialPrice_rightEndpoint_eq_of_left_constant twoBlockCurve
        ⟨1, by norm_num [twoBlockCurve]⟩
        (by change (1 : ℝ) < 2; norm_num)
      intro y hy _
      exact if_neg (not_le.mpr hy)

theorem essential_threeBlock_price (x : Icc (0 : ℝ) 3) :
    threeBlockCurve.essentialPrice x =
      if (x : ℝ) < 1 then 0 else if (x : ℝ) < 2 then 1 else 3 := by
  by_cases hx1 : (x : ℝ) < 1
  · rw [if_pos hx1]
    apply essentialPrice_eq_of_right_constant threeBlockCurve x
      ⟨1, by norm_num [threeBlockCurve]⟩ hx1
    intro y _ hy
    exact if_pos hy.le
  · rw [if_neg hx1]
    by_cases hx2 : (x : ℝ) < 2
    · rw [if_pos hx2]
      apply essentialPrice_eq_of_right_constant threeBlockCurve x
        ⟨2, by norm_num [threeBlockCurve]⟩ hx2
      intro y hxy hy
      have hy1 : ¬(y : ℝ) ≤ 1 := by
        have hxy' : (x : ℝ) < y := hxy
        linarith
      have hy2 : (y : ℝ) ≤ 2 := hy.le
      simp only [threeBlockCurve, threeBlockPrice, if_neg hy1, if_pos hy2]
    · rw [if_neg hx2]
      by_cases hx3 : (x : ℝ) < 3
      · apply essentialPrice_eq_of_right_constant threeBlockCurve x threeBlockCurve.domainRight hx3
        intro y hxy _
        have hxy' : (x : ℝ) < y := hxy
        have hy1 : ¬(y : ℝ) ≤ 1 := by linarith
        have hy2 : ¬(y : ℝ) ≤ 2 := by linarith
        simp only [threeBlockCurve, threeBlockPrice, if_neg hy1, if_neg hy2]
      · have hxr : x = threeBlockCurve.domainRight :=
          Subtype.ext (le_antisymm x.property.2 (not_lt.mp hx3))
        subst x
        apply essentialPrice_rightEndpoint_eq_of_left_constant threeBlockCurve
          ⟨2, by norm_num [threeBlockCurve]⟩
          (by change (2 : ℝ) < 3; norm_num)
        intro y hy _
        have hy' : (2 : ℝ) < y := hy
        have hy1 : ¬(y : ℝ) ≤ 1 := by linarith
        have hy2 : ¬(y : ℝ) ≤ 2 := by linarith
        simp only [threeBlockCurve, threeBlockPrice, if_neg hy1, if_neg hy2]

def essentialTwoMinimal : MinimalRepresentation twoBlockCurve.essential :=
  minimalRepresentationOfLevels _ (by norm_num : 0 < 2) twoRightLevel
    (by
      intro i j hij
      dsimp [twoRightLevel]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) (by norm_num)) (by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨⟨(i : ℝ) + 1 / 2, ?_⟩, ?_⟩
        · fin_cases i <;> norm_num [PriceCurve.essential, twoBlockCurve]
        · change twoBlockCurve.essentialPrice _ = _
          rw [essential_twoBlock_price]
          fin_cases i <;> norm_num [twoRightLevel]
      · rintro ⟨x, rfl⟩
        change ∃ i, twoRightLevel i = twoBlockCurve.essentialPrice x
        rw [essential_twoBlock_price]
        split_ifs
        · exact ⟨0, by norm_num [twoRightLevel]⟩
        · exact ⟨1, by norm_num [twoRightLevel]⟩)

def essentialThreeMinimal : MinimalRepresentation threeBlockCurve.essential :=
  minimalRepresentationOfLevels _ (by norm_num : 0 < 3) threeRightLevel
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [threeRightLevel] at *) (by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨⟨(i : ℝ) + 1 / 2, ?_⟩, ?_⟩
        · fin_cases i <;> norm_num [PriceCurve.essential, threeBlockCurve]
        · change threeBlockCurve.essentialPrice _ = _
          rw [essential_threeBlock_price]
          fin_cases i <;> norm_num [threeRightLevel]
      · rintro ⟨x, rfl⟩
        change ∃ i, threeRightLevel i = threeBlockCurve.essentialPrice x
        rw [essential_threeBlock_price]
        split_ifs
        · exact ⟨0, by norm_num [threeRightLevel]⟩
        · exact ⟨1, by norm_num [threeRightLevel]⟩
        · exact ⟨2, rfl⟩)

theorem cellSup_eq_of_interval_bounds {f : PriceCurve} (m : MinimalRepresentation f)
    (i : Fin m.blockCount) {l r : ℝ} (hlr : l < r)
    (hinterior : Ioo l r ⊆ cellReal m i)
    (hupper : ∀ x ∈ cellReal m i, x ≤ r) : cellSup m i = r := by
  apply le_antisymm (csSup_le (cellReal_nonempty m i) hupper)
  by_contra h
  have hr : cellSup m i < r := not_le.mp h
  obtain ⟨x, hx, hxr⟩ := exists_between (max_lt hlr hr)
  have hxc : x ∈ cellReal m i := hinterior ⟨(le_max_left _ _).trans_lt hx, hxr⟩
  have hxs := le_csSup (cellReal_bddAbove m i) hxc
  have := (le_max_right _ _).trans_lt hx
  exact (not_lt_of_ge hxs) this

theorem essentialTwo_cellSup (i : Fin 2) : cellSup essentialTwoMinimal i = (i : ℝ) + 1 := by
  apply cellSup_eq_of_interval_bounds essentialTwoMinimal i (l := i) (by linarith)
  · intro x hx
    have hxdom : x ∈ Icc (0 : ℝ) 2 := by
      fin_cases i <;> norm_num at hx <;> constructor <;> linarith [hx.1, hx.2]
    refine ⟨⟨x, hxdom⟩, ?_, rfl⟩
    change twoBlockCurve.essentialPrice _ = twoRightLevel i
    rw [essential_twoBlock_price]
    fin_cases i <;> norm_num [twoRightLevel] at * <;> linarith [hx.1, hx.2]
  · rintro _ ⟨x, hx, rfl⟩
    change twoBlockCurve.essentialPrice x = twoRightLevel i at hx
    rw [essential_twoBlock_price] at hx
    fin_cases i <;> norm_num [twoRightLevel] at *
    · exact hx.le
    · exact x.property.2

theorem essentialThree_cellSup (i : Fin 3) : cellSup essentialThreeMinimal i = (i : ℝ) + 1 := by
  apply cellSup_eq_of_interval_bounds essentialThreeMinimal i (l := i) (by linarith)
  · intro x hx
    have hxdom : x ∈ Icc (0 : ℝ) 3 := by
      fin_cases i <;> norm_num at hx <;> constructor <;> linarith [hx.1, hx.2]
    refine ⟨⟨x, hxdom⟩, ?_, rfl⟩
    change threeBlockCurve.essentialPrice _ = threeRightLevel i
    rw [essential_threeBlock_price]
    fin_cases i
    · norm_num at hx
      simp [threeRightLevel, hx.2]
    · norm_num at hx
      have hx1 : ¬x < 1 := by linarith [hx.1]
      simp [threeRightLevel, hx1, hx.2]
    · norm_num at hx
      have hx1 : ¬x < 1 := by linarith [hx.1]
      have hx2 : ¬x < 2 := by linarith [hx.1]
      simp [threeRightLevel, hx1, hx2]
  · rintro _ ⟨x, hx, rfl⟩
    change threeBlockCurve.essentialPrice x = threeRightLevel i at hx
    rw [essential_threeBlock_price] at hx
    fin_cases i <;> norm_num [threeRightLevel] at *
    · split_ifs at hx <;> norm_num at hx
      all_goals linarith
    · split_ifs at hx <;> norm_num at hx
      all_goals linarith
    · exact x.property.2

theorem rightCount_of_all_active {f : PriceCurve} (m : MinimalRepresentation f)
    (h : ∀ i, RightActive m i) : rightCount m = m.blockCount := by
  classical
  have hall : rightActiveCells m = Finset.univ := by ext i; simp [h i]
  simp [rightCount, hall]

theorem rightCell_val_of_all_active {f : PriceCurve} (m : MinimalRepresentation f)
    (h : ∀ i, RightActive m i) (j : Fin (rightCount m)) : (rightCell m j).val = j.val := by
  have hc := rightCount_of_all_active m h
  let q : Fin m.blockCount → Fin m.blockCount := fun i => rightCell m (Fin.cast hc.symm i)
  have hq : StrictMono q := (rightCell m).strictMono.comp (Fin.castOrderIso hc.symm).strictMono
  have hqid (i) : q i = i := le_antisymm (hq.le_id i) (hq.id_le i)
  simpa [q] using congrArg Fin.val (hqid (Fin.cast hc j))

theorem canonicalRightKnot_eq_natCast {f : PriceCurve} (m : MinimalRepresentation f)
    (hactive : ∀ i, RightActive m i) (hsup : ∀ i, cellSup m i = (i : ℝ) + 1)
    (j : Fin (rightCount m + 1)) : canonicalRightKnot m j = (j : ℝ) := by
  cases j using Fin.cases with
  | zero => simp [canonicalRightKnot_zero]
  | succ j =>
      rw [canonicalRightKnot_succ, hsup]
      have hj := rightCell_val_of_all_active m hactive j
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      change max 0 ((rightCell m j).val + 1 : ℝ) = (j.val : ℝ) + 1
      rw [hj, max_eq_right (by positivity)]

theorem essentialTwo_all_rightActive (i : Fin 2) : RightActive essentialTwoMinimal i := by
  have hdom : (i : ℝ) + 1 / 2 ∈ Icc (0 : ℝ) 2 := by fin_cases i <;> norm_num
  refine ⟨⟨(i : ℝ) + 1 / 2, hdom⟩, ?_, by positivity⟩
  change twoBlockCurve.essentialPrice _ = twoRightLevel i
  rw [essential_twoBlock_price]
  fin_cases i <;> norm_num [twoRightLevel]

theorem essentialThree_all_rightActive (i : Fin 3) : RightActive essentialThreeMinimal i := by
  have hdom : (i : ℝ) + 1 / 2 ∈ Icc (0 : ℝ) 3 := by fin_cases i <;> norm_num
  refine ⟨⟨(i : ℝ) + 1 / 2, hdom⟩, ?_, by positivity⟩
  change threeBlockCurve.essentialPrice _ = threeRightLevel i
  rw [essential_threeBlock_price]
  fin_cases i <;> norm_num [threeRightLevel]

theorem canonical_volume_nonpos_of_left_zero {f : PriceCurve} (hl : f.leftEndpoint = 0)
    (u : Parameter) (hu : (u : ℝ) ≤ 0) : (canonicalSidedEncoding f u).1 = 0 := by
  let p := sidedAdmissibleParametrisation (canonicalCertificate f).knots
  change (p u : ℝ) = 0
  apply le_antisymm
  · have h := p.monotone (show u ≤ parameterZero from hu)
    simpa only [p.map_zero] using h
  · simpa only [canonicalCertificate_curve, PriceCurve.essential, hl] using (p u).property.1

theorem canonicalTwo_volume (u : Parameter) (hu : 0 ≤ (u : ℝ)) :
    (canonicalSidedEncoding twoBlockCurve u).1 = 2 * (u : ℝ) := by
  by_cases hu0 : (u : ℝ) ≤ 0
  · rw [canonical_volume_nonpos_of_left_zero rfl u hu0, le_antisymm hu0 hu]
    norm_num
  · unfold canonicalSidedEncoding canonicalCertificate
    rw [chosenMinimalRepresentation_eq _ essentialTwoMinimal]
    change sidedVolumeReal (canonicalSidedKnotDataOfMinimal essentialTwoMinimal) u = _
    rw [sidedVolumeReal, if_neg hu0]
    change uniformInterpolation (canonicalRightKnot essentialTwoMinimal) (u : ℝ) = _
    have hk : canonicalRightKnot essentialTwoMinimal =
        fun j : Fin (rightCount essentialTwoMinimal + 1) => (j : ℝ) :=
      funext (canonicalRightKnot_eq_natCast essentialTwoMinimal
        essentialTwo_all_rightActive essentialTwo_cellSup)
    rw [hk]
    have hc : rightCount essentialTwoMinimal = 2 :=
      rightCount_of_all_active _ essentialTwo_all_rightActive
    rw [hc]
    exact uniformInterpolation_twoRightKnot hu u.property.2

theorem canonicalThree_volume (u : Parameter) (hu : 0 ≤ (u : ℝ)) :
    (canonicalSidedEncoding threeBlockCurve u).1 = 3 * (u : ℝ) := by
  by_cases hu0 : (u : ℝ) ≤ 0
  · rw [canonical_volume_nonpos_of_left_zero rfl u hu0, le_antisymm hu0 hu]
    norm_num
  · unfold canonicalSidedEncoding canonicalCertificate
    rw [chosenMinimalRepresentation_eq _ essentialThreeMinimal]
    change sidedVolumeReal (canonicalSidedKnotDataOfMinimal essentialThreeMinimal) u = _
    rw [sidedVolumeReal, if_neg hu0]
    change uniformInterpolation (canonicalRightKnot essentialThreeMinimal) (u : ℝ) = _
    have hk : canonicalRightKnot essentialThreeMinimal =
        fun j : Fin (rightCount essentialThreeMinimal + 1) => (j : ℝ) :=
      funext (canonicalRightKnot_eq_natCast essentialThreeMinimal
        essentialThree_all_rightActive essentialThree_cellSup)
    rw [hk]
    have hc : rightCount essentialThreeMinimal = 3 :=
      rightCount_of_all_active _ essentialThree_all_rightActive
    rw [hc]
    exact uniformInterpolation_threeRightKnot hu u.property.2

theorem sided_volume_nonpos_of_left_zero (c : CanonicalSidedCurve)
    (hl : c.curve.leftEndpoint = 0) (u : Parameter) (hu : (u : ℝ) ≤ 0) :
    (sidedParametrisationOperator c u).1 = 0 := by
  let p := sidedAdmissibleParametrisation c.knots
  change (p u : ℝ) = 0
  apply le_antisymm
  · have h := p.monotone (show u ≤ parameterZero from hu)
    simpa only [p.map_zero] using h
  · simpa only [hl] using (p u).property.1

theorem canonicalTwo_volume_eq_legacy (u : Parameter) :
    (canonicalSidedEncoding twoBlockCurve u).1 =
      (sidedParametrisationOperator canonicalTwoBlockCurve u).1 := by
  by_cases hu : 0 ≤ (u : ℝ)
  · rw [canonicalTwo_volume u hu, canonicalTwoBlock_volume u hu]
  · rw [canonical_volume_nonpos_of_left_zero rfl u (not_le.mp hu).le,
      sided_volume_nonpos_of_left_zero _ rfl u (not_le.mp hu).le]

theorem canonicalThree_volume_eq_legacy (u : Parameter) :
    (canonicalSidedEncoding threeBlockCurve u).1 =
      (sidedParametrisationOperator canonicalThreeBlockCurve u).1 := by
  by_cases hu : 0 ≤ (u : ℝ)
  · rw [canonicalThree_volume u hu, canonicalThreeBlock_volume u hu]
  · rw [canonical_volume_nonpos_of_left_zero rfl u (not_le.mp hu).le,
      sided_volume_nonpos_of_left_zero _ rfl u (not_le.mp hu).le]

theorem canonicalTwo_eq_legacy_of_ne (u : Parameter) (hne : (u : ℝ) ≠ 1 / 2) :
    canonicalSidedEncoding twoBlockCurve u =
      sidedParametrisationOperator canonicalTwoBlockCurve u := by
  have hv := canonicalTwo_volume_eq_legacy u
  apply Prod.ext hv
  change twoBlockCurve.essentialPrice _ = twoBlockPrice _
  rw [essential_twoBlock_price]
  change (if (canonicalSidedEncoding twoBlockCurve u).1 < 1 then 0 else 2) =
    if (sidedParametrisationOperator canonicalTwoBlockCurve u).1 ≤ 1 then 0 else 2
  rw [hv]
  have hvne : (sidedParametrisationOperator canonicalTwoBlockCurve u).1 ≠ 1 := by
    by_cases hu : 0 ≤ (u : ℝ)
    · rw [canonicalTwoBlock_volume u hu]
      intro h
      apply hne
      linarith
    · rw [sided_volume_nonpos_of_left_zero _ rfl u (not_le.mp hu).le]
      norm_num
  split_ifs <;> first | rfl | exact False.elim (hvne (by linarith))

theorem canonicalThree_eq_legacy_of_ne (u : Parameter)
    (hne1 : (u : ℝ) ≠ 1 / 3) (hne2 : (u : ℝ) ≠ 2 / 3) :
    canonicalSidedEncoding threeBlockCurve u =
      sidedParametrisationOperator canonicalThreeBlockCurve u := by
  have hv := canonicalThree_volume_eq_legacy u
  apply Prod.ext hv
  change threeBlockCurve.essentialPrice _ = threeBlockPrice _
  rw [essential_threeBlock_price]
  change (if (canonicalSidedEncoding threeBlockCurve u).1 < 1 then 0
      else if (canonicalSidedEncoding threeBlockCurve u).1 < 2 then 1 else 3) =
    if (sidedParametrisationOperator canonicalThreeBlockCurve u).1 ≤ 1 then 0
      else if (sidedParametrisationOperator canonicalThreeBlockCurve u).1 ≤ 2 then 1 else 3
  rw [hv]
  have hvne1 : (sidedParametrisationOperator canonicalThreeBlockCurve u).1 ≠ 1 := by
    by_cases hu : 0 ≤ (u : ℝ)
    · rw [canonicalThreeBlock_volume u hu]
      intro h
      apply hne1
      linarith
    · rw [sided_volume_nonpos_of_left_zero _ rfl u (not_le.mp hu).le]
      norm_num
  have hvne2 : (sidedParametrisationOperator canonicalThreeBlockCurve u).1 ≠ 2 := by
    by_cases hu : 0 ≤ (u : ℝ)
    · rw [canonicalThreeBlock_volume u hu]
      intro h
      apply hne2
      linarith
    · rw [sided_volume_nonpos_of_left_zero _ rfl u (not_le.mp hu).le]
      norm_num
  split_ifs <;> first
    | rfl
    | exact False.elim (hvne1 (by linarith))
    | exact False.elim (hvne2 (by linarith))

theorem canonicalTwo_ae_eq_legacy :
    (fun x : ℝ => canonicalSidedEncoding twoBlockCurve (clampParameter x)) =ᵐ[
      sidedLebesgueMeasure]
    (fun x => sidedParametrisationOperator canonicalTwoBlockCurve (clampParameter x)) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    Measure.ae_ne sidedLebesgueMeasure (1 / 2 : ℝ)] with x hx hne
  apply canonicalTwo_eq_legacy_of_ne
  simpa [clampParameter, min_eq_right hx.2, max_eq_right hx.1] using hne

theorem canonicalThree_ae_eq_legacy :
    (fun x : ℝ => canonicalSidedEncoding threeBlockCurve (clampParameter x)) =ᵐ[
      sidedLebesgueMeasure]
    (fun x => sidedParametrisationOperator canonicalThreeBlockCurve (clampParameter x)) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    Measure.ae_ne sidedLebesgueMeasure (1 / 3 : ℝ),
    Measure.ae_ne sidedLebesgueMeasure (2 / 3 : ℝ)]
      with x hx hne1 hne2
  apply canonicalThree_eq_legacy_of_ne
  · simpa [clampParameter, min_eq_right hx.2, max_eq_right hx.1] using hne1
  · simpa [clampParameter, min_eq_right hx.2, max_eq_right hx.1] using hne2

end Thesis.DayAhead.SidedCertificate
