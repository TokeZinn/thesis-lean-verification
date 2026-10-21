import Thesis.DayAhead.ClearingOperatorPriceCurves.SelectedGraphAdmissible
import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedNonconvexity

/-! # The exact two-curve nonconvexity example, with selected knot values -/

noncomputable section
namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation Set

/-- Original label: `exmp:sided-average-not-canonical`. -/
def selectedTwoThreeAverage : ActualRepresentative :=
  representativeCombination (1 / 2) (1 / 2)
    (canonicalSidedEncoding twoBlockCurve) (canonicalSidedEncoding threeBlockCurve)

def selectedAverageGraph : SelectedGraphAdmissiblePair :=
  selectedConicCombination (1 / 2) (1 / 2)
    (canonicalSelectedGraph twoBlockCurve) (canonicalSelectedGraph threeBlockCurve)
    (by norm_num) (by norm_num)

theorem selectedAverageGraph_representative :
    selectedGraphRepresentative selectedAverageGraph = selectedTwoThreeAverage := rfl

theorem selectedTwoThreeAverage_volume (u : Parameter) (hu : 0 ≤ (u : ℝ)) :
    (selectedTwoThreeAverage u).1 = (5 / 2 : ℝ) * u := by
  change (1 / 2 : ℝ) * (canonicalSidedEncoding twoBlockCurve u).1 +
    (1 / 2 : ℝ) * (canonicalSidedEncoding threeBlockCurve u).1 = _
  rw [canonicalTwo_volume u hu, canonicalThree_volume u hu]
  ring

theorem canonicalTwo_price (u : Parameter) (hu : 0 ≤ (u : ℝ)) :
    (canonicalSidedEncoding twoBlockCurve u).2 = if (u : ℝ) < 1 / 2 then 0 else 2 := by
  change twoBlockCurve.essentialPrice _ = _
  rw [essential_twoBlock_price]
  change (if (canonicalSidedEncoding twoBlockCurve u).1 < 1 then 0 else 2) = _
  rw [canonicalTwo_volume u hu]
  split_ifs <;> first | rfl | linarith

theorem canonicalThree_price (u : Parameter) (hu : 0 ≤ (u : ℝ)) :
    (canonicalSidedEncoding threeBlockCurve u).2 =
      if (u : ℝ) < 1 / 3 then 0 else if (u : ℝ) < 2 / 3 then 1 else 3 := by
  change threeBlockCurve.essentialPrice _ = _
  rw [essential_threeBlock_price]
  change (if (canonicalSidedEncoding threeBlockCurve u).1 < 1 then 0
    else if (canonicalSidedEncoding threeBlockCurve u).1 < 2 then 1 else 3) = _
  rw [canonicalThree_volume u hu]
  split_ifs <;> first | rfl | linarith

/-- Original label: `exmp:sided-average-not-canonical`.
The four levels change at the exact current right-continuous breakpoints. -/
theorem selectedTwoThreeAverage_price (u : Parameter) (hu : 0 ≤ (u : ℝ)) :
    (selectedTwoThreeAverage u).2 =
      if (u : ℝ) < 1 / 3 then 0 else if (u : ℝ) < 1 / 2 then 1 / 2
      else if (u : ℝ) < 2 / 3 then 3 / 2 else 5 / 2 := by
  change (1 / 2 : ℝ) * (canonicalSidedEncoding twoBlockCurve u).2 +
    (1 / 2 : ℝ) * (canonicalSidedEncoding threeBlockCurve u).2 = _
  rw [canonicalTwo_price u hu, canonicalThree_price u hu]
  split_ifs <;> norm_num at * <;> linarith

/-- Original label: `exmp:sided-average-not-canonical`.
The decoded cell endpoints are the images of the three breakpoints and one. -/
theorem selectedTwoThreeAverage_endpoints :
    (selectedTwoThreeAverage ⟨1 / 3, by constructor <;> norm_num⟩).1 = 5 / 6 ∧
    (selectedTwoThreeAverage ⟨1 / 2, by constructor <;> norm_num⟩).1 = 5 / 4 ∧
    (selectedTwoThreeAverage ⟨2 / 3, by constructor <;> norm_num⟩).1 = 5 / 3 ∧
    (selectedTwoThreeAverage parameterRight).1 = 5 / 2 ∧
    (selectedTwoThreeAverage ⟨1 / 4, by constructor <;> norm_num⟩).1 = 5 / 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [selectedTwoThreeAverage_volume _ (by norm_num [parameterRight])] <;>
    norm_num [parameterRight]

theorem selectedTwoThreeAverage_nonpos (u : Parameter) (hu : (u : ℝ) ≤ 0) :
    selectedTwoThreeAverage u = (0, 0) := by
  have hf := canonical_volume_nonpos_of_left_zero (f := twoBlockCurve) rfl u hu
  have hg := canonical_volume_nonpos_of_left_zero (f := threeBlockCurve) rfl u hu
  apply Prod.ext
  · change (1 / 2 : ℝ) * (canonicalSidedEncoding twoBlockCurve u).1 +
      (1 / 2 : ℝ) * (canonicalSidedEncoding threeBlockCurve u).1 = 0
    rw [hf, hg]
    ring
  · have hfp : (canonicalSidedEncoding twoBlockCurve u).2 = 0 := by
      change twoBlockCurve.essentialPrice _ = 0
      rw [essential_twoBlock_price]
      change (if (canonicalSidedEncoding twoBlockCurve u).1 < 1 then 0 else 2) = 0
      rw [hf]
      norm_num
    have hgp : (canonicalSidedEncoding threeBlockCurve u).2 = 0 := by
      change threeBlockCurve.essentialPrice _ = 0
      rw [essential_threeBlock_price]
      change (if (canonicalSidedEncoding threeBlockCurve u).1 < 1 then 0
        else if (canonicalSidedEncoding threeBlockCurve u).1 < 2 then 1 else 3) = 0
      rw [hg]
      norm_num
    change (1 / 2 : ℝ) * (canonicalSidedEncoding twoBlockCurve u).2 +
      (1 / 2 : ℝ) * (canonicalSidedEncoding threeBlockCurve u).2 = 0
    rw [hfp, hgp]
    ring

def selectedAverageCurve : PriceCurve := (selectedGraphDecoder selectedAverageGraph).val

theorem selectedAverageCurve_essential : selectedAverageCurve.essential = selectedAverageCurve :=
  selectedAverageGraph.decode_essential

theorem selectedAverageCurve_endpoints :
    selectedAverageCurve.leftEndpoint = 0 ∧ selectedAverageCurve.rightEndpoint = 5 / 2 := by
  constructor
  · change (selectedTwoThreeAverage parameterLeft).1 = 0
    rw [selectedTwoThreeAverage_nonpos _ (by norm_num [parameterLeft])]
  · exact selectedTwoThreeAverage_endpoints.2.2.2.1

theorem selectedAverageCurve_price
    (x : Icc selectedAverageCurve.leftEndpoint selectedAverageCurve.rightEndpoint) :
    selectedAverageCurve.price x = if (x : ℝ) < 5 / 6 then 0
      else if (x : ℝ) < 5 / 4 then 1 / 2 else if (x : ℝ) < 5 / 3 then 3 / 2 else 5 / 2 := by
  let q := selectedAverageGraph.toGraphAdmissiblePair
  obtain ⟨u, hu⟩ := (toVolumeRange q x).property
  change decodedPrice q x = _
  rw [q.decodedPrice_eq_of_volume x u hu]
  change (selectedTwoThreeAverage u).2 = _
  change (selectedTwoThreeAverage u).1 = (x : ℝ) at hu
  by_cases hu0 : 0 ≤ (u : ℝ)
  · rw [selectedTwoThreeAverage_price u hu0]
    rw [selectedTwoThreeAverage_volume u hu0] at hu
    split_ifs <;> first | rfl | linarith
  · rw [selectedTwoThreeAverage_nonpos u (not_le.mp hu0).le] at hu ⊢
    norm_num at hu
    simp [← hu]

def averageFourLevels : Fin 4 → ℝ := ![0, 1 / 2, 3 / 2, 5 / 2]

def selectedAverageMinimal : MinimalRepresentation selectedAverageCurve :=
  minimalRepresentationOfLevels _ (by norm_num : 0 < 4) averageFourLevels
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [averageFourLevels] at *) (by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨⟨((i : ℝ) + 1) / 2, ?_⟩, ?_⟩
        · rw [selectedAverageCurve_endpoints.1, selectedAverageCurve_endpoints.2]
          fin_cases i <;> norm_num
        · rw [selectedAverageCurve_price]
          fin_cases i <;> norm_num [averageFourLevels]
      · rintro ⟨x, rfl⟩
        rw [selectedAverageCurve_price]
        split_ifs
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩)

def averageLowerEndpoints : Fin 4 → ℝ := ![0, 5 / 6, 5 / 4, 5 / 3]
def averageUpperEndpoints : Fin 4 → ℝ := ![5 / 6, 5 / 4, 5 / 3, 5 / 2]

theorem selectedAverage_cellSup (i : Fin 4) :
    cellSup selectedAverageMinimal i = averageUpperEndpoints i := by
  apply cellSup_eq_of_interval_bounds selectedAverageMinimal i
    (l := averageLowerEndpoints i)
    (by fin_cases i <;> norm_num [averageLowerEndpoints, averageUpperEndpoints])
  · intro x hx
    have hxdom : x ∈ Icc selectedAverageCurve.leftEndpoint selectedAverageCurve.rightEndpoint := by
      rw [selectedAverageCurve_endpoints.1, selectedAverageCurve_endpoints.2]
      fin_cases i <;> norm_num [averageLowerEndpoints, averageUpperEndpoints] at hx <;>
        constructor <;> linarith [hx.1, hx.2]
    refine ⟨⟨x, hxdom⟩, ?_, rfl⟩
    change selectedAverageCurve.price _ = averageFourLevels i
    rw [selectedAverageCurve_price]
    fin_cases i <;> norm_num [averageLowerEndpoints, averageUpperEndpoints, averageFourLevels] at *
    all_goals split_ifs <;> norm_num at * <;> linarith [hx.1, hx.2]
  · rintro _ ⟨x, hx, rfl⟩
    change selectedAverageCurve.price x = averageFourLevels i at hx
    rw [selectedAverageCurve_price] at hx
    have hxR : (x : ℝ) ≤ 5 / 2 := by
      simpa only [selectedAverageCurve_endpoints.2] using x.property.2
    fin_cases i <;> norm_num [averageFourLevels, averageUpperEndpoints] at *
    all_goals split_ifs at hx <;> norm_num at hx <;> linarith

theorem selectedAverage_all_rightActive (i : Fin 4) :
    RightActive selectedAverageMinimal i := by
  have hdom : ((i : ℝ) + 1) / 2 ∈
      Icc selectedAverageCurve.leftEndpoint selectedAverageCurve.rightEndpoint := by
    rw [selectedAverageCurve_endpoints.1, selectedAverageCurve_endpoints.2]
    fin_cases i <;> norm_num
  refine ⟨⟨((i : ℝ) + 1) / 2, hdom⟩, ?_, by positivity⟩
  change selectedAverageCurve.price _ = averageFourLevels i
  rw [selectedAverageCurve_price]
  fin_cases i <;> norm_num [averageFourLevels]

/-- Original label: `exmp:sided-average-not-canonical`.
The decoded curve has four positive-side blocks, so its first canonical knot
is the physical endpoint 5/6 at parameter 1/4. -/
theorem selectedAverage_canonical_quarter :
    (canonicalSidedEncoding selectedAverageCurve
      ⟨1 / 4, by constructor <;> norm_num⟩).1 = 5 / 6 := by
  unfold canonicalSidedEncoding canonicalCertificate
  rw [selectedAverageCurve_essential,
    chosenMinimalRepresentation_eq _ selectedAverageMinimal]
  change sidedVolumeReal (canonicalSidedKnotDataOfMinimal selectedAverageMinimal) (1 / 4) = _
  rw [sidedVolumeReal, if_neg (by norm_num : ¬(1 / 4 : ℝ) ≤ 0)]
  change uniformInterpolation (canonicalRightKnot selectedAverageMinimal) (1 / 4) = _
  have hc : rightCount selectedAverageMinimal = 4 :=
    rightCount_of_all_active _ selectedAverage_all_rightActive
  let j : Fin (rightCount selectedAverageMinimal) := ⟨0, by rw [hc]; decide⟩
  have hk0 : canonicalRightKnot selectedAverageMinimal j.castSucc = 0 :=
    canonicalRightKnot_zero _
  have hj : rightCell selectedAverageMinimal j = (0 : Fin 4) :=
    Fin.ext (rightCell_val_of_all_active _ selectedAverage_all_rightActive j)
  have hk1 : canonicalRightKnot selectedAverageMinimal j.succ = 5 / 6 := by
    rw [canonicalRightKnot_succ, hj, selectedAverage_cellSup]
    norm_num [averageUpperEndpoints]
  rw [uniformInterpolation_on_block _ j (by simp [j]) (by norm_num [j, hc]), hk0, hk1]
  norm_num [j, hc]

/-- Original label: `exmp:sided-average-not-canonical`.
Decoding and then canonically re-encoding changes the actual average. -/
theorem selectedAverage_decode_reencode_ne :
    canonicalSidedEncoding selectedAverageCurve ≠ selectedTwoThreeAverage := by
  intro h
  have he := congrArg (fun z : ActualRepresentative =>
    (z ⟨1 / 4, by constructor <;> norm_num⟩).1) h
  dsimp only at he
  rw [selectedAverage_canonical_quarter, selectedTwoThreeAverage_endpoints.2.2.2.2] at he
  norm_num at he

theorem selectedTwoThreeAverage_ae_legacy :
    (fun x => selectedTwoThreeAverage (clampParameter x)) =ᵐ[
      SidedCurveLp.sidedLebesgueMeasure] (fun x => twoThreeAverage (clampParameter x)) := by
  filter_upwards [canonicalTwo_ae_eq_legacy, canonicalThree_ae_eq_legacy] with x hf hg
  simp only [selectedTwoThreeAverage, representativeCombination, hf, hg, twoThreeAverage]

/-- Original label: `exmp:sided-average-not-canonical`.
The actual selected average remains outside the image after almost-everywhere
identification; it is not merely an endpoint-value discrepancy. -/
theorem selectedTwoThreeAverage_not_ae_in_range :
    ¬ ∃ f : PriceCurve, (fun x => canonicalSidedEncoding f (clampParameter x)) =ᵐ[
      SidedCurveLp.sidedLebesgueMeasure] (fun x => selectedTwoThreeAverage (clampParameter x)) := by
  rintro ⟨f, hf⟩
  exact twoThreeAverage_not_ae_in_canonical_range
    ⟨f, hf.trans selectedTwoThreeAverage_ae_legacy⟩

theorem selectedTwoThreeAverage_not_in_range :
    selectedTwoThreeAverage ∉ range canonicalSidedEncoding := by
  rintro ⟨f, hf⟩
  exact selectedTwoThreeAverage_not_ae_in_range
    ⟨f, Filter.Eventually.of_forall (fun x => congrFun hf (clampParameter x))⟩

open CanonicalSidedLp PriceCurveHilbert MeasureTheory in
/-- Original label: `exmp:sided-average-not-canonical`.
The explicit midpoint of the two actual Hilbert encodings is outside the
canonical Hilbert image. -/
theorem selectedTwoThreeHilbert_not_in_range :
    (1 / 2 : ℝ) • canonicalSidedEncodingLpReal twoBlockCurve +
      (1 / 2 : ℝ) • canonicalSidedEncodingLpReal threeBlockCurve ∉
        range canonicalSidedEncodingLpReal := by
  rintro ⟨f, hf⟩
  apply selectedTwoThreeAverage_not_ae_in_range
  refine ⟨f, ?_⟩
  filter_upwards [coeFn_canonicalSidedEncodingLpReal f,
    coeFn_canonicalSidedEncodingLpReal twoBlockCurve,
    coeFn_canonicalSidedEncodingLpReal threeBlockCurve,
    Lp.coeFn_add ((1 / 2 : ℝ) • canonicalSidedEncodingLpReal twoBlockCurve)
      ((1 / 2 : ℝ) • canonicalSidedEncodingLpReal threeBlockCurve),
    Lp.coeFn_smul (1 / 2 : ℝ) (canonicalSidedEncodingLpReal twoBlockCurve),
    Lp.coeFn_smul (1 / 2 : ℝ) (canonicalSidedEncodingLpReal threeBlockCurve)]
    with x hF htwo hthree hadd hst hsg
  apply pairEquiv.injective
  have he := congrArg (fun z : PriceHilbertSpace SidedCurveLp.sidedLebesgueMeasure => z x) hf
  dsimp only at he
  dsimp only [Pi.add_apply, Pi.smul_apply] at hadd hst hsg
  rw [hF, hadd, hst, hsg, htwo, hthree] at he
  simpa only [selectedTwoThreeAverage, representativeCombination, map_add, map_smul] using he

end Thesis.DayAhead.SidedCertificate
