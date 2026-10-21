import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLSourceCarrier
import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLPositiveDepth
import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLBorel
import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLMoment
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLSourceRepresentative
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # The complete literal published-list measurability proposition

Original label: `prop:pl-encoding-measurable`.
The actual source state space uses the Hausdorff tuple-product subspace
Borel structure. Fixed-length comparison cells construct the true canonical
encoding; countable length pasting and restriction give its Borel map on
the literal source domain. The source-selected right/terminal-left version
has the same L² class. Raw midpoint crossing prices remain separate. The
depth second moment then gives square integrability without a separately
assumed measurability or calibration certificate.
-/

noncomputable section
namespace Thesis.DayAhead.VendorPLSourceTheorem

open Set MeasureTheory VendorPLParser VendorPLVertices VendorPLSourceCarrier
open VendorPLPositiveDepth PriceCurves PriceCurveHilbert

variable {lo hi : ℝ} (hlohi : lo ≤ hi)

theorem source_positive_depths (m : Source hlohi) :
    0 < (sourceBook hlohi m).buyDepth ∧ 0 < (sourceBook hlohi m).sellDepth := by
  have hs := (datum_spec hlohi m).2.2.1
  have hb := (datum_spec hlohi m).2.2.2.1
  exact ⟨(buyDepth_pos_iff_raw_positive hlohi _).mpr hb,
    (sellDepth_pos_iff_raw_positive hlohi _).mpr hs⟩

variable (ν : Measure Parameter) [IsFiniteMeasure ν] [NoAtoms ν]

def rawEncoding (m : Source hlohi) : PriceHilbertSpace ν :=
  PLCanonicalEncoding.encodingLp ν (InterpolatedImpactCurve.Book.impactCurve (sourceBook hlohi m))

/-- The actual source convention is right-continuous below the upper
quantity endpoint and takes the left limit at that endpoint. -/
def encoding (m : Source hlohi) : PriceHilbertSpace ν :=
  PLCanonicalEncoding.encodingLp ν (PLSourceRepresentative.representative
    (InterpolatedImpactCurve.Book.impactCurve (sourceBook hlohi m)))

theorem encoding_eq_raw (m : Source hlohi) : encoding hlohi ν m = rawEncoding hlohi ν m :=
  PLSourceRepresentative.book_encodingLp_representative ν (sourceBook hlohi m)
    (source_positive_depths hlohi m).1 (source_positive_depths hlohi m).2

def boundedEncoding (ns nb : ℕ) : BoundedLayer lo hi ns nb → PriceHilbertSpace ν :=
  positiveExtension hlohi 0 (fun x => PLCanonicalEncoding.encodingLp ν
    (InterpolatedImpactCurve.Book.impactCurve (book hlohi x.val)))

theorem measurable_boundedEncoding (ns nb : ℕ) :
    @Measurable (BoundedLayer lo hi ns nb) (PriceHilbertSpace ν) _ (borel (PriceHilbertSpace ν))
      (boundedEncoding hlohi ν ns nb) := by
  letI : MeasurableSpace (PriceHilbertSpace ν) := borel (PriceHilbertSpace ν)
  exact measurable_positiveExtension hlohi 0 _
    (VendorPLBorel.measurable_encoding_positive_layer hlohi ν)

omit [NoAtoms ν] in
theorem sourceMap_boundedEncoding :
    sourceMap hlohi (boundedEncoding hlohi ν) = rawEncoding hlohi ν := by
  funext m
  dsimp only [sourceMap, boundedEncoding]
  have hpos : 0 < (book hlohi (datum hlohi m).2.2).buyDepth ∧
      0 < (book hlohi (datum hlohi m).2.2).sellDepth := source_positive_depths hlohi m
  rw [positiveExtension, dif_pos hpos]
  rfl

theorem measurable_rawEncoding :
    @Measurable (Source hlohi) (PriceHilbertSpace ν) _ (borel (PriceHilbertSpace ν))
      (rawEncoding hlohi ν) := by
  letI : MeasurableSpace (PriceHilbertSpace ν) := borel (PriceHilbertSpace ν)
  rw [← sourceMap_boundedEncoding hlohi ν]
  exact measurable_sourceMap hlohi 0 _ (measurable_boundedEncoding hlohi ν)

/-- Original label: `prop:pl-encoding-measurable`.
First Hilbert-valued conclusion of the literal source proposition: `m ↦ Z(m) = Ψ̄(P_m)` is
Borel measurable on the literal vendor-list state space `𝓛`, by the fixed-length layer
decomposition and the finite Borel partition into cells of continuity. -/
theorem measurable_encoding :
    @Measurable (Source hlohi) (PriceHilbertSpace ν) _ (borel (PriceHilbertSpace ν))
      (encoding hlohi ν) := by
  have he : encoding hlohi ν = rawEncoding hlohi ν := funext (encoding_eq_raw hlohi ν)
  rw [he]
  exact measurable_rawEncoding hlohi ν

def crossingPrice (m : Source hlohi) : ℝ := (sourceBook hlohi m).price 0

/-- Original label: `prop:pl-encoding-measurable`.
Second conclusion of the literal source proposition: `m ↦ P_m(0)` is Borel measurable on `𝓛`.
The crossing price uses the original completed-fiber midpoint even
when the L² representative uses a one-sided selected value at zero. -/
theorem measurable_crossingPrice : Measurable (crossingPrice hlohi) := by
  change Measurable (sourceMap hlohi (fun _ _ x => (book hlohi x).price 0))
  apply measurable_sourceMap hlohi 0
  intro ns nb
  exact VendorPLMidpoint.measurable_actual_price hlohi (fun _ => 0) measurable_const
    (fun x => (book hlohi x).zero_mem_domain)

def depth (m : Source hlohi) : ℝ := VendorPLMoment.depth (sourceBook hlohi m)

theorem measurable_depth : Measurable (depth hlohi) := by
  change Measurable (sourceMap hlohi (fun _ _ x => VendorPLMoment.depth (book hlohi x)))
  apply measurable_sourceMap hlohi 0
  intro ns nb
  exact (VendorPLQuantityCells.measurable_buyDepth hlohi).max
    (VendorPLQuantityCells.measurable_sellDepth hlohi)

/-- Original label: `prop:pl-encoding-measurable`.
Third conclusion of the literal source proposition: `E[D(M)²] < ∞` implies
`E[‖Z(M)‖²] < ∞`, with Borel/strong measurability derived from the actual
published lists rather than left as a premise. -/
theorem encoding_memLp_of_depth_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hν : ν.real univ = 2) (M : Ω → Source hlohi) (hM : Measurable M)
    (hdepth : Integrable (fun w => depth hlohi (M w) ^ 2) μ) :
    MemLp (fun w => encoding hlohi ν (M w)) 2 μ := by
  letI : MeasurableSpace (PriceHilbertSpace ν) := borel (PriceHilbertSpace ν)
  letI : BorelSpace (PriceHilbertSpace ν) := ⟨rfl⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hraw : AEStronglyMeasurable (fun w => rawEncoding hlohi ν (M w)) μ :=
    ((measurable_rawEncoding hlohi ν).comp hM).aestronglyMeasurable
  have hm := VendorPLMoment.canonical_memLp_of_depth_second_moment ν hν
    (fun w => sourceBook hlohi (M w)) hraw hdepth
  have he : (fun w => encoding hlohi ν (M w)) = (fun w => rawEncoding hlohi ν (M w)) :=
    funext (fun w => encoding_eq_raw hlohi ν (M w))
  rw [he]
  exact hm

end Thesis.DayAhead.VendorPLSourceTheorem
