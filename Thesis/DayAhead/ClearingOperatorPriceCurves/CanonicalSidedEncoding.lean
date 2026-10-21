import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialSidedCertificate
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveGraph

/-!
# The total canonical sided encoder

The current thesis first chooses the essential representative, then counts
its positive-length sided blocks. The total function on `PriceCurve` factors
through this normalization; actual injectivity is stated on essential curves.
-/

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves SidedParametrisation Set

noncomputable section

/-- A fixed minimal representation, used only to make the thesis operator a
literal total Lean function. -/
noncomputable def chosenMinimalRepresentation (f : PriceCurve) :
    MinimalRepresentation f :=
  Classical.choice (exists_minimalRepresentation f)

/-- The current thesis's canonical certificate: normalize isolated knot
values before choosing and counting the minimal cells. -/
noncomputable def canonicalCertificate (f : PriceCurve) :
    CanonicalSidedCurve :=
  canonicalSidedCurveOfMinimal (chosenMinimalRepresentation f.essential)

/--
Thesis source: Definition `defn:parametrisation-operator` in
`2 - day-ahead/2_clearing_operator_price_curves.tex`.

Original label: `defn:parametrisation-operator`.

The current chapter's actual sided parametrisation of the selected essential
representative. On arbitrary curves it deliberately forgets isolated knot
values. On the essential-curve domain used in this section it is injective.
-/
noncomputable def canonicalSidedEncoding (f : PriceCurve) :
    ActualRepresentative :=
  sidedParametrisationOperator (canonicalCertificate f)

@[simp] theorem canonicalCertificate_curve (f : PriceCurve) :
    (canonicalCertificate f).curve = f.essential := rfl

/-- Each left block counted by the revised encoder has positive physical
Lebesgue measure; no singleton is allocated a full parameter block. -/
theorem canonical_left_block_positive_volume (f : PriceCurve)
    (j : Fin (leftCount (chosenMinimalRepresentation f.essential))) :
    0 < MeasureTheory.volume (cellReal (chosenMinimalRepresentation f.essential)
      (leftCell (chosenMinimalRepresentation f.essential) j) ∩ Iio 0) :=
  essential_left_cell_positive_volume f _ _ (leftCell_active _ j)

/-- The corresponding positive-length statement on the right side. -/
theorem canonical_right_block_positive_volume (f : PriceCurve)
    (j : Fin (rightCount (chosenMinimalRepresentation f.essential))) :
    0 < MeasureTheory.volume (cellReal (chosenMinimalRepresentation f.essential)
      (rightCell (chosenMinimalRepresentation f.essential) j) ∩ Ioi 0) :=
  essential_right_cell_positive_volume f _ _ (rightCell_active _ j)

/-- Original label: `eq:sided-parametrisation-recovers-graph`.
For the normalized construction, the recovered graph is precisely that of
the essential representative. -/
theorem range_canonicalSidedEncoding (f : PriceCurve) :
    range (canonicalSidedEncoding f) = f.essential.graph :=
  range_parametrisedGraph _ (sidedAdmissibleParametrisation (canonicalCertificate f).knots)

theorem canonicalSidedEncoding_essential (f : PriceCurve) :
    canonicalSidedEncoding f.essential = canonicalSidedEncoding f := by
  unfold canonicalSidedEncoding canonicalCertificate
  rw [f.essential_idempotent]

theorem canonicalSidedEncoding_eq_iff_essential_eq (f g : PriceCurve) :
    canonicalSidedEncoding f = canonicalSidedEncoding g ↔ f.essential = g.essential := by
  constructor
  · intro h
    apply PriceCurve.graph_injective
    rw [← range_canonicalSidedEncoding f, ← range_canonicalSidedEncoding g, h]
  · intro h
    unfold canonicalSidedEncoding canonicalCertificate
    rw [h]

/-- The actual sided operator on the section's essential-curve domain. -/
def essentialSidedEncoding (f : EssentialPriceCurve) : ActualRepresentative :=
  canonicalSidedEncoding f.val

/-- Original label: `eq:sided-parametrisation-recovers-graph`.
The actual sided operator is injective on essential representatives. -/
theorem essentialSidedEncoding_injective : Function.Injective essentialSidedEncoding := by
  intro f g h
  apply Subtype.ext
  have he := (canonicalSidedEncoding_eq_iff_essential_eq f.val g.val).mp h
  simpa only [f.property, g.property] using he

end


end Thesis.DayAhead.SidedCertificate
