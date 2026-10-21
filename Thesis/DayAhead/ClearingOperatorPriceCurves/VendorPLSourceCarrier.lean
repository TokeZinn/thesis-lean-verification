import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLTupleCarrier
import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLVertices
import Thesis.DayAhead.ClearingOperatorPriceCurves.EquilibriumQuantity

/-! # The literal published-list state space of the thesis proposition

Inputs are nonempty bounded price/cumulative-volume lists. The largest
listed price is the upper limit, each raw list has positive maximum volume,
and the actual constructed equilibrium quantity is strictly positive.
The additional equilibrium condition is only a relative-subspace
restriction, just as in the supplied comparison-cell proof.
-/

noncomputable section
namespace Thesis.DayAhead.VendorPLSourceCarrier

open Set MeasureTheory VendorPLParser VendorPLTupleCarrier VendorPLVertices

variable {lo hi : ℝ} (hlohi : lo ≤ hi)

abbrev Datum (lo hi : ℝ) := Σ ns : ℕ, Σ nb : ℕ, BoundedLayer lo hi ns nb

def tuplePair (d : Datum lo hi) : TuplePair :=
  (⟨d.1 + 1, d.2.2.val.1⟩, ⟨d.2.1 + 1, d.2.2.val.2⟩)

def admissible (d : Datum lo hi) : Prop :=
  ((∃ i, (d.2.2.val.1 i).1 = hi) ∨ (∃ j, (d.2.2.val.2 j).1 = hi)) ∧
    (∃ i, 0 < (d.2.2.val.1 i).2) ∧ (∃ j, 0 < (d.2.2.val.2 j).2) ∧
      0 < EquilibriumQuantity.Book.equilibriumQuantity (book hlohi d.2.2)

def sourceSet : Set TuplePair := {t | ∃ d : Datum lo hi, tuplePair d = t ∧ admissible hlohi d}
abbrev Source := sourceSet hlohi

def datum (m : Source hlohi) : Datum lo hi := Classical.choose m.property

theorem datum_spec (m : Source hlohi) :
    tuplePair (datum hlohi m) = m.val ∧ admissible hlohi (datum hlohi m) :=
  Classical.choose_spec m.property

def sourceBook (m : Source hlohi) : ExcessSupply.Book lo hi := book hlohi (datum hlohi m).2.2

theorem sourceBook_positive_equilibrium (m : Source hlohi) :
    0 < EquilibriumQuantity.Book.equilibriumQuantity (sourceBook hlohi m) :=
  (datum_spec hlohi m).2.2.2.2

def sourceMap {Y : Type*} (f : ∀ ns nb : ℕ, BoundedLayer lo hi ns nb → Y)
    (m : Source hlohi) : Y := f (datum hlohi m).1 (datum hlohi m).2.1 (datum hlohi m).2.2

/-- The actual source map is the restriction of countable fixed-length
pasting. The witness selection introduces no measurability premise. -/
theorem sourceMap_eq_boundedExtension {Y : Type*} (defaultValue : Y)
    (f : ∀ ns nb : ℕ, BoundedLayer lo hi ns nb → Y) (m : Source hlohi) :
    sourceMap hlohi f m = boundedExtension lo hi defaultValue f m.val := by
  rw [← (datum_spec hlohi m).1]
  exact (boundedExtension_on_layer lo hi defaultValue f
    (datum hlohi m).1 (datum hlohi m).2.1 (datum hlohi m).2.2).symm

theorem measurable_sourceMap {Y : Type*} [MeasurableSpace Y] (defaultValue : Y)
    (f : ∀ ns nb : ℕ, BoundedLayer lo hi ns nb → Y)
    (hf : ∀ ns nb, Measurable (f ns nb)) : Measurable (sourceMap hlohi f) := by
  have h := measurable_on_source_restriction lo hi defaultValue f hf (sourceSet hlohi)
  convert h using 1
  funext m
  exact sourceMap_eq_boundedExtension hlohi defaultValue f m

/-- Independent choices of a layer witness give the same resulting value. -/
theorem sourceMap_eq_on_datum {Y : Type*} (defaultValue : Y)
    (f : ∀ ns nb : ℕ, BoundedLayer lo hi ns nb → Y)
    (m : Source hlohi) (d : Datum lo hi) (hd : tuplePair d = m.val) :
    sourceMap hlohi f m = f d.1 d.2.1 d.2.2 := by
  rw [sourceMap_eq_boundedExtension hlohi defaultValue f m, ← hd]
  exact boundedExtension_on_layer lo hi defaultValue f d.1 d.2.1 d.2.2

end Thesis.DayAhead.VendorPLSourceCarrier
