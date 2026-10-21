import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLParser
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The source tuple-product carrier and countable list-length pasting

The Hausdorff tuple topology equals the countable coproduct topology from
the source's standard machinery. Paired lists therefore have exactly the
Borel structure used by the explicit fixed-length vendor constructions.
Arbitrary further source restrictions inherit measurability as subspaces;
in particular no ambient Borel proof of positive equilibrium is needed.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Thesis.DayAhead.VendorPLTupleCarrier

open Set MeasureTheory VendorPLParser
open Foundations.MarketRepresentation TuplesMetricTopology

local instance sigmaBorel {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] : BorelSpace (Σ i, X i) where
  measurable_eq := by
    rw [DisjointUnionTopology.borel_sigma_eq]
    congr 1
    funext i
    exact BorelSpace.measurable_eq

abbrev TuplePair := Tuple Point × Tuple Point
abbrev AllLayers := Σ ns : ℕ, Σ nb : ℕ, RawSide ns × RawSide nb

def sigmaHomeomorph {ι : Type*} {X Y : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (h : ∀ i, X i ≃ₜ Y i) : (Σ i, X i) ≃ₜ Σ i, Y i where
  toEquiv := Equiv.sigmaCongrRight (fun i => (h i).toEquiv)
  continuous_toFun := continuous_sigma (fun i => continuous_sigmaMk.comp (h i).continuous)
  continuous_invFun := continuous_sigma (fun i => continuous_sigmaMk.comp (h i).symm.continuous)

def tuplePairHomeomorph : TuplePair ≃ₜ AllLayers :=
  Homeomorph.sigmaProdDistrib.trans
    (sigmaHomeomorph fun _ =>
      (Homeomorph.prodComm _ _).trans (Homeomorph.sigmaProdDistrib.trans
        (sigmaHomeomorph fun _ => Homeomorph.prodComm _ _)))

@[simp] theorem tuplePairHomeomorph_apply (ns nb : ℕ) (x : RawSide ns) (y : RawSide nb) :
    tuplePairHomeomorph (⟨ns, x⟩, ⟨nb, y⟩) = ⟨ns, ⟨nb, (x, y)⟩⟩ := rfl

theorem source_product_borel_eq :
    @borel TuplePair
      (@instTopologicalSpaceProd (Tuple Point) (Tuple Point)
        (tupleHausdorffMetricTopology (X := Point))
        (tupleHausdorffMetricTopology (X := Point))) =
      (inferInstance : MeasurableSpace TuplePair) := by
  rw [tupleHausdorffMetricTopology_eq_sigma]
  exact BorelSpace.measurable_eq.symm

theorem source_restriction_borel_eq (source : Set TuplePair) :
    @borel source (@TopologicalSpace.induced source TuplePair Subtype.val
      (@instTopologicalSpaceProd (Tuple Point) (Tuple Point)
        (tupleHausdorffMetricTopology (X := Point))
        (tupleHausdorffMetricTopology (X := Point)))) =
      (inferInstance : MeasurableSpace source) := by
  rw [tupleHausdorffMetricTopology_eq_sigma]
  exact BorelSpace.measurable_eq.symm

theorem measurable_of_fixed_lengths {Y : Type*} [MeasurableSpace Y] (f : TuplePair → Y)
    (hf : ∀ ns nb : ℕ, Measurable
      (fun x : RawSide ns × RawSide nb => f (⟨ns, x.1⟩, ⟨nb, x.2⟩))) :
    Measurable f := by
  have h : Measurable (fun z : AllLayers => f (⟨z.1, z.2.2.1⟩, ⟨z.2.1, z.2.2.2⟩)) := by
    rw [DisjointUnionTopology.measurable_pasting_iff]
    intro ns
    rw [DisjointUnionTopology.measurable_pasting_iff]
    intro nb
    exact hf ns nb
  convert h.comp tuplePairHomeomorph.measurable using 1

theorem measurableSet_priceBounded (lo hi : ℝ) (ns nb : ℕ) :
    MeasurableSet {x : RawLayer ns nb | priceBounded lo hi x} := by
  unfold priceBounded
  simp only [setOf_and, setOf_forall]
  exact (MeasurableSet.iInter fun i => measurableSet_Icc.preimage
    ((measurable_pi_apply i).comp measurable_fst).fst).inter
    (MeasurableSet.iInter fun i => measurableSet_Icc.preimage
      ((measurable_pi_apply i).comp measurable_snd).fst)

def boundedExtension {Y : Type*} (lo hi : ℝ) (defaultValue : Y)
    (f : ∀ ns nb : ℕ, BoundedLayer lo hi ns nb → Y) : TuplePair → Y
  | (⟨0, _⟩, _) => defaultValue
  | (⟨_ + 1, _⟩, ⟨0, _⟩) => defaultValue
  | (⟨ns + 1, x⟩, ⟨nb + 1, y⟩) =>
    if h : priceBounded lo hi (x, y) then f ns nb ⟨(x, y), h⟩ else defaultValue

theorem measurable_boundedExtension {Y : Type*} [MeasurableSpace Y]
    (lo hi : ℝ) (defaultValue : Y)
    (f : ∀ ns nb : ℕ, BoundedLayer lo hi ns nb → Y)
    (hf : ∀ ns nb, Measurable (f ns nb)) :
    Measurable (boundedExtension lo hi defaultValue f) := by
  apply measurable_of_fixed_lengths
  intro ns nb
  cases ns with
  | zero => exact measurable_const
  | succ ns =>
    cases nb with
    | zero => exact measurable_const
    | succ nb =>
      apply measurable_of_restrict_of_restrict_compl (measurableSet_priceBounded lo hi ns nb)
      · convert hf ns nb using 1
        funext x
        simp only [Set.restrict_apply, boundedExtension, Prod.mk.eta]
        split_ifs with hx
        · rfl
        · exact False.elim (hx x.property)
      · convert (measurable_const : Measurable
          (fun _ : {x : RawLayer ns nb // ¬priceBounded lo hi x} => defaultValue)) using 1
        funext x
        simp only [Set.restrict_apply, boundedExtension, Prod.mk.eta]
        split_ifs with hx
        · exact False.elim (x.property hx)
        · rfl

/-- Restriction to the literal source conditions (including Q>0) is free:
the subtype carries the relative Borel structure even without an ambient
Borel description of that additional predicate. -/
theorem measurable_on_source_restriction {Y : Type*} [MeasurableSpace Y]
    (lo hi : ℝ) (defaultValue : Y)
    (f : ∀ ns nb : ℕ, BoundedLayer lo hi ns nb → Y)
    (hf : ∀ ns nb, Measurable (f ns nb)) (source : Set TuplePair) :
    Measurable (fun x : source => boundedExtension lo hi defaultValue f x.val) :=
  (measurable_boundedExtension lo hi defaultValue f hf).comp measurable_subtype_coe

@[simp] theorem boundedExtension_on_layer {Y : Type*} (lo hi : ℝ) (defaultValue : Y)
    (f : ∀ ns nb : ℕ, BoundedLayer lo hi ns nb → Y) (ns nb : ℕ)
    (x : BoundedLayer lo hi ns nb) :
    boundedExtension lo hi defaultValue f (⟨ns + 1, x.val.1⟩, ⟨nb + 1, x.val.2⟩) =
      f ns nb x := by
  simp only [boundedExtension, dif_pos x.property]

end Thesis.DayAhead.VendorPLTupleCarrier
