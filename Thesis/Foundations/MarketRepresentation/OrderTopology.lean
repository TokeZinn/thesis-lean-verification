import Thesis.Foundations.MarketRepresentation.OrderExamples
import Thesis.Foundations.MarketRepresentation.DisjointUnionTopology
import Mathlib.Analysis.Real.Cardinality

/-! # Why submission time must be a coordinate rather than a component tag -/

noncomputable section

open Set TopologicalSpace

namespace Thesis.Foundations.MarketRepresentation.OrderTopology

open MarketClearing.Sorting DisjointUnionTopology

/-- A separable disjoint union of nonempty spaces has countably many tags. -/
theorem countable_tags_of_separable
    {A : Type*} {X : A → Type*} [∀ a, TopologicalSpace (X a)]
    [∀ a, Nonempty (X a)] [SeparableSpace (Sigma X)] : Countable A := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  have hc : Continuous (Sigma.fst : Sigma X → A) :=
    continuous_sigma (fun _ => continuous_const)
  have hs : Function.Surjective (Sigma.fst : Sigma X → A) :=
    fun a => ⟨⟨a, Classical.choice (inferInstance : Nonempty (X a))⟩, rfl⟩
  letI : SeparableSpace A := hs.denseRange.separableSpace hc
  exact separableSpace_iff_countable.mp inferInstance

/-- Original label: `exmp:adm-dyn`.
The exact time-tagged order representation in the current source is not
separable under the disjoint-union metric. Set-theoretic regrouping alone
therefore cannot identify the two topologies. -/
theorem timeTaggedOrders_not_separable :
    ¬ @SeparableSpace (Σ _ : OrderSide × Quantity, ℝ × Quantity)
      (disjointUnionMetricTopology (X := fun _ : OrderSide × Quantity => ℝ × Quantity)) := by
  rw [metricTopology_eq_sigma]
  intro h
  letI : SeparableSpace (Σ _ : OrderSide × Quantity, ℝ × Quantity) := h
  letI : Countable (OrderSide × Quantity) :=
    countable_tags_of_separable (X := fun _ : OrderSide × Quantity => ℝ × Quantity)
  let f : Ioo (0 : ℝ) 1 → OrderSide × Quantity :=
    fun t => (.buy, ⟨t.val, t.property.1.le⟩)
  have hf : Function.Injective f := by
    intro s t hst
    exact Subtype.ext (congrArg (fun z : OrderSide × Quantity => (z.2 : ℝ)) hst)
  letI : Countable (Ioo (0 : ℝ) 1) := hf.countable
  have hbad := Cardinal.Real.Ioo_countable_iff.mp (Set.to_countable (Ioo (0 : ℝ) 1))
  norm_num at hbad

/-- Original label: `exmp:adm-dyn`.
Keeping time inside the payload gives two separable Euclidean components. -/
theorem timeCoordinateOrders_separable :
    @SeparableSpace (Σ _ : OrderSide, (ℝ × Quantity) × Quantity)
      (disjointUnionMetricTopology (X := fun _ : OrderSide => (ℝ × Quantity) × Quantity)) :=
  separableSpace_metricTopology_of_countable

end Thesis.Foundations.MarketRepresentation.OrderTopology
