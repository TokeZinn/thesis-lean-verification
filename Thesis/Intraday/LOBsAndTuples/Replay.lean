import Thesis.Intraday.LOBsAndTuples.Visibility
import Thesis.Intraday.LOBsAndTuples.MarketSorting
import Thesis.Foundations.MarketActions.Composite

/-! # The depth-restricted step: full-book clearing observed through the visible projection -/

noncomputable section
namespace Thesis.Intraday.Replay

open Execution Clearing Visibility MarketSorting Foundations.MarketRepresentation
open DisjointUnionTopology TuplesMetricTopology
open Foundations.MarketActions.Composite

attribute [local instance] Execution.sigmaBorel
local instance : EMetricSpace TaggedOrder := disjointUnionEMetricSpace
local instance : @TopologicalSpace.SeparableSpace TaggedOrder
    (disjointUnionMetricTopology (X := fun _ : Bool => Order)) :=
  separableSpace_metricTopology_of_countable

abbrev Action := MarketAction TaggedOrder
abbrev Script := CompositeAction TaggedOrder

instance : MeasurableSpace Action := borel Action
instance : BorelSpace Action := ⟨rfl⟩
instance : TopologicalSpace.SeparableSpace Action :=
  Foundations.MarketActions.Composite.separableSpace

theorem continuous_applyScript :
    Continuous (fun x : Market × Script => applyCompositeAction x.1 x.2) := by
  have h := continuous_applyCompositeAction_emetricTopology (X := TaggedOrder)
  change @Continuous (Market × Script) Market
    (@instTopologicalSpaceProd Market Script
      (tupleHausdorffMetricTopology (X := TaggedOrder))
      (tupleHausdorffMetricTopology (X := Action)))
    (tupleHausdorffMetricTopology (X := TaggedOrder)) _ at h
  rw [market_topology_eq, tupleHausdorffMetricTopology_eq_sigma (X := Action)] at h
  exact h

/-- The full-book update underlying `defn:depth-restricted-step`: the script acts
on the complete book, the result is sorted, and the whole sorted book is cleared.
No latent tail is set aside before clearing. -/
def depthStep (x : Market × Script) : Market :=
  clearMarket (sortMarket (applyCompositeAction x.1 x.2))

theorem measurable_depthStep : Measurable depthStep :=
  measurable_clearMarket.comp (measurable_sortMarket.comp continuous_applyScript.measurable)

theorem depthStep_sorted (x : Market × Script) : SortedMarket (depthStep x) :=
  clearMarket_sorted (sortMarket_sorted _)

/-- Original label: `defn:depth-restricted-step`.
The step operator with the thesis's sorted domain and codomain: full-book
clearing of the sorted post-action book. -/
def sortedDepthStep (x : {m : Market // SortedMarket m} × Script) :
    {m : Market // SortedMarket m} := ⟨depthStep (x.1.val, x.2), depthStep_sorted _⟩

/-- The visible book after a step is the visible projection of the cleared full
book. The thesis uses k = 100. -/
def visibleBook (k : ℕ) (x : {m : Market // SortedMarket m} × Script) : Market :=
  visible k (sortedDepthStep x).val

theorem visibleBook_sorted (k : ℕ) (x : {m : Market // SortedMarket m} × Script) :
    SortedMarket (visibleBook k x) :=
  visible_sorted k (sortedDepthStep x).property

/-- Restricting the input to sorted books preserves joint measurability. -/
theorem measurable_depthStep_sorted_input :
    Measurable (fun x : {m : Market // SortedMarket m} × Script => depthStep (x.1.val, x.2)) :=
  measurable_depthStep.comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

end Thesis.Intraday.Replay
