import Thesis.Intraday.LOBsAndTuples.Visibility
import Thesis.Intraday.LOBsAndTuples.MarketSorting
import Thesis.Foundations.MarketActions.Composite

/-! # Joint measurability of the full-book depth-restricted update -/

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

/-- Original label: `fig:visible-latent-book`, formula m unlhd c.
The script acts on the complete book, then sorting precedes projection.
The thesis uses k = 100. -/
def depthStep (k : ℕ) (x : Market × Script) : Market :=
  depthClear k (sortMarket (applyCompositeAction x.1 x.2))

theorem measurable_depthStep (k : ℕ) : Measurable (depthStep k) :=
  (measurable_depthClear k).comp (measurable_sortMarket.comp continuous_applyScript.measurable)

theorem depthStep_sorted (k : ℕ) (x : Market × Script) : SortedMarket (depthStep k x) :=
  depthClear_sorted k (sortMarket_sorted _)

/-- Original label: `defn:depth-restricted-step`.
The actual jointly measurable update, with the thesis's sorted codomain. -/
def sortedDepthStep (k : ℕ) (x : {m : Market // SortedMarket m} × Script) :
    {m : Market // SortedMarket m} := ⟨depthStep k (x.1.val, x.2), depthStep_sorted k _⟩

/-- Restricting the input to sorted books preserves joint measurability. -/
theorem measurable_depthStep_sorted_input (k : ℕ) :
    Measurable (fun x : {m : Market // SortedMarket m} × Script => depthStep k (x.1.val, x.2)) :=
  (measurable_depthStep k).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

/-- Original label: `prop:visible-step-measurable`. -/
theorem measurable_sortedDepthStep (k : ℕ) : Measurable (sortedDepthStep k) :=
  (measurable_depthStep_sorted_input k).subtype_mk

end Thesis.Intraday.Replay
