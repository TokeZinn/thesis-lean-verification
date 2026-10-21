import Thesis.Context.ThesisContext

/-! # The intermediate time-aggregated admissibility injection -/

noncomputable section

namespace Thesis.Foundations.ThesisContext

open MarketClearing.Sorting

universe u

/-- Original label: `exmp:agent-adm-dyn`.
Keep the actual submission time, while relaxing each admissible coordinate
to the union of that agent/direction's admissible coordinates over time.
The dependent-sum tag is merely regrouped relative to the source display. -/
def timeAggregatedAdmissibilityEmbedding {Agent : Type u}
    {P : OrderSide → Agent → Quantity → Set ℝ}
    {Q : OrderSide → Agent → Quantity → Set Quantity}
    (x : AgentDynamicOrder Agent P Q) :
    AgentDynamicOrder Agent (fun s a _ => ⋃ t, P s a t) (fun s a _ => ⋃ t, Q s a t) :=
  ⟨x.1, ⟨⟨x.2.1, Set.mem_iUnion.mpr ⟨x.1.2, x.2.1.property⟩⟩,
    ⟨x.2.2, Set.mem_iUnion.mpr ⟨x.1.2, x.2.2.property⟩⟩⟩⟩

/-- Original label: `exmp:agent-adm-dyn`.
The intermediate map erases only admissibility information, so it remains
injective and composes with the existing unrestricted coordinate injection. -/
theorem timeAggregatedAdmissibilityEmbedding_injective {Agent : Type u}
    {P : OrderSide → Agent → Quantity → Set ℝ}
    {Q : OrderSide → Agent → Quantity → Set Quantity} :
    Function.Injective (timeAggregatedAdmissibilityEmbedding (P := P) (Q := Q)) := by
  intro x y h
  apply agentDynamicOrderEmbedding_injective
  exact congrArg (agentDynamicOrderEmbedding
    (P := fun s a _ => ⋃ t, P s a t) (Q := fun s a _ => ⋃ t, Q s a t)) h

end Thesis.Foundations.ThesisContext
