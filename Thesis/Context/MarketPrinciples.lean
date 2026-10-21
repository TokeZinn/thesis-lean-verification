import Thesis.Context.ThesisContext

/-! # The finitism principle for a complete event history

Events are indexed separately from their action payload, so repeated actions
remain separate occurrences. The principle is a model assumption quantified
over all bounded time windows, not an assertion about observed venues.
-/

open Set

namespace Thesis.Foundations.MarketPrinciples

universe u v w

structure EventHistory (Agent : Type u) (Action : Type v) (Event : Type w) where
  agent : Event → Agent
  time : Event → ℝ
  action : Event → Action

namespace EventHistory

variable {Agent : Type u} {Action : Type v} {Event : Type w}

def eventsIn (H : EventHistory Agent Action Event) (a b : ℝ) : Set Event :=
  {e | H.time e ∈ Icc a b}

def agentsIn (H : EventHistory Agent Action Event) (a b : ℝ) : Set Agent :=
  H.agent '' H.eventsIn a b

def eventsOf (H : EventHistory Agent Action Event) (a b : ℝ) (agent : Agent) : Set Event :=
  {e | e ∈ H.eventsIn a b ∧ H.agent e = agent}

/-- Original label: `prin:finitism`.
Both finiteness clauses, for every bounded interval of one event history. -/
def Finitism (H : EventHistory Agent Action Event) : Prop :=
  ∀ a b : ℝ, a ≤ b → (H.agentsIn a b).Finite ∧
    ∀ agent ∈ H.agentsIn a b, (H.eventsOf a b agent).Finite

/-- Original label: `prin:finitism`.
The two source clauses are equivalent to finitely many realized event
occurrences in every bounded interval. The action type may still be infinite. -/
theorem finitism_iff_finite_events (H : EventHistory Agent Action Event) :
    H.Finitism ↔ ∀ a b : ℝ, a ≤ b → (H.eventsIn a b).Finite := by
  constructor
  · intro h a b hab
    obtain ⟨hagents, hevents⟩ := h a b hab
    apply (hagents.biUnion hevents).subset
    intro e he
    exact mem_iUnion.mpr ⟨H.agent e, mem_iUnion.mpr
      ⟨mem_image_of_mem H.agent he, ⟨he, rfl⟩⟩⟩
  · intro h a b hab
    have hevents := h a b hab
    exact ⟨hevents.image H.agent, fun agent _ ↦ hevents.subset (fun _ he ↦ he.1)⟩

end EventHistory

end Thesis.Foundations.MarketPrinciples
