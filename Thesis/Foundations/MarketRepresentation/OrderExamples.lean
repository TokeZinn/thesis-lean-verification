import Thesis.Context.ThesisContext
import Thesis.Appendices.Analysis.BoundedMetric
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- Source-based block IDs must stay on one line for the inventory parser.
set_option linter.style.longLine false

/-! # Literal order-space examples and their full ordering axioms -/

namespace Thesis.Foundations.ThesisContext

open MarketClearing.Sorting
open Set MeasureTheory

universe u

/-- Original label: `exmp:partial-order-static-market`.
The fixed-side formula has all the linear-order axioms, not just comparability. -/
theorem staticPriority_isLinearOrder (side : OrderSide) :
    IsLinearOrder (ℝ × Quantity) (staticPriority side) where
  refl := by intro x; cases side <;> simp [staticPriority]
  trans := by
    intro x y z hxy hyz
    cases side <;> simp only [staticPriority] at * <;> grind
  antisymm := by
    intro x y hxy hyx
    cases side <;> simp only [staticPriority] at * <;> grind
  total := staticPriority_total side

/-- Original label: `exmp:total-order-dynamic-market`. -/
theorem dynamicPriority_isLinearOrder (side : OrderSide) :
    IsLinearOrder ((ℝ × Quantity) × Quantity) (dynamicPriority side) where
  refl := by intro x; cases side <;> simp [dynamicPriority]
  trans := by
    intro x y z hxy hyz
    cases side <;> simp only [dynamicPriority] at * <;> grind
  antisymm := by
    intro x y hxy hyx
    cases side <;> simp only [dynamicPriority] at * <;> grind
  total := dynamicPriority_total side

/-- Original label: `exmp:partial-order-static-market`. -/
theorem taggedStaticPriority_isPartialOrder :
    IsPartialOrder (OrderSide × (ℝ × Quantity)) taggedStaticPriority where
  refl x := ⟨rfl, (staticPriority_isLinearOrder x.1).refl x.2⟩
  trans := by
    intro x y z hxy hyz
    refine ⟨hxy.1.trans hyz.1, ?_⟩
    exact (staticPriority_isLinearOrder x.1).trans x.2 y.2 z.2 hxy.2
      (by simpa [hxy.1] using hyz.2)
  antisymm := by
    intro x y hxy hyx
    exact Prod.ext hxy.1 ((staticPriority_isLinearOrder x.1).antisymm x.2 y.2
      hxy.2 (by simpa [hxy.1] using hyx.2))

private theorem sidePriority_isLinearOrder {X : Type*}
    (r : OrderSide → X → X → Prop) (hr : ∀ side, IsLinearOrder X (r side)) :
    IsLinearOrder (OrderSide × X) (fun x y =>
      (x.1 = OrderSide.buy ∧ y.1 = OrderSide.sell) ∨ (x.1 = y.1 ∧ r x.1 x.2 y.2)) where
  refl x := Or.inr ⟨rfl, (hr x.1).refl x.2⟩
  trans := by
    rintro ⟨s, x⟩ ⟨t, y⟩ ⟨v, z⟩ hxy hyz
    cases s <;> cases t <;> cases v <;>
      simp_all only [reduceCtorEq, and_false, and_true, true_and, false_and,
        false_or, or_false]
    · exact (hr _).trans x y z hxy hyz
    · exact (hr _).trans x y z hxy hyz
  antisymm := by
    rintro ⟨s, x⟩ ⟨t, y⟩ hxy hyx
    cases s <;> cases t <;>
      simp_all only [reduceCtorEq, and_false, and_true, true_and, false_and,
        false_or, or_false, Prod.mk.injEq]
    · exact (hr _).antisymm x y hxy hyx
    · exact (hr _).antisymm x y hxy hyx
  total := by
    rintro ⟨s, x⟩ ⟨t, y⟩
    cases s <;> cases t <;>
      simp only [reduceCtorEq, and_false, and_true, true_and, false_and,
        false_or, or_false, or_true]
    · exact (hr _).total x y
    · exact (hr _).total x y

/-- Original label: `exmp:total-order-static-market`. -/
theorem staticTotalPriority_isLinearOrder :
    IsLinearOrder (OrderSide × (ℝ × Quantity)) staticTotalPriority :=
  sidePriority_isLinearOrder staticPriority staticPriority_isLinearOrder

/-- Original label: `exmp:total-order-dynamic-market`. -/
theorem dynamicTotalPriority_isLinearOrder :
    IsLinearOrder (OrderSide × ((ℝ × Quantity) × Quantity)) dynamicTotalPriority :=
  sidePriority_isLinearOrder dynamicPriority dynamicPriority_isLinearOrder

variable {Agent : Type u}
  (P : OrderSide → Agent → Set ℝ) (Q : OrderSide → Agent → Set Quantity)

def restrictedMarketView : AgentStaticOrder Agent P Q → OrderSide × (ℝ × Quantity) :=
  fun order => (order.1.1, order.2.1.val, order.2.2.val)

/-- Original label: `exmp:completing-order-agent-based-static-market`.
The range retains the same agent in both restrictions, rather than taking
the product of two independent unions or allowing all visible orders. -/
theorem range_restrictedMarketView :
    range (restrictedMarketView P Q) =
      {z | ∃ a, z.2.1 ∈ P z.1 a ∧ z.2.2 ∈ Q z.1 a} := by
  ext z
  constructor
  · rintro ⟨⟨⟨side, a⟩, ⟨⟨p, hp⟩, ⟨q, hq⟩⟩⟩, rfl⟩
    exact ⟨a, hp, hq⟩
  · rintro ⟨a, hp, hq⟩
    exact ⟨⟨(z.1, a), ⟨z.2.1, hp⟩, ⟨z.2.2, hq⟩⟩, rfl⟩

/-- Original label: `exmp:completing-order-agent-based-static-market`.
This is the quotient of the actual agent-constrained space in the example. -/
noncomputable def restrictedAgentOrderQuotientEquiv :
    Quotient (Setoid.ker (restrictedMarketView P Q)) ≃
      {z : OrderSide × (ℝ × Quantity) // ∃ a, z.2.1 ∈ P z.1 a ∧ z.2.2 ∈ Q z.1 a} :=
  (Setoid.quotientKerEquivRange (restrictedMarketView P Q)).trans
    (Equiv.setCongr (range_restrictedMarketView P Q))

/-- Original label: `exmp:completing-order-agent-based-static-market`.
The inherited visible priority is a full linear order on the constrained quotient. -/
theorem restrictedAgentOrderQuotient_isLinearOrder :
    IsLinearOrder (Quotient (Setoid.ker (restrictedMarketView P Q)))
      (fun x y => staticTotalPriority
        (restrictedAgentOrderQuotientEquiv P Q x).val
        (restrictedAgentOrderQuotientEquiv P Q y).val) where
  refl x := staticTotalPriority_isLinearOrder.refl _
  trans x y z hxy hyz := staticTotalPriority_isLinearOrder.trans _ _ _ hxy hyz
  antisymm := by
    intro x y hxy hyx
    apply (restrictedAgentOrderQuotientEquiv P Q).injective
    exact Subtype.ext (staticTotalPriority_isLinearOrder.antisymm _ _ hxy hyx)
  total x y := staticTotalPriority_isLinearOrder.total _ _

/-- Original label: `exmp:agent-adm-static`.
Failure of surjectivity gives the strict inclusion meant in the example. -/
theorem agentStaticOrderEmbedding_range_proper
    (h : ¬ Function.Surjective (agentStaticOrderEmbedding (P := P) (Q := Q))) :
    range (agentStaticOrderEmbedding (P := P) (Q := Q)) ⊂ univ := by
  exact Set.ssubset_univ_iff.mpr (by simpa [Set.range_eq_univ] using h)

/-- Original label: `exmp:adm-dyn`.
The intermediate representation keeps submission time in the payload. -/
def unrestrictedDynamicRegrouping :
    (Σ _ : OrderSide × Quantity, ℝ × Quantity) ≃
      (Σ _ : OrderSide, (ℝ × Quantity) × Quantity) where
  toFun order := ⟨order.1.1, order.2, order.1.2⟩
  invFun order := ⟨(order.1, order.2.2), order.2.1⟩
  left_inv := by rintro ⟨⟨side, time⟩, payload⟩; rfl
  right_inv := by rintro ⟨side, ⟨payload, time⟩⟩; rfl

section DynamicRestrictions

variable (Pt : OrderSide → Agent → Quantity → Set ℝ)
  (Qt : OrderSide → Agent → Quantity → Set Quantity)

/-- The source's separate unions of admissible prices and quantities over time. -/
abbrev TimeUnionOrder :=
  (AgentStaticOrder Agent (fun side a => ⋃ t, Pt side a t)
    (fun side a => ⋃ t, Qt side a t)) × Quantity

def toTimeUnionOrder : AgentDynamicOrder Agent Pt Qt → TimeUnionOrder Pt Qt :=
  fun order => (⟨order.1.1,
    ⟨order.2.1.val, mem_iUnion.mpr ⟨order.1.2, order.2.1.property⟩⟩,
    ⟨order.2.2.val, mem_iUnion.mpr ⟨order.1.2, order.2.2.property⟩⟩⟩, order.1.2)

def timeUnionOrderEmbedding : TimeUnionOrder Pt Qt →
    (((ℝ × Quantity) × (OrderSide × Agent)) × Quantity) :=
  fun order => (agentStaticOrderEmbedding order.1, order.2)

theorem timeUnionOrderEmbedding_toTimeUnionOrder (order : AgentDynamicOrder Agent Pt Qt) :
    timeUnionOrderEmbedding Pt Qt (toTimeUnionOrder Pt Qt order) =
      agentDynamicOrderEmbedding order := rfl

/-- Original label: `exmp:agent-adm-dyn`.
Both injections in the displayed chain are proved, including the intermediate
space with independently time-unioned price and quantity restrictions. -/
theorem timeUnionOrder_injections :
    Function.Injective (toTimeUnionOrder Pt Qt) ∧
      Function.Injective (timeUnionOrderEmbedding Pt Qt) := by
  constructor
  · intro x y h
    apply agentDynamicOrderEmbedding_injective
    exact congrArg (timeUnionOrderEmbedding Pt Qt) h
  · intro x y h
    change (agentStaticOrderEmbedding x.1, x.2) =
      (agentStaticOrderEmbedding y.1, y.2) at h
    have htime : x.2 = y.2 := congrArg
      (fun z : (((ℝ × Quantity) × (OrderSide × Agent)) × Quantity) => z.2) h
    exact Prod.ext (agentStaticOrderEmbedding_injective (congrArg Prod.fst h)) htime

end DynamicRestrictions

/--
Original block id: `source:1 - theoretical foundations/2_chapter_market_representations.tex:368:rem:20`
The truncated finite-valued metric has exactly the original topology. -/
theorem truncatedMetric_same_topology (X : Type*) [EMetricSpace X] :
    (Preliminary.BoundedMetric.truncatedMetricSpace X).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace X) := rfl

end Thesis.Foundations.ThesisContext
