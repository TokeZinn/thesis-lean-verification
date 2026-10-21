import Thesis.Foundations.MarketRepresentation.TuplesMeasurableSorting
import Thesis.Foundations.MarketActions.Identifiers
import Mathlib.Data.Nat.Pairing

/-! The product-Borel/tensor distinction in the sorting remark. A completely
explicit discrete counterexample has cardinality larger than the continuum. -/

noncomputable section
open Set

namespace Thesis.Foundations.MarketRepresentation.BorelProductScope

/-- Countably many bits suffice to distinguish the horizontal sections of
any one tensor-measurable set. -/
def SectionCoded {X : Type*} (s : Set (X × X)) : Prop :=
  ∃ c : X → ℕ → Bool, ∀ x y, c x = c y → ∀ z, (x, z) ∈ s ↔ (y, z) ∈ s

@[reducible] def sectionCodeSpace (X : Type*) : MeasurableSpace (X × X) where
  MeasurableSet' := SectionCoded
  measurableSet_empty := ⟨fun _ _ ↦ false, by simp⟩
  measurableSet_compl := by
    rintro s ⟨c, hc⟩
    exact ⟨c, fun x y h z ↦ not_congr (hc x y h z)⟩
  measurableSet_iUnion := by
    intro s hs
    choose c hc using hs
    refine ⟨fun x k ↦ c (Nat.unpair k).1 x (Nat.unpair k).2, ?_⟩
    intro x y h z
    have hcode (n : ℕ) : c n x = c n y := by
      funext m
      simpa only [Nat.unpair_pair] using congrFun h (Nat.pair n m)
    simp only [Set.mem_iUnion]
    exact exists_congr (fun n ↦ hc n x y (hcode n) z)

theorem tensor_le_sectionCodeSpace (X : Type*) :
    (⊤ : MeasurableSpace X).prod ⊤ ≤ sectionCodeSpace X := by
  classical
  have hf : @Measurable (X × X) X (sectionCodeSpace X) ⊤ Prod.fst := by
    intro s _
    refine ⟨fun x _ ↦ decide (x ∈ s), ?_⟩
    intro x y h z
    exact decide_eq_decide.mp (congrFun h 0)
  have hg : @Measurable (X × X) X (sectionCodeSpace X) ⊤ Prod.snd := by
    intro s _
    exact ⟨fun _ _ ↦ false, fun _ _ _ _ ↦ Iff.rfl⟩
  exact sup_le hf.comap_le hg.comap_le

/-- A tensor-measurable diagonal would embed the whole carrier in binary
sequences, since distinct points have different singleton sections. -/
theorem diagonal_tensor_implies_binary_injection {X : Type*}
    (h : @MeasurableSet (X × X) ((⊤ : MeasurableSpace X).prod ⊤) (Set.diagonal X)) :
    ∃ c : X → ℕ → Bool, Function.Injective c := by
  obtain ⟨c, hc⟩ := tensor_le_sectionCodeSpace X _ h
  refine ⟨c, fun x y hxy ↦ ?_⟩
  exact (hc x y hxy x).mp rfl |>.symm

/-- The concrete carrier for the nonseparable discrete example. -/
abbrev LargeDiscrete := Set (ℕ → Bool)

/-- Original block id:
`source:1 - theoretical foundations/2_chapter_market_representations.tex:1840:rem:91`.
The diagonal can fail to belong to the tensor product even though both
coordinate sigma algebras contain every subset. Cantor's theorem rules out
the injection forced by a tensor-measurable diagonal. -/
theorem large_diagonal_not_tensor :
    ¬ @MeasurableSet (LargeDiscrete × LargeDiscrete)
      ((⊤ : MeasurableSpace LargeDiscrete).prod ⊤) (Set.diagonal LargeDiscrete) := by
  intro h
  obtain ⟨c, hc⟩ := diagonal_tensor_implies_binary_injection h
  exact Function.cantor_injective c hc

/-- For the discrete topology the diagonal is closed, hence product-Borel,
while the preceding theorem shows it is not tensor measurable. -/
theorem large_diagonal_borel_not_tensor :
    @MeasurableSet (LargeDiscrete × LargeDiscrete)
      (@borel _ (@instTopologicalSpaceProd LargeDiscrete LargeDiscrete ⊥ ⊥))
      (Set.diagonal LargeDiscrete) ∧
    ¬ @MeasurableSet (LargeDiscrete × LargeDiscrete)
      ((@borel LargeDiscrete ⊥).prod (@borel LargeDiscrete ⊥))
      (Set.diagonal LargeDiscrete) := by
  have hb : @borel LargeDiscrete ⊥ = ⊤ := by
    letI : TopologicalSpace LargeDiscrete := ⊥
    letI : DiscreteTopology LargeDiscrete := ⟨rfl⟩
    exact borel_eq_top_of_discrete
  constructor
  · letI : TopologicalSpace LargeDiscrete := ⊥
    letI : DiscreteTopology LargeDiscrete := ⟨rfl⟩
    letI : MeasurableSpace (LargeDiscrete × LargeDiscrete) := borel _
    letI : BorelSpace (LargeDiscrete × LargeDiscrete) := ⟨rfl⟩
    exact isClosed_diagonal.measurableSet
  · rw [hb]
    exact large_diagonal_not_tensor

/-- The discrete counterexample carries a literal finite-valued extended
metric, obtained from the identifier metric by an injective encoding. -/
@[reducible] def largeDiscreteEMetricSpace : EMetricSpace LargeDiscrete :=
  EMetricSpace.induced
    (fun x : LargeDiscrete ↦ (⟨x⟩ : MarketActions.Identifiers.Identifier LargeDiscrete))
    (fun _ _ h ↦ congrArg MarketActions.Identifiers.Identifier.val h) inferInstance

theorem largeDiscrete_metric_topology :
    largeDiscreteEMetricSpace.toUniformSpace.toTopologicalSpace = ⊥ := by
  classical
  rw [TopologicalSpace.ext_iff]
  intro s
  constructor
  · intro _
    trivial
  · intro _
    apply (@EMetric.isOpen_iff LargeDiscrete
      largeDiscreteEMetricSpace.toPseudoEMetricSpace s).mpr
    intro x hx
    refine ⟨1, zero_lt_one, fun y hy ↦ ?_⟩
    have he : y = x := by
      change edist (MarketActions.Identifiers.Identifier.mk y)
        (MarketActions.Identifiers.Identifier.mk x) < 1 at hy
      exact congrArg MarketActions.Identifiers.Identifier.val
        (MarketActions.Identifiers.identifier_eq_of_edist_lt_one hy)
    exact he ▸ hx

/-- The example really is nonseparable. Discrete separability would make
its carrier countable; singleton coding of naturals into binary sequences
would then contradict Cantor's theorem again. -/
theorem largeDiscrete_nonseparable :
    ¬ @TopologicalSpace.SeparableSpace LargeDiscrete
      largeDiscreteEMetricSpace.toUniformSpace.toTopologicalSpace := by
  rw [largeDiscrete_metric_topology]
  letI : TopologicalSpace LargeDiscrete := ⊥
  letI : DiscreteTopology LargeDiscrete := ⟨rfl⟩
  intro hs
  haveI : Countable LargeDiscrete := TopologicalSpace.separableSpace_iff_countable.mp hs
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat LargeDiscrete
  let code : ℕ → ℕ → Bool := fun n k ↦ decide (k = n)
  have hcode : Function.Injective code := by
    intro n m h
    have he := congrFun h n
    have he' : decide (n = m) = true := by simpa only [code, decide_true] using he.symm
    exact of_decide_eq_true he'
  exact Function.cantor_injective (code ∘ f) (hcode.comp hf)

/-- Original block id:
`source:1 - theoretical foundations/2_chapter_market_representations.tex:1840:rem:91`.
Componentwise Borel random elements always give a tensor-measurable pair;
comparison events follow if the order set belongs to that tensor sigma algebra. -/
theorem comparison_event_of_tensor_order {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] (ξ η : Ω → X)
    (hξ : @Measurable Ω X inferInstance (borel X) ξ)
    (hη : @Measurable Ω X inferInstance (borel X) η) (r : X → X → Prop)
    (hr : @MeasurableSet (X × X) ((borel X).prod (borel X)) {p | r p.1 p.2}) :
    MeasurableSet {ω | r (ξ ω) (η ω)} := by
  letI : MeasurableSpace X := borel X
  exact hr.preimage (hξ.prodMk hη)

end Thesis.Foundations.MarketRepresentation.BorelProductScope
