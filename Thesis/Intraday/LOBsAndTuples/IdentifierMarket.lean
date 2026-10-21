import Thesis.Intraday.LOBsAndTuples.IdentifierClearing

/-! # Full tagged-market clearing with identifiers

Side separation, identifier-bearing clearing, retagging and concatenation are
literal. The source's priority relation is repaired explicitly as documented
in `IdentifierClearing`; the invalid displayed relation is not assumed.
-/

noncomputable section
namespace Thesis.Intraday.IdentifierMarket
open Set Foundations.MarketRepresentation
open Foundations.MarketRepresentation.TuplesBasic
open Foundations.MarketRepresentation.TuplesMetricTopology
open Foundations.MarketRepresentation.DisjointUnionTopology
open Foundations.MarketRepresentation.FiniteSets
open Foundations.MarketActions.Primitive Foundations.MarketActions.Analytic
open Foundations.MarketClearing.Selection
open IdentifierClearing

attribute [local instance] Execution.sigmaBorel

local instance : BorelSpace IdentifiedOrder := inferInstanceAs (BorelSpace (Order × ℕ))
local instance : SecondCountableTopology IdentifiedOrder :=
  inferInstanceAs (SecondCountableTopology (Order × ℕ))
local instance (n : ℕ) : BorelSpace (Fin n → IdentifiedOrder) := inferInstance
local instance (n : ℕ) : SecondCountableTopology (Fin n → IdentifiedOrder) := inferInstance

abbrev TaggedOrder := DisjointUnion (fun _ : Bool => IdentifiedOrder)
abbrev Market := Tuple TaggedOrder

local instance : EMetricSpace TaggedOrder := disjointUnionEMetricSpace

/-- The source identification of `(side-tagged order, id)` with
`(side, (order, id))` preserves the native/disjoint-union topology. -/
def taggedIdentifierHomeomorph : (Clearing.TaggedOrder × ℕ) ≃ₜ TaggedOrder :=
  Homeomorph.sigmaProdDistrib

theorem taggedIdentifierHomeomorph_apply (buy : Bool) (o : Order) (id : ℕ) :
    taggedIdentifierHomeomorph (⟨buy, o⟩, id) = ⟨buy, (o, id)⟩ := rfl

theorem market_topology_eq : tupleHausdorffMetricTopology (X := TaggedOrder) =
    (inferInstance : TopologicalSpace Market) := by
  rw [tupleHausdorffMetricTopology_eq_sigma]
  exact congrArg (fun t : TopologicalSpace TaggedOrder =>
    @instTopologicalSpaceSigma ℕ (fun n => Fin n → TaggedOrder)
      (fun n => @Pi.topologicalSpace (Fin n) (fun _ => TaggedOrder) (fun _ => t)))
    (metricTopology_eq_sigma (X := fun _ : Bool => IdentifiedOrder))

theorem market_borel_eq : tupleHausdorffBorel (X := TaggedOrder) =
    (inferInstance : MeasurableSpace Market) := by
  rw [tupleHausdorffBorel, market_topology_eq]
  exact (@BorelSpace.measurable_eq Market _ _ _).symm

def side (buy : Bool) (m : Market) : Book := separationComponent buy m

def splitMarket (m : Market) : State := (side true m, side false m)

def eraseTagged (z : TaggedOrder) : Clearing.TaggedOrder := ⟨z.1, z.2.1⟩

def eraseMarket (m : Market) : Clearing.Market := Tuple.map eraseTagged m

theorem erase_valueAtTag (buy : Bool) (z : TaggedOrder) (h : z.1 = buy) :
    (valueAtTag buy z h).1 = valueAtTag buy (eraseTagged z) h := by
  rcases z with ⟨tag, o⟩
  cases h
  rfl

def joinMarket (x : State) : Market := concat (retag true x.1) (retag false x.2)

theorem erase_joinMarket (x : State) :
    eraseMarket (joinMarket x) = Clearing.joinMarket (eraseState x) := by
  refine Sigma.ext (show (eraseMarket (joinMarket x)).1 =
    (Clearing.joinMarket (eraseState x)).1 from rfl) ?_
  apply heq_of_eq
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro i <;>
    simp only [eraseMarket, joinMarket, Clearing.joinMarket, eraseState, erase,
      Tuple.map, concat, retag, Tuple.entry, Tuple.length, Fin.append_left,
      Fin.append_right, eraseTagged]

def marketKey (z : TaggedOrder) : ℕ ×ₗ ((ℝ ×ₗ ℝ) ×ₗ ℕ) :=
  toLex (if z.1 then 0 else 1, priorityKey z.1 z.2)

def SortedMarket (m : Market) : Prop := Monotone fun i => marketKey (m.2 i)

@[implicit_reducible] def correctedMarketOrder : PartialOrder TaggedOrder where
  le x y := x = y ∨ marketKey x < marketKey y
  le_refl _ := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    exact Or.inr (lt_trans hxy hyz)
  le_antisymm x y hxy hyx := by
    rcases hxy with he | hxy
    · exact he
    rcases hyx with he | hyx
    · exact he.symm
    exact (lt_asymm hxy hyx).elim

theorem correctedMarket_lt_iff (x y : TaggedOrder) :
    @LT.lt TaggedOrder correctedMarketOrder.toLT x y ↔ marketKey x < marketKey y := by
  change ((x = y ∨ marketKey x < marketKey y) ∧
    ¬(y = x ∨ marketKey y < marketKey x)) ↔ _
  constructor
  · rintro ⟨rfl | h, hn⟩
    · exact (hn (Or.inl rfl)).elim
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rintro (rfl | h')
    · exact (lt_irrefl _ h)
    · exact lt_asymm h h'

/-- The repaired global relation is exactly the cited foundation relation,
transported through the source's `(side, payload, id)` reassociation. -/
theorem correctedMarket_le_iff_cited (x y : Clearing.TaggedOrder × ℕ) :
    @LE.le TaggedOrder correctedMarketOrder.toLE
      (taggedIdentifierHomeomorph x) (taggedIdentifierHomeomorph y) ↔
    @LE.le (Clearing.TaggedOrder × ℕ)
      (Foundations.MarketActions.Identifiers.priorityOrder Clearing.marketKey).toLE x y := by
  have hlt : marketKey (taggedIdentifierHomeomorph x) <
      marketKey (taggedIdentifierHomeomorph y) ↔
      toLex (Clearing.marketKey x.1, x.2) < toLex (Clearing.marketKey y.1, y.2) := by
    rcases x with ⟨⟨a, x⟩, i⟩
    rcases y with ⟨⟨b, y⟩, j⟩
    cases a <;> cases b <;>
      simp [taggedIdentifierHomeomorph_apply, marketKey, Clearing.marketKey,
        priorityKey, Prod.Lex.toLex_lt_toLex]
  change (taggedIdentifierHomeomorph x = taggedIdentifierHomeomorph y ∨ _) ↔ (x = y ∨ _)
  rw [taggedIdentifierHomeomorph.injective.eq_iff, hlt]

theorem sortedMarket_iff_isSorted (m : Market) :
    SortedMarket m ↔ @IsSorted TaggedOrder correctedMarketOrder.toPreorder m := by
  simp only [SortedMarket, Monotone, IsSorted, Tuple.entry, correctedMarket_lt_iff, not_lt]
  constructor
  · intro h i j hij; exact h hij
  · intro h i j hij; exact h i j hij

def sideIndex (buy : Bool) (m : Market) (i : Fin (side buy m).1) : Fin m.1 :=
  ⟨(pairing (separationIndexSet buy m)).2 i,
    ((mem_separationIndexSet buy m).mp
      (pairing_entry_mem (separationIndexSet buy m) i)).choose⟩

theorem sideIndex_monotone (buy : Bool) (m : Market) : Monotone (sideIndex buy m) := by
  intro i j hij
  exact ((isSorted_iff_monotone _).mp (pairing_isSorted (separationIndexSet buy m))) i j hij

theorem side_entry (buy : Bool) (m : Market) (i : Fin (side buy m).1) :
    Sigma.mk buy ((side buy m).2 i) = m.2 (sideIndex buy m i) := by
  have htag : (m.2 (sideIndex buy m i)).1 = buy :=
    ((mem_separationIndexSet buy m).mp
      (pairing_entry_mem (separationIndexSet buy m) i)).choose_spec
  change Sigma.mk buy (valueAtTag buy (m.2 (sideIndex buy m i)) htag) = _
  generalize m.2 (sideIndex buy m i) = z at htag ⊢
  rcases z with ⟨a, x⟩
  cases htag
  rfl

theorem sideIndex_strictMono (buy : Bool) (m : Market) : StrictMono (sideIndex buy m) := by
  intro i j hij
  exact ((FiniteSubsets.toFinset (separationIndexSet buy m)).orderEmbOfFin rfl).strictMono hij

theorem sideIndex_enumerates (buy : Bool) (m : Market) (k : Fin m.1) :
    (m.2 k).1 = buy ↔ ∃ i, sideIndex buy m i = k := by
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := exists_pairing_entry_eq_of_mem (separationIndexSet buy m)
      ((mem_separationIndexSet buy m).mpr ⟨k.isLt, ht⟩)
    exact ⟨i, Fin.ext hi⟩
  · rintro ⟨i, rfl⟩
    exact (congrArg Sigma.fst (side_entry buy m i)).symm

theorem erase_side (buy : Bool) (m : Market) :
    erase (side buy m) = Clearing.side buy (eraseMarket m) := by
  apply Eq.symm
  apply Foundations.MarketClearing.SeparationAlgebra.separationComponent_eq_of_enumeration
    buy (eraseMarket m) (sideIndex buy m) (sideIndex_strictMono buy m)
    (fun i => ((side buy m).2 i).1)
  · exact sideIndex_enumerates buy m
  · intro i
    exact (congrArg eraseTagged (side_entry buy m i)).symm

theorem erase_splitMarket (m : Market) :
    eraseState (splitMarket m) = Clearing.splitMarket (eraseMarket m) :=
  Prod.ext (erase_side true m) (erase_side false m)

theorem side_sorted (buy : Bool) {m : Market} (h : SortedMarket m) :
    Sorted buy (side buy m) := by
  intro i j hij
  have hp := h (sideIndex_monotone buy m hij)
  change marketKey (m.2 (sideIndex buy m i)) ≤ marketKey (m.2 (sideIndex buy m j)) at hp
  rw [← side_entry buy m i, ← side_entry buy m j] at hp
  simpa [marketKey, Prod.Lex.toLex_le_toLex] using hp

theorem joinMarket_sorted {x : State} (h : SortedState x) : SortedMarket (joinMarket x) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      have hp := h.1 (show i ≤ j from hij)
      simpa [joinMarket, concat, retag, Tuple.map, marketKey, Tuple.entry,
        Prod.Lex.toLex_le_toLex] using hp
    · intro j _
      simp [joinMarket, concat, retag, Tuple.map, marketKey, Prod.Lex.toLex_le_toLex]
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      have hj : j.val < x.1.1 := j.isLt
      change x.1.1 + i.val ≤ j.val at hij
      omega
    · intro j hij
      have hij' : i ≤ j := by
        change x.1.1 + i.val ≤ x.1.1 + j.val at hij
        exact Nat.le_of_add_le_add_left hij
      have hp := h.2 hij'
      simpa [joinMarket, concat, retag, Tuple.map, marketKey, Tuple.entry,
        Prod.Lex.toLex_le_toLex] using hp

theorem continuous_side (buy : Bool) : Continuous (side buy) := by
  have h := continuous_separationComponent_disjointTopology
    (X := fun _ : Bool => IdentifiedOrder) buy
  rw [market_topology_eq, tupleHausdorffMetricTopology_eq_sigma (X := IdentifiedOrder)] at h
  exact h

theorem measurable_splitMarket : Measurable splitMarket :=
  (continuous_side true).measurable.prodMk (continuous_side false).measurable

theorem measurable_retagEntry (buy : Bool) :
    Measurable (@Sigma.mk Bool (fun _ : Bool => IdentifiedOrder) buy) := by
  exact measurable_iff_le_map.2 (iInf_le _ buy)

theorem measurable_joinMarket : Measurable joinMarket := by
  apply measurable_state
  intro n m
  change Measurable (fun x : (Fin n → IdentifiedOrder) × (Fin m → IdentifiedOrder) =>
    (⟨n + m, Fin.append (fun i => Sigma.mk true (x.1 i))
      (fun i => Sigma.mk false (x.2 i))⟩ : Market))
  apply continuous_sigmaMk.measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i
    have hm : Measurable (fun x : (Fin n → IdentifiedOrder) ×
        (Fin m → IdentifiedOrder) => x.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    simpa only [Fin.append_left] using
      (measurable_retagEntry true).comp hm
  · intro i
    have hm : Measurable (fun x : (Fin n → IdentifiedOrder) ×
        (Fin m → IdentifiedOrder) => x.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    simpa only [Fin.append_right] using
      (measurable_retagEntry false).comp hm

/-- Original label: `defn:identifier-clearing-operator`.
Full literal market operator, under the explicitly repaired priority relation. -/
def clearMarket (m : Market) : Market := joinMarket (step^[m.1 - 1] (splitMarket m))

theorem measurable_clearMarket : Measurable clearMarket := by
  apply measurable_pasting_iff.mpr
  intro n
  exact measurable_joinMarket.comp
    ((measurable_step.iterate (n - 1)).comp
      (measurable_splitMarket.comp continuous_sigmaMk.measurable))

theorem clearMarket_sorted {m : Market} (h : SortedMarket m) : SortedMarket (clearMarket m) :=
  joinMarket_sorted (iterate_sorted _ ⟨side_sorted true h, side_sorted false h⟩)

def marketIdentifiers (m : Market) : List ℕ := List.ofFn fun i => (m.2 i).2.2

def DistinctIdentifiers (m : Market) : Prop := (marketIdentifiers m).Nodup

theorem side_identifier (buy : Bool) (m : Market) (i : Fin (side buy m).1) :
    ((side buy m).2 i).2 = (m.2 (sideIndex buy m i)).2.2 :=
  congrArg (fun z : TaggedOrder => z.2.2) (side_entry buy m i)

theorem splitMarket_identifiers_nodup (m : Market) (h : DistinctIdentifiers m) :
    (stateIdentifiers (splitMarket m)).Nodup := by
  have hinj : Function.Injective (fun i : Fin m.1 => (m.2 i).2.2) :=
    List.nodup_ofFn.mp h
  have hs (buy : Bool) : (identifiers (side buy m)).Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j hij
    apply (sideIndex_strictMono buy m).injective
    apply hinj
    change (m.2 (sideIndex buy m i)).2.2 = (m.2 (sideIndex buy m j)).2.2
    rw [← side_identifier buy m i, ← side_identifier buy m j]
    exact hij
  apply List.Nodup.append (hs true) (hs false)
  apply List.disjoint_left.mpr
  intro id hb hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hs
  have heq : sideIndex true m i = sideIndex false m j := by
    apply hinj
    change (m.2 (sideIndex true m i)).2.2 = (m.2 (sideIndex false m j)).2.2
    rw [← side_identifier true m i, ← side_identifier false m j]
    exact hj.symm
  have ht := congrArg Sigma.fst (side_entry true m i)
  have hf := congrArg Sigma.fst (side_entry false m j)
  rw [heq] at ht
  exact Bool.noConfusion (ht.trans hf.symm)

theorem identifiers_joinMarket (x : State) :
    marketIdentifiers (joinMarket x) = stateIdentifiers x := by
  have heq : (fun i => ((joinMarket x).2 i).2.2) =
      Fin.append (fun i => (x.1.2 i).2) (fun i => (x.2.2 i).2) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;>
      simp only [joinMarket, concat, retag, Tuple.map, Tuple.entry,
        Tuple.length, Fin.append_left, Fin.append_right]
  change List.ofFn _ = _
  rw [heq]
  exact List.ofFn_fin_append (m := x.1.1) (n := x.2.1) _ _

theorem clearMarket_preserves_distinctIdentifiers (m : Market) (h : DistinctIdentifiers m) :
    DistinctIdentifiers (clearMarket m) := by
  unfold DistinctIdentifiers clearMarket
  rw [identifiers_joinMarket]
  exact (splitMarket_identifiers_nodup m h).sublist (iterate_identifiers_sublist _ _)

theorem eraseMarket_sorted {m : Market} (hm : SortedMarket m) :
    Clearing.SortedMarket (eraseMarket m) := by
  intro i j hij
  have h := hm hij
  change toLex (if (m.2 i).1 then 0 else 1, priorityKey (m.2 i).1 (m.2 i).2) ≤
    toLex (if (m.2 j).1 then 0 else 1, priorityKey (m.2 j).1 (m.2 j).2) at h
  change toLex (if (m.2 i).1 then 0 else 1,
      Execution.priorityKey (m.2 i).1 (m.2 i).2.1) ≤
    toLex (if (m.2 j).1 then 0 else 1,
      Execution.priorityKey (m.2 j).1 (m.2 j).2.1)
  rw [Prod.Lex.toLex_le_toLex] at h ⊢
  rcases h with h | ⟨he, hp⟩
  · exact Or.inl h
  · refine Or.inr ⟨he, ?_⟩
    change toLex (Execution.priorityKey (m.2 i).1 (m.2 i).2.1, (m.2 i).2.2) ≤
      toLex (Execution.priorityKey (m.2 j).1 (m.2 j).2.1, (m.2 j).2.2) at hp
    rw [Prod.Lex.toLex_le_toLex] at hp
    exact hp.elim le_of_lt (fun h => le_of_eq h.1)

/-- Original label: `prop:identifier-clearing-properties`.
Exact erasure through separation, finite iteration, retagging and merge. -/
theorem erase_clearMarket (m : Market) :
    eraseMarket (clearMarket m) = Clearing.clearMarket (eraseMarket m) := by
  rw [clearMarket, erase_joinMarket, erase_iterate, erase_splitMarket]
  rfl

def sortedClearMarket (m : {m : Market // SortedMarket m}) : {m : Market // SortedMarket m} :=
  ⟨clearMarket m, clearMarket_sorted m.property⟩

theorem measurable_sortedClearMarket : Measurable sortedClearMarket :=
  (measurable_clearMarket.comp measurable_subtype_coe).subtype_mk

/-- Original label: `prop:identifier-clearing-properties`.
All three clauses of the source proposition for the explicitly corrected
identifier priority: Borel measurability, preservation of distinct identifiers,
and exact commutation with identifier erasure. -/
theorem clearing_properties :
    Measurable sortedClearMarket ∧
    (∀ m : Market, SortedMarket m → DistinctIdentifiers m →
      SortedMarket (clearMarket m) ∧ DistinctIdentifiers (clearMarket m)) ∧
    (∀ m : Market, eraseMarket (clearMarket m) = Clearing.clearMarket (eraseMarket m)) :=
  ⟨measurable_sortedClearMarket,
    (fun m hm hd => ⟨clearMarket_sorted hm, clearMarket_preserves_distinctIdentifiers m hd⟩),
    erase_clearMarket⟩

end Thesis.Intraday.IdentifierMarket
