import Thesis.Foundations.MarketActions.Alignment
import Mathlib.Data.Prod.Lex
import Mathlib.Topology.Homeomorph.Lemmas
import Thesis.Appendices.Analysis.BoundedMetric

/-! # Identifier coordinates in the current doctoral manuscript

The metric wrapper below gives identifiers distance zero when equal and one
otherwise. This is essential: the usual metric on numeric identifiers does
not express the source's intended geometry.
-/

noncomputable section


open Set
open scoped ENNReal

namespace Thesis.Foundations.MarketActions.Identifiers

open MarketRepresentation MarketRepresentation.TuplesBasic
open MarketRepresentation.TuplesSorting MarketRepresentation.TuplesMetricTopology
open MarketRepresentation.FiniteSets MarketRepresentation.FiniteSets.FiniteSubsets
open Primitive Analytic Alignment

universe u v w

/-- Original label: `exmp:identifier-coordinates`. -/
structure Identifier (I : Type u) where
  val : I

instance {I : Type u} [Countable I] : Countable (Identifier I) :=
  Function.Injective.countable (f := Identifier.val) (by rintro ⟨i⟩ ⟨j⟩ h; congr)

/-- Original label: `exmp:identifier-coordinates`. -/
instance {I : Type u} : EMetricSpace (Identifier I) := by
  classical
  exact
    { edist := fun i j => if i = j then 0 else 1
      edist_self := fun _ => if_pos rfl
      edist_comm := fun i j => by simp [eq_comm]
      edist_triangle := fun i j k => by
        by_cases hij : i = j
        · subst j; simp
        by_cases hjk : j = k
        · subst k; simp
        simp only [hij, hjk, if_false]
        split_ifs <;> norm_num
      eq_of_edist_eq_zero := by
        classical
        intro i j h
        by_contra hij
        simp [hij] at h }

open Classical in
@[simp] theorem identifier_edist {I : Type u} (i j : Identifier I) :
    edist i j = if i = j then 0 else 1 := rfl

theorem identifier_eq_of_edist_lt_one {I : Type u} {i j : Identifier I}
    (h : edist i j < 1) : i = j := by
  classical
  by_contra hij
  simp [hij] at h

theorem identifier_separation {I : Type u} (i j : Identifier I) (h : i ≠ j) :
    (1 : ℝ≥0∞) ≤ edist i j := by classical exact le_of_eq (if_neg h).symm

instance {I : Type u} : CompleteSpace (Identifier I) :=
  completeSpace_of_isolative ⟨1, zero_lt_one, identifier_separation⟩

instance {I : Type u} [Countable I] : PolishSpace (Identifier I) := by
  letI : MetricSpace (Identifier I) := Preliminary.BoundedMetric.truncatedMetricSpace _
  infer_instance

instance {I : Type u} : DiscreteTopology (Identifier I) := by
  classical
  rw [discreteTopology_iff_isOpen_singleton]
  intro i
  have heq : ({i} : Set (Identifier I)) = Metric.eball i 1 := by
    classical
    ext j
    simp only [Set.mem_singleton_iff, Metric.mem_eball]
    exact ⟨fun h => by subst j; simp, identifier_eq_of_edist_lt_one⟩
  rw [heq]
  exact Metric.isOpen_eball

open Classical in
/-- Original label: `exmp:identifier-coordinates`.
The product metric is exactly the maximum specified by the manuscript. -/
theorem identifier_product_edist {Y : Type u} [EMetricSpace Y] {I : Type v}
    (x y : Y × Identifier I) :
    edist x y = max (edist x.1 y.1) (if x.2 = y.2 then 0 else 1) :=
  Prod.edist_eq x y

/-- Original label: `exmp:identifier-coordinates`. -/
theorem identifier_lipschitz {Y : Type u} [EMetricSpace Y] {I : Type v} :
    LipschitzWith 1 (Prod.snd : Y × Identifier I → Identifier I) := by
  classical
  intro x y
  simp only [ENNReal.coe_one, one_mul, Prod.edist_eq]
  exact le_max_right _ _

/-- Original label: `defn:identifier-cancel`.
Resolve identifiers against the current input tuple, then remove the
matching entries in their original order. -/
def cancelByIdentifier {Y : Type u} {I : Type v}
    (x : Tuple (Y × Identifier I)) (J : FiniteSubsets (Identifier I)) :
    Tuple (Y × Identifier I) := cancelIdentifiers Prod.snd (J : Set (Identifier I)) x

theorem identifier_sets_eq_of_near {I : Type u}
    {J K : FiniteSubsets (Identifier I)} (h : edist J K < 1) : J = K := by
  classical
  apply Subtype.ext
  apply Set.Subset.antisymm
  · intro i hi
    by_contra hk
    exact (not_lt_of_ge (hausdorffEDistance_lower_bound_of_mem_notMem
      identifier_separation hi hk)) h
  · intro i hi
    by_contra hj
    have h' : edist K J < 1 := by rw [edist_comm]; exact h
    exact (not_lt_of_ge (hausdorffEDistance_lower_bound_of_mem_notMem
      identifier_separation hi hj)) h'

theorem identifierIndices_eq_of_near {Y : Type u} [EMetricSpace Y] {I : Type v}
    {n : ℕ} {x y : Fin n → Y × Identifier I}
    (J : Set (Identifier I))
    (h : edist (Sigma.mk n x : Tuple (Y × Identifier I)) (Sigma.mk n y) < 1) :
    identifierIndices Prod.snd J (Sigma.mk n x) =
      identifierIndices Prod.snd J (Sigma.mk n y) := by
  classical
  apply Subtype.ext
  ext k
  change (∃ hk : k < n, (x ⟨k, hk⟩).2 ∈ J) ↔
    ∃ hk : k < n, (y ⟨k, hk⟩).2 ∈ J
  have hid (i : Fin n) : (x i).2 = (y i).2 := by
    classical
    apply identifier_eq_of_edist_lt_one
    exact lt_of_le_of_lt (le_max_right _ _) <|
      lt_of_le_of_lt (coordinate_edist_le_fixedLength_edist_of_lt_one h i) h
  constructor
  · rintro ⟨hk, hx⟩
    exact ⟨hk, hid ⟨k, hk⟩ ▸ hx⟩
  · rintro ⟨hk, hy⟩
    exact ⟨hk, (hid ⟨k, hk⟩).symm ▸ hy⟩

/-- Original label: `prop:identifier-cancel-continuous`, clause (i).
No distinctness restriction on the identifiers is required. -/
theorem continuous_cancelByIdentifier {Y : Type u} [EMetricSpace Y] {I : Type v} :
    @Continuous (Tuple (Y × Identifier I) × FiniteSubsets (Identifier I))
      (Tuple (Y × Identifier I))
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p => cancelByIdentifier p.1 p.2) := by
  classical
  letI : TopologicalSpace (Tuple (Y × Identifier I)) := emetricTopology _
  letI : TopologicalSpace (FiniteSubsets (Identifier I)) := emetricTopology _
  letI : TopologicalSpace (Tuple (Y × Identifier I) × FiniteSubsets (Identifier I)) :=
    emetricTopology _
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨n, y⟩, K⟩
  rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  rintro ⟨⟨m, x⟩, J⟩ hp
  have hp' := max_lt_iff.mp (by simpa only [Prod.edist_eq] using hp)
  have hx : edist (Sigma.mk m x : Tuple (Y × Identifier I)) (Sigma.mk n y) < 1 :=
    hp'.1.trans_le (min_le_right _ _)
  have hm : m = n := length_eq_of_edist_lt_one hx
  subst m
  have hJ : J = K := identifier_sets_eq_of_near (hp'.2.trans_le (min_le_right _ _))
  subst J
  have hη := identifierIndices_eq_of_near (K : Set (Identifier I)) hx
  change edist (cancel (Sigma.mk n x) _) (cancel (Sigma.mk n y) _) < ε
  rw [hη]
  exact lt_of_le_of_lt (cancel_edist_le_of_fixed_same_removed_lt_one _ hx)
    (hp'.1.trans_le (min_le_left _ _))

/-- Original label: `prop:identifier-tie-breaking`.
The key order remains partial when different payloads have the same key. -/
@[implicit_reducible] def priorityOrder {Y : Type u} {I : Type v} {K : Type w}
    [LinearOrder I] [LinearOrder K] (h : Y → K) : PartialOrder (Y × I) where
  le x y := x = y ∨ toLex (h x.1, x.2) < toLex (h y.1, y.2)
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    classical
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    exact Or.inr (lt_trans hxy hyz)
  le_antisymm x y hxy hyx := by
    classical
    rcases hxy with heq | hxy
    · exact heq
    rcases hyx with heq | hyx
    · exact heq.symm
    exact (lt_asymm hxy hyx).elim

/-- Original label: `prop:identifier-tie-breaking`, clause (i). -/
theorem priorityOrder_total_on_distinct_identifiers {Y : Type u} {I : Type v}
    {K : Type w} [LinearOrder I] [LinearOrder K] (h : Y → K)
    {x y : Y × I} (hid : x.2 ≠ y.2) :
    @LE.le _ (priorityOrder h).toLE x y ∨ @LE.le _ (priorityOrder h).toLE y x := by
  classical
  change (x = y ∨ toLex (h x.1, x.2) < toLex (h y.1, y.2)) ∨
    (y = x ∨ toLex (h y.1, y.2) < toLex (h x.1, x.2))
  rcases lt_trichotomy (toLex (h x.1, x.2)) (toLex (h y.1, y.2)) with hlt | heq | hgt
  · exact Or.inl (Or.inr hlt)
  · exact (hid (congrArg (fun k : K ×ₗ I => (ofLex k).2) heq)).elim
  · exact Or.inr (Or.inr hgt)

/-- Original label: `prop:identifier-tie-breaking`.
On a tuple with distinct identifiers, the sorting key is injective even if
the primary attribute map is not. -/
theorem key_injective_on_tuple {Y : Type u} {I : Type v} {K : Type w}
    (h : Y → K) (x : Tuple (Y × I))
    (hx : Function.Injective (fun i => (x.entry i).2)) :
    Function.Injective (fun i => (h (x.entry i).1, (x.entry i).2)) := by
  classical
  intro i j hij
  exact hx (congrArg (fun z : K × I => z.2) hij)

/-- The order-preserving inclusion of the reindexed domain in the original
domain. The entries themselves are never altered. -/
def keptIndex {X : Type u} (x : Tuple X) (η : FiniteSubsets ℕ)
    (i : Fin (reindex x η).length) : Fin x.length :=
  ⟨(pairing (finiteSubsetInter η (tupleDomain x))).entry i,
    (mem_tupleDomain x).mp (pairing_entry_mem _ i).2⟩

/-- Original label: `rem:reindex-bracket-notation`, order-preservation clause.
The kept indices are enumerated in increasing order, so `reindex` preserves the
relative order of the surviving entries. -/
theorem keptIndex_strictMono {X : Type u} (x : Tuple X) (η : FiniteSubsets ℕ) :
    StrictMono (keptIndex x η) := by
  classical
  intro i j hij
  exact (toFinset (finiteSubsetInter η (tupleDomain x))).orderEmbOfFin rfl |>.strictMono hij

theorem keptIndex_mem {X : Type u} (x : Tuple X) (η : FiniteSubsets ℕ)
    (k : Fin x.length) :
    (∃ i, keptIndex x η i = k) ↔ k.val ∈ (η : Set ℕ) := by
  classical
  constructor
  · rintro ⟨i, rfl⟩
    exact (pairing_entry_mem (finiteSubsetInter η (tupleDomain x)) i).1
  · intro hk
    obtain ⟨i, hi⟩ := exists_pairing_entry_eq_of_mem
      (finiteSubsetInter η (tupleDomain x)) ⟨hk, (mem_tupleDomain x).mpr k.isLt⟩
    exact ⟨i, Fin.ext hi⟩

open Classical in
theorem keptIndex_list {X : Type u} (x : Tuple X) (η : FiniteSubsets ℕ) :
    List.ofFn (keptIndex x η) =
      (List.finRange x.length).filter (fun i => decide (i.val ∈ (η : Set ℕ))) := by
  classical
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact List.pairwise_ofFn.mpr (keptIndex_strictMono x η)
  · exact (List.sortedLT_finRange x.length).pairwise.filter _
  · intro k
    simpa only [List.mem_ofFn, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] using keptIndex_mem x η k

open Classical in
theorem tupleList_reindex {X : Type u} (x : Tuple X) (η : FiniteSubsets ℕ) :
    tupleList (reindex x η) =
      ((List.finRange x.length).filter
        (fun i => decide (i.val ∈ (η : Set ℕ)))).map x.entry := by
  classical
  change List.ofFn (fun i => x.entry (keptIndex x η i)) = _
  rw [← Function.comp_def, ← List.map_ofFn, keptIndex_list]

open Classical in
/-- Original label: `rem:identifier-coordinates`.
The list characterization proves that every matching identifier is deleted
and that the relative order and multiplicities of all survivors are kept. -/
theorem tupleList_cancelIdentifiers {X : Type u} {I : Type v} (id : X → I)
    (J : Set I) (x : Tuple X) :
    tupleList (cancelIdentifiers id J x) =
      (tupleList x).filter (fun z => decide (id z ∉ J)) := by
  classical
  unfold cancelIdentifiers cancel
  rw [tupleList_reindex]
  have hpred : (fun i : Fin x.length => decide
      (i.val ∈ (finiteSubsetDiff (tupleDomain x) (identifierIndices id J x) : Set ℕ))) =
      (fun i => decide (id (x.entry i) ∉ J)) := by
    classical
    funext i
    congr 1
    exact propext (identifierCancellation_surviving_indices id J x i)
  rw [hpred]
  change List.map x.entry (List.filter ((fun z => decide (id z ∉ J)) ∘ x.entry)
    (List.finRange x.length)) = _
  rw [← List.filter_map]
  congr 1
  exact (List.ofFn_eq_map (f := x.entry)).symm

/-- Original label: `rem:identifier-coordinates`.
Unlike position-based cancellation, requests by stable identifiers combine
by set union, including repeated requests and repeated identifiers. -/
theorem cancelIdentifiers_union {X : Type u} {I : Type v} (id : X → I)
    (J K : Set I) (x : Tuple X) :
    cancelIdentifiers id K (cancelIdentifiers id J x) = cancelIdentifiers id (J ∪ K) x := by
  classical
  apply tuple_eq_of_tupleList_eq
  simp only [tupleList_cancelIdentifiers, List.filter_filter]
  congr 1
  funext z
  simp [Set.mem_union, Bool.and_comm]

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii).
Deletion preserves injectivity because its reindexing is strictly increasing. -/
theorem injective_identifiers_reindex {X : Type u} {I : Type v} (id : X → I)
    (x : Tuple X) (hx : Function.Injective (fun i => id (x.entry i)))
    (η : FiniteSubsets ℕ) :
    Function.Injective (fun i => id ((reindex x η).entry i)) :=
  hx.comp (keptIndex_strictMono x η).injective

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii). -/
theorem injective_identifiers_cancel {X : Type u} {I : Type v} (id : X → I)
    (x : Tuple X) (hx : Function.Injective (fun i => id (x.entry i)))
    (η : FiniteSubsets ℕ) :
    Function.Injective (fun i => id ((cancel x η).entry i)) :=
  injective_identifiers_reindex id x hx _

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii). -/
theorem injective_identifiers_cancelIdentifiers {X : Type u} {I : Type v} (id : X → I)
    (x : Tuple X) (hx : Function.Injective (fun i => id (x.entry i))) (J : Set I) :
    Function.Injective (fun i => id ((cancelIdentifiers id J x).entry i)) :=
  injective_identifiers_cancel id x hx _

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii). -/
theorem injective_identifiers_sort {X : Type u} [Preorder X] {I : Type v} (id : X → I)
    (σ : SortingRule X) (x : Tuple X)
    (hx : Function.Injective (fun i => id (x.entry i))) :
    Function.Injective (fun i => id ((σ.sort x).entry i)) := by
  classical
  obtain ⟨π, hπ⟩ := σ.exists_sortingPermutation x
  rw [hπ]
  exact hx.comp π.1.injective

theorem priorityOrder_lt_iff {Y : Type u} {I : Type v} {K : Type w}
    [LinearOrder I] [LinearOrder K] (h : Y → K) (x y : Y × I) :
    @LT.lt _ (priorityOrder h).toLT x y ↔
      toLex (h x.1, x.2) < toLex (h y.1, y.2) := by
  classical
  change ((x = y ∨ _) ∧ ¬ (y = x ∨ _)) ↔ _
  constructor
  · rintro ⟨heq | hlt, hn⟩
    · exact (hn (Or.inl heq.symm)).elim
    · exact hlt
  · intro hlt
    refine ⟨Or.inr hlt, ?_⟩
    rintro (rfl | hgt)
    · exact lt_irrefl _ hlt
    · exact lt_asymm hlt hgt

/-- Original label: `prop:identifier-tie-breaking`, clause (ii).
Distinct identifiers determine not only the sorted rearrangement but also
its sorting permutation uniquely. -/
theorem tie_break_sortingPermutation_unique {Y : Type u} {I : Type v} {K : Type w}
    [LinearOrder I] [LinearOrder K] (h : Y → K) (x : Tuple (Y × I))
    (hx : Function.Injective (fun i => (x.entry i).2)) :
    letI : PartialOrder (Y × I) := priorityOrder h
    ∀ π ρ : SortingPermutations x, π = ρ := by
  classical
  letI : PartialOrder (Y × I) := priorityOrder h
  intro π ρ
  let keyTuple : Tuple (K ×ₗ I) :=
    ⟨x.length, fun i => toLex (h (x.entry i).1, (x.entry i).2)⟩
  have keySorted (σ : SortingPermutations x) :
      IsSortingPermutation keyTuple σ.val := by
    classical
    intro i j hij hji
    apply σ.property i j hij
    exact (priorityOrder_lt_iff h _ _).mpr hji
  have heq := sortedPermutations_eq_of_linearOrder keyTuple
    ⟨π.val, keySorted π⟩ ⟨ρ.val, keySorted ρ⟩
  have hfun : (fun i => toLex (h (x.entry (π.val i)).1, (x.entry (π.val i)).2)) =
      (fun i => toLex (h (x.entry (ρ.val i)).1, (x.entry (ρ.val i)).2)) := by
    classical
    injection heq
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact hx (congrArg (fun z : K ×ₗ I => (ofLex z).2) (congrFun hfun i))

/-- Original label: `prop:identifier-tie-breaking`, clause (ii). -/
theorem tie_break_sortingRules_agree {Y : Type u} {I : Type v} {K : Type w}
    [LinearOrder I] [LinearOrder K] (h : Y → K) (x : Tuple (Y × I))
    (hx : Function.Injective (fun i => (x.entry i).2)) :
    letI : PartialOrder (Y × I) := priorityOrder h
    ∀ σ τ : SortingRule (Y × I), σ.sort x = τ.sort x := by
  classical
  letI : PartialOrder (Y × I) := priorityOrder h
  intro σ τ
  obtain ⟨π, hπ⟩ := σ.exists_sortingPermutation x
  obtain ⟨ρ, hρ⟩ := τ.exists_sortingPermutation x
  rw [hπ, hρ, tie_break_sortingPermutation_unique h x hx π ρ]

/-- Original label: `prop:identifier-tie-breaking-borel`.
The source's Borel graph is taken in the topology of the full product.
No separability of the payload space is imposed. -/
theorem priorityOrder_borel {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    {I : Type v} [TopologicalSpace I] [DiscreteTopology I] [LinearOrder I]
    {K : Type w} [TopologicalSpace K] [SecondCountableTopology K] [T2Space K]
    [LinearOrder K] (h : Y → K)
    (hh : @Measurable Y K (borel Y) (borel K) h)
    (hlt : @MeasurableSet (K × K) (borel (K × K)) {p | p.1 < p.2}) :
    @MeasurableSet ((Y × I) × (Y × I)) (borel ((Y × I) × (Y × I)))
      {p | @LE.le _ (priorityOrder h).toLE p.1 p.2} := by
  classical
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  letI : MeasurableSpace ((Y × I) × (Y × I)) := borel _
  letI : BorelSpace ((Y × I) × (Y × I)) := ⟨rfl⟩
  have hk₁ : Measurable (fun p : (Y × I) × (Y × I) => h p.1.1) :=
    hh.comp (continuous_fst.comp continuous_fst).measurable
  have hk₂ : Measurable (fun p : (Y × I) × (Y × I) => h p.2.1) :=
    hh.comp (continuous_fst.comp continuous_snd).measurable
  have hlt' : MeasurableSet {p : K × K | p.1 < p.2} := by
    classical
    exact (BorelSpace.measurable_eq (α := K × K)).symm ▸ hlt
  have hprimary : MeasurableSet {p : (Y × I) × (Y × I) | h p.1.1 < h p.2.1} :=
    hlt'.preimage (hk₁.prodMk hk₂)
  have hI : IsOpen {p : I × I | p.1 < p.2} := isOpen_discrete _
  have hsecondary : MeasurableSet {p : (Y × I) × (Y × I) | p.1.2 < p.2.2} :=
    (hI.preimage ((continuous_snd.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd))).measurableSet
  have heq : MeasurableSet {p : (Y × I) × (Y × I) | h p.1.1 = h p.2.1} :=
    measurableSet_eq_fun hk₁ hk₂
  have hdiag : MeasurableSet {p : (Y × I) × (Y × I) | p.1 = p.2} :=
    isClosed_eq continuous_fst continuous_snd |>.measurableSet
  change MeasurableSet {p : (Y × I) × (Y × I) | p.1 = p.2 ∨
    toLex (h p.1.1, p.1.2) < toLex (h p.2.1, p.2.2)}
  simpa only [Prod.Lex.toLex_lt_toLex, Set.setOf_or, Set.setOf_and] using
    hdiag.union (hprimary.union (heq.inter hsecondary))

/-- Original label: `exmp:identifier-coordinates`. -/
def HasDistinctIdentifiers {Y : Type u} {I : Type v}
    (x : Tuple (Y × Identifier I)) : Prop :=
  Function.Injective (fun i => (x.entry i).2)

theorem hasDistinctIdentifiers_iff_of_near {Y : Type u} [EMetricSpace Y]
    {I : Type v} {x y : Tuple (Y × Identifier I)} (h : edist x y < 1) :
    HasDistinctIdentifiers x ↔ HasDistinctIdentifiers y := by
  classical
  rcases x with ⟨n, x⟩
  rcases y with ⟨m, y⟩
  have hnm : n = m := length_eq_of_edist_lt_one h
  subst m
  have hid : (fun i => (x i).2) = fun i => (y i).2 := by
    classical
    funext i
    apply identifier_eq_of_edist_lt_one
    exact lt_of_le_of_lt (le_max_right _ _) <|
      lt_of_le_of_lt (coordinate_edist_le_fixedLength_edist_of_lt_one h i) h
  change Function.Injective (fun i => (x i).2) ↔ Function.Injective (fun i => (y i).2)
  rw [hid]

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii).
On a fixed length layer `Xⁿ`, the distinct-identifier set is the finite
intersection `⋂_{k ≠ l} {x ∈ Xⁿ | id(x(k)) ≠ id(x(l))}`; each comparison set is
clopen because `id` takes values in the discrete identifier space. -/
theorem distinctIdentifiers_fixedLayer_clopen {Y : Type u} [EMetricSpace Y]
    {I : Type v} (n : ℕ) :
    IsClopen {x : Fin n → Y × Identifier I | Function.Injective (fun i => (x i).2)} := by
  classical
  let P := {p : Fin n × Fin n // p.1 ≠ p.2}
  have hp (p : P) : IsClopen {x : Fin n → Y × Identifier I |
      (x p.val.1).2 ≠ (x p.val.2).2} :=
    (isClopen_discrete {q : Identifier I × Identifier I | q.1 ≠ q.2}).preimage
      ((continuous_snd.comp (continuous_apply p.val.1)).prodMk
        (continuous_snd.comp (continuous_apply p.val.2)))
  have heq : {x : Fin n → Y × Identifier I | Function.Injective (fun i => (x i).2)} =
      ⋂ p : P, {x | (x p.val.1).2 ≠ (x p.val.2).2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hx p he
      exact p.property (hx he)
    · intro hx i j he
      by_contra hij
      exact hx ⟨(i, j), hij⟩ he
  rw [heq]
  exact isClopen_iInter_of_finite hp

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii).
As in the thesis: `T(X) = ⨆ₙ Xⁿ` by the standard machinery
(`tupleHausdorffMetricTopology_eq_sigma`), and on every layer `T≠(X) ∩ Xⁿ` is
clopen by the finite coordinate comparison
`distinctIdentifiers_fixedLayer_clopen`. -/
theorem distinctIdentifiers_clopen {Y : Type u} [EMetricSpace Y] {I : Type v} :
    @IsClopen (Tuple (Y × Identifier I)) (emetricTopology _)
      {x | HasDistinctIdentifiers x} := by
  change @IsClopen _ (tupleHausdorffMetricTopology (X := Y × Identifier I)) _
  rw [tupleHausdorffMetricTopology_eq_sigma]
  constructor
  · rw [isClosed_sigma_iff]
    intro n
    exact (distinctIdentifiers_fixedLayer_clopen (Y := Y) (I := I) n).isClosed
  · rw [isOpen_sigma_iff]
    intro n
    exact (distinctIdentifiers_fixedLayer_clopen (Y := Y) (I := I) n).isOpen

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii). -/
theorem distinctIdentifiers_polish {Y : Type u} [EMetricSpace Y]
    [PolishSpace Y] {I : Type v} [Countable I] :
    letI : TopologicalSpace (Tuple (Y × Identifier I)) := emetricTopology _
    PolishSpace {x : Tuple (Y × Identifier I) // HasDistinctIdentifiers x} := by
  classical
  letI : TopologicalSpace (Tuple (Y × Identifier I)) := emetricTopology _
  letI : PolishSpace (Tuple (Y × Identifier I)) := by
    change @PolishSpace _ (tupleHausdorffMetricTopology (X := Y × Identifier I))
    rw [tupleHausdorffMetricTopology_eq_sigma]
    infer_instance
  exact distinctIdentifiers_clopen.isClosed.polishSpace

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii).
Concatenation preserves identifier uniqueness precisely when there are no
cross-tuple collisions, assuming uniqueness within each input. -/
theorem injective_identifiers_concat {X : Type u} {I : Type v} (id : X → I)
    (x y : Tuple X) (hx : Function.Injective (fun i => id (x.entry i)))
    (hy : Function.Injective (fun i => id (y.entry i)))
    (hdisj : ∀ i j, id (x.entry i) ≠ id (y.entry j)) :
    Function.Injective (fun i => id ((concat x y).entry i)) := by
  classical
  have heq : (fun i => id ((concat x y).entry i)) =
      Fin.append (fun i => id (x.entry i)) (fun i => id (y.entry i)) := by
    classical
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  rw [heq]
  exact Fin.append_injective_iff.mpr ⟨hx, hy, hdisj⟩

/-- Product distributes over the open coproduct: a map out of `P × ⨆_a F a` is
continuous iff each restriction to `P × F a` is (used to paste over the
product length layers `Xⁿ × Xᵐ`). -/
private theorem continuous_prod_sigma_iff {A : Type*} {F : A → Type*} {P Z : Type*}
    [∀ a, TopologicalSpace (F a)] [TopologicalSpace P] [TopologicalSpace Z]
    (f : P × Sigma F → Z) :
    Continuous f ↔ ∀ a, Continuous (fun p : P × F a => f (p.1, ⟨a, p.2⟩)) := by
  let h : P × Sigma F ≃ₜ Sigma (fun a => F a × P) :=
    (Homeomorph.prodComm P (Sigma F)).trans Homeomorph.sigmaProdDistrib
  have hp : Continuous f ↔ Continuous (f ∘ h.symm) :=
    h.symm.comp_continuous_iff'.symm
  rw [hp, continuous_sigma_iff]
  constructor
  · intro hf a
    exact (hf a).comp (Homeomorph.prodComm P (F a)).continuous
  · intro hf a
    exact (hf a).comp (Homeomorph.prodComm (F a) P).continuous

private theorem continuous_sigma_prod_iff {A : Type*} {F : A → Type*} {P Z : Type*}
    [∀ a, TopologicalSpace (F a)] [TopologicalSpace P] [TopologicalSpace Z]
    (f : Sigma F × P → Z) :
    Continuous f ↔ ∀ a, Continuous (fun p : F a × P => f (⟨a, p.1⟩, p.2)) := by
  constructor
  · intro hf a
    have h := (continuous_prod_sigma_iff _).mp (hf.comp continuous_swap) a
    exact h.comp continuous_swap
  · intro hf
    have h : Continuous (fun p : P × Sigma F => f (p.2, p.1)) := by
      apply (continuous_prod_sigma_iff _).mpr
      intro a
      exact (hf a).comp continuous_swap
    exact h.comp continuous_swap

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii).
On a product layer `Xⁿ × Xᵐ`, cross-identifier disjointness is the finite
intersection `⋂_{k,l} {(x, y) | id(x(k)) ≠ id(y(l))}` of clopen comparison
sets. -/
theorem disjointIdentifiers_fixedLayers_clopen {Y : Type u} [EMetricSpace Y]
    {I : Type v} (n m : ℕ) :
    IsClopen {p : (Fin n → Y × Identifier I) × (Fin m → Y × Identifier I) |
      ∀ i j, (p.1 i).2 ≠ (p.2 j).2} := by
  have hp (i : Fin n) (j : Fin m) : IsClopen
      {p : (Fin n → Y × Identifier I) × (Fin m → Y × Identifier I) |
        (p.1 i).2 ≠ (p.2 j).2} :=
    (isClopen_discrete {q : Identifier I × Identifier I | q.1 ≠ q.2}).preimage
      ((continuous_snd.comp ((continuous_apply i).comp continuous_fst)).prodMk
        (continuous_snd.comp ((continuous_apply j).comp continuous_snd)))
  have heq : {p : (Fin n → Y × Identifier I) × (Fin m → Y × Identifier I) |
      ∀ i j, (p.1 i).2 ≠ (p.2 j).2} =
      ⋂ i : Fin n, ⋂ j : Fin m, {p | (p.1 i).2 ≠ (p.2 j).2} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  exact isClopen_iInter_of_finite (fun i => isClopen_iInter_of_finite (hp i))

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii).
Cross-identifier disjointness is clopen in `T(X) × T(X)`: decompose both
factors into their clopen length layers (`tupleHausdorffMetricTopology_eq_sigma`),
distribute the product over the coproducts, and use the finite comparison
`disjointIdentifiers_fixedLayers_clopen` on each product layer `Xⁿ × Xᵐ`. -/
theorem disjointIdentifiers_clopen_tuples {Y : Type u} [EMetricSpace Y] {I : Type v} :
    letI : TopologicalSpace (Tuple (Y × Identifier I)) := emetricTopology _
    IsClopen {p : Tuple (Y × Identifier I) × Tuple (Y × Identifier I) |
      ∀ i j, (p.1.entry i).2 ≠ (p.2.entry j).2} := by
  classical
  change @IsClopen _
    (@instTopologicalSpaceProd _ _ (tupleHausdorffMetricTopology (X := Y × Identifier I))
      (tupleHausdorffMetricTopology (X := Y × Identifier I))) _
  rw [tupleHausdorffMetricTopology_eq_sigma]
  letI : TopologicalSpace (Tuple (Y × Identifier I)) := instTopologicalSpaceSigma
  rw [← continuous_boolIndicator_iff_isClopen]
  rw [continuous_prod_sigma_iff]
  intro m
  rw [continuous_sigma_prod_iff]
  intro n
  exact (continuous_boolIndicator_iff_isClopen _).mpr
    (disjointIdentifiers_fixedLayers_clopen (Y := Y) (I := I) n m)

/-- Original label: `prop:identifier-cancel-continuous`, clause (ii).
Cross-identifier-disjointness is clopen in the product of the distinct-ID
tuple spaces, with the subspace topology required by the manuscript: the
product-layer finite-intersection result `disjointIdentifiers_clopen_tuples`
restricted to `T≠(X)²`. -/
theorem disjointIdentifiers_clopen {Y : Type u} [EMetricSpace Y] {I : Type v} :
    letI : TopologicalSpace (Tuple (Y × Identifier I)) := emetricTopology _
    IsClopen {p : {x : Tuple (Y × Identifier I) // HasDistinctIdentifiers x} ×
        {y : Tuple (Y × Identifier I) // HasDistinctIdentifiers y} |
      ∀ i j, (p.1.val.entry i).2 ≠ (p.2.val.entry j).2} := by
  letI : TopologicalSpace (Tuple (Y × Identifier I)) := emetricTopology _
  exact (disjointIdentifiers_clopen_tuples (Y := Y) (I := I)).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- Original label: `prop:identifier-cancel-continuous`, clause (iv). -/
def forgetIdentifiers {Y : Type u} {I : Type v}
    (x : Tuple (Y × Identifier I)) : Tuple Y :=
  ⟨x.length, fun i => (x.entry i).1⟩

/-- Original label: `prop:identifier-cancel-continuous`, clause (iv). -/
theorem continuous_forgetIdentifiers {Y : Type u} [EMetricSpace Y] {I : Type v} :
    @Continuous (Tuple (Y × Identifier I)) (Tuple Y)
      (emetricTopology _) (emetricTopology _) forgetIdentifiers := by
  classical
  letI : TopologicalSpace (Tuple Y) := emetricTopology _
  rw [continuous_tupleHausdorff_iff_fixedLength]
  intro n
  exact (TuplesMeasurableSorting.continuous_sigmaMk_tupleHausdorff n).comp
    (continuous_pi fun i => continuous_fst.comp (continuous_apply i))

/-- Original label: `prop:identifier-cancel-continuous`, clause (iii).
The input sigma algebra is the product of the Borel sigma algebras of the
two factors, exactly as required by the manuscript. -/
theorem measurable_sortedCancelByIdentifier {Y : Type u} [EMetricSpace Y]
    [TopologicalSpace.SeparableSpace Y] {I : Type v} [Countable I]
    [Preorder (Y × Identifier I)] (σ : SortingRule (Y × Identifier I))
    (hσ : IsMeasurableSortingRule σ) :
    @Measurable (Tuple (Y × Identifier I) × FiniteSubsets (Identifier I))
      (SortedTuple (Y × Identifier I))
      (@Prod.instMeasurableSpace _ _ (emetricBorel (Tuple (Y × Identifier I)))
        (emetricBorel (FiniteSubsets (Identifier I))))
      (emetricBorel (SortedTuple (Y × Identifier I)))
      (fun p => σ.toSortedTuple (cancelByIdentifier p.1 p.2)) := by
  classical
  letI : TopologicalSpace (Tuple (Y × Identifier I)) := emetricTopology _
  letI : TopologicalSpace (FiniteSubsets (Identifier I)) := emetricTopology _
  letI : MeasurableSpace (Tuple (Y × Identifier I)) := emetricBorel _
  letI : MeasurableSpace (FiniteSubsets (Identifier I)) := emetricBorel _
  letI : BorelSpace (Tuple (Y × Identifier I)) := ⟨rfl⟩
  letI : BorelSpace (FiniteSubsets (Identifier I)) := ⟨rfl⟩
  letI : TopologicalSpace.SeparableSpace (Tuple (Y × Identifier I)) :=
    TuplesMetricTopology.separableSpace
  have hc : @Measurable
      (Tuple (Y × Identifier I) × FiniteSubsets (Identifier I))
      (Tuple (Y × Identifier I)) (emetricBorel _) (emetricBorel _)
      (fun p => cancelByIdentifier p.1 p.2) :=
    continuous_cancelByIdentifier.borel_measurable
  rw [← emetricBorel_prod_of_separable_left]
  exact hσ.comp hc

end Thesis.Foundations.MarketActions.Identifiers
