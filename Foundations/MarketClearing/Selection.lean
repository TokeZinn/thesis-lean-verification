import Foundations.MarketActions.Composite

/-!
# Market Clearing: Selections, Filters, and Segregation

Blueprint module for
`1 - theoretical foundations/4_market_clearing.tex`,
section "Selections, Filters, and Market Segregation".

Planned formal content:

* `prop:composition-continuous`;
* `cor:filter`;
* `prop:characteristic-functions-tuple`;
* tuple projections and decomposition;
* `prop:tuple-projection-continuous`;
* separation operators;
* `prop:separation-continuous`.
-/

namespace Thesis
namespace Foundations
namespace MarketClearing
namespace Selection

open Thesis.Foundations.MarketRepresentation
open Thesis.Foundations.MarketRepresentation.FiniteSets
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
open Thesis.Foundations.MarketRepresentation.TuplesMeasurableSorting
open Thesis.Foundations.MarketActions.Primitive
open Thesis.Foundations.MarketActions.Analytic

universe u v

/-! ## Reindexing and Filters -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, section "Selections,
Filters, and Market Segregation".

Original label: `prop:composition-continuous`.

Informal statement: the reindexing/filtering map
`(\bm{x}, \eta) \mapsto \bm{x}[\eta]` is continuous for the tuple Hausdorff
topology and the Hausdorff topology on finite index sets.

Lean strategy / thesis relation note: the thesis proof uses the standard machinery: below distance
`1`, the tuple length and finite index set stabilize. Lean follows the same
argument, using the Chapter 3 fixed-index nonexpansive estimate for `reindex`.
-/
theorem continuousAt_reindex_emetricTopology {X : Type u} [EMetricSpace X]
    (p₀ : Tuple X × FiniteSubsets ℕ) :
    @ContinuousAt (Tuple X × FiniteSubsets ℕ) (Tuple X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p : Tuple X × FiniteSubsets ℕ => reindex p.1 p.2) p₀ := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (FiniteSubsets ℕ) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Tuple X × FiniteSubsets ℕ) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  rcases p₀ with ⟨x₀Tuple, eta₀⟩
  rcases x₀Tuple with ⟨m, x₀⟩
  rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
  intro ε hε
  let δ : ENNReal := min ε (1 : ENNReal)
  refine ⟨δ, lt_min hε zero_lt_one, ?_⟩
  intro p hp
  rcases p with ⟨xTuple, eta⟩
  rcases xTuple with ⟨m', x⟩
  rw [Prod.edist_eq] at hp
  have hxδ :
      edist (Sigma.mk m' x : Tuple X) (Sigma.mk m x₀ : Tuple X) < δ :=
    (max_lt_iff.mp hp).1
  have hetaδ : edist eta eta₀ < δ :=
    (max_lt_iff.mp hp).2
  have hx_one :
      edist (Sigma.mk m' x : Tuple X) (Sigma.mk m x₀ : Tuple X) <
        (1 : ENNReal) :=
    lt_of_lt_of_le hxδ (min_le_right _ _)
  have heta_one : edist eta eta₀ < (1 : ENNReal) :=
    lt_of_lt_of_le hetaδ (min_le_right _ _)
  have hm : m' = m := by
    simpa [Tuple.length] using length_eq_of_edist_lt_one hx_one
  have heta : eta = eta₀ := finiteSubsets_nat_eq_of_edist_lt_one heta_one
  subst m'
  subst eta
  have houtδ :
      edist (reindex (Sigma.mk m x : Tuple X) eta₀)
          (reindex (Sigma.mk m x₀ : Tuple X) eta₀) < δ :=
    lt_of_le_of_lt (reindex_edist_le_of_fixed_lt_one eta₀ hx_one) hxδ
  exact lt_of_lt_of_le houtδ (min_le_left _ _)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, section "Selections,
Filters, and Market Segregation".

Original label: `prop:composition-continuous`.

Informal statement: the global reindexing/filtering map is continuous.
-/
theorem continuous_reindex_emetricTopology {X : Type u} [EMetricSpace X] :
    @Continuous (Tuple X × FiniteSubsets ℕ) (Tuple X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (fun p : Tuple X × FiniteSubsets ℕ => reindex p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (FiniteSubsets ℕ) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Tuple X × FiniteSubsets ℕ) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  rw [continuous_iff_continuousAt]
  exact continuousAt_reindex_emetricTopology

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, section "Selections,
Filters, and Market Segregation".

Original label: `prop:composition-continuous`.

Informal statement: the continuous reindexing map is Borel measurable.
-/
theorem measurable_reindex_emetricBorel {X : Type u} [EMetricSpace X] :
    @Measurable (Tuple X × FiniteSubsets ℕ) (Tuple X)
      (emetricBorel (Tuple X × FiniteSubsets ℕ)) (emetricBorel (Tuple X))
      (fun p : Tuple X × FiniteSubsets ℕ => reindex p.1 p.2) := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (FiniteSubsets ℕ) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Tuple X × FiniteSubsets ℕ) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (Tuple X × FiniteSubsets ℕ) :=
    emetricBorel (Tuple X × FiniteSubsets ℕ)
  letI : MeasurableSpace (Tuple X) := emetricBorel (Tuple X)
  letI : OpensMeasurableSpace (Tuple X × FiniteSubsets ℕ) := ⟨le_rfl⟩
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  exact continuous_reindex_emetricTopology.measurable

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, section "Selections,
Filters, and Market Segregation".

Original label: `cor:filter`.

Informal statement: if a finite-index selector `F` is measurable, then the
filtered tuple map `\bm{x} \mapsto \bm{x}[F(\bm{x})]` is measurable.

Lean strategy / thesis relation note: this is exactly the thesis composition argument: measurable
graph map `x ↦ (x,F x)` followed by the Borel-measurable reindexing map above.
-/
theorem measurable_filter_emetricBorel {X : Type u} [EMetricSpace X]
    {F : Tuple X → FiniteSubsets ℕ}
    (hF : @Measurable (Tuple X) (FiniteSubsets ℕ)
      (emetricBorel (Tuple X)) (emetricBorel (FiniteSubsets ℕ)) F) :
    @Measurable (Tuple X) (Tuple X)
      (emetricBorel (Tuple X)) (emetricBorel (Tuple X))
      (fun x : Tuple X => reindex x (F x)) := by
  letI : MeasurableSpace (Tuple X) := emetricBorel (Tuple X)
  letI : MeasurableSpace (FiniteSubsets ℕ) := emetricBorel (FiniteSubsets ℕ)
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (FiniteSubsets ℕ) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Tuple X × FiniteSubsets ℕ) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (Tuple X) := ⟨rfl⟩
  letI : BorelSpace (FiniteSubsets ℕ) := ⟨rfl⟩
  haveI : TopologicalSpace.SeparableSpace (FiniteSubsets ℕ) :=
    finiteSubsets_separableSpace (α := ℕ)
  exact continuous_reindex_emetricTopology.measurable2 measurable_id hF

/-! ## Characteristic Index Selectors -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, section "Selections,
Filters, and Market Segregation".

Original label: `prop:characteristic-functions-tuple`.

Informal statement: given coordinatewise characteristic functions
`\chi_i : X -> {0,1}`, collect exactly the tuple indices at which the
corresponding characteristic function is true.

Lean strategy / thesis relation note: Lean uses `Bool` for the two-point set `{0,1}` and zero-based
indices `n < x.length` for the thesis domain `{1,\dots,\ell(\bm{x})}`.
-/
noncomputable def characteristicIndexSet {X : Type u}
    (χ : ℕ → X → Bool) (x : Tuple X) : FiniteSubsets ℕ := by
  classical
  refine ⟨{n : ℕ | ∃ h : n < x.length, χ n (Tuple.entry x ⟨n, h⟩) = true}, ?_⟩
  have hsub :
      {n : ℕ | ∃ h : n < x.length, χ n (Tuple.entry x ⟨n, h⟩) = true} ⊆
        Set.range (fun i : Fin x.length => (i : ℕ)) := by
    intro n hn
    rcases hn with ⟨hnlt, _hχ⟩
    exact ⟨⟨n, hnlt⟩, rfl⟩
  exact (Set.finite_range (fun i : Fin x.length => (i : ℕ))).subset hsub

@[simp]
theorem mem_characteristicIndexSet {X : Type u}
    (χ : ℕ → X → Bool) (x : Tuple X) {n : ℕ} :
    n ∈ (characteristicIndexSet χ x : Set ℕ) ↔
      ∃ h : n < x.length, χ n (Tuple.entry x ⟨n, h⟩) = true :=
  Iff.rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`prop:characteristic-functions-tuple`.

Original label: support observation in `prop:characteristic-functions-tuple`.

Informal statement: the characteristic selector only returns indices inside
the tuple domain.
-/
theorem characteristicIndexSet_subset_domain {X : Type u}
    (χ : ℕ → X → Bool) (x : Tuple X) :
    (characteristicIndexSet χ x : Set ℕ) ⊆ (tupleDomain x : Set ℕ) := by
  intro n hn
  rcases (mem_characteristicIndexSet χ x).mp hn with ⟨hnlt, _hχ⟩
  exact (mem_tupleDomain x).mpr hnlt

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`prop:characteristic-functions-tuple`.

Original label: fixed-length fiber step in
`prop:characteristic-functions-tuple`.

Informal statement: on a fixed tuple-length layer, the fiber of the
characteristic index selector over a finite index set is Borel.

Lean strategy / thesis relation note: this is the thesis' finite-coordinate argument. For length
`n`, membership of the output index set is decided by the finitely many
Boolean tests `χ_i(x_i)`, `i < n`; if the proposed output contains an index
outside `{0, ..., n-1}`, the fiber is empty.
-/
theorem measurableSet_fixedLength_characteristicIndexSet_fiber {X : Type u}
    [EMetricSpace X] (χ : ℕ → X → Bool)
    (hχ : ∀ i : ℕ,
      @Measurable X Bool (emetricBorel X) inferInstance (χ i))
    (n : ℕ) (eta : FiniteSubsets ℕ) :
    @MeasurableSet (Fin n → X) (@borel (Fin n → X) inferInstance)
      {x : Fin n → X | characteristicIndexSet χ (Sigma.mk n x : Tuple X) = eta} := by
  classical
  letI : MeasurableSpace X := emetricBorel X
  letI : OpensMeasurableSpace X := ⟨le_rfl⟩
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : OpensMeasurableSpace (Fin n → X) := ⟨le_rfl⟩
  letI : BorelSpace (Fin n → X) := ⟨rfl⟩
  by_cases heta_domain : (eta : Set ℕ) ⊆ {k : ℕ | k < n}
  · let cell : Fin n → Set (Fin n → X) := fun i =>
      {x : Fin n → X |
        χ i.1 (x i) = if i.1 ∈ (eta : Set ℕ) then true else false}
    have hcell_meas : ∀ i : Fin n, MeasurableSet (cell i) := by
      intro i
      have hcoord :
          @Measurable (Fin n → X) X (@borel (Fin n → X) inferInstance)
            (emetricBorel X) (fun x : Fin n → X => x i) := by
        simpa using (continuous_apply i).measurable
      have htest :
          @Measurable (Fin n → X) Bool (@borel (Fin n → X) inferInstance)
            inferInstance (fun x : Fin n → X => χ i.1 (x i)) :=
        (hχ i.1).comp hcoord
      by_cases hi : i.1 ∈ (eta : Set ℕ)
      · have hpre :
            MeasurableSet
              ((fun x : Fin n → X => χ i.1 (x i)) ⁻¹' ({true} : Set Bool)) :=
          measurableSet_singleton true |>.preimage htest
        simpa [cell, hi, Set.preimage, Set.mem_setOf_eq] using hpre
      · have hpre :
            MeasurableSet
              ((fun x : Fin n → X => χ i.1 (x i)) ⁻¹' ({false} : Set Bool)) :=
          measurableSet_singleton false |>.preimage htest
        simpa [cell, hi, Set.preimage, Set.mem_setOf_eq] using hpre
    have hfiber :
        {x : Fin n → X |
            characteristicIndexSet χ (Sigma.mk n x : Tuple X) = eta} =
          ⋂ i : Fin n, cell i := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iInter]
        intro i
        by_cases hi : i.1 ∈ (eta : Set ℕ)
        · have hi_char :
              i.1 ∈
                (characteristicIndexSet χ (Sigma.mk n x : Tuple X) : Set ℕ) := by
            rw [hx]
            exact hi
          rcases (mem_characteristicIndexSet χ
              (Sigma.mk n x : Tuple X)).mp hi_char with ⟨hilt, htrue⟩
          have hfin : (⟨i.1, hilt⟩ : Fin n) = i := Fin.ext rfl
          simpa [cell, hi, Tuple.entry, hfin] using htrue
        · have hnot_true : χ i.1 (x i) ≠ true := by
            intro htrue
            have hi_char :
                i.1 ∈
                  (characteristicIndexSet χ (Sigma.mk n x : Tuple X) : Set ℕ) :=
              (mem_characteristicIndexSet χ
                (Sigma.mk n x : Tuple X)).mpr
                ⟨i.2, by simpa [Tuple.entry] using htrue⟩
            have hi_eta : i.1 ∈ (eta : Set ℕ) := by
              rw [← hx]
              exact hi_char
            exact hi hi_eta
          cases hval : χ i.1 (x i) <;> simp [cell, hi, hval] at hnot_true ⊢
      · intro hx
        apply Subtype.ext
        ext k
        constructor
        · intro hk
          rcases (mem_characteristicIndexSet χ
              (Sigma.mk n x : Tuple X)).mp hk with ⟨hklt, htrue⟩
          by_contra hk_eta
          have hcell_k : x ∈ cell ⟨k, hklt⟩ := by
            exact (Set.mem_iInter.mp hx) ⟨k, hklt⟩
          have hfalse : χ k (x ⟨k, hklt⟩) = false := by
            simpa [cell, hk_eta] using hcell_k
          simp [Tuple.entry, hfalse] at htrue
        · intro hk
          have hklt : k < n := heta_domain hk
          have hcell_k : x ∈ cell ⟨k, hklt⟩ := by
            exact (Set.mem_iInter.mp hx) ⟨k, hklt⟩
          have htrue : χ k (x ⟨k, hklt⟩) = true := by
            simpa [cell, hk] using hcell_k
          exact (mem_characteristicIndexSet χ
            (Sigma.mk n x : Tuple X)).mpr
            ⟨hklt, by simpa [Tuple.entry] using htrue⟩
    rw [hfiber]
    exact MeasurableSet.iInter hcell_meas
  · have hfiber_empty :
        {x : Fin n → X |
            characteristicIndexSet χ (Sigma.mk n x : Tuple X) = eta} = ∅ := by
      ext x
      constructor
      · intro hx
        exfalso
        apply heta_domain
        intro k hk
        have hk_char :
            k ∈
              (characteristicIndexSet χ (Sigma.mk n x : Tuple X) : Set ℕ) := by
          rw [hx]
          exact hk
        rcases (mem_characteristicIndexSet χ
            (Sigma.mk n x : Tuple X)).mp hk_char with ⟨hklt, _hχtrue⟩
        exact hklt
      · intro hx
        simp at hx
    rw [hfiber_empty]
    exact MeasurableSet.empty

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:characteristic-functions-tuple`.

Original label: fixed-length step in
`prop:characteristic-functions-tuple`.

Informal statement: on every fixed-length layer, the characteristic index
selector is Borel measurable.

Lean strategy / thesis relation note: Lean proves this from measurable fibers into the countable
finite-subset space of `ℕ`. This is the fixed-length version of the thesis'
measurable-set construction.
-/
theorem measurable_fixedLength_characteristicIndexSet {X : Type u}
    [EMetricSpace X] (χ : ℕ → X → Bool)
    (hχ : ∀ i : ℕ,
      @Measurable X Bool (emetricBorel X) inferInstance (χ i))
    (n : ℕ) :
    @Measurable (Fin n → X) (FiniteSubsets ℕ)
      (@borel (Fin n → X) inferInstance) (emetricBorel (FiniteSubsets ℕ))
      (fun x : Fin n → X => characteristicIndexSet χ (Sigma.mk n x : Tuple X)) := by
  classical
  letI : MeasurableSpace (Fin n → X) := @borel (Fin n → X) inferInstance
  letI : MeasurableSpace (FiniteSubsets ℕ) := emetricBorel (FiniteSubsets ℕ)
  haveI : Countable (FiniteSubsets ℕ) := FiniteSubsets.countable
  exact measurable_to_countable' (fun eta =>
    measurableSet_fixedLength_characteristicIndexSet_fiber χ hχ n eta)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:characteristic-functions-tuple`.

Original label: `prop:characteristic-functions-tuple`.

Informal statement: if the coordinate characteristic functions
`\chi_i : X -> {0,1}` are Borel measurable, then the tuple-index selector
`\bm{x} \mapsto \{i : \chi_i(x_i)=1\}` is Borel measurable.

Lean strategy / thesis relation note: the thesis phrases the proof as measurable pasting across the
tuple layers. Lean uses the Chapter 2 theorem
`measurable_tupleHausdorff_iff_fixedLength`, which formalizes exactly that
countable disjoint-union pasting step for the tuple Hausdorff topology.
-/
theorem measurable_characteristicIndexSet_emetricBorel {X : Type u}
    [EMetricSpace X] (χ : ℕ → X → Bool)
    (hχ : ∀ i : ℕ,
      @Measurable X Bool (emetricBorel X) inferInstance (χ i)) :
    @Measurable (Tuple X) (FiniteSubsets ℕ)
      (emetricBorel (Tuple X)) (emetricBorel (FiniteSubsets ℕ))
      (characteristicIndexSet χ) := by
  classical
  letI : MeasurableSpace (Tuple X) := tupleHausdorffBorel (X := X)
  letI : MeasurableSpace (FiniteSubsets ℕ) := emetricBorel (FiniteSubsets ℕ)
  have hfixed :
      ∀ n : ℕ,
        @Measurable (Fin n → X) (FiniteSubsets ℕ)
          (@borel (Fin n → X) inferInstance) (emetricBorel (FiniteSubsets ℕ))
          (fun x : Fin n → X =>
            characteristicIndexSet χ (Sigma.mk n x : Tuple X)) :=
    fun n => measurable_fixedLength_characteristicIndexSet χ hχ n
  have hglobal :
      @Measurable (Tuple X) (FiniteSubsets ℕ)
        (tupleHausdorffBorel (X := X)) (emetricBorel (FiniteSubsets ℕ))
        (characteristicIndexSet χ) :=
    (measurable_tupleHausdorff_iff_fixedLength (X := X)
      (Y := FiniteSubsets ℕ)).2 hfixed
  simpa [tupleHausdorffBorel] using hglobal

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`cor:measurable-index-filter-for-countable-borel-family`.

Original label: `cor:measurable-index-filter-for-countable-borel-family`.

Informal statement: the Boolean characteristic function of a set.

Lean strategy / thesis relation note: arbitrary set membership is classically decidable in the
manuscript. Lean makes this explicit by defining the characteristic function
noncomputably under classical choice.
-/
noncomputable def setCharacteristicBool {X : Type u} (B : Set X) (x : X) :
    Bool := by
  classical
  exact if x ∈ B then true else false

@[simp]
theorem setCharacteristicBool_eq_true {X : Type u} (B : Set X) (x : X) :
    setCharacteristicBool B x = true ↔ x ∈ B := by
  classical
  unfold setCharacteristicBool
  by_cases hx : x ∈ B <;> simp [hx]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`cor:measurable-index-filter-for-countable-borel-family`.

Original label: `cor:measurable-index-filter-for-countable-borel-family`.

Informal statement: the index selector associated with a countable Borel
family `(B_i)` keeps exactly those tuple indices whose entry lies in `B_i`.

Lean strategy / thesis relation note: the thesis writes this directly as a set comprehension. Lean
implements it by turning membership in `B_i` into the Boolean characteristic
function used in `prop:characteristic-functions-tuple`.
-/
noncomputable def borelIndexSet {X : Type u} (B : ℕ → Set X)
    (x : Tuple X) : FiniteSubsets ℕ :=
  characteristicIndexSet (fun i y => setCharacteristicBool (B i) y) x

@[simp]
theorem mem_borelIndexSet {X : Type u} (B : ℕ → Set X)
    (x : Tuple X) {n : ℕ} :
    n ∈ (borelIndexSet B x : Set ℕ) ↔
      ∃ h : n < x.length, Tuple.entry x ⟨n, h⟩ ∈ B n := by
  classical
  simp [borelIndexSet]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`cor:measurable-index-filter-for-countable-borel-family`.

Original label: `cor:measurable-index-filter-for-countable-borel-family`.

Informal statement: if `(B_i)` is a countable family of Borel subsets of
`X`, then `\bm{x} ↦ {i ∈ domain(\bm{x}) : \bm{x}(i) ∈ B_i}` is Borel
measurable from tuple space to finite index sets.

Lean strategy / thesis relation note: this is exactly the thesis corollary from
`prop:characteristic-functions-tuple`; the only Lean-specific step is spelling
the characteristic functions as `if y ∈ B_i then true else false`.
-/
theorem measurable_borelIndexSet_emetricBorel {X : Type u} [EMetricSpace X]
    (B : ℕ → Set X)
    (hB : ∀ i : ℕ, @MeasurableSet X (emetricBorel X) (B i)) :
    @Measurable (Tuple X) (FiniteSubsets ℕ)
      (emetricBorel (Tuple X)) (emetricBorel (FiniteSubsets ℕ))
      (borelIndexSet B) := by
  classical
  letI : MeasurableSpace X := emetricBorel X
  have hχ : ∀ i : ℕ,
      @Measurable X Bool (emetricBorel X) inferInstance
        (fun y : X => setCharacteristicBool (B i) y) := by
    intro i
    change @Measurable X Bool (emetricBorel X) inferInstance
      (fun y : X => if y ∈ B i then true else false)
    exact Measurable.ite (p := fun y : X => y ∈ B i)
      (hB i) measurable_const measurable_const
  simpa [borelIndexSet] using
    measurable_characteristicIndexSet_emetricBorel
      (X := X) (fun i y => setCharacteristicBool (B i) y) hχ

/-! ## Tuple Projections and Decomposition -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, section "Selections,
Filters, and Market Segregation".

Original label: `defn:tuple-projection`.

Informal statement: the tuple projection `\bm{P}_α` applies the product
coordinate projection `P_α` to every entry of a tuple.

Lean strategy / thesis relation note: the thesis writes `X = \prod_{α∈A} X_α`. Lean represents this
dependent product as `(a : A) → X a`; the tuple length is preserved
definitionally.
-/
def tupleProjection {A : Type v} {X : A → Type u} (a : A)
    (x : Tuple ((b : A) → X b)) : Tuple (X a) :=
  Sigma.mk x.length (fun i : Fin x.length => Tuple.entry x i a)

@[simp]
theorem tupleProjection_length {A : Type v} {X : A → Type u}
    (a : A) (x : Tuple ((b : A) → X b)) :
    (tupleProjection a x).length = x.length :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, section "Selections,
Filters, and Market Segregation".

Original label: `defn:tuple-projection`.

Informal statement: the tuple decomposition collects all coordinatewise tuple
projections into the product `\prod_α \mathscr{T}(X_α)`.
-/
def tupleDecomposition {A : Type v} {X : A → Type u}
    (x : Tuple ((b : A) → X b)) : (a : A) → Tuple (X a) :=
  fun a => tupleProjection a x

@[simp]
theorem tupleDecomposition_apply {A : Type v} {X : A → Type u}
    (x : Tuple ((b : A) → X b)) (a : A) :
    tupleDecomposition x a = tupleProjection a x :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:tuple-projection-continuous`.

Original label: fixed-length step in `prop:tuple-projection-continuous`.

Informal statement: on a fixed tuple-length layer, projecting every product
coordinate is continuous.

Lean strategy / thesis relation note: this is the fixed-length product-topology part of the thesis
epsilon proof. The finite-index assumption makes Lean's product extended
metric topology agree with the ordinary product topology used by
`continuous_pi`.
-/
theorem continuous_fixedLength_tupleProjection {A : Type v} {X : A → Type u}
    [∀ a, EMetricSpace (X a)] (a : A) (n : ℕ) :
    letI : TopologicalSpace (Tuple (X a)) := tupleHausdorffMetricTopology (X := X a)
    @Continuous (Fin n → ((b : A) → X b)) (Tuple (X a)) inferInstance
      (tupleHausdorffMetricTopology (X := X a))
      (fun x : Fin n → ((b : A) → X b) =>
        tupleProjection a (Sigma.mk n x : Tuple ((b : A) → X b))) := by
  letI : TopologicalSpace (Tuple (X a)) := tupleHausdorffMetricTopology (X := X a)
  have hcoord :
      Continuous (fun x : Fin n → ((b : A) → X b) =>
        fun i : Fin n => x i a) := by
    exact continuous_pi (fun i => (continuous_apply a).comp (continuous_apply i))
  exact (continuous_sigmaMk_tupleHausdorff (X := X a) n).comp hcoord

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:tuple-projection-continuous`.

Original label: `prop:tuple-projection-continuous`.

Informal statement: each tuple projection
`\bm{P}_α : \mathscr{T}(\prod_α X_α) → \mathscr{T}(X_α)` is continuous.

Lean strategy / thesis relation note: the proof follows the thesis standard-machinery reduction:
prove continuity on each fixed-length product layer, then paste over the
tuple disjoint union of lengths.
-/
theorem continuous_tupleProjection_tupleHausdorff {A : Type v} {X : A → Type u}
    [Fintype A] [∀ a, EMetricSpace (X a)] (a : A) :
    @Continuous (Tuple ((b : A) → X b)) (Tuple (X a))
      (tupleHausdorffMetricTopology (X := ((b : A) → X b)))
      (tupleHausdorffMetricTopology (X := X a))
      (tupleProjection a) := by
  letI : TopologicalSpace (Tuple ((b : A) → X b)) :=
    tupleHausdorffMetricTopology (X := ((b : A) → X b))
  letI : TopologicalSpace (Tuple (X a)) := tupleHausdorffMetricTopology (X := X a)
  rw [continuous_tupleHausdorff_iff_fixedLength]
  intro n
  exact continuous_fixedLength_tupleProjection (X := X) a n

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:tuple-projection-continuous`.

Original label: `prop:tuple-projection-continuous`.

Informal statement: the tuple decomposition
`\bm{P} : \mathscr{T}(\prod_α X_α) → \prod_α \mathscr{T}(X_α)` is continuous
for the product topology.
-/
theorem continuous_tupleDecomposition_tupleHausdorff {A : Type v} {X : A → Type u}
    [Fintype A] [∀ a, EMetricSpace (X a)] :
    letI : ∀ a : A, TopologicalSpace (Tuple (X a)) :=
      fun a => tupleHausdorffMetricTopology (X := X a)
    @Continuous (Tuple ((b : A) → X b)) ((a : A) → Tuple (X a))
      (tupleHausdorffMetricTopology (X := ((b : A) → X b))) inferInstance
      (tupleDecomposition (X := X)) := by
  letI : TopologicalSpace (Tuple ((b : A) → X b)) :=
    tupleHausdorffMetricTopology (X := ((b : A) → X b))
  letI : ∀ a : A, TopologicalSpace (Tuple (X a)) :=
    fun a => tupleHausdorffMetricTopology (X := X a)
  exact continuous_pi (fun a => continuous_tupleProjection_tupleHausdorff (X := X) a)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:tuple-projection-continuous`.

Original label: injectivity part of `prop:tuple-projection-continuous`.

Informal statement: over a nonempty index family, the tuple decomposition is
injective.

Lean strategy / thesis relation note: nonemptiness is needed to recover the common tuple length from
one coordinate projection. Once the length is known, equality of all
coordinate projections is pointwise equality in the dependent product.
-/
theorem tupleDecomposition_injective {A : Type v} [Nonempty A]
    {X : A → Type u} :
    Function.Injective (tupleDecomposition (X := X)) := by
  classical
  intro x y h
  rcases x with ⟨n, x⟩
  rcases y with ⟨m, y⟩
  let a0 : A := Classical.choice inferInstance
  have hproj : tupleProjection a0 (Sigma.mk n x : Tuple ((b : A) → X b)) =
      tupleProjection a0 (Sigma.mk m y : Tuple ((b : A) → X b)) := by
    exact congrFun h a0
  have hnm : n = m := by
    have hlen := congrArg Tuple.length hproj
    simpa [tupleProjection, Tuple.length] using hlen
  subst m
  congr
  funext i a
  have hproj_a : tupleProjection a (Sigma.mk n x : Tuple ((b : A) → X b)) =
      tupleProjection a (Sigma.mk n y : Tuple ((b : A) → X b)) := by
    exact congrFun h a
  have hfun : (fun i : Fin n => x i a) = (fun i : Fin n => y i a) := by
    injection hproj_a with _ hfun
  exact congrFun hfun i

/-! ## Separation Operators -/

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, section "Selections,
Filters, and Market Segregation".

Original label: auxiliary tag characteristic for `defn:separation-operators`.

Informal statement: the Boolean test for whether a disjoint-union element has
tag `a`.

Lean strategy / thesis relation note: the thesis writes membership in `X_a × {a}`. In Lean's Sigma
encoding of disjoint unions, this is the tag equality `z.1 = a`.
-/
def sigmaTagBool {A : Type v} [DecidableEq A] {X : A → Type u}
    (a : A) (z : DisjointUnion X) : Bool :=
  if z.1 = a then true else false

@[simp]
theorem sigmaTagBool_eq_true {A : Type v} [DecidableEq A]
    {X : A → Type u} (a : A) (z : DisjointUnion X) :
    sigmaTagBool a z = true ↔ z.1 = a := by
  unfold sigmaTagBool
  by_cases h : z.1 = a <;> simp [h]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`defn:separation-operators`.

Original label: proof-carrying element projection in
`defn:separation-operators`.

Informal statement: once a disjoint-union element is known to have tag `a`,
return its value as an element of `X_a`.

Lean strategy / thesis relation note: this is the formal version of the thesis'
`P_element (x,a)=x`. The proof `h : z.1 = a` is invisible in ZFC notation but
necessary in Lean's dependent Sigma type.
-/
def valueAtTag {A : Type v} {X : A → Type u}
    (a : A) (z : DisjointUnion X) (h : z.1 = a) : X a :=
  h ▸ z.2

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`defn:separation-operators`.

Original label: index set in `defn:separation-operators`.

Informal statement: the finite index set
`{i ∈ domain(x) : x(i) ∈ X_a × {a}}`.
-/
noncomputable def separationIndexSet {A : Type v} [DecidableEq A]
    {X : A → Type u} (a : A) (x : Tuple (DisjointUnion X)) :
    FiniteSubsets ℕ :=
  characteristicIndexSet (fun _ z => sigmaTagBool a z) x

@[simp]
theorem mem_separationIndexSet {A : Type v} [DecidableEq A]
    {X : A → Type u} (a : A) (x : Tuple (DisjointUnion X)) {n : ℕ} :
    n ∈ (separationIndexSet a x : Set ℕ) ↔
      ∃ h : n < x.length, (Tuple.entry x ⟨n, h⟩).1 = a := by
  simp [separationIndexSet]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`defn:separation-operators`.

Original label: auxiliary construction for `defn:separation-operators`.

Informal statement: project a tuple along a finite set of indices already
known to point into the `a`-component.

Lean strategy / thesis relation note: this isolates the dependent proof that the selected Sigma
entries have tag `a`. It is the formal analogue of applying
`P_element` after the filtering step.
-/
noncomputable def componentFromIndices {A : Type v} [DecidableEq A]
    {X : A → Type u} (a : A) (x : Tuple (DisjointUnion X))
    (eta : FiniteSubsets ℕ)
    (hη : (eta : Set ℕ) ⊆ (separationIndexSet a x : Set ℕ)) :
    Tuple (X a) :=
  let p := pairing eta
  ⟨p.length, fun i =>
    let n := Tuple.entry p i
    have hnmem : n ∈ (eta : Set ℕ) := pairing_entry_mem eta i
    have hsel : n ∈ (separationIndexSet a x : Set ℕ) := hη hnmem
    have hn : n < x.length := by
      rcases (mem_separationIndexSet a x).mp hsel with ⟨hn, _htag⟩
      exact hn
    let z := Tuple.entry x ⟨n, hn⟩
    have htag : z.1 = a := by
      rcases (mem_separationIndexSet a x).mp hsel with ⟨hn', htag'⟩
      have hfin : (⟨n, hn'⟩ : Fin x.length) = ⟨n, hn⟩ := rfl
      simpa [z, hfin] using htag'
    valueAtTag a z htag⟩

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`defn:separation-operators`.

Original label: `defn:separation-operators`.

Informal statement: the `a`-separation operator filters a tuple in the
disjoint union to the entries tagged by `a`, then forgets the tag.

Lean strategy / thesis relation note: the filtering indices are enumerated by the same increasing
finite-set pairing used in Chapter 3's reindexing operator. This is the Lean
version of the thesis formula
`\Pi_a x = P_element (x[{i : x(i) ∈ X_a × {a}}])`.
-/
noncomputable def separationComponent {A : Type v} [DecidableEq A]
    {X : A → Type u} (a : A) (x : Tuple (DisjointUnion X)) : Tuple (X a) :=
  componentFromIndices a x (separationIndexSet a x) (fun _ hn => hn)

@[simp]
theorem separationComponent_length {A : Type v} [DecidableEq A]
    {X : A → Type u} (a : A) (x : Tuple (DisjointUnion X)) :
    (separationComponent a x).length =
      (pairing (separationIndexSet a x)).length :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`defn:separation-operators`.

Original label: `defn:separation-operators`.

Informal statement: the full separation operator collects all component
separations into the product `\prod_a \mathscr{T}(X_a)`.
-/
noncomputable def separationOperator {A : Type v} [DecidableEq A]
    {X : A → Type u} (x : Tuple (DisjointUnion X)) :
    (a : A) → Tuple (X a) :=
  fun a => separationComponent a x

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`prop:separation-continuous`.

Original label: radius-`1` tag-stability step in
`prop:separation-continuous`.

Informal statement: in the disjoint-union metric, points at distance below
`1` must lie in the same component.

Lean strategy / thesis relation note: this is the formal version of the thesis observation that
cross-component distances are infinite.
-/
theorem tag_eq_of_disjoint_edist_lt_one {A : Type v} {X : A → Type u}
    [∀ a, EMetricSpace (X a)] {z w : DisjointUnion X}
    (h : @edist (DisjointUnion X)
        (DisjointUnionTopology.disjointUnionEMetricSpace (X := X)).toEDist z w <
      (1 : ENNReal)) :
    z.1 = w.1 := by
  rcases z with ⟨az, z⟩
  rcases w with ⟨aw, w⟩
  by_contra hne
  change DisjointUnionTopology.disjointEdist
      (Sigma.mk az z : DisjointUnion X) (Sigma.mk aw w) < (1 : ENNReal) at h
  rw [DisjointUnionTopology.disjointEdist_mk_mk_ne (X := X) hne] at h
  exact (not_lt_of_ge (le_top : (1 : ENNReal) ≤ ⊤)) h

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`prop:separation-continuous`.

Original label: element-projection distance step in
`prop:separation-continuous`.

Informal statement: when two disjoint-union points have the same tag `a`,
their disjoint-union distance is exactly the component distance between their
projected values.
-/
theorem valueAtTag_edist_eq {A : Type v} {X : A → Type u}
    [∀ a, EMetricSpace (X a)] {a : A} {z w : DisjointUnion X}
    (hz : z.1 = a) (hw : w.1 = a) :
    edist (valueAtTag a z hz) (valueAtTag a w hw) =
      @edist (DisjointUnion X)
        (DisjointUnionTopology.disjointUnionEMetricSpace (X := X)).toEDist z w := by
  rcases z with ⟨az, z⟩
  rcases w with ⟨aw, w⟩
  cases hz
  cases hw
  change edist z w =
    DisjointUnionTopology.disjointEdist
      (Sigma.mk az z : DisjointUnion X) (Sigma.mk az w)
  rw [DisjointUnionTopology.disjointEdist_mk_mk_same]

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`prop:separation-continuous`.

Original label: selected-index stability in `prop:separation-continuous`.

Informal statement: below tuple Hausdorff distance `1`, fixed-length tuples
over the disjoint union have the same indices in the `a`-component.
-/
theorem separationIndexSet_eq_of_fixed_edist_lt_one {A : Type v}
    [DecidableEq A] {X : A → Type u} [∀ a, EMetricSpace (X a)]
    {n : ℕ} {x y : Fin n → DisjointUnion X} (a : A)
    (h :
      letI : EMetricSpace (DisjointUnion X) :=
        DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
      edist (Sigma.mk n x : Tuple (DisjointUnion X))
        (Sigma.mk n y : Tuple (DisjointUnion X)) < (1 : ENNReal)) :
    separationIndexSet a (Sigma.mk n x : Tuple (DisjointUnion X)) =
      separationIndexSet a (Sigma.mk n y : Tuple (DisjointUnion X)) := by
  letI : EMetricSpace (DisjointUnion X) :=
    DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
  apply Subtype.ext
  ext k
  constructor
  · intro hk
    rcases (mem_separationIndexSet a
        (Sigma.mk n x : Tuple (DisjointUnion X))).mp hk with
      ⟨hklt, htag⟩
    have hcoord_lt :
        @edist (DisjointUnion X)
            (DisjointUnionTopology.disjointUnionEMetricSpace (X := X)).toEDist
            (x ⟨k, hklt⟩) (y ⟨k, hklt⟩) < (1 : ENNReal) := by
      simpa [Tuple.entry] using
        coordinate_edist_lt_one_of_fixedLength_edist_lt_one
          (X := DisjointUnion X) h ⟨k, hklt⟩
    have htagxy : (x ⟨k, hklt⟩).1 = (y ⟨k, hklt⟩).1 :=
      tag_eq_of_disjoint_edist_lt_one (X := X) hcoord_lt
    exact (mem_separationIndexSet a
        (Sigma.mk n y : Tuple (DisjointUnion X))).mpr
      ⟨hklt, by simpa [← htagxy] using htag⟩
  · intro hk
    rcases (mem_separationIndexSet a
        (Sigma.mk n y : Tuple (DisjointUnion X))).mp hk with
      ⟨hklt, htag⟩
    have hsym : edist (Sigma.mk n y : Tuple (DisjointUnion X))
        (Sigma.mk n x : Tuple (DisjointUnion X)) < (1 : ENNReal) := by
      simpa [edist_comm] using h
    have hcoord_lt :
        @edist (DisjointUnion X)
            (DisjointUnionTopology.disjointUnionEMetricSpace (X := X)).toEDist
            (y ⟨k, hklt⟩) (x ⟨k, hklt⟩) < (1 : ENNReal) := by
      simpa [Tuple.entry] using
        coordinate_edist_lt_one_of_fixedLength_edist_lt_one
          (X := DisjointUnion X) hsym ⟨k, hklt⟩
    have htagxy : (y ⟨k, hklt⟩).1 = (x ⟨k, hklt⟩).1 :=
      tag_eq_of_disjoint_edist_lt_one (X := X) hcoord_lt
    exact (mem_separationIndexSet a
        (Sigma.mk n x : Tuple (DisjointUnion X))).mpr
      ⟨hklt, by simpa [← htagxy] using htag⟩

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`, proof of
`prop:separation-continuous`.

Original label: fixed-index estimate in `prop:separation-continuous`.

Informal statement: if two fixed-length disjoint-union tuples are close and a
common finite index set selects entries in component `a` for both, then the
projected component tuples are close by the same radius.

Lean strategy / thesis relation note: this is the proof's quantitative core. It uses the thesis'
same-index comparison after the radius-`1` stabilization step.
-/
theorem componentFromIndices_edist_lt_of_fixed_near {A : Type v}
    [DecidableEq A] {X : A → Type u} [∀ a, EMetricSpace (X a)]
    {n : ℕ} {x y : Fin n → DisjointUnion X}
    {eta : FiniteSubsets ℕ} {δ : ENNReal} (a : A)
    (hδle : δ ≤ (1 : ENNReal))
    (hxyδ :
      letI : EMetricSpace (DisjointUnion X) :=
        DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
      edist (Sigma.mk n x : Tuple (DisjointUnion X))
        (Sigma.mk n y : Tuple (DisjointUnion X)) < δ)
    (hηx : (eta : Set ℕ) ⊆
      (separationIndexSet a (Sigma.mk n x : Tuple (DisjointUnion X)) : Set ℕ))
    (hηy : (eta : Set ℕ) ⊆
      (separationIndexSet a (Sigma.mk n y : Tuple (DisjointUnion X)) : Set ℕ)) :
    edist (componentFromIndices a
        (Sigma.mk n x : Tuple (DisjointUnion X)) eta hηx)
      (componentFromIndices a
        (Sigma.mk n y : Tuple (DisjointUnion X)) eta hηy) < δ := by
  letI : EMetricSpace (DisjointUnion X) :=
    DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
  let p := pairing eta
  have hδpos : (⊥ : ENNReal) < δ := lt_of_le_of_lt bot_le hxyδ
  have hxy_one : edist (Sigma.mk n x : Tuple (DisjointUnion X))
      (Sigma.mk n y : Tuple (DisjointUnion X)) < (1 : ENNReal) :=
    lt_of_lt_of_le hxyδ hδle
  have hcoord : ∀ i : Fin p.length,
      edist
        (Tuple.entry
          (componentFromIndices a
            (Sigma.mk n x : Tuple (DisjointUnion X)) eta hηx) i)
        (Tuple.entry
          (componentFromIndices a
            (Sigma.mk n y : Tuple (DisjointUnion X)) eta hηy) i) < δ := by
    intro i
    let k := Tuple.entry p i
    have hkmem : k ∈ (eta : Set ℕ) := pairing_entry_mem eta i
    have hxsel :
        k ∈ (separationIndexSet a
          (Sigma.mk n x : Tuple (DisjointUnion X)) : Set ℕ) := hηx hkmem
    have hysel :
        k ∈ (separationIndexSet a
          (Sigma.mk n y : Tuple (DisjointUnion X)) : Set ℕ) := hηy hkmem
    rcases (mem_separationIndexSet a
        (Sigma.mk n x : Tuple (DisjointUnion X))).mp hxsel with
      ⟨hkxlt, hxtag⟩
    rcases (mem_separationIndexSet a
        (Sigma.mk n y : Tuple (DisjointUnion X))).mp hysel with
      ⟨hkylt, hytag⟩
    have hxtag' : (x ⟨k, hkxlt⟩).1 = a := by
      simpa [Tuple.entry] using hxtag
    have hytag' : (y ⟨k, hkylt⟩).1 = a := by
      simpa [Tuple.entry] using hytag
    have hkx_eq : (⟨k, hkxlt⟩ : Fin n) = ⟨k, hkylt⟩ := rfl
    have hcoord_le :
        @edist (DisjointUnion X)
            (DisjointUnionTopology.disjointUnionEMetricSpace (X := X)).toEDist
            (x ⟨k, hkxlt⟩) (y ⟨k, hkylt⟩) ≤
          edist (Sigma.mk n x : Tuple (DisjointUnion X))
            (Sigma.mk n y : Tuple (DisjointUnion X)) := by
      simpa [hkx_eq] using
        coordinate_edist_le_fixedLength_edist_of_lt_one
          (X := DisjointUnion X) hxy_one ⟨k, hkxlt⟩
    have hcoord_lt :
        @edist (DisjointUnion X)
            (DisjointUnionTopology.disjointUnionEMetricSpace (X := X)).toEDist
            (x ⟨k, hkxlt⟩) (y ⟨k, hkylt⟩) < δ :=
      lt_of_le_of_lt hcoord_le hxyδ
    change edist (valueAtTag a (x ⟨k, hkxlt⟩) hxtag')
        (valueAtTag a (y ⟨k, hkylt⟩) hytag') < δ
    rw [valueAtTag_edist_eq (X := X) hxtag' hytag']
    exact hcoord_lt
  have hsup : coordinateEDistSup
      (fun i : Fin p.length =>
        Tuple.entry
          (componentFromIndices a
            (Sigma.mk n x : Tuple (DisjointUnion X)) eta hηx) i)
      (fun i : Fin p.length =>
        Tuple.entry
          (componentFromIndices a
            (Sigma.mk n y : Tuple (DisjointUnion X)) eta hηy) i) < δ := by
    rw [coordinateEDistSup]
    exact (Finset.sup_lt_iff hδpos).mpr (fun i _hi => hcoord i)
  calc
    edist (componentFromIndices a
        (Sigma.mk n x : Tuple (DisjointUnion X)) eta hηx)
      (componentFromIndices a
        (Sigma.mk n y : Tuple (DisjointUnion X)) eta hηy)
        ≤ coordinateEDistSup
          (fun i : Fin p.length =>
            Tuple.entry
              (componentFromIndices a
                (Sigma.mk n x : Tuple (DisjointUnion X)) eta hηx) i)
          (fun i : Fin p.length =>
            Tuple.entry
              (componentFromIndices a
                (Sigma.mk n y : Tuple (DisjointUnion X)) eta hηy) i) := by
          simpa [componentFromIndices, p] using
            (fixedLength_edist_le_coordinateEDistSup
              (X := X a)
              (x := fun i : Fin p.length =>
                Tuple.entry
                  (componentFromIndices a
                    (Sigma.mk n x : Tuple (DisjointUnion X)) eta hηx) i)
              (y := fun i : Fin p.length =>
                Tuple.entry
                  (componentFromIndices a
                    (Sigma.mk n y : Tuple (DisjointUnion X)) eta hηy) i))
    _ < δ := hsup

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:separation-continuous`.

Original label: component part of `prop:separation-continuous`.

Informal statement: the `a`-separation operator is continuous at every tuple
when the disjoint union is endowed with the thesis disjoint-union metric.

Lean strategy / thesis relation note: this is the thesis proof verbatim in radius form. Below radius
`1`, tuple length and component tags stabilize; the selected index set is
therefore unchanged, and the projected component tuple is controlled by the
same coordinatewise distance estimate.
-/
theorem continuousAt_separationComponent_disjointTopology {A : Type v}
    [DecidableEq A] {X : A → Type u} [∀ a, EMetricSpace (X a)]
    (a : A) (x₀Tuple : Tuple (DisjointUnion X)) :
    letI : EMetricSpace (DisjointUnion X) :=
      DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
    @ContinuousAt (Tuple (DisjointUnion X)) (Tuple (X a))
      (tupleHausdorffMetricTopology (X := DisjointUnion X))
      (tupleHausdorffMetricTopology (X := X a))
      (separationComponent a) x₀Tuple := by
  letI : EMetricSpace (DisjointUnion X) :=
    DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
  letI : TopologicalSpace (Tuple (DisjointUnion X)) :=
    tupleHausdorffMetricTopology (X := DisjointUnion X)
  letI : TopologicalSpace (Tuple (X a)) := tupleHausdorffMetricTopology (X := X a)
  rcases x₀Tuple with ⟨m, x₀⟩
  rw [ContinuousAt, EMetric.tendsto_nhds_nhds]
  intro ε hε
  let δ : ENNReal := min ε (1 : ENNReal)
  refine ⟨δ, lt_min hε zero_lt_one, ?_⟩
  intro xTuple hxδ
  rcases xTuple with ⟨m', x⟩
  have hx_one : edist (Sigma.mk m' x : Tuple (DisjointUnion X))
      (Sigma.mk m x₀ : Tuple (DisjointUnion X)) < (1 : ENNReal) :=
    lt_of_lt_of_le hxδ (min_le_right _ _)
  have hm : m' = m := by
    simpa [Tuple.length] using length_eq_of_edist_lt_one hx_one
  subst m'
  have heta : separationIndexSet a (Sigma.mk m x : Tuple (DisjointUnion X)) =
      separationIndexSet a (Sigma.mk m x₀ : Tuple (DisjointUnion X)) :=
    separationIndexSet_eq_of_fixed_edist_lt_one (X := X) a hx_one
  let eta := separationIndexSet a (Sigma.mk m x₀ : Tuple (DisjointUnion X))
  have hηx : (eta : Set ℕ) ⊆
      (separationIndexSet a (Sigma.mk m x : Tuple (DisjointUnion X)) : Set ℕ) := by
    intro k hk
    simpa [eta, heta] using hk
  have hηx0 : (eta : Set ℕ) ⊆
      (separationIndexSet a (Sigma.mk m x₀ : Tuple (DisjointUnion X)) : Set ℕ) := by
    intro k hk
    simpa [eta] using hk
  have hcomp_x : separationComponent a (Sigma.mk m x : Tuple (DisjointUnion X)) =
      componentFromIndices a (Sigma.mk m x : Tuple (DisjointUnion X)) eta hηx := by
    subst eta
    simp [separationComponent, heta]
  have hcomp_x0 : separationComponent a (Sigma.mk m x₀ : Tuple (DisjointUnion X)) =
      componentFromIndices a (Sigma.mk m x₀ : Tuple (DisjointUnion X)) eta hηx0 := by
    subst eta
    simp [separationComponent]
  have hδle : δ ≤ (1 : ENNReal) := min_le_right _ _
  have hclose : edist
      (componentFromIndices a (Sigma.mk m x : Tuple (DisjointUnion X)) eta hηx)
      (componentFromIndices a (Sigma.mk m x₀ : Tuple (DisjointUnion X)) eta hηx0) <
        δ :=
    componentFromIndices_edist_lt_of_fixed_near (X := X) a hδle hxδ hηx hηx0
  have houtδ : edist
      (separationComponent a (Sigma.mk m x : Tuple (DisjointUnion X)))
      (separationComponent a (Sigma.mk m x₀ : Tuple (DisjointUnion X))) < δ := by
    simpa [hcomp_x, hcomp_x0] using hclose
  exact lt_of_lt_of_le houtδ (min_le_left _ _)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:separation-continuous`.

Original label: `prop:separation-continuous`.

Informal statement: each component separation operator
`\Pi_a : \mathscr{T}(\bigsqcup_a X_a) -> \mathscr{T}(X_a)` is continuous.
-/
theorem continuous_separationComponent_disjointTopology {A : Type v}
    [DecidableEq A] {X : A → Type u} [∀ a, EMetricSpace (X a)]
    (a : A) :
    letI : EMetricSpace (DisjointUnion X) :=
      DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
    @Continuous (Tuple (DisjointUnion X)) (Tuple (X a))
      (tupleHausdorffMetricTopology (X := DisjointUnion X))
      (tupleHausdorffMetricTopology (X := X a))
      (separationComponent a) := by
  letI : EMetricSpace (DisjointUnion X) :=
    DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
  letI : TopologicalSpace (Tuple (DisjointUnion X)) :=
    tupleHausdorffMetricTopology (X := DisjointUnion X)
  letI : TopologicalSpace (Tuple (X a)) := tupleHausdorffMetricTopology (X := X a)
  rw [continuous_iff_continuousAt]
  exact continuousAt_separationComponent_disjointTopology (X := X) a

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:separation-continuous`.

Original label: product part of `prop:separation-continuous`.

Informal statement: the full separation operator
`\Pi x = (\Pi_a x)_a` is continuous into the product of component tuple
spaces.

Lean strategy / thesis relation note: Lean states this for the product topology on
`\prod_a \mathscr{T}(X_a)`. For the finite/countable product-metric
instances used downstream, this is the same topology targeted by the thesis'
maximum/sup product metric formulation.

Lean strategy / thesis strategy note: this is the topology-first product statement. The finite
wrapper `continuous_separationOperator_finitePiEMetric` restates the same
result for Lean's finite `Pi` extended-metric topology, which is the formal
counterpart of the thesis' maximum product metric on finite products. A
countably infinite sup-metric bridge would be a separate theorem if the
manuscript later needs that exact topology.
-/
theorem continuous_separationOperator_disjointTopology {A : Type v}
    [DecidableEq A] {X : A → Type u} [∀ a, EMetricSpace (X a)] :
    letI : EMetricSpace (DisjointUnion X) :=
      DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
    letI : ∀ a : A, TopologicalSpace (Tuple (X a)) :=
      fun a => tupleHausdorffMetricTopology (X := X a)
    @Continuous (Tuple (DisjointUnion X)) ((a : A) → Tuple (X a))
      (tupleHausdorffMetricTopology (X := DisjointUnion X)) inferInstance
      (separationOperator (X := X)) := by
  letI : EMetricSpace (DisjointUnion X) :=
    DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
  letI : TopologicalSpace (Tuple (DisjointUnion X)) :=
    tupleHausdorffMetricTopology (X := DisjointUnion X)
  letI : ∀ a : A, TopologicalSpace (Tuple (X a)) :=
    fun a => tupleHausdorffMetricTopology (X := X a)
  exact continuous_pi (fun a => continuous_separationComponent_disjointTopology (X := X) a)

/--
Thesis source:
`1 - theoretical foundations/4_market_clearing.tex`,
`prop:separation-continuous`.

Original label: finite product-metric form of `prop:separation-continuous`.

Informal statement: when the component family is finite, the full separation
operator is continuous into the finite product equipped with Lean's product
extended-metric topology.

Lean strategy / thesis relation note: for finite products, Lean's `Pi` extended-metric topology is
the maximum/sup product topology used in the thesis. The proof is therefore
the product-topology theorem above with the finite `Pi` metric topology made
explicit in the codomain.
-/
theorem continuous_separationOperator_finitePiEMetric {A : Type v}
    [Fintype A] [DecidableEq A] {X : A → Type u} [∀ a, EMetricSpace (X a)] :
    letI : EMetricSpace (DisjointUnion X) :=
      DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
    letI : ∀ a : A, TopologicalSpace (Tuple (X a)) :=
      fun a => tupleHausdorffMetricTopology (X := X a)
    @Continuous (Tuple (DisjointUnion X)) ((a : A) → Tuple (X a))
      (tupleHausdorffMetricTopology (X := DisjointUnion X))
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (separationOperator (X := X)) := by
  letI : EMetricSpace (DisjointUnion X) :=
    DisjointUnionTopology.disjointUnionEMetricSpace (X := X)
  letI : TopologicalSpace (Tuple (DisjointUnion X)) :=
    tupleHausdorffMetricTopology (X := DisjointUnion X)
  letI : ∀ a : A, TopologicalSpace (Tuple (X a)) :=
    fun a => tupleHausdorffMetricTopology (X := X a)
  exact continuous_separationOperator_disjointTopology (X := X)

end Selection
end MarketClearing
end Foundations
end Thesis
