import Thesis.Foundations.MarketClearing.DoctoralResults
import Thesis.Foundations.MarketRepresentation.TupleTopologyAlignment
import Thesis.Foundations.MarketClearing.Alignment
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
namespace Thesis.Foundations.MarketClearing.DoctoralSemicontinuity

open MarketRepresentation TuplesBasic TuplesMetricTopology
open MarketRepresentation.TuplesMeasurableSorting
open Sorting Equilibrium MidpointPrice
open Filter Set Topology

variable {α : Type*} [TopologicalSpace α]

def candidate (ps pb : α → ℝ) (qs qb : α → Quantity) (x : α) : Quantity :=
  if ps x ≤ pb x then min (qs x) (qb x) else 0

theorem upperSemicontinuous_candidate {ps pb : α → ℝ} {qs qb : α → Quantity}
    (hs : Continuous ps) (hb : Continuous pb) (hqs : Continuous qs) (hqb : Continuous qb) :
    UpperSemicontinuous (candidate ps pb qs qb) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro r
  by_cases hr : r = 0
  · simp only [hr, preimage, mem_Ici, zero_le, setOf_true]
    exact isClosed_univ
  · have hpos : 0 < r := pos_iff_ne_zero.mpr hr
    have he : (candidate ps pb qs qb) ⁻¹' Ici r =
        {x | ps x ≤ pb x} ∩ {x | r ≤ min (qs x) (qb x)} := by
      ext x
      by_cases hp : ps x ≤ pb x <;> simp [candidate, hp, not_le_of_gt hpos]
    rw [he]
    exact (isClosed_le hs hb).inter (isClosed_le continuous_const (hqs.min hqb))

theorem upperSemicontinuous_finset_sup {ι : Type*} (s : Finset ι)
    (f : ι → α → Quantity) (h : ∀ i ∈ s, UpperSemicontinuous (f i)) :
    UpperSemicontinuous (fun x ↦ s.sup fun i ↦ f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (upperSemicontinuous_const : UpperSemicontinuous (fun _ : α ↦ (0 : Quantity)))
  | @insert i s hi ih =>
    simp only [Finset.sup_insert]
    exact (h i (by simp)).sup (ih fun j hj ↦ h j (by simp [hj]))

abbrev LayerInput (n m : ℕ) :=
  ((Fin n → Quantity) × (Fin n → ℝ)) × ((Fin m → Quantity) × (Fin m → ℝ))

def layerVolume {n m : ℕ} (x : LayerInput n m) : Quantity :=
  Finset.univ.sup fun ij : Fin n × Fin m ↦
    candidate (fun y : LayerInput n m ↦ y.1.2 ij.1) (fun y ↦ y.2.2 ij.2)
      (fun y ↦ y.1.1 ij.1) (fun y ↦ y.2.1 ij.2) x

/-- Original label: `prop:executable-volume-usc`.
Upper semicontinuity on every full fixed-length layer, before restriction to
monotone cumulative quantities and sorted prices. -/
theorem upperSemicontinuous_layerVolume (n m : ℕ) :
    UpperSemicontinuous (@layerVolume n m) := by
  apply upperSemicontinuous_finset_sup
  intro ij _
  apply upperSemicontinuous_candidate <;> fun_prop

theorem continuousAt_candidate {ps pb : α → ℝ} {qs qb : α → Quantity}
    (hs : Continuous ps) (hb : Continuous pb) (hqs : Continuous qs) (hqb : Continuous qb)
    {x : α} (hx : ps x ≠ pb x) : ContinuousAt (candidate ps pb qs qb) x := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have he : candidate ps pb qs qb =ᶠ[𝓝 x] fun y ↦ min (qs y) (qb y) := by
      filter_upwards [(isOpen_lt hs hb).mem_nhds hlt] with y hy
      exact if_pos hy.le
    exact ((hqs.min hqb).continuousAt.congr_of_eventuallyEq he)
  · have he : candidate ps pb qs qb =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [(isOpen_lt hb hs).mem_nhds hgt] with y hy
      exact if_neg (not_le_of_gt hy)
    exact continuousAt_const.congr_of_eventuallyEq he

/-- Original label: `prop:executable-volume-usc`.
The fixed-layer quantity is continuous whenever no opposite prices are tied. -/
theorem continuousAt_layerVolume {n m : ℕ} (x : LayerInput n m)
    (hx : ∀ i j, x.1.2 i ≠ x.2.2 j) : ContinuousAt (@layerVolume n m) x := by
  apply ContinuousAt.finset_sup_apply
  intro ij _
  exact continuousAt_candidate (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (hx _ _)

abbrev ClearingInput := (Tuple Quantity × Tuple ℝ) × (Tuple Quantity × Tuple ℝ)

local instance : TopologicalSpace (Tuple Quantity) := tupleHausdorffMetricTopology
local instance : TopologicalSpace (Tuple ℝ) := tupleHausdorffMetricTopology

def finiteVolume (n m : ℕ) (s : ClearingInput) : Quantity :=
  Finset.univ.sup fun ij : Fin n × Fin m ↦
    candidate (fun x : ClearingInput ↦ tuplePriceEval ij.1.val x.1.2)
      (fun x ↦ tuplePriceEval ij.2.val x.2.2)
      (fun x ↦ tupleQuantityEval ij.1.val x.1.1)
      (fun x ↦ tupleQuantityEval ij.2.val x.2.1) s

theorem equilibrium_eq_finiteVolume (s : ClearingInput) {n m : ℕ}
    (hn : s.1.2.length = n) (hm : s.2.2.length = m) :
    equilibriumQuantity s = finiteVolume n m s := by
  dsimp only [equilibriumQuantity, maxClearedQuantityForIndexSet, finiteVolume]
  apply le_antisymm
  · apply Finset.sup_le
    intro ij hij
    obtain ⟨hi, hj, hp⟩ := (mem_feasibleEquilibriumIndexSet _ _).mp
      ((FiniteSets.FiniteSubsets.mem_toFinset _).mp hij)
    have hi' : ij.1 < n := hn ▸ hi
    have hj' : ij.2 < m := hm ▸ hj
    change ij.1 < s.1.2.1 at hi
    change ij.2 < s.2.2.1 at hj
    change s.1.2.2 ⟨ij.1, hi⟩ ≤ s.2.2.2 ⟨ij.2, hj⟩ at hp
    have hc : candidate (fun x : ClearingInput ↦ tuplePriceEval ij.1 x.1.2)
        (fun x ↦ tuplePriceEval ij.2 x.2.2)
        (fun x ↦ tupleQuantityEval ij.1 x.1.1)
        (fun x ↦ tupleQuantityEval ij.2 x.2.1) s =
        clearedQuantityAt s.1.1 s.2.1 ij := by
      simp only [candidate, tuplePriceEval, dif_pos hi, dif_pos hj, clearedQuantityAt]
      exact if_pos hp
    rw [← hc]
    exact Finset.le_sup (f := fun ij : Fin n × Fin m ↦
      candidate (fun x : ClearingInput ↦ tuplePriceEval ij.1.val x.1.2)
        (fun x ↦ tuplePriceEval ij.2.val x.2.2)
        (fun x ↦ tupleQuantityEval ij.1.val x.1.1)
        (fun x ↦ tupleQuantityEval ij.2.val x.2.1) s)
      (Finset.mem_univ (⟨ij.1, hi'⟩, ⟨ij.2, hj'⟩))
  · apply Finset.sup_le
    intro ij _
    have hi : ij.1.val < s.1.2.length := hn.symm ▸ ij.1.isLt
    have hj : ij.2.val < s.2.2.length := hm.symm ▸ ij.2.isLt
    change ij.1.val < s.1.2.1 at hi
    change ij.2.val < s.2.2.1 at hj
    dsimp only [candidate]
    split_ifs with hp
    · have hmem : (ij.1.val, ij.2.val) ∈ FiniteSets.FiniteSubsets.toFinset
          (feasibleEquilibriumIndexSet s.1.2 s.2.2) := by
        apply (FiniteSets.FiniteSubsets.mem_toFinset _).mpr
        refine (mem_feasibleEquilibriumIndexSet _ _).mpr ⟨hi, hj, ?_⟩
        simpa only [tuplePriceEval, Tuple.entry, dif_pos hi, dif_pos hj] using hp
      exact Finset.le_sup (f := clearedQuantityAt s.1.1 s.2.1) hmem
    · exact zero_le _

theorem upperSemicontinuous_finiteVolume (n m : ℕ) :
    UpperSemicontinuous (finiteVolume n m) := by
  apply upperSemicontinuous_finset_sup
  intro ij _
  apply upperSemicontinuous_candidate
  · exact (continuous_tuplePriceEval _).comp (continuous_fst.snd)
  · exact (continuous_tuplePriceEval _).comp (continuous_snd.snd)
  · exact (continuous_tupleQuantityEval _).comp (continuous_fst.fst)
  · exact (continuous_tupleQuantityEval _).comp (continuous_snd.fst)

theorem continuous_tupleLength : Continuous (fun x : Tuple ℝ ↦ x.length) := by
  rw [continuous_tupleHausdorff_iff_fixedLength]
  intro n
  exact continuous_const

theorem eventually_eq_finiteVolume (s : ClearingInput) :
    equilibriumQuantity =ᶠ[𝓝 s] finiteVolume s.1.2.length s.2.2.length := by
  have hs : ∀ᶠ t : ClearingInput in 𝓝 s, t.1.2.length = s.1.2.length :=
    ((isOpen_discrete {s.1.2.length}).preimage
      (continuous_tupleLength.comp continuous_fst.snd)).mem_nhds (by rfl)
  have hb : ∀ᶠ t : ClearingInput in 𝓝 s, t.2.2.length = s.2.2.length :=
    ((isOpen_discrete {s.2.2.length}).preimage
      (continuous_tupleLength.comp continuous_snd.snd)).mem_nhds (by rfl)
  filter_upwards [hs, hb] with t hts htb
  exact equilibrium_eq_finiteVolume t hts htb

/-- Original label: `prop:executable-volume-usc`, the thesis `g_k`.
For a fixed limit point `s = ((Q, p), (Q', p'))`, the maximum of
`min(Q_t(i), Q'_t(j))` over the limit's feasible index set `I(p, p')`,
evaluated at a variable point `t`; along a sequence `z_k → s` this is the
thesis `g_k = fixedIndexVolume s (z k)` (with the value `0` when
`I(p, p') = ∅`). -/
def fixedIndexVolume (s t : ClearingInput) : Quantity :=
  maxClearedQuantityForIndexSet (feasibleEquilibriumIndexSet s.1.2 s.2.2) t.1.1 t.2.1

@[simp] theorem fixedIndexVolume_self (s : ClearingInput) :
    fixedIndexVolume s s = equilibriumQuantity s := rfl

/-- Thesis step: "the maximum and minimum over a fixed finite index set are
continuous", so `g_k → Q(z)`. -/
theorem continuous_fixedIndexVolume (s : ClearingInput) : Continuous (fixedIndexVolume s) := by
  classical
  apply Continuous.finset_sup_apply
  intro ij _
  exact ((continuous_tupleQuantityEval ij.1).comp continuous_fst.fst).min
    ((continuous_tupleQuantityEval ij.2).comp continuous_snd.fst)

/-- Thesis step: once the lengths have stabilized, every pair `(i, j)` that is
infeasible at the limit (`p(i) > p'(j)`) stays infeasible nearby, and since
there are finitely many pairs, `I(p_k, p'_k) ⊆ I(p, p')` for all large `k`.
The eventual filter is the thesis' common threshold `K`. -/
theorem eventually_feasible_subset (s : ClearingInput) :
    ∀ᶠ t in 𝓝 s, (feasibleEquilibriumIndexSet t.1.2 t.2.2 : Set (ℕ × ℕ)) ⊆
      (feasibleEquilibriumIndexSet s.1.2 s.2.2 : Set (ℕ × ℕ)) := by
  classical
  have hs : ∀ᶠ t : ClearingInput in 𝓝 s, t.1.2.length = s.1.2.length :=
    ((isOpen_discrete {s.1.2.length}).preimage
      (continuous_tupleLength.comp continuous_fst.snd)).mem_nhds (by rfl)
  have hb : ∀ᶠ t : ClearingInput in 𝓝 s, t.2.2.length = s.2.2.length :=
    ((isOpen_discrete {s.2.2.length}).preimage
      (continuous_tupleLength.comp continuous_snd.snd)).mem_nhds (by rfl)
  have hp : ∀ᶠ t : ClearingInput in 𝓝 s, ∀ i : Fin s.1.2.length,
      ∀ j : Fin s.2.2.length,
      tuplePriceEval i s.1.2 > tuplePriceEval j s.2.2 →
        tuplePriceEval i t.1.2 > tuplePriceEval j t.2.2 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases h : tuplePriceEval i s.1.2 > tuplePriceEval j s.2.2
    · have he := (isOpen_lt
        ((continuous_tuplePriceEval j).comp continuous_snd.snd)
        ((continuous_tuplePriceEval i).comp continuous_fst.snd)).mem_nhds h
      exact Filter.Eventually.mono he fun _ ht _ => ht
    · exact Eventually.of_forall fun _ ht => (h ht).elim
  filter_upwards [hs, hb, hp] with t hts htb hprices
  intro ij hij
  obtain ⟨hi, hj, hprice⟩ := (mem_feasibleEquilibriumIndexSet _ _).mp hij
  have hi' : ij.1 < s.1.2.length := hts ▸ hi
  have hj' : ij.2 < s.2.2.length := htb ▸ hj
  apply (mem_feasibleEquilibriumIndexSet _ _).mpr
  refine ⟨hi', hj', ?_⟩
  by_contra hn
  change ij.1 < s.1.2.1 at hi'
  change ij.2 < s.2.2.1 at hj'
  change ij.1 < t.1.2.1 at hi
  change ij.2 < t.2.2.1 at hj
  have hgt : tuplePriceEval ij.1 s.1.2 > tuplePriceEval ij.2 s.2.2 := by
    simpa only [tuplePriceEval, Tuple.entry, dif_pos hi', dif_pos hj'] using lt_of_not_ge hn
  have ht := hprices ⟨ij.1, hi'⟩ ⟨ij.2, hj'⟩ hgt
  have hle : tuplePriceEval ij.1 t.1.2 ≤ tuplePriceEval ij.2 t.2.2 := by
    simpa only [tuplePriceEval, Tuple.entry, dif_pos hi, dif_pos hj] using hprice
  exact (not_lt_of_ge hle) ht

/-- Thesis step: "since all cumulative quantities are non-negative, the
inclusion `I(p_k, p'_k) ⊆ I(p, p')` implies `Q(z_k) ≤ g_k`" (including the
case `I(p, p') = ∅`, where both sides are `0`). -/
theorem eventually_le_fixedIndexVolume (s : ClearingInput) :
    ∀ᶠ t in 𝓝 s, equilibriumQuantity t ≤ fixedIndexVolume s t := by
  classical
  filter_upwards [eventually_feasible_subset s] with t hsub
  apply Finset.sup_le
  intro ij hij
  apply Finset.le_sup
  exact (FiniteSets.FiniteSubsets.mem_toFinset _).mpr
    (hsub ((FiniteSets.FiniteSubsets.mem_toFinset _).mp hij))

/-- Original label: `prop:executable-volume-usc`, the displayed inequality of
the proof of (i): for every sequence `z_k → z`,
`limsup_k Q(z_k) ≤ lim_k g_k = Q(z)`. -/
theorem sequence_limsup_le {z : ℕ → ClearingInput} {s : ClearingInput}
    (hz : Tendsto z atTop (𝓝 s)) :
    limsup (fun k => equilibriumQuantity (z k)) atTop ≤ equilibriumQuantity s := by
  have hg : Tendsto (fun k => fixedIndexVolume s (z k)) atTop
      (𝓝 (equilibriumQuantity s)) := by
    simpa only [fixedIndexVolume_self] using (continuous_fixedIndexVolume s).tendsto s |>.comp hz
  have hdom : (fun k => equilibriumQuantity (z k)) ≤ᶠ[atTop]
      fun k => fixedIndexVolume s (z k) := hz.eventually (eventually_le_fixedIndexVolume s)
  calc
    _ ≤ limsup (fun k => fixedIndexVolume s (z k)) atTop :=
      limsup_le_limsup hdom (by isBoundedDefault) hg.isBoundedUnder_le
    _ = equilibriumQuantity s := hg.limsup_eq

/-- Original label: `prop:executable-volume-usc`.
Clause (i), by the thesis argument: near the limit point `s` the lengths
stabilize and the infeasible pairs stay infeasible, so the feasible index set
is contained in that of `s` (`eventually_feasible_subset`); nonnegativity of
the cumulative quantities then dominates `Q` by the fixed-index maximum `g`
(`eventually_le_fixedIndexVolume`), and `g` is continuous with `g(s) = Q(s)`
(`continuous_fixedIndexVolume`). This is the neighbourhood form of
`limsup Q(z_k) ≤ lim g_k = Q(z)`; the literal sequential inequality is
`sequence_limsup_le`. The closed-superlevel-set facts for the fixed layers
above are not used here. Restricting to the thesis' sorted matching-length
subspace preserves upper semicontinuity. -/
theorem upperSemicontinuous_equilibriumQuantity : UpperSemicontinuous equilibriumQuantity := by
  intro s r hr
  have hg : ∀ᶠ t in 𝓝 s, fixedIndexVolume s t < r :=
    (continuous_fixedIndexVolume s).continuousAt.eventually
      (gt_mem_nhds (show fixedIndexVolume s s < r by simpa using hr))
  filter_upwards [eventually_le_fixedIndexVolume s, hg] with t hle hlt
  exact hle.trans_lt hlt

theorem continuousAt_equilibriumQuantity (s : ClearingInput)
    (h : ∀ (i : Fin s.1.2.length) (j : Fin s.2.2.length),
      s.1.2.2 i ≠ s.2.2.2 j) : ContinuousAt equilibriumQuantity s := by
  have hc : ContinuousAt (finiteVolume s.1.2.length s.2.2.length) s := by
    apply ContinuousAt.finset_sup_apply
    intro ij _
    apply continuousAt_candidate
    · exact (continuous_tuplePriceEval _).comp continuous_fst.snd
    · exact (continuous_tuplePriceEval _).comp continuous_snd.snd
    · exact (continuous_tupleQuantityEval _).comp continuous_fst.fst
    · exact (continuous_tupleQuantityEval _).comp continuous_snd.fst
    · have hi : ij.1.val < s.1.2.1 := ij.1.isLt
      have hj : ij.2.val < s.2.2.1 := ij.2.isLt
      simpa only [tuplePriceEval, dif_pos hi, dif_pos hj] using h ij.1 ij.2
  exact hc.congr_of_eventuallyEq (eventually_eq_finiteVolume s)

def singletonState (p : ℝ) : ClearingInput :=
  ((⟨1, fun _ ↦ 1⟩, ⟨1, fun _ ↦ p⟩), (⟨1, fun _ ↦ 1⟩, ⟨1, fun _ ↦ 0⟩))

theorem continuous_singletonState : Continuous singletonState := by
  have hp : Continuous (fun p : ℝ ↦ (⟨1, fun _ : Fin 1 ↦ p⟩ : Tuple ℝ)) :=
    (continuous_sigmaMk_tupleHausdorff 1).comp (continuous_pi fun _ ↦ continuous_id)
  exact (continuous_const.prodMk hp).prodMk continuous_const

theorem equilibrium_singletonState (p : ℝ) :
    equilibriumQuantity (singletonState p) = if p ≤ 0 then 1 else 0 := by
  rw [equilibrium_eq_finiteVolume (singletonState p) (n := 1) (m := 1) rfl rfl]
  have he : (Finset.univ : Finset (Fin 1 × Fin 1)).sup
      (fun _ ↦ if p ≤ 0 then (1 : Quantity) else 0) = if p ≤ 0 then 1 else 0 :=
    Finset.sup_const Finset.univ_nonempty _
  simpa [finiteVolume, candidate, singletonState, tuplePriceEval, tupleQuantityEval,
    Tuple.length, Tuple.entry] using he

/-- Original label: `prop:executable-volume-usc`.
The actual one-sell/one-buy example has quantity one at a tied price and zero
along positive sell-price perturbations converging to the tie. -/
theorem not_continuousAt_equilibriumQuantity_singleton :
    ¬ ContinuousAt equilibriumQuantity (singletonState 0) := by
  intro hc
  have hlim : Tendsto (fun n : ℕ ↦ equilibriumQuantity (singletonState (1 / (n + 1))))
      atTop (𝓝 (1 : Quantity)) := by
    have ht := (hc.comp continuous_singletonState.continuousAt).tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Function.comp_def, equilibrium_singletonState, le_refl, if_true] using ht
  have he : (fun n : ℕ ↦ equilibriumQuantity (singletonState (1 / (n + 1)))) =
      fun _ ↦ (0 : Quantity) := by
    funext n
    rw [equilibrium_singletonState]
    exact if_neg (not_le_of_gt (by positivity))
  rw [he] at hlim
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- Original label: `prop:executable-volume-usc`, clause (iii), the point of
the thesis as an element of the sorted matching-length domain
`\mathfrak{C}(\leq) \times \mathfrak{C}(\geq)` of
`thm:equilibrium-quantity-measurable`: one sell order of cumulative quantity
`1` at price `p` and one buy order of cumulative quantity `1` at price `0`.
Length-one tuples are trivially sorted. -/
def singletonCumulativeState (p : ℝ) :
    Alignment.CumulativeClearingStates IsIncreasingRealTuple ×
      Alignment.CumulativeClearingStates IsDecreasingRealTuple :=
  (⟨(singletonState p).1, by
      refine ⟨?_, ?_, rfl⟩ <;> intro i j _ <;> exact lt_irrefl _⟩,
    ⟨(singletonState p).2, by
      refine ⟨?_, ?_, rfl⟩ <;> intro i j _ <;> exact lt_irrefl _⟩)

theorem continuous_singletonCumulativeState : Continuous singletonCumulativeState :=
  ((continuous_fst.comp continuous_singletonState).subtype_mk
      (fun p => (singletonCumulativeState p).1.2)).prodMk
    ((continuous_snd.comp continuous_singletonState).subtype_mk
      (fun p => (singletonCumulativeState p).2.2))

/-- Original label: `prop:executable-volume-usc`, clause (iii) on the thesis
domain `\mathfrak{C}(\leq) \times \mathfrak{C}(\geq)`.
The thesis witnesses `z_k = ((Q, p_k), (Q', p'))` with `p_k(1) = 1/k` lie in
the sorted matching-length subspace, so the discontinuity at
`((Q, p), (Q', p'))` with `Q(1) = Q'(1) = 1`, `p(1) = p'(1) = 0` holds for the
restriction of `\mathscr{Q}` to that subspace (with the subspace topology),
not only on the ambient tuple space. -/
theorem not_continuousAt_equilibriumQuantity_singleton_cumulativeDomain :
    ¬ ContinuousAt
      (fun s : Alignment.CumulativeClearingStates IsIncreasingRealTuple ×
          Alignment.CumulativeClearingStates IsDecreasingRealTuple =>
        equilibriumQuantity (s.1.val, s.2.val))
      (singletonCumulativeState 0) := by
  intro hc
  have hpath : ContinuousAt (fun p : ℝ ↦ equilibriumQuantity (singletonState p)) 0 :=
    hc.comp continuous_singletonCumulativeState.continuousAt
  have hlim : Tendsto (fun n : ℕ ↦ equilibriumQuantity (singletonState (1 / (n + 1))))
      atTop (𝓝 (1 : Quantity)) := by
    have ht := hpath.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Function.comp_def, equilibrium_singletonState, le_refl, if_true] using ht
  have he : (fun n : ℕ ↦ equilibriumQuantity (singletonState (1 / (n + 1)))) =
      fun _ ↦ (0 : Quantity) := by
    funext n
    rw [equilibrium_singletonState]
    exact if_neg (not_le_of_gt (by positivity))
  rw [he] at hlim
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hlim)

end Thesis.Foundations.MarketClearing.DoctoralSemicontinuity
