import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedMarket
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Order.Lattice

/-! # Literal vendor cumulative-list preprocessing

Each side is a finite list of price/cumulative-volume points. Sorting uses
signed price and increasing volume within a price; cumulative entries are
replaced by running maxima and then differenced into individual volumes.
The resulting Book is the actual interpolated book, including zero-volume
cells. Sorting measurability uses the source finite sorting-cell cover and
continuous coordinate-permutation formulas on those cells.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLParser

open Set MeasureTheory
open Foundations.MarketRepresentation TuplesBasic TuplesSorting TuplesMeasurableSorting
open scoped BigOperators NNReal

abbrev Point := ℝ × ℝ≥0
abbrev RawSide (n : ℕ) := Fin n → Point
abbrev RawLayer (ns nb : ℕ) := RawSide (ns + 1) × RawSide (nb + 1)

def signedPrice (buy : Bool) (p : Point) : ℝ := if buy then -p.1 else p.1

def key (buy : Bool) (p : Point) : Lex (ℝ × ℝ≥0) := toLex (signedPrice buy p, p.2)

def keyTuple {n : ℕ} (buy : Bool) (x : RawSide n) : Tuple (Lex (ℝ × ℝ≥0)) :=
  ⟨n, fun i => key buy (x i)⟩

def sortPermutation {n : ℕ} (buy : Bool) (x : RawSide n) : Equiv.Perm (Fin n) :=
  minimumSortPermutation (keyTuple buy x)

def sorted {n : ℕ} (buy : Bool) (x : RawSide n) (i : Fin n) : Point :=
  x (sortPermutation buy x i)

theorem sorted_key_monotone {n : ℕ} (buy : Bool) (x : RawSide n) :
    Monotone (fun i => key buy (sorted buy x i)) := by
  have h := minimumSort_isSorted (keyTuple buy x)
  rw [minimumSort_eq_permute_minimumSortPermutation, isSorted_iff_monotone] at h
  exact h

theorem key_injective (buy : Bool) : Function.Injective (key buy) := by
  intro x y h
  have hp := congrArg (fun z => (ofLex z).1) h
  have hv := congrArg (fun z => (ofLex z).2) h
  apply Prod.ext
  · cases buy <;> simpa only [key, signedPrice, Bool.false_eq_true, ↓reduceIte,
      ofLex_toLex, neg_inj] using hp
  · exact hv

def sortCell {n : ℕ} (buy : Bool) (σ : Equiv.Perm (Fin n)) : Set (RawSide n) :=
  {x | Monotone (fun i => key buy (x (σ i)))}

/-- A fixed cell has the coordinate-permutation formula used in the source. -/
theorem sorted_eq_on_cell {n : ℕ} (buy : Bool) (σ : Equiv.Perm (Fin n))
    {x : RawSide n} (hx : x ∈ sortCell buy σ) : sorted buy x = fun i => x (σ i) := by
  change Monotone (fun i => key buy (x (σ i))) at hx
  have hmin := sorted_key_monotone buy x
  have hperm := (list_ofFn_perm_comp_equiv (fun i => key buy (x i))
    (sortPermutation buy x)).trans
      (list_ofFn_perm_comp_equiv (fun i => key buy (x i)) σ).symm
  have hlist := List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => le_antisymm hab hba)
    (List.pairwise_ofFn.mpr (fun _ _ hij => hmin hij.le))
    (List.pairwise_ofFn.mpr (fun _ _ hij => hx hij.le)) hperm
  have hkeys := List.ofFn_inj.mp hlist
  funext i
  exact key_injective buy (congrFun hkeys i)

theorem sortCell_cover {n : ℕ} (buy : Bool) :
    (⋃ σ : Equiv.Perm (Fin n), sortCell buy σ) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨sortPermutation buy x, sorted_key_monotone buy x⟩

theorem measurableSet_sortCell {n : ℕ} (buy : Bool) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (sortCell buy σ) := by
  change MeasurableSet {x : RawSide n | ∀ i j, i ≤ j → key buy (x (σ i)) ≤ key buy (x (σ j))}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hij
  simp only [key, Prod.Lex.toLex_le_toLex, setOf_or, setOf_and]
  have hpi : Measurable (fun x : RawSide n => signedPrice buy (x (σ i))) := by
    cases buy <;> simp only [signedPrice, Bool.false_eq_true, ↓reduceIte]
    · exact (measurable_pi_apply _).fst
    · exact (measurable_pi_apply _).fst.neg
  have hpj : Measurable (fun x : RawSide n => signedPrice buy (x (σ j))) := by
    cases buy <;> simp only [signedPrice, Bool.false_eq_true, ↓reduceIte]
    · exact (measurable_pi_apply _).fst
    · exact (measurable_pi_apply _).fst.neg
  exact (measurableSet_lt hpi hpj).union
    ((measurableSet_eq_fun hpi hpj).inter
      (measurableSet_le (measurable_pi_apply (σ i)).snd (measurable_pi_apply (σ j)).snd))
/-- Actual sorted point arrays are Borel by finite sorting-cell pasting. -/
theorem measurable_sorted {n : ℕ} (buy : Bool) : Measurable (sorted (n := n) buy) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_of_measurable_restrict_countable_cover
    (S := fun σ : Equiv.Perm (Fin n) => sortCell buy σ)
    (measurableSet_sortCell buy) (sortCell_cover buy)
  intro σ
  have heq : (fun x : sortCell buy σ => sorted buy x.val i) =
      (fun x : sortCell buy σ => x.val (σ i)) := by
    funext x
    exact congrFun (sorted_eq_on_cell buy σ x.property) i
  rw [heq]
  exact (measurable_pi_apply _).comp measurable_subtype_coe

def runningMax {n : ℕ} (v : Fin n → ℝ≥0) (i : Fin (n + 1)) : ℝ≥0 :=
  (Finset.univ.filter fun j : Fin n => j.val < i.val).sup v

theorem runningMax_zero {n : ℕ} (v : Fin n → ℝ≥0) : runningMax v 0 = 0 := by
  simp [runningMax]

theorem runningMax_monotone {n : ℕ} (v : Fin n → ℝ≥0) : Monotone (runningMax v) := by
  intro i j hij
  apply Finset.sup_mono
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact hk.trans_le hij

def cumulative {n : ℕ} (buy : Bool) (x : RawSide n) (i : Fin (n + 1)) : ℝ :=
  runningMax (fun j => (sorted buy x j).2) i

def incrementalVolume {n : ℕ} (buy : Bool) (x : RawSide n) (i : Fin n) : ℝ :=
  cumulative buy x i.succ - cumulative buy x i.castSucc

theorem incrementalVolume_nonneg {n : ℕ} (buy : Bool) (x : RawSide n) (i : Fin n) :
    0 ≤ incrementalVolume buy x i := by
  apply sub_nonneg.mpr
  have h := runningMax_monotone (fun j => (sorted buy x j).2)
    (Fin.castSucc_le_succ i)
  exact_mod_cast h

/-- Differencing and then accumulating recovers the source running maxima. -/
theorem cumulative_incremental_eq {n : ℕ} (buy : Bool) (x : RawSide n) :
    InterpolatedSide.cumulative (incrementalVolume buy x) = cumulative buy x := by
  funext i
  induction i using Fin.induction with
  | zero => simp [InterpolatedSide.cumulative_zero, cumulative, runningMax_zero]
  | succ i hi =>
    have h := InterpolatedSide.cumulative_increment (incrementalVolume buy x) i
    rw [hi] at h
    have hr : incrementalVolume buy x i =
        cumulative buy x i.succ - cumulative buy x i.castSucc := rfl
    rw [hr] at h
    linarith

def priceBounded {ns nb : ℕ} (lo hi : ℝ) (x : RawLayer ns nb) : Prop :=
  (∀ i, (x.1 i).1 ∈ Icc lo hi) ∧ (∀ j, (x.2 j).1 ∈ Icc lo hi)

def parsedBook {ns nb : ℕ} (lo hi : ℝ) (hlohi : lo ≤ hi)
    (x : RawLayer ns nb) (hx : priceBounded lo hi x) : ExcessSupply.Book lo hi where
  sellCount := ns + 1
  buyCount := nb + 1
  sellPrice := Fin.cases lo (fun i => (sorted false x.1 i).1)
  buyPrice := Fin.cases hi (fun i => (sorted true x.2 i).1)
  sellVolume := incrementalVolume false x.1
  buyVolume := incrementalVolume true x.2
  sellVolume_nonneg := incrementalVolume_nonneg false x.1
  buyVolume_nonneg := incrementalVolume_nonneg true x.2
  sellPrice_zero := rfl
  buyPrice_zero := rfl
  sellPrice_monotone := InterpolatedMarket.prepend_monotone _ (by
    intro i j hij
    exact (Prod.Lex.toLex_le_toLex'.mp (sorted_key_monotone false x.1 hij)).1) lo
      (fun i => (hx.1 _).1)
  buyPrice_antitone := InterpolatedMarket.prepend_antitone _ (by
    intro i j hij
    have h := (Prod.Lex.toLex_le_toLex'.mp (sorted_key_monotone true x.2 hij)).1
    simpa only [key, signedPrice, ↓reduceIte, neg_le_neg_iff] using h) hi
      (fun i => (hx.2 _).2)
  sellPrice_bounds := Fin.cases ⟨le_rfl, hlohi⟩ (fun i => hx.1 _)
  buyPrice_bounds := Fin.cases ⟨hlohi, le_rfl⟩ (fun i => hx.2 _)

theorem parsedBook_sell_cumulative {ns nb : ℕ} (lo hi : ℝ) (hlohi : lo ≤ hi)
    (x : RawLayer ns nb) (hx : priceBounded lo hi x) :
    InterpolatedSide.cumulative (parsedBook lo hi hlohi x hx).sellVolume =
      cumulative false x.1 := cumulative_incremental_eq false x.1

theorem parsedBook_buy_cumulative {ns nb : ℕ} (lo hi : ℝ) (hlohi : lo ≤ hi)
    (x : RawLayer ns nb) (hx : priceBounded lo hi x) :
    InterpolatedSide.cumulative (parsedBook lo hi hlohi x hx).buyVolume =
      cumulative true x.2 := cumulative_incremental_eq true x.2

/-- Running maxima are continuous finite maxima before differencing. -/
theorem continuous_runningMax {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun v : Fin n → ℝ≥0 => runningMax v i) := by
  classical
  have hsup (s : Finset (Fin n)) : Continuous (fun v : Fin n → ℝ≥0 => s.sup v) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty] using
        (continuous_const : Continuous (fun _ : Fin n → ℝ≥0 => (0 : ℝ≥0)))
    | @insert a s ha ih =>
      simpa only [Finset.sup_insert] using (continuous_apply a).sup ih
  exact hsup _

theorem measurable_cumulative {n : ℕ} (buy : Bool) :
    Measurable (cumulative (n := n) buy) := by
  have hv : Measurable (fun x : RawSide n => fun j => (sorted buy x j).2) :=
    measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp (measurable_sorted buy)).snd
  apply measurable_pi_lambda
  intro i
  exact NNReal.continuous_coe.measurable.comp
    ((continuous_runningMax i).measurable.comp hv)

theorem measurable_incrementalVolume {n : ℕ} (buy : Bool) :
    Measurable (incrementalVolume (n := n) buy) := by
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i.succ).comp (measurable_cumulative buy)).sub
    ((measurable_pi_apply i.castSucc).comp (measurable_cumulative buy))

/-- On a sorting cell the literal sorted vector is a continuous permutation. -/
theorem continuous_sorted_on_cell {n : ℕ} (buy : Bool) (σ : Equiv.Perm (Fin n)) :
    Continuous (fun x : sortCell buy σ => sorted buy x.val) := by
  have hfun : (fun x : sortCell buy σ => sorted buy x.val) =
      (fun x : sortCell buy σ => fun i => x.val (σ i)) := by
    funext x
    exact sorted_eq_on_cell buy σ x.property
  rw [hfun]
  exact continuous_pi fun i => (continuous_apply (σ i)).comp continuous_subtype_val

/-- Running maxima remain continuous on each source sorting cell. -/
theorem continuous_cumulative_on_cell {n : ℕ} (buy : Bool) (σ : Equiv.Perm (Fin n)) :
    Continuous (fun x : sortCell buy σ => cumulative buy x.val) := by
  apply continuous_pi
  intro i
  apply NNReal.continuous_coe.comp
  exact (continuous_runningMax i).comp (continuous_pi fun j =>
    continuous_snd.comp ((continuous_apply j).comp (continuous_sorted_on_cell buy σ)))

abbrev BoundedLayer (lo hi : ℝ) (ns nb : ℕ) :=
  {x : RawLayer ns nb // priceBounded lo hi x}

theorem measurable_parsed_sellPrice {lo hi : ℝ} (hlohi : lo ≤ hi) (ns nb : ℕ)
    (i : Fin (ns + 2)) :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      (parsedBook lo hi hlohi x.val x.property).sellPrice i) := by
  refine Fin.cases measurable_const (fun j => ?_) i
  exact (((measurable_pi_apply j).comp (measurable_sorted false)).fst.comp
    (measurable_fst.comp measurable_subtype_coe))

theorem measurable_parsed_buyPrice {lo hi : ℝ} (hlohi : lo ≤ hi) (ns nb : ℕ)
    (i : Fin (nb + 2)) :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      (parsedBook lo hi hlohi x.val x.property).buyPrice i) := by
  refine Fin.cases measurable_const (fun j => ?_) i
  exact (((measurable_pi_apply j).comp (measurable_sorted true)).fst.comp
    (measurable_snd.comp measurable_subtype_coe))

theorem measurable_parsed_sellCumulative {lo hi : ℝ} (hlohi : lo ≤ hi) (ns nb : ℕ)
    (i : Fin (ns + 2)) :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      InterpolatedSide.cumulative (parsedBook lo hi hlohi x.val x.property).sellVolume i) := by
  simp only [parsedBook_sell_cumulative]
  exact ((measurable_pi_apply i).comp (measurable_cumulative false)).comp
    (measurable_fst.comp measurable_subtype_coe)

theorem measurable_parsed_buyCumulative {lo hi : ℝ} (hlohi : lo ≤ hi) (ns nb : ℕ)
    (i : Fin (nb + 2)) :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      InterpolatedSide.cumulative (parsedBook lo hi hlohi x.val x.property).buyVolume i) := by
  simp only [parsedBook_buy_cumulative]
  exact ((measurable_pi_apply i).comp (measurable_cumulative true)).comp
    (measurable_snd.comp measurable_subtype_coe)

end Thesis.DayAhead.VendorPLParser
