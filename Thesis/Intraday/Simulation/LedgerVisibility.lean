import Thesis.Intraday.Simulation.LedgerSorting

/-! # Visible-book projection retaining lifecycle identifiers

The same original index that supplies each retained order supplies its full
ledger entry. This is the chapter's top-k projection on metadata-bearing books;
hidden entries do not remain in this projected ledger. It is not the current
simulator's arrival-admitted visible and waiting queues, which are specified
separately in `AnalogueReplay`.
-/

noncomputable section
namespace Thesis.Intraday.LedgerVisibility

open LiveLedger LedgerSorting LedgerTupleActions InstructionConservation
open Execution Clearing Visibility
open Foundations.MarketRepresentation Foundations.MarketRepresentation.TuplesBasic
open Foundations.MarketRepresentation.FiniteSets
open Foundations.MarketActions.Primitive Foundations.MarketClearing.Selection

theorem sideIndex_injective (buy : Bool) (m : Market) : Function.Injective (sideIndex buy m) := by
  intro i j h
  have hv := congrArg Fin.val h
  exact (FiniteSubsets.toFinset (separationIndexSet buy m)).orderEmbOfFin rfl |>.injective hv

theorem sideIndex_tag (buy : Bool) (m : Market) (i : Fin (side buy m).1) :
    (m.2 (sideIndex buy m i)).1 = buy := (congrArg Sigma.fst (side_entry buy m i)).symm

def visibleIndex (k : ℕ) (m : Market) : Fin (visible k m).1 → Fin m.1 :=
  fun i => Fin.addCases
    (fun j : Fin (min k (side true m).1) =>
      sideIndex true m ⟨j.val, lt_of_lt_of_le j.isLt (min_le_right _ _)⟩)
    (fun j : Fin (min k (side false m).1) =>
      sideIndex false m ⟨j.val, lt_of_lt_of_le j.isLt (min_le_right _ _)⟩) i

theorem visibleIndex_injective (k : ℕ) (m : Market) : Function.Injective (visibleIndex k m) := by
  intro i j
  refine Fin.addCases ?_ ?_ i <;> intro a
  · refine Fin.addCases ?_ ?_ j <;> intro b h
    · simp only [visibleIndex, Fin.addCases_left] at h
      have hv := congrArg Fin.val ((sideIndex_injective true m) h)
      exact Fin.ext hv
    · simp only [visibleIndex, Fin.addCases_left, Fin.addCases_right] at h
      have ht := congrArg (fun t => (m.2 t).1) h
      simp only [sideIndex_tag] at ht
      cases ht
  · refine Fin.addCases ?_ ?_ j <;> intro b h
    · simp only [visibleIndex, Fin.addCases_left, Fin.addCases_right] at h
      have ht := congrArg (fun t => (m.2 t).1) h
      simp only [sideIndex_tag] at ht
      cases ht
    · simp only [visibleIndex, Fin.addCases_right] at h
      have hv := congrArg Fin.val ((sideIndex_injective false m) h)
      apply Fin.ext
      change min k (side true m).1 + a.val = min k (side true m).1 + b.val
      exact congrArg (min k (side true m).1 + ·) hv

theorem visibleIndex_entry (k : ℕ) (m : Market) (i : Fin (visible k m).1) :
    (visible k m).2 i = m.2 (visibleIndex k m i) := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [visible, joinMarket, concat, retag, Tuple.map, Tuple.entry, Tuple.length,
      Fin.append_left, take, visibleIndex, Fin.addCases_left] using
      side_entry true m ⟨j.val, lt_of_lt_of_le j.isLt (min_le_right _ _)⟩
  · intro j
    simpa only [visible, joinMarket, concat, retag, Tuple.map, Tuple.entry, Tuple.length,
      Fin.append_right, take, visibleIndex, Fin.addCases_right] using
      side_entry false m ⟨j.val, lt_of_lt_of_le j.isLt (min_le_right _ _)⟩

def projectLedger (k : ℕ) (s : Ledger) : Ledger := selectEntries s (visibleIndex k (market s))

theorem projectLedger_valid {s : Ledger} (hs : Valid s) (k : ℕ) : Valid (projectLedger k s) :=
  selectEntries_valid hs _ (visibleIndex_injective k (market s))

theorem projectLedger_market (k : ℕ) (s : Ledger) :
    market (projectLedger k s) = visible k (market s) := by
  rw [projectLedger, selectEntries_market]
  apply congrArg (fun f => (⟨(visible k (market s)).1, f⟩ : Market))
  funext i
  exact (visibleIndex_entry k (market s) i).symm

def refresh (k : ℕ) (s : Ledger) : Ledger := projectLedger k (sortLedger s)

theorem refresh_valid {s : Ledger} (hs : Valid s) (k : ℕ) : Valid (refresh k s) :=
  projectLedger_valid (sortLedger_valid hs) k

theorem refresh_market (k : ℕ) (s : Ledger) :
    market (refresh k s) = visibleMarket k s := by
  rw [refresh, projectLedger_market, sortLedger_market]
  rfl

theorem refresh_sorted (k : ℕ) (s : Ledger) : SortedMarket (market (refresh k s)) := by
  rw [refresh_market]
  exact visibleMarket_sorted k s

theorem refresh_side_count (k : ℕ) (s : Ledger) (buy : Bool) :
    (side buy (market (refresh k s))).1 = min k (side buy (sortedMarket s)).1 := by
  rw [refresh_market]
  exact visible_side_count k buy (sortedMarket s)

theorem refresh_length_bound (k : ℕ) (s : Ledger) : (refresh k s).live.length ≤ 2 * k := by
  change (market (refresh k s)).1 ≤ 2 * k
  rw [refresh_market]
  exact visible_length_bound k (sortedMarket s)

theorem refresh_mem (k : ℕ) (s : Ledger) {a : Entry} (ha : a ∈ (refresh k s).live) : a ∈ s.live :=
  (sortLedger_perm s).mem_iff.mp (selectEntries_mem (sortLedger s) _ ha)

theorem refresh_lookup_preserved {s : Ledger} (hs : Valid s) (k : ℕ) {a : Entry}
    (ha : a ∈ (refresh k s).live) :
    lookup (refresh k s) a.localKey = some a ∧ lookup s a.localKey = some a :=
  ⟨lookup_of_mem (refresh_valid hs k) ha, lookup_of_mem hs (refresh_mem k s ha)⟩

theorem refresh_dropped_missing {s : Ledger} (hs : Valid s) (k : ℕ) {a : Entry}
    (ha : a ∈ s.live) (hdropped : a ∉ (refresh k s).live) :
    lookup (refresh k s) a.localKey = none := by
  apply (lookup_none_iff _ _).mpr
  intro b hb he
  have hsame := unique_of_pairwise Entry.localKey hs.1 (refresh_mem k s hb) ha he
  exact hdropped (hsame ▸ hb)

@[simp] theorem refresh_counter (k : ℕ) (s : Ledger) : (refresh k s).nextId = s.nextId := rfl

end Thesis.Intraday.LedgerVisibility
