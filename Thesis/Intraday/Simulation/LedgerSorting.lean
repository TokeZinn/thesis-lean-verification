import Thesis.Intraday.Simulation.TypedReplay
import Mathlib.Data.List.OfFn

/-! # Carry lifecycle metadata through the thesis's actual sorting permutation

The minimum sorting permutation is computed on the existing tagged market and
then applied to the entire ledger entry. Identifiers are never recovered by
matching price/quantity/time values, which could coincide for distinct orders.
-/

noncomputable section
namespace Thesis.Intraday.LedgerSorting

open LiveLedger LedgerTupleActions InstructionConservation Clearing
open Foundations.MarketRepresentation Foundations.MarketRepresentation.TuplesBasic
open Foundations.MarketRepresentation.TuplesSorting

attribute [local instance] Clearing.marketPriceTimeOrder

def selectEntries (s : Ledger) {n : ℕ} (j : Fin n → Fin s.live.length) : Ledger :=
  ⟨s.nextId, List.ofFn (fun i => s.live.get (j i))⟩

theorem selectEntries_mem (s : Ledger) {n : ℕ} (j : Fin n → Fin s.live.length) {a : Entry}
    (ha : a ∈ (selectEntries s j).live) : a ∈ s.live := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact List.get_mem _ _

theorem key_index_injective {s : Ledger} (hs : Valid s) :
    Function.Injective (fun i : Fin s.live.length => (s.live.get i).localKey) := by
  intro i j hij
  apply (List.nodup_iff_injective_get.mp (ledger_nodup hs))
  exact unique_of_pairwise Entry.localKey hs.1 (List.get_mem _ _) (List.get_mem _ _) hij

theorem id_index_injective {s : Ledger} (hs : Valid s) :
    Function.Injective (fun i : Fin s.live.length => (s.live.get i).liveId) := by
  intro i j hij
  apply (List.nodup_iff_injective_get.mp (ledger_nodup hs))
  exact unique_of_pairwise Entry.liveId hs.2.1 (List.get_mem _ _) (List.get_mem _ _) hij

theorem selectEntries_valid {s : Ledger} (hs : Valid s) {n : ℕ}
    (j : Fin n → Fin s.live.length) (hj : Function.Injective j) : Valid (selectEntries s j) := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_ofFn.mpr
    intro a b hab he
    exact (ne_of_lt hab) (hj (key_index_injective hs he))
  · apply List.pairwise_ofFn.mpr
    intro a b hab he
    exact (ne_of_lt hab) (hj (id_index_injective hs he))
  · intro a ha
    exact hs.2.2 a (selectEntries_mem s j ha)

theorem selectEntries_market (s : Ledger) {n : ℕ} (j : Fin n → Fin s.live.length) :
    market (selectEntries s j) = ⟨n, fun i => (market s).2 (j i)⟩ := by
  apply tupleList_injective
  rw [tupleList_market]
  simp [selectEntries, Foundations.MarketActions.Primitive.tupleList,
    Tuple.entry, List.map_ofFn, Function.comp_def, tagged, market]

theorem selectEntries_lookup_preserved {s : Ledger} (hs : Valid s) {n : ℕ}
    (j : Fin n → Fin s.live.length) (hj : Function.Injective j) {a : Entry}
    (ha : a ∈ (selectEntries s j).live) :
    lookup (selectEntries s j) a.localKey = some a ∧ lookup s a.localKey = some a :=
  ⟨lookup_of_mem (selectEntries_valid hs j hj) ha,
    lookup_of_mem hs (selectEntries_mem s j ha)⟩

def sortingPermutation (s : Ledger) : Equiv.Perm (Fin s.live.length) :=
  minimumSortPermutation (market s)

def sortLedger (s : Ledger) : Ledger := selectEntries s (sortingPermutation s)

theorem sortLedger_valid {s : Ledger} (hs : Valid s) : Valid (sortLedger s) :=
  selectEntries_valid hs _ (sortingPermutation s).injective

theorem sortLedger_market (s : Ledger) :
    market (sortLedger s) = MarketSorting.sortMarket (market s) := by
  rw [sortLedger, selectEntries_market]
  exact (minimumSort_eq_permute_minimumSortPermutation (market s)).symm

theorem sortLedger_sorted (s : Ledger) : SortedMarket (market (sortLedger s)) := by
  rw [sortLedger_market]
  exact MarketSorting.sortMarket_sorted _

theorem sortLedger_perm (s : Ledger) : (sortLedger s).live.Perm s.live := by
  have h := (sortingPermutation s).ofFn_comp_perm s.live.get
  simpa [sortLedger, selectEntries, Function.comp_def] using h

theorem sortLedger_lookup {s : Ledger} (hs : Valid s) (key : ℕ) :
    lookup (sortLedger s) key = lookup s key := by
  cases h : lookup s key with
  | none =>
    apply (lookup_none_iff _ _).mpr
    intro a ha
    exact (lookup_none_iff _ _).mp h a ((sortLedger_perm s).mem_iff.mp ha)
  | some a =>
    rw [← lookup_some_key h]
    apply lookup_of_mem (sortLedger_valid hs)
    exact (sortLedger_perm s).mem_iff.mpr (lookup_some_mem h)

@[simp] theorem sortLedger_counter (s : Ledger) : (sortLedger s).nextId = s.nextId := rfl

end Thesis.Intraday.LedgerSorting
