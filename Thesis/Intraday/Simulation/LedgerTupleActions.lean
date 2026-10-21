import Thesis.Intraday.Simulation.InstructionConservation
import Thesis.Foundations.MarketActions.Alignment
import Mathlib.Data.List.NodupEquivFin

/-! # Structural tuple actions for the lifecycle ledger

Identifiers are resolved in the input ledger before metadata is forgotten.
The bridge below relates its order-preserving list operations to the thesis's
actual finite-tuple concatenation, cancellation and indexed modification.
-/

noncomputable section
namespace Thesis.Intraday.LedgerTupleActions

open LiveLedger LifecycleResolver Clearing
open Foundations.MarketRepresentation Foundations.MarketRepresentation.TuplesBasic
open Foundations.MarketRepresentation.FiniteSets
open Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
open Foundations.MarketActions.Primitive Foundations.MarketActions.Alignment

def tupleOfList {X : Type*} (l : List X) : Tuple X := ⟨l.length, l.get⟩

theorem tupleList_tupleOfList {X : Type*} (l : List X) : tupleList (tupleOfList l) = l := by
  simp [tupleList, tupleOfList, Tuple.entry]

theorem tupleList_injective {X : Type*} : Function.Injective (tupleList (X := X)) := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  have hlen := congrArg List.length h
  simp only [tupleList_length, Tuple.length] at hlen
  subst m
  have hfun : x = y := List.ofFn_inj.mp h
  subst y
  rfl

theorem tupleOfList_append {X : Type*} (a b : List X) :
    tupleOfList (a ++ b) = concat (tupleOfList a) (tupleOfList b) := by
  apply tupleList_injective
  simp [tupleList_concat, tupleList_tupleOfList]

theorem reindex_eq_of_enumeration {X : Type*} (x : Tuple X) (keep : FiniteSubsets ℕ)
    {n : ℕ} (j : Fin n → Fin x.1) (hj : StrictMono j)
    (hmem : ∀ k : Fin x.1, k.val ∈ (keep : Set ℕ) ↔ ∃ i, j i = k) :
    reindex x keep = ⟨n, fun i => x.2 (j i)⟩ := by
  classical
  let kept := finiteSubsetInter keep (tupleDomain x)
  let s := FiniteSubsets.toFinset kept
  have hs : s = Finset.univ.image (fun i => (j i).val) := by
    ext k
    rw [FiniteSubsets.mem_toFinset, Finset.mem_image]
    constructor
    · rintro ⟨hk, hdom⟩
      have hlt := (mem_tupleDomain x).mp hdom
      obtain ⟨i, hi⟩ := (hmem ⟨k, hlt⟩).mp hk
      exact ⟨i, Finset.mem_univ _, congrArg Fin.val hi⟩
    · rintro ⟨i, _, hi⟩
      subst k
      exact ⟨(hmem (j i)).mpr ⟨i, rfl⟩, (mem_tupleDomain x).mpr (j i).isLt⟩
  have hjval : StrictMono (fun i => (j i).val) := fun _ _ h => hj h
  have hcard : s.card = n := by
    rw [hs, Finset.card_image_of_injective _ hjval.injective, Finset.card_univ, Fintype.card_fin]
  have hmemb (i : Fin n) : (j i).val ∈ s := by
    rw [hs]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  subst n
  have he := Finset.orderEmbOfFin_unique rfl hmemb hjval
  refine Sigma.ext (show (reindex x keep).1 = s.card from rfl) ?_
  apply heq_of_eq
  funext i
  apply congrArg x.2
  apply Fin.ext
  exact (congrFun he i).symm

theorem cancelIdentifiers_filter {X I : Type*} [DecidableEq I]
    (id : X → I) (l : List X) (hl : l.Nodup) (target : I) :
    cancelIdentifiers id {target} (tupleOfList l) =
      tupleOfList (l.filter fun a => id a != target) := by
  classical
  let filtered := l.filter fun a => id a != target
  obtain ⟨j, hj⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
    (show List.Sublist filtered l from List.filter_sublist)
  have hmem (k : Fin l.length) : id (l.get k) ≠ target ↔ ∃ i, j i = k := by
    constructor
    · intro hk
      have hf : l.get k ∈ filtered := List.mem_filter.mpr ⟨List.get_mem _ _, by simpa using hk⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hf
      exact ⟨i, (List.nodup_iff_injective_get.mp hl) ((hj i).symm.trans hi)⟩
    · rintro ⟨i, rfl⟩
      have hi := (List.mem_filter.mp (show filtered.get i ∈ filtered from List.get_mem _ _)).2
      have hip : id (filtered.get i) ≠ target := by simpa using hi
      rw [hj i] at hip
      exact hip
  have he := reindex_eq_of_enumeration (tupleOfList l)
    (finiteSubsetDiff (tupleDomain (tupleOfList l)) (identifierIndices id {target} (tupleOfList l)))
    j j.strictMono (fun k => by
      rw [identifierCancellation_surviving_indices]
      exact hmem k)
  rw [cancelIdentifiers, cancel, he]
  apply congrArg (fun f => (⟨filtered.length, f⟩ : Tuple X))
  funext i
  exact (hj i).symm

theorem ledger_nodup {s : Ledger} (hs : Valid s) : s.live.Nodup :=
  hs.2.1.imp fun h he => h (congrArg Entry.liveId he)

def tagged (a : Entry) : TaggedOrder := ⟨a.isBuy, a.order⟩

theorem market_eq_map (s : Ledger) : market s = Tuple.map tagged (tupleOfList s.live) := rfl

theorem tupleList_market (s : Ledger) : tupleList (market s) = s.live.map tagged := by
  change List.ofFn (tagged ∘ s.live.get) = _
  rw [← List.map_ofFn]
  simp

theorem map_reindex {X Y : Type*} (f : X → Y) (x : Tuple X) (keep : FiniteSubsets ℕ) :
    Tuple.map f (reindex x keep) = reindex (Tuple.map f x) keep := rfl

theorem map_cancel {X Y : Type*} (f : X → Y) (x : Tuple X) (remove : FiniteSubsets ℕ) :
    Tuple.map f (cancel x remove) = cancel (Tuple.map f x) remove := rfl

def cancellationIndices (s : Ledger) (id : ℕ) : FiniteSubsets ℕ :=
  identifierIndices Entry.liveId {id} (tupleOfList s.live)

theorem eraseId_market {s : Ledger} (hs : Valid s) (id : ℕ) :
    market (eraseId s id) = cancel (market s) (cancellationIndices s id) := by
  rw [market_eq_map, market_eq_map]
  change Tuple.map tagged (tupleOfList (s.live.filter fun a => a.liveId != id)) = _
  rw [← cancelIdentifiers_filter Entry.liveId s.live (ledger_nodup hs) id]
  exact map_cancel _ _ _

theorem appendFresh_market (s : Ledger) (key : ℕ) (buy : Bool) (o : Order) :
    market (appendFresh s key buy o) = concat (market s) ⟨1, fun _ => ⟨buy, o⟩⟩ := by
  apply tupleList_injective
  rw [tupleList_market, tupleList_concat, tupleList_market]
  simp [appendFresh, tupleList, Tuple.entry, tagged]

def resizePayload (s : Ledger) (id : ℕ) (q : PositiveQuantity) :
    DistinctFiniteSubsets TaggedOrder := by
  let I := {i : Fin s.live.length // (s.live.get i).liveId = id}
  let point : I → IndexAugmented TaggedOrder := fun i =>
    IndexAugmented.mk i.val.val (tagged (resized id q (s.live.get i.val)))
  refine ⟨⟨Set.range point, Set.finite_range point⟩, ?_⟩
  intro n x y hx hy
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have hij : i = j := by
    apply Subtype.ext
    apply Fin.ext
    exact (congrArg IndexAugmented.index hi).trans (congrArg IndexAugmented.index hj).symm
  subst j
  exact (congrArg IndexAugmented.value hi).symm.trans (congrArg IndexAugmented.value hj)

theorem mem_resizePayload (s : Ledger) (id : ℕ) (q : PositiveQuantity)
    (p : IndexAugmented TaggedOrder) :
    p ∈ ((resizePayload s id q).val : Set (IndexAugmented TaggedOrder)) ↔
      ∃ i : Fin s.live.length, (s.live.get i).liveId = id ∧
        p = IndexAugmented.mk i.val (tagged (resized id q (s.live.get i))) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.property, hi.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem resizeId_market_vector (s : Ledger) (id : ℕ) (q : PositiveQuantity) :
    market (resizeId s id q) =
      ⟨s.live.length, fun i => tagged (resized id q (s.live.get i))⟩ := by
  apply tupleList_injective
  rw [tupleList_market]
  change (s.live.map (resized id q)).map tagged =
    List.ofFn ((tagged ∘ resized id q) ∘ s.live.get)
  rw [← List.map_ofFn]
  simp [List.map_map]

theorem resizeId_market (s : Ledger) (id : ℕ) (q : PositiveQuantity) :
    market (resizeId s id q) = modify (market s) (resizePayload s id q) := by
  rw [resizeId_market_vector]
  apply congrArg (fun f : Fin s.live.length → TaggedOrder => (⟨s.live.length, f⟩ : Market))
  funext i
  change tagged (resized id q (s.live.get i)) =
    Tuple.entry (modify (market s) (resizePayload s id q)) i
  by_cases hi : (s.live.get i).liveId = id
  · exact (modify_entry_of_mem (market s) (resizePayload s id q) i
      ((mem_resizePayload s id q _).mpr ⟨i, hi, rfl⟩)).symm
  · rw [modify_entry_of_not_exists (market s) (resizePayload s id q) i]
    · change tagged (resized id q (s.live.get i)) = tagged (s.live.get i)
      rw [resized, if_neg hi]
    · rintro ⟨z, hz⟩
      obtain ⟨j, hj, hp⟩ := (mem_resizePayload s id q _).mp hz
      have hij : i = j := Fin.ext (congrArg IndexAugmented.index hp)
      exact hi (hij ▸ hj)

open Foundations.MarketActions.Composite

def eventAction (s : Ledger) : Event → MarketAction TaggedOrder
  | .added a => .add ⟨1, fun _ => tagged a⟩
  | .removed id => .cancel (cancellationIndices s id)
  | .resized id q => .modify (resizePayload s id q)

theorem applyEvent_market {s : Ledger} (hs : Valid s) (event : Event) :
    market (applyEvent s event) = applyAction (market s) (eventAction s event) := by
  cases event with
  | added a =>
    apply tupleList_injective
    change tupleList (market (applyEvent s (.added a))) =
      tupleList (concat (market s) ⟨1, fun _ => tagged a⟩)
    rw [tupleList_market, tupleList_concat, tupleList_market]
    simp [applyEvent, tupleList, Tuple.entry]
  | removed id => exact eraseId_market hs id
  | resized id q => exact resizeId_market s id q

end Thesis.Intraday.LedgerTupleActions
