import Thesis.Foundations.MarketClearing.SeparationAlgebra

/-! # Separation commutes with ordered tuple concatenation -/

noncomputable section
namespace Thesis.Foundations.MarketClearing.SeparationConcat

open Set MarketRepresentation FiniteSets
open MarketActions.Primitive Selection SeparationAlgebra

variable {A : Type*} [DecidableEq A] {X : A → Type*}

def selectedIndex (a : A) (m : Tuple (DisjointUnion X)) :
    Fin (separationComponent a m).1 → Fin m.1 := fun i =>
  ⟨(pairing (separationIndexSet a m)).2 i,
    (mem_separationIndexSet a m).mp (pairing_entry_mem (separationIndexSet a m) i) |>.1⟩

theorem selectedIndex_strictMono (a : A) (m : Tuple (DisjointUnion X)) :
    StrictMono (selectedIndex a m) := by
  intro i j hij
  exact ((FiniteSubsets.toFinset (separationIndexSet a m)).orderEmbOfFin rfl).strictMono hij

theorem tag_iff_selectedIndex (a : A) (m : Tuple (DisjointUnion X)) (k : Fin m.1) :
    (m.2 k).1 = a ↔ ∃ i, selectedIndex a m i = k := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_pairing_entry_eq_of_mem (separationIndexSet a m)
      ((mem_separationIndexSet a m).mpr ⟨k.isLt, h⟩)
    exact ⟨i, Fin.ext hi⟩
  · rintro ⟨i, rfl⟩
    exact ((mem_separationIndexSet a m).mp (pairing_entry_mem (separationIndexSet a m) i)).2

theorem selected_entry (a : A) (m : Tuple (DisjointUnion X))
    (i : Fin (separationComponent a m).1) :
    m.2 (selectedIndex a m i) = Sigma.mk a ((separationComponent a m).2 i) := by
  symm
  exact mk_valueAtTag a _ _

def concatenatedIndex (a : A) (x y : Tuple (DisjointUnion X)) :
    Fin ((separationComponent a x).1 + (separationComponent a y).1) → Fin (x.1 + y.1) :=
  Fin.addCases (fun i => Fin.castAdd y.1 (selectedIndex a x i))
    (fun j => Fin.natAdd x.1 (selectedIndex a y j))

theorem concatenatedIndex_strictMono (a : A) (x y : Tuple (DisjointUnion X)) :
    StrictMono (concatenatedIndex a x y) := by
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      simp only [concatenatedIndex, Fin.addCases_left]
      exact selectedIndex_strictMono a x hij
    · intro j _
      simp only [concatenatedIndex, Fin.addCases_left, Fin.addCases_right]
      change (selectedIndex a x i).val < x.1 + (selectedIndex a y j).val
      have h := (selectedIndex a x i).isLt
      omega
  · intro i
    refine Fin.addCases ?_ ?_ j
    · intro j hij
      have hj := j.isLt
      change (separationComponent a x).1 + i.val < j.val at hij
      omega
    · intro j hij
      simp only [concatenatedIndex, Fin.addCases_right]
      change x.1 + (selectedIndex a y i).val < x.1 + (selectedIndex a y j).val
      apply Nat.add_lt_add_left
      apply selectedIndex_strictMono a y
      change (separationComponent a x).1 + i.val < (separationComponent a x).1 + j.val at hij
      omega

theorem separationComponent_concat (a : A) (x y : Tuple (DisjointUnion X)) :
    separationComponent a (concat x y) =
      concat (separationComponent a x) (separationComponent a y) := by
  apply separationComponent_eq_of_enumeration a _ (concatenatedIndex a x y)
    (concatenatedIndex_strictMono a x y)
    (Fin.append (separationComponent a x).2 (separationComponent a y).2)
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro k
      dsimp only [concat, Tuple.entry, Tuple.length]
      rw [Fin.append_left, tag_iff_selectedIndex]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨Fin.castAdd _ i, by simp [concatenatedIndex]⟩
      · rintro ⟨i, hi⟩
        revert hi
        refine Fin.addCases ?_ ?_ i
        · intro i hi
          have hv := congrArg Fin.val hi
          simp only [concatenatedIndex, Fin.addCases_left, Fin.val_castAdd] at hv
          exact ⟨i, Fin.ext hv⟩
        · intro i hi
          have hv := congrArg Fin.val hi
          simp only [concatenatedIndex, Fin.addCases_right, Fin.val_natAdd,
            Fin.val_castAdd] at hv
          have hk := k.isLt
          omega
    · intro k
      dsimp only [concat, Tuple.entry, Tuple.length]
      rw [Fin.append_right, tag_iff_selectedIndex]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨Fin.natAdd _ i, by simp [concatenatedIndex]⟩
      · rintro ⟨i, hi⟩
        revert hi
        refine Fin.addCases ?_ ?_ i
        · intro i hi
          have hv := congrArg Fin.val hi
          simp only [concatenatedIndex, Fin.addCases_left, Fin.val_natAdd,
            Fin.val_castAdd] at hv
          have hi := (selectedIndex a x i).isLt
          omega
        · intro i hi
          have hv := congrArg Fin.val hi
          simp only [concatenatedIndex, Fin.addCases_right, Fin.val_natAdd,
            Nat.add_left_cancel_iff] at hv
          exact ⟨i, Fin.ext hv⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      dsimp only [concat, Tuple.entry, Tuple.length]
      simp only [concatenatedIndex, Fin.addCases_left, Fin.append_left]
      exact selected_entry a x i
    · intro i
      dsimp only [concat, Tuple.entry, Tuple.length]
      simp only [concatenatedIndex, Fin.addCases_right, Fin.append_right]
      exact selected_entry a y i

theorem separationComponent_tagged (a : A) (x : Tuple (X a)) :
    separationComponent a (Sigma.mk x.1 (fun i => Sigma.mk a (x.2 i))) = x := by
  rcases x with ⟨n, x⟩
  apply separationComponent_eq_of_enumeration (X := X) a
    (Sigma.mk n (fun i => Sigma.mk a (x i))) id (fun _ _ h => h) x
  · intro k
    exact ⟨fun _ => ⟨k, rfl⟩, fun _ => rfl⟩
  · intro i
    rfl

theorem separationComponent_other (a b : A) (hab : a ≠ b) (x : Tuple (X b)) :
    separationComponent a (Sigma.mk x.1 (fun i => Sigma.mk b (x.2 i))) =
      Tuple.empty (X a) := by
  apply separationComponent_eq_of_enumeration a _ (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  · intro k
    exact ⟨fun h => (hab h.symm).elim, fun ⟨i, _⟩ => Fin.elim0 i⟩
  · intro i
    exact Fin.elim0 i

omit [DecidableEq A] in
theorem concat_empty_left {Y : Type*} (x : Tuple Y) :
    concat (Tuple.empty Y) x = x := by
  apply tuple_eq_of_tupleList_eq
  simp only [tupleList_concat, tupleList_empty, List.nil_append]

end Thesis.Foundations.MarketClearing.SeparationConcat
