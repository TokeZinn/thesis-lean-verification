import Thesis.Foundations.MarketClearing.Selection

/-! # Exact algebra of the order-preserving separation operator -/

noncomputable section
namespace Thesis.Foundations.MarketClearing.SeparationAlgebra

open Set MarketRepresentation FiniteSets
open MarketActions.Primitive Selection

variable {A : Type*} [DecidableEq A] {X : A → Type*}

omit [DecidableEq A] in
theorem mk_valueAtTag (a : A) (z : DisjointUnion X) (h : z.1 = a) :
    Sigma.mk a (valueAtTag a z h) = z := by
  rcases z with ⟨b, z⟩
  cases h
  rfl

/-- Separation returns exactly any increasing enumeration of all entries
with the selected tag. Multiplicities and the original order are preserved. -/
theorem separationComponent_eq_of_enumeration (a : A) (m : Tuple (DisjointUnion X))
    {n : ℕ} (j : Fin n → Fin m.1) (hj : StrictMono j) (x : Fin n → X a)
    (htag : ∀ k : Fin m.1, (m.2 k).1 = a ↔ ∃ i, j i = k)
    (hentry : ∀ i, m.2 (j i) = Sigma.mk a (x i)) :
    separationComponent a m = Sigma.mk n x := by
  classical
  let s := FiniteSubsets.toFinset (separationIndexSet a m)
  have hs : s = Finset.univ.image (fun i => (j i).val) := by
    ext k
    rw [FiniteSubsets.mem_toFinset, mem_separationIndexSet, Finset.mem_image]
    constructor
    · rintro ⟨hk, htagk⟩
      obtain ⟨i, hi⟩ := (htag ⟨k, hk⟩).mp htagk
      exact ⟨i, Finset.mem_univ _, congrArg Fin.val hi⟩
    · rintro ⟨i, _, hi⟩
      subst k
      exact ⟨(j i).isLt, (htag (j i)).mpr ⟨i, rfl⟩⟩
  have hjval : StrictMono (fun i => (j i).val) := fun _ _ h => hj h
  have hcard : s.card = n := by
    rw [hs, Finset.card_image_of_injective _ hjval.injective, Finset.card_univ, Fintype.card_fin]
  have hmemb (i : Fin n) : (j i).val ∈ s := by
    rw [hs]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  subst n
  have he := Finset.orderEmbOfFin_unique rfl hmemb hjval
  refine Sigma.ext (show (separationComponent a m).1 = s.card from rfl) ?_
  apply heq_of_eq
  funext i
  have hindex : (pairing (separationIndexSet a m)).2 i = (j i).val :=
    (congrFun he i).symm
  have htagi : (m.2 (j i)).1 = a := (htag (j i)).mpr ⟨i, rfl⟩
  have hpair : Sigma.mk a ((separationComponent a m).2 i) = m.2 (j i) := by
    change Sigma.mk a (valueAtTag a (m.2 ⟨_, _⟩) _) = _
    rw [mk_valueAtTag]
    apply congrArg m.2
    exact Fin.ext hindex
  exact eq_of_heq (Sigma.mk.inj (hpair.trans (hentry i))).2

def taggedConcat (a b : A) (x : Tuple (X a)) (y : Tuple (X b)) : Tuple (DisjointUnion X) :=
  concat ⟨x.1, fun i => Sigma.mk a (x.2 i)⟩ ⟨y.1, fun i => Sigma.mk b (y.2 i)⟩

theorem separationComponent_taggedConcat_left (a b : A) (hab : a ≠ b)
    (x : Tuple (X a)) (y : Tuple (X b)) : separationComponent a (taggedConcat a b x y) = x := by
  apply separationComponent_eq_of_enumeration a _ (Fin.castAdd y.1) (fun _ _ h => h) x.2
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      dsimp only [taggedConcat, concat, Tuple.entry, Tuple.length]
      rw [Fin.append_left]
      exact ⟨fun _ => ⟨i, rfl⟩, fun _ => rfl⟩
    · intro i
      dsimp only [taggedConcat, concat, Tuple.entry, Tuple.length]
      rw [Fin.append_right]
      constructor
      · intro h
        exact (hab h.symm).elim
      · rintro ⟨j, hj⟩
        have hv := congrArg Fin.val hj
        have hjlt := j.isLt
        change j.val < x.1 at hjlt
        change j.val = x.1 + i.val at hv
        omega
  · intro i
    dsimp only [taggedConcat, concat, Tuple.entry, Tuple.length]
    rw [Fin.append_left]

theorem separationComponent_taggedConcat_right (a b : A) (hab : a ≠ b)
    (x : Tuple (X a)) (y : Tuple (X b)) : separationComponent b (taggedConcat a b x y) = y := by
  apply separationComponent_eq_of_enumeration b _ (Fin.natAdd x.1) (fun _ _ h =>
    Nat.add_lt_add_left h _) y.2
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      dsimp only [taggedConcat, concat, Tuple.entry, Tuple.length]
      rw [Fin.append_left]
      constructor
      · intro h
        exact (hab h).elim
      · rintro ⟨j, hj⟩
        have hv := congrArg Fin.val hj
        have hilt := i.isLt
        change i.val < x.1 at hilt
        change x.1 + j.val = i.val at hv
        omega
    · intro i
      dsimp only [taggedConcat, concat, Tuple.entry, Tuple.length]
      rw [Fin.append_right]
      exact ⟨fun _ => ⟨i, rfl⟩, fun _ => rfl⟩
  · intro i
    dsimp only [taggedConcat, concat, Tuple.entry, Tuple.length]
    rw [Fin.append_right]

end Thesis.Foundations.MarketClearing.SeparationAlgebra
