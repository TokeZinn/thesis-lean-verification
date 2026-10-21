import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedOffered

/-! # A finite affine partition of the actual accepted-volume function -/

noncomputable section
namespace Thesis.DayAhead.OfferedPartition

open Set InterpolatedSide InterpolatedOffered ExcessSupply PiecewiseAffinePriceCurves

variable {n : ℕ} (p : Fin (n + 1) → ℝ)

local instance : Fintype (Set.range p) := (Set.finite_range p).fintype

abbrev Index := (Set.range p) ⊕ (Fin n ⊕ Fin 2)

def piece : Index p → Set ℝ
  | .inl v => {v.val}
  | .inr (.inl j) => Ioo (p j.castSucc) (p j.succ)
  | .inr (.inr k) => if k = 0 then Iio (p 0) else Ioi (p (Fin.last n))

theorem node_not_open (hp : Monotone p) (k : Fin (n + 1)) (j : Fin n) :
    p k ∉ Ioo (p j.castSucc) (p j.succ) := by
  intro h
  by_cases hk : k ≤ j.castSucc
  · exact (not_lt_of_ge (hp hk)) h.1
  · have hj : j.succ ≤ k := by
      change ¬(k.val ≤ j.val) at hk
      change j.val + 1 ≤ k.val
      omega
    exact (not_lt_of_ge (hp hj)) h.2

theorem open_disjoint (hp : Monotone p) (i j : Fin n) (hij : i ≠ j) :
    Disjoint (Ioo (p i.castSucc) (p i.succ)) (Ioo (p j.castSucc) (p j.succ)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hidx : i.succ ≤ j.castSucc := by exact_mod_cast hij
    linarith [hx.2, hy.1, hp hidx]
  · have hidx : j.succ ≤ i.castSucc := by exact_mod_cast hji
    linarith [hy.2, hx.1, hp hidx]

theorem piece_unique (hp : Monotone p) (x : ℝ) (i j : Index p)
    (hi : x ∈ piece p i) (hj : x ∈ piece p j) : i = j := by
  cases i with
  | inl a =>
    have hx : x = a.val := hi
    subst x
    cases j with
    | inl b => exact congrArg Sum.inl (Subtype.ext (mem_singleton_iff.mp hj))
    | inr b =>
      cases b with
      | inl k =>
        obtain ⟨r, hr⟩ := a.property
        exact False.elim (node_not_open p hp r k (hr.symm ▸ hj))
      | inr k =>
        obtain ⟨r, hr⟩ := a.property
        fin_cases k <;> simp only [piece, ↓reduceIte, Fin.zero_eta, Fin.isValue,
          Fin.mk_one, one_ne_zero, mem_Iio, mem_Ioi] at hj
        · exact False.elim ((not_lt_of_ge (hp (Fin.zero_le r))) (hr.symm ▸ hj))
        · exact False.elim ((not_lt_of_ge (hp (Fin.le_last r))) (hr.symm ▸ hj))
  | inr a =>
    cases a with
    | inl a =>
      cases j with
      | inl b =>
        have hx : x = b.val := hj
        obtain ⟨r, hr⟩ := b.property
        exact False.elim (node_not_open p hp r a (hr.symm ▸ hx ▸ hi))
      | inr b =>
        cases b with
        | inl b =>
          by_cases hab : a = b
          · exact hab ▸ rfl
          · exact False.elim (Set.disjoint_left.mp (open_disjoint p hp a b hab) hi hj)
        | inr k =>
          fin_cases k <;> simp only [piece, ↓reduceIte, Fin.zero_eta, Fin.isValue,
            Fin.mk_one, one_ne_zero, mem_Iio, mem_Ioi] at hj
          · have h := hp (Fin.zero_le a.castSucc)
            exact False.elim (by change _ < x ∧ x < _ at hi; linarith)
          · have h := hp (Fin.le_last a.succ)
            exact False.elim (by change _ < x ∧ x < _ at hi; linarith)
    | inr a =>
      cases j with
      | inl b =>
        have hx : x = b.val := hj
        obtain ⟨r, hr⟩ := b.property
        fin_cases a <;> simp only [piece, ↓reduceIte, Fin.zero_eta, Fin.isValue,
          Fin.mk_one, one_ne_zero, mem_Iio, mem_Ioi] at hi
        · exact False.elim (by have := hp (Fin.zero_le r); rw [← hr] at hx; linarith)
        · exact False.elim (by have := hp (Fin.le_last r); rw [← hr] at hx; linarith)
      | inr b =>
        cases b with
        | inl b =>
          fin_cases a <;> simp only [piece, ↓reduceIte, Fin.zero_eta, Fin.isValue,
            Fin.mk_one, one_ne_zero, mem_Iio, mem_Ioi] at hi
          · have h := hp (Fin.zero_le b.castSucc)
            exact False.elim (by change _ < x ∧ x < _ at hj; linarith)
          · have h := hp (Fin.le_last b.succ)
            exact False.elim (by change _ < x ∧ x < _ at hj; linarith)
        | inr b =>
          fin_cases a <;> fin_cases b
          · rfl
          · have hl : x < p 0 := by simpa [piece] using hi
            have hr : p (Fin.last n) < x := by simpa [piece] using hj
            exact False.elim (by have := hp (Fin.zero_le (Fin.last n)); linarith)
          · have hl : x < p 0 := by simpa [piece] using hj
            have hr : p (Fin.last n) < x := by simpa [piece] using hi
            exact False.elim (by have := hp (Fin.zero_le (Fin.last n)); linarith)
          · rfl

theorem piece_cover (x : ℝ) : ∃ i : Index p, x ∈ piece p i := by
  by_cases hl : x < p 0
  · exact ⟨.inr (.inr 0), by simpa [piece] using hl⟩
  by_cases hr : p (Fin.last n) < x
  · exact ⟨.inr (.inr 1), by simpa [piece] using hr⟩
  by_cases hn : x ∈ Set.range p
  · exact ⟨.inl ⟨x, hn⟩, rfl⟩
  have hx0 : 0 < x - p 0 := by
    have hne : x ≠ p 0 := fun h => hn ⟨0, h.symm⟩
    exact sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm hne))
  obtain ⟨j, hj⟩ := exists_cell (fun i => p i - p 0) (by simp) hx0
    (sub_le_sub_right (le_of_not_gt hr) _)
  refine ⟨.inr (.inl j), ?_⟩
  change p j.castSucc < x ∧ x < p j.succ
  have hne : x ≠ p j.succ := fun h => hn ⟨_, h.symm⟩
  change p j.castSucc - p 0 < x - p 0 ∧ x - p 0 ≤ p j.succ - p 0 at hj
  exact ⟨by linarith [hj.1], lt_of_le_of_ne (by linarith [hj.2]) hne⟩

def partition (Q : Fin (n + 1) → ℝ) (hp : Monotone p) (hQ : Monotone Q)
    (hz : Q 0 = 0) : AffinePartition Set.univ (offered (Q (Fin.last n)) (curve p Q)) where
  count := Fintype.card (Index p)
  piece := fun k => piece p ((Fintype.equivFin (Index p)).symm k)
  interval := by
    intro k
    generalize (Fintype.equivFin (Index p)).symm k = a
    cases a with
    | inl a => exact Set.ordConnected_singleton
    | inr a =>
      cases a with
      | inl a => exact Set.ordConnected_Ioo
      | inr a =>
        fin_cases a
        · exact Set.ordConnected_Iio
        · exact Set.ordConnected_Ioi
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij ((Fintype.equivFin (Index p)).symm.injective (piece_unique p hp x _ _ hi hj))
  cover := by
    intro x
    simp only [Set.mem_univ, true_iff]
    obtain ⟨i, hi⟩ := piece_cover p x
    exact ⟨Fintype.equivFin _ i, by simpa using hi⟩
  affine := by
    intro k
    generalize (Fintype.equivFin (Index p)).symm k = a
    cases a with
    | inl a => exact ⟨0, offered (Q (Fin.last n)) (curve p Q) a.val, fun x hx => by
        have hx' : x = a.val := hx
        simp [hx']⟩
    | inr a =>
      cases a with
      | inl j => exact offered_on_price_cell_affine p Q hp hQ hz j
      | inr j =>
        have hdepth : 0 ≤ Q (Fin.last n) := hz ▸ hQ (Fin.zero_le _)
        have hbounds := curve_bounded p Q hQ hz (p 0) (p (Fin.last n))
          (fun i => ⟨hp (Fin.zero_le _), hp (Fin.le_last _)⟩)
        fin_cases j
        · refine ⟨0, 0, fun x hx => ?_⟩
          have hx' : x < p 0 := by simpa [piece] using hx
          rw [offered_eq_zero _ _ _ (fun q hq h => by
            have := (hbounds q ⟨hq.1.le, hq.2⟩).1; linarith)]
          simp
        · refine ⟨0, Q (Fin.last n), fun x hx => ?_⟩
          have hx' : p (Fin.last n) < x := by simpa [piece] using hx
          rw [offered_eq_depth _ hdepth _ _ (fun q hq =>
            (hbounds q ⟨hq.1.le, hq.2⟩).2.trans hx'.le)]
          simp

end Thesis.DayAhead.OfferedPartition
