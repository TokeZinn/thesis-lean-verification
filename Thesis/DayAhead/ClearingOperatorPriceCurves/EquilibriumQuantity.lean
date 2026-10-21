import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedImpactCurve

/-! # Attained equilibrium quantity and positively matched interpolated books

Closing each positive-width interpolation cell at its left endpoint adds
only already accepted quantities: the supply price at that endpoint is no
greater than the local interpolant. This gives a finite closed-cell cover of
the actual supremum-defined acceptance set and proves maximum attainment.
-/

noncomputable section
namespace Thesis.DayAhead.EquilibriumQuantity

open Set InterpolatedSide InterpolatedOffered ExcessSupply

def closedAcceptedCell {n : ℕ} (p Q : Fin (n + 1) → ℝ) (level : ℝ) (j : Fin n) : Set ℝ :=
  if Q j.castSucc < Q j.succ then
    Icc (Q j.castSucc) (Q j.succ) ∩
      {q | interpolate (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) q ≤ level}
  else ∅

theorem isClosed_closedAcceptedCell {n : ℕ} (p Q : Fin (n + 1) → ℝ) (level : ℝ)
    (j : Fin n) : IsClosed (closedAcceptedCell p Q level j) := by
  unfold closedAcceptedCell
  split_ifs
  · exact isClosed_Icc.inter (isClosed_le (by unfold interpolate; fun_prop) continuous_const)
  · exact isClosed_empty

theorem offeredSet_eq_closed_cells {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (level : ℝ) :
    offeredSet (Q (Fin.last n)) (curve p Q) level =
      insert 0 (⋃ j : Fin n, closedAcceptedCell p Q level j) := by
  ext q
  constructor
  · rintro (rfl | hq)
    · exact Or.inl rfl
    · obtain ⟨j, hj⟩ := exists_cell Q hz hq.1.1 hq.1.2
      refine Or.inr (mem_iUnion.mpr ⟨j, ?_⟩)
      rw [closedAcceptedCell, if_pos (hj.1.trans_le hj.2)]
      refine ⟨⟨hj.1.le, hj.2⟩, ?_⟩
      change interpolate (Q j.castSucc) (Q j.succ) (p j.castSucc) (p j.succ) q ≤ level
      rw [← curve_on_cell p Q hQ hz j hj]
      exact hq.2
  · rintro (rfl | hq)
    · exact Or.inl rfl
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hq
      by_cases hwidth : Q j.castSucc < Q j.succ
      · rw [closedAcceptedCell, if_pos hwidth] at hj
        by_cases hzero : q = 0
        · exact Or.inl hzero
        · have hqpos : 0 < q := lt_of_le_of_ne
            ((hz ▸ hQ (Fin.zero_le j.castSucc)).trans hj.1.1) (Ne.symm hzero)
          refine Or.inr ⟨⟨hqpos, hj.1.2.trans (hQ (Fin.le_last _))⟩, ?_⟩
          rcases hj.1.1.eq_or_lt with heq | hlt
          · have hprefix := curve_prefix_le p Q hp hQ hz j.castSucc q ⟨hqpos, heq.symm.le⟩
            have hinterp : interpolate (Q j.castSucc) (Q j.succ)
                (p j.castSucc) (p j.succ) q = p j.castSucc := by
              rw [← heq]
              unfold interpolate
              field_simp [sub_ne_zero.mpr hwidth.ne']
              ring
            exact hprefix.trans (hinterp ▸ hj.2)
          · exact (curve_on_cell p Q hQ hz j ⟨hlt, hj.1.2⟩).symm ▸ hj.2
      · simp [closedAcceptedCell, hwidth] at hj

theorem offeredSet_isCompact {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (level : ℝ) :
    IsCompact (offeredSet (Q (Fin.last n)) (curve p Q) level) := by
  have hclosed : IsClosed (offeredSet (Q (Fin.last n)) (curve p Q) level) := by
    rw [offeredSet_eq_closed_cells p Q hp hQ hz]
    exact isClosed_singleton.union
      (isClosed_iUnion_of_finite (fun j => isClosed_closedAcceptedCell p Q level j))
  apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) (Q (Fin.last n)))).of_isClosed_subset hclosed
  intro q hq
  rcases hq with rfl | hq
  · exact ⟨le_rfl, hz ▸ hQ (Fin.zero_le _)⟩
  · exact ⟨hq.1.1.le, hq.1.2⟩

theorem offered_attained {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0) (level : ℝ) :
    offered (Q (Fin.last n)) (curve p Q) level ∈
      offeredSet (Q (Fin.last n)) (curve p Q) level :=
  (offeredSet_isCompact p Q hp hQ hz level).sSup_mem (offeredSet_nonempty _ _ _)

namespace Book

variable {lo hi : ℝ}

def matchingSet (m : ExcessSupply.Book lo hi) : Set ℝ :=
  offeredSet m.sellDepth m.supply m.crossingPrice ∩
    offeredSet m.buyDepth (fun q => -m.demand q) (-m.crossingPrice)

theorem matchingSet_nonempty (m : ExcessSupply.Book lo hi) : (matchingSet m).Nonempty :=
  ⟨0, Or.inl rfl, Or.inl rfl⟩

theorem matchingSet_isCompact (m : ExcessSupply.Book lo hi) : IsCompact (matchingSet m) := by
  have hS := offeredSet_isCompact m.sellPrice (cumulative m.sellVolume)
    m.sellPrice_monotone (cumulative_monotone _ m.sellVolume_nonneg) (cumulative_zero _)
    m.crossingPrice
  have hD := offeredSet_isCompact (fun i => -m.buyPrice i) (cumulative m.buyVolume)
    (fun _ _ h => neg_le_neg (m.buyPrice_antitone h))
    (cumulative_monotone _ m.buyVolume_nonneg) (cumulative_zero _) (-m.crossingPrice)
  have he : curve (fun i => -m.buyPrice i) (cumulative m.buyVolume) =
      fun q => -m.demand q := by
    funext q
    exact curve_neg_prices _ _ q
  rw [he] at hD
  exact hS.inter hD

/-- Original label: `defn:crossing-price-and-equilibrium-operator`.
The maximum is derived for the literal both-accepted quantity set. -/
def equilibriumQuantity (m : ExcessSupply.Book lo hi) : ℝ := sSup (matchingSet m)

theorem equilibriumQuantity_isGreatest (m : ExcessSupply.Book lo hi) :
    IsGreatest (matchingSet m) (equilibriumQuantity m) :=
  ⟨(matchingSet_isCompact m).sSup_mem (matchingSet_nonempty m),
    fun _ hq => le_csSup (matchingSet_isCompact m).bddAbove hq⟩

theorem equilibriumQuantity_nonneg (m : ExcessSupply.Book lo hi) :
    0 ≤ (equilibriumQuantity m) := (equilibriumQuantity_isGreatest m).2 ⟨Or.inl rfl, Or.inl rfl⟩

def equilibriumOperator (m : ExcessSupply.Book lo hi) : ℝ × {q : ℝ // 0 ≤ q} :=
  (m.crossingPrice, ⟨(equilibriumQuantity m), (equilibriumQuantity_nonneg m)⟩)

theorem matchingSet_eq_source (m : ExcessSupply.Book lo hi) :
    (matchingSet m) = insert 0 {q | q ∈ Ioc 0 (min m.sellDepth m.buyDepth) ∧
      m.supply q ≤ m.crossingPrice ∧ m.crossingPrice ≤ m.demand q} := by
  ext q
  simp only [matchingSet, offeredSet, mem_inter_iff, mem_insert_iff, mem_setOf_eq,
    mem_Ioc, le_min_iff, neg_le_neg_iff]
  constructor
  · rintro ⟨hs, hb⟩
    rcases hs with rfl | hs
    · exact Or.inl rfl
    rcases hb with rfl | hb
    · exact Or.inl rfl
    exact Or.inr ⟨⟨hs.1.1, hs.1.2, hb.1.2⟩, hs.2, hb.2⟩
  · rintro (rfl | ⟨⟨hq, hs, hb⟩, hS, hD⟩)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr ⟨⟨hq, hs⟩, hS⟩, Or.inr ⟨⟨hq, hb⟩, hD⟩⟩

/-- Original label: `defn:positively-matched-state-space-and-price-impact-curve`. -/
abbrev PositivelyMatched (lo hi : ℝ) := {m : ExcessSupply.Book lo hi // 0 < (equilibriumQuantity m)}

def positiveImpactCurve (m : PositivelyMatched lo hi) : PiecewiseAffinePriceCurves.Curve :=
  InterpolatedImpactCurve.Book.impactCurve m.val

end Book
end Thesis.DayAhead.EquilibriumQuantity
