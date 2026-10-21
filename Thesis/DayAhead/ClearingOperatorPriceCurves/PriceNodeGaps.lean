import Thesis.DayAhead.ClearingOperatorPriceCurves.OfferedPartition
import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLVertices

/-! # Affine excess supply between consecutive original price nodes

The finite merged price grid contains every original buy and sell nodal price.
On a grid gap, each actual accepted-volume function stays in one of its
original affine cells (or a constant exterior tail). Their difference is
therefore affine on that entire gap, as in the source polygonal path proof.
-/
noncomputable section
namespace Thesis.DayAhead.PriceNodeGaps

open Set InterpolatedSide InterpolatedOffered ExcessSupply PiecewiseAffinePriceCurves

/-- A gap containing no original nodal price is contained in one original
accepted-volume partition cell. This includes constant exterior tails. -/
theorem gap_subset_piece {n : ℕ} (p : Fin (n + 1) → ℝ) {a b : ℝ}
    (hab : a < b) (hnodes : ∀ i, p i ∉ Ioo a b) :
    ∃ i : OfferedPartition.Index p, Ioo a b ⊆ OfferedPartition.piece p i := by
  let x := (a + b) / 2
  have hax : a < x := by dsimp [x]; linarith
  have hxb : x < b := by dsimp [x]; linarith
  obtain ⟨i, hi⟩ := OfferedPartition.piece_cover p x
  refine ⟨i, ?_⟩
  cases i with
  | inl v =>
    obtain ⟨j, hj⟩ := v.property
    have hx : x = v.val := hi
    exact False.elim (hnodes j (hj.symm ▸ hx ▸ ⟨hax, hxb⟩))
  | inr i =>
    cases i with
    | inl j =>
      change p j.castSucc < x ∧ x < p j.succ at hi
      have hla : p j.castSucc ≤ a := by
        by_contra h
        exact hnodes j.castSucc ⟨lt_of_not_ge h, hi.1.trans hxb⟩
      have hbr : b ≤ p j.succ := by
        by_contra h
        exact hnodes j.succ ⟨hax.trans hi.2, lt_of_not_ge h⟩
      intro y hy
      exact ⟨hla.trans_lt hy.1, hy.2.trans_le hbr⟩
    | inr k =>
      fin_cases k
      · have hxp : x < p 0 := by simpa [OfferedPartition.piece] using hi
        have hbp : b ≤ p 0 := by
          by_contra h
          exact hnodes 0 ⟨hax.trans hxp, lt_of_not_ge h⟩
        intro y hy
        simpa [OfferedPartition.piece] using hy.2.trans_le hbp
      · have hpx : p (Fin.last n) < x := by simpa [OfferedPartition.piece] using hi
        have hpa : p (Fin.last n) ≤ a := by
          by_contra h
          exact hnodes (Fin.last n) ⟨lt_of_not_ge h, hpx.trans hxb⟩
        intro y hy
        simpa [OfferedPartition.piece] using hpa.trans_lt hy.1

/-- The actual supremum-defined accepted volume is affine throughout a gap
in the original price-node list. -/
theorem offered_affine_on_gap {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hz : Q 0 = 0)
    {a b : ℝ} (hab : a < b) (hnodes : ∀ i, p i ∉ Ioo a b) :
    ∃ A B : ℝ, ∀ x ∈ Ioo a b, offered (Q (Fin.last n)) (curve p Q) x = A*x+B := by
  letI : Fintype (Set.range p) := (Set.finite_range p).fintype
  let P := OfferedPartition.partition p Q hp hQ hz
  obtain ⟨i, hi⟩ := gap_subset_piece p hab hnodes
  obtain ⟨A, B, hAB⟩ := P.affine (Fintype.equivFin (OfferedPartition.Index p) i)
  refine ⟨A, B, fun x hx => hAB x ?_⟩
  simpa only [P, OfferedPartition.partition, Equiv.symm_apply_apply] using hi hx

/-- Actual excess is affine between any two prices having no original buy
or sell price strictly between them. No positivity of individual volumes or
strictness of the price ordering is assumed. -/
theorem excess_affine_on_gap {lo hi : ℝ} (m : Book lo hi)
    {a b : ℝ} (hab : a < b)
    (hs : ∀ i, m.sellPrice i ∉ Ioo a b)
    (hb : ∀ i, m.buyPrice i ∉ Ioo a b) :
    ∃ A B : ℝ, ∀ x ∈ Ioo a b, m.excess x = A*x+B := by
  obtain ⟨As, Bs, hS⟩ := offered_affine_on_gap m.sellPrice
    (InterpolatedSide.cumulative m.sellVolume) m.sellPrice_monotone
    (cumulative_monotone _ m.sellVolume_nonneg) (cumulative_zero _) hab hs
  obtain ⟨Ab, Bb, hB⟩ := offered_affine_on_gap (fun i => -m.buyPrice i)
    (InterpolatedSide.cumulative m.buyVolume)
    (fun i j hij => neg_le_neg (m.buyPrice_antitone hij))
    (cumulative_monotone _ m.buyVolume_nonneg) (cumulative_zero _)
    (neg_lt_neg hab) (by
      intro i h
      exact hb i ⟨neg_lt_neg_iff.mp h.2, neg_lt_neg_iff.mp h.1⟩)
  refine ⟨As+Ab, Bs-Bb, fun x hx => ?_⟩
  rw [VendorPLVertices.excess_eq_offered_difference]
  change offered _ _ x - offered _ _ (-x) = _
  simp only [Book.sellDepth, Book.buyDepth]
  rw [hS x hx, hB (-x) ⟨neg_lt_neg hx.2, neg_lt_neg hx.1⟩]
  ring

end Thesis.DayAhead.PriceNodeGaps
