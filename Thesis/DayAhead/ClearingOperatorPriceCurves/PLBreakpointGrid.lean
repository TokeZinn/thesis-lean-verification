import Thesis.DayAhead.ClearingOperatorPriceCurves.PLJoinComparison
import Thesis.DayAhead.ClearingOperatorPriceCurves.OfferedPartition

/-! # Finite candidate pruning for the intrinsic canonical nodes

Open candidate gaps are affine. Therefore every intrinsic breakpoint is a
candidate vertex, and deleting locally affine joins merges adjacent affine
pieces using their equal slopes and selected join values.
-/

noncomputable section
namespace Thesis.DayAhead.PLBreakpointGrid

open Set Filter Topology PiecewiseAffinePriceCurves PLCanonicalEncoding PLJoinComparison

theorem breakpoints_subset_grid (f : Curve) {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hfirst : y 0 = f.leftEndpoint) (hlast : y (Fin.last n) = f.rightEndpoint)
    (hgaps : ∀ j : Fin n, ∃ A B : ℝ,
      ∀ x ∈ Ioo (y j.castSucc) (y j.succ), f.price x = A * x + B) :
    breakpoints f ⊆ Set.range y := by
  intro q hq
  obtain ⟨i, hi⟩ := OfferedPartition.piece_cover y q
  cases i with
  | inl v =>
    have he : q = v.val := hi
    exact he ▸ v.property
  | inr k =>
    cases k with
    | inl j =>
      obtain ⟨A, B, hAB⟩ := hgaps j
      have ha : AffineNear f q := by
        refine ⟨A, B, ?_⟩
        filter_upwards [isOpen_Ioo.mem_nhds hi] with x hx using hAB x hx
      exact False.elim (hq.2.2 ha)
    | inr k =>
      fin_cases k
      · have hh : q < f.leftEndpoint := by simpa [OfferedPartition.piece, hfirst] using hi
        exact False.elim (not_lt_of_ge hq.1.1.le hh)
      · have hh : f.rightEndpoint < q := by simpa [OfferedPartition.piece, hlast] using hi
        exact False.elim (not_lt_of_ge hq.1.2.le hh)

/-- The finite collinear-join deletion step, following the vertex path. -/
theorem affine_on_grid_of_local_joins (f : Curve) {n : ℕ} (y : Fin (n + 2) → ℝ)
    (hy : StrictMono y)
    (hgaps : ∀ j : Fin (n + 1), ∃ A B : ℝ,
      ∀ x ∈ Ioo (y j.castSucc) (y j.succ), f.price x = A * x + B)
    (hjoins : ∀ j : Fin n, AffineNear f (y j.succ.castSucc)) :
    ∃ A B : ℝ, ∀ x ∈ Ioo (y 0) (y (Fin.last (n + 1))), f.price x = A * x + B := by
  induction n with
  | zero => exact hgaps 0
  | succ n ih =>
    let prefixGrid : Fin (n + 2) → ℝ := fun i => y i.castSucc
    have hp : StrictMono prefixGrid := hy.comp (fun _ _ h => h)
    have hpg : ∀ j : Fin (n + 1), ∃ A B : ℝ,
        ∀ x ∈ Ioo (prefixGrid j.castSucc) (prefixGrid j.succ), f.price x = A * x + B := by
      intro j
      exact hgaps j.castSucc
    have hpj : ∀ j : Fin n, AffineNear f (prefixGrid j.succ.castSucc) := by
      intro j
      exact hjoins j.castSucc
    obtain ⟨L, B, hleft⟩ := ih prefixGrid hp hpg hpj
    obtain ⟨R, D, hright⟩ := hgaps (Fin.last (n + 1))
    have hab : y 0 < y (Fin.last (n + 1)).castSucc :=
      hy (by change (0 : ℕ) < n + 1; omega)
    have hbc : y (Fin.last (n + 1)).castSucc < y (Fin.last (n + 2)) :=
      hy (Fin.castSucc_lt_succ (i := Fin.last (n + 1)))
    have hjoin : AffineNear f (y (Fin.last (n + 1)).castSucc) := hjoins (Fin.last n)
    have hl : ∀ x ∈ Ioo (y 0) (y (Fin.last (n + 1)).castSucc),
        f.price x = L * x + B := by simpa only [prefixGrid, Fin.castSucc_zero] using hleft
    have hr : ∀ x ∈ Ioo (y (Fin.last (n + 1)).castSucc) (y (Fin.last (n + 2))),
        f.price x = R * x + D := hright
    obtain ⟨hbL, hbR, hLR⟩ := (affineNear_iff_two_lines f hab hbc hl hr).mp hjoin
    have hBD : B = D := by rw [← hLR] at hbR; linarith
    refine ⟨L, B, ?_⟩
    intro x hx
    rcases lt_trichotomy x (y (Fin.last (n + 1)).castSucc) with hxb | rfl | hbx
    · exact hl x ⟨hx.1, hxb⟩
    · exact hbL
    · rw [hr x ⟨hbx, hx.2⟩, ← hLR, ← hBD]

end Thesis.DayAhead.PLBreakpointGrid
