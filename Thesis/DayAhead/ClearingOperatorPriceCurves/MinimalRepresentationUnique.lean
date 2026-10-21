import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialSidedCertificate

/-! # Uniqueness of the ordered minimal representation -/

namespace Thesis.DayAhead.SidedCertificate

open PriceCurves Set

/-- Construct the unique ordered minimal representation from an explicit
strictly increasing enumeration of all attained price levels. -/
def minimalRepresentationOfLevels (f : PriceCurve) {n : ℕ} (hn : 0 < n)
    (level : Fin n → ℝ) (hlevel : StrictMono level) (hrange : range level = range f.price) :
    MinimalRepresentation f where
  blockCount := n
  blockCount_pos := hn
  cell i := {x | f.price x = level i}
  level := level
  cell_nonempty i := by
    obtain ⟨x, hx⟩ := hrange ▸ mem_range_self i
    exact ⟨x, hx⟩
  cell_disjoint := by
    intro i _ j _ hij
    change Disjoint {x | f.price x = level i} {x | f.price x = level j}
    rw [disjoint_left]
    intro x hx hy
    exact hij (hlevel.injective (hx.symm.trans hy))
  cell_cover := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := hrange.symm ▸ mem_range_self x
    exact mem_iUnion.mpr ⟨i, hi.symm⟩
  cell_ordConnected := by
    intro i
    apply ordConnected_iff.mpr
    intro x hx y hy _ z hz
    exact le_antisymm ((f.price_monotone hz.2).trans_eq hy)
      (hx.symm.trans_le (f.price_monotone hz.1))
  cell_ordered := by
    intro i j hij x hx y hy
    by_contra hxy
    have h := f.price_monotone (le_of_not_ge hxy)
    have hlevels := hlevel hij
    change f.price x = level i at hx
    change f.price y = level j at hy
    rw [hx, hy] at h
    exact (not_le_of_gt hlevels) h
  level_strictMono := hlevel
  represents := by
    classical
    intro x
    obtain ⟨i, hi⟩ := hrange.symm ▸ mem_range_self x
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hne : f.price x ≠ level j := by
        intro h
        exact hji (hlevel.injective (h.symm.trans hi.symm))
      simp [hne]
    · simp

theorem range_minimal_levels {f : PriceCurve} (m : MinimalRepresentation f) :
    range m.level = range f.price := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := m.cell_nonempty i
    exact ⟨x, price_eq_level_of_mem m hx⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := exists_cell_mem m x
    exact ⟨i, (price_eq_level_of_mem m hi).symm⟩

theorem minimalRepresentation_unique {f : PriceCurve} (m n : MinimalRepresentation f) : m = n := by
  have hr : range m.level = range n.level :=
    (range_minimal_levels m).trans (range_minimal_levels n).symm
  have hc : m.blockCount = n.blockCount := by
    have h := congrArg Set.ncard hr
    simpa only [Set.ncard_range_of_injective m.level_strictMono.injective,
      Set.ncard_range_of_injective n.level_strictMono.injective, Nat.card_fin] using h
  have hmcell := mem_cell_iff_price_eq m
  have hncell := mem_cell_iff_price_eq n
  cases m with
  | mk mc mcpos mcell mlevel mne mdisj mcov moc mo mstrict mrep =>
    cases n with
    | mk nc ncpos ncell nlevel nne ndisj ncov noc no nstrict nrep =>
      dsimp only at hc hr hmcell hncell
      subst nc
      have hl : mlevel = nlevel := (mstrict.range_inj nstrict).mp hr
      subst nlevel
      have hcell : mcell = ncell := by
        funext i
        exact Set.ext (fun x => (hmcell i x).trans (hncell i x).symm)
      subst ncell
      rfl

instance (f : PriceCurve) : Subsingleton (MinimalRepresentation f) :=
  ⟨minimalRepresentation_unique⟩

end Thesis.DayAhead.SidedCertificate
