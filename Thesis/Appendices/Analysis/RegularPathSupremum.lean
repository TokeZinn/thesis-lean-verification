import Thesis.Appendices.Analysis.Analysis
import Mathlib.Analysis.Real.Cardinality

/-! # Jump paths and the nonseparability of the supremum metric

The examples and the uncountable separated family in the paragraph preceding
the Skorokhod construction in the analysis appendix.
-/

noncomputable section
open Set
open scoped ENNReal

namespace Thesis.Foundations.Preliminary.Analysis

variable {a b : ℝ}

def cadlagJump (c : ℝ) : RegularPath a b ℝ .cadlag := by
  refine ⟨fun t ↦ if c ≤ (t : ℝ) then 1 else 0, ?_⟩
  apply isCadlag_of_finite_cut_cells {c}
  intro u v h
  simp only [h c (Finset.mem_singleton_self c)]

def cagladJump (c : ℝ) : RegularPath a b ℝ .caglad := by
  refine ⟨fun t ↦ if c < (t : ℝ) then 1 else 0, ?_⟩
  apply isCaglad_of_finite_cut_cells {c}
  intro u v h
  simp only [h c (Finset.mem_singleton_self c)]

theorem cadlagJump_sup_distance {c d : ℝ} (hc : c ∈ Ioo a b)
    (hd : d ∈ Ioo a b) (hcd : c ≠ d) :
    supPathEDistance (cadlagJump (a := a) (b := b) c).val (cadlagJump d).val = 1 := by
  have upper : supPathEDistance (cadlagJump (a := a) (b := b) c).val
      (cadlagJump d).val ≤ 1 := by
    rw [supPathEDistance_le_iff]
    intro t
    simp only [cadlagJump]
    split_ifs <;> norm_num [edist_dist, Real.dist_eq]
  have lower (c d : ℝ) (hc : c ∈ Ioo a b) (hcd : c < d) :
      1 ≤ supPathEDistance (cadlagJump (a := a) (b := b) c).val (cadlagJump d).val := by
    have h := edist_le_supPathEDistance (cadlagJump (a := a) (b := b) c).val
      (cadlagJump d).val ⟨c, hc.1.le, hc.2.le⟩
    simpa [cadlagJump, not_le.mpr hcd, edist_dist, Real.dist_eq] using h
  refine le_antisymm upper ?_
  rcases lt_or_gt_of_ne hcd with h | h
  · exact lower c d hc h
  · rw [supPathEDistance_symm]
    exact lower d c hd h

/-- The analysis appendix's real-valued counterexample: the supremum metric
on cadlag paths on any nondegenerate interval has no countable dense set. -/
theorem cadlag_sup_not_separable (hab : a < b) :
    ¬ IsSeparableFor (fun f g : RegularPath a b ℝ .cadlag ↦
      supPathEDistance f.val g.val) := by
  classical
  rintro ⟨D, hD, hdense⟩
  have near (t : Ioo a b) : ∃ g ∈ D,
      supPathEDistance (cadlagJump (a := a) (b := b) t).val g.val < 1 / 3 :=
    hdense (cadlagJump t) (1 / 3) (by norm_num)
  choose g hgD hnear using near
  have hinj : Function.Injective g := by
    intro s t hst
    by_contra hne
    have hdist := cadlagJump_sup_distance s.property t.property
      (fun h ↦ hne (Subtype.ext h))
    have ht : supPathEDistance (g s).val (cadlagJump (a := a) (b := b) t).val < 1 / 3 := by
      rw [hst, supPathEDistance_symm]
      exact hnear t
    have h := (supPathEDistance_triangle (cadlagJump (a := a) (b := b) s).val (g s).val
      (cadlagJump t).val).trans_lt (ENNReal.add_lt_add (hnear s) ht)
    rw [hdist] at h
    have hle : (1 : ℝ≥0∞) / 3 + 1 / 3 ≤ 1 := by
      simpa only [one_div, ENNReal.inv_three_add_inv_three] using
        (le_add_right le_rfl : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ ≤ 3⁻¹ + 3⁻¹ + 3⁻¹)
    exact (not_lt_of_ge hle) h
  letI : Countable D := hD.to_subtype
  have hinj' : Function.Injective (fun t ↦ (⟨g t, hgD t⟩ : D)) :=
    fun s t h ↦ hinj (congrArg Subtype.val h)
  haveI : Countable (Ioo a b) := hinj'.countable
  exact (not_le.mpr hab) (Cardinal.Real.Ioo_countable_iff.mp (Set.to_countable _))

end Thesis.Foundations.Preliminary.Analysis
