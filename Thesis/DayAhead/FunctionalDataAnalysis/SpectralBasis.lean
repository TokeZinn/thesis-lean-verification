import Thesis.DayAhead.FunctionalDataAnalysis.SpectralTheorem
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The spectral-basis convention is attainable

This supplies the existence claims in the thesis prose on the spectral
decomposition of compact self-adjoint operators. The nonzero eigenvectors can be
indexed by a subset of
the natural numbers, with their eigenvalue magnitudes in decreasing order.
The range basis can separately be completed by vectors in the kernel.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Thesis.DayAhead.SpectralTheorem

universe u v

/-- A positive countable family with finite positive superlevel sets can be
enumerated in decreasing order. Equal values are ordered using an injective
natural-number encoding; finite predecessor counts give the ordered indices.
The empty and finite cases are included. -/
theorem exists_antitone_reindex {ι : Type v} [Countable ι] (f : ι → ℝ)
    (hpos : ∀ i, 0 < f i)
    (hfinite : ∀ ε > 0, Set.Finite {i | ε ≤ f i}) :
    ∃ (I : Set ℕ) (r : I ≃ ι), Antitone (fun n => f (r n)) := by
  classical
  obtain ⟨code, hcode⟩ := exists_injective_nat ι
  let before : ι → ι → Prop := fun i j => f j < f i ∨ f i = f j ∧ code i < code j
  have htrans {i j k : ι} (hij : before i j) (hjk : before j k) : before i k := by
    rcases hij with hij | ⟨hij, hcij⟩ <;> rcases hjk with hjk | ⟨hjk, hcjk⟩
    · exact Or.inl (hjk.trans hij)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨hij.trans hjk, hcij.trans hcjk⟩
  have hirrefl (i : ι) : ¬ before i i := by simp [before]
  have htotal {i j : ι} (hij : i ≠ j) : before i j ∨ before j i := by
    rcases lt_trichotomy (f i) (f j) with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases lt_or_gt_of_ne (fun hc => hij (hcode hc)) with hc | hc
      · exact Or.inl (Or.inr ⟨h, hc⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hc⟩)
    · exact Or.inl (Or.inl h)
  let pred (i : ι) : Set ι := {j | before j i}
  have hpred (i : ι) : (pred i).Finite := (hfinite (f i) (hpos i)).subset (by
    intro j hj
    rcases hj with hj | ⟨hj, _⟩
    · exact hj.le
    · exact hj.ge)
  let rank (i : ι) : ℕ := (pred i).ncard
  have hrank {i j : ι} (hij : before i j) : rank i < rank j := by
    apply Set.ncard_lt_ncard _ (hpred j)
    refine ⟨fun k hk => htrans hk hij, ?_⟩
    intro hsub
    exact hirrefl i (hsub hij)
  have hinj : Function.Injective rank := by
    intro i j hij
    by_contra hne
    rcases htotal hne with h | h
    · exact (ne_of_lt (hrank h)) hij
    · exact (ne_of_lt (hrank h)) hij.symm
  let r : Set.range rank ≃ ι := (Equiv.ofInjective rank hinj).symm
  refine ⟨Set.range rank, r, ?_⟩
  intro i j hij
  by_contra h
  have hlt : rank (r j) < rank (r i) := hrank (Or.inl (lt_of_not_ge h))
  have hi : rank (r i) = i.val :=
    congrArg Subtype.val ((Equiv.ofInjective rank hinj).apply_symm_apply i)
  have hj : rank (r j) = j.val :=
    congrArg Subtype.val ((Equiv.ofInjective rank hinj).apply_symm_apply j)
  rw [hi, hj] at hlt
  exact (not_lt_of_ge hij) hlt

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Supporting fact: the algebraic span of an infinite orthonormal basis is proper.

The dense span of a countably infinite Hilbert basis is strictly larger than
its algebraic span: the vector with coordinates `2⁻ⁿ` has infinitely many
nonzero coordinates, whereas every finite linear combination has finite support. -/
theorem hilbertBasis_algebraic_span_ne_top (b : HilbertBasis ℕ ℝ H) :
    Submodule.span ℝ (Set.range b) ≠ ⊤ := by
  classical
  let W : Submodule ℝ H :=
    { carrier := {x | Memℓp (fun i => b.repr x i) 0}
      zero_mem' := by simpa using (zero_memℓp (E := fun _ : ℕ => ℝ) (p := 0))
      add_mem' := fun hx hy => by simpa using hx.add hy
      smul_mem' := fun c _ hx => by simpa using hx.const_smul c }
  have hspan : Submodule.span ℝ (Set.range b) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change Memℓp (fun j => b.repr (b i) j) 0
    simpa only [b.repr_self, lp.coeFn_single] using
      (lp.memℓp (lp.single (E := fun _ : ℕ => ℝ) 0 i 1))
  have hc : Memℓp (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
    apply memℓp_gen
    have hs := summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ) ^ 2| < 1)
    convert hs using 1
    ext n
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  let c : lp (fun _ : ℕ => ℝ) 2 := ⟨_, hc⟩
  intro htop
  have hmem : b.repr.symm c ∈ W := hspan (by rw [htop]; trivial)
  change Memℓp (fun n => b.repr (b.repr.symm c) n) 0 at hmem
  rw [b.repr.apply_symm_apply] at hmem
  have hfinite := hmem.finite_dsupport
  have hsupport : {n : ℕ | c n ≠ 0} = Set.univ := by
    ext n
    simp [c]
  rw [hsupport] at hfinite
  exact Set.infinite_univ hfinite

/-- Operator-norm convergence of an orthonormal eigen-expansion forces only
finitely many eigenvalues to exceed any given positive magnitude. -/
theorem finite_eigenvalue_superlevels {ι : Type v} (A : H →L[ℝ] H)
    (e : ι → H) (eigenvalue : ι → ℝ) (he : Orthonormal ℝ e)
    (heigen : ∀ i, A (e i) = eigenvalue i • e i)
    (hseries : Tendsto
      (fun s : Finset ι => ∑ i ∈ s, eigenvalue i • FunctionalData.tensorProduct (e i) (e i))
      atTop (𝓝 A)) (ε : ℝ) (hε : 0 < ε) :
    Set.Finite {i | ε ≤ |eigenvalue i|} := by
  classical
  obtain ⟨s, hs⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hseries ε hε)
  let P := ∑ i ∈ s, eigenvalue i • FunctionalData.tensorProduct (e i) (e i)
  have hnorm : ‖A - P‖ < ε := by simpa [dist_eq_norm, norm_sub_rev, P] using hs s le_rfl
  apply s.finite_toSet.subset
  intro i hi
  by_contra hnot
  have hPi : P (e i) = 0 := by
    simp only [P, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      FunctionalData.tensorProduct_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := fun h => hnot (h ▸ hj)
    simp [orthonormal_iff_ite.mp he, hji]
  have hbound := (A - P).le_opNorm (e i)
  rw [ContinuousLinearMap.sub_apply, hPi, sub_zero, heigen, norm_smul,
    he.norm_eq_one i, mul_one, mul_one, Real.norm_eq_abs] at hbound
  exact (not_lt_of_ge hi) (hbound.trans_lt hnorm)

end Thesis.DayAhead.SpectralTheorem
