import Thesis.DayAhead.FunctionalDataAnalysis.SpectralTheorem
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The spectral-basis convention is attainable

This supplies the existence claims in the unlabelled remark following
`thm:spectral-thm`. The nonzero eigenvectors can be indexed by a subset of
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

set_option maxHeartbeats 1000000 in
-- Reindexing the operator-valued series elaborates both finite and infinite basis constructions.
/-- Thesis source: the eigenvalue-ordering clause in the spectral remark.

Original block id: `source:2 - day-ahead/3_functional_data_analysis.tex:105:rem:5`

This is an actual ordered nonzero eigenbasis and operator-norm expansion,
including empty and finite-dimensional range cases. -/
theorem compact_selfAdjoint_ordered_rankOne_expansion [CompleteSpace H]
    [SecondCountableTopology H] (A : H →L[ℝ] H)
    (hcompact : IsCompactOperator A) (hsymm : A.toLinearMap.IsSymmetric) :
    ∃ (I : Set ℕ) (e : I → H) (eigenvalue : I → ℝ),
      Orthonormal ℝ e ∧
      (∀ i, eigenvalue i ≠ 0) ∧
      Antitone (fun i => |eigenvalue i|) ∧
      (Submodule.span ℝ (Set.range e)).topologicalClosure =
        (LinearMap.range A.toLinearMap).topologicalClosure ∧
      (∀ i, A (e i) = eigenvalue i • e i) ∧
      HasSum (fun i => eigenvalue i • FunctionalData.tensorProduct (e i) (e i)) A := by
  classical
  have hdata : ∃ (ι : Type) (_ : Countable ι) (e : ι → H) (eigenvalue : ι → ℝ),
      Orthonormal ℝ e ∧ (∀ i, eigenvalue i ≠ 0) ∧
      (∀ i, A (e i) = eigenvalue i • e i) ∧
      HasSum (fun i => eigenvalue i • FunctionalData.tensorProduct (e i) (e i)) A := by
    by_cases hfinite : FiniteDimensional ℝ H
    · letI := hfinite
      exact finiteDimensional_rankOne_expansion_data A hsymm
    · exact compact_selfAdjoint_rankOne_expansion_external A hcompact hsymm hfinite
  obtain ⟨ι, hι, e, eigenvalue, he, hne, heigen, hseries⟩ := hdata
  letI := hι
  obtain ⟨I, r, hr⟩ := exists_antitone_reindex (fun i => |eigenvalue i|)
    (fun i => abs_pos.mpr (hne i))
    (finite_eigenvalue_superlevels A e eigenvalue he heigen hseries)
  have hseries' : HasSum
      (fun i : I => eigenvalue (r i) • FunctionalData.tensorProduct (e (r i)) (e (r i))) A :=
    r.hasSum_iff.mpr hseries
  refine ⟨I, e ∘ r, eigenvalue ∘ r, he.comp r r.injective,
    fun i => hne (r i), hr, ?_, fun i => heigen (r i), hseries'⟩
  exact closedSpan_eq_closure_range_of_rankOne_expansion A (e ∘ r) (eigenvalue ∘ r)
    (fun i => hne (r i)) (fun i => heigen (r i)) hseries'

/-- Thesis source: the kernel-extension clause in the spectral remark.

Original block id: `source:2 - day-ahead/3_functional_data_analysis.tex:105:rem:5`

An orthonormal basis of the closed range extends to a Hilbert basis of the
whole space, and the newly adjoined orthonormal vectors have closed span
exactly the kernel. Ordering is asserted for the nonzero range eigenvalues
separately; it is not imposed on a natural-number enumeration of this union. -/
theorem range_basis_extension_by_kernel [CompleteSpace H]
    (A : H →L[ℝ] H) (hsymm : A.toLinearMap.IsSymmetric)
    {ι : Type v} (e : ι → H) (he : Orthonormal ℝ e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure =
      (LinearMap.range A.toLinearMap).topologicalClosure) :
    ∃ (w : Set H) (b : HilbertBasis w ℝ H),
      Set.range e ⊆ w ∧ ⇑b = (Subtype.val : w → H) ∧
      (∀ x ∈ w \ Set.range e, A x = 0) ∧
      (Submodule.span ℝ (w \ Set.range e)).topologicalClosure =
        LinearMap.ker A.toLinearMap := by
  classical
  obtain ⟨w, b, hsub, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  have hzero (x : H) (hx : x ∈ w \ Set.range e) : A x = 0 := by
    have hxspan : Submodule.span ℝ (Set.range e) ≤ (innerSL ℝ x).ker := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      have hne : (⟨x, hx.1⟩ : w) ≠ ⟨e i, hsub (Set.mem_range_self i)⟩ := by
        intro h
        exact hx.2 ⟨i, (congrArg Subtype.val h).symm⟩
      have hinner := orthonormal_iff_ite.mp b.orthonormal
        (⟨x, hx.1⟩ : w) ⟨e i, hsub (Set.mem_range_self i)⟩
      simpa [hb, hne] using hinner
    have hclosed := (Submodule.span ℝ (Set.range e)).topologicalClosure_minimal
      hxspan (innerSL ℝ x).isClosed_ker
    rw [hspan] at hclosed
    apply ext_inner_left ℝ
    intro y
    rw [inner_zero_right]
    calc
      inner ℝ y (A x) = inner ℝ (A y) x := (hsymm y x).symm
      _ = inner ℝ x (A y) := real_inner_comm _ _
      _ = 0 := hclosed ((LinearMap.range A.toLinearMap).le_topologicalClosure
        (LinearMap.mem_range_self A.toLinearMap y))
  refine ⟨w, b, hsub, hb, hzero, ?_⟩
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · exact Submodule.span_le.mpr fun x hx => hzero x hx
    · exact A.isClosed_ker
  · intro x hx
    let W := Submodule.span ℝ (w \ Set.range e)
    have hterm (i : w) : b.repr x i • b i ∈ W := by
      by_cases hi : b i ∈ Set.range e
      · have hmem : b i ∈ (LinearMap.ker A.toLinearMap)ᗮ := by
          rw [← selfAdjoint_closure_range_eq_orthogonal_ker A hsymm, ← hspan]
          exact (Submodule.span ℝ (Set.range e)).le_topologicalClosure
            (Submodule.subset_span hi)
        have hcoeff : b.repr x i = 0 := by
          rw [b.repr_apply_apply, real_inner_comm]
          exact hmem x hx
        simp [hcoeff]
      · exact W.smul_mem _ (Submodule.subset_span ⟨by simp [hb], hi⟩)
    exact (Submodule.isClosed_topologicalClosure W).mem_of_tendsto (b.hasSum_repr x)
      (Filter.Eventually.of_forall fun s => W.le_topologicalClosure
        (Submodule.sum_mem W fun i _ => hterm i))

end Thesis.DayAhead.SpectralTheorem
