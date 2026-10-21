import Thesis.DayAhead.FunctionalDataAnalysis.FunctionalData
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # Operator-norm convergence of compact spectral expansions

Finite orthogonal projections are contractions and converge to the identity
on the closed span of the orthonormal family. Equicontinuity makes this
convergence uniform on compact sets. Applied to the image of the unit ball
under a compact operator, this gives operator-norm convergence.
-/

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace Thesis.DayAhead.CompactSpectralExpansion

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type v} (e : ι → H)

def partialProjection (s : Finset ι) : H →L[ℝ] H :=
  ∑ i ∈ s, FunctionalData.tensorProduct (e i) (e i)

theorem partialProjection_apply (s : Finset ι) (x : H) :
    partialProjection e s x = ∑ i ∈ s, inner ℝ (e i) x • e i := by
  simp [partialProjection, FunctionalData.tensorProduct_apply]

theorem partialProjection_norm_le (he : Orthonormal ℝ e) (s : Finset ι) (x : H) :
    ‖partialProjection e s x‖ ≤ ‖x‖ := by
  have hsq : ‖partialProjection e s x‖ ^ 2 = ∑ i ∈ s, ‖inner ℝ (e i) x‖ ^ 2 := by
    rw [partialProjection_apply, ← real_inner_self_eq_norm_sq]
    rw [he.inner_sum]
    simp [Real.norm_eq_abs, pow_two]
  have hbound := he.sum_inner_products_le (s := s) x
  nlinarith [norm_nonneg (partialProjection e s x), norm_nonneg x]

theorem partialProjection_lipschitz (he : Orthonormal ℝ e) (s : Finset ι) :
    LipschitzWith 1 (partialProjection e s) := by
  apply (ContinuousLinearMap.opNorm_le_iff_lipschitz (K := 1)).mp
  apply (partialProjection e s).opNorm_le_bound zero_le_one
  simpa only [one_mul] using partialProjection_norm_le e he s

theorem partialProjection_eq_self (he : Orthonormal ℝ e) (s : Finset ι) {i : ι}
    (hi : i ∈ s) : partialProjection e s (e i) = e i := by
  classical
  rw [partialProjection_apply]
  simp [orthonormal_iff_ite.mp he, hi]

theorem partialProjection_tendsto (he : Orthonormal ℝ e) {x : H}
    (hx : x ∈ (Submodule.span ℝ (range e)).topologicalClosure) :
    Tendsto (fun s => partialProjection e s x) atTop (𝓝 x) := by
  classical
  let V : Submodule ℝ H :=
    { carrier := {x | Tendsto (fun s => partialProjection e s x) atTop (𝓝 x)}
      zero_mem' := by simp
      add_mem' := fun ha hb => by simpa only [mem_setOf_eq, map_add] using ha.add hb
      smul_mem' := fun c _ hx => by simpa only [mem_setOf_eq, map_smul] using hx.const_smul c }
  have hspan : Submodule.span ℝ (range e) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact tendsto_atTop_of_eventually_const (i₀ := {i}) fun s hs =>
      partialProjection_eq_self e he s (hs (Finset.mem_singleton_self i))
  have hequi : Equicontinuous (fun s x => partialProjection e s x) :=
    (LipschitzWith.uniformEquicontinuous _ 1 (partialProjection_lipschitz e he)).equicontinuous
  have hclosed : IsClosed (V : Set H) := hequi.isClosed_setOf_tendsto continuous_id
  exact (Submodule.span ℝ (range e)).topologicalClosure_minimal hspan hclosed hx

theorem partialProjection_uniformlyOn_compact (he : Orthonormal ℝ e)
    {K : Set H} (hK : IsCompact K)
    (hspan : K ⊆ (Submodule.span ℝ (range e)).topologicalClosure) :
    TendstoUniformly (fun s (x : K) => partialProjection e s x.val) (fun x => x.val) atTop := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hequi : Equicontinuous (fun s (x : K) => partialProjection e s x.val) :=
    (LipschitzWith.uniformEquicontinuous _ 1 (fun s => by
      simpa only [one_mul, Function.comp_def] using
        (partialProjection_lipschitz e he s).comp
          (isometry_subtype_coe (s := K)).lipschitz)).equicontinuous
  have hpoint : Tendsto (fun s (x : K) => partialProjection e s x.val) atTop
      (𝓝 fun x => x.val) := tendsto_pi_nhds.mpr fun x =>
    partialProjection_tendsto e he (hspan x.property)
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((hequi.tendsto_uniformFun_iff_pi atTop _).mpr hpoint)

theorem partialProjection_comp_tendsto (he : Orthonormal ℝ e)
    (A : H →L[ℝ] H) (hA : IsCompactOperator A)
    (hrange : LinearMap.range A.toLinearMap ≤
      (Submodule.span ℝ (range e)).topologicalClosure) :
    Tendsto (fun s => (partialProjection e s).comp A) atTop (𝓝 A) := by
  let K := closure (A '' Metric.closedBall 0 1)
  have hK : IsCompact K := hA.isCompact_closure_image_closedBall 1
  have hspan : K ⊆ (Submodule.span ℝ (range e)).topologicalClosure := by
    apply closure_minimal
    · rintro _ ⟨x, _, rfl⟩
      exact hrange (LinearMap.mem_range_self A.toLinearMap x)
    · exact Submodule.isClosed_topologicalClosure _
  have hlim := partialProjection_uniformlyOn_compact e he hK hspan
  rw [Metric.tendstoUniformly_iff] at hlim
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hlim (ε / 2) (half_pos hε)] with s hs
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
  intro x hx
  have hxK : A x ∈ K := subset_closure (mem_image_of_mem A
    (by simpa only [Metric.mem_closedBall, dist_zero_right, hx] using (le_refl (1 : ℝ))))
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    dist_eq_norm, norm_sub_rev] using (hs ⟨A x, hxK⟩).le

theorem rankOne_expansion_tendsto (he : Orthonormal ℝ e)
    (A : H →L[ℝ] H) (hA : IsCompactOperator A) (hsymm : A.toLinearMap.IsSymmetric)
    (eigenvalue : ι → ℝ) (heigen : ∀ i, A (e i) = eigenvalue i • e i)
    (hrange : LinearMap.range A.toLinearMap ≤
      (Submodule.span ℝ (range e)).topologicalClosure) :
    Tendsto (fun s : Finset ι =>
      ∑ i ∈ s, eigenvalue i • FunctionalData.tensorProduct (e i) (e i)) atTop (𝓝 A) := by
  convert partialProjection_comp_tendsto e he A hA hrange using 1
  ext s x
  simp only [ContinuousLinearMap.comp_apply, partialProjection_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    FunctionalData.tensorProduct_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hinner : inner ℝ (e i) (A x) = eigenvalue i * inner ℝ (e i) x := by
    calc
      _ = inner ℝ (A (e i)) x := (hsymm (e i) x).symm
      _ = _ := by rw [heigen i, real_inner_smul_left]
  rw [hinner, smul_smul]

theorem countable_of_orthonormal [SecondCountableTopology H] (he : Orthonormal ℝ e) :
    Countable ι := by
  have hdisj : Pairwise (fun i j => Disjoint (Metric.ball (e i) (1 / 2))
      (Metric.ball (e j) (1 / 2))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hsq : dist (e i) (e j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real]
      norm_num [he.norm_eq_one i, he.norm_eq_one j, he.inner_eq_zero hij]
    nlinarith [show 0 ≤ dist (e i) (e j) from dist_nonneg]
  exact hdisj.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => Metric.nonempty_ball.mpr (by norm_num))

end Thesis.DayAhead.CompactSpectralExpansion
