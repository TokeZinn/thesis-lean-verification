import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-! # The finite-dimensional Moore–Penrose inverse

Construct the inverse on the orthogonal complement of the kernel, then project
the response onto the range. No full-rank hypothesis or ridge penalty is used.
This supplies the singular-design convention in the intraday simulator appendix.
-/

noncomputable section
namespace Thesis.MoorePenrose

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E]

def restricted (A : E →ₗ[ℝ] F) : A.kerᗮ →ₗ[ℝ] A.range :=
  A.rangeRestrict.comp A.kerᗮ.subtype

omit [FiniteDimensional ℝ E] in
theorem restricted_injective (A : E →ₗ[ℝ] F) : Function.Injective (restricted A) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hAx : A x = 0 := congrArg Subtype.val hx
  have hx0 : (x : E) = 0 := by
    have hinner := x.property x (show (x : E) ∈ A.ker from hAx)
    exact inner_self_eq_zero.mp hinner
  simpa only [Submodule.mem_bot, Subtype.ext_iff, Submodule.coe_zero] using hx0

theorem map_kernel_complement (A : E →ₗ[ℝ] F) (x : E) :
    A (A.kerᗮ.starProjection x) = A x := by
  rw [Submodule.starProjection_orthogonal_val, map_sub]
  have h : A (A.ker.starProjection x) = 0 := A.ker.starProjection_apply_mem x
  rw [h, sub_zero]

theorem restricted_surjective (A : E →ₗ[ℝ] F) : Function.Surjective (restricted A) := by
  rintro ⟨y, x, rfl⟩
  refine ⟨A.kerᗮ.orthogonalProjection x, ?_⟩
  apply Subtype.ext
  exact map_kernel_complement A x

def rangeEquiv (A : E →ₗ[ℝ] F) : A.kerᗮ ≃ₗ[ℝ] A.range :=
  LinearEquiv.ofBijective (restricted A)
    ⟨restricted_injective A, restricted_surjective A⟩

def inverse (A : E →ₗ[ℝ] F) : F →ₗ[ℝ] E :=
  A.kerᗮ.subtype.comp ((rangeEquiv A).symm.toLinearMap.comp
    A.range.orthogonalProjection.toLinearMap)

theorem inverse_mem (A : E →ₗ[ℝ] F) (y : F) : inverse A y ∈ A.kerᗮ :=
  ((rangeEquiv A).symm (A.range.orthogonalProjection y)).property

theorem map_inverse (A : E →ₗ[ℝ] F) (y : F) :
    A (inverse A y) = A.range.starProjection y := by
  exact congrArg Subtype.val ((rangeEquiv A).apply_symm_apply
    (A.range.orthogonalProjection y))

theorem inverse_map (A : E →ₗ[ℝ] F) (x : E) :
    inverse A (A x) = A.kerᗮ.starProjection x := by
  have h : (⟨inverse A (A x), inverse_mem A (A x)⟩ : A.kerᗮ) =
      A.kerᗮ.orthogonalProjection x := by
    apply restricted_injective A
    apply Subtype.ext
    change A (inverse A (A x)) = A (A.kerᗮ.starProjection x)
    rw [map_inverse, map_kernel_complement]
    exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self A x)
  exact congrArg Subtype.val h

theorem first_penrose (A : E →ₗ[ℝ] F) : A.comp ((inverse A).comp A) = A := by
  ext x
  exact (map_inverse A (A x)).trans
    (Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self A x))

theorem second_penrose (A : E →ₗ[ℝ] F) :
    (inverse A).comp (A.comp (inverse A)) = inverse A := by
  ext y
  exact (inverse_map A (inverse A y)).trans
    (Submodule.starProjection_eq_self_iff.mpr (inverse_mem A y))

theorem third_penrose (A : E →ₗ[ℝ] F) : (A.comp (inverse A)).IsSymmetric := by
  have h : A.comp (inverse A) = A.range.starProjection.toLinearMap := by
    ext y
    exact map_inverse A y
  rw [h]
  exact A.range.starProjection_isSymmetric

theorem fourth_penrose (A : E →ₗ[ℝ] F) : ((inverse A).comp A).IsSymmetric := by
  have h : (inverse A).comp A = A.kerᗮ.starProjection.toLinearMap := by
    ext x
    exact inverse_map A x
  rw [h]
  exact A.kerᗮ.starProjection_isSymmetric

theorem least_squares (A : E →ₗ[ℝ] F) (y : F) (x : E) :
    ‖y - A (inverse A y)‖ ≤ ‖y - A x‖ := by
  rw [map_inverse, Submodule.starProjection_minimal]
  exact ciInf_le (bddBelow_def.mpr ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩)
    (⟨A x, LinearMap.mem_range_self A x⟩ : A.range)

theorem least_squares_sq (A : E →ₗ[ℝ] F) (y : F) (x : E) :
    ‖y - A (inverse A y)‖ ^ 2 ≤ ‖y - A x‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (least_squares A y x) 2

theorem minimum_norm (A : E →ₗ[ℝ] F) (y : F) (x : E)
    (hx : A x = A (inverse A y)) : ‖inverse A y‖ ≤ ‖x‖ := by
  have h : inverse A y = A.kerᗮ.starProjection x := by
    rw [← inverse_map, hx, inverse_map]
    exact (Submodule.starProjection_eq_self_iff.mpr (inverse_mem A y)).symm
  rw [h]
  exact A.kerᗮ.norm_starProjection_apply_le x

theorem minimum_norm_unique (A : E →ₗ[ℝ] F) (y : F) (x : E)
    (hx : A x = A (inverse A y)) (hn : ‖x‖ ≤ ‖inverse A y‖) : x = inverse A y := by
  have h : inverse A y = A.kerᗮ.starProjection x := by
    rw [← inverse_map, hx, inverse_map]
    exact (Submodule.starProjection_eq_self_iff.mpr (inverse_mem A y)).symm
  have hm : x ∈ A.kerᗮ := (A.kerᗮ.mem_iff_norm_starProjection x).mpr
    (le_antisymm (A.kerᗮ.norm_starProjection_apply_le x) (h ▸ hn))
  exact (Submodule.starProjection_eq_self_iff.mpr hm).symm.trans h.symm

theorem residual_orthogonal (A : E →ₗ[ℝ] F) (y : F) :
    y - A (inverse A y) ∈ A.rangeᗮ := by
  rw [map_inverse]
  exact A.range.sub_starProjection_mem_orthogonal y

theorem loss_decomposition (A : E →ₗ[ℝ] F) (y : F) (x : E) :
    ‖y - A x‖ ^ 2 = ‖y - A (inverse A y)‖ ^ 2 +
      ‖A (inverse A y) - A x‖ ^ 2 := by
  have h : inner ℝ (y - A (inverse A y)) (A (inverse A y) - A x) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (residual_orthogonal A y) _
      (A.range.sub_mem (LinearMap.mem_range_self A _) (LinearMap.mem_range_self A _))
  simpa only [sub_add_sub_cancel, pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real h

theorem minimizer_iff (A : E →ₗ[ℝ] F) (y : F) (x : E) :
    (∀ z, ‖y - A x‖ ^ 2 ≤ ‖y - A z‖ ^ 2) ↔ A x = A (inverse A y) := by
  constructor
  · intro h
    have hd := loss_decomposition A y x
    have hh := h (inverse A y)
    have hn : ‖A (inverse A y) - A x‖ = 0 := by nlinarith [sq_nonneg ‖A (inverse A y) - A x‖]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  · intro h z
    rw [h]
    exact least_squares_sq A y z

theorem unique_minimum_norm_minimizer (A : E →ₗ[ℝ] F) (y : F) (x : E)
    (hx : ∀ z, ‖y - A x‖ ^ 2 ≤ ‖y - A z‖ ^ 2)
    (hn : ‖x‖ ≤ ‖inverse A y‖) : x = inverse A y :=
  minimum_norm_unique A y x ((minimizer_iff A y x).mp hx) hn

theorem coefficient_norm_decomposition (A : E →ₗ[ℝ] F) (y : F) (x : E)
    (hx : A x = A (inverse A y)) :
    ‖x‖ ^ 2 = ‖inverse A y‖ ^ 2 + ‖x - inverse A y‖ ^ 2 := by
  have hk : x - inverse A y ∈ A.ker := by
    change A (x - inverse A y) = 0
    rw [map_sub, hx, sub_self]
  have h : inner ℝ (inverse A y) (x - inverse A y) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (inverse_mem A y) _ hk
  simpa only [add_sub_cancel, pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real h

end Thesis.MoorePenrose
