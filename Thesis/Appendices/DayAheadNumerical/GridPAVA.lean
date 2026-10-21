import Thesis.Appendices.DayAheadNumerical.PAVA.Fits
import Thesis.Appendices.DayAheadNumerical.GridFits

/-! # PAVA computes the actual grid fits

The terminating adjacent-pooling algorithm is identified with the unique
unweighted Euclidean minimizers, including the current bounded price fit.
The current quantity fit uses unequal endpoint weights; this unweighted
quantity algorithm is a supporting lemma, not that weighted fit.
-/

noncomputable section
namespace Thesis.DayAhead.GridPAVA

open PAVA GridFits

def quantityPAVA {n : ℕ} (u : Vector n) : Vector n :=
  WithLp.toLp 2 fun i => (fit (List.ofFn u))[i.val]'(by
    rw [fit_length, List.length_ofFn]; exact i.isLt)

def pricePAVA {n : ℕ} (lo hi : ℝ) (u : Vector n) : Vector n :=
  WithLp.toLp 2 fun i => (boundedFit lo hi (List.ofFn u))[i.val]'(by
    rw [boundedFit_length, List.length_ofFn]; exact i.isLt)

theorem list_quantityPAVA {n : ℕ} (u : Vector n) :
    List.ofFn (quantityPAVA u) = fit (List.ofFn u) := by
  apply List.ext_getElem
  · simp [fit_length]
  · intro i hi hj
    simp [quantityPAVA]

theorem list_pricePAVA {n : ℕ} (lo hi : ℝ) (u : Vector n) :
    List.ofFn (pricePAVA lo hi u) = boundedFit lo hi (List.ofFn u) := by
  apply List.ext_getElem
  · simp [boundedFit_length]
  · intro i hi hj
    simp [pricePAVA]

theorem monotone_iff_sorted {n : ℕ} (u : Vector n) :
    Monotone u ↔ (List.ofFn u).Pairwise (· ≤ ·) := by
  rw [List.pairwise_ofFn]
  constructor
  · intro h i j hij; exact h hij.le
  · intro h i j hij
    rcases lt_or_eq_of_le hij with hlt | rfl
    · exact h hlt
    · rfl

theorem quantityPAVA_monotone {n : ℕ} (u : Vector n) : Monotone (quantityPAVA u) := by
  rw [monotone_iff_sorted, list_quantityPAVA]
  exact fit_sorted _

theorem pricePAVA_monotone {n : ℕ} (lo hi : ℝ) (u : Vector n) : Monotone (pricePAVA lo hi u) := by
  rw [monotone_iff_sorted, list_pricePAVA]
  exact boundedFit_sorted _ _ _

theorem pricePAVA_bounds {n : ℕ} {lo hi : ℝ} (h : lo ≤ hi) (u : Vector n) (i : Fin n) :
    pricePAVA lo hi u i ∈ Set.Icc lo hi := by
  apply boundedFit_mem h (List.ofFn u)
  change (boundedFit lo hi (List.ofFn u))[i.val]'(by
    rw [boundedFit_length, List.length_ofFn]; exact i.isLt) ∈ _
  exact List.getElem_mem _

theorem loss_ofFn {n : ℕ} (u v : Vector n) :
    loss (List.ofFn u) (List.ofFn v) = squaredLoss u v := by
  have hz : List.zipWith (fun x y => (x-y)^2) (List.ofFn u) (List.ofFn v) =
      List.ofFn (fun i => (u i - v i)^2) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  simp only [loss, hz, List.sum_ofFn, squaredLoss]

theorem quantityPAVA_minimal {n : ℕ} (u v : Vector n) (hv : Monotone v) :
    squaredLoss u (quantityPAVA u) ≤ squaredLoss u v := by
  rw [← loss_ofFn, ← loss_ofFn, list_quantityPAVA]
  exact fit_minimal _ _ (by simp) ((monotone_iff_sorted v).mp hv)

theorem pricePAVA_minimal {n : ℕ} {lo hi : ℝ} (h : lo ≤ hi) (u v : Vector n)
    (hv : v ∈ priceSet n lo hi) : squaredLoss u (pricePAVA lo hi u) ≤ squaredLoss u v := by
  rw [← loss_ofFn, ← loss_ofFn, list_pricePAVA]
  apply boundedFit_minimal _ _ (by simp) ((monotone_iff_sorted v).mp hv.1) h
  intro y hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  exact hv.2 i

theorem minimizer_eq_choice {n : ℕ} (u p : Vector n) (C : Set (Vector n))
    (hex : ∃! q : Vector n, q ∈ C ∧ ‖u - q‖ = ⨅ v : C, ‖u - (v : Vector n)‖)
    (hp : p ∈ C) (hmin : ∀ v ∈ C, squaredLoss u p ≤ squaredLoss u v) : p = hex.choose := by
  have hpq := hmin hex.choose hex.choose_spec.1.1
  have hqp := squaredLoss_minimal hex.choose_spec.1.2 hp
  rw [squaredLoss_eq_norm_sq, squaredLoss_eq_norm_sq] at hpq hqp
  have hn := (sq_eq_sq₀ (norm_nonneg (u - p)) (norm_nonneg (u - hex.choose))).mp
    (le_antisymm hpq hqp)
  exact hex.choose_spec.2 p ⟨hp, hn.trans hex.choose_spec.1.2⟩

/-- The algorithm computes the quantity optimizer, for every input vector. -/
theorem quantityPAVA_eq_quantityFit {n : ℕ} (u : Vector n) : quantityPAVA u = quantityFit u :=
  minimizer_eq_choice u _ (quantitySet n) (quantityFit_existsUnique n u)
    (quantityPAVA_monotone u) (fun v hv => quantityPAVA_minimal u v hv)

/-- Pooling followed by clipping computes the bounded price optimizer. -/
theorem pricePAVA_eq_priceFit {n : ℕ} {lo hi : ℝ} (h : lo ≤ hi) (u : Vector n) :
    pricePAVA lo hi u = priceFit lo hi h u :=
  minimizer_eq_choice u _ (priceSet n lo hi) (priceFit_existsUnique n lo hi h u)
    ⟨pricePAVA_monotone lo hi u, pricePAVA_bounds h u⟩
    (fun v hv => pricePAVA_minimal h u v hv)

end Thesis.DayAhead.GridPAVA
