import Thesis.Appendices.DayAheadNumerical.NumericalRepresentation
import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurveHilbert
import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedSide
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Global Euclidean L² realization of the current numerical mass form

Half-open cells choose one of the adjacent price values at a grid knot. This
choice affects finitely many points and therefore does not affect the L²
class. Both coordinates are assembled into one function on [-1,1].
-/

noncomputable section
namespace Thesis.DayAhead.NumericalEmbedding

open Set MeasureTheory NumericalRepresentation PriceCurveHilbert
open scoped BigOperators

def parameterMeasure : Measure ℝ := volume.restrict (Icc (-1 : ℝ) 1)

def openCell (m : ℕ) (i : Fin (2 * m)) : Set ℝ :=
  Ioc (node m i.castSucc) (node m i.succ)

def quantityOnCell {m : ℕ} (z : Values m) (i : Fin (2 * m)) (u : ℝ) : ℝ :=
  (1 - (u - node m i.castSucc) / width m) * z.quantity i.castSucc +
    ((u - node m i.castSucc) / width m) * z.quantity i.succ

def cellGraph {m : ℕ} (z : Values m) (i : Fin (2 * m)) (u : ℝ) : PricePair :=
  pairEquiv (quantityOnCell z i u, z.price i)

def representative {m : ℕ} (z : Values m) (u : ℝ) : PricePair :=
  ∑ i : Fin (2 * m), (openCell m i).indicator (cellGraph z i) u

theorem cellGraph_continuous {m : ℕ} (z : Values m) (i : Fin (2 * m)) :
    Continuous (cellGraph z i) := by
  unfold cellGraph quantityOnCell
  exact pairEquiv.continuous.comp (by fun_prop)

@[simp] theorem quantityOnCell_left {m : ℕ} (z : Values m) (i : Fin (2 * m)) :
    quantityOnCell z i (node m i.castSucc) = z.quantity i.castSucc := by
  simp [quantityOnCell]

@[simp] theorem quantityOnCell_right {m : ℕ} (hm : 0 < m) (z : Values m)
    (i : Fin (2 * m)) : quantityOnCell z i (node m i.succ) = z.quantity i.succ := by
  simp [quantityOnCell, node_succ_sub, (width_pos hm).ne']

theorem continuous_memLp (f : ℝ → PricePair) (hf : Continuous f) :
    MemLp f 2 parameterMeasure := by
  letI : IsFiniteMeasure parameterMeasure := by dsimp [parameterMeasure]; infer_instance
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.norm.continuousOn
  refine MemLp.of_bound hf.measurable.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  exact hC ⟨u, hu, rfl⟩

theorem representative_memLp {m : ℕ} (z : Values m) :
    MemLp (representative z) 2 parameterMeasure := by
  have h := memLp_finset_sum Finset.univ (fun i _ =>
    (continuous_memLp _ (cellGraph_continuous z i)).indicator
      (s := openCell m i) measurableSet_Ioc)
  exact h

def embedding {m : ℕ} (z : Values m) : PriceHilbertSpace parameterMeasure :=
  (representative_memLp z).toLp (representative z)

theorem openCell_disjoint {m : ℕ} (hm : 0 < m) (i j : Fin (2 * m)) (hij : i ≠ j) :
    Disjoint (openCell m i) (openCell m j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hidx : i.succ ≤ j.castSucc := by exact_mod_cast hij
    have h := (node_strictMono hm).monotone hidx
    exact (not_lt_of_ge (hx.2.trans h)) hy.1
  · have hidx : j.succ ≤ i.castSucc := by exact_mod_cast hji
    have h := (node_strictMono hm).monotone hidx
    exact (not_lt_of_ge (hy.2.trans h)) hx.1

theorem representative_on_cell {m : ℕ} (hm : 0 < m) (z : Values m)
    (i : Fin (2 * m)) (u : ℝ) (hu : u ∈ openCell m i) :
    representative z u = cellGraph z i u := by
  classical
  rw [representative, Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hu _
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj =>
      Set.disjoint_left.mp (openCell_disjoint hm j i hji) hj hu) _
  · simp

theorem openCell_union {m : ℕ} (hm : 0 < m) :
    (⋃ i : Fin (2 * m), openCell m i) = Ioc (-1 : ℝ) 1 := by
  ext u
  constructor
  · intro hu
    obtain ⟨i, hi⟩ := mem_iUnion.mp hu
    exact ⟨lt_of_le_of_lt (node_mem_interval hm i.castSucc).1 hi.1,
      hi.2.trans (node_mem_interval hm i.succ).2⟩
  · intro hu
    have hpositive : 0 < u + 1 := by linarith [hu.1]
    obtain ⟨i, hi⟩ := InterpolatedSide.exists_cell
      (fun i : Fin (2 * m + 1) => node m i + 1)
      (by simp [node_zero hm]) hpositive (by simpa [node_last hm] using hu.2)
    exact mem_iUnion.mpr ⟨i, by simpa [openCell, InterpolatedSide.cell] using hi⟩

theorem inner_cellGraph {m : ℕ} (z w : Values m) (i : Fin (2 * m)) (u : ℝ) :
    inner ℝ (cellGraph z i u) (cellGraph w i u) =
      quantityOnCell z i u * quantityOnCell w i u + z.price i * w.price i := by
  simp only [cellGraph, pairEquiv_apply, WithLp.prod_inner_apply]
  change quantityOnCell w i u * quantityOnCell z i u + w.price i * z.price i = _
  ring

theorem integral_cell_inner {m : ℕ} (hm : 0 < m) (z w : Values m) (i : Fin (2 * m)) :
    (∫ u in openCell m i, inner ℝ (cellGraph z i u) (cellGraph w i u)) =
      affineMass (width m) (z.quantity i.castSucc) (z.quantity i.succ)
        (w.quantity i.castSucc) (w.quantity i.succ) + width m * z.price i * w.price i := by
  let l := node m i.castSucc
  let r := node m i.succ
  let h := width m
  have hh : h ≠ 0 := (width_pos hm).ne'
  have hlr : l ≤ r := (node_strictMono hm).monotone (Fin.castSucc_le_succ i)
  have hrl : r = h + l := by dsimp [r, h, l]; linarith [node_succ_sub m i]
  change (∫ u in Ioc l r, inner ℝ (cellGraph z i u) (cellGraph w i u)) = _
  rw [← intervalIntegral.integral_of_le hlr]
  simp_rw [inner_cellGraph]
  have hq : IntervalIntegrable (fun u => quantityOnCell z i u * quantityOnCell w i u)
      volume l r := (by unfold quantityOnCell; fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hq intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul]
  have hchange := intervalIntegral.smul_integral_comp_mul_add
    (fun u => quantityOnCell z i u * quantityOnCell w i u) h l (a := 0) (b := 1)
  simp only [mul_zero, zero_add, mul_one, ← hrl, smul_eq_mul] at hchange
  have hs (s : ℝ) : quantityOnCell z i (h * s + l) =
      (1 - s) * z.quantity i.castSucc + s * z.quantity i.succ := by
    dsimp [quantityOnCell]
    change (1 - (h * s + l - l) / h) * _ + ((h * s + l - l) / h) * _ = _
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hh]
  have ht (s : ℝ) : quantityOnCell w i (h * s + l) =
      (1 - s) * w.quantity i.castSucc + s * w.quantity i.succ := by
    dsimp [quantityOnCell]
    change (1 - (h * s + l - l) / h) * _ + ((h * s + l - l) / h) * _ = _
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hh]
  simp_rw [hs, ht] at hchange
  rw [← hchange, affineMass_exact]
  congr 1
  dsimp [r, l, h]
  rw [node_succ_sub]
  ring

/-- Original label: `prop:app-numerical-inner-product-exact`.
The local mass form is exactly the L² inner product of the two fully
assembled Euclidean-valued interpolants on the common interval. -/
theorem inner_embedding {m : ℕ} (hm : 0 < m) (z w : Values m) :
    inner ℝ (embedding z) (embedding w) = numericalInner z w := by
  rw [L2.inner_def]
  have he : (fun u => inner ℝ (embedding z u) (embedding w u)) =ᵐ[parameterMeasure]
      (fun u => inner ℝ (representative z u) (representative w u)) := by
    filter_upwards [(representative_memLp z).coeFn_toLp,
      (representative_memLp w).coeFn_toLp] with u hz hw
    change inner ℝ ((representative_memLp z).toLp (representative z) u)
      ((representative_memLp w).toLp (representative w) u) = _
    rw [hz, hw]
  rw [integral_congr_ae he]
  change (∫ u in Icc (-1 : ℝ) 1, inner ℝ (representative z u) (representative w u)) = _
  rw [integral_Icc_eq_integral_Ioc, ← openCell_union hm]
  have hcell (i : Fin (2 * m)) :
      IntegrableOn (fun u => inner ℝ (representative z u) (representative w u))
        (openCell m i) volume := by
    have hcont : Continuous (fun u => inner ℝ (cellGraph z i u) (cellGraph w i u)) :=
      (cellGraph_continuous z i).inner (cellGraph_continuous w i)
    have hi : IntegrableOn (fun u => inner ℝ (cellGraph z i u) (cellGraph w i u))
        (Icc (node m i.castSucc) (node m i.succ)) volume := hcont.integrableOn_Icc
    apply (hi.mono_set Ioc_subset_Icc_self).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [representative_on_cell hm z i u hu, representative_on_cell hm w i u hu]
  rw [integral_iUnion_fintype (s := openCell m) (fun _ => measurableSet_Ioc)
    (fun i j hij => openCell_disjoint hm i j hij) hcell, numericalInner]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_cell_inner hm z w i]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  change inner ℝ (representative z u) (representative w u) = _
  rw [representative_on_cell hm z i u hu, representative_on_cell hm w i u hu]

theorem numericalInner_eq_inner (z w : Values 500) :
    numericalInner z w = inner ℝ (embedding z) (embedding w) :=
  (inner_embedding (by norm_num) z w).symm

theorem norm_embedding_sq {m : ℕ} (hm : 0 < m) (z : Values m) :
    ‖embedding z‖ ^ 2 = numericalInner z z := by
  rw [← real_inner_self_eq_norm_sq, inner_embedding hm]

end Thesis.DayAhead.NumericalEmbedding
