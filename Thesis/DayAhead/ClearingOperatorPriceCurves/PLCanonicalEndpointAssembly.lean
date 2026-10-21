import Thesis.DayAhead.ClearingOperatorPriceCurves.PLCellEndpointEncoding
import Thesis.DayAhead.ClearingOperatorPriceCurves.PLJoinComparison
import Thesis.DayAhead.ClearingOperatorPriceCurves.SidedInterpolation
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Endpoint reconstruction of the actual canonical affine encoding

Each maximal physical affine piece occupies one uniform parameter block.
Interior samples recover its one-sided affine endpoints without choosing
affine witnesses. Only finitely many parameter knots are omitted, which
does not change the source atomless L² class. -/

noncomputable section
namespace Thesis.DayAhead.PLCanonicalEndpointAssembly

open Set MeasureTheory PiecewiseAffinePriceCurves PriceCurves PriceCurveHilbert
open PLCanonicalEncoding PLCellEndpointEncoding PLJoinComparison SidedParametrisation
open scoped BigOperators

def leftBoundary (L R : ℕ) : Fin (L + R) → ℝ :=
  Fin.addCases (fun j : Fin L ↦ (j : ℝ) / L - 1) (fun j : Fin R ↦ (j : ℝ) / R)

def rightBoundary (L R : ℕ) : Fin (L + R) → ℝ :=
  Fin.addCases (fun j : Fin L ↦ ((j : ℝ) + 1) / L - 1)
    (fun j : Fin R ↦ ((j : ℝ) + 1) / R)

def pieceEndpoints (price : ℝ → ℝ) (a b : ℝ) : PricePair × PricePair :=
  (pairEquiv (a, sampledSlope price a b * a + sampledIntercept price a b),
   pairEquiv (b, sampledSlope price a b * b + sampledIntercept price a b))

/-- These sample formulas give exactly the inward one-sided price values
of the affine physical piece, including at a price jump. -/
theorem pieceEndpoints_eq_oneSided (price : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (haff : ∃ A B : ℝ, ∀ x ∈ Ioo a b, price x = A * x + B) :
    pieceEndpoints price a b =
      (pairEquiv (a, price.rightLim a), pairEquiv (b, price.leftLim b)) := by
  have h := FinitePricePathSource.affine_gap_limits price hab
    (affine_eq_sampled price hab haff)
  rw [h.1, h.2.1]
  rfl

def endpointData {L R : ℕ} (price : ℝ → ℝ)
    (kl : Fin (L + 1) → ℝ) (kr : Fin (R + 1) → ℝ) : Endpoints (L + R) :=
  Fin.addCases (fun j ↦ pieceEndpoints price (kl j.castSucc) (kl j.succ))
    (fun j ↦ pieceEndpoints price (kr j.castSucc) (kr j.succ))

def parameterKnots (L R : ℕ) : Set Parameter :=
  (Subtype.val : Parameter → ℝ) ⁻¹'
    (Set.range (fun j : Fin (L + 1) ↦ (j : ℝ) / L - 1) ∪
      Set.range (fun j : Fin (R + 1) ↦ (j : ℝ) / R))

theorem parameterKnots_finite (L R : ℕ) : (parameterKnots L R).Finite :=
  ((Set.finite_range _).union (Set.finite_range _)).preimage Subtype.val_injective.injOn

theorem uniform_block_exists {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hknots : ∀ i : Fin (n + 1), t ≠ (i : ℝ) / n) :
    ∃ j : Fin n, (j : ℝ) / n < t ∧ t < ((j : ℝ) + 1) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnt : 0 ≤ (n : ℝ) * t := mul_nonneg hnR.le ht0.le
  have hk : Nat.floor ((n : ℝ) * t) < n :=
    (Nat.floor_lt hnt).mpr (by nlinarith)
  let j : Fin n := ⟨Nat.floor ((n : ℝ) * t), hk⟩
  have hlo : (j : ℝ) / n ≤ t :=
    (div_le_iff₀ hnR).mpr (by simpa only [j, mul_comm] using Nat.floor_le hnt)
  have hhi : t < ((j : ℝ) + 1) / n :=
    (lt_div_iff₀ hnR).mpr (by
      simpa only [j, mul_comm] using Nat.lt_floor_add_one ((n : ℝ) * t))
  refine ⟨j, lt_of_le_of_ne hlo ?_, hhi⟩
  exact (hknots j.castSucc).symm

theorem uniform_cell_fraction {n : ℕ} (hn : n ≠ 0) (j : Fin n) (s u : ℝ) :
    (u - ((j : ℝ) / n + s)) /
      ((((j : ℝ) + 1) / n + s) - ((j : ℝ) / n + s)) =
      (n : ℝ) * (u - s) - j := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

theorem uniform_block_unique {n : ℕ} (hn : 0 < n) (j k : Fin n) {t : ℝ}
    (hj : (j : ℝ) / n < t ∧ t < ((j : ℝ) + 1) / n)
    (hk : (k : ℝ) / n < t ∧ t ≤ ((k : ℝ) + 1) / n) : k = j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hklt : (k : ℝ) < (j : ℝ) + 1 :=
    (div_lt_div_iff_of_pos_right hnR).mp (hk.1.trans hj.2)
  have hjlt : (j : ℝ) < (k : ℝ) + 1 :=
    (div_lt_div_iff_of_pos_right hnR).mp (hj.1.trans_le hk.2)
  have hkN : k.val < j.val + 1 := by exact_mod_cast hklt
  have hjN : j.val < k.val + 1 := by exact_mod_cast hjlt
  exact Fin.ext (by omega)

theorem left_cell_unique {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (j : Fin L) (u : Parameter)
    (hu : (j : ℝ) / L < (u : ℝ) + 1 ∧ (u : ℝ) + 1 < ((j : ℝ) + 1) / L)
    (hu0 : (u : ℝ) < 0) (i : Fin (L + R))
    (hi : u ∈ cell (leftBoundary L R) (rightBoundary L R) i) :
    i = Fin.castAdd R j := by
  revert hi
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
  · intro hi
    simp only [cell, leftBoundary, rightBoundary, Fin.addCases_left,
      mem_preimage, mem_Ioc] at hi
    have hkj := uniform_block_unique hL j k hu ⟨by linarith [hi.1], by linarith [hi.2]⟩
    exact congrArg (Fin.castAdd R) hkj
  · intro hi
    simp only [cell, leftBoundary, rightBoundary, Fin.addCases_right,
      mem_preimage, mem_Ioc] at hi
    have hnonneg : 0 ≤ (k : ℝ) / R := div_nonneg (by positivity) (by positivity)
    linarith [hi.1]

theorem right_cell_unique {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (j : Fin R) (u : Parameter)
    (hu : (j : ℝ) / R < (u : ℝ) ∧ (u : ℝ) < ((j : ℝ) + 1) / R)
    (hu0 : 0 < (u : ℝ)) (i : Fin (L + R))
    (hi : u ∈ cell (leftBoundary L R) (rightBoundary L R) i) :
    i = Fin.natAdd L j := by
  revert hi
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
  · intro hi
    simp only [cell, leftBoundary, rightBoundary, Fin.addCases_left,
      mem_preimage, mem_Ioc] at hi
    have hnR : (0 : ℝ) < L := by exact_mod_cast hL
    have hkn : (k : ℝ) + 1 ≤ L := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    have hle : ((k : ℝ) + 1) / L ≤ 1 := (div_le_one hnR).mpr hkn
    linarith [hi.2]
  · intro hi
    simp only [cell, leftBoundary, rightBoundary, Fin.addCases_right,
      mem_preimage, mem_Ioc] at hi
    exact congrArg (Fin.natAdd L) (uniform_block_unique hR j k hu ⟨hi.1, hi.2⟩)

theorem graph_of_affine_piece (price : ℝ → ℝ) {a b q t : ℝ}
    (hab : a < b) (hq : q ∈ Ioo a b)
    (haff : ∃ A B : ℝ, ∀ x ∈ Ioo a b, price x = A * x + B)
    (hqt : q = (1 - t) * a + t * b) :
    pairEquiv (q, price q) =
      (1 - t) • (pieceEndpoints price a b).1 + t • (pieceEndpoints price a b).2 := by
  have hp := affine_eq_sampled price hab haff q hq
  simp only [pieceEndpoints]
  rw [← map_smul, ← map_smul, ← map_add]
  apply congrArg pairEquiv
  apply Prod.ext
  · change q = (1 - t) * a + t * b
    exact hqt
  · change price q = (1 - t) * (sampledSlope price a b * a + sampledIntercept price a b) +
      t * (sampledSlope price a b * b + sampledIntercept price a b)
    rw [hp, hqt]
    ring

theorem canonical_encoding_pair (f : Curve) (u : Parameter) :
    pairEquiv (PLCanonicalEncoding.encoding f u) =
      pairEquiv (quantityReal f u, f.price (quantityReal f u)) := rfl

theorem representative_eq_graph_of_unique {n : ℕ} (left right : Fin n → ℝ)
    (z : Endpoints n) (u : Parameter) (j : Fin n)
    (hj : u ∈ cell left right j) (hunique : ∀ i, u ∈ cell left right i → i = j) :
    representative left right z u = graph left right z j u := by
  unfold representative
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem hj _
  · intro i _ hij
    exact indicator_of_notMem (fun hi ↦ hij (hunique i hi)) _
  · simp

theorem canonical_eq_endpoint_pointwise (f : Curve)
    (hL : 0 < leftCount f) (hR : 0 < rightCount f)
    (hl : ∀ j : Fin (leftCount f), ∃ A B : ℝ,
      ∀ x ∈ Ioo (leftKnot f j.castSucc) (leftKnot f j.succ), f.price x = A * x + B)
    (hr : ∀ j : Fin (rightCount f), ∃ A B : ℝ,
      ∀ x ∈ Ioo (rightKnot f j.castSucc) (rightKnot f j.succ), f.price x = A * x + B)
    (u : Parameter) (hu : u ∉ parameterKnots (leftCount f) (rightCount f)) :
    pairEquiv (PLCanonicalEncoding.encoding f u) =
      representative (leftBoundary (leftCount f) (rightCount f))
        (rightBoundary (leftCount f) (rightCount f))
        (endpointData f.price (leftKnot f) (rightKnot f)) u := by
  have hleftNode (j : Fin (leftCount f + 1)) :
      (u : ℝ) ≠ (j : ℝ) / leftCount f - 1 := by
    intro h
    exact hu (Or.inl ⟨j, h.symm⟩)
  have hrightNode (j : Fin (rightCount f + 1)) :
      (u : ℝ) ≠ (j : ℝ) / rightCount f := by
    intro h
    exact hu (Or.inr ⟨j, h.symm⟩)
  have hLne : (leftCount f : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hRne : (rightCount f : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hR
  have hu0 : (u : ℝ) ≠ 0 := by simpa using hrightNode 0
  have huminus : (u : ℝ) ≠ -1 := by simpa using hleftNode 0
  have huplus : (u : ℝ) ≠ 1 := by simpa [hRne] using hrightNode (Fin.last (rightCount f))
  by_cases huside : (u : ℝ) ≤ 0
  · have hu0' : (u : ℝ) < 0 := lt_of_le_of_ne huside hu0
    have ht0 : 0 < (u : ℝ) + 1 := by
      have := lt_of_le_of_ne u.property.1 huminus.symm
      linarith
    have ht1 : (u : ℝ) + 1 < 1 := by linarith
    obtain ⟨j, hj⟩ := uniform_block_exists hL ht0 ht1 (fun i h ↦ hleftNode i (by linarith))
    let a := leftKnot f j.castSucc
    let b := leftKnot f j.succ
    let t := (leftCount f : ℝ) * ((u : ℝ) + 1) - j
    have hab : a < b :=
      (enumeration (leftNodes f) (leftNodes_nonempty f)).strictMono Fin.castSucc_lt_succ
    have hqi : quantityReal f u ∈ Ioo a b := by
      rw [quantityReal, if_pos huside]
      exact uniformInterpolation_block_interior _
        (enumeration (leftNodes f) (leftNodes_nonempty f)).strictMono j hj.1 hj.2
    have hqt : quantityReal f u = (1 - t) * a + t * b := by
      rw [quantityReal, if_pos huside,
        uniformInterpolation_on_block (leftKnot f) j hj.1.le hj.2.le]
      dsimp [a, b, t]
      ring
    have hfrac := uniform_cell_fraction (Nat.ne_of_gt hL) j (-1) (u : ℝ)
    have hfrac' : ((u : ℝ) - ((j : ℝ) / leftCount f - 1)) /
        ((((j : ℝ) + 1) / leftCount f - 1) - ((j : ℝ) / leftCount f - 1)) = t := by
      simpa only [sub_eq_add_neg, neg_neg] using hfrac
    have hgraph : pairEquiv (PLCanonicalEncoding.encoding f u) =
        graph (leftBoundary (leftCount f) (rightCount f))
          (rightBoundary (leftCount f) (rightCount f))
          (endpointData f.price (leftKnot f) (rightKnot f)) (Fin.castAdd (rightCount f) j) u := by
      rw [canonical_encoding_pair]
      simp only [graph, leftBoundary, rightBoundary, endpointData, Fin.addCases_left]
      rw [hfrac']
      exact graph_of_affine_piece f.price hab hqi (hl j) hqt
    have hmem : u ∈ cell (leftBoundary (leftCount f) (rightCount f))
        (rightBoundary (leftCount f) (rightCount f)) (Fin.castAdd (rightCount f) j) := by
      simp only [cell, leftBoundary, rightBoundary, Fin.addCases_left,
        mem_preimage, mem_Ioc]
      constructor <;> linarith [hj.1, hj.2]
    exact hgraph.trans (representative_eq_graph_of_unique _ _ _ u _ hmem
      (left_cell_unique hL hR j u hj hu0')).symm
  · have hu0' : 0 < (u : ℝ) := lt_of_not_ge huside
    have ht1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 huplus
    obtain ⟨j, hj⟩ := uniform_block_exists hR hu0' ht1 hrightNode
    let a := rightKnot f j.castSucc
    let b := rightKnot f j.succ
    let t := (rightCount f : ℝ) * (u : ℝ) - j
    have hab : a < b :=
      (enumeration (rightNodes f) (rightNodes_nonempty f)).strictMono Fin.castSucc_lt_succ
    have hqi : quantityReal f u ∈ Ioo a b := by
      rw [quantityReal, if_neg huside]
      exact uniformInterpolation_block_interior _
        (enumeration (rightNodes f) (rightNodes_nonempty f)).strictMono j hj.1 hj.2
    have hqt : quantityReal f u = (1 - t) * a + t * b := by
      rw [quantityReal, if_neg huside,
        uniformInterpolation_on_block (rightKnot f) j hj.1.le hj.2.le]
      dsimp [a, b, t]
      ring
    have hfrac := uniform_cell_fraction (Nat.ne_of_gt hR) j 0 (u : ℝ)
    have hfrac' : ((u : ℝ) - (j : ℝ) / rightCount f) /
        ((((j : ℝ) + 1) / rightCount f) - (j : ℝ) / rightCount f) = t := by
      simpa only [add_zero, sub_zero] using hfrac
    have hgraph : pairEquiv (PLCanonicalEncoding.encoding f u) =
        graph (leftBoundary (leftCount f) (rightCount f))
          (rightBoundary (leftCount f) (rightCount f))
          (endpointData f.price (leftKnot f) (rightKnot f)) (Fin.natAdd (leftCount f) j) u := by
      rw [canonical_encoding_pair]
      simp only [graph, leftBoundary, rightBoundary, endpointData, Fin.addCases_right]
      rw [hfrac']
      exact graph_of_affine_piece f.price hab hqi (hr j) hqt
    have hmem : u ∈ cell (leftBoundary (leftCount f) (rightCount f))
        (rightBoundary (leftCount f) (rightCount f)) (Fin.natAdd (leftCount f) j) := by
      simpa only [cell, leftBoundary, rightBoundary, Fin.addCases_right,
        mem_preimage, mem_Ioc] using And.intro hj.1 hj.2.le
    exact hgraph.trans (representative_eq_graph_of_unique _ _ _ u _ hmem
      (right_cell_unique hL hR j u hj hu0')).symm

/-- Original label: `prop:pl-encoding-measurable`.
The analytic identification step for the actual canonical node counts. -/
theorem canonical_eq_endpoint_actual_counts (μ : Measure Parameter) [IsFiniteMeasure μ]
    [NoAtoms μ] (f : Curve) (hL : 0 < leftCount f) (hR : 0 < rightCount f)
    (hl : ∀ j : Fin (leftCount f), ∃ A B : ℝ,
      ∀ x ∈ Ioo (leftKnot f j.castSucc) (leftKnot f j.succ), f.price x = A * x + B)
    (hr : ∀ j : Fin (rightCount f), ∃ A B : ℝ,
      ∀ x ∈ Ioo (rightKnot f j.castSucc) (rightKnot f j.succ), f.price x = A * x + B) :
    PLCanonicalEncoding.encodingLp μ f =
      endpointContinuousLinearMap μ (leftBoundary (leftCount f) (rightCount f))
        (rightBoundary (leftCount f) (rightCount f))
        (endpointData f.price (leftKnot f) (rightKnot f)) :=
  canonical_eq_endpoint_off_finite μ f _ _ _ _ (parameterKnots_finite _ _)
    (canonical_eq_endpoint_pointwise f hL hR hl hr)

/-- Original label: `prop:pl-encoding-measurable`.
Fixed comparison-cell coordinates may be substituted for the actual
canonical node arrays. No conclusion identifying the encoding is assumed. -/
theorem canonical_eq_endpoint_fixed_counts (μ : Measure Parameter) [IsFiniteMeasure μ]
    [NoAtoms μ] (f : Curve) {L R : ℕ}
    (kl : Fin (L + 1) → ℝ) (kr : Fin (R + 1) → ℝ)
    (hL : leftCount f = L) (hR : rightCount f = R) (hLpos : 0 < L) (hRpos : 0 < R)
    (hkl : ∀ j : Fin (leftCount f + 1),
      leftKnot f j = kl (Fin.cast (congrArg (fun n ↦ n + 1) hL) j))
    (hkr : ∀ j : Fin (rightCount f + 1),
      rightKnot f j = kr (Fin.cast (congrArg (fun n ↦ n + 1) hR) j))
    (hl : ∀ j : Fin L, ∃ A B : ℝ,
      ∀ x ∈ Ioo (kl j.castSucc) (kl j.succ), f.price x = A * x + B)
    (hr : ∀ j : Fin R, ∃ A B : ℝ,
      ∀ x ∈ Ioo (kr j.castSucc) (kr j.succ), f.price x = A * x + B) :
    PLCanonicalEncoding.encodingLp μ f =
      endpointContinuousLinearMap μ (leftBoundary L R) (rightBoundary L R)
        (endpointData f.price kl kr) := by
  subst L
  subst R
  have hekl : kl = leftKnot f := funext (fun j ↦ (hkl j).symm)
  have hekr : kr = rightKnot f := funext (fun j ↦ (hkr j).symm)
  subst kl
  subst kr
  exact canonical_eq_endpoint_actual_counts μ f hLpos hRpos hl hr

theorem measurable_pieceEndpoints {Ω : Type*} [MeasurableSpace Ω]
    (price : Ω → ℝ → ℝ) (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hf : Measurable (fun w ↦ price w (firstSample (a w) (b w))))
    (hs : Measurable (fun w ↦ price w (secondSample (a w) (b w)))) :
    Measurable (fun w ↦ pieceEndpoints (price w) (a w) (b w)) := by
  have hfirst : Measurable (fun w ↦ firstSample (a w) (b w)) := by
    unfold firstSample
    fun_prop
  have hsecond : Measurable (fun w ↦ secondSample (a w) (b w)) := by
    unfold secondSample
    fun_prop
  have hsl : Measurable (fun w ↦ sampledSlope (price w) (a w) (b w)) :=
    (hs.sub hf).div (hsecond.sub hfirst)
  have hin : Measurable (fun w ↦ sampledIntercept (price w) (a w) (b w)) :=
    hf.sub (hsl.mul hfirst)
  exact ((pairEquiv.continuous.measurable.comp
    (ha.prodMk ((hsl.mul ha).add hin))).prodMk
      (pairEquiv.continuous.measurable.comp (hb.prodMk ((hsl.mul hb).add hin))))

/-- Original label: `prop:pl-encoding-measurable`.
The finite endpoint data are Borel functions of knot coordinates and
the two prescribed interior sample prices on each physical piece. -/
theorem measurable_endpointData {Ω : Type*} [MeasurableSpace Ω] {L R : ℕ}
    (price : Ω → ℝ → ℝ) (kl : Ω → Fin (L + 1) → ℝ) (kr : Ω → Fin (R + 1) → ℝ)
    (hkl : ∀ j, Measurable (fun w ↦ kl w j))
    (hkr : ∀ j, Measurable (fun w ↦ kr w j))
    (hlf : ∀ j : Fin L, Measurable (fun w ↦
      price w (firstSample (kl w j.castSucc) (kl w j.succ))))
    (hls : ∀ j : Fin L, Measurable (fun w ↦
      price w (secondSample (kl w j.castSucc) (kl w j.succ))))
    (hrf : ∀ j : Fin R, Measurable (fun w ↦
      price w (firstSample (kr w j.castSucc) (kr w j.succ))))
    (hrs : ∀ j : Fin R, Measurable (fun w ↦
      price w (secondSample (kr w j.castSucc) (kr w j.succ)))) :
    Measurable (fun w ↦ endpointData (price w) (kl w) (kr w)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa only [endpointData, Fin.addCases_left] using
      measurable_pieceEndpoints price (fun w ↦ kl w j.castSucc) (fun w ↦ kl w j.succ)
        (hkl j.castSucc) (hkl j.succ) (hlf j) (hls j)
  · simpa only [endpointData, Fin.addCases_right] using
      measurable_pieceEndpoints price (fun w ↦ kr w j.castSucc) (fun w ↦ kr w j.succ)
        (hkr j.castSucc) (hkr j.succ) (hrf j) (hrs j)

end Thesis.DayAhead.PLCanonicalEndpointAssembly
