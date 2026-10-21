import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedAcceptanceFormula
import Mathlib.Analysis.Convex.Segment

/-! # Arithmetic horizontal slices of finite monotone polygons

The source transposes a finite completed-excess polygon. On a segment with
positive quantity width its inverse is affine; on a horizontal segment the
fiber is the full price interval. Empty fibers use the global price bounds
as finite-minimum/maximum sentinels. All formulas are Borel arithmetic.
-/
noncomputable section
namespace Thesis.DayAhead.FinitePolygonInverse

open Set MeasureTheory InterpolatedSide

def segmentLeft (a b : ℝ × ℝ) (q : ℝ) : ℝ :=
  if a.2 < b.2 then interpolate a.2 b.2 a.1 b.1 q else a.1

def segmentRight (a b : ℝ × ℝ) (q : ℝ) : ℝ :=
  if a.2 < b.2 then interpolate a.2 b.2 a.1 b.1 q else b.1

theorem interpolate_convex {a b : ℝ} (hab : a ≠ b) (l r x : ℝ) :
    interpolate a b l r x =
      (1 - (x-a)/(b-a))*l + ((x-a)/(b-a))*r := by
  unfold interpolate
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

/-- Exact arithmetic horizontal section of one actual monotone segment. -/
theorem mem_segment_iff {a b : ℝ × ℝ} (hp : a.1 ≤ b.1) (hq : a.2 ≤ b.2)
    (p q : ℝ) :
    (p,q) ∈ segment ℝ a b ↔ q ∈ Icc a.2 b.2 ∧
      p ∈ Icc (segmentLeft a b q) (segmentRight a b q) := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, he⟩
    have heP := congrArg Prod.fst he
    have heQ := congrArg Prod.snd he
    change (1-t)*a.1+t*b.1 = p at heP
    change (1-t)*a.2+t*b.2 = q at heQ
    have hbq : q ∈ Icc a.2 b.2 := by
      constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hq),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hq)]
    refine ⟨hbq, ?_⟩
    by_cases hw : a.2 < b.2
    · have heq : interpolate a.2 b.2 a.1 b.1 q = p := by
        rw [← heQ, ← heP]
        unfold interpolate
        field_simp [sub_ne_zero.mpr hw.ne']
        ring
      simp only [segmentLeft, segmentRight, if_pos hw, heq, mem_Icc, le_refl, and_self]
    · have hab : a.2 = b.2 := le_antisymm hq (le_of_not_gt hw)
      simp only [segmentLeft, segmentRight, if_neg hw, mem_Icc]
      constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hp),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hp)]
  · rintro ⟨hbq, hbp⟩
    by_cases hw : a.2 < b.2
    · simp only [segmentLeft, segmentRight, if_pos hw, mem_Icc] at hbp
      have hpeq := le_antisymm hbp.1 hbp.2
      let t := (q-a.2)/(b.2-a.2)
      have ht : t ∈ Icc (0:ℝ) 1 := by
        refine ⟨div_nonneg (sub_nonneg.mpr hbq.1) (sub_nonneg.mpr hw.le), ?_⟩
        exact (div_le_one (sub_pos.mpr hw)).mpr (sub_le_sub_right hbq.2 _)
      refine ⟨t, ht, Prod.ext ?_ ?_⟩
      · change (1-t)*a.1+t*b.1 = p
        simpa only [t, ← interpolate_convex hw.ne] using hpeq
      · change (1-(q-a.2)/(b.2-a.2))*a.2+((q-a.2)/(b.2-a.2))*b.2 = q
        field_simp [sub_ne_zero.mpr hw.ne']
        ring
    · have heQ : q = a.2 := le_antisymm (hbq.2.trans (le_of_not_gt hw)) hbq.1
      have habQ : a.2 = b.2 := le_antisymm hq (le_of_not_gt hw)
      simp only [segmentLeft, segmentRight, if_neg hw, mem_Icc] at hbp
      by_cases hpw : a.1 < b.1
      · let t := (p-a.1)/(b.1-a.1)
        have ht : t ∈ Icc (0:ℝ) 1 := by
          refine ⟨div_nonneg (sub_nonneg.mpr hbp.1) (sub_nonneg.mpr hpw.le), ?_⟩
          exact (div_le_one (sub_pos.mpr hpw)).mpr (sub_le_sub_right hbp.2 _)
        refine ⟨t, ht, Prod.ext ?_ ?_⟩
        · change (1-(p-a.1)/(b.1-a.1))*a.1+((p-a.1)/(b.1-a.1))*b.1 = p
          field_simp [sub_ne_zero.mpr hpw.ne']
          ring
        · change (1-t)*a.2+t*b.2 = q
          rw [← habQ, heQ]
          ring
      · have habP : a.1 = b.1 := le_antisymm hp (le_of_not_gt hpw)
        have heP : p = a.1 := by linarith
        refine ⟨0, by norm_num, ?_⟩
        simp only [sub_zero, one_smul, zero_smul, add_zero]
        exact Prod.ext heP.symm heQ.symm

/-- Each endpoint of a nonempty horizontal slice belongs to the segment. -/
theorem segment_endpoints_mem {a b : ℝ × ℝ} (hp : a.1 ≤ b.1) (hq : a.2 ≤ b.2)
    {q : ℝ} (h : q ∈ Icc a.2 b.2) :
    (segmentLeft a b q,q) ∈ segment ℝ a b ∧
      (segmentRight a b q,q) ∈ segment ℝ a b := by
  have hlr : segmentLeft a b q ≤ segmentRight a b q := by
    unfold segmentLeft segmentRight
    split_ifs
    · exact le_rfl
    · exact hp
  exact ⟨(mem_segment_iff hp hq _ _).mpr ⟨h, le_rfl, hlr⟩,
    (mem_segment_iff hp hq _ _).mpr ⟨h, hlr, le_rfl⟩⟩

theorem measurable_segmentLeft :
    Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) × ℝ => segmentLeft x.1 x.2.1 x.2.2) := by
  unfold segmentLeft interpolate
  exact (show Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) × ℝ =>
    ((x.2.1.2-x.2.2)*x.1.1+(x.2.2-x.1.2)*x.2.1.1)/(x.2.1.2-x.1.2)) by
      fun_prop).ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)

theorem measurable_segmentRight :
    Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) × ℝ => segmentRight x.1 x.2.1 x.2.2) := by
  unfold segmentRight interpolate
  exact (show Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) × ℝ =>
    ((x.2.1.2-x.2.2)*x.1.1+(x.2.2-x.1.2)*x.2.1.1)/(x.2.1.2-x.1.2)) by
      fun_prop).ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)


def fiber {n : ℕ} (a b : Fin n → ℝ × ℝ) (q : ℝ) : Set ℝ :=
  {p | ∃ i, (p,q) ∈ segment ℝ (a i) (b i)}

def candidateLower (hi : ℝ) (a b : ℝ × ℝ) (q : ℝ) : ℝ :=
  if q ∈ Icc a.2 b.2 then segmentLeft a b q else hi

def candidateUpper (lo : ℝ) (a b : ℝ × ℝ) (q : ℝ) : ℝ :=
  if q ∈ Icc a.2 b.2 then segmentRight a b q else lo

def finiteLower {n : ℕ} (hi : ℝ) (a b : Fin n → ℝ × ℝ) (q : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (n+1))).inf' (by simp)
    (Fin.cases hi (fun i => candidateLower hi (a i) (b i) q))

def finiteUpper {n : ℕ} (lo : ℝ) (a b : Fin n → ℝ × ℝ) (q : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (n+1))).sup' (by simp)
    (Fin.cases lo (fun i => candidateUpper lo (a i) (b i) q))

theorem segment_price_bounds {a b : ℝ × ℝ} (hp : a.1 ≤ b.1)
    {q : ℝ} (hq : q ∈ Icc a.2 b.2) :
    a.1 ≤ segmentLeft a b q ∧ segmentRight a b q ≤ b.1 := by
  unfold segmentLeft segmentRight
  split_ifs with hw
  · exact interpolate_mem_Icc hw hq hp
  · exact ⟨le_rfl, le_rfl⟩

theorem fiber_price_bounds {n : ℕ} {lo hi : ℝ} (a b : Fin n → ℝ × ℝ)
    (hp : ∀ i, (a i).1 ≤ (b i).1) (hq : ∀ i, (a i).2 ≤ (b i).2)
    (hl : ∀ i, lo ≤ (a i).1) (hu : ∀ i, (b i).1 ≤ hi)
    {q p : ℝ} (h : p ∈ fiber a b q) : p ∈ Icc lo hi := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨hvol, hprice⟩ := (mem_segment_iff (hp i) (hq i) p q).mp hi
  have hb := segment_price_bounds (hp i) hvol
  exact ⟨(hl i).trans (hb.1.trans hprice.1), (hprice.2.trans hb.2).trans (hu i)⟩

/-- The minimum of the actual finite polygon fiber is its arithmetic finite
minimum. Invalid segments contribute only the upper price sentinel. -/
theorem sInf_fiber_eq {n : ℕ} {lo hi : ℝ} (a b : Fin n → ℝ × ℝ)
    (hp : ∀ i, (a i).1 ≤ (b i).1) (hq : ∀ i, (a i).2 ≤ (b i).2)
    (hl : ∀ i, lo ≤ (a i).1) (hu : ∀ i, (b i).1 ≤ hi)
    (q : ℝ) (hne : (fiber a b q).Nonempty) :
    sInf (fiber a b q) = finiteLower hi a b q := by
  have hbound : BddBelow (fiber a b q) :=
    ⟨lo, fun p hp' => (fiber_price_bounds a b hp hq hl hu hp').1⟩
  have hsInf_hi : sInf (fiber a b q) ≤ hi := by
    obtain ⟨p, hmem⟩ := hne
    exact (csInf_le hbound hmem).trans (fiber_price_bounds a b hp hq hl hu hmem).2
  apply le_antisymm
  · apply Finset.le_inf'
    intro i _
    refine Fin.cases hsInf_hi (fun j => ?_) i
    change sInf (fiber a b q) ≤ candidateLower hi (a j) (b j) q
    by_cases hvol : q ∈ Icc (a j).2 (b j).2
    · rw [candidateLower, if_pos hvol]
      exact csInf_le hbound ⟨j, (segment_endpoints_mem (hp j) (hq j) hvol).1⟩
    · simpa only [candidateLower, if_neg hvol] using hsInf_hi
  · apply le_csInf hne
    rintro p ⟨i, hseg⟩
    obtain ⟨hvol, hprice⟩ := (mem_segment_iff (hp i) (hq i) p q).mp hseg
    have hle := Finset.inf'_le (Fin.cases hi (fun j => candidateLower hi (a j) (b j) q))
      (Finset.mem_univ i.succ)
    have hle' : finiteLower hi a b q ≤ candidateLower hi (a i) (b i) q := by
      simpa only [finiteLower, Fin.cases_succ] using hle
    exact hle'.trans ((if_pos hvol).trans_le hprice.1)

/-- The maximum of the actual finite polygon fiber is its arithmetic finite
maximum. Invalid segments contribute only the lower price sentinel. -/
theorem sSup_fiber_eq {n : ℕ} {lo hi : ℝ} (a b : Fin n → ℝ × ℝ)
    (hp : ∀ i, (a i).1 ≤ (b i).1) (hq : ∀ i, (a i).2 ≤ (b i).2)
    (hl : ∀ i, lo ≤ (a i).1) (hu : ∀ i, (b i).1 ≤ hi)
    (q : ℝ) (hne : (fiber a b q).Nonempty) :
    sSup (fiber a b q) = finiteUpper lo a b q := by
  have hbound : BddAbove (fiber a b q) :=
    ⟨hi, fun p hp' => (fiber_price_bounds a b hp hq hl hu hp').2⟩
  have hlo_sSup : lo ≤ sSup (fiber a b q) := by
    obtain ⟨p, hmem⟩ := hne
    exact (fiber_price_bounds a b hp hq hl hu hmem).1.trans (le_csSup hbound hmem)
  apply le_antisymm
  · apply csSup_le hne
    rintro p ⟨i, hseg⟩
    obtain ⟨hvol, hprice⟩ := (mem_segment_iff (hp i) (hq i) p q).mp hseg
    have hle := Finset.le_sup' (Fin.cases lo (fun j => candidateUpper lo (a j) (b j) q))
      (Finset.mem_univ i.succ)
    have hle' : candidateUpper lo (a i) (b i) q ≤ finiteUpper lo a b q := by
      simpa only [finiteUpper, Fin.cases_succ] using hle
    exact hprice.2.trans ((if_pos hvol).symm.trans_le hle')
  · apply Finset.sup'_le
    intro i _
    refine Fin.cases hlo_sSup (fun j => ?_) i
    change candidateUpper lo (a j) (b j) q ≤ sSup (fiber a b q)
    by_cases hvol : q ∈ Icc (a j).2 (b j).2
    · rw [candidateUpper, if_pos hvol]
      exact le_csSup hbound ⟨j, (segment_endpoints_mem (hp j) (hq j) hvol).2⟩
    · simpa only [candidateUpper, if_neg hvol] using hlo_sSup


/-- On fixed comparison cells, each segment contributes a Borel arithmetic
endpoint or its harmless exterior sentinel. -/
theorem measurable_candidateLower {A : Type*} [MeasurableSpace A]
    (hi : ℝ) (a b : A → ℝ × ℝ) (q : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hq : Measurable q) :
    Measurable (fun w => candidateLower hi (a w) (b w) (q w)) := by
  have he := measurable_segmentLeft.comp (ha.prodMk (hb.prodMk hq))
  exact he.ite ((measurableSet_le ha.snd hq).inter (measurableSet_le hq hb.snd))
    measurable_const

theorem measurable_candidateUpper {A : Type*} [MeasurableSpace A]
    (lo : ℝ) (a b : A → ℝ × ℝ) (q : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hq : Measurable q) :
    Measurable (fun w => candidateUpper lo (a w) (b w) (q w)) := by
  have he := measurable_segmentRight.comp (ha.prodMk (hb.prodMk hq))
  exact he.ite ((measurableSet_le ha.snd hq).inter (measurableSet_le hq hb.snd))
    measurable_const

theorem measurable_finiteLower {A : Type*} [MeasurableSpace A] {n : ℕ}
    (hi : ℝ) (a b : A → Fin n → ℝ × ℝ) (q : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hq : Measurable q) :
    Measurable (fun w => finiteLower hi (a w) (b w) (q w)) := by
  let f : Fin (n+1) → A → ℝ :=
    fun i w => Fin.cases hi (fun j => candidateLower hi (a w j) (b w j) (q w)) i
  have hsup : Measurable ((Finset.univ : Finset (Fin (n+1))).inf' (by simp) f) := by
    apply Finset.measurable_sup' (α := ℝᵒᵈ) (by simp)
    intro i _
    refine Fin.cases measurable_const (fun j => ?_) i
    exact measurable_candidateLower hi _ _ _
      ((measurable_pi_apply j).comp ha) ((measurable_pi_apply j).comp hb) hq
  convert hsup using 1
  funext w
  exact (Finset.inf'_apply _ f w).symm

theorem measurable_finiteUpper {A : Type*} [MeasurableSpace A] {n : ℕ}
    (lo : ℝ) (a b : A → Fin n → ℝ × ℝ) (q : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hq : Measurable q) :
    Measurable (fun w => finiteUpper lo (a w) (b w) (q w)) := by
  let f : Fin (n+1) → A → ℝ :=
    fun i w => Fin.cases lo (fun j => candidateUpper lo (a w j) (b w j) (q w)) i
  have hsup : Measurable ((Finset.univ : Finset (Fin (n+1))).sup' (by simp) f) := by
    apply Finset.measurable_sup'
    intro i _
    refine Fin.cases measurable_const (fun j => ?_) i
    exact measurable_candidateUpper lo _ _ _
      ((measurable_pi_apply j).comp ha) ((measurable_pi_apply j).comp hb) hq
  convert hsup using 1
  funext w
  exact (Finset.sup'_apply _ f w).symm

/-- The finite polygon midpoint formula itself is Borel, with all dependence
on source vertices explicit. Its identification with an actual market's
completed inverse requires the separately proved graph equality. -/
theorem measurable_finiteMidpoint {A : Type*} [MeasurableSpace A] {n : ℕ}
    (lo hi : ℝ) (a b : A → Fin n → ℝ × ℝ) (q : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hq : Measurable q) :
    Measurable (fun w => (finiteLower hi (a w) (b w) (q w) +
      finiteUpper lo (a w) (b w) (q w))/2) :=
  ((measurable_finiteLower hi a b q ha hb hq).add
    (measurable_finiteUpper lo a b q ha hb hq)).div_const 2

end Thesis.DayAhead.FinitePolygonInverse


