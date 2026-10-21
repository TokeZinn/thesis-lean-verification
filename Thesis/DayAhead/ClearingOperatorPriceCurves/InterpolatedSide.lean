import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic

/-! # Current interpolated supply and demand sides

Unlike the former step-book model, these curves interpolate prices between
cumulative quantities. Zero-volume orders have empty cells and may change the
price from which the next positive-volume interpolation begins. The half-open
cell convention and the separate zero-quantity endpoint are exact.
-/

noncomputable section
namespace Thesis.DayAhead.InterpolatedSide

open Set
open scoped BigOperators

/-- Cumulative order volumes, including the empty sum at index zero. -/
def cumulative {n : ℕ} (volume : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), volume j

theorem cumulative_zero {n : ℕ} (volume : Fin n → ℝ) : cumulative volume 0 = 0 := by
  simp [cumulative]

theorem cumulative_monotone {n : ℕ} (volume : Fin n → ℝ) (hv : ∀ i, 0 ≤ volume i) :
    Monotone (cumulative volume) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact lt_of_lt_of_le (Finset.mem_filter.mp hk).2 hij
  · intro k _ _
    exact hv k

theorem cumulative_increment {n : ℕ} (volume : Fin n → ℝ) (i : Fin n) :
    cumulative volume i.succ - cumulative volume i.castSucc = volume i := by
  classical
  have hfilter : Finset.univ.filter (fun j : Fin n => j.val < i.succ.val) =
      insert i (Finset.univ.filter fun j : Fin n => j.val < i.castSucc.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.val_castSucc]
    constructor
    · intro h
      by_cases heq : j = i
      · exact Or.inl heq
      · exact Or.inr (by have hne : j.val ≠ i.val := fun h => heq (Fin.ext h); omega)
    · rintro (rfl | h) <;> omega
  rw [cumulative, cumulative, hfilter, Finset.sum_insert (by simp)]
  ring

def cell {n : ℕ} (Q : Fin (n + 1) → ℝ) (i : Fin n) : Set ℝ :=
  Ioc (Q i.castSucc) (Q i.succ)

def interpolate (left right pleft pright x : ℝ) : ℝ :=
  ((right - x) * pleft + (x - left) * pright) / (right - left)

/-- Original label: `defn:supply-and-demand-curves`.
`p` is nondecreasing for supply and nonincreasing for demand. -/
def curve {n : ℕ} (p Q : Fin (n + 1) → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x = 0 then p 0 else
    ∑ i : Fin n, if x ∈ cell Q i then
      interpolate (Q i.castSucc) (Q i.succ) (p i.castSucc) (p i.succ) x else 0

theorem curve_zero {n : ℕ} (p Q : Fin (n + 1) → ℝ) : curve p Q 0 = p 0 := by
  simp [curve]

theorem empty_zero_volume_cell {n : ℕ} (Q : Fin (n + 1) → ℝ) (i : Fin n)
    (hi : Q i.castSucc = Q i.succ) : cell Q i = ∅ := by
  simp [cell, hi]

theorem disjoint_cells {n : ℕ} (Q : Fin (n + 1) → ℝ) (hQ : Monotone Q)
    {i j : Fin n} (hij : i ≠ j) : Disjoint (cell Q i) (cell Q j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hidx : i.succ ≤ j.castSucc := by exact_mod_cast hij
    exact (not_lt_of_ge (hxi.2.trans (hQ hidx))) hxj.1
  · have hidx : j.succ ≤ i.castSucc := by exact_mod_cast hji
    exact (not_lt_of_ge (hxj.2.trans (hQ hidx))) hxi.1

/-- Positive-volume cells cover the entire available quantity interval,
including repeated cumulative quantities caused by zero-volume orders. -/
theorem exists_cell {n : ℕ} (Q : Fin (n + 1) → ℝ) (hzero : Q 0 = 0)
    {x : ℝ} (hx : 0 < x) (hxlast : x ≤ Q (Fin.last n)) :
    ∃ i : Fin n, x ∈ cell Q i := by
  classical
  let eligible : Finset (Fin (n + 1)) := Finset.univ.filter fun i => x ≤ Q i
  have hne : eligible.Nonempty := ⟨Fin.last n, by simpa [eligible] using hxlast⟩
  let j := eligible.min' hne
  have hj : x ≤ Q j := (Finset.mem_filter.mp (eligible.min'_mem hne)).2
  have hjne : j ≠ 0 := by
    intro hz
    rw [hz, hzero] at hj
    linarith
  have hjpos : 0 < j.val := by
    by_contra h
    apply hjne
    apply Fin.ext
    change j.val = 0
    omega
  let i : Fin n := ⟨j.val - 1, by omega⟩
  have hisucc : i.succ = j := by apply Fin.ext; dsimp [i]; omega
  refine ⟨i, ?_, ?_⟩
  · change Q i.castSucc < x
    by_contra h
    have hmem : i.castSucc ∈ eligible := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
    have hmin : j ≤ i.castSucc := eligible.min'_le _ hmem
    have : j.val ≤ i.val := hmin
    dsimp [i] at this
    omega
  · change x ≤ Q i.succ
    simpa [hisucc] using hj

theorem curve_on_cell {n : ℕ} (p Q : Fin (n + 1) → ℝ) (hQ : Monotone Q)
    (hzero : Q 0 = 0) (i : Fin n) {x : ℝ} (hx : x ∈ cell Q i) :
    curve p Q x = interpolate (Q i.castSucc) (Q i.succ) (p i.castSucc) (p i.succ) x := by
  have hxpos : 0 < x := (hzero ▸ hQ (Fin.zero_le i.castSucc)).trans_lt hx.1
  rw [curve, if_neg (ne_of_gt hxpos)]
  rw [Finset.sum_eq_single i]
  · simp [hx]
  · intro j _ hji
    have hj : x ∉ cell Q j := fun hj => (disjoint_cells Q hQ hji).le_bot ⟨hj, hx⟩
    simp [hj]
  · simp

theorem interpolate_mem_Icc {l r a b x : ℝ} (hlr : l < r)
    (hx : x ∈ Icc l r) (hab : a ≤ b) : interpolate l r a b x ∈ Icc a b := by
  have hd : 0 < r - l := sub_pos.mpr hlr
  constructor
  · rw [interpolate, le_div_iff₀ hd]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab)]
  · rw [interpolate, div_le_iff₀ hd]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hab)]

theorem interpolate_bounded {l r a b x lo hi : ℝ} (hlr : l < r)
    (hx : x ∈ Icc l r) (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) :
    interpolate l r a b x ∈ Icc lo hi := by
  have hd : 0 < r - l := sub_pos.mpr hlr
  have hleft := sub_nonneg.mpr hx.1
  have hright := sub_nonneg.mpr hx.2
  constructor
  · rw [interpolate, le_div_iff₀ hd]
    nlinarith [mul_nonneg hright (sub_nonneg.mpr ha.1),
      mul_nonneg hleft (sub_nonneg.mpr hb.1)]
  · rw [interpolate, div_le_iff₀ hd]
    nlinarith [mul_nonneg hright (sub_nonneg.mpr ha.2),
      mul_nonneg hleft (sub_nonneg.mpr hb.2)]

theorem curve_bounded {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hQ : Monotone Q) (hzero : Q 0 = 0) (lo hi : ℝ)
    (hp : ∀ i, p i ∈ Icc lo hi) (x : ℝ) (hx : x ∈ Icc 0 (Q (Fin.last n))) :
    curve p Q x ∈ Icc lo hi := by
  by_cases hx0 : x = 0
  · simpa [hx0, curve_zero] using hp 0
  · obtain ⟨i, hi⟩ := exists_cell Q hzero (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hx.2
    rw [curve_on_cell p Q hQ hzero i hi]
    exact interpolate_bounded (hi.1.trans_le hi.2) ⟨hi.1.le, hi.2⟩ (hp _) (hp _)

theorem interpolate_monotone {l r a b : ℝ} (hlr : l < r) (hab : a ≤ b) :
    Monotone (interpolate l r a b) := by
  intro x y hxy
  rw [interpolate, interpolate, div_le_div_iff_of_pos_right (sub_pos.mpr hlr)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hab)]

/-- The interpolated supply function is nondecreasing on its actual domain;
the proof handles zero-volume entries and the separately specified origin. -/
theorem curve_monotoneOn {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Monotone p) (hQ : Monotone Q) (hzero : Q 0 = 0) :
    MonotoneOn (curve p Q) (Icc 0 (Q (Fin.last n))) := by
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · rw [hx0, curve_zero]
    by_cases hy0 : y = 0
    · rw [hy0, curve_zero]
    · obtain ⟨j, hj⟩ := exists_cell Q hzero (lt_of_le_of_ne hy.1 (Ne.symm hy0)) hy.2
      rw [curve_on_cell p Q hQ hzero j hj]
      exact (hp (Fin.zero_le j.castSucc)).trans
        (interpolate_mem_Icc (hx := ⟨hj.1.le, hj.2⟩) (lt_of_lt_of_le hj.1 hj.2)
          (hp (Fin.castSucc_le_succ j))).1
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hypos : 0 < y := hxpos.trans_le hxy
    obtain ⟨i, hi⟩ := exists_cell Q hzero hxpos hx.2
    obtain ⟨j, hj⟩ := exists_cell Q hzero hypos hy.2
    rw [curve_on_cell p Q hQ hzero i hi, curve_on_cell p Q hQ hzero j hj]
    rcases lt_trichotomy i j with hij | heq | hji
    · have hidx : i.succ ≤ j.castSucc := by exact_mod_cast hij
      exact (interpolate_mem_Icc (lt_of_lt_of_le hi.1 hi.2) ⟨hi.1.le, hi.2⟩
        (hp (Fin.castSucc_le_succ i))).2.trans ((hp hidx).trans
          (interpolate_mem_Icc (lt_of_lt_of_le hj.1 hj.2) ⟨hj.1.le, hj.2⟩
            (hp (Fin.castSucc_le_succ j))).1)
    · subst j
      exact interpolate_monotone (lt_of_lt_of_le hi.1 hi.2)
        (hp (Fin.castSucc_le_succ i)) hxy
    · have hidx : j.succ ≤ i.castSucc := by exact_mod_cast hji
      have : y ≤ Q i.castSucc := hj.2.trans (hQ hidx)
      linarith [hi.1]

/-- Every interpolation piece is genuinely affine, without any finite-range
price hypothesis. -/
theorem interpolate_affine (l r a b : ℝ) :
    ∃ slope intercept : ℝ, ∀ x, interpolate l r a b x = slope * x + intercept := by
  refine ⟨(b - a) / (r - l), (r * a - l * b) / (r - l), ?_⟩
  intro x
  unfold interpolate
  ring

theorem curve_on_cell_affine {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hQ : Monotone Q) (hzero : Q 0 = 0) (i : Fin n) :
    ∃ a b : ℝ, ∀ x ∈ cell Q i, curve p Q x = a * x + b := by
  obtain ⟨a, b, hab⟩ := interpolate_affine (Q i.castSucc) (Q i.succ) (p i.castSucc) (p i.succ)
  exact ⟨a, b, fun x hx => (curve_on_cell p Q hQ hzero i hx).trans (hab x)⟩

theorem curve_neg_prices {n : ℕ} (p Q : Fin (n + 1) → ℝ) (x : ℝ) :
    curve (fun i => -p i) Q x = -curve p Q x := by
  classical
  have hinterp (l r a b x : ℝ) : interpolate l r (-a) (-b) x =
      -interpolate l r a b x := by unfold interpolate; ring
  unfold curve
  split_ifs with hx
  · rfl
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp only [hinterp, neg_zero]

/-- The same exact interpolation construction gives the nonincreasing demand
side when its sorted price coordinates are nonincreasing. -/
theorem curve_antitoneOn {n : ℕ} (p Q : Fin (n + 1) → ℝ)
    (hp : Antitone p) (hQ : Monotone Q) (hzero : Q 0 = 0) :
    AntitoneOn (curve p Q) (Icc 0 (Q (Fin.last n))) := by
  have hneg : Monotone (fun i => -p i) := fun i j hij => neg_le_neg (hp hij)
  have hmono := curve_monotoneOn (fun i => -p i) Q hneg hQ hzero
  intro x hx y hy hxy
  have h := hmono hx hy hxy
  rw [curve_neg_prices, curve_neg_prices] at h
  exact neg_le_neg_iff.mp h

/-- Joint Borel measurability of the interpolated side in all price,
cumulative-quantity, and evaluation coordinates. This is an actual finite
formula and includes zero-width cells. -/
theorem measurable_curve {n : ℕ} :
    Measurable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ =>
      curve z.1 z.2.1 z.2.2) := by
  unfold curve cell interpolate
  simp only [mem_Ioc]
  have hz : MeasurableSet {z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ |
      z.2.2 = 0} := (measurableSet_singleton (0 : ℝ)).preimage (by fun_prop)
  apply Measurable.ite hz (by fun_prop)
  apply Finset.measurable_sum
  intro i _
  have hs : MeasurableSet {z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ |
      z.2.1 i.castSucc < z.2.2 ∧ z.2.2 ≤ z.2.1 i.succ} := by
    change MeasurableSet
      ({z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ | z.2.1 i.castSucc < z.2.2} ∩
        {z | z.2.2 ≤ z.2.1 i.succ})
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop))
  apply Measurable.ite hs
  · fun_prop
  · exact measurable_const

end Thesis.DayAhead.InterpolatedSide
