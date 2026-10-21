import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! # The current midpoint inverse of a completed monotone graph

The level set uses the actual one-sided limits, not a certificate assuming
the desired inverse exists. Constant tails outside the admissible price
interval provide existence at every available-depth level, including endpoints.
-/

noncomputable section
namespace Thesis.DayAhead.CompletedInverse

open Set Filter Topology

/-- Original label: `defn:excess-supply-and-completed-graph`. -/
def levelSet (lo hi : ℝ) (E : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {p | p ∈ Icc lo hi ∧ E.leftLim p ≤ q ∧ q ≤ E.rightLim p}

theorem leftLim_le_iff (E : ℝ → ℝ) (hE : Monotone E) (p q : ℝ) :
    E.leftLim p ≤ q ↔ ∀ x < p, E x ≤ q := by
  constructor
  · intro h x hx
    exact (hE.le_leftLim hx).trans h
  · intro h
    rw [hE.leftLim_eq_sSup (by exact neBot_iff.mp inferInstance)]
    apply csSup_le (by exact ⟨E (p - 1), ⟨p - 1, by simp, rfl⟩⟩)
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx

theorem le_rightLim_iff (E : ℝ → ℝ) (hE : Monotone E) (p q : ℝ) :
    q ≤ E.rightLim p ↔ ∀ x, p < x → q ≤ E x := by
  constructor
  · intro h x hx
    exact h.trans (hE.rightLim_le hx)
  · intro h
    rw [hE.rightLim_eq_sInf (by exact neBot_iff.mp inferInstance)]
    apply le_csInf (by exact ⟨E (p + 1), ⟨p + 1, by simp, rfl⟩⟩)
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx

theorem levelSet_eq_closed_intersections (lo hi : ℝ) (E : ℝ → ℝ) (hE : Monotone E)
    (q : ℝ) :
    levelSet lo hi E q = Icc lo hi ∩
      (⋂ x : {x : ℝ // q < E x}, Iic (x : ℝ)) ∩
      (⋂ x : {x : ℝ // E x < q}, Ici (x : ℝ)) := by
  ext p
  simp only [levelSet, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_Iic, mem_Ici]
  rw [leftLim_le_iff E hE, le_rightLim_iff E hE]
  constructor
  · rintro ⟨hp, hl, hr⟩
    refine ⟨⟨hp, fun x => ?_⟩, fun x => ?_⟩
    · by_contra h
      have := hl x.val (lt_of_not_ge h)
      linarith [x.property]
    · by_contra h
      have := hr x.val (lt_of_not_ge h)
      linarith [x.property]
  · rintro ⟨⟨hp, hl⟩, hr⟩
    refine ⟨hp, ?_, ?_⟩
    · intro x hx
      by_contra h
      have := hl ⟨x, lt_of_not_ge h⟩
      linarith
    · intro x hx
      by_contra h
      have := hr ⟨x, lt_of_not_ge h⟩
      linarith

/-- Alternative route for `prop:price-impact-curve-properties` (not the mapped
proof): closedness of the level set as an intersection of closed half-lines, for
an arbitrary monotone `E`.  The thesis derives closedness of `J_m(q)` from the
completed graph being a finite union of closed segments; for the actual book that
argument is `FinitePricePathSource.actual_levelSet_compact`. -/
theorem levelSet_closed (lo hi : ℝ) (E : ℝ → ℝ) (hE : Monotone E) (q : ℝ) :
    IsClosed (levelSet lo hi E q) := by
  rw [levelSet_eq_closed_intersections lo hi E hE q]
  exact (isClosed_Icc.inter (isClosed_iInter fun _ => isClosed_Iic)).inter
    (isClosed_iInter fun _ => isClosed_Ici)

theorem levelSet_compact (lo hi : ℝ) (E : ℝ → ℝ) (hE : Monotone E) (q : ℝ) :
    IsCompact (levelSet lo hi E q) :=
  isCompact_Icc.of_isClosed_subset (levelSet_closed lo hi E hE q) fun _ hp => hp.1

theorem levelSet_ordConnected (lo hi : ℝ) (E : ℝ → ℝ) (hE : Monotone E) (q : ℝ) :
    OrdConnected (levelSet lo hi E q) := by
  refine ⟨?_⟩
  intro p hp r hr x hx
  exact ⟨⟨hp.1.1.trans hx.1, hx.2.trans hr.1.2⟩,
    (hE.leftLim hx.2).trans hr.2.1, hp.2.2.trans (hE.rightLim hx.1)⟩

/-- Alternative route for `prop:price-impact-curve-properties` (not the mapped
proof): existence is derived from order completeness (`sup {p | E p < q}`) and
constant endpoint tails, for an arbitrary monotone `E`; no continuity or strict
monotonicity is assumed.  The thesis derives nonemptiness of `J_m(q)` from the
connected finite polygonal segment cover of the completed graph; for the actual
book that argument is `FinitePricePathSource.actual_levelSet_nonempty`. -/
theorem levelSet_nonempty (lo hi lower upper : ℝ) (E : ℝ → ℝ)
    (hlohi : lo ≤ hi) (hE : Monotone E)
    (hlower : ∀ p < lo, E p = lower) (hupper : ∀ p, hi < p → E p = upper)
    (q : ℝ) (hq : q ∈ Icc lower upper) : (levelSet lo hi E q).Nonempty := by
  by_cases hql : q = lower
  · refine ⟨lo, ⟨⟨le_rfl, hlohi⟩, ?_, ?_⟩⟩
    · apply (leftLim_le_iff E hE lo q).mpr
      intro x hx
      rw [hlower x hx, hql]
    · apply (le_rightLim_iff E hE lo q).mpr
      intro x hx
      have h := hE (show lo - 1 ≤ x by linarith)
      rw [hlower (lo - 1) (by linarith)] at h
      simpa [hql] using h
  by_cases hqu : q = upper
  · refine ⟨hi, ⟨⟨hlohi, le_rfl⟩, ?_, ?_⟩⟩
    · apply (leftLim_le_iff E hE hi q).mpr
      intro x hx
      have h := hE (show x ≤ hi + 1 by linarith)
      rw [hupper (hi + 1) (by linarith)] at h
      simpa [hqu] using h
    · apply (le_rightLim_iff E hE hi q).mpr
      intro x hx
      rw [hupper x hx, hqu]
  have hlq : lower < q := lt_of_le_of_ne hq.1 (Ne.symm hql)
  have hqu' : q < upper := lt_of_le_of_ne hq.2 hqu
  let A : Set ℝ := {p | E p < q}
  have hAne : A.Nonempty := ⟨lo - 1, by simp [A, hlower (lo - 1) (by linarith), hlq]⟩
  have hhiUpper : ∀ x ∈ A, x ≤ hi := by
    intro x hx
    by_contra h
    have hxhi : hi < x := lt_of_not_ge h
    have he := hupper x hxhi
    change E x < q at hx
    linarith
  have hAbdd : BddAbove A := ⟨hi, hhiUpper⟩
  have hpupper : sSup A ≤ hi := csSup_le hAne hhiUpper
  have hplower : lo ≤ sSup A := by
    apply le_of_forall_lt
    intro x hx
    obtain ⟨y, hxy, hy⟩ := exists_between hx
    apply hxy.trans_le
    apply le_csSup hAbdd
    change E y < q
    simpa [hlower y hy] using hlq
  refine ⟨sSup A, ⟨⟨hplower, hpupper⟩, ?_, ?_⟩⟩
  · apply (leftLim_le_iff E hE (sSup A) q).mpr
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (lt_csSup_iff hAbdd hAne).mp hx
    exact (hE hxy.le).trans (le_of_lt hy)
  · apply (le_rightLim_iff E hE (sSup A) q).mpr
    intro x hx
    by_contra h
    have hxA : x ∈ A := lt_of_not_ge h
    have := le_csSup hAbdd hxA
    linarith

def midpointPrice (lo hi : ℝ) (E : ℝ → ℝ) (q : ℝ) : ℝ :=
  (sInf (levelSet lo hi E q) + sSup (levelSet lo hi E q)) / 2

theorem levelSet_eq_Icc (lo hi : ℝ) (E : ℝ → ℝ) (hE : Monotone E) (q : ℝ)
    (hne : (levelSet lo hi E q).Nonempty) :
    levelSet lo hi E q = Icc (sInf (levelSet lo hi E q)) (sSup (levelSet lo hi E q)) := by
  have hc := levelSet_compact lo hi E hE q
  have hlow := hc.sInf_mem hne
  have hupp := hc.sSup_mem hne
  ext p
  constructor
  · intro hp
    exact ⟨csInf_le hc.bddBelow hp, le_csSup hc.bddAbove hp⟩
  · intro hp
    exact (levelSet_ordConnected lo hi E hE q).out hlow hupp hp

theorem midpointPrice_mem_levelSet (lo hi : ℝ) (E : ℝ → ℝ) (hE : Monotone E) (q : ℝ)
    (hne : (levelSet lo hi E q).Nonempty) : midpointPrice lo hi E q ∈ levelSet lo hi E q := by
  have hc := levelSet_compact lo hi E hE q
  have horder : sInf (levelSet lo hi E q) ≤ sSup (levelSet lo hi E q) :=
    csInf_le hc.bddBelow (hc.sSup_mem hne)
  rw [levelSet_eq_Icc lo hi E hE q hne]
  unfold midpointPrice
  constructor <;> linarith

/-- The midpoint-selected inverse is monotone on every set of levels for
which the completed level sets are nonempty. -/
theorem midpointPrice_monotoneOn (lo hi : ℝ) (E : ℝ → ℝ) (hE : Monotone E)
    (D : Set ℝ) (hne : ∀ q ∈ D, (levelSet lo hi E q).Nonempty) :
    MonotoneOn (midpointPrice lo hi E) D := by
  intro q hq r hr hqr
  rcases eq_or_lt_of_le hqr with rfl | hqr'
  · rfl
  have hqc := levelSet_compact lo hi E hE q
  have hrc := levelSet_compact lo hi E hE r
  have hqmax := hqc.sSup_mem (hne q hq)
  have hrmin := hrc.sInf_mem (hne r hr)
  have hsep : sSup (levelSet lo hi E q) ≤ sInf (levelSet lo hi E r) := by
    by_contra h
    have hp := hE.rightLim_le_leftLim (lt_of_not_ge h)
    linarith [hqmax.2.1, hrmin.2.2]
  have hqord := csInf_le hqc.bddBelow hqmax
  have hrord := le_csSup hrc.bddAbove hrmin
  unfold midpointPrice
  linarith

end Thesis.DayAhead.CompletedInverse
