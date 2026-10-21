import Thesis.DayAhead.ClearingOperatorPriceCurves.CompletedInverse
import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedSide

/-! # The exact current excess-supply function and midpoint price

Offered and bid volumes are constructed as suprema of the quantity sets in
the thesis. Their monotonicity and constant exterior tails are derived; the
completed-graph inverse existence theorem then applies to every depth level.
-/

noncomputable section
namespace Thesis.DayAhead.ExcessSupply

open Set

def offeredSet (depth : ℝ) (S : ℝ → ℝ) (p : ℝ) : Set ℝ :=
  insert 0 {q | q ∈ Ioc 0 depth ∧ S q ≤ p}

def offered (depth : ℝ) (S : ℝ → ℝ) (p : ℝ) : ℝ := sSup (offeredSet depth S p)

theorem offeredSet_nonempty (depth : ℝ) (S : ℝ → ℝ) (p : ℝ) :
    (offeredSet depth S p).Nonempty := ⟨0, Or.inl rfl⟩

theorem offeredSet_bddAbove (depth : ℝ) (hd : 0 ≤ depth) (S : ℝ → ℝ) (p : ℝ) :
    BddAbove (offeredSet depth S p) := by
  refine ⟨depth, ?_⟩
  intro q hq
  rcases hq with rfl | hq
  · exact hd
  · exact hq.1.2

theorem offered_bounds (depth : ℝ) (hd : 0 ≤ depth) (S : ℝ → ℝ) (p : ℝ) :
    offered depth S p ∈ Icc 0 depth := by
  exact ⟨le_csSup (offeredSet_bddAbove depth hd S p) (Or.inl rfl),
    csSup_le (offeredSet_nonempty depth S p) (fun _ hq => by
      rcases hq with rfl | hq
      · exact hd
      · exact hq.1.2)⟩

theorem offered_monotone (depth : ℝ) (hd : 0 ≤ depth) (S : ℝ → ℝ) :
    Monotone (offered depth S) := by
  intro p r hpr
  apply csSup_le (offeredSet_nonempty depth S p)
  intro q hq
  apply le_csSup (offeredSet_bddAbove depth hd S r)
  rcases hq with rfl | hq
  · exact Or.inl rfl
  · exact Or.inr ⟨hq.1, hq.2.trans hpr⟩

theorem offered_eq_zero (depth : ℝ) (S : ℝ → ℝ) (p : ℝ)
    (hnone : ∀ q ∈ Ioc 0 depth, ¬S q ≤ p) : offered depth S p = 0 := by
  have hs : offeredSet depth S p = {0} := by
    ext q
    constructor
    · rintro (rfl | hq)
      · exact mem_singleton 0
      · exact False.elim (hnone q hq.1 hq.2)
    · intro hq
      exact Or.inl (mem_singleton_iff.mp hq)
  simp [offered, hs]

theorem offered_eq_depth (depth : ℝ) (hd : 0 ≤ depth) (S : ℝ → ℝ) (p : ℝ)
    (hall : ∀ q ∈ Ioc 0 depth, S q ≤ p) : offered depth S p = depth := by
  apply le_antisymm (offered_bounds depth hd S p).2
  apply le_csSup (offeredSet_bddAbove depth hd S p)
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · exact Or.inl hd0.symm
  · exact Or.inr ⟨⟨hdpos, le_rfl⟩, hall depth ⟨hdpos, le_rfl⟩⟩

/-- Original label: `defn:excess-supply-and-completed-graph`.
Negating demand prices and the threshold expresses the exact `D(q)>=p`
quantity set using the same accepted-volume construction. -/
def excess (sellDepth buyDepth : ℝ) (S D : ℝ → ℝ) (p : ℝ) : ℝ :=
  offered sellDepth S p - offered buyDepth (fun q => -D q) (-p)

theorem excess_monotone (s b : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) (S D : ℝ → ℝ) :
    Monotone (excess s b S D) := by
  intro p r hpr
  exact sub_le_sub (offered_monotone s hs S hpr)
    (offered_monotone b hb (fun q => -D q) (neg_le_neg hpr))

theorem excess_bounds (s b : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) (S D : ℝ → ℝ) (p : ℝ) :
    excess s b S D p ∈ Icc (-b) s := by
  have hS := offered_bounds s hs S p
  have hD := offered_bounds b hb (fun q => -D q) (-p)
  unfold excess
  constructor <;> linarith [hS.1, hS.2, hD.1, hD.2]

theorem excess_lower_tail (lo : ℝ) (s b : ℝ) (hb : 0 ≤ b) (S D : ℝ → ℝ)
    (hS : ∀ q ∈ Ioc 0 s, lo ≤ S q) (hD : ∀ q ∈ Ioc 0 b, lo ≤ D q)
    (p : ℝ) (hp : p < lo) : excess s b S D p = -b := by
  have hsz : offered s S p = 0 := offered_eq_zero s S p (by
    intro q hq h
    have := hS q hq
    linarith)
  have hbd : offered b (fun q => -D q) (-p) = b := offered_eq_depth b hb _ _ (by
    intro q hq
    have := hD q hq
    linarith)
  simp [excess, hsz, hbd]

theorem excess_upper_tail (hi : ℝ) (s b : ℝ) (hs : 0 ≤ s) (S D : ℝ → ℝ)
    (hS : ∀ q ∈ Ioc 0 s, S q ≤ hi) (hD : ∀ q ∈ Ioc 0 b, D q ≤ hi)
    (p : ℝ) (hp : hi < p) : excess s b S D p = s := by
  have hsd : offered s S p = s := offered_eq_depth s hs S p (by
    intro q hq
    exact (hS q hq).trans hp.le)
  have hbz : offered b (fun q => -D q) (-p) = 0 := offered_eq_zero b _ _ (by
    intro q hq h
    have := hD q hq
    linarith)
  simp [excess, hsd, hbz]

/-- Every available-depth completed level is a nonempty compact interval.
This conclusion is derived for the actual supremum-defined excess function. -/
theorem completed_levels_nonempty (lo hi s b : ℝ) (hlohi : lo ≤ hi)
    (hs : 0 ≤ s) (hb : 0 ≤ b) (S D : ℝ → ℝ)
    (hS : ∀ q ∈ Ioc 0 s, S q ∈ Icc lo hi)
    (hD : ∀ q ∈ Ioc 0 b, D q ∈ Icc lo hi)
    (q : ℝ) (hq : q ∈ Icc (-b) s) :
    (CompletedInverse.levelSet lo hi (excess s b S D) q).Nonempty :=
  CompletedInverse.levelSet_nonempty lo hi (-b) s _ hlohi (excess_monotone s b hs hb S D)
    (excess_lower_tail lo s b hb S D (fun q hq => (hS q hq).1) (fun q hq => (hD q hq).1))
    (excess_upper_tail hi s b hs S D (fun q hq => (hS q hq).2) (fun q hq => (hD q hq).2)) q hq

/-- Original label: `defn:positively-matched-state-space-and-price-impact-curve`.
The price clause is implemented for the actual supremum-defined excess supply. -/
def price (lo hi s b : ℝ) (S D : ℝ → ℝ) (q : ℝ) : ℝ :=
  CompletedInverse.midpointPrice lo hi (excess s b S D) q

/-- Original label: `prop:price-impact-curve-properties`, monotonicity clause. -/
theorem price_monotoneOn (lo hi s b : ℝ) (hlohi : lo ≤ hi)
    (hs : 0 ≤ s) (hb : 0 ≤ b) (S D : ℝ → ℝ)
    (hS : ∀ q ∈ Ioc 0 s, S q ∈ Icc lo hi)
    (hD : ∀ q ∈ Ioc 0 b, D q ∈ Icc lo hi) :
    MonotoneOn (price lo hi s b S D) (Icc (-b) s) :=
  CompletedInverse.midpointPrice_monotoneOn lo hi _ (excess_monotone s b hs hb S D)
    _ (completed_levels_nonempty lo hi s b hlohi hs hb S D hS hD)

/-- A sorted interpolated book. The data are the current individual order
volumes and price coordinates; no inverse, clearing, or curve property is
postulated as a field. -/
structure Book (lo hi : ℝ) where
  sellCount : ℕ
  buyCount : ℕ
  sellPrice : Fin (sellCount + 1) → ℝ
  buyPrice : Fin (buyCount + 1) → ℝ
  sellVolume : Fin sellCount → ℝ
  buyVolume : Fin buyCount → ℝ
  sellVolume_nonneg : ∀ i, 0 ≤ sellVolume i
  buyVolume_nonneg : ∀ i, 0 ≤ buyVolume i
  sellPrice_zero : sellPrice 0 = lo
  buyPrice_zero : buyPrice 0 = hi
  sellPrice_monotone : Monotone sellPrice
  buyPrice_antitone : Antitone buyPrice
  sellPrice_bounds : ∀ i, sellPrice i ∈ Icc lo hi
  buyPrice_bounds : ∀ i, buyPrice i ∈ Icc lo hi

namespace Book

open InterpolatedSide

variable {lo hi : ℝ}

def sellDepth (m : Book lo hi) : ℝ := cumulative m.sellVolume (Fin.last m.sellCount)
def buyDepth (m : Book lo hi) : ℝ := cumulative m.buyVolume (Fin.last m.buyCount)

def supply (m : Book lo hi) : ℝ → ℝ := curve m.sellPrice (cumulative m.sellVolume)
def demand (m : Book lo hi) : ℝ → ℝ := curve m.buyPrice (cumulative m.buyVolume)

theorem sellDepth_nonneg (m : Book lo hi) : 0 ≤ m.sellDepth := by
  have h := cumulative_monotone m.sellVolume m.sellVolume_nonneg
    (Fin.zero_le (Fin.last m.sellCount))
  simpa only [cumulative_zero] using h

theorem buyDepth_nonneg (m : Book lo hi) : 0 ≤ m.buyDepth := by
  have h := cumulative_monotone m.buyVolume m.buyVolume_nonneg
    (Fin.zero_le (Fin.last m.buyCount))
  simpa only [cumulative_zero] using h

theorem supply_monotone (m : Book lo hi) : MonotoneOn m.supply (Icc 0 m.sellDepth) :=
  curve_monotoneOn _ _ m.sellPrice_monotone
    (cumulative_monotone m.sellVolume m.sellVolume_nonneg) (cumulative_zero _)

theorem demand_antitone (m : Book lo hi) : AntitoneOn m.demand (Icc 0 m.buyDepth) :=
  curve_antitoneOn _ _ m.buyPrice_antitone
    (cumulative_monotone m.buyVolume m.buyVolume_nonneg) (cumulative_zero _)

theorem supply_bounded (m : Book lo hi) (q : ℝ) (hq : q ∈ Icc 0 m.sellDepth) :
    m.supply q ∈ Icc lo hi :=
  curve_bounded _ _ (cumulative_monotone m.sellVolume m.sellVolume_nonneg)
    (cumulative_zero _) lo hi m.sellPrice_bounds q hq

theorem demand_bounded (m : Book lo hi) (q : ℝ) (hq : q ∈ Icc 0 m.buyDepth) :
    m.demand q ∈ Icc lo hi :=
  curve_bounded _ _ (cumulative_monotone m.buyVolume m.buyVolume_nonneg)
    (cumulative_zero _) lo hi m.buyPrice_bounds q hq

def excess (m : Book lo hi) : ℝ → ℝ :=
  ExcessSupply.excess m.sellDepth m.buyDepth m.supply m.demand

def price (m : Book lo hi) : ℝ → ℝ :=
  ExcessSupply.price lo hi m.sellDepth m.buyDepth m.supply m.demand

def domain (m : Book lo hi) : Set ℝ := Icc (-m.buyDepth) m.sellDepth

theorem zero_mem_domain (m : Book lo hi) : 0 ∈ m.domain :=
  ⟨neg_nonpos.mpr m.buyDepth_nonneg, m.sellDepth_nonneg⟩

theorem completed_level_nonempty (m : Book lo hi) (q : ℝ) (hq : q ∈ m.domain) :
    (CompletedInverse.levelSet lo hi m.excess q).Nonempty :=
  completed_levels_nonempty lo hi _ _ ((m.sellPrice_bounds 0).1.trans (m.sellPrice_bounds 0).2)
    m.sellDepth_nonneg m.buyDepth_nonneg m.supply m.demand
    (fun q hq => m.supply_bounded q ⟨hq.1.le, hq.2⟩)
    (fun q hq => m.demand_bounded q ⟨hq.1.le, hq.2⟩) q hq

theorem price_monotone (m : Book lo hi) : MonotoneOn m.price m.domain :=
  ExcessSupply.price_monotoneOn lo hi _ _ ((m.sellPrice_bounds 0).1.trans (m.sellPrice_bounds 0).2)
    m.sellDepth_nonneg m.buyDepth_nonneg m.supply m.demand
    (fun q hq => m.supply_bounded q ⟨hq.1.le, hq.2⟩)
    (fun q hq => m.demand_bounded q ⟨hq.1.le, hq.2⟩)

theorem price_bounded (m : Book lo hi) (q : ℝ) (hq : q ∈ m.domain) :
    m.price q ∈ Icc lo hi :=
  (CompletedInverse.midpointPrice_mem_levelSet lo hi m.excess
    (excess_monotone _ _ m.sellDepth_nonneg m.buyDepth_nonneg _ _) q
    (m.completed_level_nonempty q hq)).1

/-- Original label: `defn:crossing-price-and-equilibrium-operator`.
The selected crossing price is the same midpoint inverse at zero level.
The equilibrium quantity maximisation clause remains separate. -/
def crossingPrice (m : Book lo hi) : ℝ := m.price 0

theorem price_zero_eq_crossingPrice (m : Book lo hi) : m.price 0 = m.crossingPrice := rfl

end Book

end Thesis.DayAhead.ExcessSupply
