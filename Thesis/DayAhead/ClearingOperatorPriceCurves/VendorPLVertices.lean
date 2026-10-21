import Thesis.DayAhead.ClearingOperatorPriceCurves.VendorPLParser
import Thesis.DayAhead.ClearingOperatorPriceCurves.InterpolatedAcceptanceLimits

/-! # The actual finite one-sided vertices of vendor excess supply

Both one-sided excess values are arithmetic finite maxima of the parsed
lists. Negating the demand threshold exchanges the two sides of the limit.
Every coordinate is Borel on each raw-list length layer. These are the actual
completed-graph vertices, rather than a step-book replacement.
-/
noncomputable section
namespace Thesis.DayAhead.VendorPLVertices

open Set Filter MeasureTheory InterpolatedSide ExcessSupply
open VendorPLParser InterpolatedAcceptanceFormula InterpolatedAcceptanceLimits
open scoped Topology

def lowerVertex {lo hi : ℝ} (m : Book lo hi) (p : ℝ) : ℝ :=
  finiteAcceptedLeft m.sellPrice (InterpolatedSide.cumulative m.sellVolume) p -
    finiteAccepted (fun i => -m.buyPrice i) (InterpolatedSide.cumulative m.buyVolume) (-p)

def upperVertex {lo hi : ℝ} (m : Book lo hi) (p : ℝ) : ℝ :=
  finiteAccepted m.sellPrice (InterpolatedSide.cumulative m.sellVolume) p -
    finiteAcceptedLeft (fun i => -m.buyPrice i) (InterpolatedSide.cumulative m.buyVolume) (-p)

theorem excess_eq_offered_difference {lo hi : ℝ} (m : Book lo hi) :
    m.excess = fun p =>
      offered m.sellDepth (curve m.sellPrice (InterpolatedSide.cumulative m.sellVolume)) p -
      offered m.buyDepth
        (curve (fun i => -m.buyPrice i) (InterpolatedSide.cumulative m.buyVolume)) (-p) := by
  funext p
  simp only [Book.excess, ExcessSupply.excess, Book.supply, Book.demand]
  congr 2
  funext q
  exact (curve_neg_prices _ _ q).symm

theorem excess_tendsto_left {lo hi : ℝ} (m : Book lo hi) (p : ℝ) :
    Tendsto m.excess (𝓝[<] p) (𝓝 (lowerVertex m p)) := by
  have hs := offered_tendsto_left m.sellPrice (InterpolatedSide.cumulative m.sellVolume)
    m.sellPrice_monotone (cumulative_monotone _ m.sellVolume_nonneg) (cumulative_zero _) p
  have hb := offered_tendsto_right (fun i => -m.buyPrice i)
    (InterpolatedSide.cumulative m.buyVolume)
    (fun i j hij => neg_le_neg (m.buyPrice_antitone hij))
    (cumulative_monotone _ m.buyVolume_nonneg) (cumulative_zero _) (-p)
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝[<] p) (𝓝[>] (-p)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact neg_lt_neg (show x < p from hx)
  rw [excess_eq_offered_difference]
  exact hs.sub (hb.comp hneg)

theorem excess_tendsto_right {lo hi : ℝ} (m : Book lo hi) (p : ℝ) :
    Tendsto m.excess (𝓝[>] p) (𝓝 (upperVertex m p)) := by
  have hs := offered_tendsto_right m.sellPrice (InterpolatedSide.cumulative m.sellVolume)
    m.sellPrice_monotone (cumulative_monotone _ m.sellVolume_nonneg) (cumulative_zero _) p
  have hb := offered_tendsto_left (fun i => -m.buyPrice i)
    (InterpolatedSide.cumulative m.buyVolume)
    (fun i j hij => neg_le_neg (m.buyPrice_antitone hij))
    (cumulative_monotone _ m.buyVolume_nonneg) (cumulative_zero _) (-p)
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝[>] p) (𝓝[<] (-p)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact neg_lt_neg (show p < x from hx)
  rw [excess_eq_offered_difference]
  exact hs.sub (hb.comp hneg)

theorem excess_leftLim_eq {lo hi : ℝ} (m : Book lo hi) (p : ℝ) :
    m.excess.leftLim p = lowerVertex m p :=
  leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) (excess_tendsto_left m p)

theorem excess_rightLim_eq {lo hi : ℝ} (m : Book lo hi) (p : ℝ) :
    m.excess.rightLim p = upperVertex m p :=
  rightLim_eq_of_tendsto (neBot_iff.mp inferInstance) (excess_tendsto_right m p)

section Measurable
variable {lo hi : ℝ} (hlohi : lo ≤ hi) {ns nb : ℕ}

def book (x : BoundedLayer lo hi ns nb) : Book lo hi :=
  parsedBook lo hi hlohi x.val x.property

theorem measurable_sellPrice :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      (show Fin (ns + 2) → ℝ from (book hlohi x).sellPrice)) :=
  measurable_pi_lambda _ (measurable_parsed_sellPrice hlohi ns nb)

theorem measurable_buyNegPrice :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      (show Fin (nb + 2) → ℝ from fun i => -(book hlohi x).buyPrice i)) :=
  measurable_pi_lambda _ fun i => (measurable_parsed_buyPrice hlohi ns nb i).neg

theorem measurable_sellQ :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      InterpolatedSide.cumulative (book hlohi x).sellVolume) :=
  measurable_pi_lambda _ (measurable_parsed_sellCumulative hlohi ns nb)

theorem measurable_buyQ :
    Measurable (fun x : BoundedLayer lo hi ns nb =>
      InterpolatedSide.cumulative (book hlohi x).buyVolume) :=
  measurable_pi_lambda _ (measurable_parsed_buyCumulative hlohi ns nb)

/-- Both actual one-sided excess vertices are jointly Borel in the literal
vendor data and the queried price, by the source finite arithmetic formulas. -/
theorem measurable_vertices
    (p : BoundedLayer lo hi ns nb → ℝ) (hp : Measurable p) :
    Measurable (fun x => lowerVertex (book hlohi x) (p x)) ∧
      Measurable (fun x => upperVertex (book hlohi x) (p x)) := by
  have hsl := measurable_finiteAcceptedLeft.comp
    ((measurable_sellPrice hlohi).prodMk ((measurable_sellQ hlohi).prodMk hp))
  have hsr := measurable_finiteAccepted.comp
    ((measurable_sellPrice hlohi).prodMk ((measurable_sellQ hlohi).prodMk hp))
  have hbl := measurable_finiteAcceptedLeft.comp
    ((measurable_buyNegPrice hlohi).prodMk ((measurable_buyQ hlohi).prodMk hp.neg))
  have hbr := measurable_finiteAccepted.comp
    ((measurable_buyNegPrice hlohi).prodMk ((measurable_buyQ hlohi).prodMk hp.neg))
  exact ⟨hsl.sub hbr, hsr.sub hbl⟩

theorem measurable_actual_excess_leftLim
    (p : BoundedLayer lo hi ns nb → ℝ) (hp : Measurable p) :
    Measurable (fun x => (book hlohi x).excess.leftLim (p x)) := by
  simp only [excess_leftLim_eq]
  exact (measurable_vertices hlohi p hp).1

theorem measurable_actual_excess_rightLim
    (p : BoundedLayer lo hi ns nb → ℝ) (hp : Measurable p) :
    Measurable (fun x => (book hlohi x).excess.rightLim (p x)) := by
  simp only [excess_rightLim_eq]
  exact (measurable_vertices hlohi p hp).2

end Measurable
end Thesis.DayAhead.VendorPLVertices
