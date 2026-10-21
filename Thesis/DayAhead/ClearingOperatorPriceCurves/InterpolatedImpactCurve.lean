import Thesis.DayAhead.ClearingOperatorPriceCurves.OfferedPartition
import Thesis.DayAhead.ClearingOperatorPriceCurves.PolygonalInverse

/-! # The actual interpolated-book price-impact curve is finitely affine

The accepted-volume partitions are derived from the supremum definitions.
Their common refinement gives the actual excess supply. The completed-graph
midpoint inverse theorem then constructs the price-curve partition.
-/

noncomputable section
namespace Thesis.DayAhead.InterpolatedImpactCurve

open Set PiecewiseAffinePriceCurves InterpolatedSide ExcessSupply

/-- Reversing the coordinate preserves a finite affine partition. This
allows the demand acceptance threshold `-p`, rather than only increasing
affine coordinate changes. -/
def reflectedArgument {D : Set ℝ} {f : ℝ → ℝ} (P : AffinePartition D f) :
    AffinePartition ((fun x : ℝ => -x) ⁻¹' D) (fun x => f (-x)) where
  count := P.count
  piece := fun i => (fun x : ℝ => -x) ⁻¹' P.piece i
  interval := fun i => (P.interval i).preimage_anti (fun _ _ h => neg_le_neg h)
  disjoint := fun i j hij => (P.disjoint i j hij).preimage _
  cover := fun x => P.cover (-x)
  affine := by
    intro i
    obtain ⟨a, b, h⟩ := P.affine i
    refine ⟨-a, b, fun x hx => ?_⟩
    rw [h _ hx]
    ring

namespace Book

variable {lo hi : ℝ}

/-- The exact sell-acceptance function has a finite affine partition on all
prices, including its constant tails and values at nodal prices. -/
def supplyAcceptancePartition (m : ExcessSupply.Book lo hi) :
    AffinePartition univ (offered m.sellDepth m.supply) :=
  OfferedPartition.partition m.sellPrice (cumulative m.sellVolume) m.sellPrice_monotone
    (cumulative_monotone m.sellVolume m.sellVolume_nonneg) (cumulative_zero _)

/-- Demand is handled through the exact negated-price interpolation identity;
the function being partitioned is the bid supremum in the thesis. -/
def demandAcceptancePartition (m : ExcessSupply.Book lo hi) :
    AffinePartition univ (fun p => offered m.buyDepth (fun q => -m.demand q) (-p)) := by
  have hp : Monotone (fun i => -m.buyPrice i) :=
    fun _ _ h => neg_le_neg (m.buyPrice_antitone h)
  let P := OfferedPartition.partition (fun i => -m.buyPrice i)
    (cumulative m.buyVolume) hp
    (cumulative_monotone m.buyVolume m.buyVolume_nonneg) (cumulative_zero _)
  have he : curve (fun i => -m.buyPrice i) (cumulative m.buyVolume) =
      fun q => -m.demand q := by
    funext q
    exact curve_neg_prices m.buyPrice (cumulative m.buyVolume) q
  have R := reflectedArgument P
  change AffinePartition ((fun x : ℝ => -x) ⁻¹' univ)
    (fun x => offered m.buyDepth
      (curve (fun i => -m.buyPrice i) (cumulative m.buyVolume)) (-x)) at R
  rw [he] at R
  simpa only [preimage_univ] using R

/-- Original label: `defn:excess-supply-and-completed-graph`.
The finite partition is derived for the literal difference of the two
supremum-defined acceptance functions. -/
def excessPartition (m : ExcessSupply.Book lo hi) :
    AffinePartition (Icc lo hi) m.excess := by
  have P := (supplyAcceptancePartition m).combine (demandAcceptancePartition m) 1 (-1)
  have H : AffinePartition univ m.excess := by
    simpa only [univ_inter, one_mul, neg_one_mul, ← sub_eq_add_neg, ExcessSupply.Book.excess,
      ExcessSupply.excess] using P
  simpa only [univ_inter] using H.restrict (Icc lo hi) ordConnected_Icc

/-- Original label: `prop:price-impact-curve-properties`, clause (ii).
The actual book midpoint inverse has a finite affine partition on its entire
available-depth domain. No finite-affinity field is assumed of a book. -/
def pricePartition (m : ExcessSupply.Book lo hi) : AffinePartition m.domain m.price := by
  change AffinePartition m.domain (CompletedInverse.midpointPrice lo hi m.excess)
  exact PolygonalInverse.inversePartition (excessPartition m)
    (excess_monotone _ _ m.sellDepth_nonneg m.buyDepth_nonneg _ _) m.domain
    ordConnected_Icc m.completed_level_nonempty

/-- Original label: `prop:price-impact-curve-properties`.
The actual interpolated-book inverse belongs to the source's full finite
piecewise-affine curve space, including nonconstant affine pieces and jumps. -/
def impactCurve (m : ExcessSupply.Book lo hi) : Curve where
  leftEndpoint := -m.buyDepth
  rightEndpoint := m.sellDepth
  left_nonpos := neg_nonpos.mpr m.buyDepth_nonneg
  right_nonneg := m.sellDepth_nonneg
  price := m.price
  monotone := m.price_monotone
  pieces := ⟨pricePartition m⟩

@[simp] theorem impactCurve_price (m : ExcessSupply.Book lo hi) :
    (impactCurve m).price = m.price := rfl

@[simp] theorem impactCurve_domain (m : ExcessSupply.Book lo hi) :
    Icc (impactCurve m).leftEndpoint (impactCurve m).rightEndpoint = m.domain := rfl

end Book
end Thesis.DayAhead.InterpolatedImpactCurve
