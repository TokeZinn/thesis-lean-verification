import Thesis.DayAhead.ClearingOperatorPriceCurves.MarketCurveKnots

/-! # Joint measurability of the actual canonical market representative -/

noncomputable section
namespace Thesis.DayAhead.MarketCurve

open Set MeasureTheory
open Foundations.MarketClearing.Sorting
open MarketImpact PriceCurves SidedCertificate SidedParametrisation SidedCurveLp

local instance : MeasurableSpace MarketTuple := borel _
local instance : BorelSpace MarketTuple := ⟨rfl⟩

theorem measurable_uniformInterpolation {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (k : Ω → Fin (n + 1) → ℝ) (t : Ω → ℝ)
    (hk : ∀ j, Measurable (fun ω => k ω j)) (ht : Measurable t) :
    Measurable (fun ω => uniformInterpolation (k ω) (t ω)) := by
  apply (hk 0).add
  apply Finset.measurable_sum
  intro j _
  exact ((hk j.succ).sub (hk j.castSucc)).mul
    (continuous_clampUnit.measurable.comp ((ht.const_mul _).sub measurable_const))

theorem measurable_variableInterpolation {Ω : Type*} [MeasurableSpace Ω]
    (c : Ω → ℕ) (k : ℕ → Ω → ℝ) (t : Ω → ℝ)
    (hc : Measurable c) (hk : ∀ j, Measurable (k j)) (ht : Measurable t) :
    Measurable (fun ω => uniformInterpolation (fun j : Fin (c ω + 1) => k j.val ω) (t ω)) := by
  have h : Measurable (fun x : Ω × ℕ =>
      uniformInterpolation (fun j : Fin (x.2 + 1) => k j.val x.1) (t x.1)) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_uniformInterpolation _ _ (fun j => hk j.val) ht
  exact h.comp (measurable_id.prodMk hc)

def marketLeftInterpolation (upper : ℝ) (hupper : 0 ≤ upper) (x : RegimeState upper × ℝ) : ℝ :=
  uniformInterpolation
    (fun j : Fin (marketLeftCount upper hupper x.1 + 1) =>
      marketLeftKnot upper hupper j.val x.1) x.2

def marketRightInterpolation (upper : ℝ) (hupper : 0 ≤ upper) (x : RegimeState upper × ℝ) : ℝ :=
  uniformInterpolation
    (fun j : Fin (marketRightCount upper hupper x.1 + 1) =>
      marketRightKnot upper hupper j.val x.1) x.2

theorem measurable_marketLeftInterpolation (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (marketLeftInterpolation upper hupper) := by
  exact measurable_variableInterpolation _ _ _
    ((measurable_marketLeftCount upper hupper).comp measurable_fst)
    (fun j => (measurable_marketLeftKnot upper hupper j).comp measurable_fst) measurable_snd

theorem measurable_marketRightInterpolation (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (marketRightInterpolation upper hupper) := by
  exact measurable_variableInterpolation _ _ _
    ((measurable_marketRightCount upper hupper).comp measurable_fst)
    (fun j => (measurable_marketRightKnot upper hupper j).comp measurable_fst) measurable_snd

def marketSidedQuantity (upper : ℝ) (hupper : 0 ≤ upper) (x : RegimeState upper × ℝ) : ℝ :=
  if x.2 ≤ 0 then marketLeftInterpolation upper hupper (x.1, x.2 + 1)
  else marketRightInterpolation upper hupper x

theorem measurable_marketSidedQuantity (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (marketSidedQuantity upper hupper) :=
  ((measurable_marketLeftInterpolation upper hupper).comp
    (measurable_fst.prodMk (measurable_snd.add_const 1))).ite
      (measurableSet_le measurable_snd measurable_const)
      (measurable_marketRightInterpolation upper hupper)

theorem marketSidedQuantity_eq (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper)
    (u : Parameter) : marketSidedQuantity upper hupper (m, u) =
      (canonicalSidedEncoding (impactCurve upper hupper m.val m.property.1 m.property.2) u).1 := by
  let R := chosenMinimalRepresentation
    (impactCurve upper hupper m.val m.property.1 m.property.2).essential
  change (if (u : ℝ) ≤ 0 then marketLeftInterpolation upper hupper (m, (u : ℝ) + 1)
    else marketRightInterpolation upper hupper (m, u)) =
    if (u : ℝ) ≤ 0 then uniformInterpolation (canonicalLeftKnot R) ((u : ℝ) + 1)
      else uniformInterpolation (canonicalRightKnot R) u
  split_ifs
  · exact congrArg (fun k => uniformInterpolation k ((u : ℝ) + 1))
      (funext fun j => marketLeftKnot_eq upper hupper m j)
  · exact congrArg (fun k => uniformInterpolation k (u : ℝ))
      (funext fun j => marketRightKnot_eq upper hupper m j)

theorem marketSidedQuantity_mem (upper : ℝ) (hupper : 0 ≤ upper) (m : RegimeState upper)
    (u : Parameter) : marketSidedQuantity upper hupper (m, u) ∈ availableDepth m.val := by
  rw [marketSidedQuantity_eq]
  exact ((sidedAdmissibleParametrisation
    (canonicalCertificate
      (impactCurve upper hupper m.val m.property.1 m.property.2)).knots) u).property

theorem canonicalSidedEncoding_market_eq (upper : ℝ) (hupper : 0 ≤ upper)
    (m : RegimeState upper) (u : Parameter) :
    canonicalSidedEncoding (impactCurve upper hupper m.val m.property.1 m.property.2) u =
      (marketSidedQuantity upper hupper (m, u),
        essentialImpactPrice upper hupper (m, marketSidedQuantity upper hupper (m, u))) := by
  apply Prod.ext
  · exact (marketSidedQuantity_eq upper hupper m u).symm
  · let f := impactCurve upper hupper m.val m.property.1 m.property.2
    let q := (sidedAdmissibleParametrisation (canonicalCertificate f).knots) u
    have hq : clampedQuantity m (marketSidedQuantity upper hupper (m, u)) = q := by
      apply Subtype.ext
      have hb := marketSidedQuantity_mem upper hupper m u
      change max (-buyDepth m.val) (min (sellDepth m.val)
        (marketSidedQuantity upper hupper (m, u))) = (q : ℝ)
      rw [min_eq_right hb.2, max_eq_right hb.1, marketSidedQuantity_eq]
      rfl
    change f.essential.price q = f.essential.price _
    rw [hq]

theorem measurable_canonicalMarketRepresentative (upper : ℝ) (hupper : 0 ≤ upper) :
    Measurable (fun x : RegimeState upper × ℝ =>
      canonicalSidedEncoding (impactCurve upper hupper x.1.val x.1.property.1 x.1.property.2)
        (clampParameter x.2)) := by
  simp_rw [canonicalSidedEncoding_market_eq]
  have hq : Measurable (fun x : RegimeState upper × ℝ =>
      marketSidedQuantity upper hupper (x.1, (clampParameter x.2 : ℝ))) :=
    (measurable_marketSidedQuantity upper hupper).comp
      (measurable_fst.prodMk
        (continuous_subtype_val.measurable.comp (continuous_clampParameter.measurable.comp
          measurable_snd)))
  exact hq.prodMk ((measurable_essentialImpactPrice upper hupper).comp
    (measurable_fst.prodMk hq))

end Thesis.DayAhead.MarketCurve
