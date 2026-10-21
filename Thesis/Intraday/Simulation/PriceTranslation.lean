import Thesis.Intraday.Simulation.GeometrySweep

/-! # Exact price translation without rounding or clipping

The current simulator freezes a side-specific shift for a drawn window.
The bounded formal order representation requires a price-domain certificate.
The `_fix.tex` revision uses an operational real-price domain, whose total
translation and exact conditional bounded bridge are in `DomainExtensions`.
-/

noncomputable section
namespace Thesis.Intraday.PriceTranslation

def shiftOrder (o : Order) (s : ℝ) (h : price o + s ∈ Set.Icc (-9999 : ℝ) 9999) : Order :=
  WithLp.toLp 1 (⟨price o + s, h⟩, o.snd)

@[simp] theorem shiftOrder_price (o : Order) (s : ℝ) (h) :
    price (shiftOrder o s h) = price o + s := rfl

@[simp] theorem shiftOrder_quantity (o : Order) (s : ℝ) (h) :
    quantity (shiftOrder o s h) = quantity o := rfl

@[simp] theorem shiftOrder_time (o : Order) (s : ℝ) (h) :
    time (shiftOrder o s h) = time o := rfl

/-- A source limit buy at zero below an ask of 5000, transferred to a live
ask of -6000, leaves the declared price interval. -/
theorem opposite_anchor_can_leave_price_domain :
    (0 : ℝ) ∈ Set.Icc (-9999 : ℝ) 9999 ∧
    (5000 : ℝ) ∈ Set.Icc (-9999 : ℝ) 9999 ∧
    (-6000 : ℝ) ∈ Set.Icc (-9999 : ℝ) 9999 ∧
    ¬((0 : ℝ) + (-6000 - 5000) ∈ Set.Icc (-9999 : ℝ) 9999) := by
  norm_num

end Thesis.Intraday.PriceTranslation
