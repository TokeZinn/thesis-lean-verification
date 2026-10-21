import Thesis.DayAhead.ClearingOperatorPriceCurves.PLGraphTracing
import Mathlib.Topology.Order.DenselyOrdered

/-! # The decoder inherits the selected one-sided values

Right continuity is transferred at the greatest point of each quantity
fiber. The terminal left limit is transferred at the first point of the
terminal plateau. Choosing those different fiber endpoints is essential.
-/

noncomputable section
namespace Thesis.DayAhead.PLGraphTracing

open Set Filter Topology PriceCurves

theorem Pair.exists_greatest_fiber (f : Pair) (x : f.Domain) :
    ∃ u : Parameter, IsGreatest {u | f.volume u = x} u := by
  apply (isClosed_eq f.volume_continuous continuous_const).isCompact.exists_isGreatest
  exact f.preimage_nonempty x x.property

theorem TracingPair.exists_right_price_lt (f : TracingPair) (u : Parameter)
    (hu : u < parameterRight) (b : ℝ) (hb : f.price u < b) :
    ∃ v : Parameter, u < v ∧ f.price v < b := by
  haveI : NeBot (𝓝[>] u) := nhdsWithin_Ioi_neBot' ⟨parameterRight, hu⟩ le_rfl
  have hp : ∀ᶠ v in 𝓝[>] u, f.price v < b :=
    ((f.price_right u).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).eventually
      (gt_mem_nhds hb)
  have hu' : ∀ᶠ v in 𝓝[>] u, u < v := self_mem_nhdsWithin
  exact (hu'.and hp).exists

theorem TracingPair.exists_terminal_left_price_gt (f : TracingPair)
    (hu : parameterLeft < f.toPair.terminalStart) (b : ℝ)
    (hb : b < f.price f.toPair.terminalStart) :
    ∃ v : Parameter, v < f.toPair.terminalStart ∧ b < f.price v := by
  haveI : NeBot (𝓝[<] f.toPair.terminalStart) :=
    nhdsWithin_Iio_neBot' ⟨parameterLeft, hu⟩ le_rfl
  have hp : ∀ᶠ v in 𝓝[<] f.toPair.terminalStart, b < f.price v :=
    (f.price_terminal.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)).eventually
      (lt_mem_nhds hb)
  have hu' : ∀ᶠ v in 𝓝[<] f.toPair.terminalStart, v < f.toPair.terminalStart :=
    self_mem_nhdsWithin
  exact (hu'.and hp).exists

/-- Original label: `prop:admissible-parametrisations-cone`.
The graph-wise decoder has the source's right-continuous representative on
its entire physical domain, including quantity fibers of positive length. -/
theorem TracingPair.decode_right (f : TracingPair) (x : f.toPair.Domain) :
    ContinuousWithinAt f.toPair.decode (Ici x) x := by
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hb.trans_le (f.toPair.decode_monotone hy)
  · intro b hb
    by_cases hx : (x : ℝ) = f.volume parameterRight
    · apply Filter.Eventually.of_forall
      intro y
      exact (f.toPair.decode_monotone (show y ≤ x from y.property.2.trans_eq hx.symm)).trans_lt hb
    · obtain ⟨u, hu⟩ := f.toPair.exists_greatest_fiber x
      have hur : u < parameterRight := by
        apply lt_of_le_of_ne u.property.2
        intro he
        exact hx (hu.1.symm.trans (congrArg f.volume (Subtype.ext he)))
      have hpu : f.price u < b := by
        rwa [f.toPair.decode_eq_of_volume x u hu.1] at hb
      obtain ⟨v, huv, hpv⟩ := f.exists_right_price_lt u hur b hpu
      have hxv : x < f.toPair.domainPoint v := by
        have hle : (x : ℝ) ≤ f.volume v := hu.1 ▸ f.volume_monotone huv.le
        apply lt_of_le_of_ne hle
        intro he
        exact huv.not_ge (hu.2 he.symm)
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hxv)] with y hy
      exact (f.toPair.decode_monotone hy.le).trans_lt
        (by simpa only [f.toPair.decode_domainPoint] using hpv)

/-- Original label: `prop:admissible-parametrisations-cone`.
The terminal value of the decoded curve equals its physical left limit,
even when the parameter-space terminal plateau has positive length. -/
theorem TracingPair.decode_terminal_left (f : TracingPair) :
    ContinuousWithinAt f.toPair.decode
      (Iic (f.toPair.domainPoint parameterRight)) (f.toPair.domainPoint parameterRight) := by
  let r := f.toPair.domainPoint parameterRight
  let u := f.toPair.terminalStart
  have hqu : f.volume u = r := f.toPair.terminalStart_isLeast.1
  have hprice : f.toPair.decode r = f.price u := f.toPair.decode_eq_of_volume r u hqu
  apply tendsto_order.2
  constructor
  · intro b hb
    by_cases hu : u = parameterLeft
    · apply Filter.Eventually.of_forall
      intro y
      have hly : r ≤ y := by
        change f.volume parameterRight ≤ (y : ℝ)
        have he : f.volume parameterRight = f.volume parameterLeft := by
          rw [← hu]
          exact hqu.symm
        rw [he]
        exact y.property.1
      exact hb.trans_le (f.toPair.decode_monotone hly)
    · have hlu : parameterLeft < u := lt_of_le_of_ne u.property.1 (Ne.symm hu)
      have hbp : b < f.price u := hprice ▸ hb
      obtain ⟨v, hvu, hpv⟩ := f.exists_terminal_left_price_gt hlu b hbp
      have hvr : f.toPair.domainPoint v < r := by
        apply lt_of_le_of_ne (f.volume_monotone v.property.2)
        intro he
        exact hvu.not_ge (f.toPair.terminalStart_isLeast.2 he)
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hvr)] with y hy
      have hpv' : b < f.toPair.decode (f.toPair.domainPoint v) := by
        simpa only [f.toPair.decode_domainPoint] using hpv
      exact hpv'.trans_le (f.toPair.decode_monotone hy.le)
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (f.toPair.decode_monotone hy).trans_lt hb

/-- The actual finite-affine curve constructed by the decoder uses those
same selected right-continuous values on its recorded domain. -/
theorem TracingPair.decodedCurve_right (f : TracingPair) (x : f.toPair.Domain) :
    ContinuousWithinAt (fun y : f.toPair.Domain => f.toPair.decodedCurve.price y)
      (Ici x) x := by
  change ContinuousWithinAt (fun y : f.toPair.Domain => f.toPair.decodedReal y) (Ici x) x
  simpa only [f.toPair.decodedReal_eq_decode] using f.decode_right x

/-- The actual decoded curve also retains the required final left limit. -/
theorem TracingPair.decodedCurve_terminal_left (f : TracingPair) :
    ContinuousWithinAt (fun y : f.toPair.Domain => f.toPair.decodedCurve.price y)
      (Iic (f.toPair.domainPoint parameterRight)) (f.toPair.domainPoint parameterRight) := by
  change ContinuousWithinAt (fun y : f.toPair.Domain => f.toPair.decodedReal y)
    (Iic (f.toPair.domainPoint parameterRight)) (f.toPair.domainPoint parameterRight)
  simpa only [f.toPair.decodedReal_eq_decode] using f.decode_terminal_left

end Thesis.DayAhead.PLGraphTracing
