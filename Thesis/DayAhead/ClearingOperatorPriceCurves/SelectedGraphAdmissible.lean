import Thesis.DayAhead.ClearingOperatorPriceCurves.GraphAdmissibleCone
import Thesis.DayAhead.ClearingOperatorPriceCurves.EssentialPriceCurve
import Thesis.DayAhead.ClearingOperatorPriceCurves.CanonicalSidedEncoding

/-! # One-sided conventions in the current admissible graph cone

The older GraphAdmissiblePair remains useful for arbitrary pointwise graphs.
The current source's admissible family additionally selects right-continuous
prices and the left limit at the first point of the terminal volume plateau.
-/

noncomputable section
namespace Thesis.DayAhead.PriceCurves

open Set Filter Topology

theorem GraphAdmissiblePair.exists_terminalStart (f : GraphAdmissiblePair) :
    ∃ u : Parameter, IsLeast {u | f.volume u = f.volume parameterRight} u :=
  (isClosed_eq f.volume_continuous continuous_const).isCompact.exists_isLeast
    ⟨parameterRight, rfl⟩

def GraphAdmissiblePair.terminalStart (f : GraphAdmissiblePair) : Parameter :=
  Classical.choose f.exists_terminalStart

theorem GraphAdmissiblePair.terminalStart_isLeast (f : GraphAdmissiblePair) :
    IsLeast {u | f.volume u = f.volume parameterRight} f.terminalStart :=
  Classical.choose_spec f.exists_terminalStart

theorem GraphAdmissiblePair.terminal_iff (f : GraphAdmissiblePair) (u : Parameter) :
    f.volume u = f.volume parameterRight ↔ f.terminalStart ≤ u := by
  constructor
  · exact fun h => f.terminalStart_isLeast.2 h
  · intro h
    exact le_antisymm (f.volume_monotone u.property.2)
      (f.terminalStart_isLeast.1 ▸ f.volume_monotone h)

theorem GraphAdmissiblePair.terminal_price (f : GraphAdmissiblePair)
    {u v : Parameter} (hu : f.terminalStart ≤ u) (hv : f.terminalStart ≤ v) :
    f.price u = f.price v :=
  f.fiber_const (((f.terminal_iff u).mpr hu).trans ((f.terminal_iff v).mpr hv).symm)

/-- Original label: `prop:admissible-parametrisations-cone`.
Original label: `defn:graph-tracing-pairs`.
This retained implementation restricts the price coordinate to finite range.
The additional one-sided conditions in the authoritative admissible family.
At an extreme endpoint the within-continuity condition is automatic. -/
structure SelectedGraphAdmissiblePair extends GraphAdmissiblePair where
  price_right : ∀ u, ContinuousWithinAt price (Ici u) u
  price_terminal : ContinuousWithinAt price (Iic toGraphAdmissiblePair.terminalStart)
    toGraphAdmissiblePair.terminalStart

/-- The terminal convention at its first point propagates along the plateau. -/
theorem SelectedGraphAdmissiblePair.price_left_at_terminal
    (f : SelectedGraphAdmissiblePair) (u : Parameter)
    (hu : f.volume u = f.volume parameterRight) :
    ContinuousWithinAt f.price (Iic u) u := by
  have hle := (f.toGraphAdmissiblePair.terminal_iff u).mp hu
  rcases hle.eq_or_lt with h | h
  · simpa only [← h] using f.price_terminal
  · apply continuousWithinAt_const.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds (s := Iic u)) (Ioi_mem_nhds h)] with v _ hv
      exact f.toGraphAdmissiblePair.terminal_price hv.le hle
    · rfl

theorem conicCombination_terminal_components (α β : ℝ)
    (f g : GraphAdmissiblePair) (hα : 0 ≤ α) (hβ : 0 ≤ β) (u : Parameter)
    (hu : (conicCombination α β f g hα hβ).volume u =
      (conicCombination α β f g hα hβ).volume parameterRight) :
    (0 < α → f.volume u = f.volume parameterRight) ∧
      (0 < β → g.volume u = g.volume parameterRight) := by
  have hf := f.volume_monotone (show u ≤ parameterRight from u.property.2)
  have hg := g.volume_monotone (show u ≤ parameterRight from u.property.2)
  change α * f.volume u + β * g.volume u =
    α * f.volume parameterRight + β * g.volume parameterRight at hu
  have hfd := mul_nonneg hα (sub_nonneg.mpr hf)
  have hgd := mul_nonneg hβ (sub_nonneg.mpr hg)
  constructor
  · intro ha
    have he : α * (f.volume parameterRight - f.volume u) = 0 := by nlinarith
    have := (mul_eq_zero.mp he).resolve_left ha.ne'
    linarith
  · intro hb
    have he : β * (g.volume parameterRight - g.volume u) = 0 := by nlinarith
    have := (mul_eq_zero.mp he).resolve_left hb.ne'
    linarith

/-- Original label: `prop:admissible-parametrisations-cone`.
Original label: `defn:graph-tracing-pairs`.
This retained implementation restricts the price coordinate to finite range.
All current admissibility conditions are preserved by nonnegative sums,
including a zero coefficient and a fully collapsed volume domain. -/
def selectedConicCombination (α β : ℝ) (f g : SelectedGraphAdmissiblePair)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : SelectedGraphAdmissiblePair where
  toGraphAdmissiblePair := conicCombination α β f.toGraphAdmissiblePair
    g.toGraphAdmissiblePair hα hβ
  price_right u := (continuousWithinAt_const.mul (f.price_right u)).add
    (continuousWithinAt_const.mul (g.price_right u))
  price_terminal := by
    let c := conicCombination α β f.toGraphAdmissiblePair g.toGraphAdmissiblePair hα hβ
    have ht := conicCombination_terminal_components α β f.toGraphAdmissiblePair
      g.toGraphAdmissiblePair hα hβ c.terminalStart c.terminalStart_isLeast.1
    have hf : ContinuousWithinAt (fun u => α * f.price u)
        (Iic c.terminalStart) c.terminalStart := by
      rcases hα.eq_or_lt with h | h
      · simp only [← h, zero_mul]
        exact continuousWithinAt_const
      · exact continuousWithinAt_const.mul (f.price_left_at_terminal _ (ht.1 h))
    have hg : ContinuousWithinAt (fun u => β * g.price u)
        (Iic c.terminalStart) c.terminalStart := by
      rcases hβ.eq_or_lt with h | h
      · simp only [← h, zero_mul]
        exact continuousWithinAt_const
      · exact continuousWithinAt_const.mul (g.price_left_at_terminal _ (ht.2 h))
    exact hf.add hg

def selectedGraphRepresentative (f : SelectedGraphAdmissiblePair) : ActualRepresentative :=
  graphAdmissibleRepresentative f.toGraphAdmissiblePair

/-- Original label: `prop:admissible-parametrisations-cone`.
Original label: `defn:graph-tracing-pairs`.
This retained implementation restricts the price coordinate to finite range.
The current, narrower family of actual graph functions is a convex cone. -/
theorem range_selectedGraphRepresentative_convexCone :
    Foundations.Stochastic.KernelHilbert.ConvexCone (range selectedGraphRepresentative) := by
  rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩ α β hα hβ
  exact ⟨selectedConicCombination α β f g hα hβ, rfl⟩

theorem GraphAdmissiblePair.terminalStart_eq_inf (f : GraphAdmissiblePair) :
    (f.terminalStart : ℝ) =
      sInf {u : ℝ | ∃ hu : u ∈ Icc (-1 : ℝ) 1,
        f.volume ⟨u, hu⟩ = f.volume parameterRight} := by
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨f.terminalStart.property, f.terminalStart_isLeast.1⟩, ?_⟩
  rintro u ⟨hu, h⟩
  exact f.terminalStart_isLeast.2 h

theorem SelectedGraphAdmissiblePair.price_right_constant
    (f : SelectedGraphAdmissiblePair) (u : Parameter) (hu : u < parameterRight) :
    ∃ v, u < v ∧ ∀ w, u ≤ w → w < v → f.price w = f.price u := by
  have he := eventually_eq_of_tendsto_finite_range f.price_finite
    ((f.price_right u).mono Ioi_subset_Ici_self)
  obtain ⟨v, huv, hv⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hu).mp he
  refine ⟨v, huv, fun w huw hwv => ?_⟩
  rcases huw.eq_or_lt with rfl | huw
  · rfl
  · exact hv ⟨huw, hwv⟩

theorem SelectedGraphAdmissiblePair.price_terminal_constant
    (f : SelectedGraphAdmissiblePair)
    (hu : parameterLeft < f.toGraphAdmissiblePair.terminalStart) :
    ∃ v, v < f.toGraphAdmissiblePair.terminalStart ∧ ∀ w, v < w →
      w ≤ f.toGraphAdmissiblePair.terminalStart →
      f.price w = f.price f.toGraphAdmissiblePair.terminalStart := by
  have he := eventually_eq_of_tendsto_finite_range f.price_finite
    (f.price_terminal.mono Iio_subset_Iic_self)
  obtain ⟨v, hvu, hv⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hu).mp he
  refine ⟨v, hvu, fun w hvw hwu => ?_⟩
  rcases hwu.eq_or_lt with rfl | hwu
  · rfl
  · exact hv ⟨hvw, hwu⟩

theorem GraphAdmissiblePair.decodedPrice_eq_of_volume (f : GraphAdmissiblePair)
    (x : Icc (f.volume parameterLeft) (f.volume parameterRight)) (u : Parameter)
    (hu : f.volume u = x) : decodedPrice f x = f.price u := by
  have hx : x = volumeDomainPoint f u := Subtype.ext hu.symm
  rw [hx, decodedPrice_volumeDomainPoint]

theorem SelectedGraphAdmissiblePair.decoded_right_constant
    (f : SelectedGraphAdmissiblePair)
    (x : Icc (f.volume parameterLeft) (f.volume parameterRight))
    (hx : (x : ℝ) < f.volume parameterRight) :
    ∃ z, x < z ∧ ∀ y, x ≤ y → y < z →
      decodedPrice f.toGraphAdmissiblePair y = decodedPrice f.toGraphAdmissiblePair x := by
  let q := f.toGraphAdmissiblePair
  obtain ⟨u, hu⟩ := (isClosed_eq f.volume_continuous continuous_const).isCompact.exists_isGreatest
    (show {u | f.volume u = (x : ℝ)}.Nonempty from (toVolumeRange q x).property)
  have huR : u < parameterRight := by
    by_contra hn
    have he : u = parameterRight := le_antisymm u.property.2 (not_lt.mp hn)
    have hux : f.volume u = x := hu.1
    rw [he] at hux
    linarith
  obtain ⟨v, huv, hv⟩ := f.price_right_constant u huR
  have hvx : (x : ℝ) < f.volume v := by
    have hle := f.volume_monotone huv.le
    have hux : f.volume u = x := hu.1
    rw [hux] at hle
    apply lt_of_le_of_ne hle
    intro h
    exact (not_le.mpr huv) (hu.2 h.symm)
  refine ⟨volumeDomainPoint q v, hvx, fun y hxy hyz => ?_⟩
  rcases hxy.eq_or_lt with rfl | hxy
  · rfl
  obtain ⟨w, hw⟩ := (toVolumeRange q y).property
  have huw : u < w := by
    by_contra hn
    have hle := f.volume_monotone (not_lt.mp hn)
    have hux : f.volume u = x := hu.1
    rw [hw, hux] at hle
    exact (not_le.mpr hxy) hle
  have hwv : w < v := by
    by_contra hn
    have hle := f.volume_monotone (not_lt.mp hn)
    rw [hw] at hle
    exact (not_le.mpr hyz) hle
  rw [q.decodedPrice_eq_of_volume y w hw,
    q.decodedPrice_eq_of_volume x u hu.1]
  exact hv w huw.le hwv

theorem SelectedGraphAdmissiblePair.decoded_left_constant
    (f : SelectedGraphAdmissiblePair)
    (hab : f.volume parameterLeft < f.volume parameterRight) :
    ∃ z, z < (decodePriceCurve f.toGraphAdmissiblePair).domainRight ∧
      ∀ y, z < y → y ≤ (decodePriceCurve f.toGraphAdmissiblePair).domainRight →
        decodedPrice f.toGraphAdmissiblePair y =
          decodedPrice f.toGraphAdmissiblePair
            (decodePriceCurve f.toGraphAdmissiblePair).domainRight := by
  let q := f.toGraphAdmissiblePair
  have ht : parameterLeft < q.terminalStart := by
    by_contra hn
    have he : q.terminalStart = parameterLeft :=
      le_antisymm (not_lt.mp hn) q.terminalStart.property.1
    have hterm := q.terminalStart_isLeast.1
    rw [he] at hterm
    exact hab.ne hterm
  obtain ⟨v, hvt, hv⟩ := f.price_terminal_constant ht
  have hvr : f.volume v < f.volume parameterRight := by
    have hle := f.volume_monotone (show v ≤ parameterRight from v.property.2)
    apply lt_of_le_of_ne hle
    intro he
    exact (not_le.mpr hvt) ((q.terminal_iff v).mp he)
  refine ⟨volumeDomainPoint q v, hvr, fun y hvy _ => ?_⟩
  obtain ⟨w, hw⟩ := (toVolumeRange q y).property
  have hvw : v < w := by
    by_contra hn
    have hle := f.volume_monotone (not_lt.mp hn)
    rw [hw] at hle
    exact (not_le.mpr hvy) hle
  rw [q.decodedPrice_eq_of_volume y w hw,
    q.decodedPrice_eq_of_volume (decodePriceCurve q).domainRight
      q.terminalStart q.terminalStart_isLeast.1]
  rcases le_total w q.terminalStart with h | h
  · exact hv w hvw h
  · exact q.terminal_price h le_rfl

/-- Original label: `prop:admissible-parametrisations-cone`.
Original label: `defn:graph-tracing-pairs`.
This retained implementation restricts the price coordinate to finite range.
The decoded graph has exactly the selected physical one-sided representative. -/
theorem SelectedGraphAdmissiblePair.decode_essential (f : SelectedGraphAdmissiblePair) :
    (decodePriceCurve f.toGraphAdmissiblePair).essential =
      decodePriceCurve f.toGraphAdmissiblePair := by
  let g := decodePriceCurve f.toGraphAdmissiblePair
  have hp : g.essentialPrice = g.price := by
    funext x
    by_cases hx : (x : ℝ) < g.rightEndpoint
    · rw [PriceCurve.essentialPrice, if_pos hx]
      obtain ⟨z, hxz, hz⟩ := f.decoded_right_constant x hx
      haveI : (𝓝[>] x).NeBot := nhdsGT_neBot_of_exists_gt ⟨z, hxz⟩
      apply rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hxz] with y hy
      exact (hz y hy.1.le hy.2).symm
    · have hxr : x = g.domainRight :=
        Subtype.ext (le_antisymm x.property.2 (not_lt.mp hx))
      subst x
      rw [PriceCurve.essentialPrice, if_neg hx]
      by_cases hab : g.leftEndpoint < g.rightEndpoint
      · obtain ⟨z, hzr, hz⟩ := f.decoded_left_constant hab
        haveI : (𝓝[<] g.domainRight).NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hzr⟩
        apply leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioo_mem_nhdsLT hzr] with y hy
        exact (hz y hy.1 hy.2.le).symm
      · apply leftLim_eq_of_isBot
        intro y
        change g.rightEndpoint ≤ (y : ℝ)
        exact (not_lt.mp hab).trans y.property.1
  change g.essential = g
  generalize hg : g = g' at hp ⊢
  cases g'
  simp only [PriceCurve.essential] at *
  congr 1

/-- Original label: `eq:graph-wise-decoder`.
The actual decoder lands in the narrower selected-curve domain. -/
def selectedGraphDecoder (f : SelectedGraphAdmissiblePair) : EssentialPriceCurve :=
  ⟨decodePriceCurve f.toGraphAdmissiblePair, f.decode_essential⟩

theorem selectedGraphDecoder_graph (f : SelectedGraphAdmissiblePair) :
    (selectedGraphDecoder f).val.graph = range (selectedGraphRepresentative f) :=
  (range_representative_eq_decodePriceCurve_graph f.toGraphAdmissiblePair).symm

/-- Original label: `prop:admissible-parametrisations-cone`.
Original label: `defn:graph-tracing-pairs`.
This retained implementation restricts the price coordinate to finite range.
Uniqueness includes the physical domain and every selected endpoint value. -/
theorem selectedGraphDecoder_unique (f : SelectedGraphAdmissiblePair)
    (g : EssentialPriceCurve) (hg : g.val.graph = range (selectedGraphRepresentative f)) :
    g = selectedGraphDecoder f := by
  apply Subtype.ext
  exact PriceCurve.graph_injective (hg.trans (selectedGraphDecoder_graph f).symm)

theorem PriceCurve.essential_parametrised_price_right (f : PriceCurve)
    (a : AdmissibleParametrisation f.essential) (u : Parameter) :
    ContinuousWithinAt (fun v => f.essentialPrice (a v)) (Ici u) u := by
  apply continuousWithinAt_const.congr_of_eventuallyEq
  · by_cases hx : (a u : ℝ) < f.rightEndpoint
    · obtain ⟨z, hxz, hz⟩ := f.essentialPrice_right_constant (a u) hx
      have he := (a.continuous.tendsto u) (Iio_mem_nhds hxz)
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds (s := Ici u)) he] with v huv hvz
      exact hz (a v) (a.monotone huv) hvz
    · filter_upwards [self_mem_nhdsWithin] with v huv
      have hxu : (a u : ℝ) = f.rightEndpoint :=
        le_antisymm (a u).property.2 (not_lt.mp hx)
      have hav : a v = a u := by
        apply le_antisymm _ (a.monotone huv)
        change (a v : ℝ) ≤ a u
        rw [hxu]
        exact (a v).property.2
      rw [hav]
  · rfl

theorem PriceCurve.essential_parametrised_price_at_right (f : PriceCurve)
    (a : AdmissibleParametrisation f.essential) (u : Parameter)
    (hu : (a u : ℝ) = f.rightEndpoint) :
    ContinuousAt (fun v => f.essentialPrice (a v)) u := by
  apply (continuousAt_const (y := f.essentialPrice (a u))).congr_of_eventuallyEq
  by_cases hab : f.leftEndpoint < f.rightEndpoint
  · obtain ⟨z, hzr, hz⟩ := f.essentialPrice_left_constant hab
    have hau : a u = f.domainRight := Subtype.ext hu
    have he := (a.continuous.tendsto u) (Ioi_mem_nhds (hau ▸ hzr))
    filter_upwards [he] with v hzv
    rw [hau]
    exact hz (a v) hzv (a v).property.2
  · apply Eventually.of_forall
    intro v
    have he : a v = a u := by
      apply Subtype.ext
      exact (le_antisymm (a v).property.2 ((not_lt.mp hab).trans (a v).property.1)).trans hu.symm
    change f.essentialPrice (a v) = f.essentialPrice (a u)
    rw [he]

/-- Original label: `prop:admissible-parametrisations-cone`.
Original label: `defn:graph-tracing-pairs`.
This retained implementation restricts the price coordinate to finite range.
Every admissible parametrisation of a selected physical curve obeys the
current graph convention. In particular, this applies to the canonical sided
parametrisation, including its collapsed side. -/
def selectedGraphOfParametrisation (f : PriceCurve)
    (a : AdmissibleParametrisation f.essential) : SelectedGraphAdmissiblePair where
  toGraphAdmissiblePair := a.toGraphAdmissiblePair f.essential
  price_right := f.essential_parametrised_price_right a
  price_terminal := by
    let q := a.toGraphAdmissiblePair f.essential
    have haR : (a parameterRight : ℝ) = f.rightEndpoint := by
      obtain ⟨v, hv⟩ := a.surjective f.domainRight
      apply le_antisymm (a parameterRight).property.2
      have h := a.monotone (show v ≤ parameterRight from v.property.2)
      rw [hv] at h
      exact h
    have ht : (a q.terminalStart : ℝ) = f.rightEndpoint :=
      q.terminalStart_isLeast.1.trans haR
    exact (f.essential_parametrised_price_at_right a q.terminalStart ht).continuousWithinAt

theorem selectedGraphOfParametrisation_graph (f : PriceCurve)
    (a : AdmissibleParametrisation f.essential) :
    (selectedGraphDecoder (selectedGraphOfParametrisation f a)).val = f.essential := by
  apply PriceCurve.graph_injective
  rw [selectedGraphDecoder_graph]
  exact range_parametrisedGraph f.essential a

/-- The canonical sided graph belongs to the current admissible family. -/
def canonicalSelectedGraph (f : PriceCurve) : SelectedGraphAdmissiblePair :=
  selectedGraphOfParametrisation f
    (SidedParametrisation.sidedAdmissibleParametrisation
      (SidedCertificate.canonicalCertificate f).knots)

theorem canonicalSelectedGraph_representative (f : PriceCurve) :
    selectedGraphRepresentative (canonicalSelectedGraph f) =
      SidedCertificate.canonicalSidedEncoding f := rfl

theorem selectedGraphDecoder_canonical (f : PriceCurve) :
    (selectedGraphDecoder (canonicalSelectedGraph f)).val = f.essential :=
  selectedGraphOfParametrisation_graph f _

end Thesis.DayAhead.PriceCurves
