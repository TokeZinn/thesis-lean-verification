import Thesis.DayAhead.ClearingOperatorPriceCurves.PriceCurves

/-! # Graph recovery and injectivity of actual price-curve representatives -/

namespace Thesis.DayAhead.PriceCurves

open Set

def PriceCurve.graph (f : PriceCurve) : Set (ℝ × ℝ) :=
  range (fun x : Icc f.leftEndpoint f.rightEndpoint => ((x : ℝ), f.price x))

/-- Original label: `eq:parametrised-graph-recovers-curve`.
An actual admissible representative recovers the entire pointwise graph. -/
theorem range_parametrisedGraph (f : PriceCurve) (p : AdmissibleParametrisation f) :
    range (parametrisedGraph f p) = f.graph := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨p u, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := p.surjective x
    exact ⟨u, rfl⟩

theorem PriceCurve.domain_mem_of_graph_eq {f g : PriceCurve} (h : f.graph = g.graph)
    (x : Icc f.leftEndpoint f.rightEndpoint) : (x : ℝ) ∈ Icc g.leftEndpoint g.rightEndpoint := by
  have hx : ((x : ℝ), f.price x) ∈ g.graph := h ▸ mem_range_self x
  obtain ⟨y, hy⟩ := hx
  have hyx : (y : ℝ) = x := congrArg Prod.fst hy
  simpa only [hyx] using y.property

theorem PriceCurve.graph_injective : Function.Injective PriceCurve.graph := by
  intro f g h
  have hfl : f.leftEndpoint ∈ Icc g.leftEndpoint g.rightEndpoint :=
    domain_mem_of_graph_eq h ⟨f.leftEndpoint, le_rfl,
      f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg⟩
  have hgl : g.leftEndpoint ∈ Icc f.leftEndpoint f.rightEndpoint :=
    domain_mem_of_graph_eq h.symm ⟨g.leftEndpoint, le_rfl,
      g.leftEndpoint_nonpos.trans g.rightEndpoint_nonneg⟩
  have hfr : f.rightEndpoint ∈ Icc g.leftEndpoint g.rightEndpoint :=
    domain_mem_of_graph_eq h ⟨f.rightEndpoint,
      f.leftEndpoint_nonpos.trans f.rightEndpoint_nonneg, le_rfl⟩
  have hgr : g.rightEndpoint ∈ Icc f.leftEndpoint f.rightEndpoint :=
    domain_mem_of_graph_eq h.symm ⟨g.rightEndpoint,
      g.leftEndpoint_nonpos.trans g.rightEndpoint_nonneg, le_rfl⟩
  have hl : f.leftEndpoint = g.leftEndpoint := le_antisymm hgl.1 hfl.1
  have hr : f.rightEndpoint = g.rightEndpoint := le_antisymm hfr.2 hgr.2
  cases f with
  | mk fl fr fl_nonpos fr_nonneg fp hfm hff =>
    cases g with
    | mk gl gr gl_nonpos gr_nonneg gp hgm hgf =>
      dsimp only at hl hr
      subst gl
      subst gr
      have hp : fp = gp := by
        funext x
        have hx : ((x : ℝ), fp x) ∈
            (PriceCurve.mk fl fr gl_nonpos gr_nonneg gp hgm hgf).graph := h ▸ mem_range_self x
        obtain ⟨y, hy⟩ := hx
        have hyx : y = x := Subtype.ext (congrArg Prod.fst hy)
        subst y
        exact (congrArg Prod.snd hy).symm
      subst gp
      rfl

theorem parametrisedGraph_eq_implies_eq {f g : PriceCurve}
    (p : AdmissibleParametrisation f) (q : AdmissibleParametrisation g)
    (h : parametrisedGraph f p = parametrisedGraph g q) : f = g := by
  apply PriceCurve.graph_injective
  rw [← range_parametrisedGraph f p, ← range_parametrisedGraph g q, h]

end Thesis.DayAhead.PriceCurves
