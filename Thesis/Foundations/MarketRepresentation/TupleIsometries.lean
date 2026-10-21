import Thesis.Foundations.MarketRepresentation.TuplesMetricTopology

noncomputable section

namespace Thesis.Foundations.MarketRepresentation

open Set FiniteSets FiniteSets.FiniteSubsets TuplesBasic TuplesMetricTopology

universe u v

def Tuple.map {X : Type u} {Y : Type v} (f : X → Y) (x : Tuple X) : Tuple Y :=
  ⟨x.1, fun i => f (x.2 i)⟩

theorem isometry_tupleMap {X : Type u} {Y : Type v} [EMetricSpace X] [EMetricSpace Y]
    {f : X → Y} (hf : Isometry f) : Isometry (Tuple.map f) := by
  let F : IndexAugmented X → IndexAugmented Y :=
    fun p => IndexAugmented.mk p.index (f p.value)
  have hF : Isometry F := by
    intro p q
    change edist (IndexAugmented.mk p.index (f p.value))
      (IndexAugmented.mk q.index (f q.value)) = edist p q
    rw [IndexAugmented.edist_mk_mk, hf.edist_eq]
    conv_rhs => rw [← IndexAugmented.mk_index_value p, ← IndexAugmented.mk_index_value q]
    rw [IndexAugmented.edist_mk_mk]
  intro x y
  change Metric.hausdorffEDist
    (range (fun i : Fin x.1 => IndexAugmented.mk i.val (f (x.2 i))))
    (range (fun i : Fin y.1 => IndexAugmented.mk i.val (f (y.2 i)))) =
    Metric.hausdorffEDist
    (range (fun i : Fin x.1 => IndexAugmented.mk i.val (x.2 i)))
    (range (fun i : Fin y.1 => IndexAugmented.mk i.val (y.2 i)))
  simpa only [← Set.range_comp, Function.comp_def, F, IndexAugmented.index_mk,
    IndexAugmented.value_mk] using
    (Metric.hausdorffEDist_image
      (s := range (fun i : Fin x.1 => IndexAugmented.mk i.val (x.2 i)))
      (t := range (fun i : Fin y.1 => IndexAugmented.mk i.val (y.2 i))) hF)

end Thesis.Foundations.MarketRepresentation
