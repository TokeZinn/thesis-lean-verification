import Thesis.Foundations.MarketClearing.Sorting

/-! # Simultaneous fixed-length Borel layers

The thesis proof of `lem:tuple-space-measurable-2` for arbitrary finite
products of possibly different (including zero-length) layers now lives in
`Sorting` (`fixedLayers`, `fixedLayers_isOpenEmbedding`, `fixedLayers_Borel`),
where it is the mapped proof. This module is retained for interface stability
and only re-exports those names. -/

noncomputable section

namespace Thesis.Foundations.MarketClearing.DoctoralLayerBorel

open MarketRepresentation MarketRepresentation.TuplesMetricTopology

export Sorting (fixedLayers fixedLayers_isOpenEmbedding fixedLayers_Borel)

end Thesis.Foundations.MarketClearing.DoctoralLayerBorel
