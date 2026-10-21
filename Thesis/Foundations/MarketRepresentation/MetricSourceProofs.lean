import Thesis.Foundations.MarketRepresentation.DisjointUnionTopology
import Thesis.Foundations.MarketRepresentation.DoctoralGeometry
import Thesis.Foundations.MarketRepresentation.TuplesMeasurableSorting

/-! # Metric source proofs (stub)

This module used to hold the thesis-faithful function-level and finite-minimum
proofs of the metric chapter. Those proofs now live in the primary modules,
which carry the `Original label:` lines:

* `thm:pasting-lemma` →
  `DisjointUnionTopology.continuous_metricTopology_pasting_iff`;
* finite-minimum and separation steps of `thm:Hausdorff-finite-sets` →
  `FiniteSets.FiniteSubsets.infEDist_attained` and
  `FiniteSets.FiniteSubsets.hausdorffEDistance_eq_zero`;
* separability in `thm:labelled-properties` →
  `FiniteSets.DistinctFiniteSubsets.separableSpace`;
* truncation argument of `thm:the-standard-machinery` →
  `TuplesMetricTopology.topologies_eq_of_equal_truncations`,
  `TuplesMetricTopology.tupleHausdorffMetricTopology_eq_tupleSup` and
  `TuplesMetricTopology.tupleHausdorffMetricTopology_eq_sigma`;
* `prop:permutations-countable` →
  `TuplesMeasurableSorting.finitePermutations_countable`
  (via `finitePermutationTuple_injective`);
* `prop:permuting-continuous` →
  `TuplesMeasurableSorting.continuous_permutationMap`, with the helpers
  `coordinateEDistSup_permutation` and
  `permutationMap_edist_le_of_edist_lt_one`.

The duplicates that lived here were removed. The module is retained, with its
imports, for interface stability: `ActionSourceProofs`, `ConfigurationScope`
and `Formalization` import it. -/

namespace Thesis.Foundations.MarketRepresentation.MetricSourceProofs

-- The primary statement under its former secondary qualified name, so that
-- `MetricSourceProofs.topologies_eq_of_equal_truncations` still resolves.
export Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
  (topologies_eq_of_equal_truncations)

end Thesis.Foundations.MarketRepresentation.MetricSourceProofs
