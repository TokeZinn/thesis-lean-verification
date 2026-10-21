import Thesis.Foundations.MarketRepresentation.TupleIsometries

/-! # Retagging actual thesis tuples into a disjoint union -/

noncomputable section

namespace Thesis.Intraday

open Foundations.MarketRepresentation
open Foundations.MarketRepresentation.DisjointUnionTopology
open Foundations.MarketRepresentation.TuplesMetricTopology

universe u v
variable {A : Type u} {X : A → Type v}

/-- Original label: `defn:retagging`.
Attach the selected side to every tuple entry, retaining its index. -/
def retag (a : A) : Tuple (X a) → Tuple (DisjointUnion X) := Tuple.map (Sigma.mk a)

/-- Original label: `cor:retagging-measurable`.
The exact indexed Hausdorff distances, including the empty tuple, are preserved.
Countability of the side set is unnecessary for this stronger conclusion. -/
theorem retag_isometry [∀ a, EMetricSpace (X a)] (a : A) :
    letI := disjointUnionEMetricSpace (X := X)
    Isometry (retag (X := X) a) := by
  letI := disjointUnionEMetricSpace (X := X)
  apply isometry_tupleMap
  intro x y
  exact disjointEdist_mk_mk_same x y

/-- Original label: `cor:retagging-measurable`. -/
theorem retag_continuous [∀ a, EMetricSpace (X a)] (a : A) :
    letI := disjointUnionEMetricSpace (X := X)
    @Continuous (Tuple (X a)) (Tuple (DisjointUnion X))
      (tupleHausdorffMetricTopology (X := X a))
      (tupleHausdorffMetricTopology (X := DisjointUnion X)) (retag a) := by
  letI := disjointUnionEMetricSpace (X := X)
  exact (retag_isometry a).continuous

/-- Original label: `cor:retagging-measurable`. -/
theorem retag_measurable [∀ a, EMetricSpace (X a)] (a : A) :
    letI := disjointUnionEMetricSpace (X := X)
    @Measurable (Tuple (X a)) (Tuple (DisjointUnion X))
      (tupleHausdorffBorel (X := X a))
      (tupleHausdorffBorel (X := DisjointUnion X)) (retag a) := by
  letI := disjointUnionEMetricSpace (X := X)
  letI : TopologicalSpace (Tuple (X a)) := tupleHausdorffMetricTopology (X := X a)
  letI : TopologicalSpace (Tuple (DisjointUnion X)) :=
    tupleHausdorffMetricTopology (X := DisjointUnion X)
  exact (retag_continuous a).borel_measurable

end Thesis.Intraday
