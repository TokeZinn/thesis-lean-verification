import Thesis.Foundations.Stochastic.KernelHilbertAlignment
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The source's cancellative cone and finite coefficient splitting proof (interface module)

The manuscript's proof of `thm:grothendieck-vector-space-from-convex-cone` now
lives in `KernelHilbert`: the cancellative transitivity argument is inside
`grothendieckRel_equivalence`, and the finite positive/negative coefficient
split is `weakConvex_nonnegative_sum_mem_range` /
`span_mem_positive_negative_split`, feeding `grothendieckToSpan_surjective`
and `grothendieckVectorizationEquivSpan`. The labels live there. This module
is retained for interface stability only: it keeps the former `_source` names
as aliases of those declarations.
-/

noncomputable section
namespace Thesis.Foundations.Stochastic.KernelHilbert

/-- Alias of `grothendieckRel_equivalence` (the mapped proof). -/
alias grothendieckRel_equivalence_source := grothendieckRel_equivalence

/-- Alias of `weakConvex_nonnegative_sum_mem_range`. -/
alias nonnegative_finset_sum_mem_range := weakConvex_nonnegative_sum_mem_range

/-- Alias of `span_mem_positive_negative_split` (the mapped coefficient split). -/
alias span_element_positive_negative_split := span_mem_positive_negative_split

/-- Alias of `grothendieckToSpan_surjective` (the mapped proof). -/
alias grothendieckToSpan_surjective_source := grothendieckToSpan_surjective

/-- Alias of `grothendieckVectorizationEquivSpan` (the mapped bijection). -/
alias grothendieckVectorizationEquivSpan_source := grothendieckVectorizationEquivSpan

/-- Alias of `grothendieck_vectorSpace_from_convexCone` (the mapped theorem). -/
alias grothendieck_vectorSpace_from_convexCone_source := grothendieck_vectorSpace_from_convexCone

end Thesis.Foundations.Stochastic.KernelHilbert
