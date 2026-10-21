import Thesis.Appendices.ExtendedResearch.CDFConditional

/-! # Conditional CDF classes by scalar tests and a common null set

The thesis proof of clause (ii) of `prop:cdf-constraint-properties` (commute
each scalar inner-product test through conditional expectation, use the scalar
conditional-law identity and kernel Fubini, then intersect the null-set
complements for a countable dense family of tests) now lives on the primary
module `CDFConditional` (`scalar_kernel_fubini`, `cdfClass_mem`,
`scalar_conditional_cdf`, `conditional_cdf`, `conditional_cdf_subsigma`).
This module is retained for interface stability and only re-exports those
results under their former names. -/

noncomputable section
namespace Thesis.Foundations.Research.CDFConditionalSource

export Thesis.Foundations.Research.CDFConditional
  (scalar_kernel_fubini cdfClass_mem scalar_conditional_cdf)

/-- Moved to `CDFConditional` as `conditional_cdf` (the labelled theorem); kept as an alias. -/
alias conditional_cdf_source := CDFConditional.conditional_cdf

/-- Moved to `CDFConditional` as `conditional_cdf_subsigma`; kept as an alias. -/
alias conditional_cdf_subsigma_source := CDFConditional.conditional_cdf_subsigma

end Thesis.Foundations.Research.CDFConditionalSource
