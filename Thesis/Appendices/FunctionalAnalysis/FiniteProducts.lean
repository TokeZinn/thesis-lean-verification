import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Finite products in the functional-analysis appendix

These prove the three facts stated informally after the Banach/Hilbert
definitions. The Hilbert structure uses the Euclidean product norm.
-/

namespace Thesis.Foundations.Preliminary.FunctionalAnalysis

universe u v
open scoped ENNReal

/-- Original label: `prop:finite-products`.
Finite products of real Banach spaces are Banach for every standard finite
product `p`-norm, including the maximum norm at `p = ∞`. -/
theorem finiteProductBanach {ι : Type u} [Fintype ι] (V : ι → Type v)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    [∀ i, CompleteSpace (V i)] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Nonempty (NormedSpace ℝ (PiLp p V)) ∧ CompleteSpace (PiLp p V) :=
  ⟨⟨inferInstance⟩, inferInstance⟩

/-- Original label: `prop:finite-products`.
Finite Hilbert products are complete and have exactly the coordinate-sum
inner product. The `PiLp 2` instance provides the Hilbert axioms. -/
theorem finiteProductHilbert {ι : Type u} [Fintype ι] (H : ι → Type v)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] :
    CompleteSpace (PiLp 2 H) ∧
      ∀ f g : PiLp 2 H, inner ℝ f g = ∑ i, inner ℝ (f i) (g i) :=
  ⟨inferInstance, fun _ _ ↦ PiLp.inner_apply _ _⟩

/-- Original label: `prop:finite-products`.
Separability is preserved by the product topology and hence by all of these
finite-product norms. No completeness assumption is needed. -/
theorem finiteProductSeparable {ι : Type u} [Finite ι] (V : ι → Type v)
    [∀ i, TopologicalSpace (V i)] [∀ i, TopologicalSpace.SeparableSpace (V i)]
    (p : ℝ≥0∞) : TopologicalSpace.SeparableSpace (PiLp p V) := by
  exact (PiLp.homeomorph p V).isOpenEmbedding.separableSpace

end Thesis.Foundations.Preliminary.FunctionalAnalysis
