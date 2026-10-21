import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

/-! # Independent-block bootstrap: selected-array law

`prop:block-bootstrap-invariance`. This proves the complete selected-vector
and measurable-aggregation step for an independent block array.
`Intraday.BootstrapDistribution` derives array independence from independent
whole paths and within-path restrictions, proves the literal half-open time
partition decomposition, and proves invariance for arbitrary random selector
vectors independent of the whole observations.
-/

noncomputable section
namespace Thesis.Intraday.BlockBootstrap
open MeasureTheory ProbabilityTheory

variable {Ω K J X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [Finite J]

omit [Finite J] in
/-- Reusing a path for several intervals still selects distinct array entries:
the interval is part of the index. This prevents a common erroneous demand
that the selected path indices themselves be distinct. -/
theorem selection_injective (choose : J → K) :
    Function.Injective (fun j => (choose j, j)) := by
  intro i j h
  exact congrArg Prod.snd h

/-- Original label: `prop:block-bootstrap-invariance`.
The independent-array stage of the full theorem in `BootstrapDistribution`. -/
theorem selected_vector_same_law (μ : Measure Ω) [IsProbabilityMeasure μ]
    (blocks : K × J → Ω → X) (reference : K) (choose : J → K)
    (hm : ∀ i, AEMeasurable (blocks i) μ) (hind : iIndepFun blocks μ)
    (hlaw : ∀ k j, IdentDistrib (blocks (k, j)) (blocks (reference, j)) μ μ) :
    IdentDistrib (fun ω j => blocks (choose j,j) ω)
      (fun ω j => blocks (reference,j) ω) μ μ := by
  letI := Fintype.ofFinite J
  have hs : iIndepFun (fun j => blocks (choose j,j)) μ :=
    hind.precomp (selection_injective choose)
  have hr : iIndepFun (fun j => blocks (reference,j)) μ :=
    hind.precomp (selection_injective (fun _ : J => reference))
  refine ⟨aemeasurable_pi_lambda _ (fun j => hm _),
    aemeasurable_pi_lambda _ (fun j => hm _), ?_⟩
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun j => hm (choose j,j))).mp hs,
    (iIndepFun_iff_map_fun_eq_pi_map (fun j => hm (reference,j))).mp hr]
  congr 1
  funext j
  exact (hlaw (choose j) j).map_eq

theorem selected_aggregate_same_law (μ : Measure Ω) [IsProbabilityMeasure μ]
    (blocks : K × J → Ω → X) (reference : K) (choose : J → K)
    (hm : ∀ i, AEMeasurable (blocks i) μ) (hind : iIndepFun blocks μ)
    (hlaw : ∀ k j, IdentDistrib (blocks (k, j)) (blocks (reference, j)) μ μ)
    (aggregate : (J → X) → Y) (ha : Measurable aggregate) :
    IdentDistrib (fun ω => aggregate (fun j => blocks (choose j,j) ω))
      (fun ω => aggregate (fun j => blocks (reference,j) ω)) μ μ :=
  (selected_vector_same_law μ blocks reference choose hm hind hlaw).comp ha

end Thesis.Intraday.BlockBootstrap
