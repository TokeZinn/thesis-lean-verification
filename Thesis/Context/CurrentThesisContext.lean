import Thesis.Foundations.MarketActions.Composite
import Thesis.Foundations.MarketClearing.Equilibrium
import Thesis.Appendices.Analysis.BoundedMetric
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! # Contracts made explicit in the September 2026 thesis

These declarations formalize the mathematical content of the new modelling
remarks. A record of required data is not a proof that an actual venue supplies
that data or satisfies the associated predicates.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Thesis.Foundations.CurrentThesisContext

open MarketRepresentation MarketRepresentation.TuplesBasic MarketRepresentation.TuplesMetricTopology
open MarketActions.Composite

universe u v w

/-- Original label: `thm:tuple-space-properties`.
Small tuple perturbations preserve length and compare the existing indexed
coordinates. This asserts a property of the chosen representation. -/
theorem tuple_small_perturbation {X : Type u} [EMetricSpace X] {n : ℕ}
    {x y : Fin n → X}
    (h : edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) < 1) :
    ∀ i, edist (x i) (y i) ≤ edist (Sigma.mk n x : Tuple X) (Sigma.mk n y : Tuple X) :=
  coordinate_edist_le_fixedLength_edist_of_lt_one h

/-- Original label: `thm:tuple-space-properties`. -/
theorem tuple_length_rigid {X : Type u} [EMetricSpace X] {x y : Tuple X}
    (h : edist x y < 1) : x.length = y.length :=
  length_eq_of_edist_lt_one h

/-- Original block id: `source:2 - day-ahead/2_clearing_operator_price_curves.tex:166:defn:7`
A parametrisation of an arbitrary set by a parameter set is a surjection. -/
structure Parametrisation (U : Type u) (X : Type v) where
  toFun : U → X
  surjective : Function.Surjective toFun

/-- Original labels: `rem:pointwise-versus-lp`, `rem:lp-point-evaluation`.
On a nonatomic space, a change at a prescribed point does not change the
almost-everywhere class. Both representatives are in every finite-exponent
Lp space; their values at that point are different. -/
theorem point_evaluation_not_ae_invariant {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [NoAtoms μ] (a : X) (p : ℝ≥0∞) :
    ∃ f g : X → ℝ, MemLp f p μ ∧ MemLp g p μ ∧ f =ᵐ[μ] g ∧ f a ≠ g a := by
  classical
  let g : X → ℝ := fun x => if x = a then 1 else 0
  have hg : g =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [μ.ae_ne a] with x hx
    simp [g, hx]
  refine ⟨fun _ => 0, g, MemLp.zero', MemLp.ae_eq hg.symm MemLp.zero', hg.symm, ?_⟩
  simp [g]

/-- Original labels: `rem:pointwise-versus-lp`, `rem:lp-point-evaluation`.
There is no operation on L² classes that evaluates every representative at a
prescribed point of a nonatomic space. -/
theorem no_evaluation_on_L2 {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [NoAtoms μ] (a : X) :
    ¬ ∃ eval : Lp ℝ 2 μ → ℝ,
      ∀ (f : X → ℝ) (hf : MemLp f 2 μ), eval (hf.toLp f) = f a := by
  rintro ⟨eval, heval⟩
  obtain ⟨f, g, hf, hg, hfg, hne⟩ := point_evaluation_not_ae_invariant μ a 2
  apply hne
  rw [← heval f hf, ← heval g hg, hf.toLp_congr hg hfg]

/-- Original label: `rem:bijection-not-homeomorphism`.
Even an identity bijection need not be continuous for the supplied topologies. -/
theorem bijection_need_not_be_continuous :
    ∃ f : Bool ≃ Bool, ¬ @Continuous Bool Bool ⊤ ⊥ f := by
  refine ⟨Equiv.refl Bool, ?_⟩
  change ¬ @Continuous Bool Bool ⊤ ⊥ id
  rw [continuous_id_iff_le]
  intro h
  have hopen : @IsOpen Bool ⊤ ({true} : Set Bool) := h _ trivial
  rcases (TopologicalSpace.isOpen_top_iff _).mp hopen with hempty | hall
  · exact Set.singleton_ne_empty true hempty
  · have hf : false ∈ ({true} : Set Bool) := by rw [hall]; trivial
    simp at hf

/-- Original label: `rem:bijection-not-homeomorphism`.
The canonical tag-forgetting map is injective exactly for pairwise disjoint
components. This does not assert the converse for arbitrary bijections. -/
theorem tag_forgetting_injective_iff {A : Type u} {B : Type v} (S : A → Set B) :
    Function.Injective (SetDisjointUnion.forget (S := S)) ↔ PairwiseDisjoint S := by
  constructor
  · intro hinj a b hab x hxa hxb
    have h : (⟨a, ⟨x, hxa⟩⟩ : SetDisjointUnion S) = ⟨b, ⟨x, hxb⟩⟩ :=
      hinj rfl
    exact hab (congrArg Sigma.fst h)
  · exact SetDisjointUnion.forget_injective_of_pairwiseDisjoint

/-- Original label: `rem:group-completion-scope`.
A faithful additive embedding into a group forces cancellation in the source.
Thus introducing formal inverses cannot faithfully preserve a noncancellative
model without first identifying elements. -/
theorem cancellation_of_faithful_group_embedding
    {M : Type u} {G : Type v} [AddMonoid M] [AddGroup G]
    (f : M →+ G) (hf : Function.Injective f) (a b c : M)
    (h : a + c = b + c) : a = b := by
  apply hf
  apply add_right_cancel (b := f c)
  simpa only [map_add] using congrArg f h

/-- Original label: `rem:group-completion-scope`.
An algebraic inverse can lie outside a natural admissible subset. -/
theorem nonnegative_quantities_not_closed_under_inverse :
    ¬ ∀ q : ℝ, 0 ≤ q → 0 ≤ -q := by
  intro h
  have := h 1 (by norm_num)
  norm_num at this

end Thesis.Foundations.CurrentThesisContext
