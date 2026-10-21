import Thesis.Foundations.Stochastic.PointProcessAlignment
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Fintype.BigOperators

/-! # Exact multiplicity of each reordered tuple

The source proof of `prop:finite-equivalence-classes` has three steps: a
permutation fixes `x` iff it preserves every level set `I_a = {i | x(i) = a}`,
so the fixing permutations are in bijection with `∏_a P(I_a)` and number
`m_1! ⋯ m_κ!`; right multiplication by `σ₀⁻¹` carries the fibre over
`x ∘ σ₀` onto the fibre over `x`; and the fibres of `σ ↦ x ∘ σ` partition
`P_n` into `|x^π|` blocks of that common size, whence
`|x^π| = n! / (m_1! ⋯ m_κ!)`. The three declarations below follow those steps.
-/

noncomputable section
namespace Thesis.Foundations.Stochastic.PermutationMultiplicity
open MarketRepresentation MarketRepresentation.TuplesBasic
open MarketRepresentation.TuplesSorting PermutedTuples PointProcessAlignment
open scoped BigOperators

variable {X : Type*}

theorem permute_eq_self_iff (x : Tuple X) (π : FinitePermutation x.length) :
    permute x π = x ↔ x.2 ∘ π = x.2 := by
  cases x with
  | mk n x =>
      exact ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => congrArg (Sigma.mk n) h⟩

/-- Original label: `prop:finite-equivalence-classes`.
The level-set criterion of the source proof: `x ∘ σ = x` holds iff
`x(σ(i)) = x(i)` for every `i`, i.e. iff `σ` maps each level set
`I_a = {i | x(i) = a}` into itself. -/
theorem permute_eq_self_iff_levelSets (x : Tuple X) (π : FinitePermutation x.length) :
    permute x π = x ↔ ∀ a : X, ∀ i, x.2 i = a → x.2 (π i) = a := by
  rw [permute_eq_self_iff]
  constructor
  · rintro h a i rfl
    exact congrFun h i
  · intro h
    funext i
    exact h (x.2 i) i rfl

open Classical in
/-- Original label: `prop:finite-equivalence-classes`.
`|S(x)| = m_1! ⋯ m_κ!`: by `permute_eq_self_iff_levelSets` the permutations
fixing `x` are those preserving every level set, and Mathlib's
`DomMulAct.stabilizer_card'` is exactly the bijection of that stabiliser with
the product `∏_a P(I_a)` of the level-set permutation groups, of cardinality
`∏_a |I_a|!` over the distinct entries `a` of `x`. -/
theorem stabilizing_permutations_card (x : Tuple X) :
    Nat.card {π : FinitePermutation x.length // permute x π = x} =
      ∏ a ∈ Finset.univ.image x.2,
        (Nat.card {i : Fin x.length // x.2 i = a}).factorial := by
  classical
  simp_rw [permute_eq_self_iff, Nat.card_eq_fintype_card]
  exact DomMulAct.stabilizer_card' x.2

open Classical in
/-- Original label: `prop:finite-equivalence-classes`.
`|S(y)| = |S(x)|` for every `y = x ∘ σ₀` in the class: right multiplication
`σ ↦ σ ∘ σ₀⁻¹` (here `Equiv.mulRight`) is a bijection of `P_n` carrying the
fibre over `y` onto the fibre over `x`. This includes repeated values and the
empty tuple. -/
theorem reordered_tuple_permutations_card (x : Tuple X) (σ : FinitePermutation x.length) :
    Nat.card {π : FinitePermutation x.length // permute x π = permute x σ} =
      ∏ a ∈ Finset.univ.image x.2,
        (Nat.card {i : Fin x.length // x.2 i = a}).factorial := by
  classical
  let e : {π : FinitePermutation x.length // permute x π = x} ≃
      {π : FinitePermutation x.length // permute x π = permute x σ} :=
    Equiv.subtypeEquiv (Equiv.mulRight σ) (fun π => (permute_mul_eq_iff x π σ).symm)
  exact (Nat.card_congr e).symm.trans (stabilizing_permutations_card x)

/-- The fibre map `σ ↦ x ∘ σ` from `P_n` onto the class `x^π`. -/
def toOrbit (x : Tuple X) (σ : FinitePermutation x.length) : permutativeClass x :=
  ⟨permute x σ, ⟨σ, rfl⟩⟩

open Classical in
/-- Original label: `prop:finite-equivalence-classes`.
The source's counting identity `n! = |P_n| = Σ_{y ∈ x^π} |S(y)| = |x^π| · m_1! ⋯ m_κ!`:
the fibres of `σ ↦ x ∘ σ` partition `P_n` into `|x^π|` blocks, each of the
common size given by `reordered_tuple_permutations_card`. -/
theorem orbit_card_mul_multiplicities (x : Tuple X) :
    (permutativeClass x).ncard *
      (∏ a ∈ Finset.univ.image x.2,
        (Nat.card {i : Fin x.length // x.2 i = a}).factorial) = x.length.factorial := by
  classical
  letI : Fintype (permutativeClass x) := (finite_permutativeClass x).fintype
  let f := toOrbit x
  have hfiber : ∀ y : permutativeClass x,
      Fintype.card {σ : FinitePermutation x.length // f σ = y} =
        ∏ a ∈ Finset.univ.image x.2,
          (Nat.card {i : Fin x.length // x.2 i = a}).factorial := by
    intro y
    obtain ⟨σ, hσ⟩ := y.property
    let e : {τ : FinitePermutation x.length // f τ = y} ≃
        {τ : FinitePermutation x.length // permute x τ = permute x σ} :=
      Equiv.subtypeEquiv (Equiv.refl _) (by
        intro τ
        simp only [Equiv.refl_apply, Subtype.ext_iff]
        change permute x τ = y.val ↔ permute x τ = permute x σ
        rw [hσ])
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
    exact reordered_tuple_permutations_card x σ
  have hcard : Fintype.card (FinitePermutation x.length) =
      ∑ y : permutativeClass x, Fintype.card {σ : FinitePermutation x.length // f σ = y} := by
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
  simp_rw [hfiber] at hcard
  rw [Fintype.card_perm] at hcard
  have horbit : Fintype.card (permutativeClass x) = (permutativeClass x).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, horbit, Fintype.card_fin]
    using hcard.symm

open Classical in
/-- Original label: `prop:finite-equivalence-classes`.
The exact multinomial cardinality `|x^π| = n! / (m_1! ⋯ m_κ!)`, including
repeated entries and the empty tuple, obtained from the equal-fibre identity
`orbit_card_mul_multiplicities` by dividing out the common fibre size. -/
theorem orbit_ncard_eq_factorial_div (x : Tuple X) :
    (permutativeClass x).ncard = x.length.factorial /
      (∏ a ∈ Finset.univ.image x.2,
        (Nat.card {i : Fin x.length // x.2 i = a}).factorial) := by
  classical
  have hpos : 0 < ∏ a ∈ Finset.univ.image x.2,
      (Nat.card {i : Fin x.length // x.2 i = a}).factorial :=
    Finset.prod_pos fun _ _ => Nat.factorial_pos _
  rw [← orbit_card_mul_multiplicities x, Nat.mul_div_cancel _ hpos]

end Thesis.Foundations.Stochastic.PermutationMultiplicity
