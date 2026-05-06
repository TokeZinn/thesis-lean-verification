import Mathlib.Analysis.SpecificLimits.Basic
import Foundations.MarketRepresentation.TuplesMetricTopology
import Foundations.Stochastic.PointProcesses

/-!
# Stochastic Markets: Permuted Tuples

Blueprint module for
`1 - theoretical foundations/5_stochastic_markets.tex`,
the tuple quotient part of "Tuples and Point Processes".

Planned formal content:

* `defn:permutative-equality`;
* `prop:perm-equal-equiv`;
* quotient tuple space;
* `prop:choosing-a-permutation`;
* finite equivalence classes;
* `defn:permuted-tuple-hausdorff-distance`;
* metric, completeness, and separability of permuted tuple space.
-/

namespace Thesis
namespace Foundations
namespace Stochastic
namespace PermutedTuples

open Thesis.Foundations.MarketRepresentation
open Thesis.Foundations.MarketRepresentation.TuplesBasic
open Thesis.Foundations.MarketRepresentation.TuplesMetricTopology
open Thesis.Foundations.MarketRepresentation.FiniteSets
open Thesis.Foundations.MarketRepresentation.FiniteSets.FiniteSubsets
open scoped ENNReal

universe u

/-! ## Permutative Equality -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:permutative-equality`.

Original label: `defn:permutative-equality`.

Informal statement: two tuples are equal up to permutation when one can be
obtained from the other by reindexing its finite domain.

Lean strategy / thesis relation note: the thesis writes
`\bm{x} = \bm{x}' \circ \pi`. The Lean permutation action `permute x π`
is the tuple `x \circ π`, so the formal relation uses the equivalent
orientation `y = permute x π`.
-/
def PermutativeEquality {X : Type u} (x y : Tuple X) : Prop :=
  ∃ π : FinitePermutation x.length, y = permute x π

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:permutative-equality`.

Original label: length part of `defn:permutative-equality`.

Informal statement: permutatively equal tuples have the same length.
-/
theorem length_eq_of_permutativeEquality {X : Type u} {x y : Tuple X}
    (hxy : PermutativeEquality x y) : y.length = x.length := by
  rcases hxy with ⟨π, rfl⟩
  exact permute_length x π

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:perm-equal-equiv`.

Original label: reflexive part of `prop:perm-equal-equiv`.

Informal statement: every tuple is permutatively equal to itself.
-/
theorem permutativeEquality_refl {X : Type u} (x : Tuple X) :
    PermutativeEquality x x := by
  exact ⟨Equiv.refl (Fin x.length), (permute_refl x).symm⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:perm-equal-equiv`.

Original label: inverse-permutation helper in `prop:perm-equal-equiv`.

Informal statement: permuting by `π` and then by `π.symm` returns the original
tuple.
-/
theorem permute_symm {X : Type u} (x : Tuple X)
    (π : FinitePermutation x.length) :
    permute (permute x π) π.symm = x := by
  cases x with
  | mk n f =>
      change (Sigma.mk n (fun i : Fin n => f (π (π.symm i))) : Tuple X) =
        Sigma.mk n f
      congr
      funext i
      rw [Equiv.apply_symm_apply]

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:perm-equal-equiv`.

Original label: composition helper in `prop:perm-equal-equiv`.

Informal statement: applying two tuple permutations is the same as applying
their composed finite permutation.
-/
theorem permute_trans {X : Type u} (x : Tuple X)
    (π σ : FinitePermutation x.length) :
    permute (permute x π) σ = permute x (σ.trans π) := by
  cases x with
  | mk n f =>
      change (Sigma.mk n (fun i : Fin n => f (π (σ i))) : Tuple X) =
        Sigma.mk n (fun i : Fin n => f ((σ.trans π) i))
      congr

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:perm-equal-equiv`.

Original label: symmetric part of `prop:perm-equal-equiv`.

Informal statement: if `x` is equal to `y` up to a permutation, then `y` is
equal to `x` up to the inverse permutation.
-/
theorem permutativeEquality_symm {X : Type u} {x y : Tuple X}
    (hxy : PermutativeEquality x y) : PermutativeEquality y x := by
  rcases hxy with ⟨π, rfl⟩
  exact ⟨π.symm, (permute_symm x π).symm⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:perm-equal-equiv`.

Original label: transitive part of `prop:perm-equal-equiv`.

Informal statement: composing the two witnessing permutations witnesses
transitivity.
-/
theorem permutativeEquality_trans {X : Type u} {x y z : Tuple X}
    (hxy : PermutativeEquality x y) (hyz : PermutativeEquality y z) :
    PermutativeEquality x z := by
  rcases hxy with ⟨π, rfl⟩
  rcases hyz with ⟨σ, rfl⟩
  exact ⟨σ.trans π, (permute_trans x π σ).symm⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:perm-equal-equiv`.

Original label: `prop:perm-equal-equiv`.

Informal statement: permutative equality is an equivalence relation.
-/
def permutativeSetoid (X : Type u) : Setoid (Tuple X) where
  r := PermutativeEquality
  iseqv := ⟨permutativeEquality_refl, permutativeEquality_symm,
    permutativeEquality_trans⟩

/-! ## Quotient Space and Finite Orbits -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:permuted-tuple-quotient-space`.

Original label: `defn:permuted-tuple-quotient-space`.

Informal statement: the space of permuted tuples is the quotient of tuple
space by permutative equality.

Lean strategy / thesis relation note: Lean's `Quot` is the type-theoretic quotient corresponding to
the thesis set of equivalence classes.
-/
abbrev PermutedTupleQuotientSpace (X : Type u) : Type u :=
  Quot (permutativeSetoid X)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:permuted-tuple-quotient-space`.

Original label: class notation in `defn:permuted-tuple-quotient-space`.

Informal statement: the equivalence class of a tuple is the set of all tuples
obtained from it by finite permutations.
-/
def permutativeClass {X : Type u} (x : Tuple X) : Set (Tuple X) :=
  {y | PermutativeEquality x y}

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:permuted-tuple-quotient-space`.

Original label: nonemptiness of a quotient class.

Informal statement: every tuple belongs to its own permutative equivalence
class.
-/
theorem self_mem_permutativeClass {X : Type u} (x : Tuple X) :
    x ∈ permutativeClass x :=
  permutativeEquality_refl x

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:choosing-a-permutation`.

Original label: representative choice for quotient classes.

Informal statement: every quotient class has a representative.

Lean strategy / thesis relation note: the thesis cites choice. Lean's quotient API provides a
canonical representative `Quot.out`, which uses choice internally.
-/
noncomputable def chooseRepresentative {X : Type u}
    (q : PermutedTupleQuotientSpace X) : Tuple X :=
  Quot.out q

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:choosing-a-permutation`.

Original label: `prop:choosing-a-permutation`.

Informal statement: the chosen representative maps back to the quotient class
from which it was chosen.
-/
theorem mk_chooseRepresentative {X : Type u}
    (q : PermutedTupleQuotientSpace X) :
    Quot.mk (permutativeSetoid X) (chooseRepresentative q) = q :=
  Quot.out_eq q

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:finite-equivalence-classes`.

Original label: class equality helper for
`prop:finite-equivalence-classes`.

Informal statement: permutatively equal representatives determine the same
equivalence class.
-/
theorem permutativeClass_eq_of_related {X : Type u} {x y : Tuple X}
    (hxy : PermutativeEquality x y) :
    permutativeClass x = permutativeClass y := by
  ext z
  constructor
  · intro hxz
    exact permutativeEquality_trans (permutativeEquality_symm hxy) hxz
  · intro hyz
    exact permutativeEquality_trans hxy hyz

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:finite-equivalence-classes`.

Original label: `prop:finite-equivalence-classes`.

Informal statement: every permutative equivalence class is finite because it
is the image of the finite permutation group of the tuple length.
-/
theorem finite_permutativeClass {X : Type u} (x : Tuple X) :
    (permutativeClass x).Finite := by
  classical
  refine (Set.finite_range (fun π : FinitePermutation x.length =>
    permute x π)).subset ?_
  intro y hy
  rcases hy with ⟨π, hπ⟩
  exact ⟨π, hπ.symm⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:finite-equivalence-classes`.

Original label: cardinality bound in `prop:finite-equivalence-classes`.

Informal statement: the permutative equivalence class of a tuple has
cardinality at most `\ell(x)!`.

Lean strategy / thesis relation note: the proof follows the thesis literally: the class is contained
in the image of the finite permutation group on `Fin x.length`, and that
group has cardinality `x.length!`.
-/
theorem ncard_permutativeClass_le_factorial {X : Type u} (x : Tuple X) :
    (permutativeClass x).ncard ≤ x.length.factorial := by
  classical
  let f : FinitePermutation x.length → Tuple X := fun π => permute x π
  have hsubset : permutativeClass x ⊆ Set.range f := by
    intro y hy
    rcases hy with ⟨π, hπ⟩
    exact ⟨π, hπ.symm⟩
  have hclass_range :
      (permutativeClass x).ncard ≤ (Set.range f).ncard :=
    Set.ncard_le_ncard hsubset (Set.finite_range f)
  have hrange_domain :
      (Set.range f).ncard ≤
        (Set.univ : Set (FinitePermutation x.length)).ncard := by
    have h :=
      Set.ncard_image_le
        (s := (Set.univ : Set (FinitePermutation x.length))) (f := f)
        (Set.finite_univ)
    simpa [Set.image_univ] using h
  have huniv :
      (Set.univ : Set (FinitePermutation x.length)).ncard =
        x.length.factorial := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    simp [FinitePermutation, Fintype.card_perm, Fintype.card_fin]
  calc
    (permutativeClass x).ncard ≤ (Set.range f).ncard := hclass_range
    _ ≤ (Set.univ : Set (FinitePermutation x.length)).ncard := hrange_domain
    _ = x.length.factorial := huniv

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: orbit map `\mathcal{O}` used in the proof.

Informal statement: a tuple determines the finite subset of tuple space
consisting of its whole permutative orbit.
-/
noncomputable def permutativeOrbit {X : Type u} (x : Tuple X) :
    FiniteSubsets (Tuple X) :=
  ⟨permutativeClass x, finite_permutativeClass x⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: well-definedness of the orbit map on quotient classes.

Informal statement: permutatively equal representatives have the same finite
orbit.
-/
theorem permutativeOrbit_eq_of_related {X : Type u} {x y : Tuple X}
    (hxy : PermutativeEquality x y) :
    permutativeOrbit x = permutativeOrbit y := by
  apply Subtype.ext
  exact permutativeClass_eq_of_related hxy

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: quotient orbit map `\Psi`.

Informal statement: the quotient class of a tuple is represented as the finite
subset of tuple space consisting of all its permutations.
-/
noncomputable def quotientOrbit {X : Type u}
    (q : PermutedTupleQuotientSpace X) : FiniteSubsets (Tuple X) :=
  Quot.lift permutativeOrbit
    (fun _ _ hxy => permutativeOrbit_eq_of_related hxy) q

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
proof of `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: injectivity of the quotient orbit map `\Psi`.

Informal statement: two quotient classes with the same finite orbit are the
same quotient class.
-/
theorem quotientOrbit_injective {X : Type u} :
    Function.Injective (quotientOrbit (X := X)) := by
  intro q r hqr
  refine Quot.induction_on₂ q r ?_ hqr
  intro x y hxyOrbit
  change permutativeOrbit x = permutativeOrbit y at hxyOrbit
  apply Quot.sound
  have hy_mem : y ∈ (permutativeOrbit y : Set (Tuple X)) :=
    self_mem_permutativeClass y
  have hy_mem_x : y ∈ (permutativeOrbit x : Set (Tuple X)) := by
    rw [hxyOrbit]
    exact hy_mem
  exact hy_mem_x

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:permuted-tuple-hausdorff-distance`.

Original label: `defn:permuted-tuple-hausdorff-distance`.

Informal statement: the permuted tuple Hausdorff distance is the Hausdorff
distance between the finite permutation orbits of two quotient classes.

Lean strategy / thesis relation note: this uses the thesis' later "formally more correct"
paraphrase: `d_\pi(x^\pi,y^\pi)` is the Hausdorff distance between the two
finite subsets `O(x)` and `O(y)` of tuple space.
-/
noncomputable def permutedTupleHausdorffEDistance {X : Type u}
    [EMetricSpace X] (q r : PermutedTupleQuotientSpace X) : ENNReal :=
  edist (quotientOrbit q) (quotientOrbit r)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:permuted-tuple-hausdorff-distance`.

Original label: representative formula for
`defn:permuted-tuple-hausdorff-distance`.

Informal statement: evaluating the quotient distance on classes represented
by `x` and `y` unfolds to the Hausdorff distance between their finite orbits.
-/
theorem permutedTupleHausdorffEDistance_mk_mk {X : Type u}
    [EMetricSpace X] (x y : Tuple X) :
    permutedTupleHausdorffEDistance
      (Quot.mk (permutativeSetoid X) x)
      (Quot.mk (permutativeSetoid X) y) =
        edist (permutativeOrbit x) (permutativeOrbit y) :=
  rfl

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: final quotient-distance inequality in
`prop:inverse-permuted-tuple-measure-continuous`.

Informal statement: for fixed-length representatives, the permuted tuple
Hausdorff distance between quotient classes is bounded by the largest
coordinatewise distance between those representatives.

Lean strategy / thesis relation note: the thesis writes
`\mathscr d_\pi(x^\pi,y^\pi) \leq \mathscr d_H(x,y)`. Lean proves the
slightly more concrete fixed-length estimate used in the last step of the
inverse-continuity proof. The proof matches finite permutation orbits point by
point: a permutation of `x` is paired with the same permutation of `y`.
-/
theorem permutedTupleHausdorffEDistance_mk_mk_le_coordinateEDistSup
    {X : Type u} [EMetricSpace X] {n : ℕ} (x y : Fin n → X) :
    permutedTupleHausdorffEDistance
      (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X))
      (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X)) ≤
        coordinateEDistSup x y := by
  classical
  change edist (permutativeOrbit (Sigma.mk n x : Tuple X))
    (permutativeOrbit (Sigma.mk n y : Tuple X)) ≤ coordinateEDistSup x y
  change Metric.hausdorffEDist
    ((permutativeOrbit (Sigma.mk n x : Tuple X)).1 : Set (Tuple X))
    ((permutativeOrbit (Sigma.mk n y : Tuple X)).1 : Set (Tuple X)) ≤
      coordinateEDistSup x y
  apply Metric.hausdorffEDist_le_of_mem_edist
  · intro p hp
    change PermutativeEquality (Sigma.mk n x : Tuple X) p at hp
    rcases hp with ⟨π, rfl⟩
    refine ⟨permute (Sigma.mk n y : Tuple X) π, ?_, ?_⟩
    · change PermutativeEquality (Sigma.mk n y : Tuple X)
        (permute (Sigma.mk n y : Tuple X) π)
      exact ⟨π, rfl⟩
    · change edist
        (Sigma.mk n (fun i : Fin n => x (π i)) : Tuple X)
        (Sigma.mk n (fun i : Fin n => y (π i)) : Tuple X) ≤
          coordinateEDistSup x y
      refine (fixedLength_edist_le_coordinateEDistSup
        (fun i : Fin n => x (π i)) (fun i : Fin n => y (π i))).trans ?_
      rw [coordinateEDistSup]
      apply Finset.sup_le
      intro i _hi
      exact Finset.le_sup (s := Finset.univ)
        (f := fun j : Fin n => edist (x j) (y j)) (Finset.mem_univ (π i))
  · intro p hp
    change PermutativeEquality (Sigma.mk n y : Tuple X) p at hp
    rcases hp with ⟨π, rfl⟩
    refine ⟨permute (Sigma.mk n x : Tuple X) π, ?_, ?_⟩
    · change PermutativeEquality (Sigma.mk n x : Tuple X)
        (permute (Sigma.mk n x : Tuple X) π)
      exact ⟨π, rfl⟩
    · change edist
        (Sigma.mk n (fun i : Fin n => y (π i)) : Tuple X)
        (Sigma.mk n (fun i : Fin n => x (π i)) : Tuple X) ≤
          coordinateEDistSup x y
      refine (fixedLength_edist_le_coordinateEDistSup
        (fun i : Fin n => y (π i)) (fun i : Fin n => x (π i))).trans ?_
      rw [coordinateEDistSup]
      apply Finset.sup_le
      intro i _hi
      simpa [edist_comm] using
        Finset.le_sup (s := Finset.univ)
          (f := fun j : Fin n => edist (x j) (y j)) (Finset.mem_univ (π i))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Proposition `prop:inverse-permuted-tuple-measure-continuous`.

Original label: epsilon form of the final quotient-distance inequality.

Informal statement: if two fixed-length representatives are coordinatewise
within `ε`, then their quotient classes are within `ε` in permuted tuple
Hausdorff distance.
-/
theorem permutedTupleHausdorffEDistance_mk_mk_lt_of_forall_edist_lt
    {X : Type u} [EMetricSpace X] {n : ℕ} {x y : Fin n → X}
    {ε : ℝ≥0∞} (hε_pos : 0 < ε)
    (hxy : ∀ i : Fin n, edist (x i) (y i) < ε) :
    permutedTupleHausdorffEDistance
      (Quot.mk (permutativeSetoid X) (Sigma.mk n x : Tuple X))
      (Quot.mk (permutativeSetoid X) (Sigma.mk n y : Tuple X)) < ε := by
  have hsup : coordinateEDistSup x y < ε := by
    rw [coordinateEDistSup]
    exact (Finset.sup_lt_iff hε_pos).mpr (fun i _hi => hxy i)
  exact lt_of_le_of_lt
    (permutedTupleHausdorffEDistance_mk_mk_le_coordinateEDistSup x y) hsup

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Definition `defn:permuted-tuple-hausdorff-distance`.

Original label: distance structure following
`defn:permuted-tuple-hausdorff-distance`.

Informal statement: use the permuted tuple Hausdorff edistance as the
extended distance on the quotient space.
-/
noncomputable instance instEDist {X : Type u} [EMetricSpace X] :
    EDist (PermutedTupleQuotientSpace X) where
  edist := permutedTupleHausdorffEDistance

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: pseudometric part of
`thm:permuted-tuple-hausdorff-metric-complete-separable`.

Informal statement: the permuted tuple Hausdorff edistance satisfies the
extended pseudometric laws because it is the Hausdorff edistance between the
finite quotient orbits.
-/
noncomputable instance instPseudoEMetricSpace {X : Type u} [EMetricSpace X] :
    PseudoEMetricSpace (PermutedTupleQuotientSpace X) where
  edist_self := by
    intro q
    change edist (quotientOrbit q) (quotientOrbit q) = 0
    simp
  edist_comm := by
    intro q r
    change edist (quotientOrbit q) (quotientOrbit r) =
      edist (quotientOrbit r) (quotientOrbit q)
    exact edist_comm _ _
  edist_triangle := by
    intro q r s
    change edist (quotientOrbit q) (quotientOrbit s) ≤
      edist (quotientOrbit q) (quotientOrbit r) +
        edist (quotientOrbit r) (quotientOrbit s)
    exact edist_triangle _ _ _

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: metric part of
`thm:permuted-tuple-hausdorff-metric-complete-separable`.

Informal statement: the permuted tuple Hausdorff edistance separates quotient
classes, because the orbit map into finite subsets is injective and the
finite-subset Hausdorff edistance is an extended metric.

Lean strategy / thesis relation note: this proves the metric-space part of the theorem. The
separability and completeness transfer statements are left as later
topological work, matching the remaining paragraphs of the thesis proof.
-/
noncomputable instance instEMetricSpace {X : Type u} [EMetricSpace X] :
    EMetricSpace (PermutedTupleQuotientSpace X) :=
  EMetricSpace.mk (by
    intro q r hqr
    apply quotientOrbit_injective
    change edist (quotientOrbit q) (quotientOrbit r) = 0 at hqr
    exact edist_eq_zero.mp hqr)

/-! ## Separability and Completeness Transfers -/

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: continuity estimate for the quotient map in the separability
and completeness paragraphs.

Informal statement: if two tuple representatives are within Hausdorff
distance `< 1`, then their permuted-tuple classes are no farther apart than
the original tuple distance.

Lean strategy / thesis relation note: the proof is the local version needed by the thesis. Below
radius `1`, Chapter 2 identifies the tuple Hausdorff distance with the
fixed-length coordinate supremum; the quotient orbit Hausdorff distance is
bounded by matching each permutation of one tuple with the same permutation of
the other.
-/
theorem quotientMk_edist_le_of_tuple_edist_lt_one {X : Type u}
    [EMetricSpace X] {x y : Tuple X}
    (hxy : edist x y < (1 : ENNReal)) :
    edist (Quot.mk (permutativeSetoid X) x)
      (Quot.mk (permutativeSetoid X) y) ≤ edist x y := by
  rcases x with ⟨m, x⟩
  rcases y with ⟨n, y⟩
  have hmn : m = n := by
    simpa [Tuple.length] using
      (length_eq_of_edist_lt_one
        (x := (Sigma.mk m x : Tuple X))
        (y := (Sigma.mk n y : Tuple X)) hxy)
  subst n
  have hcoord :
      edist (Sigma.mk m x : Tuple X) (Sigma.mk m y : Tuple X) =
        coordinateEDistSup x y :=
    fixedLength_edist_eq_coordinateEDistSup_of_lt_one hxy
  rw [hcoord]
  exact permutedTupleHausdorffEDistance_mk_mk_le_coordinateEDistSup x y

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: quotient-map epsilon estimate used in the separability
paragraph.

Informal statement: if two tuples are closer than both `ε` and `1`, then
their permuted-tuple classes are within `ε`.
-/
theorem quotientMk_edist_lt_of_tuple_edist_lt_min {X : Type u}
    [EMetricSpace X] {x y : Tuple X} {ε : ENNReal}
    (hxy : edist x y < min ε 1) :
    edist (Quot.mk (permutativeSetoid X) x)
      (Quot.mk (permutativeSetoid X) y) < ε := by
  have hxy_one : edist x y < (1 : ENNReal) :=
    lt_of_lt_of_le hxy (min_le_right ε 1)
  exact lt_of_le_of_lt
    (quotientMk_edist_le_of_tuple_edist_lt_one hxy_one)
    (lt_of_lt_of_le hxy (min_le_left ε 1))

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: chosen representative belongs to its orbit.

Informal statement: the representative chosen from a quotient class is an
element of the finite orbit representing that class.
-/
theorem chooseRepresentative_mem_quotientOrbit {X : Type u}
    (q : PermutedTupleQuotientSpace X) :
    chooseRepresentative q ∈
      ((quotientOrbit q).1 : Set (Tuple X)) := by
  have hOrbit : permutativeOrbit (chooseRepresentative q) = quotientOrbit q := by
    simpa [quotientOrbit] using
      congrArg (quotientOrbit (X := X)) (mk_chooseRepresentative q)
  rw [← hOrbit]
  change chooseRepresentative q ∈ permutativeClass (chooseRepresentative q)
  exact self_mem_permutativeClass (chooseRepresentative q)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: orbit membership returns the quotient class.

Informal statement: every tuple in the finite orbit of a quotient class maps
back to that quotient class.
-/
theorem mk_eq_of_mem_quotientOrbit {X : Type u}
    {q : PermutedTupleQuotientSpace X} {x : Tuple X}
    (hx : x ∈ ((quotientOrbit q).1 : Set (Tuple X))) :
    Quot.mk (permutativeSetoid X) x = q := by
  refine Quot.induction_on q ?_ hx
  intro y hy
  change x ∈ permutativeClass y at hy
  exact Quot.sound (permutativeEquality_symm hy)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: finite-minimum representative step in the completeness proof.

Informal statement: if a representative `x` of class `q` is fixed and class
`r` is within quotient Hausdorff distance `< ε` of `q`, then some
representative `y` of `r` is within tuple Hausdorff distance `< ε` of `x`.

Lean strategy / thesis relation note: the thesis phrases this using an attained finite minimum. Lean
uses mathlib's finite-Hausdorff lemma
`Metric.exists_edist_lt_of_hausdorffEDist_lt`, which gives the same
representative-selection step in strict epsilon form.
-/
theorem exists_representative_edist_lt_of_quotient_edist_lt
    {X : Type u} [EMetricSpace X]
    {q r : PermutedTupleQuotientSpace X} {x : Tuple X} {ε : ENNReal}
    (hx : x ∈ ((quotientOrbit q).1 : Set (Tuple X)))
    (hqr : edist q r < ε) :
    ∃ y : Tuple X, Quot.mk (permutativeSetoid X) y = r ∧ edist x y < ε := by
  change edist (quotientOrbit q) (quotientOrbit r) < ε at hqr
  rcases Metric.exists_edist_lt_of_hausdorffEDist_lt hx hqr with
    ⟨y, hyr, hxy⟩
  exact ⟨y, mk_eq_of_mem_quotientOrbit hyr, hxy⟩

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: quotient length used in the completeness proof.

Informal statement: a permuted-tuple class has a well-defined tuple length.
-/
def quotientLength {X : Type u} :
    PermutedTupleQuotientSpace X → ℕ :=
  Quot.lift Tuple.length
    (fun _ _ hxy => (length_eq_of_permutativeEquality hxy).symm)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: length rigidity below quotient distance `1`.

Informal statement: permuted-tuple classes at distance below `1` have the
same tuple length.
-/
theorem quotientLength_eq_of_edist_lt_one {X : Type u} [EMetricSpace X]
    {q r : PermutedTupleQuotientSpace X}
    (hqr : edist q r < (1 : ENNReal)) :
    quotientLength q = quotientLength r := by
  refine Quot.induction_on₂ q r ?_ hqr
  intro x y hxy
  change edist (permutativeOrbit x) (permutativeOrbit y) <
    (1 : ENNReal) at hxy
  have hx_mem : x ∈ ((permutativeOrbit x).1 : Set (Tuple X)) := by
    change x ∈ permutativeClass x
    exact self_mem_permutativeClass x
  rcases Metric.exists_edist_lt_of_hausdorffEDist_lt hx_mem hxy with
    ⟨z, hz_mem, hxz⟩
  have hxz_len : x.length = z.length :=
    length_eq_of_edist_lt_one hxz
  have hzy_len : z.length = y.length := by
    change PermutativeEquality y z at hz_mem
    exact length_eq_of_permutativeEquality hz_mem
  exact hxz_len.trans hzy_len

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: Cauchy length-stabilization step.

Informal statement: a Cauchy sequence of permuted-tuple classes eventually
lies in one fixed-length quotient layer.
-/
theorem cauchySeq_eventually_constant_quotientLength {X : Type u}
    [EMetricSpace X] {u : ℕ → PermutedTupleQuotientSpace X}
    (hu : CauchySeq u) :
    ∃ L : ℕ, ∀ᶠ n in Filter.atTop, quotientLength (u n) = L := by
  rcases (EMetric.cauchySeq_iff.1 hu) (1 : ENNReal) zero_lt_one with
    ⟨N, hN⟩
  refine ⟨quotientLength (u N), Filter.eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn
  exact quotientLength_eq_of_edist_lt_one (hN n hn N le_rfl)

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: representative membership from quotient equality.

Informal statement: if `x` represents `q`, then `x` belongs to the finite
orbit attached to `q`.
-/
theorem mem_quotientOrbit_of_mk_eq {X : Type u}
    {q : PermutedTupleQuotientSpace X} {x : Tuple X}
    (hx : Quot.mk (permutativeSetoid X) x = q) :
    x ∈ ((quotientOrbit q).1 : Set (Tuple X)) := by
  rw [← hx]
  change x ∈ permutativeClass x
  exact self_mem_permutativeClass x

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: separability transfer in
`thm:permuted-tuple-hausdorff-metric-complete-separable`.

Informal statement: if the ambient space `X` is separable, then the permuted
tuple quotient space is separable.

Lean strategy / thesis relation note: this is the manuscript's quotient-image argument. Chapter 2
gives a countable dense set `D` of tuples; the set of quotient classes
represented by elements of `D` is countable, and density follows from the
local quotient-map epsilon estimate above.
-/
theorem separableSpace {X : Type u} [EMetricSpace X]
    [TopologicalSpace.SeparableSpace X] :
    @TopologicalSpace.SeparableSpace
      (PermutedTupleQuotientSpace X)
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (PermutedTupleQuotientSpace X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  haveI : TopologicalSpace.SeparableSpace (Tuple X) :=
    TuplesMetricTopology.separableSpace (X := X)
  rcases TopologicalSpace.exists_countable_dense (Tuple X) with
    ⟨D, hD_count, hD_dense⟩
  let qD : Set (PermutedTupleQuotientSpace X) :=
    (fun x : Tuple X => Quot.mk (permutativeSetoid X) x) '' D
  refine ⟨⟨qD, hD_count.image _, ?_⟩⟩
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.mpr
  intro q
  rw [EMetric.mem_closure_iff]
  intro ε hε
  rcases Quot.exists_rep q with ⟨x, rfl⟩
  have hx_closure : x ∈ closure D := by
    rw [dense_iff_closure_eq.mp hD_dense]
    trivial
  rcases EMetric.mem_closure_iff.mp hx_closure (min ε 1)
      (lt_min hε zero_lt_one) with ⟨y, hyD, hxy⟩
  refine ⟨Quot.mk (permutativeSetoid X) y, ?_, ?_⟩
  · exact ⟨y, hyD, rfl⟩
  · exact quotientMk_edist_lt_of_tuple_edist_lt_min hxy

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: completeness transfer in
`thm:permuted-tuple-hausdorff-metric-complete-separable`.

Informal statement: every Cauchy sequence in the permuted-tuple quotient has
a convergent subsequence obtained by recursively choosing close tuple
representatives.

Lean strategy / thesis relation note: this is the thesis subsequence/lift paragraph. Lean states the
limit with the metric topology explicitly because `Quot` also carries a
native quotient topology. The representative choices are made recursively
using the finite-Hausdorff selection lemma above.
-/
theorem cauchySeq_tendsto_of_complete {X : Type u} [EMetricSpace X]
    [CompleteSpace X] {u : ℕ → PermutedTupleQuotientSpace X}
    (hu : CauchySeq u) :
    ∃ q : PermutedTupleQuotientSpace X,
      Filter.Tendsto u Filter.atTop
        (@nhds (PermutedTupleQuotientSpace X)
          PseudoEMetricSpace.toUniformSpace.toTopologicalSpace q) := by
  letI : TopologicalSpace (Tuple X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (PermutedTupleQuotientSpace X) :=
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  haveI : CompleteSpace (Tuple X) :=
    TuplesMetricTopology.completeSpace (X := X)
  let radius : ℕ → ENNReal := fun k =>
    (1 : ENNReal) / (2 : ENNReal) ^ k
  have hradius_pos : ∀ k, 0 < radius k := by
    intro k
    exact ENNReal.div_pos (by simp) (by finiteness)
  let N : ℕ → ℕ := fun k =>
    Classical.choose ((EMetric.cauchySeq_iff.1 hu) (radius k) (hradius_pos k))
  have hN : ∀ k, ∀ m ≥ N k, ∀ n ≥ N k,
      edist (u m) (u n) < radius k := by
    intro k
    exact Classical.choose_spec
      ((EMetric.cauchySeq_iff.1 hu) (radius k) (hradius_pos k))
  let φ : ℕ → ℕ :=
    Nat.rec (N 0) (fun k previous => max (previous + 1) (N (k + 1)))
  have hφ_ge_N : ∀ k, N k ≤ φ k := by
    intro k
    induction k with
    | zero =>
        exact le_rfl
    | succ k ih =>
        exact le_max_right (φ k + 1) (N (k + 1))
  have hφ_lt_succ : ∀ k, φ k < φ (k + 1) := by
    intro k
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (φ k))
      (le_max_left (φ k + 1) (N (k + 1)))
  have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ hφ_lt_succ
  have hφ_succ_close : ∀ k,
      edist (u (φ k)) (u (φ (k + 1))) < radius k := by
    intro k
    exact hN k (φ k) (hφ_ge_N k) (φ (k + 1))
      (le_trans (hφ_ge_N k) (le_of_lt (hφ_lt_succ k)))
  let base :
      {x : Tuple X // Quot.mk (permutativeSetoid X) x = u (φ 0)} :=
    ⟨chooseRepresentative (u (φ 0)), mk_chooseRepresentative (u (φ 0))⟩
  let next :
      (k : ℕ) →
        {x : Tuple X // Quot.mk (permutativeSetoid X) x = u (φ k)} →
        {x : Tuple X // Quot.mk (permutativeSetoid X) x = u (φ (k + 1))} :=
    fun k previous =>
      let hx : previous.1 ∈
          ((quotientOrbit (u (φ k))).1 : Set (Tuple X)) :=
        mem_quotientOrbit_of_mk_eq previous.2
      let hchoice :=
        exists_representative_edist_lt_of_quotient_edist_lt
          (q := u (φ k)) (r := u (φ (k + 1))) (x := previous.1)
          (ε := radius k) hx (hφ_succ_close k)
      ⟨Classical.choose hchoice, (Classical.choose_spec hchoice).1⟩
  have next_edist : ∀ k
      (previous :
        {x : Tuple X // Quot.mk (permutativeSetoid X) x = u (φ k)}),
      edist previous.1 (next k previous).1 < radius k := by
    intro k previous
    let hx : previous.1 ∈
        ((quotientOrbit (u (φ k))).1 : Set (Tuple X)) :=
      mem_quotientOrbit_of_mk_eq previous.2
    let hchoice :=
      exists_representative_edist_lt_of_quotient_edist_lt
        (q := u (φ k)) (r := u (φ (k + 1))) (x := previous.1)
        (ε := radius k) hx (hφ_succ_close k)
    change edist previous.1 (Classical.choose hchoice) < radius k
    exact (Classical.choose_spec hchoice).2
  let lifted : (k : ℕ) →
      {x : Tuple X // Quot.mk (permutativeSetoid X) x = u (φ k)} :=
    Nat.rec base (fun k previous => next k previous)
  let y : ℕ → Tuple X := fun k => (lifted k).1
  have hy_mk : ∀ k, Quot.mk (permutativeSetoid X) (y k) = u (φ k) := by
    intro k
    exact (lifted k).2
  have hy_step : ∀ k, edist (y k) (y (k + 1)) < radius k := by
    intro k
    change edist (lifted k).1 (next k (lifted k)).1 < radius k
    exact next_edist k (lifted k)
  have hy_cauchy : CauchySeq y := by
    refine cauchySeq_of_edist_le_geometric_two (1 : ENNReal) (by simp) ?_
    intro k
    exact le_of_lt (by simpa [radius, y] using hy_step k)
  rcases TuplesMetricTopology.cauchySeq_tendsto_of_complete
      (X := X) hy_cauchy with ⟨ylim, hy_lim⟩
  let qlim : PermutedTupleQuotientSpace X := Quot.mk (permutativeSetoid X) ylim
  have hsub_tendsto :
      Filter.Tendsto (u ∘ φ) Filter.atTop (nhds qlim) := by
    rw [EMetric.tendsto_nhds]
    intro ε hε
    rcases exists_pos_lt_ennreal hε with ⟨δ, hδpos, hδε⟩
    have hy_event : ∀ᶠ k in Filter.atTop,
        edist (y k) ylim < min δ 1 :=
      EMetric.tendsto_nhds.1 hy_lim (min δ 1) (lt_min hδpos zero_lt_one)
    filter_upwards [hy_event] with k hk
    have hqdist :
        edist (Quot.mk (permutativeSetoid X) (y k)) qlim < δ :=
      quotientMk_edist_lt_of_tuple_edist_lt_min (x := y k) (y := ylim)
        (ε := δ) hk
    have hqdistε :
        edist (Quot.mk (permutativeSetoid X) (y k)) qlim < ε :=
      lt_trans hqdist hδε
    simpa [Function.comp, qlim, hy_mk k] using hqdistε
  refine ⟨qlim, ?_⟩
  exact tendsto_nhds_of_cauchySeq_of_subseq hu
    hφ_strict.tendsto_atTop hsub_tendsto

/--
Thesis source:
`1 - theoretical foundations/5_stochastic_markets.tex`,
Theorem `thm:permuted-tuple-hausdorff-metric-complete-separable`.

Original label: completeness transfer in
`thm:permuted-tuple-hausdorff-metric-complete-separable`.

Informal statement: if the ambient space `X` is complete, then the
permuted-tuple quotient is complete for the thesis' orbit-Hausdorff metric.
-/
theorem completeSpace {X : Type u} [EMetricSpace X] [CompleteSpace X] :
    CompleteSpace (PermutedTupleQuotientSpace X) := by
  refine EMetric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  exact cauchySeq_tendsto_of_complete hu

end PermutedTuples
end Stochastic
end Foundations
end Thesis
