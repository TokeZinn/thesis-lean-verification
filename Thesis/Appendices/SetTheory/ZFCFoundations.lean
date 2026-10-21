import Thesis.Appendices.SetTheory.SetTheory
import Mathlib.SetTheory.ZFC.Basic

/-! # The appendix's set-theoretic statements in a common set universe

`ZFSet` models well-founded extensional sets inside Lean. These results retain
the source's self-membership language and Kuratowski pairs. They complement
the typed constructions used in subsequent analysis; they do not claim to
derive ZFC from no foundational assumptions or to prove its own consistency.
-/

noncomputable section

namespace Thesis.Foundations.Preliminary.SetTheory.ZFC

universe u

/-- Original label: `axiom:existence`. -/
theorem existence : ∃ x : ZFSet.{u}, x = x := ⟨∅, rfl⟩

/-- Original label: `axiom:extensionality`. -/
theorem extensionality (x y : ZFSet.{u}) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  ZFSet.ext h

/-- Original label: `axiom:scheme-of-comprehension`.
External parameters in the formula are included in the predicate. -/
theorem separation (z : ZFSet.{u}) (φ : ZFSet.{u} → Prop) :
    ∃ x : ZFSet.{u}, ∀ y, y ∈ x ↔ y ∈ z ∧ φ y :=
  ⟨ZFSet.sep φ z, fun _ ↦ ZFSet.mem_sep⟩

/-- Original labels: `prop:empty-set-unique`, `defn:empty-set`.

The thesis argument: Existence supplies a set `x`; Separation with the formula
`y ≠ y` cuts out of `x` a set with no elements; Extensionality identifies any
two sets with no elements, since they vacuously have the same elements. -/
theorem unique_empty : ∃! x : ZFSet.{u}, ∀ z, z ∉ x := by
  obtain ⟨x, _⟩ := existence.{u}
  obtain ⟨e, he⟩ := separation x (fun y ↦ y ≠ y)
  have hempty : ∀ z, z ∉ e := fun z hz ↦ ((he z).mp hz).2 rfl
  refine ⟨e, hempty, fun b hb ↦ ?_⟩
  exact extensionality b e (fun z ↦ iff_of_false (hb z) (hempty z))

/-- Original label: `thm:no-universal-set`.
The manuscript's Russell argument, with its separation premise discharged. -/
theorem no_universal_set : ¬ ∃ y : ZFSet.{u}, ∀ x : ZFSet.{u}, x ∈ y :=
  noUniversalObjectOfSeparation (· ∈ ·) separation

/-- Original label: `axiom:foundation`. -/
theorem foundation (x : ZFSet.{u}) (hx : x ≠ ∅) :
    ∃ y, y ∈ x ∧ ¬ ∃ z, z ∈ x ∧ z ∈ y := by
  obtain ⟨y, hy, hxy⟩ := ZFSet.regularity x hx
  refine ⟨y, hy, ?_⟩
  rintro ⟨z, hzx, hzy⟩
  exact ZFSet.notMem_empty z (hxy ▸ ZFSet.mem_inter.mpr ⟨hzx, hzy⟩)

theorem not_self_member (x : ZFSet.{u}) : x ∉ x := ZFSet.mem_irrefl x

/-- Original label: `axiom:pairing`. -/
theorem pairing (x y : ZFSet.{u}) :
    ∃ z : ZFSet.{u}, ∀ w, w ∈ z ↔ w = x ∨ w = y :=
  ⟨{x, y}, fun _ ↦ ZFSet.mem_pair⟩

/-- Original label: `axiom:union`. -/
theorem union (F : ZFSet.{u}) :
    ∃ U : ZFSet.{u}, ∀ x, x ∈ U ↔ ∃ X, X ∈ F ∧ x ∈ X :=
  ⟨ZFSet.sUnion F, fun _ ↦ ZFSet.mem_sUnion⟩

/-- Original label: `axiom:replacement`.
The functional image is a member of the same set universe, not merely an
unrestricted predicate on an already supplied output type. -/
theorem replacement (X : ZFSet.{u}) (φ : ZFSet.{u} → ZFSet.{u} → Prop)
    (h : ∀ x ∈ X, ∃! y, φ x y) :
    ∃ Y : ZFSet.{u}, ∀ y, y ∈ Y ↔ ∃ x ∈ X, φ x y := by
  let f : X → ZFSet.{u} := fun x ↦ Classical.choose (h x x.property)
  have hf (x : X) : φ x (f x) := (Classical.choose_spec (h x x.property)).1
  refine ⟨ZFSet.range f, fun y ↦ ?_⟩
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, hf x⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, ((Classical.choose_spec (h x hx)).2 y hxy).symm⟩

/-- Original label: `axiom:infinity`.
The successor is the literal set operation in the displayed source formula. -/
theorem infinity : ∃ X : ZFSet.{u}, (∅ : ZFSet.{u}) ∈ X ∧
    ∀ x, x ∈ X → x ∪ ({x} : ZFSet.{u}) ∈ X := by
  refine ⟨ZFSet.omega, ZFSet.omega_zero, fun x hx ↦ ?_⟩
  have he : insert x x = x ∪ ({x} : ZFSet.{u}) := by
    ext y
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_union, ZFSet.mem_singleton, or_comm]
  exact he ▸ ZFSet.omega_succ hx

/-- A set is inductive when it contains `∅` and is closed under the successor
`n ↦ n ∪ {n}` of the Infinity axiom. -/
def IsInductive (S : ZFSet.{u}) : Prop :=
  (∅ : ZFSet.{u}) ∈ S ∧ ∀ n, n ∈ S → n ∪ ({n} : ZFSet.{u}) ∈ S

/-- The set `ℕ₀` of natural numbers: by Separation inside the inductive set
supplied by the Infinity axiom, the elements that lie in every inductive set. -/
def naturals : ZFSet.{u} :=
  ZFSet.sep (fun n ↦ ∀ S, IsInductive S → n ∈ S) (Classical.choose infinity.{u})

theorem mem_naturals {n : ZFSet.{u}} :
    n ∈ naturals.{u} ↔ ∀ S, IsInductive S → n ∈ S := by
  have hI : IsInductive (Classical.choose infinity.{u}) := Classical.choose_spec infinity.{u}
  constructor
  · intro hn
    exact (ZFSet.mem_sep.mp hn).2
  · intro hn
    exact ZFSet.mem_sep.mpr ⟨hn _ hI, hn⟩

/-- `ℕ₀` is inductive. -/
theorem naturals_isInductive : IsInductive naturals.{u} := by
  constructor
  · exact mem_naturals.mpr (fun S hS ↦ hS.1)
  · intro n hn
    exact mem_naturals.mpr (fun S hS ↦ hS.2 n (mem_naturals.mp hn S hS))

/-- `ℕ₀` is the least inductive set: it is contained in every inductive set. -/
theorem naturals_least {S : ZFSet.{u}} (hS : IsInductive S) : naturals.{u} ⊆ S :=
  fun _ hn ↦ mem_naturals.mp hn S hS

/-- Original label: `prop:induction`.

The thesis argument in the set universe: `S ⊆ ℕ₀` by assumption; `0 ∈ S` and
`n + 1 = n ∪ {n} ∈ S` for all `n ∈ S` say that `S` is an inductive set; since
`ℕ₀` is the least inductive set, `ℕ₀ ⊆ S`; the two inclusions give `S = ℕ₀`
by Extensionality. -/
theorem induction_naturals {S : ZFSet.{u}} (hS : S ⊆ naturals.{u})
    (hzero : (∅ : ZFSet.{u}) ∈ S)
    (hstep : ∀ n, n ∈ S → n ∪ ({n} : ZFSet.{u}) ∈ S) : S = naturals.{u} := by
  have hinductive : IsInductive S := ⟨hzero, hstep⟩
  have hle : naturals.{u} ⊆ S := naturals_least hinductive
  exact extensionality S naturals (fun n ↦ ⟨fun hn ↦ hS hn, fun hn ↦ hle hn⟩)

/-- Original labels: `axiom:power-set`, `defn:power-set`. -/
theorem power_set (X : ZFSet.{u}) :
    ∃ P : ZFSet.{u}, ∀ Z : ZFSet.{u}, Z ∈ P ↔ Z ⊆ X :=
  ⟨ZFSet.powerset X, fun _ ↦ ZFSet.mem_powerset⟩

/-- Original label: `defn:product-space`. -/
theorem kuratowski_pair (x y : ZFSet.{u}) :
    ZFSet.pair x y = ({{x}, {x, y}} : ZFSet.{u}) := rfl

/-- Original label: `defn:product-space`. -/
theorem product_membership (X Y z : ZFSet.{u}) :
    z ∈ ZFSet.prod X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ZFSet.pair x y :=
  ZFSet.mem_prod

/-- The usual typed product and the manuscript's set-coded product agree. -/
def productEquiv (X Y : ZFSet.{u}) : X × Y ≃ ZFSet.prod X Y :=
  Equiv.ofBijective
    (fun p ↦ ⟨ZFSet.pair p.1 p.2, ZFSet.pair_mem_prod.mpr ⟨p.1.property, p.2.property⟩⟩)
    ⟨by
      intro p q h
      have hp := ZFSet.pair_inj.mp (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext hp.1) (Subtype.ext hp.2), by
      rintro ⟨z, hz⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := ZFSet.mem_prod.mp hz
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy.symm⟩⟩

/-- Original label: `defn:graph`.
The graph is itself a ZFC set of Kuratowski pairs. -/
def functionGraph {X Y : ZFSet.{u}} (f : X → Y) : ZFSet.{u} :=
  ZFSet.range (fun x : X ↦ ZFSet.pair x (f x))

theorem mem_functionGraph {X Y : ZFSet.{u}} (f : X → Y) (z : ZFSet.{u}) :
    z ∈ functionGraph f ↔ ∃ x : X, ZFSet.pair x (f x) = z := ZFSet.mem_range

/-- Original label: `defn:function`. -/
theorem functionGraph_isFunc {X Y : ZFSet.{u}} (f : X → Y) :
    ZFSet.IsFunc X Y (functionGraph f) := by
  constructor
  · intro z hz
    obtain ⟨x, rfl⟩ := (mem_functionGraph f z).mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨x.property, (f x).property⟩
  · intro x hx
    refine ⟨f ⟨x, hx⟩, (mem_functionGraph f _).mpr ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨z, hz⟩ := (mem_functionGraph f _).mp hy
    obtain ⟨hzx, hzy⟩ := ZFSet.pair_inj.mp hz
    have he : z = (⟨x, hx⟩ : X) := Subtype.ext hzx
    simpa only [he] using hzy.symm

def evaluate {X Y f : ZFSet.{u}} (hf : ZFSet.IsFunc X Y f) (x : X) : Y :=
  ⟨Classical.choose (hf.2 x x.property),
    (ZFSet.pair_mem_prod.mp (hf.1 (Classical.choose_spec (hf.2 x x.property)).1)).2⟩

theorem evaluate_mem {X Y f : ZFSet.{u}} (hf : ZFSet.IsFunc X Y f) (x : X) :
    ZFSet.pair x (evaluate hf x) ∈ f :=
  (Classical.choose_spec (hf.2 x x.property)).1

/-- Original label: `prop:graph-defines`.
Literal equality of the graph with the source function relation. -/
theorem graph_equals_function {X Y f : ZFSet.{u}} (hf : ZFSet.IsFunc X Y f) :
    functionGraph (evaluate hf) = f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := (mem_functionGraph _ z).mp hz
    exact evaluate_mem hf x
  · intro hz
    obtain ⟨x, hx, y, _, hxy⟩ := ZFSet.mem_prod.mp (hf.1 hz)
    apply (mem_functionGraph _ z).mpr
    refine ⟨⟨x, hx⟩, ?_⟩
    have he : y = (evaluate hf ⟨x, hx⟩ : ZFSet.{u}) :=
      (Classical.choose_spec (hf.2 x hx)).2 y (by simpa only [hxy] using hz)
    rw [hxy, he]

theorem evaluate_graph {X Y : ZFSet.{u}} (f : X → Y) :
    evaluate (functionGraph_isFunc f) = f := by
  funext x
  apply Subtype.ext
  obtain ⟨z, hz⟩ := (mem_functionGraph f _).mp (evaluate_mem (functionGraph_isFunc f) x)
  obtain ⟨hzx, hzy⟩ := ZFSet.pair_inj.mp hz
  have he : z = x := Subtype.ext hzx
  simpa only [he] using hzy.symm

/-- The relation definition of a function is equivalent to the typed one. -/
def functionEquiv (X Y : ZFSet.{u}) : (X → Y) ≃ {f : ZFSet.{u} // ZFSet.IsFunc X Y f} where
  toFun f := ⟨functionGraph f, functionGraph_isFunc f⟩
  invFun f := evaluate f.property
  left_inv := evaluate_graph
  right_inv f := Subtype.ext (graph_equals_function f.property)

theorem empty_domain_function {Y f : ZFSet.{u}} (hf : ZFSet.IsFunc ∅ Y f) : f = ∅ := by
  apply (ZFSet.eq_empty f).mpr
  intro z hz
  obtain ⟨x, hx, _, _, _⟩ := ZFSet.mem_prod.mp (hf.1 hz)
  exact ZFSet.notMem_empty x hx

/-- Original label: `prop:empty-domain-function`.

The thesis argument: because the domain `∅` has no elements, both graphs are
empty, `∅ = Γ(f) = Γ(f′)`, and the graph-identifies-function proposition
(`graph_equals_function`) then gives `f = Γ(f) = Γ(f′) = f′`. The two functions
are equal as sets, even with different codomains. -/
theorem empty_domain_functions_equal {Y Y' f f' : ZFSet.{u}}
    (hf : ZFSet.IsFunc ∅ Y f) (hf' : ZFSet.IsFunc ∅ Y' f') : f = f' := by
  have hgraph {Z g : ZFSet.{u}} (hg : ZFSet.IsFunc ∅ Z g) :
      functionGraph (evaluate hg) = ∅ := by
    apply extensionality
    intro z
    refine iff_of_false (fun hz ↦ ?_) (ZFSet.notMem_empty z)
    obtain ⟨x, _⟩ := (mem_functionGraph _ z).mp hz
    exact ZFSet.notMem_empty x x.property
  calc f = functionGraph (evaluate hf) := (graph_equals_function hf).symm
    _ = ∅ := hgraph hf
    _ = functionGraph (evaluate hf') := (hgraph hf').symm
    _ = f' := graph_equals_function hf'

/-- Original label: `axiom:choice`.
The selected function is a set-coded relation whose codomain is the union of
the family and whose selected value belongs to its argument. -/
theorem choice (X : ZFSet.{u}) (hX : (∅ : ZFSet.{u}) ∉ X) :
    ∃ f : ZFSet.{u}, ZFSet.IsFunc X (ZFSet.sUnion X) f ∧
      ∀ A ∈ X, ∃ y ∈ A, ZFSet.pair A y ∈ f := by
  have hne (A : X) : ∃ y, y ∈ (A : ZFSet.{u}) := by
    by_contra h
    have he : (A : ZFSet.{u}) = ∅ := (ZFSet.eq_empty A).mpr (by simpa using h)
    exact hX (he ▸ A.property)
  let f : X → ZFSet.sUnion X := fun A ↦
    ⟨Classical.choose (hne A), ZFSet.mem_sUnion.mpr
      ⟨A, A.property, Classical.choose_spec (hne A)⟩⟩
  refine ⟨functionGraph f, functionGraph_isFunc f, fun A hA ↦ ?_⟩
  exact ⟨f ⟨A, hA⟩, Classical.choose_spec (hne ⟨A, hA⟩),
    (mem_functionGraph f _).mpr ⟨⟨A, hA⟩, rfl⟩⟩

end Thesis.Foundations.Preliminary.SetTheory.ZFC
