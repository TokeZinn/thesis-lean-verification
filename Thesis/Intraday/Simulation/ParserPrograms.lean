import Thesis.Intraday.Simulation.ParserMatching
import Mathlib.Algebra.Order.Monoid.WithTop

/-! # Literal finite inner and global matching programmes

Every decision variable is binary. Partition maps encode the source's two
finite partitions; all price, channel, capacity, degree, noncrossing and gate
constraints are explicit. The inner score is an attained finite maximum.
`ParserDecomposition` and `ParserAssembly` prove its global maximum equals
the dynamic programme, with `ParserLinks` providing the combinatorial bridge.
-/

noncomputable section
namespace Thesis.Intraday.ParserPrograms
open scoped BigOperators
open ParserMatching

structure Problem (n m N M : ℕ) where
  orderBlock : Fin n → Fin N
  tradeBlock : Fin m → Fin M
  orderBlock_surjective : Function.Surjective orderBlock
  tradeBlock_surjective : Function.Surjective tradeBlock
  reductions : Finset (Fin n)
  additions : Finset (Fin n)
  disjoint_channels : Disjoint reductions additions
  price : Fin n → ℝ
  buy : Fin n → Bool
  capacity : Fin n → ℝ
  capacity_nonneg : ∀ i, 0 ≤ capacity i
  capacity_pos : ∀ i ∈ reductions, 0 < capacity i
  tradePrice : Fin m → ℝ
  tradeQuantity : Fin m → ℝ
  tradeQuantity_pos : ∀ j, 0 < tradeQuantity j
  orderTime : Fin N → ℝ
  tradeTime : Fin M → ℝ
  orderTime_strictMono : StrictMono orderTime
  tradeTime_strictMono : StrictMono tradeTime
  priceTolerance : ℝ
  priceTolerance_nonneg : 0 ≤ priceTolerance
  timeGate : ℝ
  timeGate_pos : 0 < timeGate

def bit (b : Bool) : ℕ := if b then 1 else 0

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp [bit]

theorem channel_constraints_bool (reductions additions : ℕ) :
    (∃ beta : Bool, reductions ≤ bit beta ∧ additions ≤ 1 - bit beta) ↔
      reductions + additions ≤ 1 := by
  constructor
  · rintro ⟨beta, hr, ha⟩
    have := bit_le_one beta
    omega
  · intro h
    by_cases hr : reductions = 0
    · refine ⟨false, ?_, ?_⟩ <;> simp [bit] <;> omega
    · refine ⟨true, ?_, ?_⟩ <;> simp [bit] <;> omega

structure Assignment (n m : ℕ) where
  x : Fin n → Fin m → Bool
  y : Fin n → Fin m → Bool
  beta : Fin m → Bool
  deriving Fintype

structure GlobalVariables (n m N M : ℕ) where
  assignment : Assignment n m
  z : Fin N → Fin M → Bool
  deriving Fintype

def channels {n m : ℕ} (a : Assignment n m) : Prop :=
  ∀ j, (∑ i, bit (a.x i j)) ≤ bit (a.beta j) ∧
    (∑ i, bit (a.y i j)) ≤ 1 - bit (a.beta j)

theorem exists_channels_iff {n m : ℕ} (x y : Fin n → Fin m → Bool) :
    (∃ beta, channels (⟨x, y, beta⟩ : Assignment n m)) ↔
      ∀ j, (∑ i, bit (x i j)) + (∑ i, bit (y i j)) ≤ 1 := by
  constructor
  · rintro ⟨beta, hb⟩ j
    exact (channel_constraints_bool _ _).1 ⟨beta j, hb j⟩
  · intro h
    have he (j : Fin m) := (channel_constraints_bool _ _).2 (h j)
    choose beta hb using he
    exact ⟨beta, hb⟩

def objective {n m N M : ℕ} (p : Problem n m N M) (a : Assignment n m) : ℝ :=
  (∑ i, ∑ j, (bit (a.x i j) : ℝ) * p.tradeQuantity j) +
    ∑ i, ∑ j, (bit (a.y i j) : ℝ) * p.tradeQuantity j

def commonFeasible {n m N M : ℕ} (p : Problem n m N M) (a : Assignment n m) : Prop :=
  (∀ i, i ∉ p.reductions → ∀ j, a.x i j = false) ∧
  (∀ i, i ∉ p.additions → ∀ j, a.y i j = false) ∧
  channels a ∧
  (∀ i ∈ p.reductions, ∑ j, (bit (a.x i j) : ℝ) * p.tradeQuantity j ≤ p.capacity i) ∧
  (∀ i j, p.buy i = true → p.price i + p.priceTolerance < p.tradePrice j → a.x i j = false) ∧
  (∀ i j, p.buy i = false → p.tradePrice j < p.price i - p.priceTolerance → a.x i j = false) ∧
  (∀ i j, p.priceTolerance < |p.tradePrice j - p.price i| → a.y i j = false)

def allowed {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) : Prop :=
  |p.orderTime k - p.tradeTime l| ≤ p.timeGate

def innerFeasible {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M)
    (a : Assignment n m) : Prop :=
  commonFeasible p a ∧
  (∀ i j, p.orderBlock i ≠ k ∨ p.tradeBlock j ≠ l → a.x i j = false) ∧
  (∀ i j, p.orderBlock i ≠ k ∨ p.tradeBlock j ≠ l → a.y i j = false)

def globalFeasible {n m N M : ℕ} (p : Problem n m N M)
    (v : GlobalVariables n m N M) : Prop :=
  commonFeasible p v.assignment ∧
  (∀ i j, bit (v.assignment.x i j) ≤ bit (v.z (p.orderBlock i) (p.tradeBlock j))) ∧
  (∀ i j, bit (v.assignment.y i j) ≤ bit (v.z (p.orderBlock i) (p.tradeBlock j))) ∧
  (∀ k l, bit (v.z k l) ≤
    (∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
      ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), bit (v.assignment.x i j)) +
    ∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
      ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), bit (v.assignment.y i j)) ∧
  (∀ l, ∑ k, bit (v.z k l) ≤ 1) ∧
  (∀ k, ∑ l, bit (v.z k l) ≤ 1) ∧
  (∀ k k' l l', k < k' → l' < l → bit (v.z k l) + bit (v.z k' l') ≤ 1) ∧
  (∀ k l, ¬allowed p k l → v.z k l = false)

def zeroAssignment (n m : ℕ) : Assignment n m := ⟨fun _ _ => false, fun _ _ => false,
  fun _ => false⟩

def zeroGlobal (n m N M : ℕ) : GlobalVariables n m N M :=
  ⟨zeroAssignment n m, fun _ _ => false⟩

theorem zero_commonFeasible {n m N M : ℕ} (p : Problem n m N M) :
    commonFeasible p (zeroAssignment n m) := by
  simp [commonFeasible, zeroAssignment, channels, bit, p.capacity_nonneg]

theorem zero_innerFeasible {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) :
    innerFeasible p k l (zeroAssignment n m) := by
  exact ⟨zero_commonFeasible p, by simp [zeroAssignment], by simp [zeroAssignment]⟩

theorem zero_globalFeasible {n m N M : ℕ} (p : Problem n m N M) :
    globalFeasible p (zeroGlobal n m N M) := by
  refine ⟨zero_commonFeasible p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [zeroGlobal, zeroAssignment, bit]

def innerCandidates {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) :
    Finset (Assignment n m) := by
  classical
  exact Finset.univ.filter (innerFeasible p k l)

theorem innerCandidates_nonempty {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) : (innerCandidates p k l).Nonempty := by
  classical
  exact ⟨zeroAssignment n m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, zero_innerFeasible p k l⟩⟩

def globalCandidates {n m N M : ℕ} (p : Problem n m N M) :
    Finset (GlobalVariables n m N M) := by
  classical
  exact Finset.univ.filter (globalFeasible p)

theorem globalCandidates_nonempty {n m N M : ℕ} (p : Problem n m N M) :
    (globalCandidates p).Nonempty := by
  classical
  exact ⟨zeroGlobal n m N M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, zero_globalFeasible p⟩⟩

def finiteMaximum {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) : ℝ :=
  (s.image f).max' (hs.image f)

theorem finiteMaximum_attained {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    ∃ a ∈ s, f a = finiteMaximum s hs f :=
  Finset.mem_image.mp (Finset.max'_mem (s.image f) (hs.image f))

theorem le_finiteMaximum {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    (a : α) (ha : a ∈ s) : f a ≤ finiteMaximum s hs f :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem f ha)

/-- Original label: `defn:parser-inner-outer-programs`.
The true finite optimum of every binary inner variable/constraint family.
Variables outside the selected blocks are set to zero, an exact extension
of the source's local indexing. -/
def innerMaximum {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) : ℝ :=
  finiteMaximum (innerCandidates p k l) (innerCandidates_nonempty p k l) (objective p)

def globalMaximum {n m N M : ℕ} (p : Problem n m N M) : ℝ :=
  finiteMaximum (globalCandidates p) (globalCandidates_nonempty p)
    (fun v => objective p v.assignment)

def matchScore {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) : WithBot ℝ := by
  classical
  exact if allowed p k l then (innerMaximum p k l : WithBot ℝ) else ⊥

theorem innerMaximum_isGreatest {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) :
    (∃ a, innerFeasible p k l a ∧ objective p a = innerMaximum p k l) ∧
    (∀ a, innerFeasible p k l a → objective p a ≤ innerMaximum p k l) := by
  classical
  constructor
  · obtain ⟨a, ha, he⟩ := finiteMaximum_attained (innerCandidates p k l)
      (innerCandidates_nonempty p k l) (objective p)
    exact ⟨a, (Finset.mem_filter.mp ha).2, he⟩
  · intro a ha
    exact le_finiteMaximum _ _ _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)

theorem globalMaximum_isGreatest {n m N M : ℕ} (p : Problem n m N M) :
    (∃ v, globalFeasible p v ∧ objective p v.assignment = globalMaximum p) ∧
    (∀ v, globalFeasible p v → objective p v.assignment ≤ globalMaximum p) := by
  classical
  constructor
  · obtain ⟨v, hv, he⟩ := finiteMaximum_attained (globalCandidates p)
      (globalCandidates_nonempty p) (fun v => objective p v.assignment)
    exact ⟨v, (Finset.mem_filter.mp hv).2, he⟩
  · intro v hv
    exact le_finiteMaximum (globalCandidates p) (globalCandidates_nonempty p)
      (fun v => objective p v.assignment) v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)

theorem objective_nonneg {n m N M : ℕ} (p : Problem n m N M) (a : Assignment n m) :
    0 ≤ objective p a := by
  apply add_nonneg
  all_goals
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (Nat.cast_nonneg _) (p.tradeQuantity_pos j).le

theorem innerMaximum_nonneg {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) : 0 ≤ innerMaximum p k l := by
  obtain ⟨a, _, he⟩ := (innerMaximum_isGreatest p k l).1
  rw [← he]
  exact objective_nonneg p a

def restrictAssignment {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M)
    (a : Assignment n m) : Assignment n m :=
  ⟨fun i j => if p.orderBlock i = k ∧ p.tradeBlock j = l then a.x i j else false,
    fun i j => if p.orderBlock i = k ∧ p.tradeBlock j = l then a.y i j else false,
    a.beta⟩

theorem bit_mask_le (P : Prop) [Decidable P] (b : Bool) :
    bit (if P then b else false) ≤ bit b := by
  by_cases h : P <;> simp [h, bit]

theorem restrictAssignment_commonFeasible {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) (a : Assignment n m) (ha : commonFeasible p a) :
    commonFeasible p (restrictAssignment p k l a) := by
  rcases ha with ⟨hr, had, hc, hcap, hbuy, hsell, hprice⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j
    simp [restrictAssignment, hr i hi j]
  · intro i hi j
    simp [restrictAssignment, had i hi j]
  · intro j
    constructor
    · exact (Finset.sum_le_sum (fun i _ => bit_mask_le _ (a.x i j))).trans (hc j).1
    · exact (Finset.sum_le_sum (fun i _ => bit_mask_le _ (a.y i j))).trans (hc j).2
  · intro i hi
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hcap i hi)
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (bit_mask_le _ (a.x i j)))
      (p.tradeQuantity_pos j).le
  · intro i j hb hp
    simp [restrictAssignment, hbuy i j hb hp]
  · intro i j hb hp
    simp [restrictAssignment, hsell i j hb hp]
  · intro i j hp
    simp [restrictAssignment, hprice i j hp]

theorem restrictAssignment_innerFeasible {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) (a : Assignment n m) (ha : commonFeasible p a) :
    innerFeasible p k l (restrictAssignment p k l a) := by
  refine ⟨restrictAssignment_commonFeasible p k l a ha, ?_, ?_⟩
  all_goals
    intro i j h
    rcases h with h | h <;> simp [restrictAssignment, h]

theorem restricted_objective_le_innerMaximum {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) (a : Assignment n m) (ha : commonFeasible p a) :
    objective p (restrictAssignment p k l a) ≤ innerMaximum p k l :=
  (innerMaximum_isGreatest p k l).2 _ (restrictAssignment_innerFeasible p k l a ha)

def blockObjective {n m N M : ℕ} (p : Problem n m N M) (a : Assignment n m)
    (k : Fin N) (l : Fin M) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
    ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l),
      (bit (a.x i j) : ℝ) * p.tradeQuantity j) +
  ∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
    ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l),
      (bit (a.y i j) : ℝ) * p.tradeQuantity j

theorem sum_by_blocks {n m N M : ℕ} (p : Problem n m N M) (f : Fin n → Fin m → ℝ) :
    (∑ k, ∑ l, ∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
      ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), f i j) = ∑ i, ∑ j, f i j := by
  calc
    _ = ∑ k, ∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k),
        ∑ l, ∑ j ∈ Finset.univ.filter (fun j => p.tradeBlock j = l), f i j := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i ∈ Finset.univ.filter (fun i => p.orderBlock i = k), ∑ j, f i j := by
      simp_rw [Finset.sum_fiberwise Finset.univ p.tradeBlock]
    _ = _ := Finset.sum_fiberwise Finset.univ p.orderBlock _

theorem objective_eq_sum_blockObjective {n m N M : ℕ} (p : Problem n m N M)
    (a : Assignment n m) : objective p a = ∑ k, ∑ l, blockObjective p a k l := by
  simp only [blockObjective, Finset.sum_add_distrib]
  rw [sum_by_blocks, sum_by_blocks]
  rfl

theorem cast_bit_mask (P : Prop) [Decidable P] (b : Bool) :
    (bit (if P then b else false) : ℝ) = if P then (bit b : ℝ) else 0 := by
  by_cases h : P <;> simp [h, bit]

theorem restricted_objective_eq_blockObjective {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) (a : Assignment n m) :
    objective p (restrictAssignment p k l a) = blockObjective p a k l := by
  simp only [objective, restrictAssignment, cast_bit_mask, ite_mul, zero_mul,
    blockObjective, Finset.sum_filter]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    by_cases hi : p.orderBlock i = k <;> simp [hi]

def natScore {n m N M : ℕ} (p : Problem n m N M) (k l : ℕ) : ℝ :=
  if h : k < N ∧ l < M then innerMaximum p ⟨k, h.1⟩ ⟨l, h.2⟩ else 0

def natGate {n m N M : ℕ} (p : Problem n m N M) (k l : ℕ) : Prop :=
  ∃ hk : k < N, ∃ hl : l < M, allowed p ⟨k, hk⟩ ⟨l, hl⟩

instance natGate_decidable {n m N M : ℕ} (p : Problem n m N M) :
    DecidableRel (natGate p) := fun _ _ => Classical.propDecidable _

theorem natGate_iff {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) :
    natGate p k.val l.val ↔ allowed p k l := by
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · exact fun h => ⟨k.isLt, l.isLt, h⟩

theorem natScore_eq {n m N M : ℕ} (p : Problem n m N M) (k : Fin N) (l : Fin M) :
    natScore p k.val l.val = innerMaximum p k l := by
  simp only [natScore, k.isLt, l.isLt, and_self, ↓reduceDIte]

/-- Original label: `defn:parser-inner-outer-programs`.
The actual terminal Bellman value, with the exact finite inner maxima and
source time gate rather than an unspecified oracle. -/
def terminalValue {n m N M : ℕ} (p : Problem n m N M) : ℝ :=
  value (natScore p) (natGate p) N M

/-- Exactness compares both actual finite programmes. The complete proof is
`ParserAssembly.twoLevelExact`. -/
def TwoLevelExact {n m N M : ℕ} (p : Problem n m N M) : Prop :=
  terminalValue p = globalMaximum p

def extendedValue (score : ℕ → ℕ → ℝ) (gate : ℕ → ℕ → Prop) [DecidableRel gate] :
    ℕ → ℕ → WithBot ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | n + 1, m + 1 =>
    max (max (extendedValue score gate n (m + 1)) (extendedValue score gate (n + 1) m))
      (extendedValue score gate n m + if gate n m then (score n m : WithBot ℝ) else ⊥)

theorem extendedValue_eq_coe (score : ℕ → ℕ → ℝ) (gate : ℕ → ℕ → Prop)
    [DecidableRel gate] (n m : ℕ) :
    extendedValue score gate n m = (value score gate n m : WithBot ℝ) := by
  induction n generalizing m with
  | zero => simp [extendedValue, value]
  | succ n ih =>
    induction m with
    | zero => simp [extendedValue, value]
    | succ m ihm =>
      by_cases hg : gate n m <;>
        simp [extendedValue, value, hg, ih, ihm, WithBot.coe_add]

theorem gated_score_eq_matchScore {n m N M : ℕ} (p : Problem n m N M)
    (k : Fin N) (l : Fin M) :
    (if natGate p k.val l.val then (natScore p k.val l.val : WithBot ℝ) else ⊥) =
      matchScore p k l := by
  classical
  simp only [natGate_iff, natScore_eq, matchScore]

theorem terminalValue_eq_extended {n m N M : ℕ} (p : Problem n m N M) :
    (terminalValue p : WithBot ℝ) = extendedValue (natScore p) (natGate p) N M :=
  (extendedValue_eq_coe _ _ _ _).symm

end Thesis.Intraday.ParserPrograms
