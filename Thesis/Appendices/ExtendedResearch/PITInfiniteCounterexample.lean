import Thesis.Appendices.ExtendedResearch.RandomizedPIT
import Mathlib.Probability.Independence.InfinitePi

/-! # A full infinite ideal-PIT counterexample to strong 1-dependence

The thesis supplies no proof of its negative dependence claim. This model
supplements that claim: a persistent fair regime selects either independent
uniform pairs or identical uniform pairs. Forecast information reveals the
regime and completed pairs. Each outcome is conditionally uniform and is
observed by origin plus two, but distant adjacent pairs remain dependent.
This is separate from the Fin-4 finite-count example in `PITCounterexample`.
-/

noncomputable section
namespace Thesis.Foundations.Research.PITInfiniteCounterexample

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open PITCalibration RandomizedCDF RandomizedPIT

def chosen (s : Bool) (z : ℝ × ℝ) : ℝ := if s then z.1 else z.2

theorem conditionalLaw_chosen {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → T) (Z : Ω → ℝ × ℝ)
    (hY : Measurable Y) (hZ : Measurable Z) (independent : IndepFun Y Z P)
    (law : P.map Z = uniformLaw.prod uniformLaw) (selector : T → Bool)
    (hselector : Measurable selector) :
    ConditionalLaw P ((inferInstance : MeasurableSpace T).comap Y)
      (fun ω => chosen (selector (Y ω)) (Z ω)) uniformLaw := by
  classical
  have hm : Measurable (fun p : T × (ℝ × ℝ) => chosen (selector p.1) p.2) := by
    apply Measurable.ite _ measurable_snd.fst measurable_snd.snd
    exact (hselector.comp measurable_fst) (measurableSet_singleton true)
  have hj : P.map (fun ω => (Y ω, Z ω)) =
      (P.map Y).prod (uniformLaw.prod uniformLaw) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mp independent,
      law]
  intro A B hA hB
  obtain ⟨A', hA', rfl⟩ := hA
  let S : Set (T × (ℝ × ℝ)) := {p | p.1 ∈ A' ∧ chosen (selector p.1) p.2 ∈ B}
  have hS : MeasurableSet S := (hA'.preimage measurable_fst).inter (hm hB)
  have hfiber (y : T) : (uniformLaw.prod uniformLaw) (Prod.mk y ⁻¹' S) =
      A'.indicator (fun _ => uniformLaw B) y := by
    by_cases hy : y ∈ A'
    · rw [Set.indicator_of_mem hy]
      cases hs : selector y with
      | false =>
        have he : Prod.mk y ⁻¹' S = univ ×ˢ B := by ext z; simp [S, chosen, hy, hs]
        rw [he, Measure.prod_prod]
        simp
      | true =>
        have he : Prod.mk y ⁻¹' S = B ×ˢ univ := by ext z; simp [S, chosen, hy, hs]
        rw [he, Measure.prod_prod]
        simp
    · have he : Prod.mk y ⁻¹' S = ∅ := by ext z; simp [S, hy]
      simp [he, Set.indicator_of_notMem hy]
  calc
    P (Y ⁻¹' A' ∩ (fun ω => chosen (selector (Y ω)) (Z ω)) ⁻¹' B) =
        (P.map (fun ω => (Y ω, Z ω))) S := (Measure.map_apply (hY.prodMk hZ) hS).symm
    _ = ((P.map Y).prod (uniformLaw.prod uniformLaw)) S := by rw [hj]
    _ = ∫⁻ y, A'.indicator (fun _ => uniformLaw B) y ∂P.map Y := by
      rw [Measure.prod_apply hS]
      exact lintegral_congr hfiber
    _ = P (Y ⁻¹' A') * uniformLaw B := by
      rw [lintegral_indicator_const hA', Measure.map_apply hY hA', mul_comm]

abbrev Ω := ℕ → ℝ

def P : Measure Ω := Measure.infinitePi (fun _ : ℕ => uniformLaw)

instance : IsProbabilityMeasure P := by unfold P; infer_instance

theorem coordinates_independent : iIndepFun (fun i (ω : Ω) => ω i) P :=
  iIndepFun_infinitePi (fun _ => measurable_id)

theorem coordinate_law (i : ℕ) : P.map (fun ω => ω i) = uniformLaw :=
  Measure.infinitePi_map_eval _ i

def past (n : ℕ) : Finset ℕ := Finset.range (4 * (n / 2) + 1)

def readPast (n : ℕ) (ω : Ω) : past n → ℝ := fun j => ω j

theorem measurable_readPast (n : ℕ) : Measurable (readPast n) :=
  measurable_pi_lambda _ (fun j => measurable_pi_apply (j : ℕ))

theorem past_mono {n m : ℕ} (hnm : n ≤ m) : past n ⊆ past m := by
  apply Finset.range_mono
  have : n / 2 ≤ m / 2 := Nat.div_le_div_right hnm
  omega

def information : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq n := MeasurableSpace.comap (readPast n) inferInstance
  mono' := by
    intro n m hnm
    have hm : @Measurable Ω (past n → ℝ)
        (MeasurableSpace.comap (readPast m) inferInstance) inferInstance (readPast n) := by
      letI : MeasurableSpace Ω := MeasurableSpace.comap (readPast m) inferInstance
      have hRm : Measurable (readPast m) := Measurable.of_comap_le le_rfl
      exact measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply (⟨j, past_mono hnm j.property⟩ : past m)).comp
          hRm)
    exact hm.comap_le
  le' n := (measurable_readPast n).comap_le

def a (n : ℕ) : ℕ := 4 * (n / 2) + 1
def b (n : ℕ) : ℕ := 4 * (n / 2) + 2
def v (n : ℕ) : ℕ := 4 * (n / 2) + 3 + n % 2

def X (n : ℕ) (ω : Ω) : ℝ :=
  if n % 2 = 0 ∨ ω 0 ≤ 1 / 2 then ω (a n) else ω (b n)

def V (n : ℕ) (ω : Ω) : ℝ := ω (v n)

theorem measurable_X (n : ℕ) : Measurable (X n) := by
  unfold X
  apply Measurable.ite _ (measurable_pi_apply (a n)) (measurable_pi_apply (b n))
  by_cases hn : n % 2 = 0
  · simp [hn]
  · simpa [hn] using measurableSet_le (measurable_pi_apply 0) measurable_const

theorem measurable_V (n : ℕ) : Measurable (V n) := measurable_pi_apply _

theorem measurable_info_eval (n j : ℕ) (hj : j ∈ past n) :
    Measurable[information n] (fun ω : Ω => ω j) := by
  letI : MeasurableSpace Ω := information n
  have hr : Measurable (readPast n) := Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (⟨j, hj⟩ : past n)).comp hr

theorem observed_X (n : ℕ) : Measurable[information (n + 2)] (X n) := by
  letI : MeasurableSpace Ω := information (n + 2)
  have h0 := measurable_info_eval (n + 2) 0 (by simp [past])
  have ha := measurable_info_eval (n + 2) (a n) (by simp only [past, a, Finset.mem_range]; omega)
  have hb := measurable_info_eval (n + 2) (b n) (by simp only [past, b, Finset.mem_range]; omega)
  unfold X
  apply Measurable.ite _ ha hb
  by_cases hn : n % 2 = 0
  · simp [hn]
  · simpa [hn] using measurableSet_le h0 measurable_const

theorem observed_V (n : ℕ) : Measurable[information (n + 2)] (V n) :=
  measurable_info_eval (n + 2) (v n) (by simp only [past, v, Finset.mem_range]; omega)

theorem pair_independent_past (n : ℕ) :
    IndepFun (readPast n) (fun ω : Ω => (ω (a n), ω (b n))) P := by
  classical
  let J : Finset ℕ := {a n, b n}
  have hd : Disjoint (past n) J := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [J, Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [past, Finset.mem_range] at hj
    rcases hk with rfl | rfl <;> dsimp [a, b] at hj <;> omega
  have hind := coordinates_independent.indepFun_finset (past n) J hd
    (fun j => measurable_pi_apply j)
  let g : (J → ℝ) → ℝ × ℝ := fun z =>
    (z ⟨a n, by simp [J]⟩, z ⟨b n, by simp [J]⟩)
  have hg : Measurable g := (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  exact hind.comp measurable_id hg

theorem pair_law (n : ℕ) :
    P.map (fun ω => (ω (a n), ω (b n))) = uniformLaw.prod uniformLaw := by
  have hind := coordinates_independent.indepFun (show a n ≠ b n by dsimp [a, b]; omega)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
    (measurable_pi_apply _).aemeasurable).mp hind, coordinate_law, coordinate_law]

def selector (n : ℕ) (z : past n → ℝ) : Bool :=
  if n % 2 = 0 ∨ z ⟨0, by simp [past]⟩ ≤ 1 / 2 then true else false

theorem measurable_selector (n : ℕ) : Measurable (selector n) := by
  unfold selector
  apply Measurable.ite _ measurable_const measurable_const
  by_cases hn : n % 2 = 0
  · simp [hn]
  · simpa [hn] using measurableSet_le (measurable_pi_apply _) measurable_const

theorem conditional_X (n : ℕ) : ConditionalLaw P (information n) (X n) uniformLaw := by
  have h := conditionalLaw_chosen P (readPast n) (fun ω => (ω (a n), ω (b n)))
    (measurable_readPast n) ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
    (pair_independent_past n) (pair_law n) (selector n) (measurable_selector n)
  convert h using 1
  funext ω
  simp [chosen, selector, readPast, X]

theorem fresh_V (n : ℕ) : IndepFun (fun ω => (readPast n ω, X n ω)) (V n) P := by
  classical
  let J : Finset ℕ := past n ∪ {a n, b n}
  have h0 : 0 ∈ J := by simp [J, past]
  have ha : a n ∈ J := by simp [J]
  have hb : b n ∈ J := by simp [J]
  have hv : v n ∉ J := by
    simp only [J, past, Finset.mem_union, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton, a, b, v]
    omega
  have hind := coordinates_independent.indepFun_finset J {v n}
    (Finset.disjoint_singleton_right.mpr hv) (fun j => measurable_pi_apply j)
  let f : (J → ℝ) → (past n → ℝ) × ℝ := fun z =>
    ((fun j => z ⟨j, Finset.mem_union_left _ j.property⟩),
      if n % 2 = 0 ∨ z ⟨0, h0⟩ ≤ 1 / 2 then z ⟨a n, ha⟩ else z ⟨b n, hb⟩)
  have hf : Measurable f := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    · apply Measurable.ite _ (measurable_pi_apply (⟨a n, ha⟩ : J))
        (measurable_pi_apply (⟨b n, hb⟩ : J))
      by_cases hn : n % 2 = 0
      · simp [hn]
      · simpa [hn] using measurableSet_le (measurable_pi_apply _) measurable_const
  have hg : Measurable (fun z : ({v n} : Finset ℕ) → ℝ => z ⟨v n, by simp⟩) :=
    measurable_pi_apply _
  exact hind.comp hf hg

theorem V_law (n : ℕ) : P.map (V n) = uniformLaw := coordinate_law _

theorem V_independent : iIndepFun V P := by
  apply coordinates_independent.precomp
  intro n m h
  dsimp [v] at h
  have hn := Nat.mod_lt n (by omega : 0 < 2)
  have hm := Nat.mod_lt m (by omega : 0 < 2)
  omega

abbrev coordinateSigma (S : Set ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ S, (inferInstance : MeasurableSpace ℝ).comap (fun ω : Ω => ω j)

theorem measurable_coordinate_sigma (S : Set ℕ) (j : ℕ) (hj : j ∈ S) :
    Measurable[coordinateSigma S] (fun ω : Ω => ω j) :=
  Measurable.of_comap_le (le_iSup_of_le j (le_iSup_of_le hj le_rfl))

/-- The entire iid auxiliary sequence is independent of the entire outcome
sequence, not merely fresh separately at each forecast origin. -/
theorem auxiliaries_independent_outcomes :
    IndepFun (fun ω n => V n ω) (fun ω n => X n ω) P := by
  let S := Set.range v
  have hσ : Indep (coordinateSigma S) (coordinateSigma Sᶜ) P :=
    indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le)
      coordinates_independent.iIndep disjoint_compl_right
  have hVm : @Measurable Ω (ℕ → ℝ) (coordinateSigma S) inferInstance
      (fun ω n => V n ω) := by
    letI : MeasurableSpace Ω := coordinateSigma S
    exact measurable_pi_lambda _ (fun n => measurable_coordinate_sigma S (v n) ⟨n, rfl⟩)
  have hXm : @Measurable Ω (ℕ → ℝ) (coordinateSigma Sᶜ) inferInstance
      (fun ω n => X n ω) := by
    letI : MeasurableSpace Ω := coordinateSigma Sᶜ
    apply measurable_pi_lambda
    intro n
    have hnot (j : ℕ) (hj : j = 0 ∨ j = a n ∨ j = b n) : j ∈ Sᶜ := by
      rintro ⟨m, hm⟩
      have hmod := Nat.mod_lt m (by omega : 0 < 2)
      dsimp [v, a, b] at hm hj
      omega
    unfold X
    apply Measurable.ite _
      (measurable_coordinate_sigma Sᶜ (a n) (hnot _ (Or.inr (Or.inl rfl))))
      (measurable_coordinate_sigma Sᶜ (b n) (hnot _ (Or.inr (Or.inr rfl))))
    by_cases hn : n % 2 = 0
    · simp [hn]
    · simpa [hn] using measurableSet_le (measurable_coordinate_sigma Sᶜ 0
        (hnot _ (Or.inl rfl))) measurable_const
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hσ hVm.comap_le) hXm.comap_le

def U (n : ℕ) (ω : Ω) : ℝ := transform uniformLaw (X n ω) (V n ω)

theorem transform_uniform {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (v : ℝ) :
    transform uniformLaw x v = x := by
  have hc := cdf_eq_real uniformLaw x
  rw [measureReal_def, uniformLaw_Iic x hx, ENNReal.toReal_ofReal hx.1] at hc
  have hl := congrArg ENNReal.toReal (RandomizedCDF.measure_Iio (μ := uniformLaw) x)
  rw [uniformLaw_Iio hx, ENNReal.toReal_ofReal hx.1,
    ENNReal.toReal_ofReal (leftCDF_nonneg _ _)] at hl
  simp [transform, hc, ← hl]

theorem U_eq_X_ae (n : ℕ) : U n =ᵐ[P] X n := by
  have hm : ∀ᵐ x ∂P.map (X n), x ∈ Icc (0 : ℝ) 1 := by
    rw [(conditional_X n).map_eq (measurable_X n)]
    exact ae_restrict_mem measurableSet_Icc
  filter_upwards [ae_of_ae_map (measurable_X n).aemeasurable hm] with ω hω
  exact transform_uniform hω _

theorem observed_U (n : ℕ) : Measurable[information (n + 2)] (U n) := by
  letI : MeasurableSpace Ω := information (n + 2)
  exact (measurable_transform uniformLaw).comp ((observed_X n).prodMk (observed_V n))

theorem forecast_disintegration (n : ℕ) :
    P.map (fun ω => (readPast n ω, X n ω)) =
      (P.map (readPast n)) ⊗ₘ Kernel.const (past n → ℝ) uniformLaw := by
  rw [Measure.compProd_const]
  apply Measure.ext_prod
  intro A B hA hB
  have hr : @Measurable Ω (past n → ℝ) (information n) inferInstance (readPast n) :=
    Measurable.of_comap_le le_rfl
  rw [Measure.map_apply ((measurable_readPast n).prodMk (measurable_X n)) (hA.prod hB),
    Measure.prod_prod, Measure.map_apply (measurable_readPast n) hA]
  exact conditional_X n (readPast n ⁻¹' A) B (hr hA) hB

theorem conditional_U (n : ℕ) : ConditionalLaw P (information n) (U n) uniformLaw := by
  exact conditionalLaw_randomizedCDF_of_kernel P (X n) (readPast n) (V n)
    (Kernel.const _ uniformLaw) (measurable_X n) (measurable_readPast n) (measurable_V n)
    (forecast_disintegration n) (fresh_V n) (V_law n)

theorem horizon_spaced_uniforms (residue : ℕ) :
    iIndepFun (fun k => U (residue + k * 2)) P ∧
      ∀ k, P.map (U (residue + k * 2)) = uniformLaw :=
  horizon_spaced_uniform P information U 2 (by decide) observed_U conditional_U residue

def box (J : Finset ℕ) (lower : ℕ → Bool) : Set Ω :=
  Set.pi (J : Set ℕ) (fun j => if lower j then Iic (1 / 2 : ℝ) else Ioi (1 / 2 : ℝ))

theorem measurable_box (J : Finset ℕ) (lower : ℕ → Bool) : MeasurableSet (box J lower) := by
  apply MeasurableSet.pi J.countable_toSet
  intro j _
  cases lower j <;> simp

theorem upper_half_measure : uniformLaw (Ioi (1 / 2 : ℝ)) = ENNReal.ofReal (1 / 2) := by
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
    uniformLaw_Iic (1 / 2) (by norm_num)]
  rw [measure_univ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num)]
  congr 1
  norm_num

theorem box_measure (J : Finset ℕ) (lower : ℕ → Bool) :
    P (box J lower) = ENNReal.ofReal (1 / 2 : ℝ) ^ J.card := by
  unfold P box
  rw [Measure.infinitePi_pi (fun _ : ℕ => uniformLaw) (fun j _ => by cases lower j <;> simp)]
  calc
    (∏ j ∈ J, uniformLaw (if lower j then Iic (1 / 2 : ℝ) else Ioi (1 / 2 : ℝ))) =
        ∏ _j ∈ J, ENNReal.ofReal (1 / 2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro j _
      cases lower j
      · exact upper_half_measure
      · exact uniformLaw_Iic (1 / 2) (by norm_num)
    _ = _ := by simp

def lowerExceptZero (j : ℕ) : Bool := decide (j ≠ 0)

theorem boxes_disjoint {J K : Finset ℕ} (hJ : 0 ∈ J) (hK : 0 ∈ K) :
    Disjoint (box J (fun _ => true)) (box K lowerExceptZero) := by
  apply Set.disjoint_left.mpr
  intro ω hω hω'
  have hlo : ω 0 ≤ (1 / 2 : ℝ) := by simpa [box] using hω 0 hJ
  have hhi : (1 / 2 : ℝ) < ω 0 := by simpa [box, lowerExceptZero] using hω' 0 hK
  exact (not_lt_of_ge hlo) hhi

def E : Set Ω := {ω | X 0 ω ≤ 1 / 2 ∧ X 1 ω ≤ 1 / 2}
def F : Set Ω := {ω | X 4 ω ≤ 1 / 2 ∧ X 5 ω ≤ 1 / 2}

theorem E_boxes : E = box {0, 1} (fun _ => true) ∪ box {0, 1, 2} lowerExceptZero := by
  ext ω
  by_cases hs : ω 0 ≤ (2 : ℝ)⁻¹
  · simp [E, X, a, b, hs, box, lowerExceptZero, not_lt.mpr hs]
  · simp [E, X, a, b, hs, box, lowerExceptZero, lt_of_not_ge hs]

theorem F_boxes : F = box {0, 9} (fun _ => true) ∪ box {0, 9, 10} lowerExceptZero := by
  ext ω
  by_cases hs : ω 0 ≤ (2 : ℝ)⁻¹
  · simp [F, X, a, b, hs, box, lowerExceptZero, not_lt.mpr hs]
  · simp [F, X, a, b, hs, box, lowerExceptZero, lt_of_not_ge hs]

theorem inter_boxes : E ∩ F =
    box {0, 1, 9} (fun _ => true) ∪ box {0, 1, 2, 9, 10} lowerExceptZero := by
  ext ω
  by_cases hs : ω 0 ≤ (2 : ℝ)⁻¹
  · simp [E, F, X, a, b, hs, box, lowerExceptZero, not_lt.mpr hs]
  · simp [E, F, X, a, b, hs, box, lowerExceptZero, lt_of_not_ge hs]
    tauto

theorem E_measure : P E = ENNReal.ofReal (3 / 8) := by
  rw [E_boxes, measure_union (boxes_disjoint (by simp) (by simp)) (measurable_box _ _),
    box_measure, box_measure]
  norm_num only [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, Finset.card_singleton]
  rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  norm_num

theorem F_measure : P F = ENNReal.ofReal (3 / 8) := by
  rw [F_boxes, measure_union (boxes_disjoint (by simp) (by simp)) (measurable_box _ _),
    box_measure, box_measure]
  norm_num only [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, Finset.card_singleton]
  rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  norm_num

theorem inter_measure : P (E ∩ F) = ENNReal.ofReal (5 / 32) := by
  rw [inter_boxes, measure_union (boxes_disjoint (by simp) (by simp)) (measurable_box _ _),
    box_measure, box_measure]
  norm_num only [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, Finset.card_singleton]
  rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  norm_num

theorem separated_outcome_blocks_depend : ¬ IndepSet E F P := by
  intro h
  have he := h.measure_inter_eq_mul
  rw [E_measure, F_measure, inter_measure] at he
  have he' := congrArg ENNReal.toReal he
  norm_num [ENNReal.toReal_mul] at he'

def EPIT : Set Ω := {ω | U 0 ω ≤ 1 / 2 ∧ U 1 ω ≤ 1 / 2}
def FPIT : Set Ω := {ω | U 4 ω ≤ 1 / 2 ∧ U 5 ω ≤ 1 / 2}

theorem EPIT_ae : EPIT =ᵐ[P] E := by
  filter_upwards [U_eq_X_ae 0, U_eq_X_ae 1] with ω h0 h1
  change (U 0 ω ≤ 1 / 2 ∧ U 1 ω ≤ 1 / 2) = (X 0 ω ≤ 1 / 2 ∧ X 1 ω ≤ 1 / 2)
  rw [h0, h1]

theorem FPIT_ae : FPIT =ᵐ[P] F := by
  filter_upwards [U_eq_X_ae 4, U_eq_X_ae 5] with ω h4 h5
  change (U 4 ω ≤ 1 / 2 ∧ U 5 ω ≤ 1 / 2) = (X 4 ω ≤ 1 / 2 ∧ X 5 ω ≤ 1 / 2)
  rw [h4, h5]

theorem EPIT_measure : P EPIT = ENNReal.ofReal (3 / 8) :=
  (measure_congr EPIT_ae).trans E_measure

theorem FPIT_measure : P FPIT = ENNReal.ofReal (3 / 8) :=
  (measure_congr FPIT_ae).trans F_measure

theorem PIT_inter_measure : P (EPIT ∩ FPIT) = ENNReal.ofReal (5 / 32) := by
  have he : (EPIT ∩ FPIT : Set Ω) =ᵐ[P] (E ∩ F : Set Ω) := by
    filter_upwards [EPIT_ae, FPIT_ae] with ω hE hF
    change (EPIT ω ∧ FPIT ω) = (E ω ∧ F ω)
    rw [hE, hF]
  exact (measure_congr he).trans inter_measure

theorem PIT_block_defect :
    (P (EPIT ∩ FPIT)).toReal - (P EPIT).toReal * (P FPIT).toReal = 1 / 64 := by
  rw [PIT_inter_measure, EPIT_measure, FPIT_measure]
  norm_num

/-- Blocks with origins `{0,1}` and `{4,5}` are dependent, despite a gap
larger than the two-step forecast horizon. -/
theorem separated_PIT_blocks_depend :
    ¬ IndepFun (fun ω => (U 0 ω, U 1 ω)) (fun ω => (U 4 ω, U 5 ω)) P := by
  intro h
  have hb : MeasurableSet (Iic (1 / 2 : ℝ) ×ˢ Iic (1 / 2 : ℝ)) :=
    measurableSet_Iic.prod measurableSet_Iic
  have he := h.measure_inter_preimage_eq_mul _ _ hb hb
  change P (EPIT ∩ FPIT) = P EPIT * P FPIT at he
  rw [PIT_inter_measure, EPIT_measure, FPIT_measure] at he
  have he' := congrArg ENNReal.toReal he
  norm_num [ENNReal.toReal_mul] at he'

/-- The complete infinite probability model simultaneously satisfies the
ideal conditional forecasts, iid independent auxiliary uniforms, two-step
observation, conditional PIT uniformity and residue independence, while
violating independence of the displayed separated blocks. -/
theorem full_counterexample :
    (∀ n, ConditionalLaw P (information n) (X n) uniformLaw ∧
      Measurable[information (n + 2)] (X n) ∧
      Measurable[information (n + 2)] (V n) ∧ P.map (V n) = uniformLaw) ∧
    iIndepFun V P ∧
    IndepFun (fun ω n => V n ω) (fun ω n => X n ω) P ∧
    (∀ n, ConditionalLaw P (information n) (U n) uniformLaw ∧
      Measurable[information (n + 2)] (U n)) ∧
    (∀ residue, iIndepFun (fun k => U (residue + k * 2)) P) ∧
    ¬ IndepFun (fun ω => (U 0 ω, U 1 ω)) (fun ω => (U 4 ω, U 5 ω)) P := by
  exact ⟨fun n => ⟨conditional_X n, observed_X n, observed_V n, V_law n⟩,
    V_independent, auxiliaries_independent_outcomes,
    fun n => ⟨conditional_U n, observed_U n⟩,
    fun residue => (horizon_spaced_uniforms residue).1, separated_PIT_blocks_depend⟩

end Thesis.Foundations.Research.PITInfiniteCounterexample
