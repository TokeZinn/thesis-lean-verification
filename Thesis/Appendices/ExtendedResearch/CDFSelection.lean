import Thesis.Appendices.ExtendedResearch.CDFConstraint
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Right-continuous selection of the literal bounded monotone L² classes -/

noncomputable section
namespace Thesis.Foundations.Research.CDFConstraint

open Set MeasureTheory Filter Topology

/-- The source's CDFs supported on `[a,b]`, including possible endpoint atoms. -/
structure SupportedCDF (a b : ℝ) where
  cdf : StieltjesFunction ℝ
  below : ∀ x < a, cdf x = 0
  above : ∀ x, b ≤ x → cdf x = 1

instance {a b : ℝ} : CoeFun (SupportedCDF a b) (fun _ => ℝ → ℝ) := ⟨fun F => F.cdf⟩

theorem SupportedCDF.bounds {a b : ℝ} (F : SupportedCDF a b) (x : ℝ) :
    0 ≤ F x ∧ F x ≤ 1 := by
  constructor
  · by_cases hx : x < a
    · simp only [F.below x hx, le_refl]
    · have hl : min x (a - 1) < a := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hm := F.cdf.mono (min_le_left x (a - 1))
      rwa [F.below _ hl] at hm
  · have hm := F.cdf.mono (le_max_left x b)
    rwa [F.above _ (le_max_right _ _)] at hm

theorem SupportedCDF.memLp {a b : ℝ} (F : SupportedCDF a b) :
    MemLp F 2 (intervalMeasure a b) :=
  F.cdf.mono.monotoneOn (Icc a b) |>.memLp_isCompact isCompact_Icc

/-- Original label: `defn:cdf-constraint-selection`.
Restriction to the actual L² class, without choosing pointwise representatives. -/
def SupportedCDF.toL2 {a b : ℝ} (F : SupportedCDF a b) :
    ℝ →₂[intervalMeasure a b] ℝ := F.memLp.toLp F

theorem SupportedCDF.toL2_mem {a b : ℝ} (F : SupportedCDF a b) :
    F.toL2 ∈ constraint a b := by
  refine ⟨F, F.cdf.mono.monotoneOn _, fun x _ => F.bounds x, ?_⟩
  exact F.memLp.coeFn_toLp.symm

/-- Right-continuous monotone functions are determined by their Lebesgue class. -/
theorem Stieltjes_eq_of_ae_eq {F G : StieltjesFunction ℝ}
    (h : F =ᵐ[volume] G) : F = G := by
  have hd := (volume : Measure ℝ).dense_of_ae h
  have hle (F G : StieltjesFunction ℝ) (hd : Dense {x | F x = G x}) (x : ℝ) :
      F x ≤ G x := by
    have hlim : Tendsto G (𝓝[>] x) (𝓝 (G x)) :=
      (G.right_continuous x).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨z, hz, hxy⟩ := hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hy)
    exact (F.mono hxy.1.le).trans (hz ▸ G.mono hxy.2.le)
  ext x
  exact le_antisymm (hle F G hd x) (hle G F (by simpa only [eq_comm] using hd) x)

theorem SupportedCDF.toL2_injective {a b : ℝ} :
    Function.Injective (SupportedCDF.toL2 (a := a) (b := b)) := by
  intro F G h
  have he : F =ᵐ[intervalMeasure a b] G :=
    F.memLp.coeFn_toLp.symm.trans ((congrArg (fun f : ℝ →₂[intervalMeasure a b] ℝ =>
      (f : ℝ → ℝ)) h).eventuallyEq.trans G.memLp.coeFn_toLp)
  have hg : F.cdf =ᵐ[volume] G.cdf := by
    have he' := (ae_restrict_iff' measurableSet_Icc).mp he
    filter_upwards [he'] with x hx
    by_cases ha : x < a
    · exact (F.below x ha).trans (G.below x ha).symm
    · by_cases hb : b ≤ x
      · exact (F.above x hb).trans (G.above x hb).symm
      · exact hx ⟨le_of_not_gt ha, (lt_of_not_ge hb).le⟩
  cases F
  cases G
  congr 1
  exact Stieltjes_eq_of_ae_eq hg

def cutoff (a b : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < a then 0 else if x < b then g x else 1

theorem cutoff_monotone {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hm : Monotone g) (hb : ∀ x, 0 ≤ g x ∧ g x ≤ 1) : Monotone (cutoff a b g) := by
  intro x y hxy
  unfold cutoff
  split_ifs with hxa hxb hya hyb <;>
    first | linarith | exact (hb y).1 | exact hm hxy | exact (hb x).2

theorem cutoff_rightLim_below {a b x : ℝ} {g : ℝ → ℝ} (hx : x < a) :
    Function.rightLim (cutoff a b g) x = 0 := by
  apply rightLim_eq_of_tendsto (by exact NeBot.ne inferInstance)
  have he : cutoff a b g =ᶠ[𝓝[>] x] (fun _ => 0) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with y hy
    simp only [cutoff, show y < a from hy, if_true]
  exact tendsto_const_nhds.congr' he.symm

theorem cutoff_rightLim_above {a b x : ℝ} {g : ℝ → ℝ} (hab : a ≤ b) (hx : b ≤ x) :
    Function.rightLim (cutoff a b g) x = 1 := by
  apply rightLim_eq_of_tendsto (by exact NeBot.ne inferInstance)
  have he : cutoff a b g =ᶠ[𝓝[>] x] (fun _ => 1) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hby : b ≤ y := hx.trans hy.le
    simp [cutoff, not_lt.mpr (hab.trans hby), not_lt.mpr hby]
  exact tendsto_const_nhds.congr' he.symm

/-- Original label: `prop:cdf-constraint-properties`, clause (iii).
Every literal constraint class admits the supported right-continuous CDF
representative. The only altered values are at monotone discontinuities and
the endpoints, a Lebesgue-null set. -/
theorem supportedCDF_exists {a b : ℝ} (hab : a < b) (f : constraint a b) :
    ∃ F : SupportedCDF a b, F.toL2 = f.val := by
  letI : NoAtoms (intervalMeasure a b) := by dsimp only [intervalMeasure]; infer_instance
  obtain ⟨g, hmono, hb, hgf⟩ := f.property
  obtain ⟨hm, hbound, hext⟩ := monotoneExtension_properties hmono hb
  let k := cutoff a b (monotoneExtension g (Icc a b))
  have hkm : Monotone k := cutoff_monotone hab hm hbound
  let F : SupportedCDF a b :=
    ⟨hkm.stieltjesFunction, fun _ hx => cutoff_rightLim_below hx,
      fun _ hx => cutoff_rightLim_above hab.le hx⟩
  refine ⟨F, ?_⟩
  have hrc : F =ᵐ[intervalMeasure a b] k := by
    filter_upwards [hkm.countable_not_continuousAt.ae_notMem (intervalMeasure a b)] with x hx
    change Function.rightLim k x = k x
    exact (not_not.mp hx).continuousWithinAt.rightLim_eq
  have hkg : k =ᵐ[intervalMeasure a b] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (intervalMeasure a b).ae_ne b] with x hx hxb
    have hlt : x < b := lt_of_le_of_ne hx.2 hxb
    change cutoff a b (monotoneExtension g (Icc a b)) x = g x
    simp only [cutoff, not_lt.mpr hx.1, if_false, hlt, if_true, hext x hx]
  apply Lp.ext
  exact F.memLp.coeFn_toLp.trans (hrc.trans (hkg.trans hgf))

/-- Original label: `defn:cdf-constraint-selection`.
The source's selected CDF, constructed from the actual L² constraint class. -/
def selection {a b : ℝ} (hab : a < b) (f : constraint a b) : SupportedCDF a b :=
  (supportedCDF_exists hab f).choose

theorem selection_toL2 {a b : ℝ} (hab : a < b) (f : constraint a b) :
    (selection hab f).toL2 = f.val := (supportedCDF_exists hab f).choose_spec

/-- Original label: `prop:cdf-constraint-properties`, clause (iii). -/
theorem selection_inverse {a b : ℝ} (hab : a < b) (F : SupportedCDF a b) :
    selection hab ⟨F.toL2, F.toL2_mem⟩ = F :=
  SupportedCDF.toL2_injective (selection_toL2 hab _)

def cramerDistance {a b : ℝ} (F G : SupportedCDF a b) : ℝ :=
  Real.sqrt (∫ x, (F x - G x) ^ 2)

/-- Original label: `prop:cdf-constraint-properties`, clause (iii).
The Cramér distance is exactly the L² distance of the restricted classes. -/
theorem cramerDistance_eq_norm {a b : ℝ} (F G : SupportedCDF a b) :
    cramerDistance F G = ‖F.toL2 - G.toL2‖ := by
  have hnorm : ‖F.toL2 - G.toL2‖ ^ 2 = ∫ x in Icc a b, (F x - G x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub F.toL2 G.toL2, F.memLp.coeFn_toLp,
      G.memLp.coeFn_toLp] with x hx hFx hGx
    change F.toL2 x = F x at hFx
    change G.toL2 x = G x at hGx
    simp only [hx, Pi.sub_apply, hFx, hGx, real_inner_self_eq_norm_sq,
      Real.norm_eq_abs, sq_abs]
  have hint : (∫ x in Icc a b, (F x - G x) ^ 2) = ∫ x, (F x - G x) ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_cases hxa : x < a
    · simp [F.below x hxa, G.below x hxa]
    · have hbx : b ≤ x := le_of_not_gt (fun h => hx ⟨le_of_not_gt hxa, h.le⟩)
      simp [F.above x hbx, G.above x hbx]
  unfold cramerDistance
  rw [← hint, ← hnorm, Real.sqrt_sq (norm_nonneg _)]

/-- Original label: `prop:cdf-constraint-properties`, clause (iii). -/
theorem selection_isometry {a b : ℝ} (hab : a < b) (f g : constraint a b) :
    cramerDistance (selection hab f) (selection hab g) = dist f g := by
  rw [cramerDistance_eq_norm, selection_toL2, selection_toL2, Subtype.dist_eq, dist_eq_norm]

end Thesis.Foundations.Research.CDFConstraint
