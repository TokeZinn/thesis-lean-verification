import Thesis.Intraday.Simulation.RetrievalWeights
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Current Analogue-Attention encoder and retrieval

Current labels: `defn:aa-encoder`, `defn:aa-retrieval-policy`, and
`prop:aa-attention-equivalence`. The two-layer GELU network is explicit.
Layer normalisation uses exposed positive epsilon and affine parameters;
the source does not fix their numerical convention or fitted values.
The retrieval is over the entire supplied finite candidate gate.
-/

noncomputable section
namespace Thesis.Intraday.AnalogueAttention
open scoped BigOperators InnerProductSpace

abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)

def softmax {ι : Type*} [Fintype ι] (score : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (score i) / ∑ j, Real.exp (score j)

theorem softmax_mass_pos {ι : Type*} [Fintype ι] [Nonempty ι] (score : ι → ℝ) :
    0 < ∑ j, Real.exp (score j) := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem softmax_pos {ι : Type*} [Fintype ι] [Nonempty ι] (score : ι → ℝ) (i : ι) :
    0 < softmax score i := div_pos (Real.exp_pos _) (softmax_mass_pos score)

theorem softmax_sum {ι : Type*} [Fintype ι] [Nonempty ι] (score : ι → ℝ) :
    ∑ i, softmax score i = 1 := by
  simp only [softmax, ← Finset.sum_div]
  exact div_self (ne_of_gt (softmax_mass_pos score))

theorem softmax_shift {ι : Type*} [Fintype ι] (score : ι → ℝ) (c : ℝ) (i : ι) :
    softmax (fun j => score j + c) i = softmax score i := by
  simp only [softmax, Real.exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (Real.exp_ne_zero c)

def retrievalScore {ι : Type*} {d : ℕ} (query : Vector d) (key : ι → Vector d)
    (bias : ι → ℝ) (i : ι) : ℝ := -‖query - key i‖ ^ 2 + bias i

/-- Original label: `defn:aa-retrieval-policy`.
Both the learned policy and the Gaussian-kernel introductory policy use
this same finite softmax. The latter sets both bias vectors to zero. -/
def policy {ι : Type*} [Fintype ι] {d : ℕ} (query : Vector d)
    (key : ι → Vector d) (bias : ι → ℝ) : ι → ℝ :=
  softmax (retrievalScore query key bias)

/-- Original label: `prop:aa-attention-equivalence`.
For arbitrary finite embedding dimension.
No equal-key-norm assumption is used; the key norm is an additive bias. -/
theorem attention_equivalence {ι : Type*} [Fintype ι] {d : ℕ}
    (query : Vector d) (key : ι → Vector d) (bias : ι → ℝ) (i : ι) :
    policy query key bias i = softmax (fun j =>
      ⟪query, key j⟫_ℝ / (1 / 2) - ‖key j‖ ^ 2 + bias j) i := by
  have hs : retrievalScore query key bias = fun j =>
      (⟪query, key j⟫_ℝ / (1 / 2) - ‖key j‖ ^ 2 + bias j) + (-‖query‖ ^ 2) := by
    funext j
    simp only [retrievalScore, norm_sub_sq_real]
    ring
  rw [policy, hs, softmax_shift]

theorem bias_shift_invariance {ι : Type*} [Fintype ι] {d : ℕ}
    (query : Vector d) (key : ι → Vector d) (bias : ι → ℝ) (c : ℝ) :
    policy query key (fun j => bias j + c) = policy query key bias := by
  funext i
  simpa only [policy, retrievalScore, add_assoc] using
    softmax_shift (retrievalScore query key bias) c i

def applyMatrix {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (x : Vector n) : Vector m :=
  WithLp.toLp 2 (a.mulVec (WithLp.ofLp x))

/-- Exact GELU, using the standard normal distribution function rather than a
tanh approximation. The source names GELU but specifies no approximation. -/
def gelu (x : ℝ) : ℝ :=
  x * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

@[simp] theorem gelu_zero : gelu 0 = 0 := by simp [gelu]

/-- The source's position-wise 64-to-128-to-64 network. Zero biases include
the purely linear-layer convention as a special case. -/
structure Feedforward where
  first : Matrix (Fin 128) (Fin 64) ℝ
  firstBias : Vector 128
  second : Matrix (Fin 64) (Fin 128) ℝ
  secondBias : Vector 64

def feedforward (f : Feedforward) (x : Vector 64) : Vector 64 :=
  let hidden := applyMatrix f.first x + f.firstBias
  applyMatrix f.second (WithLp.toLp 2 (fun i => gelu (hidden i))) + f.secondBias

def coordinateMean (x : Vector 64) : ℝ := (∑ i, x i) / 64

def coordinateVariance (x : Vector 64) : ℝ :=
  (∑ i, (x i - coordinateMean x) ^ 2) / 64

theorem coordinateVariance_nonneg (x : Vector 64) : 0 ≤ coordinateVariance x := by
  exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)

/-- Explicit standard affine layer-normalisation parameters. Epsilon is an
input, not an undocumented numerical choice. Its strict positivity makes
normalisation well-defined even at a constant input. -/
structure LayerNorm where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  scale : Vector 64
  offset : Vector 64

def normalise (p : LayerNorm) (x : Vector 64) : Vector 64 :=
  WithLp.toLp 2 (fun i =>
    p.scale i * ((x i - coordinateMean x) /
      Real.sqrt (coordinateVariance x + p.epsilon)) + p.offset i)

theorem normalise_denominator_pos (p : LayerNorm) (x : Vector 64) :
    0 < Real.sqrt (coordinateVariance x + p.epsilon) := by
  exact Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (coordinateVariance_nonneg x) p.epsilon_pos)

structure Encoder where
  embed : Matrix (Fin 64) (Fin 4) ℝ
  positional : Fin 41 → Vector 64
  key : Matrix (Fin 64) (Fin 64) ℝ
  query : Matrix (Fin 64) (Fin 64) ℝ
  value : Matrix (Fin 64) (Fin 64) ℝ
  layerNormAttention : LayerNorm
  feedforward : Feedforward
  layerNormFeedforward : LayerNorm
  pooling : Vector 64
  output : Matrix (Fin 32) (Fin 68) ℝ

def embedded (e : Encoder) (features : Fin 41 → Vector 4) (i : Fin 41) : Vector 64 :=
  applyMatrix e.embed (features i) + e.positional i

def attentionWeights (e : Encoder) (z : Fin 41 → Vector 64) (i : Fin 41) : Fin 41 → ℝ :=
  softmax fun j => ⟪applyMatrix e.key (z j), applyMatrix e.query (z i)⟫_ℝ / Real.sqrt 64

def updated (e : Encoder) (z : Fin 41 → Vector 64) (i : Fin 41) : Vector 64 :=
  normalise e.layerNormAttention
    (z i + ∑ j, attentionWeights e z i j • applyMatrix e.value (z j))

def postFeedforward (e : Encoder) (z : Fin 41 → Vector 64) (i : Fin 41) : Vector 64 :=
  let v := updated e z i
  normalise e.layerNormFeedforward (v + feedforward e.feedforward v)

def clock (minutes : ℝ) : Vector 4 := WithLp.toLp 2 ![
  Real.sin (2 * Real.pi * minutes / 1440), Real.cos (2 * Real.pi * minutes / 1440),
  Real.sin (4 * Real.pi * minutes / 1440), Real.cos (4 * Real.pi * minutes / 1440)]

/-- Original label: `defn:aa-encoder`.
The literal GELU network and affine layer normalisations have explicit
parameters. A fitted implementation must supply the source's unstated epsilon
and affine conventions before numerical correspondence can be certified. -/
def encode (e : Encoder) (features : Fin 41 → Vector 4) (minutes : ℝ) : Vector 32 :=
  let y := postFeedforward e (embedded e features)
  let pooled := ∑ i, softmax (fun j => ⟪e.pooling, y j⟫_ℝ) i • y i
  applyMatrix e.output
    (WithLp.toLp 2 (Fin.append (WithLp.ofLp pooled) (WithLp.ofLp (clock minutes))))

theorem attentionWeights_sum (e : Encoder) (z : Fin 41 → Vector 64) (i : Fin 41) :
    ∑ j, attentionWeights e z i j = 1 := softmax_sum _

/-- Original label: `defn:state-dependent-selection-probabilities`. -/
def gaussianPolicy {ι : Type*} [Fintype ι] {d : ℕ} (query : Vector d)
    (key : ι → Vector d) : ι → ℝ := policy query key (fun _ => 0)

end Thesis.Intraday.AnalogueAttention
