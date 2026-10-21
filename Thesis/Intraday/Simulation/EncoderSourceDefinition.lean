import Thesis.Intraday.Simulation.AnalogueAttention

/-! # Encoder with the source's supplied normalisation operator

`defn:aa-encoder` names a map LN but does not specify an epsilon or affine
parameters. This definition leaves that map as an explicit input, uses it at
both occurrences of LN, and implements the displayed attention, feedforward,
pooling, harmonic clock and final output formulas. Numerical equivalence to a
trained implementation still requires its actual normalisation convention.
-/

noncomputable section
namespace Thesis.Intraday.EncoderSourceDefinition

open scoped BigOperators InnerProductSpace
open AnalogueAttention

def updatedWith (LN : Vector 64 → Vector 64) (e : Encoder)
    (z : Fin 41 → Vector 64) (i : Fin 41) : Vector 64 :=
  LN (z i + ∑ j, attentionWeights e z i j • applyMatrix e.value (z j))

def postFeedforwardWith (LN : Vector 64 → Vector 64) (e : Encoder)
    (z : Fin 41 → Vector 64) (i : Fin 41) : Vector 64 :=
  let v := updatedWith LN e z i
  LN (v + feedforward e.feedforward v)

/-- Original label: `defn:aa-encoder`. LN is the operator supplied by the
source; no unreported numerical epsilon or affine convention is selected. -/
def encodeWith (LN : Vector 64 → Vector 64) (e : Encoder)
    (features : Fin 41 → Vector 4) (minutes : ℝ) : Vector 32 :=
  let y := postFeedforwardWith LN e (embedded e features)
  let pooled := ∑ i, softmax (fun j => ⟪e.pooling, y j⟫_ℝ) i • y i
  applyMatrix e.output
    (WithLp.toLp 2 (Fin.append (WithLp.ofLp pooled) (WithLp.ofLp (clock minutes))))

/-- The explicit affine-normalisation implementation instantiates the source
formula whenever its two occurrences use the same supplied normalisation. -/
theorem encode_eq_source_when_norms_agree (e : Encoder)
    (h : e.layerNormFeedforward = e.layerNormAttention)
    (features : Fin 41 → Vector 4) (minutes : ℝ) :
    encode e features minutes = encodeWith (normalise e.layerNormAttention) e features minutes := by
  simp only [encode, encodeWith, postFeedforwardWith, postFeedforward, updatedWith, updated, h]

end Thesis.Intraday.EncoderSourceDefinition
