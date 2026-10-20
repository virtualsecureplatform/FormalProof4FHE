/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWQuadraticPreimage
import FormalProof4FHE.LWE.BlockBinaryReduction

/-!
# Derived small-secret source for the correlated-control candidate

Apply the SAME public shear to a complete block-binary source batch. Its
finite advantage is exactly block-binary LWE, and the existing weak-secret
reduction bounds it by ordinary uniform-secret LWE plus the explicit entropy
and noise-absorption losses. Binary-LWE hardness is not assumed independently.

The builder remains arbitrary: this does not prove its norm, failure rate,
runtime, native GSW materialization, or reusable bootstrap parameters. The
wide-error law required by the weak-secret reduction must also fit correctness.
-/

open OracleComp Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWQuadraticPreimageBinary

open GSWQuadraticPreimage FormalProof4FHE.BlockBinary

noncomputable section

variable {q b n m k : ℕ} [NeZero q]

noncomputable local instance : SampleableType (View (ZMod q) (n * b) m k) := inferInstance

def realView (builder : Builder (ZMod q) (n * b) m k)
    (linear : Matrix (Fin (n * b)) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (errorSampler : ProbComp (ZMod q)) : ProbComp (View (ZMod q) (n * b) m k) :=
  sourceEquiv builder linear offset <$>
    LearningWithErrors.distr (problem b n (m + k) errorSampler)

theorem uniform_source_evalDist (builder : Builder (ZMod q) (n * b) m k)
    (linear : Matrix (Fin (n * b)) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (errorSampler : ProbComp (ZMod q)) :
    𝒟[sourceEquiv builder linear offset <$>
      LearningWithErrors.uniformDistr (problem b n (m + k) errorSampler)] =
        𝒟[$ᵗ View (ZMod q) (n * b) m k] := by
  have hsource : 𝒟[LearningWithErrors.uniformDistr
      (problem b n (m + k) errorSampler)] =
      𝒟[$ᵗ BatchTranscript (ZMod q) (n * b) (m + k)] := by
    simpa only [LearningWithErrors.uniformDistr, problem] using
      (FiniteProduct.evalDist_independent_uniform_product
        (first := Matrix (Fin (n * b)) (Fin (m + k)) (ZMod q))
        (second := Fin (m + k) → ZMod q))
  exact (evalDist_map_eq_of_evalDist_eq hsource (sourceEquiv builder linear offset)).trans
    (evalDist_map_bijective_uniform_cross
      (BatchTranscript (ZMod q) (n * b) (m + k)) (sourceEquiv builder linear offset)
      (sourceEquiv builder linear offset).bijective)

theorem advantage_eq_blockBinary (builder : Builder (ZMod q) (n * b) m k)
    (linear : Matrix (Fin (n * b)) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (errorSampler : ProbComp (ZMod q))
    (adversary : View (ZMod q) (n * b) m k → ProbComp Bool) :
    (realView builder linear offset errorSampler >>= adversary).boolDistAdvantage
      (($ᵗ View (ZMod q) (n * b) m k) >>= adversary) =
      LearningWithErrors.advantage (problem b n (m + k) errorSampler)
        (reduction builder linear offset adversary) := by
  have hreal : realView builder linear offset errorSampler >>= adversary =
      LearningWithErrors.game0 (problem b n (m + k) errorSampler)
        (reduction builder linear offset adversary) := by
    simp [realView, reduction, LearningWithErrors.game0, monad_norm]
  have hideal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniform_source_evalDist builder linear offset errorSampler) adversary
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage, hreal]
  unfold ProbComp.boolDistAdvantage
  have hideal' : 𝒟[LearningWithErrors.game1 (problem b n (m + k) errorSampler)
      (reduction builder linear offset adversary)] =
      𝒟[($ᵗ View (ZMod q) (n * b) m k) >>= adversary] := by
    simpa [LearningWithErrors.game1, reduction, monad_norm] using hideal
  rw [evalDist_ext_iff.mp hideal' true]

/-- All three computational terms below are ORDINARY uniform-secret LWE.
The remaining costs are the weak-source noise gap and its entropy loss. -/
def ordinaryLoss (builder : Builder (ZMod q) (n * b) m k)
    (linear : Matrix (Fin (n * b)) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (d : ℕ) (narrow wide : ProbComp (ZMod q))
    (adversary : View (ZMod q) (n * b) m k → ProbComp Bool) : ℝ :=
  let red := reduction builder linear offset adversary
  (∑ coordinate : Fin (n * b),
    LearningWithErrors.advantage
      (batchProblem d (m + k) ($ᵗ (Fin d → ZMod q)) narrow)
      (rowHybridReduction (n * b) d (m + k) narrow coordinate
        (realMaskReduction b n d (m + k) narrow wide red))) +
    noiseAbsorptionGap b n d (m + k) narrow wide +
    Real.sqrt ((q : ℝ) ^ d / (b + 1 : ℝ) ^ n) / 2 +
    LearningWithErrors.advantage
      (batchProblem d (m + k) ($ᵗ (Fin d → ZMod q)) wide)
      (extractedLWReduction b n d (m + k) narrow wide red) +
    (∑ coordinate : Fin (n * b),
      LearningWithErrors.advantage
        (batchProblem d (m + k) ($ᵗ (Fin d → ZMod q)) narrow)
        (rowHybridReduction (n * b) d (m + k) narrow coordinate
          (uniformMaskReduction b n d (m + k) narrow wide red)))

theorem advantage_le_ordinaryLWE (builder : Builder (ZMod q) (n * b) m k)
    (linear : Matrix (Fin (n * b)) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (d : ℕ) (narrow wide : ProbComp (ZMod q))
    (adversary : View (ZMod q) (n * b) m k → ProbComp Bool) :
    (realView builder linear offset wide >>= adversary).boolDistAdvantage
      (($ᵗ View (ZMod q) (n * b) m k) >>= adversary) ≤
      ordinaryLoss builder linear offset d narrow wide adversary := by
  rw [advantage_eq_blockBinary]
  simpa only [ordinaryLoss, ZMod.card] using
    (advantage_le_ordinaryLWE_add_gaps b n d (m + k) narrow wide
      (reduction builder linear offset adversary))

end

end FormalProof4FHE.LWE.GSWQuadraticPreimageBinary
