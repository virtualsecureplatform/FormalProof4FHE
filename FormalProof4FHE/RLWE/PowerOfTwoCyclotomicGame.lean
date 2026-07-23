/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.PowerOfTwoCyclotomic
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Exact RLWE Game Transport to Power-of-Two Cyclotomic Quotients

`PowerOfTwoCyclotomic` identifies each executable degree-`2^k` negacyclic ring element with the
corresponding quotient by `Φ_(2^(k+1))`.  This module lifts that elementwise result to the complete
decisional RLWE experiment.  Public challenges, secrets, errors, outputs, and transcripts are
transported coefficientwise.  Both the real and uniform games, and hence distinguishing
advantages, are preserved exactly.

This is a representation theorem.  It does not supply a computational hardness theorem or change
the coefficient error law into a canonical-embedding Gaussian law.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.PowerOfTwoCyclotomic

/-- The exact order-`2^(k+1)` cyclotomic residue-ring carrier. -/
abbrev Carrier (q exponent : ℕ) :=
  CyclotomicQuotient (ZMod q) (2 ^ (exponent + 1))

/-- The carrier is finite because its executable degree-`2^k` coefficient presentation is finite. -/
noncomputable instance instCarrierFintype (q exponent : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] : Fintype (Carrier q exponent) :=
  Fintype.ofEquiv (Rq q (2 ^ exponent))
    (executableEquivCyclotomic q exponent)

noncomputable instance instCarrierDecidableEq (q exponent : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] : DecidableEq (Carrier q exponent) :=
  Classical.decEq _

/-- Uniform cyclotomic sampling is induced by the exact executable carrier equivalence. -/
noncomputable instance instCarrierSampleableType (q exponent : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] : SampleableType (Carrier q exponent) :=
  SampleableType.ofEquiv (executableEquivCyclotomic q exponent)

/-- A pointwise carrier equivalence for finite vectors. -/
noncomputable def vectorEquiv (q exponent length : ℕ) [Nontrivial (ZMod q)] :
    (Fin length → Rq q (2 ^ exponent)) ≃
      (Fin length → Carrier q exponent) where
  toFun vector index := executableToCyclotomic q exponent (vector index)
  invFun vector index := (executableEquivCyclotomic q exponent).symm (vector index)
  left_inv vector := by
    funext index
    exact (executableEquivCyclotomic q exponent).symm_apply_apply (vector index)
  right_inv vector := by
    funext index
    exact (executableEquivCyclotomic q exponent).apply_symm_apply (vector index)

/-- Pointwise transport of a public rank-one RLWE challenge matrix. -/
noncomputable def sampleEquiv (q exponent sampleCount : ℕ) [Nontrivial (ZMod q)] :
    RLWE.Sample q (2 ^ exponent) sampleCount ≃
      Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent) where
  toFun challenge row sample := executableToCyclotomic q exponent (challenge row sample)
  invFun challenge row sample :=
    (executableEquivCyclotomic q exponent).symm (challenge row sample)
  left_inv challenge := by
    funext row sample
    exact (executableEquivCyclotomic q exponent).symm_apply_apply (challenge row sample)
  right_inv challenge := by
    funext row sample
    exact (executableEquivCyclotomic q exponent).apply_symm_apply (challenge row sample)

/-- Pointwise transport of the shared rank-one secret. -/
noncomputable abbrev secretEquiv (q exponent : ℕ) [Nontrivial (ZMod q)] :=
  vectorEquiv q exponent 1

/-- Pointwise transport of RLWE output and error vectors. -/
noncomputable abbrev outputEquiv (q exponent sampleCount : ℕ) [Nontrivial (ZMod q)] :=
  vectorEquiv q exponent sampleCount

/-- Public transcript equivalence induced by the cyclotomic carrier equivalence. -/
noncomputable def transcriptEquiv (q exponent sampleCount : ℕ) [Nontrivial (ZMod q)] :
    (RLWE.Sample q (2 ^ exponent) sampleCount ×
        RLWE.Output q (2 ^ exponent) sampleCount) ≃
      (Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent) ×
        (Fin sampleCount → Carrier q exponent)) :=
  (sampleEquiv q exponent sampleCount).prodCongr
    (outputEquiv q exponent sampleCount)

/-- Mapping executable errors into the cyclotomic quotient. -/
noncomputable def errorSampler (q exponent : ℕ)
    (source : ProbComp (Rq q (2 ^ exponent))) : ProbComp (Carrier q exponent) :=
  executableToCyclotomic q exponent <$> source

/-- Standard matrix-form decisional RLWE over the exact cyclotomic quotient, with the source
secret and error laws pushed through the carrier equivalence. -/
noncomputable def problem (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent))) :
    LearningWithErrors.Problem
      (Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent))
      (Fin 1 → Carrier q exponent)
      (Fin sampleCount → Carrier q exponent) :=
  LWE.batchProblem 1 sampleCount
    (secretEquiv q exponent <$> sourceSecret)
    (errorSampler q exponent sourceError)

/-- Pointwise cyclotomic transport preserves zero output vectors. -/
theorem outputEquiv_zero (q exponent sampleCount : ℕ) [Nontrivial (ZMod q)] :
    outputEquiv q exponent sampleCount
        (0 : RLWE.Output q (2 ^ exponent) sampleCount) = 0 := by
  funext sample
  exact executableToCyclotomic_zero q exponent

/-- Pointwise cyclotomic transport preserves output addition. -/
theorem outputEquiv_add (q exponent sampleCount : ℕ) [Nontrivial (ZMod q)]
    (left right : RLWE.Output q (2 ^ exponent) sampleCount) :
    outputEquiv q exponent sampleCount (left + right) =
      outputEquiv q exponent sampleCount left +
        outputEquiv q exponent sampleCount right := by
  funext sample
  exact executableToCyclotomic_add q exponent (left sample) (right sample)

/-- Rank-one matrix multiplication commutes with the cyclotomic carrier transport. -/
theorem outputEquiv_vecMul (q exponent sampleCount : ℕ) [Nontrivial (ZMod q)]
    (secret : RLWE.Secret q (2 ^ exponent))
    (challenge : RLWE.Sample q (2 ^ exponent) sampleCount) :
    outputEquiv q exponent sampleCount (vecMul secret challenge) =
      vecMul (secretEquiv q exponent secret)
        (sampleEquiv q exponent sampleCount challenge) := by
  funext sample
  simp [Matrix.vecMul, dotProduct,
    secretEquiv, outputEquiv, vectorEquiv, sampleEquiv]
  exact executableToCyclotomic_commRing_mul q exponent
    (secret 0) (challenge 0 sample)

/-- Mapping a complete executable real transcript commutes with signal multiplication and error
addition. -/
theorem transcriptEquiv_real (q exponent sampleCount : ℕ) [Nontrivial (ZMod q)]
    (challenge : RLWE.Sample q (2 ^ exponent) sampleCount)
    (secret : RLWE.Secret q (2 ^ exponent))
    (error : RLWE.Output q (2 ^ exponent) sampleCount) :
    transcriptEquiv q exponent sampleCount
        (challenge, vecMul secret challenge + error) =
      (sampleEquiv q exponent sampleCount challenge,
        vecMul (secretEquiv q exponent secret)
            (sampleEquiv q exponent sampleCount challenge) +
          outputEquiv q exponent sampleCount error) := by
  apply Prod.ext
  · rfl
  · change outputEquiv q exponent sampleCount
        (vecMul secret challenge + error) = _
    rw [outputEquiv_add, outputEquiv_vecMul]

/-- Mapping independent executable errors pointwise gives independent mapped cyclotomic errors. -/
theorem outputEquiv_sampleIID_evalDist (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceError : ProbComp (Rq q (2 ^ exponent))) :
    evalDist (outputEquiv q exponent sampleCount <$>
      ProbComp.sampleIID sampleCount sourceError) =
    evalDist (ProbComp.sampleIID sampleCount
      (errorSampler q exponent sourceError)) := by
  apply evalDist_ext
  intro values
  rw [probOutput_map_equiv]
  simp only [ProbComp.sampleIID,
    FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn]
  apply Fintype.prod_congr
  intro sample
  change Pr[= (outputEquiv q exponent sampleCount).symm values sample | sourceError] =
    Pr[= values sample | executableToCyclotomic q exponent <$> sourceError]
  change Pr[= (outputEquiv q exponent sampleCount).symm values sample | sourceError] =
    Pr[= values sample | executableEquivCyclotomic q exponent <$> sourceError]
  rw [probOutput_map_equiv]
  rfl

/-- A uniform executable public challenge maps to a uniform cyclotomic public challenge. -/
theorem sampleEquiv_uniform_evalDist (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] :
    evalDist (sampleEquiv q exponent sampleCount <$>
      ($ᵗ RLWE.Sample q (2 ^ exponent) sampleCount)) =
    evalDist ($ᵗ Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent)) :=
  evalDist_map_bijective_uniform_cross
    (α := RLWE.Sample q (2 ^ exponent) sampleCount)
    (β := Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent))
    (sampleEquiv q exponent sampleCount)
    (sampleEquiv q exponent sampleCount).bijective

/-- A uniform executable right-hand side maps to a uniform cyclotomic right-hand side. -/
theorem outputEquiv_uniform_evalDist (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] :
    evalDist (outputEquiv q exponent sampleCount <$>
      ($ᵗ RLWE.Output q (2 ^ exponent) sampleCount)) =
    evalDist ($ᵗ (Fin sampleCount → Carrier q exponent)) :=
  evalDist_map_bijective_uniform_cross
    (α := RLWE.Output q (2 ^ exponent) sampleCount)
    (β := Fin sampleCount → Carrier q exponent)
    (outputEquiv q exponent sampleCount)
    (outputEquiv q exponent sampleCount).bijective

/-- Mapping the executable real RLWE transcript gives exactly the standard real cyclotomic RLWE
transcript distribution. -/
theorem real_evalDist (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent))) :
    evalDist (LearningWithErrors.distr
          (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) >>=
        fun transcript ↦ pure (transcriptEquiv q exponent sampleCount transcript)) =
      evalDist (LearningWithErrors.distr
        (problem q exponent sampleCount sourceSecret sourceError)) := by
  let mappedChallenge := sampleEquiv q exponent sampleCount <$>
    ($ᵗ RLWE.Sample q (2 ^ exponent) sampleCount)
  let targetChallenge :
      ProbComp (Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent)) :=
    $ᵗ Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent)
  let mappedSecret := secretEquiv q exponent <$> sourceSecret
  let mappedError := outputEquiv q exponent sampleCount <$>
    ProbComp.sampleIID sampleCount sourceError
  let targetError := ProbComp.sampleIID sampleCount
    (errorSampler q exponent sourceError)
  let finish :
      Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent) →
      (Fin 1 → Carrier q exponent) →
      (Fin sampleCount → Carrier q exponent) →
      ProbComp (Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent) ×
        (Fin sampleCount → Carrier q exponent)) := fun
      (challenge : Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent))
      (secret : Fin 1 → Carrier q exponent)
      (error : Fin sampleCount → Carrier q exponent) ↦
    pure (challenge, vecMul secret challenge + error)
  have hChallenge : evalDist mappedChallenge = evalDist targetChallenge := by
    exact sampleEquiv_uniform_evalDist q exponent sampleCount
  have hError : evalDist mappedError = evalDist targetError := by
    exact outputEquiv_sampleIID_evalDist q exponent sampleCount sourceError
  have left_eq :
      (LearningWithErrors.distr
          (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) >>=
        fun transcript ↦ pure (transcriptEquiv q exponent sampleCount transcript)) =
      (mappedChallenge >>= fun challenge ↦
        mappedSecret >>= fun secret ↦
        mappedError >>= fun error ↦
        finish challenge secret error) := by
    simp [LearningWithErrors.distr, RLWE.problem, LWE.batchProblem,
      mappedChallenge, mappedSecret, mappedError, finish,
      transcriptEquiv_real, bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.distr
          (problem q exponent sampleCount sourceSecret sourceError) =
      (targetChallenge >>= fun challenge ↦
        mappedSecret >>= fun secret ↦
        targetError >>= fun error ↦
        finish challenge secret error) := by
    simp [LearningWithErrors.distr, problem, LWE.batchProblem,
      targetChallenge, mappedSecret, targetError, errorSampler, finish,
      monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = evalDist (targetChallenge >>= fun challenge ↦
        mappedSecret >>= fun secret ↦
        mappedError >>= fun error ↦
        finish challenge secret error) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' targetChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' mappedSecret fun secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hError _

/-- Mapping the executable uniform RLWE transcript gives exactly the standard uniform
cyclotomic RLWE transcript distribution. -/
theorem uniform_evalDist (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent))) :
    evalDist (LearningWithErrors.uniformDistr
          (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) >>=
        fun transcript ↦ pure (transcriptEquiv q exponent sampleCount transcript)) =
      evalDist (LearningWithErrors.uniformDistr
        (problem q exponent sampleCount sourceSecret sourceError)) := by
  let mappedChallenge := sampleEquiv q exponent sampleCount <$>
    ($ᵗ RLWE.Sample q (2 ^ exponent) sampleCount)
  let targetChallenge :
      ProbComp (Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent)) :=
    $ᵗ Matrix (Fin 1) (Fin sampleCount) (Carrier q exponent)
  let mappedOutput := outputEquiv q exponent sampleCount <$>
    ($ᵗ RLWE.Output q (2 ^ exponent) sampleCount)
  let targetOutput : ProbComp (Fin sampleCount → Carrier q exponent) :=
    $ᵗ (Fin sampleCount → Carrier q exponent)
  have hChallenge : evalDist mappedChallenge = evalDist targetChallenge := by
    exact sampleEquiv_uniform_evalDist q exponent sampleCount
  have hOutput : evalDist mappedOutput = evalDist targetOutput := by
    exact outputEquiv_uniform_evalDist q exponent sampleCount
  have left_eq :
      (LearningWithErrors.uniformDistr
          (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) >>=
        fun transcript ↦ pure (transcriptEquiv q exponent sampleCount transcript)) =
      (mappedChallenge >>= fun challenge ↦
        mappedOutput >>= fun output ↦ pure (challenge, output)) := by
    simp [LearningWithErrors.uniformDistr, RLWE.problem, LWE.batchProblem,
      mappedChallenge, mappedOutput, transcriptEquiv, bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.uniformDistr
          (problem q exponent sampleCount sourceSecret sourceError) =
      (targetChallenge >>= fun challenge ↦
        targetOutput >>= fun output ↦ pure (challenge, output)) := by
    simp [LearningWithErrors.uniformDistr, problem, LWE.batchProblem,
      targetChallenge, targetOutput, monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = evalDist (targetChallenge >>= fun challenge ↦
        mappedOutput >>= fun output ↦ pure (challenge, output)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' targetChallenge fun challenge ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hOutput _

/-- Preprocess an executable transcript for a cyclotomic-quotient adversary. -/
noncomputable def reduction
    {q exponent sampleCount : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    {sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent))}
    {sourceError : ProbComp (Rq q (2 ^ exponent))}
    (adversary : LearningWithErrors.Adversary
      (problem q exponent sampleCount sourceSecret sourceError)) :
    LearningWithErrors.Adversary
      (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) :=
  fun transcript ↦ adversary (transcriptEquiv q exponent sampleCount transcript)

/-- Transport an executable-carrier adversary to the cyclotomic presentation. -/
noncomputable def ofExecutableAdversary
    {q exponent sampleCount : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    {sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent))}
    {sourceError : ProbComp (Rq q (2 ^ exponent))}
    (adversary : LearningWithErrors.Adversary
      (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)) :
    LearningWithErrors.Adversary
      (problem q exponent sampleCount sourceSecret sourceError) :=
  fun transcript ↦ adversary ((transcriptEquiv q exponent sampleCount).symm transcript)

@[simp]
theorem reduction_ofExecutableAdversary
    {q exponent sampleCount : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    {sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent))}
    {sourceError : ProbComp (Rq q (2 ^ exponent))}
    (adversary : LearningWithErrors.Adversary
      (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)) :
    reduction (ofExecutableAdversary adversary) = adversary := by
  funext transcript
  simp [reduction, ofExecutableAdversary]

@[simp]
theorem ofExecutableAdversary_reduction
    {q exponent sampleCount : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    {sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent))}
    {sourceError : ProbComp (Rq q (2 ^ exponent))}
    (adversary : LearningWithErrors.Adversary
      (problem q exponent sampleCount sourceSecret sourceError)) :
    ofExecutableAdversary (reduction adversary) = adversary := by
  funext transcript
  simp [reduction, ofExecutableAdversary]

/-- The executable and cyclotomic real games are distributionally identical under transcript
preprocessing. -/
theorem game0_evalDist_eq (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent)))
    (adversary : LearningWithErrors.Adversary
      (problem q exponent sampleCount sourceSecret sourceError)) :
    evalDist (LearningWithErrors.game0
        (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)
        (reduction adversary)) =
      evalDist (LearningWithErrors.game0
        (problem q exponent sampleCount sourceSecret sourceError) adversary) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [reduction]
  rw [show (LearningWithErrors.distr
        (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) >>=
      fun transcript ↦ adversary (transcriptEquiv q exponent sampleCount transcript)) =
    ((LearningWithErrors.distr
        (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) >>=
      fun transcript ↦ pure (transcriptEquiv q exponent sampleCount transcript)) >>=
        adversary) by simp [bind_assoc, monad_norm]]
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (real_evalDist q exponent sampleCount sourceSecret sourceError) adversary

/-- The executable and cyclotomic uniform games are distributionally identical under transcript
preprocessing. -/
theorem game1_evalDist_eq (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent)))
    (adversary : LearningWithErrors.Adversary
      (problem q exponent sampleCount sourceSecret sourceError)) :
    evalDist (LearningWithErrors.game1
        (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)
        (reduction adversary)) =
      evalDist (LearningWithErrors.game1
        (problem q exponent sampleCount sourceSecret sourceError) adversary) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [reduction]
  rw [show (LearningWithErrors.uniformDistr
        (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) >>=
      fun transcript ↦ adversary (transcriptEquiv q exponent sampleCount transcript)) =
    ((LearningWithErrors.uniformDistr
        (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) >>=
      fun transcript ↦ pure (transcriptEquiv q exponent sampleCount transcript)) >>=
        adversary) by simp [bind_assoc, monad_norm]]
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniform_evalDist q exponent sampleCount sourceSecret sourceError) adversary

/-- Every cyclotomic distinguisher has exactly the same advantage after preprocessing against the
executable RLWE presentation. -/
theorem reduction_advantage_eq (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent)))
    (adversary : LearningWithErrors.Adversary
      (problem q exponent sampleCount sourceSecret sourceError)) :
    LearningWithErrors.advantage
        (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)
        (reduction adversary) =
      LearningWithErrors.advantage
        (problem q exponent sampleCount sourceSecret sourceError) adversary := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq q exponent sampleCount sourceSecret sourceError adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq q exponent sampleCount sourceSecret sourceError adversary) true]

/-- Conversely, transporting an executable distinguisher to the cyclotomic presentation preserves
its advantage exactly. -/
theorem ofExecutableAdversary_advantage_eq (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent)))
    (adversary : LearningWithErrors.Adversary
      (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)) :
    LearningWithErrors.advantage
        (problem q exponent sampleCount sourceSecret sourceError)
        (ofExecutableAdversary adversary) =
      LearningWithErrors.advantage
        (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)
        adversary := by
  rw [← reduction_advantage_eq q exponent sampleCount sourceSecret sourceError]
  simp

/-- Any executable-presentation hardness bound transfers without loss to the exact cyclotomic
presentation, provided the chosen adversary classes are closed under transcript preprocessing. -/
theorem hardAgainst_of_executable (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent)))
    (sourceAllowed : LearningWithErrors.Adversary
      (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) → Prop)
    (targetAllowed : LearningWithErrors.Adversary
      (problem q exponent sampleCount sourceSecret sourceError) → Prop)
    (bound : ℝ)
    (hClosed : ∀ adversary, targetAllowed adversary →
      sourceAllowed (reduction adversary))
    (hExecutable : FormalProof4FHE.LWE.HardAgainst
      (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)
      sourceAllowed bound) :
    FormalProof4FHE.LWE.HardAgainst
      (problem q exponent sampleCount sourceSecret sourceError)
      targetAllowed bound := by
  intro adversary hadversary
  rw [← reduction_advantage_eq q exponent sampleCount sourceSecret sourceError]
  exact hExecutable (reduction adversary) (hClosed adversary hadversary)

/-- Conversely, a hardness bound for the exact cyclotomic presentation transfers without loss to
the executable presentation. -/
theorem executableHardAgainst_of_cyclotomic (q exponent sampleCount : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (sourceSecret : ProbComp (RLWE.Secret q (2 ^ exponent)))
    (sourceError : ProbComp (Rq q (2 ^ exponent)))
    (sourceAllowed : LearningWithErrors.Adversary
      (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError) → Prop)
    (targetAllowed : LearningWithErrors.Adversary
      (problem q exponent sampleCount sourceSecret sourceError) → Prop)
    (bound : ℝ)
    (hClosed : ∀ adversary, sourceAllowed adversary →
      targetAllowed (ofExecutableAdversary adversary))
    (hCyclotomic : FormalProof4FHE.LWE.HardAgainst
      (problem q exponent sampleCount sourceSecret sourceError)
      targetAllowed bound) :
    FormalProof4FHE.LWE.HardAgainst
      (RLWE.problem q (2 ^ exponent) sampleCount sourceSecret sourceError)
      sourceAllowed bound := by
  intro adversary hadversary
  rw [← ofExecutableAdversary_advantage_eq q exponent sampleCount
    sourceSecret sourceError]
  exact hCyclotomic (ofExecutableAdversary adversary)
    (hClosed adversary hadversary)

end FormalProof4FHE.RLWE.PowerOfTwoCyclotomic
