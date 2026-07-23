/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareActualNormalForm
import FormalProof4FHE.TFHE.RingSquareTopWeightCoefficientAffine

/-!
# A Security Endpoint for the Highest Two-Adic `RGSW_S(-S)` Row

The highest two-adic row of the stripped rank-one `RGSW_S(-S)` ciphertext is an exact
coefficient-affine circular-RLWE problem.  This file upgrades the algebraic identification to
the security games themselves.

For modulus `q = 2^(k+1)`, ring degree `N = degree + 1`, and the one-level gadget
`g = 2^k`, coefficient transport identifies the complete real transcript of the named
coefficient-affine problem with the genuine native square/zero batch.  It also identifies the
uniform endpoints.  Consequently every native square distinguisher has exactly the advantage
of an explicit coefficient-affine adversary.

The zero-message comparison needed for KDM security is independently and exactly an ordinary
binary-secret rank-one RLWE problem with two rows.  Combining the two identities gives a
lossless small-noise theorem:

* coefficient-affine top-row hardness with bound `epsilonCircular`; and
* ordinary binary-secret RLWE hardness with bound `epsilonZero`

imply native one-level `RGSW_S(-S)` KDM security with bound
`epsilonCircular + epsilonZero`.

No error is enlarged, replaced, or statistically smudged.  The coefficient-affine premise is
the genuine remaining circular assumption; this module does not identify it with ordinary
RLWE.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightSecurity

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.Native
open FormalProof4FHE.TFHE.TGSW.RingSquare
open FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler
open FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightCoefficientAffine

noncomputable section

/-- Ring-carrier form of the highest two-adic coefficient-affine problem.  Its real
distribution is the native stripped square/zero batch before coefficient transport. -/
noncomputable def topRGSWRingProblem
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    LearningWithErrors.Problem
      (RLWE.ModuleSample (2 ^ (exponent + 1)) (degree + 1) 1
        (TGSW.rowCount 1 1))
      (RingBinarySecret 1 (degree + 1))
      (RLWE.ModuleOutput (2 ^ (exponent + 1)) (degree + 1)
        (TGSW.rowCount 1 1)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let ordinary := CoefficientStructuredLWE.ringProblem
    (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1) errorSampler
  exact
    { sampleChallenge := ordinary.sampleChallenge
      sampleSecret := ordinary.sampleSecret
      sampleError := ordinary.sampleError
      noiseless := fun ringSecret challenge ↦
        vecMul (embedRingSecret (2 ^ (exponent + 1)) ringSecret) challenge +
          Full.squareMessages
            (embedRingSecret (2 ^ (exponent + 1)) ringSecret)
            (topGadget exponent degree)
      sampleUniform := ordinary.sampleUniform }

/-- The ring and coefficient top-row problems have literally the ordinary samplers on every
field except their common square-message noiseless map. -/
theorem topRGSWRingProblem_same_samplers_as_ordinary
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    let top := topRGSWRingProblem exponent degree errorSampler
    let ordinary := CoefficientStructuredLWE.ringProblem
      (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1) errorSampler
    top.sampleChallenge = ordinary.sampleChallenge ∧
      top.sampleSecret = ordinary.sampleSecret ∧
      top.sampleError = ordinary.sampleError ∧
      top.sampleUniform = ordinary.sampleUniform := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  simp [topRGSWRingProblem]

/-- Coefficient transport maps the ring-carrier top-row noiseless output to the named
coefficient-affine noiseless output exactly. -/
theorem outputEquiv_topRGSWRingProblem_noiseless
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (challenge : RLWE.ModuleSample (2 ^ (exponent + 1)) (degree + 1) 1
      (TGSW.rowCount 1 1)) :
    CoefficientStructuredLWE.outputEquiv
        (2 ^ (exponent + 1)) (degree + 1) (TGSW.rowCount 1 1)
        ((topRGSWRingProblem exponent degree errorSampler).noiseless
          ringSecret challenge) =
      (topRGSWCoefficientProblem exponent degree errorSampler).noiseless
        ringSecret
        (CoefficientStructuredLWE.challengeEquiv
          (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) challenge) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [topRGSWCoefficientProblem_noiseless]
  unfold topRGSWRingProblem
  dsimp only
  have hEmbedded :
      embedRingSecret (2 ^ (exponent + 1)) ringSecret =
        (fun _ ↦ embedBinaryPolynomial (2 ^ (exponent + 1))
          (degree + 1) (ringSecret 0)) := by
    funext coordinate
    rw [Subsingleton.elim coordinate 0]
    rfl
  rw [hEmbedded]
  funext row
  apply congrArg
    (CoefficientStructuredLWE.coefficientEquiv
      (2 ^ (exponent + 1)) (degree + 1))
  simp [Matrix.vecMul, dotProduct,
    CoefficientStructuredLWE.challengeEquiv]

/-- Mapping a real ring-carrier top-row transcript coefficientwise gives exactly the real
coefficient-affine transcript. -/
theorem map_topRGSWRingDistr_eq_coefficientDistr
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    (LearningWithErrors.distr
        (topRGSWRingProblem exponent degree errorSampler) >>=
      fun transcript ↦ pure
        (CoefficientStructuredLWE.transcriptEquiv
          (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) transcript)) =
      LearningWithErrors.distr
        (topRGSWCoefficientProblem exponent degree errorSampler) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  simp only [LearningWithErrors.distr, topRGSWRingProblem,
    topRGSWCoefficientProblem, CoefficientStructuredLWE.ringProblem,
    CoefficientStructuredLWE.problem, FormalProof4FHE.LWE.embeddedBatchProblem,
    map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply bind_congr
  intro challenge
  apply bind_congr
  intro ringSecret
  apply bind_congr
  intro error
  apply congrArg pure
  apply Prod.ext
  · rfl
  · change
      CoefficientStructuredLWE.outputEquiv
          (2 ^ (exponent + 1)) (degree + 1) (TGSW.rowCount 1 1)
          ((topRGSWRingProblem exponent degree errorSampler).noiseless
              ringSecret challenge + error) =
        (topRGSWCoefficientProblem exponent degree errorSampler).noiseless
            ringSecret
            (CoefficientStructuredLWE.challengeEquiv
              (2 ^ (exponent + 1)) (degree + 1) 1
              (TGSW.rowCount 1 1) challenge) +
          CoefficientStructuredLWE.outputEquiv
            (2 ^ (exponent + 1)) (degree + 1) (TGSW.rowCount 1 1) error
    rw [CoefficientStructuredLWE.outputEquiv_add,
      outputEquiv_topRGSWRingProblem_noiseless]

/-- The same coefficient transport maps the uniform ring-carrier endpoint exactly to the named
coefficient-affine uniform endpoint. -/
theorem map_topRGSWRingUniformDistr_eq_coefficientUniformDistr
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    (LearningWithErrors.uniformDistr
        (topRGSWRingProblem exponent degree errorSampler) >>=
      fun transcript ↦ pure
        (CoefficientStructuredLWE.transcriptEquiv
          (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) transcript)) =
      LearningWithErrors.uniformDistr
        (topRGSWCoefficientProblem exponent degree errorSampler) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  simp [LearningWithErrors.uniformDistr, topRGSWRingProblem,
    topRGSWCoefficientProblem, CoefficientStructuredLWE.ringProblem,
    CoefficientStructuredLWE.problem, FormalProof4FHE.LWE.embeddedBatchProblem,
    CoefficientStructuredLWE.transcriptEquiv,
    bind_assoc, monad_norm]

/-- The ring-carrier problem's uniform branch is the canonical uniform rank-one two-row
transcript. -/
theorem topRGSWRingUniformDistr_eq_uniformSample
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    LearningWithErrors.uniformDistr
        (topRGSWRingProblem exponent degree errorSampler) =
      ($ᵗ (TGSW.Ciphertext
        (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1 1)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  unfold LearningWithErrors.uniformDistr topRGSWRingProblem
    CoefficientStructuredLWE.ringProblem FormalProof4FHE.LWE.embeddedBatchProblem
  have uniformProduct :
      ($ᵗ (TGSW.Ciphertext
          (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1 1) :
        ProbComp (TGSW.Ciphertext
          (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1 1)) =
      Prod.mk <$>
          ($ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 1))
            (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) <*>
        ($ᵗ (Fin (TGSW.rowCount 1 1) →
          RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The real ring-carrier problem is exactly the native fresh square/zero batch sampler, up to
swapping two independent draws. -/
theorem topRGSWRingDistr_evalDist_eq_nativeSquareBatchSampler
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    evalDist (LearningWithErrors.distr
        (topRGSWRingProblem exponent degree errorSampler)) =
      evalDist (Full.nativeSquareBatchSampler 1
        (sampleRingSecret 1 (degree + 1))
        (embedRingSecret (2 ^ (exponent + 1))) errorSampler
        (topGadget exponent degree)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let Challenges : ProbComp
      (Matrix (Fin 1) (Fin (TGSW.rowCount 1 1))
        (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :=
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 1))
      (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))
  let Errors : ProbComp (Fin (TGSW.rowCount 1 1) →
      RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) :=
    ProbComp.sampleIID (TGSW.rowCount 1 1) errorSampler
  let finish := fun
      (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 1))
        (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
      (ringSecret : RingBinarySecret 1 (degree + 1))
      (error : Fin (TGSW.rowCount 1 1) →
        RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) ↦
    (pure (TLWE.batchAssemble
      (embedRingSecret (2 ^ (exponent + 1)) ringSecret) challenge
      (Full.squareMessages
        (embedRingSecret (2 ^ (exponent + 1)) ringSecret)
        (topGadget exponent degree)) error) :
      ProbComp (TGSW.Ciphertext
        (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1 1))
  have hRing :
      LearningWithErrors.distr
          (topRGSWRingProblem exponent degree errorSampler) =
        (Challenges >>= fun challenge ↦
          sampleRingSecret 1 (degree + 1) >>= fun ringSecret ↦
            Errors >>= finish challenge ringSecret) := by
    simp [LearningWithErrors.distr, topRGSWRingProblem,
      CoefficientStructuredLWE.ringProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem, Challenges, Errors, finish,
      TLWE.batchAssemble, monad_norm]
  have hNative :
      Full.nativeSquareBatchSampler 1
          (sampleRingSecret 1 (degree + 1))
          (embedRingSecret (2 ^ (exponent + 1))) errorSampler
          (topGadget exponent degree) =
        (sampleRingSecret 1 (degree + 1) >>= fun ringSecret ↦
          Challenges >>= fun challenge ↦
            Errors >>= finish challenge ringSecret) := by
    simp [Full.nativeSquareBatchSampler, TLWE.batchEncrypt,
      Challenges, Errors, finish, monad_norm]
  rw [hRing, hNative]
  exact evalDist_bind_bind_swap Challenges
    (sampleRingSecret 1 (degree + 1))
    (fun challenge ringSecret ↦ Errors >>= finish challenge ringSecret)

/-- Pull a native square-batch distinguisher back through the coefficient equivalence. -/
def coefficientAdversary
    {exponent degree : ℕ}
    {errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))}
    (distinguisher : Full.Distinguisher
      (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1) :
    LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree errorSampler) :=
  fun transcript ↦ distinguisher
    ((CoefficientStructuredLWE.transcriptEquiv
      (2 ^ (exponent + 1)) (degree + 1) 1
      (TGSW.rowCount 1 1)).symm transcript)

/-- The coefficient adversary's real game is exactly the native fresh square/zero game. -/
theorem coefficientAdversary_game0_evalDist_eq_nativeSquareGame
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Full.Distinguisher
      (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1) :
    evalDist (LearningWithErrors.game0
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (coefficientAdversary distinguisher)) =
      evalDist (Full.nativeSquareGame 1
        (sampleRingSecret 1 (degree + 1))
        (embedRingSecret (2 ^ (exponent + 1))) errorSampler
        (topGadget exponent degree) distinguisher) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [LearningWithErrors.game0]
  unfold coefficientAdversary
  rw [← map_topRGSWRingDistr_eq_coefficientDistr]
  simp only [bind_assoc, pure_bind, Equiv.symm_apply_apply]
  rw [evalDist_bind,
    topRGSWRingDistr_evalDist_eq_nativeSquareBatchSampler,
    ← evalDist_bind]
  rfl

/-- The coefficient adversary's ideal game is exactly the canonical uniform native batch game. -/
theorem coefficientAdversary_game1_evalDist_eq_uniformGame
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Full.Distinguisher
      (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1) :
    evalDist (LearningWithErrors.game1
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (coefficientAdversary distinguisher)) =
      evalDist (Full.uniformGame distinguisher) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [LearningWithErrors.game1]
  unfold coefficientAdversary
  rw [← map_topRGSWRingUniformDistr_eq_coefficientUniformDistr]
  simp only [bind_assoc, pure_bind, Equiv.symm_apply_apply]
  rw [topRGSWRingUniformDistr_eq_uniformSample]
  rfl

/-- Coefficient transport preserves the complete top-row real-versus-uniform advantage with no
loss. -/
theorem nativeSquareAdvantage_eq_coefficientAdvantage
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Full.Distinguisher
      (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1) :
    Full.nativeSquareAdvantage 1
        (sampleRingSecret 1 (degree + 1))
        (embedRingSecret (2 ^ (exponent + 1))) errorSampler
        (topGadget exponent degree) distinguisher =
      LearningWithErrors.advantage
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (coefficientAdversary distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Full.nativeSquareAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (coefficientAdversary_game0_evalDist_eq_nativeSquareGame
        exponent degree errorSampler distinguisher) true,
    evalDist_ext_iff.mp
      (coefficientAdversary_game1_evalDist_eq_uniformGame
        exponent degree errorSampler distinguisher) true]

/-- The genuine stripped RGSW sampler and the direct native square sampler induce the same
top-row decision game. -/
theorem nativeRGSWSquareGame_evalDist_eq_nativeSquareGame
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    evalDist (Native.RingSquareRGSW.squareGame
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher) =
      evalDist (Full.nativeSquareGame 1
        (sampleRingSecret 1 (degree + 1))
        (embedRingSecret (2 ^ (exponent + 1))) errorSampler
        (topGadget exponent degree) distinguisher) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  have hSampler :=
    PreimageCompiler.ActualNormalForm.actualSquareBatchSampler_evalDist_eq_nativeSquareBatchSampler
      1 (sampleRingSecret 1 (degree + 1))
      (embedRingSecret (2 ^ (exponent + 1))) errorSampler
      (topGadget exponent degree)
  calc
    evalDist (Native.RingSquareRGSW.squareGame
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher) =
      evalDist (Full.actualSquareBatchSampler 1
          (sampleRingSecret 1 (degree + 1))
          (embedRingSecret (2 ^ (exponent + 1))) errorSampler
          (topGadget exponent degree) >>= distinguisher) := by
        simp [Native.RingSquareRGSW.squareGame,
          Full.actualSquareBatchSampler, encryptSquareView,
          Native.RingSquareRGSW.nativeStripLinearBlock,
          map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (Full.nativeSquareBatchSampler 1
          (sampleRingSecret 1 (degree + 1))
          (embedRingSecret (2 ^ (exponent + 1))) errorSampler
          (topGadget exponent degree) >>= distinguisher) := by
      rw [evalDist_bind, hSampler, ← evalDist_bind]
    _ = _ := rfl

/-- The two native presentations use the same canonical uniform two-row ciphertext game. -/
theorem nativeUniformGame_eq_fullUniformGame
    (exponent degree : ℕ)
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    Native.RingSquareRGSW.uniformGame
        (2 ^ (exponent + 1)) (degree + 1) 1 distinguisher =
      Full.uniformGame distinguisher := by
  rfl

/-- The exact native stripped top-row advantage is the named coefficient-affine advantage. -/
theorem nativeRGSWSquareAdvantage_eq_coefficientAdvantage
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    Native.RingSquareRGSW.squareAdvantage
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher =
      LearningWithErrors.advantage
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (coefficientAdversary distinguisher) := by
  rw [← nativeSquareAdvantage_eq_coefficientAdvantage]
  unfold Native.RingSquareRGSW.squareAdvantage
    Full.nativeSquareAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (nativeRGSWSquareGame_evalDist_eq_nativeSquareGame
      exponent degree errorSampler distinguisher) true,
    nativeUniformGame_eq_fullUniformGame]

/-- The genuine unstripped top-weight `RGSW_S(-S)` circular advantage is exactly the
coefficient-affine advantage after the public restoration map. -/
theorem circularLweAdvantage_eq_coefficientAdvantage
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    Native.RingSquareRGSW.circularLweAdvantage
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher =
      LearningWithErrors.advantage
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (coefficientAdversary
          (Native.RingSquareRGSW.restoreDistinguisher
            (topGadget exponent degree) distinguisher)) := by
  rw [Native.RingSquareRGSW.circularLweAdvantage_eq_squareAdvantage_restore,
    nativeRGSWSquareAdvantage_eq_coefficientAdvantage]

/-! ## The independent ordinary-RLWE zero branch -/

/-- Feed the native zero-message RGSW distinguisher directly to the format-identical
binary-secret rank-one RLWE problem. -/
def zeroRLWEAdversary
    {exponent degree : ℕ}
    {errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))}
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    LearningWithErrors.Adversary
      (CoefficientStructuredLWE.ringProblem
        (2 ^ (exponent + 1)) (degree + 1) 1
        (TGSW.rowCount 1 1) errorSampler) :=
  distinguisher

/-- Averaged fresh zero-message ring rows are exactly the real distribution of the ordinary
binary-secret rank-one RLWE problem, up to swapping independent challenge and secret draws. -/
theorem ordinaryRingDistr_evalDist_eq_zeroBatchSampler
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    evalDist (LearningWithErrors.distr
        (CoefficientStructuredLWE.ringProblem
          (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) errorSampler)) =
      evalDist (sampleRingSecret 1 (degree + 1) >>= fun ringSecret ↦
        TLWE.batchEncrypt 1 (TGSW.rowCount 1 1) errorSampler
          (embedRingSecret (2 ^ (exponent + 1)) ringSecret) 0) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let Challenges : ProbComp
      (Matrix (Fin 1) (Fin (TGSW.rowCount 1 1))
        (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :=
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 1))
      (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))
  let Errors : ProbComp (Fin (TGSW.rowCount 1 1) →
      RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) :=
    ProbComp.sampleIID (TGSW.rowCount 1 1) errorSampler
  let finish := fun
      (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 1))
        (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
      (ringSecret : RingBinarySecret 1 (degree + 1))
      (error : Fin (TGSW.rowCount 1 1) →
        RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) ↦
    (pure (TLWE.batchAssemble
      (embedRingSecret (2 ^ (exponent + 1)) ringSecret) challenge 0 error) :
      ProbComp (TGSW.Ciphertext
        (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1 1))
  have hRing :
      LearningWithErrors.distr
          (CoefficientStructuredLWE.ringProblem
            (2 ^ (exponent + 1)) (degree + 1) 1
            (TGSW.rowCount 1 1) errorSampler) =
        (Challenges >>= fun challenge ↦
          sampleRingSecret 1 (degree + 1) >>= fun ringSecret ↦
            Errors >>= finish challenge ringSecret) := by
    simp [LearningWithErrors.distr, CoefficientStructuredLWE.ringProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem, Challenges, Errors, finish,
      TLWE.batchAssemble, monad_norm]
  have hZero :
      (sampleRingSecret 1 (degree + 1) >>= fun ringSecret ↦
        TLWE.batchEncrypt 1 (TGSW.rowCount 1 1) errorSampler
          (embedRingSecret (2 ^ (exponent + 1)) ringSecret) 0) =
        (sampleRingSecret 1 (degree + 1) >>= fun ringSecret ↦
          Challenges >>= fun challenge ↦
            Errors >>= finish challenge ringSecret) := by
    simp [TLWE.batchEncrypt, Challenges, Errors, finish, monad_norm]
  rw [hRing, hZero]
  exact evalDist_bind_bind_swap Challenges
    (sampleRingSecret 1 (degree + 1))
    (fun challenge ringSecret ↦ Errors >>= finish challenge ringSecret)

/-- The ordinary binary-secret ring problem has the same canonical uniform two-row endpoint. -/
theorem ordinaryRingUniformDistr_eq_uniformSample
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    LearningWithErrors.uniformDistr
        (CoefficientStructuredLWE.ringProblem
          (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) errorSampler) =
      ($ᵗ (TGSW.Ciphertext
        (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1 1)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  unfold LearningWithErrors.uniformDistr CoefficientStructuredLWE.ringProblem
    FormalProof4FHE.LWE.embeddedBatchProblem
  have uniformProduct :
      ($ᵗ (TGSW.Ciphertext
          (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1 1) :
        ProbComp (TGSW.Ciphertext
          (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) 1 1)) =
      Prod.mk <$>
          ($ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 1))
            (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) <*>
        ($ᵗ (Fin (TGSW.rowCount 1 1) →
          RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The actual zero-message RGSW game is exactly the real ordinary binary-secret RLWE game. -/
theorem zeroGame_evalDist_eq_ordinaryRLWEGame0
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    evalDist (Native.RingSquareRGSW.zeroGame
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher) =
      evalDist (LearningWithErrors.game0
        (CoefficientStructuredLWE.ringProblem
          (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) errorSampler)
        (zeroRLWEAdversary distinguisher)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [LearningWithErrors.game0]
  unfold zeroRLWEAdversary
  rw [evalDist_bind, ordinaryRingDistr_evalDist_eq_zeroBatchSampler,
    ← evalDist_bind]
  simp [Native.RingSquareRGSW.zeroGame, TGSW.encryptZero, TGSW.encrypt,
    TGSW.addGadget_zero, bind_assoc, monad_norm]

/-- The actual uniform RGSW game is exactly the ideal ordinary binary-secret RLWE game. -/
theorem uniformGame_evalDist_eq_ordinaryRLWEGame1
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    evalDist (Native.RingSquareRGSW.uniformGame
        (2 ^ (exponent + 1)) (degree + 1) 1 distinguisher) =
      evalDist (LearningWithErrors.game1
        (CoefficientStructuredLWE.ringProblem
          (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) errorSampler)
        (zeroRLWEAdversary distinguisher)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [LearningWithErrors.game1]
  unfold zeroRLWEAdversary
  rw [ordinaryRingUniformDistr_eq_uniformSample]
  rfl

/-- The zero-message term in the standalone KDM hybrid is precisely ordinary binary-secret
rank-one RLWE with two samples. -/
theorem zeroLweAdvantage_eq_ordinaryRLWEAdvantage
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    Native.RingSquareRGSW.zeroLweAdvantage
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher =
      LearningWithErrors.advantage
        (CoefficientStructuredLWE.ringProblem
          (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) errorSampler)
        (zeroRLWEAdversary distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Native.RingSquareRGSW.zeroLweAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (zeroGame_evalDist_eq_ordinaryRLWEGame0
        exponent degree errorSampler distinguisher) true,
    evalDist_ext_iff.mp
      (uniformGame_evalDist_eq_ordinaryRLWEGame1
        exponent degree errorSampler distinguisher) true]

/-! ## Lossless native KDM security theorem -/

/-- Pointwise form of the top-row security reduction.  The genuine real-versus-zero
`RGSW_S(-S)` advantage is bounded by exactly one coefficient-affine advantage and one ordinary
binary-secret RLWE advantage. -/
theorem kdmAdvantage_le_coefficientAffine_add_ordinaryRLWE
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    Native.RingSquareRGSW.kdmAdvantage
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher ≤
      LearningWithErrors.advantage
          (topRGSWCoefficientProblem exponent degree errorSampler)
          (coefficientAdversary
            (Native.RingSquareRGSW.restoreDistinguisher
              (topGadget exponent degree) distinguisher)) +
        LearningWithErrors.advantage
          (CoefficientStructuredLWE.ringProblem
            (2 ^ (exponent + 1)) (degree + 1) 1
            (TGSW.rowCount 1 1) errorSampler)
          (zeroRLWEAdversary distinguisher) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  simpa only [circularLweAdvantage_eq_coefficientAdvantage,
    zeroLweAdvantage_eq_ordinaryRLWEAdvantage] using
    Native.RingSquareRGSW.kdmAdvantage_le_circularLwe_add_zeroLwe
      (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
      (topGadget exponent degree) distinguisher

/-- Concrete hardness of the exact top-row coefficient-affine problem. -/
def CoefficientAffineHardAgainst
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (allowed : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree errorSampler) → Prop)
    (bound : ℝ) : Prop :=
  FormalProof4FHE.LWE.HardAgainst
    (topRGSWCoefficientProblem exponent degree errorSampler) allowed bound

/-- Concrete ordinary binary-secret RLWE hardness at the exact two-row shape used by the
zero-message branch. -/
def BinarySecretRLWEHardAgainst
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (allowed : LearningWithErrors.Adversary
      (CoefficientStructuredLWE.ringProblem
        (2 ^ (exponent + 1)) (degree + 1) 1
        (TGSW.rowCount 1 1) errorSampler) → Prop)
    (bound : ℝ) : Prop :=
  FormalProof4FHE.LWE.HardAgainst
    (CoefficientStructuredLWE.ringProblem
      (2 ^ (exponent + 1)) (degree + 1) 1
      (TGSW.rowCount 1 1) errorSampler) allowed bound

/-- **Highest two-adic native KDM theorem.**  If the explicit coefficient-affine top-row
problem and ordinary two-row binary-secret RLWE are hard for the reductions induced by every
allowed native distinguisher, then the genuine one-level `RGSW_S(-S)` ciphertext is KDM-secure.

Both premises and the conclusion use the very same error sampler.  The reduction has no
statistical term and does not increase the error. -/
theorem kdmHardAgainst_of_coefficientAffine_and_binarySecretRLWE
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (nativeAllowed : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1 → Prop)
    (coefficientAllowed : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree errorSampler) → Prop)
    (ordinaryAllowed : LearningWithErrors.Adversary
      (CoefficientStructuredLWE.ringProblem
        (2 ^ (exponent + 1)) (degree + 1) 1
        (TGSW.rowCount 1 1) errorSampler) → Prop)
    (coefficientBound ordinaryBound : ℝ)
    (hCoefficientClosed : ∀ distinguisher, nativeAllowed distinguisher →
      coefficientAllowed
        (coefficientAdversary
          (Native.RingSquareRGSW.restoreDistinguisher
            (topGadget exponent degree) distinguisher)))
    (hOrdinaryClosed : ∀ distinguisher, nativeAllowed distinguisher →
      ordinaryAllowed (zeroRLWEAdversary distinguisher))
    (hCoefficient : CoefficientAffineHardAgainst exponent degree errorSampler
      coefficientAllowed coefficientBound)
    (hOrdinary : BinarySecretRLWEHardAgainst exponent degree errorSampler
      ordinaryAllowed ordinaryBound) :
    Native.RingSquareRGSW.KDMHardAgainst
      (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
      (topGadget exponent degree) nativeAllowed
      (coefficientBound + ordinaryBound) := by
  intro distinguisher hAllowed
  exact (kdmAdvantage_le_coefficientAffine_add_ordinaryRLWE
    exponent degree errorSampler distinguisher).trans
      (add_le_add
        (hCoefficient _ (hCoefficientClosed distinguisher hAllowed))
        (hOrdinary _ (hOrdinaryClosed distinguisher hAllowed)))

/-- Centered-binomial specialization of the lossless native KDM theorem.  The parameter `eta`
is not widened anywhere in the reduction. -/
theorem centeredBinomial_kdmHardAgainst_of_coefficientAffine_and_binarySecretRLWE
    (exponent degree eta : ℕ)
    (nativeAllowed : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1 → Prop)
    (coefficientAllowed : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree
        (RLWE.CenteredBinomial.sampler
          (2 ^ (exponent + 1)) (degree + 1) eta)) → Prop)
    (ordinaryAllowed : LearningWithErrors.Adversary
      (CoefficientStructuredLWE.ringProblem
        (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1)
        (RLWE.CenteredBinomial.sampler
          (2 ^ (exponent + 1)) (degree + 1) eta)) → Prop)
    (coefficientBound ordinaryBound : ℝ)
    (hCoefficientClosed : ∀ distinguisher, nativeAllowed distinguisher →
      coefficientAllowed
        (coefficientAdversary
          (Native.RingSquareRGSW.restoreDistinguisher
            (topGadget exponent degree) distinguisher)))
    (hOrdinaryClosed : ∀ distinguisher, nativeAllowed distinguisher →
      ordinaryAllowed (zeroRLWEAdversary distinguisher))
    (hCoefficient : CoefficientAffineHardAgainst exponent degree
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (degree + 1) eta)
      coefficientAllowed coefficientBound)
    (hOrdinary : BinarySecretRLWEHardAgainst exponent degree
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (degree + 1) eta)
      ordinaryAllowed ordinaryBound) :
    Native.RingSquareRGSW.KDMHardAgainst
      (2 ^ (exponent + 1)) (degree + 1) 1
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (degree + 1) eta)
      (topGadget exponent degree) nativeAllowed
      (coefficientBound + ordinaryBound) := by
  exact kdmHardAgainst_of_coefficientAffine_and_binarySecretRLWE
    exponent degree
    (RLWE.CenteredBinomial.sampler
      (2 ^ (exponent + 1)) (degree + 1) eta)
    nativeAllowed coefficientAllowed ordinaryAllowed coefficientBound ordinaryBound
    hCoefficientClosed hOrdinaryClosed hCoefficient hOrdinary

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightSecurity
