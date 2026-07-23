/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.SampleRestriction

/-!
# The BV Three-Component Quadratic KDM Telescope

This file formalizes the exact quadratic KDM argument underlying the three-component
Brakerski--Vaikuntanathan ciphertext.  Two ordinary rank-one RLWE samples sharing a secret `S`
can be publicly telescoped into

```
(a₁ S + e₁, a₂ S + e₂ - a₁, -a₂ + g).
```

Its phase under `(1,S,S²)` is `g S² + e₁ + e₂ S`.  The public telescope maps a uniform pair of
RLWE samples to a uniform three-component ciphertext exactly: retaining `a₁` as a fourth, unused
coordinate makes the map a bijection.  Consequently the quadratic KDM advantage is exactly the
advantage of a two-sample ordinary-RLWE distinguisher, with no hybrid or statistical loss.

This theorem deliberately keeps the third ciphertext component.  It therefore does not prove
security of a native two-component `RGSW_S(-S)` row.  Compressing the third component while
retaining narrow error is the separate circular-security problem isolated by the native RGSW
development.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.BVQuadraticKDM

/-- A degree-two BV ciphertext, represented by its coefficients under `(1,S,S²)`. -/
abbrev Ciphertext (R : Type) := Fin 3 → R

/-- Evaluate a three-component ciphertext at the secret. -/
def phase {R : Type} [Ring R] (secret : R) (ciphertext : Ciphertext R) : R :=
  ciphertext 0 + ciphertext 1 * secret + ciphertext 2 * secret * secret

/-- Assemble the telescoping presentation of a gadget-scaled encryption of `S²`. -/
def assemble {R : Type} [Ring R]
    (secret : R) (challenge : Matrix (Fin 1) (Fin 2) R)
    (error : Fin 2 → R) (gadget : R) : Ciphertext R :=
  ![challenge 0 0 * secret + error 0,
    challenge 0 1 * secret + error 1 - challenge 0 0,
    -challenge 0 1 + gadget]

/-- The usual direct quadratic-message presentation from the BV argument. -/
def assembleDirectSquare {R : Type} [Ring R]
    (secret firstMask secondMask firstError secondError gadget : R) : Ciphertext R :=
  ![firstMask * secret + firstError + gadget * secret * secret,
    secondMask * secret + secondError - firstMask,
    -secondMask]

/-- Translate the two masks so the direct square presentation becomes the telescope
presentation. -/
def shiftedChallenge {R : Type} [Ring R]
    (secret firstMask secondMask gadget : R) : Matrix (Fin 1) (Fin 2) R :=
  ![![firstMask + gadget * secret, secondMask + gadget]]

/-- Reparameterizing both uniform masks identifies the direct and telescoping presentations
pointwise. -/
theorem assemble_shiftedChallenge {R : Type} [CommRing R]
    (secret firstMask secondMask firstError secondError gadget : R) :
    assemble secret (shiftedChallenge secret firstMask secondMask gadget)
        ![firstError, secondError] gadget =
      assembleDirectSquare secret firstMask secondMask firstError secondError gadget := by
  funext coordinate
  fin_cases coordinate <;>
    simp [assemble, shiftedChallenge, assembleDirectSquare] <;> ring

/-- Apply the direct-to-telescope mask translation to an entire rank-one, two-column challenge. -/
def shiftMasks {R : Type} [Ring R] (secret gadget : R)
    (challenge : Matrix (Fin 1) (Fin 2) R) : Matrix (Fin 1) (Fin 2) R :=
  shiftedChallenge secret (challenge 0 0) (challenge 0 1) gadget

/-- Undo `shiftMasks`. -/
def unshiftMasks {R : Type} [Ring R] (secret gadget : R)
    (challenge : Matrix (Fin 1) (Fin 2) R) : Matrix (Fin 1) (Fin 2) R :=
  ![![challenge 0 0 - gadget * secret, challenge 0 1 - gadget]]

@[simp]
theorem unshiftMasks_shiftMasks {R : Type} [Ring R] (secret gadget : R)
    (challenge : Matrix (Fin 1) (Fin 2) R) :
    unshiftMasks secret gadget (shiftMasks secret gadget challenge) = challenge := by
  funext row column
  fin_cases row
  fin_cases column <;> simp [unshiftMasks, shiftMasks, shiftedChallenge]

@[simp]
theorem shiftMasks_unshiftMasks {R : Type} [Ring R] (secret gadget : R)
    (challenge : Matrix (Fin 1) (Fin 2) R) :
    shiftMasks secret gadget (unshiftMasks secret gadget challenge) = challenge := by
  funext row column
  fin_cases row
  fin_cases column <;> simp [unshiftMasks, shiftMasks, shiftedChallenge]

/-- For fixed secret and gadget, the two-mask translation is a permutation. -/
theorem shiftMasks_bijective {R : Type} [Ring R] (secret gadget : R) :
    Function.Bijective (shiftMasks secret gadget :
      Matrix (Fin 1) (Fin 2) R → Matrix (Fin 1) (Fin 2) R) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unshiftMasks secret gadget, unshiftMasks_shiftMasks secret gadget,
      shiftMasks_unshiftMasks secret gadget⟩

/-- `shiftMasks` turns the telescope assembly into the direct square assembly. -/
theorem assemble_shiftMasks {R : Type} [CommRing R]
    (secret : R) (challenge : Matrix (Fin 1) (Fin 2) R)
    (error : Fin 2 → R) (gadget : R) :
    assemble secret (shiftMasks secret gadget challenge) error gadget =
      assembleDirectSquare secret (challenge 0 0) (challenge 0 1)
        (error 0) (error 1) gadget := by
  exact assemble_shiftedChallenge secret (challenge 0 0) (challenge 0 1)
    (error 0) (error 1) gadget

/-- Exact decryption identity for the telescoping ciphertext.  No error widening occurs. -/
theorem phase_assemble {R : Type} [CommRing R]
    (secret : R) (challenge : Matrix (Fin 1) (Fin 2) R)
    (error : Fin 2 → R) (gadget : R) :
    phase secret (assemble secret challenge error gadget) =
      gadget * secret * secret + error 0 + error 1 * secret := by
  simp [phase, assemble]
  ring

/-- Publicly telescope an ordinary two-sample rank-one RLWE transcript. -/
def telescope {R : Type} [Ring R] (gadget : R)
    (transcript : LWE.BatchTranscript R 1 2) : Ciphertext R :=
  ![transcript.2 0,
    transcript.2 1 - transcript.1 0 0,
    -transcript.1 0 1 + gadget]

/-- The telescope maps a concrete real two-sample transcript to `assemble` pointwise. -/
theorem telescope_real {R : Type} [CommRing R]
    (secret : R) (challenge : Matrix (Fin 1) (Fin 2) R)
    (error : Fin 2 → R) (gadget : R) :
    telescope gadget (challenge, vecMul ![secret] challenge + error) =
      assemble secret challenge error gadget := by
  funext coordinate
  fin_cases coordinate <;>
    simp [telescope, assemble, Matrix.vecMul, dotProduct] <;> ring

/-- Vector form of `telescope_real`, convenient for an arbitrary rank-one secret embedding. -/
theorem telescope_real_vector {R : Type} [CommRing R]
    (secret : Fin 1 → R) (challenge : Matrix (Fin 1) (Fin 2) R)
    (error : Fin 2 → R) (gadget : R) :
    telescope gadget (challenge, vecMul secret challenge + error) =
      assemble (secret 0) challenge error gadget := by
  funext coordinate
  fin_cases coordinate <;>
    simp [telescope, assemble, Matrix.vecMul, dotProduct] <;> ring

/-- Attach the unused first mask to the public telescope.  The resulting four-coordinate map is
a permutation. -/
def telescopeWithFiber {R : Type} [Ring R] (gadget : R)
    (transcript : LWE.BatchTranscript R 1 2) : Ciphertext R × R :=
  (telescope gadget transcript, transcript.1 0 0)

/-- Inverse of `telescopeWithFiber`. -/
def untelescopeWithFiber {R : Type} [Ring R] (gadget : R)
    (output : Ciphertext R × R) : LWE.BatchTranscript R 1 2 :=
  (![![output.2, gadget - output.1 2]], ![output.1 0, output.1 1 + output.2])

@[simp]
theorem untelescopeWithFiber_telescopeWithFiber {R : Type} [Ring R]
    (gadget : R) (transcript : LWE.BatchTranscript R 1 2) :
    untelescopeWithFiber gadget (telescopeWithFiber gadget transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  apply Prod.ext
  · funext row column
    fin_cases row
    fin_cases column <;> simp [untelescopeWithFiber, telescopeWithFiber, telescope]
  · funext coordinate
    fin_cases coordinate <;>
      simp [untelescopeWithFiber, telescopeWithFiber, telescope]

@[simp]
theorem telescopeWithFiber_untelescopeWithFiber {R : Type} [Ring R]
    (gadget : R) (output : Ciphertext R × R) :
    telescopeWithFiber gadget (untelescopeWithFiber gadget output) = output := by
  rcases output with ⟨ciphertext, fiber⟩
  apply Prod.ext
  · funext coordinate
    fin_cases coordinate <;>
      simp [untelescopeWithFiber, telescopeWithFiber, telescope]
  · simp [untelescopeWithFiber, telescopeWithFiber]

/-- The telescope together with its one-coordinate fiber is bijective. -/
theorem telescopeWithFiber_bijective {R : Type} [Ring R] (gadget : R) :
    Function.Bijective (telescopeWithFiber gadget :
      LWE.BatchTranscript R 1 2 → Ciphertext R × R) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untelescopeWithFiber gadget,
      untelescopeWithFiber_telescopeWithFiber gadget,
      telescopeWithFiber_untelescopeWithFiber gadget⟩

/-- A uniform ordinary two-sample transcript telescopes to a uniform three-component
ciphertext. -/
theorem telescope_uniform_evalDist {R : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (gadget : R) :
    evalDist (telescope gadget <$>
        ($ᵗ (LWE.BatchTranscript R 1 2))) =
      evalDist ($ᵗ (Ciphertext R)) := by
  have hFiber :
      evalDist (telescopeWithFiber gadget <$>
          ($ᵗ (LWE.BatchTranscript R 1 2))) =
        evalDist ($ᵗ (Ciphertext R × R)) :=
    evalDist_map_bijective_uniform_cross
      (α := LWE.BatchTranscript R 1 2) (β := Ciphertext R × R)
      (telescopeWithFiber gadget) (telescopeWithFiber_bijective gadget)
  calc
    evalDist (telescope gadget <$> ($ᵗ (LWE.BatchTranscript R 1 2))) =
        evalDist (Prod.fst <$> (telescopeWithFiber gadget <$>
          ($ᵗ (LWE.BatchTranscript R 1 2)))) := by
      congr 1
      simp [Functor.map_map, telescopeWithFiber]
    _ = evalDist (Prod.fst <$> ($ᵗ (Ciphertext R × R))) :=
      evalDist_map_eq_of_evalDist_eq hFiber Prod.fst
    _ = evalDist ($ᵗ (Ciphertext R)) := evalDist_map_fst_uniformSample_prod

/-! ## Exact two-sample RLWE reduction -/

/-- The ordinary two-sample rank-one RLWE problem used by the telescope. -/
abbrev ordinaryProblem {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) :=
  LWE.embeddedBatchProblem 1 2 secretSampler embed errorSampler

/-- The direct quadratic-KDM ciphertext sampler. -/
def realSampler {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R) : ProbComp (Ciphertext R) := do
  let challenge ← $ᵗ Matrix (Fin 1) (Fin 2) R
  let secret ← secretSampler
  let error ← ProbComp.sampleIID 2 errorSampler
  pure (assemble (embed secret 0) challenge error gadget)

/-- The paper's direct presentation, with the `g S²` term visibly included in the first
component. -/
def directSquareSampler {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R) : ProbComp (Ciphertext R) := do
  let challenge ← $ᵗ Matrix (Fin 1) (Fin 2) R
  let secret ← secretSampler
  let error ← ProbComp.sampleIID 2 errorSampler
  pure (assembleDirectSquare (embed secret 0) (challenge 0 0) (challenge 0 1)
    (error 0) (error 1) gadget)

/-- The telescope and direct quadratic-message presentations are exactly equal in distribution.
The proof is only a secret-dependent permutation of the two uniform masks. -/
theorem realSampler_evalDist_eq_directSquareSampler {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R) :
    evalDist (realSampler secretSampler embed errorSampler gadget) =
      evalDist (directSquareSampler secretSampler embed errorSampler gadget) := by
  let challenges : ProbComp (Matrix (Fin 1) (Fin 2) R) :=
    $ᵗ Matrix (Fin 1) (Fin 2) R
  let errors : ProbComp (Fin 2 → R) := ProbComp.sampleIID 2 errorSampler
  let finish := fun (secret : Secret) (challenge : Matrix (Fin 1) (Fin 2) R)
      (error : Fin 2 → R) ↦
    (pure (assemble (embed secret 0) challenge error gadget) : ProbComp (Ciphertext R))
  have hShift : ∀ secret : Secret,
      evalDist (shiftMasks (embed secret 0) gadget <$> challenges) =
        evalDist challenges := by
    intro secret
    exact evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin 1) (Fin 2) R) (β := Matrix (Fin 1) (Fin 2) R)
      (shiftMasks (embed secret 0) gadget)
      (shiftMasks_bijective (embed secret 0) gadget)
  have hReal :
      evalDist (realSampler secretSampler embed errorSampler gadget) =
        evalDist (secretSampler >>= fun secret ↦
          challenges >>= fun challenge ↦ errors >>= finish secret challenge) := by
    rw [show evalDist (realSampler secretSampler embed errorSampler gadget) =
        evalDist (challenges >>= fun challenge ↦
          secretSampler >>= fun secret ↦ errors >>= finish secret challenge) by
      rfl]
    exact evalDist_bind_bind_swap challenges secretSampler
      (fun challenge secret ↦ errors >>= finish secret challenge)
  have hDirect :
      evalDist (directSquareSampler secretSampler embed errorSampler gadget) =
        evalDist (secretSampler >>= fun secret ↦
          challenges >>= fun challenge ↦
            errors >>= finish secret (shiftMasks (embed secret 0) gadget challenge)) := by
    rw [show evalDist (directSquareSampler secretSampler embed errorSampler gadget) =
        evalDist (challenges >>= fun challenge ↦
          secretSampler >>= fun secret ↦
            errors >>= finish secret (shiftMasks (embed secret 0) gadget challenge)) by
      apply congrArg evalDist
      simp [directSquareSampler, challenges, errors, finish, assemble_shiftMasks,
        monad_norm]]
    exact evalDist_bind_bind_swap challenges secretSampler
      (fun challenge secret ↦
        errors >>= finish secret (shiftMasks (embed secret 0) gadget challenge))
  rw [hReal, hDirect]
  refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
  rw [show
      (challenges >>= fun challenge ↦
        errors >>= finish secret (shiftMasks (embed secret 0) gadget challenge)) =
      ((shiftMasks (embed secret 0) gadget <$> challenges) >>=
        fun challenge ↦ errors >>= finish secret challenge) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, ← hShift secret, ← evalDist_bind]

/-- A Boolean distinguisher for the three-component quadratic ciphertext. -/
abbrev Distinguisher (R : Type) := Ciphertext R → ProbComp Bool

/-- Preprocess an ordinary two-sample transcript using the public telescope. -/
def reduction {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    {secretSampler : ProbComp Secret} {embed : Secret → Fin 1 → R}
    {errorSampler : ProbComp R} (gadget : R) (distinguisher : Distinguisher R) :
    LearningWithErrors.Adversary
      (ordinaryProblem secretSampler embed errorSampler) :=
  fun transcript ↦ distinguisher (telescope gadget transcript)

/-- The real quadratic-KDM game. -/
def realGame {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) : ProbComp Bool :=
  realSampler secretSampler embed errorSampler gadget >>= distinguisher

/-- The ideal game gives the distinguisher a uniform three-component ciphertext. -/
noncomputable def uniformGame {R : Type} [SampleableType R]
    (distinguisher : Distinguisher R) : ProbComp Bool := do
  let ciphertext ← $ᵗ (Ciphertext R)
  distinguisher ciphertext

/-- Real-versus-uniform advantage for the BV quadratic-KDM ciphertext. -/
noncomputable def advantage {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) : ℝ :=
  (realGame secretSampler embed errorSampler gadget distinguisher).boolDistAdvantage
    (uniformGame distinguisher)

/-- Telescoping an ordinary real RLWE transcript gives the direct quadratic sampler exactly. -/
theorem telescope_real_evalDist {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R) :
    evalDist (LearningWithErrors.distr
          (ordinaryProblem secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (telescope gadget transcript)) =
      evalDist (realSampler secretSampler embed errorSampler gadget) := by
  apply congrArg evalDist
  simp [LearningWithErrors.distr, ordinaryProblem, LWE.embeddedBatchProblem,
    realSampler, telescope_real_vector, monad_norm]

/-- The uniform branch of the ordinary problem is the canonical uniform transcript sampler. -/
theorem ordinary_uniformDistr_eq_uniformSample {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (ordinaryProblem secretSampler embed errorSampler) =
      ($ᵗ (LWE.BatchTranscript R 1 2)) := by
  unfold LearningWithErrors.uniformDistr ordinaryProblem LWE.embeddedBatchProblem
  have uniformProduct :
      ($ᵗ (LWE.BatchTranscript R 1 2) : ProbComp (LWE.BatchTranscript R 1 2)) =
      Prod.mk <$> ($ᵗ Matrix (Fin 1) (Fin 2) R) <*> ($ᵗ (Fin 2 → R)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The real quadratic game is exactly the real game of the two-sample ordinary-RLWE
reduction. -/
theorem realGame_evalDist_eq_reduction_game0 {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) :
    evalDist (realGame secretSampler embed errorSampler gadget distinguisher) =
      evalDist (LearningWithErrors.game0
        (ordinaryProblem secretSampler embed errorSampler)
        (reduction gadget distinguisher)) := by
  rw [LearningWithErrors.game0]
  simp only [realGame, reduction]
  rw [show
      (LearningWithErrors.distr
          (ordinaryProblem secretSampler embed errorSampler) >>=
        fun transcript ↦ distinguisher (telescope gadget transcript)) =
      ((LearningWithErrors.distr
          (ordinaryProblem secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (telescope gadget transcript)) >>= distinguisher) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, ← telescope_real_evalDist secretSampler embed errorSampler gadget,
    ← evalDist_bind]

/-- The uniform ordinary-RLWE reduction game is exactly the canonical uniform-ciphertext
game. -/
theorem reduction_game1_evalDist_eq_uniformGame {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) :
    evalDist (LearningWithErrors.game1
        (ordinaryProblem secretSampler embed errorSampler)
        (reduction gadget distinguisher)) =
      evalDist (uniformGame distinguisher) := by
  rw [LearningWithErrors.game1,
    ordinary_uniformDistr_eq_uniformSample secretSampler embed errorSampler]
  simp only [reduction, uniformGame]
  rw [show
      (($ᵗ (LWE.BatchTranscript R 1 2)) >>= fun transcript ↦
        distinguisher (telescope gadget transcript)) =
      ((telescope gadget <$> ($ᵗ (LWE.BatchTranscript R 1 2))) >>= distinguisher) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, telescope_uniform_evalDist gadget, ← evalDist_bind]

/-- **Lossless quadratic KDM theorem.**  The BV three-component encryption of `g S²` has
exactly the advantage of one two-sample ordinary rank-one RLWE distinguisher. -/
theorem advantage_eq_twoSampleRLWE {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) :
    advantage secretSampler embed errorSampler gadget distinguisher =
      LearningWithErrors.advantage
        (ordinaryProblem secretSampler embed errorSampler)
        (reduction gadget distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold advantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (realGame_evalDist_eq_reduction_game0 secretSampler embed errorSampler gadget
        distinguisher) true,
    evalDist_ext_iff.mp
      (reduction_game1_evalDist_eq_uniformGame secretSampler embed errorSampler gadget
        distinguisher) true]

/-- Real game written in the direct BV quadratic-message presentation. -/
def directRealGame {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) : ProbComp Bool :=
  directSquareSampler secretSampler embed errorSampler gadget >>= distinguisher

/-- The direct and telescoping real games have identical output distributions. -/
theorem directRealGame_evalDist_eq_realGame {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) :
    evalDist (directRealGame secretSampler embed errorSampler gadget distinguisher) =
      evalDist (realGame secretSampler embed errorSampler gadget distinguisher) := by
  unfold directRealGame realGame
  simp only [evalDist_bind]
  rw [← realSampler_evalDist_eq_directSquareSampler secretSampler embed errorSampler gadget]

/-- The direct BV presentation has the same lossless ordinary-RLWE reduction. -/
theorem directAdvantage_eq_twoSampleRLWE {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) :
    (directRealGame secretSampler embed errorSampler gadget distinguisher).boolDistAdvantage
        (uniformGame distinguisher) =
      LearningWithErrors.advantage
        (ordinaryProblem secretSampler embed errorSampler)
        (reduction gadget distinguisher) := by
  rw [← advantage_eq_twoSampleRLWE secretSampler embed errorSampler gadget distinguisher]
  unfold advantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (directRealGame_evalDist_eq_realGame secretSampler embed errorSampler gadget
      distinguisher) true]

/-! ## A shared-secret batch over all gadget levels -/

namespace Batch

/-- One three-component quadratic ciphertext per gadget level. -/
abbrev Ciphertexts (R : Type) (levels : ℕ) := Fin levels → Ciphertext R

/-- First ordinary-RLWE sample associated with a gadget level. -/
def firstIndex {levels : ℕ} (level : Fin levels) : Fin (levels + levels) :=
  Fin.castAdd levels level

/-- Second ordinary-RLWE sample associated with a gadget level. -/
def secondIndex {levels : ℕ} (level : Fin levels) : Fin (levels + levels) :=
  Fin.natAdd levels level

/-- Extract the two public masks associated with one gadget level. -/
def levelChallenge {R : Type} {levels : ℕ}
    (challenge : Matrix (Fin 1) (Fin (levels + levels)) R) (level : Fin levels) :
    Matrix (Fin 1) (Fin 2) R :=
  ![![challenge 0 (firstIndex level), challenge 0 (secondIndex level)]]

/-- Extract the two outputs associated with one gadget level. -/
def levelOutput {R : Type} {levels : ℕ}
    (output : Fin (levels + levels) → R) (level : Fin levels) : Fin 2 → R :=
  ![output (firstIndex level), output (secondIndex level)]

/-- Extract one paired ordinary transcript from a complete batch transcript. -/
def levelTranscript {R : Type} {levels : ℕ}
    (transcript : LWE.BatchTranscript R 1 (levels + levels)) (level : Fin levels) :
    LWE.BatchTranscript R 1 2 :=
  (levelChallenge transcript.1 level, levelOutput transcript.2 level)

/-- Assemble all gadget-level BV quadratic ciphertexts from paired masks and errors. -/
def assemble {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (challenge : Matrix (Fin 1) (Fin (levels + levels)) R)
    (error : Fin (levels + levels) → R) (gadget : Fin levels → R) :
    Ciphertexts R levels :=
  fun level ↦ BVQuadraticKDM.assemble secret (levelChallenge challenge level)
    (levelOutput error level) (gadget level)

/-- Paper-style direct presentation at every gadget level. -/
def assembleDirectSquare {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (challenge : Matrix (Fin 1) (Fin (levels + levels)) R)
    (error : Fin (levels + levels) → R) (gadget : Fin levels → R) :
    Ciphertexts R levels :=
  fun level ↦ BVQuadraticKDM.assembleDirectSquare secret
    (challenge 0 (firstIndex level)) (challenge 0 (secondIndex level))
    (error (firstIndex level)) (error (secondIndex level)) (gadget level)

/-- Secret-dependent public-mask offset that reparameterizes every direct square ciphertext as a
telescope ciphertext. -/
def maskOffset {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (gadget : Fin levels → R) :
    Matrix (Fin 1) (Fin (levels + levels)) R :=
  fun _ ↦ Fin.append (fun level ↦ gadget level * secret) gadget

/-- Add the joint direct-to-telescope mask offset. -/
def shiftMasks {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (levels + levels)) R) :=
  challenge + maskOffset secret gadget

/-- Undo the joint mask offset. -/
def unshiftMasks {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (levels + levels)) R) :=
  challenge - maskOffset secret gadget

@[simp]
theorem unshiftMasks_shiftMasks {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (levels + levels)) R) :
    unshiftMasks secret gadget (shiftMasks secret gadget challenge) = challenge := by
  simp [unshiftMasks, shiftMasks]

@[simp]
theorem shiftMasks_unshiftMasks {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (levels + levels)) R) :
    shiftMasks secret gadget (unshiftMasks secret gadget challenge) = challenge := by
  simp [unshiftMasks, shiftMasks]

/-- The joint mask translation is a permutation. -/
theorem shiftMasks_bijective {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (gadget : Fin levels → R) :
    Function.Bijective (shiftMasks secret gadget :
      Matrix (Fin 1) (Fin (levels + levels)) R → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unshiftMasks secret gadget, unshiftMasks_shiftMasks secret gadget,
      shiftMasks_unshiftMasks secret gadget⟩

@[simp]
theorem shiftMasks_first {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (levels + levels)) R) (level : Fin levels) :
    shiftMasks secret gadget challenge 0 (firstIndex level) =
      challenge 0 (firstIndex level) + gadget level * secret := by
  simp [shiftMasks, maskOffset, firstIndex]

@[simp]
theorem shiftMasks_second {R : Type} [Ring R] {levels : ℕ}
    (secret : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (levels + levels)) R) (level : Fin levels) :
    shiftMasks secret gadget challenge 0 (secondIndex level) =
      challenge 0 (secondIndex level) + gadget level := by
  change challenge 0 (secondIndex level) +
      Fin.append (fun level ↦ gadget level * secret) gadget (secondIndex level) = _
  rw [show secondIndex level = Fin.natAdd levels level from rfl, Fin.append_right]

/-- Joint mask reparameterization identifies the direct and telescope batches pointwise. -/
theorem assemble_shiftMasks {R : Type} [CommRing R] {levels : ℕ}
    (secret : R) (challenge : Matrix (Fin 1) (Fin (levels + levels)) R)
    (error : Fin (levels + levels) → R) (gadget : Fin levels → R) :
    assemble secret (shiftMasks secret gadget challenge) error gadget =
      assembleDirectSquare secret challenge error gadget := by
  funext level
  have hChallenge :
      levelChallenge (shiftMasks secret gadget challenge) level =
        BVQuadraticKDM.shiftedChallenge secret
          (challenge 0 (firstIndex level)) (challenge 0 (secondIndex level))
          (gadget level) := by
    funext row column
    rw [Subsingleton.elim row 0]
    fin_cases column
    · simp [levelChallenge, BVQuadraticKDM.shiftedChallenge]
    · simp [levelChallenge, BVQuadraticKDM.shiftedChallenge]
  rw [show assemble secret (shiftMasks secret gadget challenge) error gadget level =
      BVQuadraticKDM.assemble secret
        (levelChallenge (shiftMasks secret gadget challenge) level)
        (levelOutput error level) (gadget level) from rfl,
    hChallenge]
  simpa [assembleDirectSquare, levelOutput] using
    (BVQuadraticKDM.assemble_shiftedChallenge secret
      (challenge 0 (firstIndex level)) (challenge 0 (secondIndex level))
      (error (firstIndex level)) (error (secondIndex level)) (gadget level))

/-- Public telescope applied independently at every gadget level. -/
def telescope {R : Type} [Ring R] {levels : ℕ} (gadget : Fin levels → R)
    (transcript : LWE.BatchTranscript R 1 (levels + levels)) : Ciphertexts R levels :=
  fun level ↦ BVQuadraticKDM.telescope (gadget level) (levelTranscript transcript level)

/-- Exact phase at each gadget level. -/
theorem phase_assemble {R : Type} [CommRing R] {levels : ℕ}
    (secret : R) (challenge : Matrix (Fin 1) (Fin (levels + levels)) R)
    (error : Fin (levels + levels) → R) (gadget : Fin levels → R)
    (level : Fin levels) :
    BVQuadraticKDM.phase secret (assemble secret challenge error gadget level) =
      gadget level * secret * secret + error (firstIndex level) +
        error (secondIndex level) * secret := by
  simpa [assemble, levelOutput] using
    (BVQuadraticKDM.phase_assemble secret (levelChallenge challenge level)
      (levelOutput error level) (gadget level))

/-- The batched public telescope maps a concrete ordinary real transcript to the batch assembly
pointwise. -/
theorem telescope_real {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R)
    (challenge : Matrix (Fin 1) (Fin (levels + levels)) R)
    (error : Fin (levels + levels) → R) (gadget : Fin levels → R) :
    telescope gadget (challenge, vecMul secret challenge + error) =
      assemble (secret 0) challenge error gadget := by
  funext level coordinate
  fin_cases coordinate <;>
    simp [telescope, levelTranscript, levelChallenge, levelOutput,
      BVQuadraticKDM.telescope, assemble, BVQuadraticKDM.assemble,
      Matrix.vecMul, dotProduct] <;> ring

/-- Retain the first mask at every level as the unused fiber of the batched telescope. -/
def telescopeWithFiber {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (transcript : LWE.BatchTranscript R 1 (levels + levels)) :
    Ciphertexts R levels × (Fin levels → R) :=
  (telescope gadget transcript, fun level ↦ transcript.1 0 (firstIndex level))

/-- Inverse of the batched telescope with its retained first-mask fiber. -/
def untelescopeWithFiber {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (output : Ciphertexts R levels × (Fin levels → R)) :
    LWE.BatchTranscript R 1 (levels + levels) :=
  (fun _ coordinate ↦
      Fin.append output.2
        (fun level ↦ gadget level - output.1 level 2) coordinate,
    fun coordinate ↦
      Fin.append (fun level ↦ output.1 level 0)
        (fun level ↦ output.1 level 1 + output.2 level) coordinate)

@[simp]
theorem untelescopeWithFiber_challenge_first {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (output : Ciphertexts R levels × (Fin levels → R)) (level : Fin levels) :
    (untelescopeWithFiber gadget output).1 0 (firstIndex level) = output.2 level := by
  simp only [untelescopeWithFiber, firstIndex, Fin.append_left]

@[simp]
theorem untelescopeWithFiber_challenge_second {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (output : Ciphertexts R levels × (Fin levels → R)) (level : Fin levels) :
    (untelescopeWithFiber gadget output).1 0 (secondIndex level) =
      gadget level - output.1 level 2 := by
  simp only [untelescopeWithFiber, secondIndex, Fin.append_right]

@[simp]
theorem untelescopeWithFiber_output_first {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (output : Ciphertexts R levels × (Fin levels → R)) (level : Fin levels) :
    (untelescopeWithFiber gadget output).2 (firstIndex level) = output.1 level 0 := by
  simp only [untelescopeWithFiber, firstIndex, Fin.append_left]

@[simp]
theorem untelescopeWithFiber_output_second {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (output : Ciphertexts R levels × (Fin levels → R)) (level : Fin levels) :
    (untelescopeWithFiber gadget output).2 (secondIndex level) =
      output.1 level 1 + output.2 level := by
  simp only [untelescopeWithFiber, secondIndex, Fin.append_right]

@[simp]
theorem untelescopeWithFiber_telescopeWithFiber {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (transcript : LWE.BatchTranscript R 1 (levels + levels)) :
    untelescopeWithFiber gadget (telescopeWithFiber gadget transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  apply Prod.ext
  · funext row
    rw [Subsingleton.elim row 0]
    change Fin.append
        (fun level ↦ challenge 0 (Fin.castAdd levels level))
        (fun level ↦ gadget level -
          (-challenge 0 (Fin.natAdd levels level) + gadget level)) = challenge 0
    convert (Fin.append_castAdd_natAdd (f := challenge 0)) using 1
    funext level
    simp
  · change Fin.append
        (fun level ↦ output (Fin.castAdd levels level))
        (fun level ↦
          output (Fin.natAdd levels level) - challenge 0 (Fin.castAdd levels level) +
            challenge 0 (Fin.castAdd levels level)) = output
    convert (Fin.append_castAdd_natAdd (f := output)) using 1
    funext level
    simp

@[simp]
theorem telescopeWithFiber_untelescopeWithFiber {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (output : Ciphertexts R levels × (Fin levels → R)) :
    telescopeWithFiber gadget (untelescopeWithFiber gadget output) = output := by
  rcases output with ⟨ciphertexts, fiber⟩
  apply Prod.ext
  · funext level coordinate
    fin_cases coordinate <;>
      simp [telescopeWithFiber, telescope, levelTranscript, levelChallenge, levelOutput,
        BVQuadraticKDM.telescope]
  · funext level
    simp [telescopeWithFiber]

/-- The batched telescope plus its `levels`-coordinate fiber is bijective. -/
theorem telescopeWithFiber_bijective {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R) :
    Function.Bijective (telescopeWithFiber gadget :
      LWE.BatchTranscript R 1 (levels + levels) →
        Ciphertexts R levels × (Fin levels → R)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untelescopeWithFiber gadget,
      untelescopeWithFiber_telescopeWithFiber gadget,
      telescopeWithFiber_untelescopeWithFiber gadget⟩

/-- A uniform `2 * levels` ordinary transcript telescopes to a uniform batch of
three-component ciphertexts. -/
theorem telescope_uniform_evalDist {R : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (gadget : Fin levels → R) :
    evalDist (telescope gadget <$>
        ($ᵗ (LWE.BatchTranscript R 1 (levels + levels)))) =
      evalDist ($ᵗ (Ciphertexts R levels)) := by
  have hFiber :
      evalDist (telescopeWithFiber gadget <$>
          ($ᵗ (LWE.BatchTranscript R 1 (levels + levels)))) =
        evalDist ($ᵗ (Ciphertexts R levels × (Fin levels → R))) :=
    evalDist_map_bijective_uniform_cross
      (α := LWE.BatchTranscript R 1 (levels + levels))
      (β := Ciphertexts R levels × (Fin levels → R))
      (telescopeWithFiber gadget) (telescopeWithFiber_bijective gadget)
  calc
    evalDist (telescope gadget <$>
        ($ᵗ (LWE.BatchTranscript R 1 (levels + levels)))) =
      evalDist (Prod.fst <$> (telescopeWithFiber gadget <$>
        ($ᵗ (LWE.BatchTranscript R 1 (levels + levels))))) := by
        congr 1
        simp [Functor.map_map, telescopeWithFiber]
    _ = evalDist (Prod.fst <$>
        ($ᵗ (Ciphertexts R levels × (Fin levels → R)))) :=
      evalDist_map_eq_of_evalDist_eq hFiber Prod.fst
    _ = evalDist ($ᵗ (Ciphertexts R levels)) := evalDist_map_fst_uniformSample_prod

/-- Ordinary rank-one RLWE with two samples allocated to each gadget level. -/
abbrev ordinaryProblem {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) :=
  LWE.embeddedBatchProblem 1 (levels + levels) secretSampler embed errorSampler

/-- Direct shared-secret batch sampler for all gadget-scaled square ciphertexts. -/
def realSampler {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    ProbComp (Ciphertexts R levels) := do
  let challenge ← $ᵗ Matrix (Fin 1) (Fin (levels + levels)) R
  let secret ← secretSampler
  let error ← ProbComp.sampleIID (levels + levels) errorSampler
  pure (assemble (embed secret 0) challenge error gadget)

/-- Batched paper-style sampler with each `g_j S²` term visible in the first component. -/
def directSquareSampler {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    ProbComp (Ciphertexts R levels) := do
  let challenge ← $ᵗ Matrix (Fin 1) (Fin (levels + levels)) R
  let secret ← secretSampler
  let error ← ProbComp.sampleIID (levels + levels) errorSampler
  pure (assembleDirectSquare (embed secret 0) challenge error gadget)

/-- The complete direct and telescope batches are exactly equal in distribution under their
shared secret. -/
theorem realSampler_evalDist_eq_directSquareSampler {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    evalDist (realSampler levels secretSampler embed errorSampler gadget) =
      evalDist (directSquareSampler levels secretSampler embed errorSampler gadget) := by
  let challenges : ProbComp (Matrix (Fin 1) (Fin (levels + levels)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (levels + levels)) R
  let errors : ProbComp (Fin (levels + levels) → R) :=
    ProbComp.sampleIID (levels + levels) errorSampler
  let finish := fun (secret : Secret)
      (challenge : Matrix (Fin 1) (Fin (levels + levels)) R)
      (error : Fin (levels + levels) → R) ↦
    (pure (assemble (embed secret 0) challenge error gadget) :
      ProbComp (Ciphertexts R levels))
  have hShift : ∀ secret : Secret,
      evalDist (shiftMasks (embed secret 0) gadget <$> challenges) =
        evalDist challenges := by
    intro secret
    exact evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin 1) (Fin (levels + levels)) R)
      (β := Matrix (Fin 1) (Fin (levels + levels)) R)
      (shiftMasks (embed secret 0) gadget)
      (shiftMasks_bijective (embed secret 0) gadget)
  have hReal :
      evalDist (realSampler levels secretSampler embed errorSampler gadget) =
        evalDist (secretSampler >>= fun secret ↦
          challenges >>= fun challenge ↦ errors >>= finish secret challenge) := by
    rw [show evalDist (realSampler levels secretSampler embed errorSampler gadget) =
        evalDist (challenges >>= fun challenge ↦
          secretSampler >>= fun secret ↦ errors >>= finish secret challenge) by rfl]
    exact evalDist_bind_bind_swap challenges secretSampler
      (fun challenge secret ↦ errors >>= finish secret challenge)
  have hDirect :
      evalDist (directSquareSampler levels secretSampler embed errorSampler gadget) =
        evalDist (secretSampler >>= fun secret ↦
          challenges >>= fun challenge ↦
            errors >>= finish secret (shiftMasks (embed secret 0) gadget challenge)) := by
    rw [show
        evalDist (directSquareSampler levels secretSampler embed errorSampler gadget) =
          evalDist (challenges >>= fun challenge ↦
            secretSampler >>= fun secret ↦
              errors >>= finish secret
                (shiftMasks (embed secret 0) gadget challenge)) by
      apply congrArg evalDist
      simp [directSquareSampler, challenges, errors, finish, assemble_shiftMasks,
        monad_norm]]
    exact evalDist_bind_bind_swap challenges secretSampler
      (fun challenge secret ↦
        errors >>= finish secret (shiftMasks (embed secret 0) gadget challenge))
  rw [hReal, hDirect]
  refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
  rw [show
      (challenges >>= fun challenge ↦
        errors >>= finish secret (shiftMasks (embed secret 0) gadget challenge)) =
      ((shiftMasks (embed secret 0) gadget <$> challenges) >>=
        fun challenge ↦ errors >>= finish secret challenge) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, ← hShift secret, ← evalDist_bind]

/-- Boolean distinguisher for the complete gadget-level BV batch. -/
abbrev Distinguisher (R : Type) (levels : ℕ) := Ciphertexts R levels → ProbComp Bool

/-- Public batched-telescope reduction. -/
def reduction {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} {secretSampler : ProbComp Secret} {embed : Secret → Fin 1 → R}
    {errorSampler : ProbComp R} (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) :
    LearningWithErrors.Adversary
      (ordinaryProblem levels secretSampler embed errorSampler) :=
  fun transcript ↦ distinguisher (telescope gadget transcript)

/-- Real batched quadratic-KDM game. -/
def realGame {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) : ProbComp Bool :=
  realSampler levels secretSampler embed errorSampler gadget >>= distinguisher

/-- Uniform batched endpoint. -/
noncomputable def uniformGame {R : Type} [SampleableType R] {levels : ℕ}
    (distinguisher : Distinguisher R levels) : ProbComp Bool := do
  let ciphertexts ← $ᵗ (Ciphertexts R levels)
  distinguisher ciphertexts

/-- Batched quadratic-KDM advantage. -/
noncomputable def advantage {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) : ℝ :=
  (realGame levels secretSampler embed errorSampler gadget distinguisher).boolDistAdvantage
    (uniformGame distinguisher)

/-- Batched real distribution is exactly the public image of an ordinary shared-secret RLWE
batch. -/
theorem telescope_real_evalDist {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    evalDist (LearningWithErrors.distr
          (ordinaryProblem levels secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (telescope gadget transcript)) =
      evalDist (realSampler levels secretSampler embed errorSampler gadget) := by
  apply congrArg evalDist
  simp [LearningWithErrors.distr, ordinaryProblem, LWE.embeddedBatchProblem,
    realSampler, telescope_real, monad_norm]

/-- The ordinary batched uniform branch is its canonical uniform transcript sampler. -/
theorem ordinary_uniformDistr_eq_uniformSample {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (ordinaryProblem levels secretSampler embed errorSampler) =
      ($ᵗ (LWE.BatchTranscript R 1 (levels + levels))) := by
  unfold LearningWithErrors.uniformDistr ordinaryProblem LWE.embeddedBatchProblem
  have uniformProduct :
      ($ᵗ (LWE.BatchTranscript R 1 (levels + levels)) :
        ProbComp (LWE.BatchTranscript R 1 (levels + levels))) =
      Prod.mk <$> ($ᵗ Matrix (Fin 1) (Fin (levels + levels)) R) <*>
        ($ᵗ (Fin (levels + levels) → R)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- Exact real-game equality for the batched reduction. -/
theorem realGame_evalDist_eq_reduction_game0 {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) :
    evalDist (realGame levels secretSampler embed errorSampler gadget distinguisher) =
      evalDist (LearningWithErrors.game0
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget distinguisher)) := by
  rw [LearningWithErrors.game0]
  simp only [realGame, reduction]
  rw [show
      (LearningWithErrors.distr
          (ordinaryProblem levels secretSampler embed errorSampler) >>=
        fun transcript ↦ distinguisher (telescope gadget transcript)) =
      ((LearningWithErrors.distr
          (ordinaryProblem levels secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (telescope gadget transcript)) >>= distinguisher) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind,
    ← telescope_real_evalDist levels secretSampler embed errorSampler gadget,
    ← evalDist_bind]

/-- Exact uniform-game equality for the batched reduction. -/
theorem reduction_game1_evalDist_eq_uniformGame {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) :
    evalDist (LearningWithErrors.game1
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget distinguisher)) =
      evalDist (uniformGame distinguisher) := by
  rw [LearningWithErrors.game1,
    ordinary_uniformDistr_eq_uniformSample levels secretSampler embed errorSampler]
  simp only [reduction, uniformGame]
  rw [show
      (($ᵗ (LWE.BatchTranscript R 1 (levels + levels))) >>= fun transcript ↦
        distinguisher (telescope gadget transcript)) =
      ((telescope gadget <$>
        ($ᵗ (LWE.BatchTranscript R 1 (levels + levels)))) >>= distinguisher) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, telescope_uniform_evalDist gadget, ← evalDist_bind]

/-- **Lossless gadget-batch theorem.**  Encrypting every `g_j S²` in the BV
three-component format has exactly the advantage of one ordinary rank-one RLWE problem with
`2 * levels` samples. -/
theorem advantage_eq_batchRLWE {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) :
    advantage levels secretSampler embed errorSampler gadget distinguisher =
      LearningWithErrors.advantage
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold advantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (realGame_evalDist_eq_reduction_game0 levels secretSampler embed errorSampler gadget
        distinguisher) true,
    evalDist_ext_iff.mp
      (reduction_game1_evalDist_eq_uniformGame levels secretSampler embed errorSampler gadget
        distinguisher) true]

/-- Direct paper-style real game for the complete gadget batch. -/
def directRealGame {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) : ProbComp Bool :=
  directSquareSampler levels secretSampler embed errorSampler gadget >>= distinguisher

/-- Direct and telescope batch games have identical output distributions. -/
theorem directRealGame_evalDist_eq_realGame {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) :
    evalDist (directRealGame levels secretSampler embed errorSampler gadget distinguisher) =
      evalDist (realGame levels secretSampler embed errorSampler gadget distinguisher) := by
  unfold directRealGame realGame
  simp only [evalDist_bind]
  rw [← realSampler_evalDist_eq_directSquareSampler levels secretSampler embed errorSampler
    gadget]

/-- The familiar direct BV gadget batch is losslessly secure under ordinary batch RLWE. -/
theorem directAdvantage_eq_batchRLWE {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : Distinguisher R levels) :
    (directRealGame levels secretSampler embed errorSampler gadget
        distinguisher).boolDistAdvantage (uniformGame distinguisher) =
      LearningWithErrors.advantage
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget distinguisher) := by
  rw [← advantage_eq_batchRLWE levels secretSampler embed errorSampler gadget distinguisher]
  unfold advantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (directRealGame_evalDist_eq_realGame levels secretSampler embed errorSampler gadget
      distinguisher) true]

end Batch

end FormalProof4FHE.TFHE.TGSW.RingSquare.BVQuadraticKDM
