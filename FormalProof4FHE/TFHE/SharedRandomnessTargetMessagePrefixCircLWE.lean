/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearchToDecision
import FormalProof4FHE.TFHE.MonomialKDM
import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageCloudReduction

/-!
# Source-Prefix CircRLWE for Full-Target-Message TFHE

For the fixed-message conversion

`BRK(KeyExtract(S_source || S_suffix), S_source)`

the genuine circular hop replaces only the coordinates belonging to `S_source`.  The independent
suffix messages and the ring-extension table remain in the public view.  This file packages that
exact joint distribution as a one-challenge auxiliary-input CircLWE problem:

* the hidden secret is `(S_source, S_suffix)`;
* the real challenge is the complete target-message source BRK;
* the reference challenge zeros only the source-prefix messages and retains the suffix messages;
* the uniform challenge has the identical BRK carrier; and
* the auxiliary input is the real ring-extension table generated from the same nested keys.

The real/reference KDM advantage is proved definitionally equal to the source-prefix circular
term used by the adaptive TFHE theorem.  It is then bounded by the paper-style real/uniform
CircLWE term plus the explicit reference/uniform acyclic term.  At each fixed secret the real BRK
is also identified with the exact degree-two monomial presentation of native TGSW.

This is a distribution-identification and reduction boundary.  It does not assert that ordinary
RLWE proves the resulting native CircLWE problem.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.PrefixCircLWE

noncomputable section

/-- The nested source and independent suffix keys retained by the exact prefix problem. -/
abbrev Secret (sourceRank suffixRank degree : ℕ) :=
  NestedSecret sourceRank suffixRank degree

/-- The source-key BRK is the concrete CircLWE challenge. -/
abbrev Challenge
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels

/-- The real ring-extension table is fixed correlated auxiliary information. -/
abbrev Auxiliary
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  RingExtensionKey q degree sourceRank suffixRank tgswLevels

/-- Exact one-challenge problem for the genuine source-prefix circular hop.

The generic field named `sampleZero` is the prefix-zero reference branch here: it retains the
independent suffix messages rather than replacing the complete target-message vector by zero. -/
noncomputable def problem
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) :
    LWE.AuxiliaryInput.Problem
      (Secret sourceRank suffixRank degree)
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels) where
  sampleSecret := sampleNestedSecret sourceRank suffixRank degree
  sampleReal := fun secret ↦
    generateSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler gadget secret.1 secret.2
  sampleZero := fun secret ↦
    generateSuffixOnlySourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler gadget secret.1 secret.2
  sampleUniform := $ᵗ (Challenge q degree sourceRank suffixRank tgswLevels)
  sampleAuxiliary := fun secret ↦
    generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
      extensionErrorSampler gadget secret.1 secret.2

/-- Repackage the existing source continuation without changing its information flow. -/
def packContinuation
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    LWE.AuxiliaryInput.Continuation
      (Secret sourceRank suffixRank degree)
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels) :=
  fun secret challenge auxiliary ↦
    continuation secret.1 secret.2 challenge auxiliary

/-- The auxiliary-input real branch is exactly the corrected target-message source game. -/
theorem realGame_eq_source
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    LWE.AuxiliaryInput.realGame
        (problem q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget)
        (packContinuation continuation) =
      realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation := by
  simp [LWE.AuxiliaryInput.realGame, problem, packContinuation,
    sampleNestedSecret, realSourceContinuationGame, monad_norm]

/-- The generic reference branch is exactly the source-prefix-zero/suffix-retained hybrid. -/
theorem zeroGame_eq_suffixOnly
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    LWE.AuxiliaryInput.zeroGame
        (problem q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget)
        (packContinuation continuation) =
      suffixOnlySourceContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation := by
  simp [LWE.AuxiliaryInput.zeroGame, problem, packContinuation,
    sampleNestedSecret, suffixOnlySourceContinuationGame, monad_norm]

/-- Uniform-BRK comparison retaining the same nested keys and real extension table. -/
noncomputable def uniformSourceContinuationGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) : ProbComp Bool := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ←
    $ᵗ (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
    extensionErrorSampler gadget sourceSecret suffixSecret
  continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey

/-- The generic uniform branch is the native uniform-BRK source continuation. -/
theorem uniformGame_eq_source
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    LWE.AuxiliaryInput.uniformGame
        (problem q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget)
        (packContinuation continuation) =
      uniformSourceContinuationGame q degree sourceRank suffixRank tgswLevels
        extensionErrorSampler gadget continuation := by
  simp [LWE.AuxiliaryInput.uniformGame, problem, packContinuation,
    sampleNestedSecret, uniformSourceContinuationGame, monad_norm]

/-- Paper-style real/reference KDM advantage for the exact source-prefix problem. -/
noncomputable def kdmAdvantage
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) : ℝ :=
  LWE.AuxiliaryInput.kdmAdvantage
    (problem q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget)
    (packContinuation continuation)

/-- Native real-versus-uniform CircLWE advantage with the complete retained context. -/
noncomputable def circularLweAdvantage
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) : ℝ :=
  LWE.AuxiliaryInput.circularLweAdvantage
    (problem q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget)
    (packContinuation continuation)

/-- Prefix-zero/suffix-retained BRK versus uniform with the same extension table. -/
noncomputable def referenceLweAdvantage
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) : ℝ :=
  LWE.AuxiliaryInput.zeroLweAdvantage
    (problem q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget)
    (packContinuation continuation)

/-! ## Public reference branch from ordinary module RLWE -/

/-- The source-prefix reference branch for a public FHE continuation is exactly the acyclic
suffix-only cloud game.  Neither nested ring secret is passed to the continuation. -/
theorem publicReferenceGame_evalDist_eq_suffixOnlyCloud
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : CloudReduction.PublicContinuation
      q degree sourceRank suffixRank tgswLevels) :
    evalDist (LWE.AuxiliaryInput.zeroGame
        (problem q degree sourceRank suffixRank tgswLevels
          errorSampler errorSampler gadget)
        (packContinuation
          (CloudReduction.publicSourceContinuation continuation))) =
      evalDist (CloudReduction.suffixOnlyGame q degree sourceRank suffixRank
        tgswLevels errorSampler gadget continuation) := by
  rw [zeroGame_eq_suffixOnly]
  rfl

/-- The public uniform branch of the exact prefix problem is the cloud zero-reduction's real
branch after independently resampling its ignored BRK.  The extra zero-BRK draw is dropped and
the independent uniform BRK is commuted past the real extension-table draw. -/
theorem publicUniformGame_evalDist_eq_zeroCloud_resampled
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : CloudReduction.PublicContinuation
      q degree sourceRank suffixRank tgswLevels) :
    evalDist (LWE.AuxiliaryInput.uniformGame
        (problem q degree sourceRank suffixRank tgswLevels
          errorSampler errorSampler gadget)
        (packContinuation
          (CloudReduction.publicSourceContinuation continuation))) =
      evalDist (CloudReduction.zeroGame q degree sourceRank suffixRank tgswLevels
        errorSampler gadget
        (CloudReduction.resampleBootstrapContinuation continuation)) := by
  rw [uniformGame_eq_source]
  let SourceSecrets := Native.sampleRingSecret sourceRank degree
  let SuffixSecrets := Native.sampleRingSecret suffixRank degree
  let UniformBootstrap : ProbComp
      (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels) :=
    $ᵗ (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
  let ZeroBootstrap := fun sourceSecret : RingBinarySecret sourceRank degree ↦
    generateZeroSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
      errorSampler gadget sourceSecret
  let Extension := fun (sourceSecret : RingBinarySecret sourceRank degree)
      (suffixSecret : RingBinarySecret suffixRank degree) ↦
    generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
      errorSampler gadget sourceSecret suffixSecret
  change evalDist (SourceSecrets >>= fun sourceSecret ↦
      SuffixSecrets >>= fun suffixSecret ↦
      UniformBootstrap >>= fun bootstrappingKey ↦
      Extension sourceSecret suffixSecret >>= fun extensionKey ↦
      continuation bootstrappingKey extensionKey) =
    evalDist (SourceSecrets >>= fun sourceSecret ↦
      SuffixSecrets >>= fun suffixSecret ↦
      ZeroBootstrap sourceSecret >>= fun _ ↦
      Extension sourceSecret suffixSecret >>= fun extensionKey ↦
      UniformBootstrap >>= fun bootstrappingKey ↦
      continuation bootstrappingKey extensionKey)
  refine evalDist_bind_congr' SourceSecrets fun sourceSecret ↦ ?_
  refine evalDist_bind_congr' SuffixSecrets fun suffixSecret ↦ ?_
  calc
    _ = evalDist (Extension sourceSecret suffixSecret >>= fun extensionKey ↦
          UniformBootstrap >>= fun bootstrappingKey ↦
          continuation bootstrappingKey extensionKey) :=
      evalDist_bind_bind_swap UniformBootstrap (Extension sourceSecret suffixSecret)
        (fun bootstrappingKey extensionKey ↦
          continuation bootstrappingKey extensionKey)
    _ = _ :=
      (FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (ZeroBootstrap sourceSecret) (by simp [ZeroBootstrap]) _).symm

/-- **The public reference branch is ordinary module RLWE.**  With one common ring-error
sampler, distinguishing the suffix-only/reference BRK from a uniform BRK while retaining the
real correlated extension table costs at most two advantages for the same blocked module-RLWE
problem.  The first reduction replaces the complete suffix cloud by uniform; the second
resamples the BRK and replaces only the retained extension table. -/
theorem publicReferenceLweAdvantage_le_two_moduleLwe
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : CloudReduction.PublicContinuation
      q degree sourceRank suffixRank tgswLevels) :
    referenceLweAdvantage errorSampler errorSampler gadget
        (CloudReduction.publicSourceContinuation continuation) ≤
      LearningWithErrors.advantage
          (CloudReduction.problem q degree sourceRank suffixRank tgswLevels errorSampler)
          (CloudReduction.suffixReduction gadget continuation) +
        LearningWithErrors.advantage
          (CloudReduction.problem q degree sourceRank suffixRank tgswLevels errorSampler)
          (CloudReduction.zeroReduction gadget
            (CloudReduction.resampleBootstrapContinuation continuation)) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold referenceLweAdvantage LWE.AuxiliaryInput.zeroLweAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (publicReferenceGame_evalDist_eq_suffixOnlyCloud q degree sourceRank suffixRank
        tgswLevels errorSampler gadget continuation) true,
    evalDist_ext_iff.mp
      (publicUniformGame_evalDist_eq_zeroCloud_resampled q degree sourceRank suffixRank
        tgswLevels errorSampler gadget continuation) true,
    evalDist_ext_iff.mp
      (CloudReduction.suffixOnlyGame_evalDist_eq_game0 q degree sourceRank suffixRank
        tgswLevels errorSampler gadget continuation) true,
    evalDist_ext_iff.mp
      (CloudReduction.zeroGame_evalDist_eq_game0 q degree sourceRank suffixRank
        tgswLevels errorSampler gadget
          (CloudReduction.resampleBootstrapContinuation continuation)) true]
  let suffixProbability : ℝ :=
    (Pr[= true | LearningWithErrors.game0
      (CloudReduction.problem q degree sourceRank suffixRank tgswLevels errorSampler)
      (CloudReduction.suffixReduction gadget continuation)]).toReal
  let uniformSuffixProbability : ℝ :=
    (Pr[= true | LearningWithErrors.game1
      (CloudReduction.problem q degree sourceRank suffixRank tgswLevels errorSampler)
      (CloudReduction.suffixReduction gadget continuation)]).toReal
  let resampledProbability : ℝ :=
    (Pr[= true | LearningWithErrors.game0
      (CloudReduction.problem q degree sourceRank suffixRank tgswLevels errorSampler)
      (CloudReduction.zeroReduction gadget
        (CloudReduction.resampleBootstrapContinuation continuation))]).toReal
  let uniformResampledProbability : ℝ :=
    (Pr[= true | LearningWithErrors.game1
      (CloudReduction.problem q degree sourceRank suffixRank tgswLevels errorSampler)
      (CloudReduction.zeroReduction gadget
        (CloudReduction.resampleBootstrapContinuation continuation))]).toReal
  have hUniform : uniformSuffixProbability = uniformResampledProbability := by
    apply congrArg ENNReal.toReal
    exact evalDist_ext_iff.mp
      ((CloudReduction.suffixReduction_game1_evalDist_eq_uniform q degree sourceRank
          suffixRank tgswLevels errorSampler gadget continuation).trans
        ((CloudReduction.uniformGame_resampleBootstrapContinuation_evalDist q degree
          sourceRank suffixRank tgswLevels continuation).symm.trans
        (CloudReduction.zeroReduction_game1_evalDist_eq_uniform q degree sourceRank
          suffixRank tgswLevels errorSampler gadget
            (CloudReduction.resampleBootstrapContinuation continuation)).symm)) true
  change |suffixProbability - resampledProbability| ≤
    |suffixProbability - uniformSuffixProbability| +
      |resampledProbability - uniformResampledProbability|
  rw [hUniform, abs_sub_comm resampledProbability uniformResampledProbability]
  exact abs_sub_le suffixProbability uniformResampledProbability resampledProbability

/-- The corrected source-prefix term is exactly this fixed-distribution KDM advantage. -/
theorem kdmAdvantage_eq_sourcePrefixCircularAdvantage
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    kdmAdvantage bootstrapErrorSampler extensionErrorSampler gadget continuation =
      sourcePrefixCircularAdvantage q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation := by
  unfold kdmAdvantage LWE.AuxiliaryInput.kdmAdvantage
    sourcePrefixCircularAdvantage
  rw [realGame_eq_source, zeroGame_eq_suffixOnly]

/-- PKC-2024-style CircLWE plus the explicit acyclic reference branch bounds the genuine
source-prefix replacement. -/
theorem sourcePrefixCircularAdvantage_le_circularLwe_add_referenceLwe
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation :
      SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    sourcePrefixCircularAdvantage q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation ≤
      circularLweAdvantage bootstrapErrorSampler extensionErrorSampler gadget continuation +
        referenceLweAdvantage bootstrapErrorSampler extensionErrorSampler gadget continuation := by
  rw [← kdmAdvantage_eq_sourcePrefixCircularAdvantage]
  exact LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe
    (problem q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget)
    (packContinuation continuation)

/-- **Public source-prefix KDM from native CircRLWE plus ordinary module RLWE.**  For the actual
FHE information flow, where the continuation sees only the public BRK and extension table, the
reference term in the generic CircLWE triangle is no longer an auxiliary circular assumption.
It is discharged by the two exact blocked module-RLWE reductions above.  Consequently the sole
nonstandard term is the real-versus-uniform native degree-two CircRLWE challenge. -/
theorem publicSourcePrefixCircularAdvantage_le_circularLwe_add_two_moduleLwe
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : CloudReduction.PublicContinuation
      q degree sourceRank suffixRank tgswLevels) :
    sourcePrefixCircularAdvantage q degree sourceRank suffixRank tgswLevels
        errorSampler errorSampler gadget
        (CloudReduction.publicSourceContinuation continuation) ≤
      circularLweAdvantage errorSampler errorSampler gadget
          (CloudReduction.publicSourceContinuation continuation) +
        (LearningWithErrors.advantage
            (CloudReduction.problem q degree sourceRank suffixRank tgswLevels errorSampler)
            (CloudReduction.suffixReduction gadget continuation) +
          LearningWithErrors.advantage
            (CloudReduction.problem q degree sourceRank suffixRank tgswLevels errorSampler)
            (CloudReduction.zeroReduction gadget
              (CloudReduction.resampleBootstrapContinuation continuation))) := by
  have hPrefix :=
    sourcePrefixCircularAdvantage_le_circularLwe_add_referenceLwe
      errorSampler errorSampler gadget
        (CloudReduction.publicSourceContinuation continuation)
  have hReference := publicReferenceLweAdvantage_le_two_moduleLwe
    errorSampler gadget continuation
  exact hPrefix.trans (add_le_add (le_refl _) hReference)

/-! ## Exact degree-two presentation -/

/-- At a source-prefix target-message coordinate, the monomial lift is literally the product of
the source ring component and one coefficient of that same source key.  This is the genuine
one-key quadratic coordinate isolated by the circular-security references. -/
@[simp]
theorem sourceCoordinate_crossMonomial_eq_self
    (q degree sourceRank suffixRank : ℕ) [NeZero q]
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree)
    (sourceComponent ringComponent : Fin sourceRank)
    (coefficient : Fin degree) :
    TGSW.MonomialKDM.crossMonomial
        (embedRingSecret q sourceSecret)
        (embedConstantBit q degree
          (targetMessages sourceSecret suffixSecret
            (finProdFinEquiv (Fin.castAdd suffixRank sourceComponent, coefficient))))
        ringComponent =
      TGSW.MonomialKDM.crossMonomial
        (embedRingSecret q sourceSecret)
        (embedConstantBit q degree
          (keyExtract sourceSecret (finProdFinEquiv (sourceComponent, coefficient))))
        ringComponent := by
  rw [targetMessages_source]

/-- At a suffix target-message coordinate, the same lift is a product of the source encryption
key and an independently sampled suffix coefficient.  It is therefore not a second self-cycle. -/
@[simp]
theorem suffixCoordinate_crossMonomial_eq_independent
    (q degree sourceRank suffixRank : ℕ) [NeZero q]
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree)
    (suffixComponent : Fin suffixRank) (ringComponent : Fin sourceRank)
    (coefficient : Fin degree) :
    TGSW.MonomialKDM.crossMonomial
        (embedRingSecret q sourceSecret)
        (embedConstantBit q degree
          (targetMessages sourceSecret suffixSecret
            (finProdFinEquiv (Fin.natAdd sourceRank suffixComponent, coefficient))))
        ringComponent =
      TGSW.MonomialKDM.crossMonomial
        (embedRingSecret q sourceSecret)
        (embedConstantBit q degree
          (keyExtract suffixSecret (finProdFinEquiv (suffixComponent, coefficient))))
        ringComponent := by
  rw [targetMessages_suffix]

/-- The supplied beyond-affine references apply only after exposing the degree-two coordinates.
This sampler presents every normalized native source-BRK row through that explicit monomial lift. -/
noncomputable def generateMonomialSourceBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels) :=
  FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
    q degree sourceRank tgswLevels (targetScalarDimension sourceRank suffixRank degree)
    errorSampler gadget (targetMessages sourceSecret suffixSecret) sourceSecret

/-- At every fixed nested key, the real native source BRK has exactly the degree-two monomial
distribution; no statistical approximation is used. -/
theorem generateSourceBootstrappingKey_evalDist_eq_monomial
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    evalDist (generateSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
      errorSampler gadget sourceSecret suffixSecret) =
      evalDist (generateMonomialSourceBootstrappingKey q degree sourceRank suffixRank
        tgswLevels errorSampler gadget sourceSecret suffixSecret) := by
  calc
    _ = evalDist
        (Native.BootstrapSecurity.generateDirectBootstrappingKey
          q degree sourceRank tgswLevels
          (targetScalarDimension sourceRank suffixRank degree)
          errorSampler gadget (targetMessages sourceSecret suffixSecret) sourceSecret) := by
      exact Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
        q degree sourceRank tgswLevels
        (targetScalarDimension sourceRank suffixRank degree)
        errorSampler gadget (targetMessages sourceSecret suffixSecret) sourceSecret
    _ = _ := by
      unfold generateMonomialSourceBootstrappingKey
      rw [FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct]

/-- The real challenge field of the exact CircLWE problem has the same monomial law. -/
theorem sampleReal_evalDist_eq_monomial
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (secret : Secret sourceRank suffixRank degree) :
    evalDist
        ((problem q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget).sampleReal secret) =
      evalDist (generateMonomialSourceBootstrappingKey q degree sourceRank suffixRank
        tgswLevels bootstrapErrorSampler gadget secret.1 secret.2) := by
  exact generateSourceBootstrappingKey_evalDist_eq_monomial
    q degree sourceRank suffixRank tgswLevels bootstrapErrorSampler gadget secret.1 secret.2

/-! ## Exact public search endpoint -/

/-- A public solver sees the source BRK and ring-extension table, but not either nested key. -/
abbrev Solver
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  LWE.AuxiliaryInput.Search.Solver
    (Secret sourceRank suffixRank degree)
    (Challenge q degree sourceRank suffixRank tgswLevels)
    (Auxiliary q degree sourceRank suffixRank tgswLevels)

/-- Exact recovery problem associated with the real source-prefix CircLWE view. -/
noncomputable def searchProblem
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) :=
  LWE.AuxiliaryInput.Search.exactRecoveryProblem
    (problem q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget)

/-- Search success is bounded by exact source-prefix CircLWE advantage plus recovery at the
uniform-BRK/real-extension endpoint. -/
theorem searchSuccess_le_circularLwe_add_uniformRecovery
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (solver : Solver q degree sourceRank suffixRank tgswLevels) :
    LWE.AuxiliaryInput.Search.successProbability
        (searchProblem q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget)
        solver ≤
      ENNReal.ofReal
          (LWE.AuxiliaryInput.circularLweAdvantage
            (problem q degree sourceRank suffixRank tgswLevels
              bootstrapErrorSampler extensionErrorSampler gadget)
            (LWE.AuxiliaryInput.Search.recoveryContinuation solver)) +
        Pr[= true |
          LWE.AuxiliaryInput.Search.uniformRecoveryGame
            (problem q degree sourceRank suffixRank tgswLevels
              bootstrapErrorSampler extensionErrorSampler gadget)
            solver] := by
  exact LWE.AuxiliaryInput.Search.successProbability_exactRecovery_le_circularLwe_add_uniform
      (problem q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget)
      solver

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.PrefixCircLWE
