/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveReduction
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleSecretRandomization

set_option autoImplicit false

/-!
# Direct Public CircLWE Game for Full-Target-Message Adaptive TFHE

This file states the circular-security object in the form used directly by FHE security.  The
real source BRK and correlated source-to-target ring-extension table are retained as public
information.  The decisional challenge is the query-counted zero-message TLWE tape under
`KeyExtract(S_target)`, compared with a uniform tape of the identical type.

Thus the joint real distribution is

`(BRK(KeyExtract(S_target), S_source), Ext(S_suffix, S_source),
  LWE_KeyExtract(S_target)(0))`,

where `S_target = S_source || S_suffix`.  This is the direct FHE analogue of auxiliary-input
CircLWE: the circular evaluation key remains real while the encryption samples are challenged.
The adaptive TFHE adversary is compiled into a public distinguisher that receives only this view,
never either nested secret.

For a query-bounded adversary, its absolute honest IND advantage is proved exactly equal to this
public CircLWE advantage.  The associated exact-recovery search problem is also exposed as the
input to a PKC-2024-style search-to-decision program.  No reduction from ordinary RLWE is asserted.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision

/-- The nested source key and independent suffix key. -/
abbrev Secret (sourceRank suffixRank degree : ℕ) :=
  NestedSecret sourceRank suffixRank degree

/-- Query-counted target-key zero-encryption tape challenged against uniform. -/
abbrev Challenge (q degree sourceRank suffixRank queryCount : ℕ) :=
  TLWE.BatchCiphertext (ZMod q)
    (targetScalarDimension sourceRank suffixRank degree) queryCount

/-- The real circular evaluation material retained in both decision branches. -/
abbrev Auxiliary (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
    RingExtensionKey q degree sourceRank suffixRank tgswLevels

/-! ## Exact fresh-secret action -/

/-- Independent coefficientwise XOR masks for the nested source and suffix keys. -/
abbrev Mask (sourceRank suffixRank degree : ℕ) :=
  Secret sourceRank suffixRank degree

/-- Apply independent complete binary masks to both nested key blocks. -/
def act
    {sourceRank suffixRank degree : ℕ}
    (secret : Secret sourceRank suffixRank degree)
    (mask : Mask sourceRank suffixRank degree) :
    Secret sourceRank suffixRank degree :=
  (Native.SharedRandomnessOneCycle.SecretRandomization.maskedRingSecret
      secret.1 mask.1,
    Native.SharedRandomnessOneCycle.SecretRandomization.maskedRingSecret
      secret.2 mask.2)

/-- The nested XOR action is an involution for every fixed source secret. -/
@[simp]
theorem act_involutive
    {sourceRank suffixRank degree : ℕ}
    (secret mask : Secret sourceRank suffixRank degree) :
    act secret (act secret mask) = mask := by
  rcases secret with ⟨sourceSecret, suffixSecret⟩
  rcases mask with ⟨sourceMask, suffixMask⟩
  simp [act,
    Native.SharedRandomnessOneCycle.SecretRandomization.maskedRingSecret_involutive]

/-- XOR by a fixed nested secret, packaged as a permutation. -/
def actEquiv
    {sourceRank suffixRank degree : ℕ}
    (secret : Secret sourceRank suffixRank degree) :
    Secret sourceRank suffixRank degree ≃ Secret sourceRank suffixRank degree where
  toFun := act secret
  invFun := act secret
  left_inv := act_involutive secret
  right_inv := act_involutive secret

/-- The explicit independent nested sampler has the canonical uniform product law. -/
theorem sampleNestedSecret_evalDist_eq_uniform
    (sourceRank suffixRank degree : ℕ) :
    evalDist (sampleNestedSecret sourceRank suffixRank degree) =
      evalDist ($ᵗ (Secret sourceRank suffixRank degree)) := by
  let sources := Native.sampleRingSecret sourceRank degree
  let suffixes := Native.sampleRingSecret suffixRank degree
  have uniformProduct :
      ($ᵗ (Secret sourceRank suffixRank degree) :
        ProbComp (Secret sourceRank suffixRank degree)) =
      Prod.mk <$> sources <*> suffixes := rfl
  rw [uniformProduct]
  simp [sampleNestedSecret, sources, suffixes, bind_assoc, monad_norm]

/-- A uniform nested XOR mask sends every fixed nested key to an exactly fresh nested key.  This
discharges the secret-law component of the PKC shifted-secret randomization; transforming the
native public view is the genuinely hard remaining component. -/
theorem secretAction_evalDist
    (sourceRank suffixRank degree : ℕ)
    (secret : Secret sourceRank suffixRank degree) :
    evalDist (act secret <$> sampleNestedSecret sourceRank suffixRank degree) =
      evalDist (sampleNestedSecret sourceRank suffixRank degree) := by
  calc
    _ = evalDist (act secret <$>
        ($ᵗ (Secret sourceRank suffixRank degree))) :=
      evalDist_map_eq_of_evalDist_eq
        (sampleNestedSecret_evalDist_eq_uniform sourceRank suffixRank degree)
        (act secret)
    _ = evalDist ($ᵗ (Secret sourceRank suffixRank degree)) :=
      evalDist_map_bijective_uniform_cross
        (α := Secret sourceRank suffixRank degree)
        (β := Secret sourceRank suffixRank degree)
        (act secret) (actEquiv secret).bijective
    _ = _ :=
      (sampleNestedSecret_evalDist_eq_uniform sourceRank suffixRank degree).symm

/-- Direct public auxiliary-input CircLWE problem for adaptive full-target-message TFHE.

The generic `sampleZero` field is set to the same uniform tape as `sampleUniform`; only the
real-versus-uniform CircLWE branches are used here. -/
def problem
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) :
    FormalProof4FHE.LWE.AuxiliaryInput.Problem
      (Secret sourceRank suffixRank degree)
      (Challenge q degree sourceRank suffixRank queryCount)
      (Auxiliary q degree sourceRank suffixRank tgswLevels) where
  sampleSecret := sampleNestedSecret sourceRank suffixRank degree
  sampleReal := fun secret ↦
    TLWE.batchEncrypt (targetScalarDimension sourceRank suffixRank degree) queryCount
      inputErrorSampler (embedBinarySecret (targetMessages secret.1 secret.2)) 0
  sampleZero := fun _ ↦
    $ᵗ (Challenge q degree sourceRank suffixRank queryCount)
  sampleUniform := $ᵗ (Challenge q degree sourceRank suffixRank queryCount)
  sampleAuxiliary := fun secret ↦ do
    let sourceBootstrappingKey ← generateSourceBootstrappingKey q degree sourceRank
      suffixRank tgswLevels bootstrapErrorSampler gadget secret.1 secret.2
    let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
      tgswLevels extensionErrorSampler gadget secret.1 secret.2
    return (sourceBootstrappingKey, ringExtensionKey)

/-! ## Specialized PKC shifted-view interface -/

/-- Complete public real view used by secret randomization: target tape followed by the real
circular evaluation material. -/
abbrev View
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  Challenge q degree sourceRank suffixRank queryCount ×
    Auxiliary q degree sourceRank suffixRank tgswLevels

/-- Sample the complete fixed-secret real public view of one direct CircLWE problem. -/
def sampleRealView
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (secret : Secret sourceRank suffixRank degree) :
    ProbComp (View q degree sourceRank suffixRank tgswLevels queryCount) := do
  let challenge ←
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget).sampleReal secret
  let auxiliary ←
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget).sampleAuxiliary
      secret
  return (challenge, auxiliary)

/-- Concrete open certificate corresponding to the shifted evaluation and noise-flooding step in
the PKC 2024 proof.  It must publicly transform the *complete* nested-key view, including the
source BRK, extension table, and target-key tape, to the widened fresh-key law. -/
structure ShiftedViewEvaluator
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree))
    (narrowInputErrorSampler : ProbComp (ZMod q))
    (wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree))
    (wideInputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) where
  evaluateAndSmudge :
    Mask sourceRank suffixRank degree →
      View q degree sourceRank suffixRank tgswLevels queryCount →
        ProbComp (View q degree sourceRank suffixRank tgswLevels queryCount)
  error : ℝ
  error_nonneg : 0 ≤ error
  viewDistance_le : ∀ secret mask,
    tvDist
        (sampleRealView q degree sourceRank suffixRank tgswLevels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler
            narrowInputErrorSampler gadget secret >>=
          evaluateAndSmudge mask)
        (sampleRealView q degree sourceRank suffixRank tgswLevels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler wideInputErrorSampler
          gadget (act secret mask)) ≤ error

namespace ShiftedViewEvaluator

/-- Package the exact nested-secret action and a supplied native shifted evaluator into the
generic paper-aligned randomization compiler. -/
def toViewRandomization
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {narrowInputErrorSampler : ProbComp (ZMod q)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideInputErrorSampler : ProbComp (ZMod q)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedViewEvaluator q degree sourceRank suffixRank tgswLevels
      queryCount narrowBootstrapErrorSampler narrowExtensionErrorSampler
      narrowInputErrorSampler wideBootstrapErrorSampler wideExtensionErrorSampler
      wideInputErrorSampler gadget) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (Secret sourceRank suffixRank degree)
      (Mask sourceRank suffixRank degree)
      (View q degree sourceRank suffixRank tgswLevels queryCount) where
  sampleMask := sampleNestedSecret sourceRank suffixRank degree
  act := act
  sampleFreshSecret := sampleNestedSecret sourceRank suffixRank degree
  sampleNarrowView := sampleRealView q degree sourceRank suffixRank tgswLevels
    queryCount narrowBootstrapErrorSampler narrowExtensionErrorSampler
    narrowInputErrorSampler gadget
  sampleWideView := sampleRealView q degree sourceRank suffixRank tgswLevels
    queryCount wideBootstrapErrorSampler wideExtensionErrorSampler wideInputErrorSampler
    gadget
  evaluateAndSmudge := evaluator.evaluateAndSmudge
  error := evaluator.error
  error_nonneg := evaluator.error_nonneg
  secretLaw := secretAction_evalDist sourceRank suffixRank degree
  viewDistance_le := evaluator.viewDistance_le

/-- A supplied complete-view evaluator pays its pointwise loss only once after sampling the full
nested mask. -/
theorem randomizedView_tvDist_freshWideView_le
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {narrowInputErrorSampler : ProbComp (ZMod q)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideInputErrorSampler : ProbComp (ZMod q)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedViewEvaluator q degree sourceRank suffixRank tgswLevels
      queryCount narrowBootstrapErrorSampler narrowExtensionErrorSampler
      narrowInputErrorSampler wideBootstrapErrorSampler wideExtensionErrorSampler
      wideInputErrorSampler gadget)
    (secret : Secret sourceRank suffixRank degree) :
    tvDist (evaluator.toViewRandomization.randomizedView secret)
        evaluator.toViewRandomization.freshWideView ≤ evaluator.error := by
  exact evaluator.toViewRandomization.randomizedView_tvDist_freshWideView_le secret

end ShiftedViewEvaluator

/-- Compile an adaptive TFHE adversary into a genuinely public CircLWE distinguisher. -/
def adaptiveDistinguisher
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    PublicDistinguisher
      (Challenge q degree sourceRank suffixRank queryCount)
      (Auxiliary q degree sourceRank suffixRank tgswLevels) :=
  fun tape auxiliary ↦ do
    let cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels :=
      ⟨deriveBootstrappingKey q degree sourceRank suffixRank tgswLevels decompose
        auxiliary.1 auxiliary.2⟩
    let bit ← $ᵗ Bool
    let guess ← runFromTranscript bit encode adversary cloudKey tape
    return bit == guess

/-- Direct public real-evaluation-key/real-tape versus real-evaluation-key/uniform-tape
CircLWE advantage. -/
def circularLweAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) : ℝ :=
  publicAdvantage
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
    (adaptiveDistinguisher decompose encode adversary)

/-- Explicit real-evaluation-key game with a uniform target-key tape. -/
def uniformTapeGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    ProbComp Bool := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ← generateSourceBootstrappingKey q degree sourceRank
    suffixRank tgswLevels bootstrapErrorSampler gadget sourceSecret suffixSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels extensionErrorSampler gadget sourceSecret suffixSecret
  let tape ← $ᵗ (Challenge q degree sourceRank suffixRank queryCount)
  adaptiveDistinguisher decompose encode adversary tape
    (sourceBootstrappingKey, ringExtensionKey)

/-- The direct CircLWE real branch is exactly the honest adaptive TFHE game. -/
theorem realGame_evalDist_eq_realAdaptiveGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.realGame
          (problem q degree sourceRank suffixRank tgswLevels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
          (publicContinuation (adaptiveDistinguisher decompose encode adversary))) =
      evalDist
        (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
          encode adversary) := by
  let sourceSecrets := Native.sampleRingSecret sourceRank degree
  let suffixes := Native.sampleRingSecret suffixRank degree
  let bootstrappingKeys := fun
      (sourceSecret : RingBinarySecret sourceRank degree)
      (suffixSecret : RingBinarySecret suffixRank degree) ↦
    generateSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler gadget sourceSecret suffixSecret
  let extensionKeys := fun
      (sourceSecret : RingBinarySecret sourceRank degree)
      (suffixSecret : RingBinarySecret suffixRank degree) ↦
    generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
      extensionErrorSampler gadget sourceSecret suffixSecret
  let tapes := fun
      (sourceSecret : RingBinarySecret sourceRank degree)
      (suffixSecret : RingBinarySecret suffixRank degree) ↦
    TLWE.batchEncrypt (targetScalarDimension sourceRank suffixRank degree) queryCount
      inputErrorSampler (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
  let finish := fun
      (bootstrappingKey : SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
      (extensionKey : RingExtensionKey q degree sourceRank suffixRank tgswLevels)
      (tape : Challenge q degree sourceRank suffixRank queryCount) ↦
    adaptiveDistinguisher decompose encode adversary tape
      (bootstrappingKey, extensionKey)
  have hLeft : evalDist
      (FormalProof4FHE.LWE.AuxiliaryInput.realGame
        (problem q degree sourceRank suffixRank tgswLevels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
        (publicContinuation (adaptiveDistinguisher decompose encode adversary))) =
      evalDist (sourceSecrets >>= fun sourceSecret ↦
        suffixes >>= fun suffixSecret ↦
        tapes sourceSecret suffixSecret >>= fun tape ↦
        bootstrappingKeys sourceSecret suffixSecret >>= fun bootstrappingKey ↦
        extensionKeys sourceSecret suffixSecret >>= fun extensionKey ↦
        finish bootstrappingKey extensionKey tape) := by
    simp [FormalProof4FHE.LWE.AuxiliaryInput.realGame, publicContinuation, problem,
      sampleNestedSecret, sourceSecrets, suffixes, tapes, bootstrappingKeys,
      extensionKeys, finish, bind_assoc, monad_norm]
  have hRight : evalDist
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary) =
      evalDist (sourceSecrets >>= fun sourceSecret ↦
        suffixes >>= fun suffixSecret ↦
        bootstrappingKeys sourceSecret suffixSecret >>= fun bootstrappingKey ↦
        extensionKeys sourceSecret suffixSecret >>= fun extensionKey ↦
        tapes sourceSecret suffixSecret >>= fun tape ↦
        finish bootstrappingKey extensionKey tape) := by
    simp [realAdaptiveGame, realContinuationGame, generateCloudKey, adaptiveContinuation,
      adaptiveDistinguisher, sourceSecrets, suffixes, tapes, bootstrappingKeys,
      extensionKeys, finish, bind_assoc, monad_norm]
  rw [hLeft, hRight]
  refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
  refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
  calc
    _ = evalDist (bootstrappingKeys sourceSecret suffixSecret >>= fun bootstrappingKey ↦
        tapes sourceSecret suffixSecret >>= fun tape ↦
        extensionKeys sourceSecret suffixSecret >>= fun extensionKey ↦
        finish bootstrappingKey extensionKey tape) :=
      evalDist_bind_bind_swap (tapes sourceSecret suffixSecret)
        (bootstrappingKeys sourceSecret suffixSecret)
        (fun tape bootstrappingKey ↦
          extensionKeys sourceSecret suffixSecret >>= fun extensionKey ↦
          finish bootstrappingKey extensionKey tape)
    _ = _ := by
      refine evalDist_bind_congr' (bootstrappingKeys sourceSecret suffixSecret)
        fun bootstrappingKey ↦ ?_
      exact evalDist_bind_bind_swap (tapes sourceSecret suffixSecret)
        (extensionKeys sourceSecret suffixSecret)
        (fun tape extensionKey ↦ finish bootstrappingKey extensionKey tape)

/-- The direct CircLWE uniform branch is exactly the explicit real-evaluation-key/uniform-tape
game. -/
theorem uniformGame_evalDist_eq_uniformTapeGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
          (problem q degree sourceRank suffixRank tgswLevels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
          (publicContinuation (adaptiveDistinguisher decompose encode adversary))) =
      evalDist
        (uniformTapeGame q degree sourceRank suffixRank tgswLevels queryCount
          bootstrapErrorSampler extensionErrorSampler gadget decompose encode adversary) := by
  let sourceSecrets := Native.sampleRingSecret sourceRank degree
  let suffixes := Native.sampleRingSecret suffixRank degree
  let bootstrappingKeys := fun
      (sourceSecret : RingBinarySecret sourceRank degree)
      (suffixSecret : RingBinarySecret suffixRank degree) ↦
    generateSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler gadget sourceSecret suffixSecret
  let extensionKeys := fun
      (sourceSecret : RingBinarySecret sourceRank degree)
      (suffixSecret : RingBinarySecret suffixRank degree) ↦
    generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
      extensionErrorSampler gadget sourceSecret suffixSecret
  let tapes : ProbComp (Challenge q degree sourceRank suffixRank queryCount) :=
    $ᵗ (Challenge q degree sourceRank suffixRank queryCount)
  let finish := fun
      (bootstrappingKey : SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
      (extensionKey : RingExtensionKey q degree sourceRank suffixRank tgswLevels)
      (tape : Challenge q degree sourceRank suffixRank queryCount) ↦
    adaptiveDistinguisher decompose encode adversary tape
      (bootstrappingKey, extensionKey)
  have hLeft : evalDist
      (FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
        (problem q degree sourceRank suffixRank tgswLevels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
        (publicContinuation (adaptiveDistinguisher decompose encode adversary))) =
      evalDist (sourceSecrets >>= fun sourceSecret ↦
        suffixes >>= fun suffixSecret ↦
        tapes >>= fun tape ↦
        bootstrappingKeys sourceSecret suffixSecret >>= fun bootstrappingKey ↦
        extensionKeys sourceSecret suffixSecret >>= fun extensionKey ↦
        finish bootstrappingKey extensionKey tape) := by
    simp [FormalProof4FHE.LWE.AuxiliaryInput.uniformGame, publicContinuation, problem,
      sampleNestedSecret, sourceSecrets, suffixes, tapes, bootstrappingKeys,
      extensionKeys, finish, bind_assoc, monad_norm]
  have hRight : evalDist
      (uniformTapeGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler gadget decompose encode adversary) =
      evalDist (sourceSecrets >>= fun sourceSecret ↦
        suffixes >>= fun suffixSecret ↦
        bootstrappingKeys sourceSecret suffixSecret >>= fun bootstrappingKey ↦
        extensionKeys sourceSecret suffixSecret >>= fun extensionKey ↦
        tapes >>= fun tape ↦ finish bootstrappingKey extensionKey tape) := by
    simp [uniformTapeGame, sourceSecrets, suffixes, tapes, bootstrappingKeys,
      extensionKeys, finish]
  rw [hLeft, hRight]
  refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
  refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
  calc
    _ = evalDist (bootstrappingKeys sourceSecret suffixSecret >>= fun bootstrappingKey ↦
        tapes >>= fun tape ↦
        extensionKeys sourceSecret suffixSecret >>= fun extensionKey ↦
        finish bootstrappingKey extensionKey tape) :=
      evalDist_bind_bind_swap tapes (bootstrappingKeys sourceSecret suffixSecret)
        (fun tape bootstrappingKey ↦
          extensionKeys sourceSecret suffixSecret >>= fun extensionKey ↦
          finish bootstrappingKey extensionKey tape)
    _ = _ := by
      refine evalDist_bind_congr' (bootstrappingKeys sourceSecret suffixSecret)
        fun bootstrappingKey ↦ ?_
      exact evalDist_bind_bind_swap tapes (extensionKeys sourceSecret suffixSecret)
        (fun tape extensionKey ↦ finish bootstrappingKey extensionKey tape)

/-- A query-bounded adversary succeeds with probability exactly one half in the uniform-tape
branch, even though the complete real circular evaluation key is retained. -/
theorem uniformTapeGame_probOutput_true
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    Pr[= true |
      uniformTapeGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler gadget decompose encode adversary] =
      1 / 2 := by
  unfold uniformTapeGame
  rw [probOutput_bind_of_const
    (r := (1 / 2 : ENNReal)) (Native.sampleRingSecret sourceRank degree)]
  · simp
  · intro sourceSecret _
    rw [probOutput_bind_of_const
      (r := (1 / 2 : ENNReal)) (Native.sampleRingSecret suffixRank degree)]
    · simp
    · intro suffixSecret _
      rw [probOutput_bind_of_const
        (r := (1 / 2 : ENNReal))
        (generateSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler gadget sourceSecret suffixSecret)]
      · simp
      · intro sourceBootstrappingKey _
        rw [probOutput_bind_of_const
          (r := (1 / 2 : ENNReal))
          (generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
            extensionErrorSampler gadget sourceSecret suffixSecret)]
        · simp
        · intro ringExtensionKey _
          let cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels :=
            ⟨deriveBootstrappingKey q degree sourceRank suffixRank tgswLevels decompose
              sourceBootstrappingKey ringExtensionKey⟩
          let tapes : ProbComp (Challenge q degree sourceRank suffixRank queryCount) :=
            $ᵗ (Challenge q degree sourceRank suffixRank queryCount)
          let finish := fun (tape : Challenge q degree sourceRank suffixRank queryCount)
              (bit : Bool) ↦ do
            let guess ← runFromTranscript bit encode adversary cloudKey tape
            return bit == guess
          rw [show Pr[= true | tapes >>= fun tape ↦
                adaptiveDistinguisher decompose encode adversary tape
                  (sourceBootstrappingKey, ringExtensionKey)] =
              Pr[= true | tapes >>= fun tape ↦
                ($ᵗ Bool) >>= fun bit ↦ finish tape bit] by
            simp [adaptiveDistinguisher, cloudKey, tapes, finish]]
          rw [probOutput_bind_bind_swap]
          simpa [tapes, finish, cloudKey] using
            (uniformTranscript_adaptive_probOutput_true queryCount encode adversary
              cloudKey (hbound cloudKey))

/-- **Exact direct circular-security theorem.**  A query-bounded adaptive TFHE adversary's
absolute honest IND advantage is exactly its public real-evaluation-key/real-tape versus
real-evaluation-key/uniform-tape CircLWE advantage. -/
theorem abs_signedAdvantage_realAdaptive_eq_circularLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary)| =
      circularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary := by
  unfold circularLweAdvantage publicAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
    ProbComp.boolDistAdvantage Encryption.signedAdvantage
  rw [evalDist_ext_iff.mp
      (realGame_evalDist_eq_realAdaptiveGame q degree sourceRank suffixRank tgswLevels
        queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
        decompose encode adversary) true,
    evalDist_ext_iff.mp
      (uniformGame_evalDist_eq_uniformTapeGame q degree sourceRank suffixRank tgswLevels
        queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
        decompose encode adversary) true,
    uniformTapeGame_probOutput_true q degree sourceRank suffixRank tgswLevels queryCount
      bootstrapErrorSampler extensionErrorSampler gadget decompose encode adversary hbound]
  norm_num

/-! ## Exact associated search problem -/

/-- A public solver receives the target-key tape and real circular evaluation material, but not
either nested secret. -/
abbrev Solver (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver
    (Secret sourceRank suffixRank degree)
    (Challenge q degree sourceRank suffixRank queryCount)
    (Auxiliary q degree sourceRank suffixRank tgswLevels)

/-- Exact nested-key recovery problem associated with the direct FHE CircLWE view. -/
def searchProblem
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) :=
  FormalProof4FHE.LWE.AuxiliaryInput.Search.exactRecoveryProblem
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)

/-- Exact recovery is bounded by direct CircLWE decision advantage plus recovery when the target
tape is uniform but the real circular evaluation key is retained. -/
theorem searchSuccess_le_circularLwe_add_uniformRecovery
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (solver : Solver q degree sourceRank suffixRank tgswLevels queryCount) :
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (searchProblem q degree sourceRank suffixRank tgswLevels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
        solver ≤
      ENNReal.ofReal
          (FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
            (problem q degree sourceRank suffixRank tgswLevels queryCount
              bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
            (FormalProof4FHE.LWE.AuxiliaryInput.Search.recoveryContinuation solver)) +
        Pr[= true |
          FormalProof4FHE.LWE.AuxiliaryInput.Search.uniformRecoveryGame
            (problem q degree sourceRank suffixRank tgswLevels queryCount
              bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
            solver] := by
  exact
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability_exactRecovery_le_circularLwe_add_uniform
      (problem q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
      solver

/-! ## PKC-style search-to-decision boundary -/

/-- A concrete decision-to-search certificate for the same direct FHE CircLWE distribution. -/
abbrev DecisionToSearchReduction
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) :=
  FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.Reduction
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)

/-- Once a same-distribution PKC-style decision-to-search certificate is supplied, adaptive TFHE
advantage is bounded by exact nested-key recovery plus the certificate's explicit loss. -/
theorem abs_signedAdvantage_realAdaptive_le_search_add_reductionLoss
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount)
    (reduction : DecisionToSearchReduction q degree sourceRank suffixRank tgswLevels
      queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary)| ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (searchProblem q degree sourceRank suffixRank tgswLevels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
        (reduction.toSolver (adaptiveDistinguisher decompose encode adversary))).toReal +
      reduction.loss (adaptiveDistinguisher decompose encode adversary) := by
  rw [abs_signedAdvantage_realAdaptive_eq_circularLwe q degree sourceRank suffixRank
    tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler
    gadget decompose encode adversary hbound]
  simpa [circularLweAdvantage, searchProblem] using
    (reduction.advantage_le (adaptiveDistinguisher decompose encode adversary))

/-- Cross-distribution certificate used when shifted evaluation widens the BRK, extension, or
input-tape noise before invoking the decision distinguisher. -/
abbrev CrossDecisionToSearchReduction
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionBootstrapErrorSampler decisionExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree))
    (decisionInputErrorSampler : ProbComp (ZMod q))
    (searchBootstrapErrorSampler searchExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree))
    (searchInputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) :=
  FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.CrossReduction
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      decisionBootstrapErrorSampler decisionExtensionErrorSampler
      decisionInputErrorSampler gadget)
    (searchProblem q degree sourceRank suffixRank tgswLevels queryCount
      searchBootstrapErrorSampler searchExtensionErrorSampler searchInputErrorSampler gadget)

/-- **Paper-aligned widened-decision theorem.**  A cross-distribution shifted-evaluation and
guess-and-check certificate reduces adaptive TFHE security at the decision noise parameters to
exact recovery in the narrow search distribution, paying its stated loss once. -/
theorem abs_signedAdvantage_realAdaptive_le_narrowSearch_add_reductionLoss
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionBootstrapErrorSampler decisionExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree))
    (decisionInputErrorSampler : ProbComp (ZMod q))
    (searchBootstrapErrorSampler searchExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree))
    (searchInputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount)
    (reduction : CrossDecisionToSearchReduction q degree sourceRank suffixRank tgswLevels
      queryCount decisionBootstrapErrorSampler decisionExtensionErrorSampler
      decisionInputErrorSampler searchBootstrapErrorSampler searchExtensionErrorSampler
      searchInputErrorSampler gadget) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        decisionBootstrapErrorSampler decisionExtensionErrorSampler
        decisionInputErrorSampler gadget decompose encode adversary)| ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (searchProblem q degree sourceRank suffixRank tgswLevels queryCount
          searchBootstrapErrorSampler searchExtensionErrorSampler searchInputErrorSampler
          gadget)
        (reduction.toSolver (adaptiveDistinguisher decompose encode adversary))).toReal +
      reduction.loss (adaptiveDistinguisher decompose encode adversary) := by
  rw [abs_signedAdvantage_realAdaptive_eq_circularLwe q degree sourceRank suffixRank
    tgswLevels queryCount decisionBootstrapErrorSampler decisionExtensionErrorSampler
    decisionInputErrorSampler gadget decompose encode adversary hbound]
  simpa [circularLweAdvantage] using
    (reduction.advantage_le (adaptiveDistinguisher decompose encode adversary))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
