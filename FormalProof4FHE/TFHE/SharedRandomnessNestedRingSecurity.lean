/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveEncryptionSecurity
import FormalProof4FHE.TFHE.SharedRandomnessBootstrappingKeyExtension
import FormalProof4FHE.TFHE.SharedRandomnessOneCycle

set_option autoImplicit false

/-!
# Security Games for Nested-Ring Shared-Randomness TFHE

This module integrates the source-to-target BRK conversion with an actual TFHE cloud-key and
adaptive encryption game.  Two independently sampled ring-key blocks form

`targetRingSecret = sourceRingSecret || suffixRingSecret`.

The scalar encryption key is `keyExtract sourceRingSecret`.  Key generation first creates the
one-circular source BRK

`BRK(keyExtract sourceRingSecret, sourceRingSecret)`,

then uses the ring-valued suffix KSK from
`SharedRandomnessBootstrappingKeyExtension` to derive

`BRK(keyExtract sourceRingSecret, targetRingSecret)`.

The cloud key also contains the ordinary scalar suffix-only KSK: it encrypts
`keyExtract suffixRingSecret` under `keyExtract sourceRingSecret`.  This is the table needed after
sample extraction when the already-shared source coordinates are retained rather than switched.
The ring-valued extension KSK is key-generation material and is not retained in the final cloud
key.

The central theorem identifies the complete derived-BRK replacement game exactly with a
one-circular source-BRK game whose continuation performs the public conversion and generates the
scalar suffix KSK.  The adaptive encryption theorem then bounds the honest derived-key game by
that single source one-circular term plus the BRK-zero endpoint.  Thus this module removes the
earlier heterogeneous two-key circular *definition* from this shared-randomness variant; it does
not yet derive the remaining source one-circular term or the BRK-zero endpoint from ordinary
RLWE/LWE.
-/

open Matrix OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessNestedRing

noncomputable section

/-- The scalar TLWE key is the coefficient extraction of the complete source ring-key block. -/
abbrev scalarDimension (sourceRank degree : ℕ) := sourceRank * degree

/-- Number of independent target-ring coefficients not shared with the scalar key. -/
abbrev suffixDimension (suffixRank degree : ℕ) := suffixRank * degree

/-- Source one-circular BRK before changing its ring encryption key. -/
abbrev SourceBootstrappingKey
    (q degree sourceRank tgswLevels : ℕ) :=
  Native.BootstrappingKey q degree sourceRank tgswLevels
    (scalarDimension sourceRank degree)

/-- Derived BRK under the appended target ring key, with the source message vector unchanged. -/
abbrev DerivedBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Native.BootstrappingKey q degree (sourceRank + suffixRank) tgswLevels
    (scalarDimension sourceRank degree)

/-- Ring-valued key-generation material used to add the target TGSW suffix gadget blocks. -/
abbrev RingExtensionKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.RingKeySwitchKey
    q degree sourceRank suffixRank tgswLevels

/-- Scalar suffix-only KSK used after extracting a TLWE row from the target ring ciphertext. -/
abbrev ScalarKeySwitchKey
    (q degree sourceRank suffixRank keySwitchLevels : ℕ) :=
  Native.KeySwitchKey q (scalarDimension sourceRank degree)
    (suffixDimension suffixRank degree) keySwitchLevels

/-- Public evaluation key for the nested-ring construction.  The ring extension key has already
been consumed while deriving `bootstrappingKey` and need not be published. -/
structure CloudKey
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) where
  bootstrappingKey :
    DerivedBootstrappingKey q degree sourceRank suffixRank tgswLevels
  keySwitchKey :
    ScalarKeySwitchKey q degree sourceRank suffixRank keySwitchLevels

/-- The scalar secret shared with the source portion of the target ring key. -/
def scalarSecret {sourceRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree) :
    BinarySecret (scalarDimension sourceRank degree) :=
  keyExtract sourceSecret

/-- The independent coefficient block encrypted by the scalar suffix-only KSK. -/
def extractedSuffixSecret {suffixRank degree : ℕ}
    (suffixSecret : RingBinarySecret suffixRank degree) :
    BinarySecret (suffixDimension suffixRank degree) :=
  keyExtract suffixSecret

/-- Every extracted source coefficient occurs unchanged in the corresponding prefix component of
the appended target ring key.  This is the precise subset relation used by the construction. -/
@[simp]
theorem keyExtract_appendRingSecret_source
    {sourceRank suffixRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree)
    (component : Fin sourceRank) (coefficient : Fin degree) :
    keyExtract
        (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret
          sourceSecret suffixSecret)
        (finProdFinEquiv (Fin.castAdd suffixRank component, coefficient)) =
      scalarSecret sourceSecret (finProdFinEquiv (component, coefficient)) := by
  simp [scalarSecret,
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret]

/-- The remaining target coefficients are exactly the independently sampled suffix block. -/
@[simp]
theorem keyExtract_appendRingSecret_suffix
    {sourceRank suffixRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree)
    (component : Fin suffixRank) (coefficient : Fin degree) :
    keyExtract
        (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret
          sourceSecret suffixSecret)
        (finProdFinEquiv (Fin.natAdd sourceRank component, coefficient)) =
      extractedSuffixSecret suffixSecret
        (finProdFinEquiv (component, coefficient)) := by
  simp [extractedSuffixSecret,
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret]

/-- Generate the ordinary scalar suffix-only KSK under the shared source scalar key. -/
def generateScalarKeySwitchKey
    (q degree sourceRank suffixRank keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (ScalarKeySwitchKey q degree sourceRank suffixRank keySwitchLevels) :=
  Native.generateKeySwitchKey q (scalarDimension sourceRank degree)
    (suffixDimension suffixRank degree) keySwitchLevels errorSampler gadget
    (extractedSuffixSecret suffixSecret) (scalarSecret sourceSecret)

/-- Zero-message scalar suffix KSK with the same source encryption key. -/
def generateZeroScalarKeySwitchKey
    (q degree sourceRank suffixRank keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (sourceSecret : RingBinarySecret sourceRank degree) :
    ProbComp (ScalarKeySwitchKey q degree sourceRank suffixRank keySwitchLevels) :=
  Native.generateZeroKeySwitchKey q (scalarDimension sourceRank degree)
    (suffixDimension suffixRank degree) keySwitchLevels errorSampler
    (scalarSecret sourceSecret)

/-- Source BRK carrying precisely the shared scalar message vector.  This is a one-circular
object because its encryption key is `sourceSecret` itself. -/
def generateSourceBootstrappingKey
    (q degree sourceRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree) :
    ProbComp (SourceBootstrappingKey q degree sourceRank tgswLevels) :=
  FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.generateSourceCircularBootstrappingKey
    q degree sourceRank tgswLevels errorSampler gadget sourceSecret

/-- Format-identical zero-message source BRK. -/
def generateZeroSourceBootstrappingKey
    (q degree sourceRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree) :
    ProbComp (SourceBootstrappingKey q degree sourceRank tgswLevels) :=
  Native.generateZeroBootstrappingKey q degree sourceRank tgswLevels
    (scalarDimension sourceRank degree) errorSampler gadget sourceSecret

/-- Generate ring-valued suffix rows used only by the BRK conversion. -/
def generateRingExtensionKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (RingExtensionKey q degree sourceRank suffixRank tgswLevels) :=
  FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.generateRingKeySwitchKey
    q degree sourceRank suffixRank tgswLevels errorSampler gadget sourceSecret suffixSecret

/-- Deterministically complete every source BRK entry to the target ring-key layout. -/
def deriveBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (sourceBootstrappingKey :
      SourceBootstrappingKey q degree sourceRank tgswLevels)
    (ringExtensionKey :
      RingExtensionKey q degree sourceRank suffixRank tgswLevels) :
    DerivedBootstrappingKey q degree sourceRank suffixRank tgswLevels :=
  FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.deriveTargetBootstrappingKey
    q degree sourceRank suffixRank tgswLevels (scalarDimension sourceRank degree)
      decompose sourceBootstrappingKey ringExtensionKey

/-- Generate a real cloud key for fixed nested ring secrets. -/
def generateCloudKey
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp
      (CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels) := do
  let sourceBootstrappingKey ← generateSourceBootstrappingKey q degree sourceRank tgswLevels
    bootstrapErrorSampler tgswGadget sourceSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
    extensionErrorSampler tgswGadget sourceSecret suffixSecret
  let scalarKeySwitchKey ← generateScalarKeySwitchKey q degree sourceRank suffixRank
    keySwitchLevels scalarKeySwitchErrorSampler scalarKeySwitchGadget sourceSecret suffixSecret
  return ⟨deriveBootstrappingKey q degree sourceRank suffixRank tgswLevels decompose
      sourceBootstrappingKey ringExtensionKey,
    scalarKeySwitchKey⟩

/-- BRK-zero cloud-key hybrid.  The public conversion and real scalar suffix KSK are unchanged. -/
def generateBootstrapZeroCloudKey
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp
      (CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels) := do
  let sourceBootstrappingKey ←
    generateZeroSourceBootstrappingKey q degree sourceRank tgswLevels
      bootstrapErrorSampler tgswGadget sourceSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
    extensionErrorSampler tgswGadget sourceSecret suffixSecret
  let scalarKeySwitchKey ← generateScalarKeySwitchKey q degree sourceRank suffixRank
    keySwitchLevels scalarKeySwitchErrorSampler scalarKeySwitchGadget sourceSecret suffixSecret
  return ⟨deriveBootstrappingKey q degree sourceRank suffixRank tgswLevels decompose
      sourceBootstrappingKey ringExtensionKey,
    scalarKeySwitchKey⟩

/-! ## Secret-dependent circular games -/

/-- A later encryption/evaluation experiment receives the hidden nested secrets internally and
the final derived public cloud key. -/
abbrev Continuation
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ)
    (Output : Type) :=
  RingBinarySecret sourceRank degree →
    RingBinarySecret suffixRank degree →
      CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels → ProbComp Output

/-- Honest derived-cloud-key game followed by an arbitrary secret-dependent continuation. -/
def realContinuationGame
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels
      keySwitchLevels Output) : ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let cloudKey ← generateCloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels
    bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler tgswGadget
    scalarKeySwitchGadget decompose sourceSecret suffixSecret
  continuation sourceSecret suffixSecret cloudKey

/-- Zero-source-message BRK hybrid with the same secrets and auxiliary keys. -/
def bootstrapZeroContinuationGame
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels
      keySwitchLevels Output) : ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let cloudKey ← generateBootstrapZeroCloudKey q degree sourceRank suffixRank tgswLevels
    keySwitchLevels bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler
    tgswGadget scalarKeySwitchGadget decompose sourceSecret suffixSecret
  continuation sourceSecret suffixSecret cloudKey

/-- A continuation at the exact source one-circular boundary, before public BRK conversion. -/
abbrev SourceContinuation
    (q degree sourceRank suffixRank tgswLevels : ℕ) (Output : Type) :=
  RingBinarySecret sourceRank degree →
    RingBinarySecret suffixRank degree →
      SourceBootstrappingKey q degree sourceRank tgswLevels →
        RingExtensionKey q degree sourceRank suffixRank tgswLevels → ProbComp Output

/-- Compile any target-cloud-key continuation into the one-circular source-BRK experiment. -/
def compileSourceContinuation
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels
      keySwitchLevels Output) :
    SourceContinuation q degree sourceRank suffixRank tgswLevels Output :=
  fun sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey ↦ do
    let scalarKeySwitchKey ← generateScalarKeySwitchKey q degree sourceRank suffixRank
      keySwitchLevels scalarKeySwitchErrorSampler scalarKeySwitchGadget
      sourceSecret suffixSecret
    continuation sourceSecret suffixSecret
      ⟨deriveBootstrappingKey q degree sourceRank suffixRank tgswLevels decompose
          sourceBootstrappingKey ringExtensionKey,
        scalarKeySwitchKey⟩

/-- Real source one-circular BRK with the ring extension key retained for the continuation. -/
def realSourceContinuationGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ←
    generateSourceBootstrappingKey q degree sourceRank tgswLevels
      bootstrapErrorSampler tgswGadget sourceSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
    extensionErrorSampler tgswGadget sourceSecret suffixSecret
  continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey

/-- Zero-message source BRK comparison with identical extension-key auxiliary input. -/
def bootstrapZeroSourceContinuationGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ←
    generateZeroSourceBootstrappingKey q degree sourceRank tgswLevels
      bootstrapErrorSampler tgswGadget sourceSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
    extensionErrorSampler tgswGadget sourceSecret suffixSecret
  continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey

/-- Exact source one-circular distinguishing advantage for an arbitrary later continuation. -/
def sourceContinuationAdvantage
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) : ℝ :=
  (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler tgswGadget continuation).boolDistAdvantage
    (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler tgswGadget continuation)

/-- Real derived-key execution is exactly the compiled source one-circular execution. -/
theorem realContinuationGame_eq_source
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels
      keySwitchLevels Output) :
    realContinuationGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
        bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler tgswGadget
        scalarKeySwitchGadget decompose continuation =
      realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler tgswGadget
        (compileSourceContinuation q degree sourceRank suffixRank tgswLevels keySwitchLevels
          scalarKeySwitchErrorSampler scalarKeySwitchGadget decompose continuation) := by
  simp [realContinuationGame, realSourceContinuationGame, generateCloudKey,
    compileSourceContinuation, bind_assoc, monad_norm]

/-- The zero-message derived execution is exactly the compiled source comparison execution. -/
theorem bootstrapZeroContinuationGame_eq_source
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels
      keySwitchLevels Output) :
    bootstrapZeroContinuationGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
        bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler tgswGadget
        scalarKeySwitchGadget decompose continuation =
      bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler tgswGadget
        (compileSourceContinuation q degree sourceRank suffixRank tgswLevels keySwitchLevels
          scalarKeySwitchErrorSampler scalarKeySwitchGadget decompose continuation) := by
  simp [bootstrapZeroContinuationGame, bootstrapZeroSourceContinuationGame,
    generateBootstrapZeroCloudKey, compileSourceContinuation, bind_assoc, monad_norm]

/-- Exact target replacement distance equals one source one-circular distance. -/
theorem tvDist_continuation_eq_sourceOneCircular
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels
      keySwitchLevels Output) :
    tvDist
        (realContinuationGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
          bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler tgswGadget
          scalarKeySwitchGadget decompose continuation)
        (bootstrapZeroContinuationGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
          bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler tgswGadget
          scalarKeySwitchGadget decompose continuation) =
      tvDist
        (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler tgswGadget
          (compileSourceContinuation q degree sourceRank suffixRank tgswLevels keySwitchLevels
            scalarKeySwitchErrorSampler scalarKeySwitchGadget decompose continuation))
        (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler tgswGadget
          (compileSourceContinuation q degree sourceRank suffixRank tgswLevels keySwitchLevels
            scalarKeySwitchErrorSampler scalarKeySwitchGadget decompose continuation)) := by
  rw [realContinuationGame_eq_source, bootstrapZeroContinuationGame_eq_source]

/-! ## Exact and quantitative source one-circular endpoints -/

/-- Uniform source-BRK row errors erase the source-secret message vector exactly for every fixed
source key. -/
theorem generateSourceBootstrappingKey_uniformError_evalDist_eq_zero
    (q degree sourceRank tgswLevels : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree) :
    evalDist
        (generateSourceBootstrappingKey q degree sourceRank tgswLevels
          ($ᵗ (RLWE.Rq q degree)) gadget sourceSecret) =
      evalDist
        (generateZeroSourceBootstrappingKey q degree sourceRank tgswLevels
          ($ᵗ (RLWE.Rq q degree)) gadget sourceSecret) := by
  let rqCommRing : CommRing (RLWE.Rq q degree) :=
    LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree
  letI := rqCommRing
  unfold generateSourceBootstrappingKey
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.generateSourceCircularBootstrappingKey
    generateZeroSourceBootstrappingKey Native.generateBootstrappingKey
    Native.generateZeroBootstrappingKey
  apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
  intro coordinate
  let zeroMessage : RLWE.Rq q degree :=
    @OfNat.ofNat (RLWE.Rq q degree) 0
      (@Zero.toOfNat0 (RLWE.Rq q degree)
        (@MulZeroClass.toZero (RLWE.Rq q degree)
          (@instMulZeroClassOfSemiring (RLWE.Rq q degree) rqCommRing.toSemiring)))
  calc
    _ = evalDist ($ᵗ (TGSW.Ciphertext (RLWE.Rq q degree) sourceRank tgswLevels)) :=
      SharedRandomnessOneCycle.tgswEncrypt_uniformError_evalDist sourceRank tgswLevels
        (embedRingSecret q sourceSecret) gadget
        (embedConstantBit q degree (keyExtract sourceSecret coordinate))
    _ = _ := by
      change evalDist ($ᵗ (TGSW.Ciphertext (RLWE.Rq q degree) sourceRank tgswLevels)) =
        evalDist (TGSW.encrypt sourceRank tgswLevels ($ᵗ (RLWE.Rq q degree))
          (embedRingSecret q sourceSecret) gadget zeroMessage)
      exact
        (SharedRandomnessOneCycle.tgswEncrypt_uniformError_evalDist sourceRank tgswLevels
          (embedRingSecret q sourceSecret) gadget zeroMessage).symm

/-- The one-circular source games have identical output laws under uniform source-BRK errors,
even though the continuation receives both hidden secrets and all correlated auxiliary keys. -/
theorem realSourceContinuationGame_uniformError_evalDist_eq_zero
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    evalDist
        (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler tgswGadget continuation) =
      evalDist
        (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler tgswGadget continuation) := by
  unfold realSourceContinuationGame bootstrapZeroSourceContinuationGame
  refine evalDist_bind_congr' (Native.sampleRingSecret sourceRank degree) fun sourceSecret ↦ ?_
  refine evalDist_bind_congr' (Native.sampleRingSecret suffixRank degree) fun suffixSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (generateSourceBootstrappingKey_uniformError_evalDist_eq_zero q degree sourceRank
      tgswLevels tgswGadget sourceSecret)
    (fun sourceBootstrappingKey ↦
      generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
          extensionErrorSampler tgswGadget sourceSecret suffixSecret >>= fun ringExtensionKey ↦
        continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey)

/-- Uniform source-BRK errors make the remaining contextual one-circular advantage exactly zero. -/
theorem sourceContinuationAdvantage_uniformError_eq_zero
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    sourceContinuationAdvantage q degree sourceRank suffixRank tgswLevels
      ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler tgswGadget continuation = 0 := by
  unfold sourceContinuationAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (realSourceContinuationGame_uniformError_evalDist_eq_zero q degree sourceRank
      suffixRank tgswLevels extensionErrorSampler tgswGadget continuation) true]
  simp

/-- Replacing the source-BRK row-error sampler in the real contextual game costs exactly the
complete source BRK row count times the one-draw distance. -/
theorem tvDist_realSourceContinuationGame_error_le
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (left right extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    tvDist
        (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          left extensionErrorSampler tgswGadget continuation)
        (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          right extensionErrorSampler tgswGadget continuation) ≤
      (SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
          (scalarDimension sourceRank degree) : ℝ) * tvDist left right := by
  unfold realSourceContinuationGame
  exact tvDist_bind_left_le_const' (m := ProbComp)
    (Native.sampleRingSecret sourceRank degree) _ _
    ((SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
      (scalarDimension sourceRank degree) : ℝ) * tvDist left right)
    (fun sourceSecret ↦
      tvDist_bind_left_le_const' (m := ProbComp)
        (Native.sampleRingSecret suffixRank degree) _ _
        ((SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
          (scalarDimension sourceRank degree) : ℝ) * tvDist left right)
        (fun suffixSecret ↦ by
          let finish := fun sourceBootstrappingKey ↦
            generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
                extensionErrorSampler tgswGadget sourceSecret suffixSecret >>=
              fun ringExtensionKey ↦
                continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey
          change tvDist
              (generateSourceBootstrappingKey q degree sourceRank tgswLevels
                left tgswGadget sourceSecret >>= finish)
              (generateSourceBootstrappingKey q degree sourceRank tgswLevels
                right tgswGadget sourceSecret >>= finish) ≤ _
          exact (tvDist_bind_right_le finish _ _).trans
            (SamplerReplacement.tvDist_generateBootstrappingKey_le q degree sourceRank
              tgswLevels (scalarDimension sourceRank degree) left right tgswGadget
              (scalarSecret sourceSecret) sourceSecret)))

/-- The same source-BRK sampler-replacement bound for the zero-message comparison game. -/
theorem tvDist_bootstrapZeroSourceContinuationGame_error_le
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (left right extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    tvDist
        (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          left extensionErrorSampler tgswGadget continuation)
        (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          right extensionErrorSampler tgswGadget continuation) ≤
      (SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
          (scalarDimension sourceRank degree) : ℝ) * tvDist left right := by
  unfold bootstrapZeroSourceContinuationGame
  exact tvDist_bind_left_le_const' (m := ProbComp)
    (Native.sampleRingSecret sourceRank degree) _ _
    ((SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
      (scalarDimension sourceRank degree) : ℝ) * tvDist left right)
    (fun sourceSecret ↦
      tvDist_bind_left_le_const' (m := ProbComp)
        (Native.sampleRingSecret suffixRank degree) _ _
        ((SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
          (scalarDimension sourceRank degree) : ℝ) * tvDist left right)
        (fun suffixSecret ↦ by
          let finish := fun sourceBootstrappingKey ↦
            generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
                extensionErrorSampler tgswGadget sourceSecret suffixSecret >>=
              fun ringExtensionKey ↦
                continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey
          change tvDist
              (generateZeroSourceBootstrappingKey q degree sourceRank tgswLevels
                left tgswGadget sourceSecret >>= finish)
              (generateZeroSourceBootstrappingKey q degree sourceRank tgswLevels
                right tgswGadget sourceSecret >>= finish) ≤ _
          exact (tvDist_bind_right_le finish _ _).trans
            (SamplerReplacement.tvDist_generateZeroBootstrappingKey_le q degree sourceRank
              tgswLevels (scalarDimension sourceRank degree) left right tgswGadget
              sourceSecret)))

/-- Quantitative security-only source one-circular theorem.  It is useful for an exact uniform
endpoint or a separately certified near-uniform error family; narrow TFHE noise normally makes
this statistical bound large. -/
theorem sourceContinuationAdvantage_le_uniformError
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    sourceContinuationAdvantage q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler tgswGadget continuation ≤
      2 * (SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
        (scalarDimension sourceRank degree) : ℝ) *
          tvDist bootstrapErrorSampler ($ᵗ (RLWE.Rq q degree)) := by
  let uniformError : ProbComp (RLWE.Rq q degree) := $ᵗ (RLWE.Rq q degree)
  let realActual := realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler tgswGadget continuation
  let realUniform := realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
    uniformError extensionErrorSampler tgswGadget continuation
  let zeroActual := bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler tgswGadget continuation
  let zeroUniform := bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
    uniformError extensionErrorSampler tgswGadget continuation
  let replacementBound :=
    (SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
      (scalarDimension sourceRank degree) : ℝ) *
        tvDist bootstrapErrorSampler uniformError
  have hReal : tvDist realActual realUniform ≤ replacementBound := by
    exact tvDist_realSourceContinuationGame_error_le q degree sourceRank suffixRank
      tgswLevels bootstrapErrorSampler uniformError extensionErrorSampler tgswGadget continuation
  have hZero : tvDist zeroActual zeroUniform ≤ replacementBound := by
    exact tvDist_bootstrapZeroSourceContinuationGame_error_le q degree sourceRank suffixRank
      tgswLevels bootstrapErrorSampler uniformError extensionErrorSampler tgswGadget continuation
  have hUniform : evalDist realUniform = evalDist zeroUniform := by
    exact realSourceContinuationGame_uniformError_evalDist_eq_zero q degree sourceRank
      suffixRank tgswLevels extensionErrorSampler tgswGadget continuation
  have hUniformToActual : tvDist realUniform zeroActual = tvDist zeroUniform zeroActual := by
    unfold tvDist
    rw [hUniform]
  calc
    sourceContinuationAdvantage q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler tgswGadget continuation ≤
        tvDist realActual zeroActual := by
      unfold sourceContinuationAdvantage realActual zeroActual
      exact abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist realActual realUniform + tvDist realUniform zeroActual :=
      tvDist_triangle _ _ _
    _ = tvDist realActual realUniform + tvDist zeroUniform zeroActual := by
      rw [hUniformToActual]
    _ ≤ replacementBound + replacementBound := by
      exact add_le_add hReal (by simpa [tvDist_comm] using hZero)
    _ = 2 * (SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
          (scalarDimension sourceRank degree) : ℝ) *
        tvDist bootstrapErrorSampler ($ᵗ (RLWE.Rq q degree)) := by
      simp [replacementBound, uniformError]
      ring

/-! ## Adaptive TFHE encryption security -/

/-- Adaptive adversary for the final nested-ring cloud-key format. -/
abbrev AdaptiveAdversary
    (Message : Type)
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) :=
  Encryption.Adaptive.Adversary Message
    (CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels)
    (TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree))

/-- Run an adaptive adversary from a fixed eager tape of scalar-LWE samples. -/
def runFromTranscript
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ}
    [NeZero q]
    (bit : Bool) (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels)
    (cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels)
    {samples : ℕ}
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q)
      (scalarDimension sourceRank degree) samples) : ProbComp Bool :=
  (simulateQ
      (GeneralizedSubspaceLWE.Adaptive.sourceImpl
        ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample
          (ZMod q) (scalarDimension sourceRank degree))).withPregen
      (simulateQ
        (Encryption.Adaptive.sourceReduction
          (lweDimension := scalarDimension sourceRank degree) bit encode)
        (adversary cloudKey))).run'
    (GeneralizedSubspaceLWE.Adaptive.sourceSampleSeed
      (GeneralizedSubspaceLWE.Adaptive.batchSamples transcript))

/-- A dummy native cloud key used only to instantiate the cloud-type-parametric uniform-tape
lemma already proved by the native adaptive security development. -/
private def dummyNativeCloudKey (q lweDimension : ℕ) :
    Encryption.NativeCloudKey q 0 0 0 lweDimension 0 :=
  ⟨fun _ ↦ (fun _ _ ↦ 0, fun _ ↦ 0),
    (fun _ _ ↦ 0, fun _ ↦ 0)⟩

/-- Regard a fixed nested cloud-key adversary as a native-cloud-key adversary that ignores its
dummy cloud-key argument.  Its oracle computation is definitionally unchanged. -/
private def asNativeAdversary
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ}
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels)
    (cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels) :
    Encryption.Adaptive.NativeAdversary Message q 0 0 0
      (scalarDimension sourceRank degree) 0 :=
  fun _ ↦ adversary cloudKey

/-- For a fixed nested cloud key, a query-bounded adversary wins with probability exactly one
half when its eager scalar transcript is uniform.  The proof reuses the native theorem through
the cloud-ignoring wrapper above; no property of either cloud-key representation is used. -/
theorem uniformTranscript_adaptive_probOutput_true
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ}
    [NeZero q]
    (queryCount : ℕ) (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels)
    (cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (Encryption.Adaptive.isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree)))
      queryCount) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let transcript ← $ᵗ (FormalProof4FHE.LWE.BatchTranscript
        (ZMod q) (scalarDimension sourceRank degree) queryCount)
      let guess ← runFromTranscript bit encode adversary cloudKey transcript
      return (bit == guess)] = 1 / 2 := by
  let nativeAdversary := asNativeAdversary adversary cloudKey
  let nativeCloudKey := dummyNativeCloudKey q (scalarDimension sourceRank degree)
  have hNativeBound : IsQueryBoundP (nativeAdversary nativeCloudKey)
      (Encryption.Adaptive.isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree)))
      queryCount := by
    simpa [nativeAdversary, asNativeAdversary] using hbound
  simpa [runFromTranscript, Encryption.Adaptive.runFromTranscript,
    nativeAdversary, asNativeAdversary] using
    (Encryption.Adaptive.uniformAdaptive_probOutput_true
      (Message := Message) (q := q) (degree := 0) (ringRank := 0)
      (tgswLevels := 0) (lweDimension := scalarDimension sourceRank degree)
      (keySwitchLevels := 0) queryCount encode nativeAdversary nativeCloudKey hNativeBound)

/-- Secret-dependent continuation implementing a query-bounded-style eager adaptive encryption
experiment.  Query boundedness is only needed later when reducing the BRK-zero endpoint to LWE. -/
def adaptiveContinuation
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ}
    [NeZero q]
    (queryCount : ℕ) (inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) :
    Continuation q degree sourceRank suffixRank tgswLevels keySwitchLevels Bool :=
  fun sourceSecret _ cloudKey ↦ do
    let tape ← TLWE.batchEncrypt (scalarDimension sourceRank degree) queryCount
      inputErrorSampler (embedBinarySecret (scalarSecret sourceSecret)) 0
    let bit ← $ᵗ Bool
    let guess ← runFromTranscript bit encode adversary cloudKey tape
    return bit == guess

/-- With a uniform input-error sampler, the fixed-secret eager tape is exactly a uniform public
transcript, and its sampling can be reordered after the independent challenge bit. -/
theorem adaptiveContinuation_uniformInput_evalDist
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ}
    [NeZero q]
    (queryCount : ℕ) (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree)
    (cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels) :
    evalDist
        (adaptiveContinuation queryCount ($ᵗ (ZMod q)) encode adversary
          sourceSecret suffixSecret cloudKey) =
      evalDist (do
        let bit ← $ᵗ Bool
        let transcript ← $ᵗ (FormalProof4FHE.LWE.BatchTranscript
          (ZMod q) (scalarDimension sourceRank degree) queryCount)
        let guess ← runFromTranscript bit encode adversary cloudKey transcript
        return bit == guess) := by
  let tapeSampler := TLWE.batchEncrypt (scalarDimension sourceRank degree) queryCount
    ($ᵗ (ZMod q)) (embedBinarySecret (scalarSecret sourceSecret)) 0
  let uniformTape : ProbComp (FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) (scalarDimension sourceRank degree) queryCount) :=
    $ᵗ (FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) (scalarDimension sourceRank degree) queryCount)
  let finish := fun
      (transcript : FormalProof4FHE.LWE.BatchTranscript
        (ZMod q) (scalarDimension sourceRank degree) queryCount)
      (bit : Bool) ↦ do
    let guess ← runFromTranscript bit encode adversary cloudKey transcript
    return bit == guess
  have htape : evalDist tapeSampler = evalDist uniformTape := by
    exact SharedRandomnessOneCycle.batchEncrypt_uniformError_evalDist
      (scalarDimension sourceRank degree) queryCount
      (embedBinarySecret (scalarSecret sourceSecret)) 0
  calc
    _ = evalDist (tapeSampler >>= fun transcript ↦
        ($ᵗ Bool) >>= fun bit ↦ finish transcript bit) := by
      simp [adaptiveContinuation, tapeSampler, finish]
    _ = evalDist (uniformTape >>= fun transcript ↦
        ($ᵗ Bool) >>= fun bit ↦ finish transcript bit) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq htape
        (fun transcript ↦ ($ᵗ Bool) >>= fun bit ↦ finish transcript bit)
    _ = evalDist (($ᵗ Bool) >>= fun bit ↦
        uniformTape >>= fun transcript ↦ finish transcript bit) :=
      evalDist_bind_bind_swap uniformTape ($ᵗ Bool) finish
    _ = _ := by
      simp [uniformTape, finish]

/-- Honest adaptive encryption game using the derived target-ring BRK. -/
def realAdaptiveGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) : ProbComp Bool :=
  realContinuationGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
    bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler tgswGadget
    scalarKeySwitchGadget decompose
    (adaptiveContinuation queryCount inputErrorSampler encode adversary)

/-- Adaptive comparison game after replacing the one-circular source BRK messages by zero. -/
def bootstrapZeroAdaptiveGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) : ProbComp Bool :=
  bootstrapZeroContinuationGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
    bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler tgswGadget
    scalarKeySwitchGadget decompose
    (adaptiveContinuation queryCount inputErrorSampler encode adversary)

/-- Uniform fresh input errors make the BRK-zero adaptive game perfectly fair for every publicly
query-bounded adversary, independently of all cloud-key correlations. -/
theorem bootstrapZeroAdaptiveGame_uniformInput_probOutput_true
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    Pr[= true |
      bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
        queryCount bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler
        ($ᵗ (ZMod q)) tgswGadget scalarKeySwitchGadget decompose encode adversary] =
      1 / 2 := by
  unfold bootstrapZeroAdaptiveGame bootstrapZeroContinuationGame
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
        (generateBootstrapZeroCloudKey q degree sourceRank suffixRank tgswLevels
          keySwitchLevels bootstrapErrorSampler extensionErrorSampler
          scalarKeySwitchErrorSampler tgswGadget scalarKeySwitchGadget decompose
          sourceSecret suffixSecret)]
      · simp
      · intro cloudKey _
        rw [evalDist_ext_iff.mp
          (adaptiveContinuation_uniformInput_evalDist queryCount encode adversary
            sourceSecret suffixSecret cloudKey) true]
        exact uniformTranscript_adaptive_probOutput_true queryCount encode adversary cloudKey
          (hbound cloudKey)

/-- The exact remaining source one-circular term for the complete adaptive continuation. -/
def sourceOneCircularAdaptiveAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) : ℝ :=
  let sourceContinuation :=
    compileSourceContinuation q degree sourceRank suffixRank tgswLevels keySwitchLevels
      scalarKeySwitchErrorSampler scalarKeySwitchGadget decompose
      (adaptiveContinuation queryCount inputErrorSampler encode adversary)
  sourceContinuationAdvantage q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler tgswGadget sourceContinuation

/-- The complete adaptive source one-circular term inherits the generic near-uniform endpoint. -/
theorem sourceOneCircularAdaptiveAdvantage_le_uniformError
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) :
    sourceOneCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
        keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
        scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
        decompose encode adversary ≤
      2 * (SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
        (scalarDimension sourceRank degree) : ℝ) *
          tvDist bootstrapErrorSampler ($ᵗ (RLWE.Rq q degree)) := by
  unfold sourceOneCircularAdaptiveAdvantage
  exact sourceContinuationAdvantage_le_uniformError q degree sourceRank suffixRank
    tgswLevels bootstrapErrorSampler extensionErrorSampler tgswGadget _

/-- Uniform source-BRK errors discharge the complete adaptive source one-circular term exactly. -/
theorem sourceOneCircularAdaptiveAdvantage_uniformError_eq_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) :
    sourceOneCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
      keySwitchLevels queryCount ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler
      scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
      decompose encode adversary = 0 := by
  unfold sourceOneCircularAdaptiveAdvantage
  exact sourceContinuationAdvantage_uniformError_eq_zero q degree sourceRank suffixRank
    tgswLevels extensionErrorSampler tgswGadget _

/-- The derived target-BRK replacement cost is exactly one source one-circular adaptive term. -/
theorem bootstrapReplacementAdvantage_eq_sourceOneCircular
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) :
    (realAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount
        bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler inputErrorSampler
        tgswGadget scalarKeySwitchGadget decompose encode adversary).boolDistAdvantage
      (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
        queryCount bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler
        inputErrorSampler tgswGadget scalarKeySwitchGadget decompose encode adversary) =
    sourceOneCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
      keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
      scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
      decompose encode adversary := by
  unfold realAdaptiveGame bootstrapZeroAdaptiveGame sourceOneCircularAdaptiveAdvantage
    sourceContinuationAdvantage
  rw [realContinuationGame_eq_source, bootstrapZeroContinuationGame_eq_source]

/-- **Adaptive nested-ring TFHE security through the exact one-circular boundary.**  Honest IND
advantage is bounded by one source self-BRK replacement and the BRK-zero endpoint. -/
theorem abs_signedAdvantage_realAdaptive_le_sourceOneCircular_add_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount
        bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler inputErrorSampler
        tgswGadget scalarKeySwitchGadget decompose encode adversary)| ≤
      sourceOneCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
          scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
          decompose encode adversary +
        |Encryption.signedAdvantage
          (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
            queryCount bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler
            inputErrorSampler tgswGadget scalarKeySwitchGadget decompose encode adversary)| := by
  unfold Encryption.signedAdvantage
  rw [← bootstrapReplacementAdvantage_eq_sourceOneCircular q degree sourceRank suffixRank
    tgswLevels keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
    scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
    decompose encode adversary]
  unfold ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | realAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
      queryCount bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler
      inputErrorSampler tgswGadget scalarKeySwitchGadget decompose encode adversary]).toReal
    (Pr[= true | bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels
      keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
      scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
      decompose encode adversary]).toReal
    (1 / 2 : ℝ)

/-- Fully explicit statistical version of the adaptive theorem.  The only remaining
cryptographic endpoint is the BRK-zero game; the source circular term is discharged by the
one-draw distance of its row-error sampler from uniform. -/
theorem abs_signedAdvantage_realAdaptive_le_uniformError_add_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount
        bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler inputErrorSampler
        tgswGadget scalarKeySwitchGadget decompose encode adversary)| ≤
      2 * (SamplerReplacement.bootstrappingErrorCount sourceRank tgswLevels
          (scalarDimension sourceRank degree) : ℝ) *
          tvDist bootstrapErrorSampler ($ᵗ (RLWE.Rq q degree)) +
        |Encryption.signedAdvantage
          (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
            queryCount bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler
            inputErrorSampler tgswGadget scalarKeySwitchGadget decompose encode adversary)| := by
  exact (abs_signedAdvantage_realAdaptive_le_sourceOneCircular_add_zero q degree sourceRank
    suffixRank tgswLevels keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
    scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget decompose
    encode adversary).trans (add_le_add
      (sourceOneCircularAdaptiveAdvantage_le_uniformError q degree sourceRank suffixRank
        tgswLevels keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
        scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
        decompose encode adversary) (le_refl _))

/-- The BRK-zero endpoint has zero signed IND advantage when fresh input errors are uniform. -/
theorem abs_signedAdvantage_bootstrapZero_uniformInput_eq_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
        queryCount bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler
        ($ᵗ (ZMod q)) tgswGadget scalarKeySwitchGadget decompose encode adversary)| = 0 := by
  unfold Encryption.signedAdvantage
  rw [bootstrapZeroAdaptiveGame_uniformInput_probOutput_true q degree sourceRank suffixRank
    tgswLevels keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
    scalarKeySwitchErrorSampler tgswGadget scalarKeySwitchGadget decompose encode adversary
    hbound]
  norm_num

/-- **Complete security-only endpoint.**  Uniform source-BRK row errors erase the sole circular
hop, and uniform fresh input errors make the remaining adaptive IND game perfectly fair.  The
extension and scalar-KSK error samplers remain arbitrary.  This theorem proves confidentiality
but deliberately does not claim TFHE correctness under these wide errors. -/
theorem abs_signedAdvantage_realAdaptive_uniformBootstrap_uniformInput_eq_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels
      keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount
        ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler scalarKeySwitchErrorSampler
        ($ᵗ (ZMod q)) tgswGadget scalarKeySwitchGadget decompose encode adversary)| = 0 := by
  have h := abs_signedAdvantage_realAdaptive_le_sourceOneCircular_add_zero q degree
    sourceRank suffixRank tgswLevels keySwitchLevels queryCount ($ᵗ (RLWE.Rq q degree))
    extensionErrorSampler scalarKeySwitchErrorSampler ($ᵗ (ZMod q)) tgswGadget
    scalarKeySwitchGadget decompose encode adversary
  rw [sourceOneCircularAdaptiveAdvantage_uniformError_eq_zero q degree sourceRank
      suffixRank tgswLevels keySwitchLevels queryCount extensionErrorSampler
      scalarKeySwitchErrorSampler ($ᵗ (ZMod q)) tgswGadget scalarKeySwitchGadget
      decompose encode adversary,
    abs_signedAdvantage_bootstrapZero_uniformInput_eq_zero q degree sourceRank suffixRank
      tgswLevels keySwitchLevels queryCount ($ᵗ (RLWE.Rq q degree))
      extensionErrorSampler scalarKeySwitchErrorSampler tgswGadget scalarKeySwitchGadget
      decompose encode adversary hbound] at h
  norm_num at h
  simp [h]

/-! ### Public FHE evaluation -/

/-- Adaptive adversary whose oracle responses have been publicly evaluated from fresh encrypted
inputs. -/
abbrev EvaluationAdversary
    (Message Output : Type)
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ) :=
  Encryption.Adaptive.Adversary Message
    (CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels) Output

/-- Honest adaptive game in which every encryption-oracle response is passed through a public
cloud-key-dependent TFHE/FHE evaluator before it reaches the adversary. -/
def realPublicEvaluationGame
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels keySwitchLevels) : ProbComp Bool :=
  realAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount
    bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler inputErrorSampler
    tgswGadget scalarKeySwitchGadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)

/-- Public-evaluation comparison game after replacing the source one-circular BRK messages. -/
def bootstrapZeroPublicEvaluationGame
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels keySwitchLevels) : ProbComp Bool :=
  bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount
    bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler inputErrorSampler
    tgswGadget scalarKeySwitchGadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)

/-- Public evaluation preserves the encryption-query bound exactly. -/
theorem compilePublicEvaluation_isQueryBound
    {Message Output : Type}
    {q degree sourceRank suffixRank tgswLevels keySwitchLevels : ℕ}
    [NeZero q]
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels keySwitchLevels)
    (queryCount : ℕ)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    Encryption.Adaptive.IsQueryBound
      (Encryption.Adaptive.compilePublicEvaluation evaluate adversary) queryCount := by
  letI : IsUniformSpec
      ((Message × Message) →ₒ
        TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree)) :=
    IsUniformSpec.ofFintypeInhabited _
  exact Encryption.Adaptive.compilePublicEvaluation_isQueryBound
    evaluate adversary queryCount hbound

/-- **FHE-evaluation security boundary for the corrected nested-ring construction.**  Public
homomorphic evaluation adds no security term: the evaluated adaptive game is bounded by the same
single source one-circular replacement and its BRK-zero endpoint. -/
theorem abs_signedAdvantage_publicEvaluation_le_sourceOneCircular_add_zero
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels keySwitchLevels) :
    |Encryption.signedAdvantage
      (realPublicEvaluationGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
        queryCount bootstrapErrorSampler extensionErrorSampler scalarKeySwitchErrorSampler
        inputErrorSampler tgswGadget scalarKeySwitchGadget decompose encode evaluate adversary)| ≤
      sourceOneCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
          scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
          decompose encode (Encryption.Adaptive.compilePublicEvaluation evaluate adversary) +
        |Encryption.signedAdvantage
          (bootstrapZeroPublicEvaluationGame q degree sourceRank suffixRank tgswLevels
            keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
            scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget
            decompose encode evaluate adversary)| := by
  exact abs_signedAdvantage_realAdaptive_le_sourceOneCircular_add_zero q degree sourceRank
    suffixRank tgswLevels keySwitchLevels queryCount bootstrapErrorSampler extensionErrorSampler
    scalarKeySwitchErrorSampler inputErrorSampler tgswGadget scalarKeySwitchGadget decompose
    encode (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)

/-- The complete security-only zero-advantage theorem also survives arbitrary public TFHE/FHE
evaluation.  Query boundedness is transferred by the checked compiler without increasing the
number of underlying encryptions. -/
theorem abs_signedAdvantage_publicEvaluation_uniformBootstrap_uniformInput_eq_zero
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels keySwitchLevels queryCount : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (scalarKeySwitchGadget : Fin keySwitchLevels → ZMod q)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod q) (scalarDimension sourceRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realPublicEvaluationGame q degree sourceRank suffixRank tgswLevels keySwitchLevels
        queryCount ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler
        scalarKeySwitchErrorSampler ($ᵗ (ZMod q)) tgswGadget scalarKeySwitchGadget
        decompose encode evaluate adversary)| = 0 := by
  unfold realPublicEvaluationGame
  exact abs_signedAdvantage_realAdaptive_uniformBootstrap_uniformInput_eq_zero q degree
    sourceRank suffixRank tgswLevels keySwitchLevels queryCount extensionErrorSampler
    scalarKeySwitchErrorSampler tgswGadget scalarKeySwitchGadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)
    (compilePublicEvaluation_isQueryBound evaluate adversary queryCount hbound)

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessNestedRing
