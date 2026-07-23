/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveEncryptionSecurity
import FormalProof4FHE.TFHE.SharedRandomnessBootstrappingKeyExtension
import FormalProof4FHE.TFHE.SharedRandomnessOneCycle
import FormalProof4FHE.LWE.AuxiliaryInput

set_option autoImplicit false

/-!
# Target-Message Security for Nested-Ring Shared-Randomness TFHE

This file formalizes the fixed-message arrow

`BRK(targetMessages, sourceRingKey) -> BRK(targetMessages, targetRingKey)`

for nested ring keys

`targetRingKey = sourceRingKey || suffixRingKey`.

Unlike the prefix-message optimization, the message vector here is the coefficient extraction of
the *complete target ring key* on both sides of the arrow.  Hence the source object is

`BRK(KeyExtract(targetRingKey), sourceRingKey)`

and the derived object is

`BRK(KeyExtract(targetRingKey), targetRingKey)`.

The source encryption key occurs literally as a prefix of the target message vector.  Thus the
only directed secret-key cycle already occurs in the source BRK; public key extension does not add
a second circular-security hop.  The independent suffix messages and the suffix ring-extension
key remain auxiliary input to that one source-cycle experiment.

After bootstrapping under `targetRingKey`, sample extraction produces a TLWE ciphertext under
`KeyExtract(targetRingKey)`, which is also the input encryption key in this variant.  Consequently
the formal cloud key below contains the derived BRK but no additional scalar shrinking KSK.

The exact uniform-error endpoint proves confidentiality only.  It deliberately makes no
correctness claim.  For narrow centered-binomial or discrete-Gaussian errors, the contextual
source one-cycle term exposed below remains the computational research obligation.
-/

open Matrix OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages

noncomputable section

/-- Dimension of the scalar target key obtained from the complete target ring key. -/
abbrev targetScalarDimension (sourceRank suffixRank degree : ℕ) :=
  (sourceRank + suffixRank) * degree

/-- Complete target ring key, whose source prefix is shared exactly. -/
def targetRingSecret {sourceRank suffixRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    RingBinarySecret (sourceRank + suffixRank) degree :=
  FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret
    sourceSecret suffixSecret

/-- The fixed target-message vector appearing on both sides of the BRK conversion. -/
def targetMessages {sourceRank suffixRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    BinarySecret (targetScalarDimension sourceRank suffixRank degree) :=
  keyExtract (targetRingSecret sourceSecret suffixSecret)

/-- Hybrid message vector with the shared source prefix zeroed and the independent target suffix
left unchanged. -/
def suffixOnlyMessages {sourceRank suffixRank degree : ℕ}
    (suffixSecret : RingBinarySecret suffixRank degree) :
    BinarySecret (targetScalarDimension sourceRank suffixRank degree) :=
  fun coordinate ↦
    let indexed := finProdFinEquiv.symm coordinate
    Fin.addCases (fun _ ↦ false)
      (fun suffixComponent ↦ suffixSecret suffixComponent indexed.2) indexed.1

/-- Every source coefficient is literally a target-message prefix coordinate. -/
@[simp]
theorem targetMessages_source
    {sourceRank suffixRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree)
    (component : Fin sourceRank) (coefficient : Fin degree) :
    targetMessages sourceSecret suffixSecret
        (finProdFinEquiv (Fin.castAdd suffixRank component, coefficient)) =
      keyExtract sourceSecret (finProdFinEquiv (component, coefficient)) := by
  simp [targetMessages, targetRingSecret,
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret]

/-- The other target-message coordinates are exactly the independent suffix coefficients. -/
@[simp]
theorem targetMessages_suffix
    {sourceRank suffixRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree)
    (component : Fin suffixRank) (coefficient : Fin degree) :
    targetMessages sourceSecret suffixSecret
        (finProdFinEquiv (Fin.natAdd sourceRank component, coefficient)) =
      keyExtract suffixSecret (finProdFinEquiv (component, coefficient)) := by
  simp [targetMessages, targetRingSecret,
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret]

/-- Source-prefix coordinates are zero in the suffix-only hybrid. -/
@[simp]
theorem suffixOnlyMessages_source
    {sourceRank suffixRank degree : ℕ}
    (suffixSecret : RingBinarySecret suffixRank degree)
    (component : Fin sourceRank) (coefficient : Fin degree) :
    suffixOnlyMessages (sourceRank := sourceRank) suffixSecret
        (finProdFinEquiv (Fin.castAdd suffixRank component, coefficient)) = false := by
  simp [suffixOnlyMessages]

/-- Target-suffix coordinates are unchanged in the suffix-only hybrid. -/
@[simp]
theorem suffixOnlyMessages_suffix
    {sourceRank suffixRank degree : ℕ}
    (suffixSecret : RingBinarySecret suffixRank degree)
    (component : Fin suffixRank) (coefficient : Fin degree) :
    suffixOnlyMessages (sourceRank := sourceRank) suffixSecret
        (finProdFinEquiv (Fin.natAdd sourceRank component, coefficient)) =
      keyExtract suffixSecret (finProdFinEquiv (component, coefficient)) := by
  simp [suffixOnlyMessages, keyExtract]

/-- The BRK before ring-key extension: target messages encrypted under the source prefix key. -/
abbrev SourceBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Native.BootstrappingKey q degree sourceRank tgswLevels
    (targetScalarDimension sourceRank suffixRank degree)

/-- The same target messages after changing only the BRK ring encryption key. -/
abbrev DerivedBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Native.BootstrappingKey q degree (sourceRank + suffixRank) tgswLevels
    (targetScalarDimension sourceRank suffixRank degree)

/-- Ring-valued suffix key used while completing the target TGSW gadget layout. -/
abbrev RingExtensionKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.RingKeySwitchKey
    q degree sourceRank suffixRank tgswLevels

/-- Final public cloud key for the full-target-message variant. -/
structure CloudKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) where
  bootstrappingKey :
    DerivedBootstrappingKey q degree sourceRank suffixRank tgswLevels

/-- Generate `BRK(KeyExtract(S_target), S_source)`. -/
def generateSourceBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels) :=
  Native.generateBootstrappingKey q degree sourceRank tgswLevels
    (targetScalarDimension sourceRank suffixRank degree) errorSampler gadget
    (targetMessages sourceSecret suffixSecret) sourceSecret

/-- Format-identical source-key BRK with every fixed target message replaced by zero. -/
def generateZeroSourceBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree) :
    ProbComp (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels) :=
  Native.generateZeroBootstrappingKey q degree sourceRank tgswLevels
    (targetScalarDimension sourceRank suffixRank degree) errorSampler gadget sourceSecret

/-- Source-key BRK hybrid that retains only the independent suffix coordinates of the fixed
target message vector. -/
def generateSuffixOnlySourceBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels) :=
  Native.generateBootstrappingKey q degree sourceRank tgswLevels
    (targetScalarDimension sourceRank suffixRank degree) errorSampler gadget
    (suffixOnlyMessages suffixSecret) sourceSecret

/-- Generate the suffix completion material under the source ring key. -/
def generateRingExtensionKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (RingExtensionKey q degree sourceRank suffixRank tgswLevels) :=
  FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.generateRingKeySwitchKey
    q degree sourceRank suffixRank tgswLevels errorSampler gadget sourceSecret suffixSecret

/-- Apply the public ring-key extension while leaving the target-message index untouched. -/
def deriveBootstrappingKey
    (q degree sourceRank suffixRank tgswLevels : ℕ)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (sourceBootstrappingKey :
      SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
    (ringExtensionKey : RingExtensionKey q degree sourceRank suffixRank tgswLevels) :
    DerivedBootstrappingKey q degree sourceRank suffixRank tgswLevels :=
  FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.deriveTargetBootstrappingKey
    q degree sourceRank suffixRank tgswLevels
      (targetScalarDimension sourceRank suffixRank degree) decompose
      sourceBootstrappingKey ringExtensionKey

/-- Generate the derived target-ring cloud key for fixed nested secrets. -/
def generateCloudKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (CloudKey q degree sourceRank suffixRank tgswLevels) := do
  let sourceBootstrappingKey ← generateSourceBootstrappingKey q degree sourceRank
    suffixRank tgswLevels bootstrapErrorSampler gadget sourceSecret suffixSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels extensionErrorSampler gadget sourceSecret suffixSecret
  return ⟨deriveBootstrappingKey q degree sourceRank suffixRank tgswLevels decompose
    sourceBootstrappingKey ringExtensionKey⟩

/-- The corresponding target cloud key after zeroing only the fixed BRK messages. -/
def generateBootstrapZeroCloudKey
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (CloudKey q degree sourceRank suffixRank tgswLevels) := do
  let sourceBootstrappingKey ← generateZeroSourceBootstrappingKey q degree sourceRank
    suffixRank tgswLevels bootstrapErrorSampler gadget sourceSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels extensionErrorSampler gadget sourceSecret suffixSecret
  return ⟨deriveBootstrappingKey q degree sourceRank suffixRank tgswLevels decompose
    sourceBootstrappingKey ringExtensionKey⟩

/-! ## Exact source-cycle boundary -/

/-- An arbitrary later experiment receives the hidden nested secrets and final public BRK. -/
abbrev Continuation
    (q degree sourceRank suffixRank tgswLevels : ℕ) (Output : Type) :=
  RingBinarySecret sourceRank degree →
    RingBinarySecret suffixRank degree →
      CloudKey q degree sourceRank suffixRank tgswLevels → ProbComp Output

/-- Honest target-message derived-cloud-key game. -/
def realContinuationGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels Output) :
    ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let cloudKey ← generateCloudKey q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler gadget decompose sourceSecret suffixSecret
  continuation sourceSecret suffixSecret cloudKey

/-- The same experiment after replacing all target messages in the source BRK by zero. -/
def bootstrapZeroContinuationGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels Output) :
    ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let cloudKey ← generateBootstrapZeroCloudKey q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler gadget decompose sourceSecret suffixSecret
  continuation sourceSecret suffixSecret cloudKey

/-- Continuation placed before the public source-to-target ring-key conversion. -/
abbrev SourceContinuation
    (q degree sourceRank suffixRank tgswLevels : ℕ) (Output : Type) :=
  RingBinarySecret sourceRank degree →
    RingBinarySecret suffixRank degree →
      SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels →
        RingExtensionKey q degree sourceRank suffixRank tgswLevels → ProbComp Output

/-- Compile any target-BRK use into a use of the source BRK and common extension material. -/
def compileSourceContinuation
    (q degree sourceRank suffixRank tgswLevels : ℕ)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels Output) :
    SourceContinuation q degree sourceRank suffixRank tgswLevels Output :=
  fun sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey ↦
    continuation sourceSecret suffixSecret
      ⟨deriveBootstrappingKey q degree sourceRank suffixRank tgswLevels decompose
        sourceBootstrappingKey ringExtensionKey⟩

/-- Source-key BRK carrying the complete target message vector. -/
def realSourceContinuationGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ← generateSourceBootstrappingKey q degree sourceRank
    suffixRank tgswLevels bootstrapErrorSampler gadget sourceSecret suffixSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels extensionErrorSampler gadget sourceSecret suffixSecret
  continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey

/-- Intermediate source game: the independent target-suffix messages remain encrypted, while
every message coordinate belonging to the shared source prefix is zero. -/
def suffixOnlySourceContinuationGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ← generateSuffixOnlySourceBootstrappingKey q degree
    sourceRank suffixRank tgswLevels bootstrapErrorSampler gadget sourceSecret suffixSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels extensionErrorSampler gadget sourceSecret suffixSecret
  continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey

/-- Source-key zero-message comparison with identical nested secrets and extension material. -/
def bootstrapZeroSourceContinuationGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    ProbComp Output := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ← generateZeroSourceBootstrappingKey q degree sourceRank
    suffixRank tgswLevels bootstrapErrorSampler gadget sourceSecret
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels extensionErrorSampler gadget sourceSecret suffixSecret
  continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey

/-- Contextual one-cycle advantage at the corrected source boundary. -/
def sourceTargetMessageCircularAdvantage
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) : ℝ :=
  (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation).boolDistAdvantage
    (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation)

/-- The genuine source-prefix circular hop.  It replaces only the message coordinates that are
coefficients of the source encryption key; suffix messages and extension material are retained. -/
def sourcePrefixCircularAdvantage
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) : ℝ :=
  (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation).boolDistAdvantage
    (suffixOnlySourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation)

/-- The remaining acyclic suffix-message hop.  Its messages depend only on the independent suffix
secret, while the BRK encryption key is the source secret. -/
def independentSuffixAdvantage
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) : ℝ :=
  (suffixOnlySourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation).boolDistAdvantage
    (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation)

/-- The former combined source term splits into exactly one true prefix-cycle hop and one
independent-suffix hop. -/
theorem sourceTargetMessageCircularAdvantage_le_prefix_add_suffix
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    sourceTargetMessageCircularAdvantage q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation ≤
      sourcePrefixCircularAdvantage q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget continuation +
        independentSuffixAdvantage q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget continuation := by
  unfold sourceTargetMessageCircularAdvantage sourcePrefixCircularAdvantage
    independentSuffixAdvantage ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation]).toReal
    (Pr[= true | suffixOnlySourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation]).toReal
    (Pr[= true | bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget continuation]).toReal

/-! ### Exact auxiliary-input classification of the acyclic suffix hop -/

/-- Pair of nested source/suffix secrets used by the suffix-only auxiliary-input problem. -/
abbrev NestedSecret (sourceRank suffixRank degree : ℕ) :=
  RingBinarySecret sourceRank degree × RingBinarySecret suffixRank degree

/-- Independently sample the two blocks of the nested key. -/
def sampleNestedSecret (sourceRank suffixRank degree : ℕ) :
    ProbComp (NestedSecret sourceRank suffixRank degree) := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  return (sourceSecret, suffixSecret)

/-- Auxiliary-input problem for the acyclic suffix-message replacement.  The challenge encrypts
only suffix-secret coordinates under the independent source key; the ring-extension table is
retained unchanged as auxiliary input. -/
def suffixAuxiliaryProblem
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) :
    FormalProof4FHE.LWE.AuxiliaryInput.Problem
      (NestedSecret sourceRank suffixRank degree)
      (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
      (RingExtensionKey q degree sourceRank suffixRank tgswLevels) where
  sampleSecret := sampleNestedSecret sourceRank suffixRank degree
  sampleReal := fun secret ↦
    generateSuffixOnlySourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler gadget secret.1 secret.2
  sampleZero := fun secret ↦
    generateZeroSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler gadget secret.1
  sampleUniform := $ᵗ (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
  sampleAuxiliary := fun secret ↦
    generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
      extensionErrorSampler gadget secret.1 secret.2

/-- Repackage a nested-ring source continuation for the generic auxiliary-input interface. -/
def compileSuffixAuxiliaryContinuation
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    FormalProof4FHE.LWE.AuxiliaryInput.Continuation
      (NestedSecret sourceRank suffixRank degree)
      (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
      (RingExtensionKey q degree sourceRank suffixRank tgswLevels) :=
  fun secret bootstrappingKey extensionKey ↦
    continuation secret.1 secret.2 bootstrappingKey extensionKey

/-- The real branch of the auxiliary-input problem is exactly the suffix-only source hybrid. -/
theorem suffixAuxiliary_realGame_eq
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    FormalProof4FHE.LWE.AuxiliaryInput.realGame
        (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget)
        (compileSuffixAuxiliaryContinuation continuation) =
      suffixOnlySourceContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation := by
  simp [FormalProof4FHE.LWE.AuxiliaryInput.realGame, suffixAuxiliaryProblem,
    sampleNestedSecret, compileSuffixAuxiliaryContinuation,
    suffixOnlySourceContinuationGame, bind_assoc, monad_norm]

/-- The zero branch of the auxiliary-input problem is exactly the all-zero source hybrid. -/
theorem suffixAuxiliary_zeroGame_eq
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    FormalProof4FHE.LWE.AuxiliaryInput.zeroGame
        (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget)
        (compileSuffixAuxiliaryContinuation continuation) =
      bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation := by
  simp [FormalProof4FHE.LWE.AuxiliaryInput.zeroGame, suffixAuxiliaryProblem,
    sampleNestedSecret, compileSuffixAuxiliaryContinuation,
    bootstrapZeroSourceContinuationGame, bind_assoc, monad_norm]

/-- The acyclic suffix advantage is definitionally the KDM real/zero distance of its exact
auxiliary-input presentation.  The name `KDM` here belongs to the generic interface; the dependency
graph has no edge from the source encryption key back into the suffix messages. -/
theorem independentSuffixAdvantage_eq_auxiliaryKDM
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    independentSuffixAdvantage q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation =
      FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage
        (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget)
        (compileSuffixAuxiliaryContinuation continuation) := by
  unfold independentSuffixAdvantage FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage
  rw [suffixAuxiliary_realGame_eq, suffixAuxiliary_zeroGame_eq]

/-- The acyclic suffix hop is reduced to its real-versus-uniform joint pseudorandomness branch
plus the zero-versus-uniform branch, both retaining the same ring-extension auxiliary input. -/
theorem independentSuffixAdvantage_le_auxiliaryRealUniform_add_zeroUniform
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    independentSuffixAdvantage q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget continuation ≤
      FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
          (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
            bootstrapErrorSampler extensionErrorSampler gadget)
          (compileSuffixAuxiliaryContinuation continuation) +
        FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage
          (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
            bootstrapErrorSampler extensionErrorSampler gadget)
          (compileSuffixAuxiliaryContinuation continuation) := by
  rw [independentSuffixAdvantage_eq_auxiliaryKDM]
  exact FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe _ _

/-- Real target-key execution is definitionally the compiled source-key execution. -/
theorem realContinuationGame_eq_source
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels Output) :
    realContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget decompose continuation =
      realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget
        (compileSourceContinuation q degree sourceRank suffixRank tgswLevels
          decompose continuation) := by
  simp [realContinuationGame, realSourceContinuationGame, generateCloudKey,
    compileSourceContinuation, bind_assoc, monad_norm]

/-- Zero target-key execution is definitionally the compiled source-key comparison. -/
theorem bootstrapZeroContinuationGame_eq_source
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels Output) :
    bootstrapZeroContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget decompose continuation =
      bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
        bootstrapErrorSampler extensionErrorSampler gadget
        (compileSourceContinuation q degree sourceRank suffixRank tgswLevels
          decompose continuation) := by
  simp [bootstrapZeroContinuationGame, bootstrapZeroSourceContinuationGame,
    generateBootstrapZeroCloudKey, compileSourceContinuation, bind_assoc, monad_norm]

/-- The complete target-BRK replacement distance is exactly the corrected source-cycle distance. -/
theorem tvDist_continuation_eq_sourceTargetMessageCircular
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : Continuation q degree sourceRank suffixRank tgswLevels Output) :
    tvDist
        (realContinuationGame q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget decompose continuation)
        (bootstrapZeroContinuationGame q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget decompose continuation) =
      tvDist
        (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget
          (compileSourceContinuation q degree sourceRank suffixRank tgswLevels
            decompose continuation))
        (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget
          (compileSourceContinuation q degree sourceRank suffixRank tgswLevels
            decompose continuation)) := by
  rw [realContinuationGame_eq_source, bootstrapZeroContinuationGame_eq_source]

/-! ## Exact security-only endpoint for the corrected source cycle -/

/-- Uniform source-BRK row errors erase the complete target message vector for fixed secrets. -/
theorem generateSourceBootstrappingKey_uniformError_evalDist_eq_zero
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    evalDist
        (generateSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
          ($ᵗ (RLWE.Rq q degree)) gadget sourceSecret suffixSecret) =
      evalDist
        (generateZeroSourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
          ($ᵗ (RLWE.Rq q degree)) gadget sourceSecret) := by
  let rqCommRing : CommRing (RLWE.Rq q degree) :=
    LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree
  letI := rqCommRing
  unfold generateSourceBootstrappingKey generateZeroSourceBootstrappingKey
    Native.generateBootstrappingKey Native.generateZeroBootstrappingKey
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
        (embedConstantBit q degree (targetMessages sourceSecret suffixSecret coordinate))
    _ = _ := by
      change evalDist ($ᵗ (TGSW.Ciphertext (RLWE.Rq q degree) sourceRank tgswLevels)) =
        evalDist (TGSW.encrypt sourceRank tgswLevels ($ᵗ (RLWE.Rq q degree))
          (embedRingSecret q sourceSecret) gadget zeroMessage)
      exact
        (SharedRandomnessOneCycle.tgswEncrypt_uniformError_evalDist sourceRank tgswLevels
          (embedRingSecret q sourceSecret) gadget zeroMessage).symm

/-- Uniform source-BRK errors erase the contextual source-cycle distinction exactly. -/
theorem realSourceContinuationGame_uniformError_evalDist_eq_zero
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    {Output : Type}
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Output) :
    evalDist
        (realSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler gadget continuation) =
      evalDist
        (bootstrapZeroSourceContinuationGame q degree sourceRank suffixRank tgswLevels
          ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler gadget continuation) := by
  unfold realSourceContinuationGame bootstrapZeroSourceContinuationGame
  refine evalDist_bind_congr' (Native.sampleRingSecret sourceRank degree) fun sourceSecret ↦ ?_
  refine evalDist_bind_congr' (Native.sampleRingSecret suffixRank degree) fun suffixSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (generateSourceBootstrappingKey_uniformError_evalDist_eq_zero q degree sourceRank
      suffixRank tgswLevels gadget sourceSecret suffixSecret)
    (fun sourceBootstrappingKey ↦
      generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
          extensionErrorSampler gadget sourceSecret suffixSecret >>= fun ringExtensionKey ↦
        continuation sourceSecret suffixSecret sourceBootstrappingKey ringExtensionKey)

/-- Uniform source-BRK errors make the corrected contextual one-cycle advantage zero. -/
theorem sourceTargetMessageCircularAdvantage_uniformError_eq_zero
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : SourceContinuation q degree sourceRank suffixRank tgswLevels Bool) :
    sourceTargetMessageCircularAdvantage q degree sourceRank suffixRank tgswLevels
      ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler gadget continuation = 0 := by
  unfold sourceTargetMessageCircularAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (realSourceContinuationGame_uniformError_evalDist_eq_zero q degree sourceRank
      suffixRank tgswLevels extensionErrorSampler gadget continuation) true]
  simp

/-! ## Adaptive encryption under the complete target key -/

/-- Adaptive adversary for the full-target-message derived cloud key. -/
abbrev AdaptiveAdversary
    (Message : Type)
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Encryption.Adaptive.Adversary Message
    (CloudKey q degree sourceRank suffixRank tgswLevels)
    (TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree))

/-- Run an adaptive adversary from a fixed eager tape of target-key LWE samples. -/
def runFromTranscript
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    [NeZero q]
    (bit : Bool) (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels)
    {samples : ℕ}
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q)
      (targetScalarDimension sourceRank suffixRank degree) samples) : ProbComp Bool :=
  (simulateQ
      (GeneralizedSubspaceLWE.Adaptive.sourceImpl
        ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample
          (ZMod q) (targetScalarDimension sourceRank suffixRank degree))).withPregen
      (simulateQ
        (Encryption.Adaptive.sourceReduction
          (lweDimension := targetScalarDimension sourceRank suffixRank degree) bit encode)
        (adversary cloudKey))).run'
    (GeneralizedSubspaceLWE.Adaptive.sourceSampleSeed
      (GeneralizedSubspaceLWE.Adaptive.batchSamples transcript))

/-- Dummy native key used to reuse the cloud-type-parametric uniform-transcript theorem. -/
private def dummyNativeCloudKey (q lweDimension : ℕ) :
    Encryption.NativeCloudKey q 0 0 0 lweDimension 0 :=
  ⟨fun _ ↦ (fun _ _ ↦ 0, fun _ ↦ 0),
    (fun _ _ ↦ 0, fun _ ↦ 0)⟩

/-- Wrap a fixed target-message adversary as a native adversary ignoring a dummy cloud key. -/
private def asNativeAdversary
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels) :
    Encryption.Adaptive.NativeAdversary Message q 0 0 0
      (targetScalarDimension sourceRank suffixRank degree) 0 :=
  fun _ ↦ adversary cloudKey

/-- A query-bounded adversary succeeds with probability one half on a uniform target transcript. -/
theorem uniformTranscript_adaptive_probOutput_true
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    [NeZero q]
    (queryCount : ℕ) (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (Encryption.Adaptive.isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q)
          (targetScalarDimension sourceRank suffixRank degree)))
      queryCount) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let transcript ← $ᵗ (FormalProof4FHE.LWE.BatchTranscript
        (ZMod q) (targetScalarDimension sourceRank suffixRank degree) queryCount)
      let guess ← runFromTranscript bit encode adversary cloudKey transcript
      return (bit == guess)] = 1 / 2 := by
  let nativeAdversary := asNativeAdversary adversary cloudKey
  let nativeCloudKey := dummyNativeCloudKey q
    (targetScalarDimension sourceRank suffixRank degree)
  have hNativeBound : IsQueryBoundP (nativeAdversary nativeCloudKey)
      (Encryption.Adaptive.isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q)
          (targetScalarDimension sourceRank suffixRank degree)))
      queryCount := by
    simpa [nativeAdversary, asNativeAdversary] using hbound
  simpa [runFromTranscript, Encryption.Adaptive.runFromTranscript,
    nativeAdversary, asNativeAdversary] using
    (Encryption.Adaptive.uniformAdaptive_probOutput_true
      (Message := Message) (q := q) (degree := 0) (ringRank := 0)
      (tgswLevels := 0)
      (lweDimension := targetScalarDimension sourceRank suffixRank degree)
      (keySwitchLevels := 0) queryCount encode nativeAdversary nativeCloudKey hNativeBound)

/-- Secret-dependent adaptive encryption continuation under `KeyExtract(S_target)`. -/
def adaptiveContinuation
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    [NeZero q]
    (queryCount : ℕ) (inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    Continuation q degree sourceRank suffixRank tgswLevels Bool :=
  fun sourceSecret suffixSecret cloudKey ↦ do
    let tape ← TLWE.batchEncrypt (targetScalarDimension sourceRank suffixRank degree)
      queryCount inputErrorSampler
      (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
    let bit ← $ᵗ Bool
    let guess ← runFromTranscript bit encode adversary cloudKey tape
    return bit == guess

/-- Uniform input errors turn the fixed-secret eager tape into a uniform public transcript. -/
theorem adaptiveContinuation_uniformInput_evalDist
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    [NeZero q]
    (queryCount : ℕ) (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree)
    (cloudKey : CloudKey q degree sourceRank suffixRank tgswLevels) :
    evalDist
        (adaptiveContinuation queryCount ($ᵗ (ZMod q)) encode adversary
          sourceSecret suffixSecret cloudKey) =
      evalDist (do
        let bit ← $ᵗ Bool
        let transcript ← $ᵗ (FormalProof4FHE.LWE.BatchTranscript
          (ZMod q) (targetScalarDimension sourceRank suffixRank degree) queryCount)
        let guess ← runFromTranscript bit encode adversary cloudKey transcript
        return bit == guess) := by
  let tapeSampler := TLWE.batchEncrypt
    (targetScalarDimension sourceRank suffixRank degree) queryCount
    ($ᵗ (ZMod q)) (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
  let uniformTape : ProbComp (FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) (targetScalarDimension sourceRank suffixRank degree) queryCount) :=
    $ᵗ (FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) (targetScalarDimension sourceRank suffixRank degree) queryCount)
  let finish := fun
      (transcript : FormalProof4FHE.LWE.BatchTranscript
        (ZMod q) (targetScalarDimension sourceRank suffixRank degree) queryCount)
      (bit : Bool) ↦ do
    let guess ← runFromTranscript bit encode adversary cloudKey transcript
    return bit == guess
  have htape : evalDist tapeSampler = evalDist uniformTape := by
    exact SharedRandomnessOneCycle.batchEncrypt_uniformError_evalDist
      (targetScalarDimension sourceRank suffixRank degree) queryCount
      (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
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

/-- Honest adaptive encryption game using the derived target-key BRK. -/
def realAdaptiveGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    ProbComp Bool :=
  realContinuationGame q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler gadget decompose
    (adaptiveContinuation queryCount inputErrorSampler encode adversary)

/-- Adaptive comparison game after zeroing the fixed target messages in the source BRK. -/
def bootstrapZeroAdaptiveGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    ProbComp Bool :=
  bootstrapZeroContinuationGame q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler gadget decompose
    (adaptiveContinuation queryCount inputErrorSampler encode adversary)

/-- Uniform fresh target-key errors make the BRK-zero adaptive endpoint perfectly fair. -/
theorem bootstrapZeroAdaptiveGame_uniformInput_probOutput_true
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
      bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler ($ᵗ (ZMod q)) gadget decompose
        encode adversary] = 1 / 2 := by
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
          bootstrapErrorSampler extensionErrorSampler gadget decompose
          sourceSecret suffixSecret)]
      · simp
      · intro cloudKey _
        rw [evalDist_ext_iff.mp
          (adaptiveContinuation_uniformInput_evalDist queryCount encode adversary
            sourceSecret suffixSecret cloudKey) true]
        exact uniformTranscript_adaptive_probOutput_true queryCount encode adversary cloudKey
          (hbound cloudKey)

/-- The sole corrected source-cycle term for the complete adaptive continuation. -/
def sourceTargetMessageCircularAdaptiveAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) : ℝ :=
  sourceTargetMessageCircularAdvantage q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler gadget
    (compileSourceContinuation q degree sourceRank suffixRank tgswLevels decompose
      (adaptiveContinuation queryCount inputErrorSampler encode adversary))

/-- Adaptive specialization of the genuine source-prefix self-key hop. -/
def sourcePrefixCircularAdaptiveAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) : ℝ :=
  sourcePrefixCircularAdvantage q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler gadget
    (compileSourceContinuation q degree sourceRank suffixRank tgswLevels decompose
      (adaptiveContinuation queryCount inputErrorSampler encode adversary))

/-- Adaptive specialization of the independent-suffix message hop. -/
def independentSuffixAdaptiveAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) : ℝ :=
  independentSuffixAdvantage q degree sourceRank suffixRank tgswLevels
    bootstrapErrorSampler extensionErrorSampler gadget
    (compileSourceContinuation q degree sourceRank suffixRank tgswLevels decompose
      (adaptiveContinuation queryCount inputErrorSampler encode adversary))

/-- The exact generic auxiliary-input continuation induced by adaptive target-key encryption. -/
def suffixAuxiliaryAdaptiveContinuation
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    [NeZero q]
    (queryCount : ℕ) (inputErrorSampler : ProbComp (ZMod q))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    FormalProof4FHE.LWE.AuxiliaryInput.Continuation
      (NestedSecret sourceRank suffixRank degree)
      (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
      (RingExtensionKey q degree sourceRank suffixRank tgswLevels) :=
  compileSuffixAuxiliaryContinuation
    (compileSourceContinuation q degree sourceRank suffixRank tgswLevels decompose
      (adaptiveContinuation queryCount inputErrorSampler encode adversary))

/-- The adaptive independent-suffix hop is bounded by the two exact joint pseudorandomness
branches that a future ordinary-LWE/RLWE simulator must discharge. -/
theorem independentSuffixAdaptiveAdvantage_le_auxiliaryRealUniform_add_zeroUniform
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    independentSuffixAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
        queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
        decompose encode adversary ≤
      FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
          (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
            bootstrapErrorSampler extensionErrorSampler gadget)
          (suffixAuxiliaryAdaptiveContinuation queryCount inputErrorSampler decompose
            encode adversary) +
        FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage
          (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
            bootstrapErrorSampler extensionErrorSampler gadget)
          (suffixAuxiliaryAdaptiveContinuation queryCount inputErrorSampler decompose
            encode adversary) := by
  exact independentSuffixAdvantage_le_auxiliaryRealUniform_add_zeroUniform q degree
    sourceRank suffixRank tgswLevels bootstrapErrorSampler extensionErrorSampler gadget _

/-- The complete adaptive source term separates into its sole true circular hop and the acyclic
suffix-message hop. -/
theorem sourceTargetMessageCircularAdaptiveAdvantage_le_prefix_add_suffix
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    sourceTargetMessageCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
        queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
        decompose encode adversary ≤
      sourcePrefixCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode adversary +
        independentSuffixAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode adversary := by
  exact sourceTargetMessageCircularAdvantage_le_prefix_add_suffix q degree sourceRank
    suffixRank tgswLevels bootstrapErrorSampler extensionErrorSampler gadget _

/-- The target-BRK adaptive replacement cost is exactly the corrected source-cycle term. -/
theorem bootstrapReplacementAdvantage_eq_sourceTargetMessageCircular
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary).boolDistAdvantage
      (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary) =
    sourceTargetMessageCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
      queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
      decompose encode adversary := by
  unfold realAdaptiveGame bootstrapZeroAdaptiveGame
    sourceTargetMessageCircularAdaptiveAdvantage sourceTargetMessageCircularAdvantage
  rw [realContinuationGame_eq_source, bootstrapZeroContinuationGame_eq_source]

/-- Honest IND advantage is bounded by one corrected source cycle and the BRK-zero endpoint. -/
theorem abs_signedAdvantage_realAdaptive_le_sourceCircular_add_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary)| ≤
      sourceTargetMessageCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode adversary +
        |Encryption.signedAdvantage
          (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
            encode adversary)| := by
  unfold Encryption.signedAdvantage
  rw [← bootstrapReplacementAdvantage_eq_sourceTargetMessageCircular q degree sourceRank
    suffixRank tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler
    inputErrorSampler gadget decompose encode adversary]
  unfold ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
      bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
      encode adversary]).toReal
    (Pr[= true | bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels
      queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
      decompose encode adversary]).toReal
    (1 / 2 : ℝ)

/-- Refined adaptive TFHE boundary: one genuine source-prefix circular term, one independent
suffix term, and the zero-BRK encryption endpoint. -/
theorem abs_signedAdvantage_realAdaptive_le_prefixCircular_add_suffix_add_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary)| ≤
      sourcePrefixCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode adversary +
        independentSuffixAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode adversary +
        |Encryption.signedAdvantage
          (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
            encode adversary)| := by
  calc
    _ ≤ sourceTargetMessageCircularAdaptiveAdvantage q degree sourceRank suffixRank
          tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler
          gadget decompose encode adversary +
        |Encryption.signedAdvantage
          (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
            encode adversary)| :=
      abs_signedAdvantage_realAdaptive_le_sourceCircular_add_zero q degree sourceRank
        suffixRank tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler
        inputErrorSampler gadget decompose encode adversary
    _ ≤ (sourcePrefixCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode adversary +
        independentSuffixAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode adversary) +
        |Encryption.signedAdvantage
          (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
            encode adversary)| := by
      exact add_le_add
        (sourceTargetMessageCircularAdaptiveAdvantage_le_prefix_add_suffix q degree
          sourceRank suffixRank tgswLevels queryCount bootstrapErrorSampler
          extensionErrorSampler inputErrorSampler gadget decompose encode adversary)
        (le_refl _)

/-- Expanded adaptive boundary whose two acyclic suffix obligations are stated through the exact
auxiliary-input problem.  This is the interface for the joint ring-extension/input-tape simulator. -/
theorem abs_signedAdvantage_realAdaptive_le_prefixCircular_add_auxiliarySuffix_add_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary)| ≤
      sourcePrefixCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode adversary +
        FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
          (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
            bootstrapErrorSampler extensionErrorSampler gadget)
          (suffixAuxiliaryAdaptiveContinuation queryCount inputErrorSampler decompose
            encode adversary) +
        FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage
          (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
            bootstrapErrorSampler extensionErrorSampler gadget)
          (suffixAuxiliaryAdaptiveContinuation queryCount inputErrorSampler decompose
            encode adversary) +
        |Encryption.signedAdvantage
          (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
            encode adversary)| := by
  let prefixTerm := sourcePrefixCircularAdaptiveAdvantage q degree sourceRank suffixRank
    tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler
    gadget decompose encode adversary
  let suffixTerm := independentSuffixAdaptiveAdvantage q degree sourceRank suffixRank
    tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler
    gadget decompose encode adversary
  let realUniform := FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
    (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget)
    (suffixAuxiliaryAdaptiveContinuation queryCount inputErrorSampler decompose
      encode adversary)
  let zeroUniform := FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage
    (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
      bootstrapErrorSampler extensionErrorSampler gadget)
    (suffixAuxiliaryAdaptiveContinuation queryCount inputErrorSampler decompose
      encode adversary)
  let endpoint := |Encryption.signedAdvantage
    (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
      bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
      encode adversary)|
  have hMain : |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode adversary)| ≤ (prefixTerm + suffixTerm) + endpoint := by
    exact abs_signedAdvantage_realAdaptive_le_prefixCircular_add_suffix_add_zero q degree
      sourceRank suffixRank tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler
      inputErrorSampler gadget decompose encode adversary
  have hSuffix : suffixTerm ≤ realUniform + zeroUniform := by
    exact independentSuffixAdaptiveAdvantage_le_auxiliaryRealUniform_add_zeroUniform q
      degree sourceRank suffixRank tgswLevels queryCount bootstrapErrorSampler
      extensionErrorSampler inputErrorSampler gadget decompose encode adversary
  calc
    _ ≤ (prefixTerm + suffixTerm) + endpoint := hMain
    _ ≤ (prefixTerm + (realUniform + zeroUniform)) + endpoint := by
      exact add_le_add (add_le_add (le_refl _) hSuffix) (le_refl _)
    _ = prefixTerm + realUniform + zeroUniform + endpoint := by ring

/-- Uniform source-BRK errors discharge the complete corrected adaptive circular term. -/
theorem sourceTargetMessageCircularAdaptiveAdvantage_uniformError_eq_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels) :
    sourceTargetMessageCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
      queryCount ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler inputErrorSampler gadget
      decompose encode adversary = 0 := by
  unfold sourceTargetMessageCircularAdaptiveAdvantage
  exact sourceTargetMessageCircularAdvantage_uniformError_eq_zero q degree sourceRank
    suffixRank tgswLevels extensionErrorSampler gadget _

/-- Uniform fresh input errors make the BRK-zero signed IND advantage zero. -/
theorem abs_signedAdvantage_bootstrapZero_uniformInput_eq_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler ($ᵗ (ZMod q)) gadget decompose
        encode adversary)| = 0 := by
  unfold Encryption.signedAdvantage
  rw [bootstrapZeroAdaptiveGame_uniformInput_probOutput_true q degree sourceRank suffixRank
    tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler gadget decompose
    encode adversary hbound]
  norm_num

/-- Complete security-only endpoint for the corrected full-target-message construction. -/
theorem abs_signedAdvantage_realAdaptive_uniformBootstrap_uniformInput_eq_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q degree sourceRank suffixRank tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
        ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler ($ᵗ (ZMod q)) gadget
        decompose encode adversary)| = 0 := by
  have h := abs_signedAdvantage_realAdaptive_le_sourceCircular_add_zero q degree
    sourceRank suffixRank tgswLevels queryCount ($ᵗ (RLWE.Rq q degree))
    extensionErrorSampler ($ᵗ (ZMod q)) gadget decompose encode adversary
  rw [sourceTargetMessageCircularAdaptiveAdvantage_uniformError_eq_zero q degree
      sourceRank suffixRank tgswLevels queryCount extensionErrorSampler ($ᵗ (ZMod q))
      gadget decompose encode adversary,
    abs_signedAdvantage_bootstrapZero_uniformInput_eq_zero q degree sourceRank suffixRank
      tgswLevels queryCount ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler gadget
      decompose encode adversary hbound] at h
  norm_num at h
  simp [h]

/-! ## Public TFHE/FHE evaluation -/

/-- Adversary receiving publicly evaluated target-key encryption responses. -/
abbrev EvaluationAdversary
    (Message Output : Type)
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Encryption.Adaptive.Adversary Message
    (CloudKey q degree sourceRank suffixRank tgswLevels) Output

/-- Honest adaptive game with a public cloud-key-dependent evaluator on every response. -/
def realPublicEvaluationGame
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels →
      TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels) : ProbComp Bool :=
  realAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
    bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)

/-- Public-evaluation comparison game with zeroed source-BRK target messages. -/
def bootstrapZeroPublicEvaluationGame
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels →
      TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels) : ProbComp Bool :=
  bootstrapZeroAdaptiveGame q degree sourceRank suffixRank tgswLevels queryCount
    bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)

/-- Compiling public evaluation preserves the encryption query bound. -/
theorem compilePublicEvaluation_isQueryBound
    {Message Output : Type}
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    [NeZero q]
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels →
      TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels)
    (queryCount : ℕ)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    Encryption.Adaptive.IsQueryBound
      (Encryption.Adaptive.compilePublicEvaluation evaluate adversary) queryCount := by
  letI : IsUniformSpec
      ((Message × Message) →ₒ
        TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree)) :=
    IsUniformSpec.ofFintypeInhabited _
  exact Encryption.Adaptive.compilePublicEvaluation_isQueryBound
    evaluate adversary queryCount hbound

/-- Public FHE evaluation adds no term to the corrected source-cycle security boundary. -/
theorem abs_signedAdvantage_publicEvaluation_le_sourceCircular_add_zero
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels →
      TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels) :
    |Encryption.signedAdvantage
      (realPublicEvaluationGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode evaluate adversary)| ≤
      sourceTargetMessageCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode (Encryption.Adaptive.compilePublicEvaluation evaluate adversary) +
        |Encryption.signedAdvantage
          (bootstrapZeroPublicEvaluationGame q degree sourceRank suffixRank tgswLevels
            queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
            decompose encode evaluate adversary)| := by
  exact abs_signedAdvantage_realAdaptive_le_sourceCircular_add_zero q degree sourceRank
    suffixRank tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler
    inputErrorSampler gadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)

/-- Refined public-evaluation boundary with the circular prefix and independent suffix hops
displayed separately. -/
theorem abs_signedAdvantage_publicEvaluation_le_prefixCircular_add_suffix_add_zero
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels →
      TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels) :
    |Encryption.signedAdvantage
      (realPublicEvaluationGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode evaluate adversary)| ≤
      sourcePrefixCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode (Encryption.Adaptive.compilePublicEvaluation evaluate adversary) +
        independentSuffixAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode (Encryption.Adaptive.compilePublicEvaluation evaluate adversary) +
        |Encryption.signedAdvantage
          (bootstrapZeroPublicEvaluationGame q degree sourceRank suffixRank tgswLevels
            queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
            decompose encode evaluate adversary)| := by
  exact abs_signedAdvantage_realAdaptive_le_prefixCircular_add_suffix_add_zero q degree
    sourceRank suffixRank tgswLevels queryCount bootstrapErrorSampler extensionErrorSampler
    inputErrorSampler gadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)

/-- Public-evaluation form of the expanded auxiliary-input suffix boundary. -/
theorem abs_signedAdvantage_publicEvaluation_le_prefixCircular_add_auxiliarySuffix_add_zero
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels →
      TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels) :
    |Encryption.signedAdvantage
      (realPublicEvaluationGame q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget decompose
        encode evaluate adversary)| ≤
      sourcePrefixCircularAdaptiveAdvantage q degree sourceRank suffixRank tgswLevels
          queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          decompose encode (Encryption.Adaptive.compilePublicEvaluation evaluate adversary) +
        FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
          (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
            bootstrapErrorSampler extensionErrorSampler gadget)
          (suffixAuxiliaryAdaptiveContinuation queryCount inputErrorSampler decompose encode
            (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)) +
        FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage
          (suffixAuxiliaryProblem q degree sourceRank suffixRank tgswLevels
            bootstrapErrorSampler extensionErrorSampler gadget)
          (suffixAuxiliaryAdaptiveContinuation queryCount inputErrorSampler decompose encode
            (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)) +
        |Encryption.signedAdvantage
          (bootstrapZeroPublicEvaluationGame q degree sourceRank suffixRank tgswLevels
            queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
            decompose encode evaluate adversary)| := by
  exact abs_signedAdvantage_realAdaptive_le_prefixCircular_add_auxiliarySuffix_add_zero
    q degree sourceRank suffixRank tgswLevels queryCount bootstrapErrorSampler
    extensionErrorSampler inputErrorSampler gadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)

/-- Complete security-only zero-advantage endpoint after arbitrary public FHE evaluation. -/
theorem abs_signedAdvantage_publicEvaluation_uniformBootstrap_uniformInput_eq_zero
    {Message Output : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q degree sourceRank suffixRank tgswLevels →
      TLWE.Ciphertext (ZMod q) (targetScalarDimension sourceRank suffixRank degree) → Output)
    (adversary : EvaluationAdversary Message Output q degree sourceRank suffixRank
      tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realPublicEvaluationGame q degree sourceRank suffixRank tgswLevels queryCount
        ($ᵗ (RLWE.Rq q degree)) extensionErrorSampler ($ᵗ (ZMod q)) gadget
        decompose encode evaluate adversary)| = 0 := by
  unfold realPublicEvaluationGame
  exact abs_signedAdvantage_realAdaptive_uniformBootstrap_uniformInput_eq_zero q degree
    sourceRank suffixRank tgswLevels queryCount extensionErrorSampler gadget decompose encode
    (Encryption.Adaptive.compilePublicEvaluation evaluate adversary)
    (compilePublicEvaluation_isQueryBound evaluate adversary queryCount hbound)

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages
