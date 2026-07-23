/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.Basic
import FormalProof4FHE.TFHE.Circular

/-!
# Native Finite-Modulus TFHE Evaluation Keys

This module instantiates the abstract TFHE circular dependency graph with the actual native
evaluation-key layouts from the original TFHE construction:

* `BootstrappingKey` contains one structured ring-TGSW ciphertext for every scalar TLWE-key bit;
* `KeySwitchKey` contains one scalar TLWE row for every extracted ring-key coefficient and gadget
  level;
* `nativeCycleSpec` samples the two binary keys independently, applies coefficient `keyExtract`,
  and connects the real and zero-message generators to `TFHE.Circular.CycleSpec`.

The coefficient domain is the executable finite-modulus model: scalar rows use `ZMod q`, while
ring rows use `RLWE.Rq q degree`.  Error samplers and gadget values remain explicit parameters.
This captures the exact cryptographic dependency and matrix layout without making a false exact
identification with TFHE's ideal continuous-torus Gaussian.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native

/-- One TRGSW ciphertext for each bit of the scalar TLWE key. -/
abbrev BootstrappingKey
    (q degree ringRank tgswLevels lweDimension : ℕ) :=
  Fin lweDimension → RingGSWCiphertext q degree ringRank tgswLevels

/-- One scalar TLWE row for each source-key coefficient and key-switch gadget level.

Rows are flattened with `finProdFinEquiv`, so the row indexed by `(coordinate, level)` is column
`finProdFinEquiv (coordinate, level)` of this batch transcript. -/
abbrev KeySwitchKey
    (q targetDimension sourceDimension keySwitchLevels : ℕ) :=
  TLWE.BatchCiphertext (ZMod q) targetDimension (sourceDimension * keySwitchLevels)

/-- A native TFHE cloud key with its two heterogeneous components. -/
structure CloudKey
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) where
  bootstrappingKey : BootstrappingKey q degree ringRank tgswLevels lweDimension
  keySwitchKey : KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels

/-- Uniform scalar binary-secret sampler. -/
def sampleLweSecret (dimension : ℕ) : ProbComp (BinarySecret dimension) :=
  $ᵗ (BinarySecret dimension)

/-- Uniform vector-of-binary-polynomials TRLWE-secret sampler. -/
def sampleRingSecret (rank degree : ℕ) : ProbComp (RingBinarySecret rank degree) :=
  $ᵗ (RingBinarySecret rank degree)

/-- Gadget-scaled source-key messages in the native key-switch table layout. -/
def keySwitchMessages {R : Type} [Zero R] [One R] [Mul R]
    (sourceDimension keySwitchLevels : ℕ) (gadget : Fin keySwitchLevels → R)
    (sourceSecret : BinarySecret sourceDimension) :
    Fin (sourceDimension * keySwitchLevels) → R :=
  fun row ↦
    let indexed := finProdFinEquiv.symm row
    embedBit (sourceSecret indexed.1) * gadget indexed.2

/-- The native message at a selected key-switch table entry. -/
@[simp]
theorem keySwitchMessages_apply {R : Type} [Zero R] [One R] [Mul R]
    (sourceDimension keySwitchLevels : ℕ) (gadget : Fin keySwitchLevels → R)
    (sourceSecret : BinarySecret sourceDimension)
    (coordinate : Fin sourceDimension) (level : Fin keySwitchLevels) :
    keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret
        (finProdFinEquiv (coordinate, level)) =
      embedBit (sourceSecret coordinate) * gadget level := by
  simp [keySwitchMessages]

/-- Generate the real TFHE bootstrapping key: entry `i` is a native structured TRGSW encryption
of scalar secret bit `s_i` under the independently sampled ring key. -/
noncomputable def generateBootstrappingKey
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
  Fin.mOfFn lweDimension fun coordinate ↦
    TGSW.encrypt ringRank tgswLevels errorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate))

/-- Generate a format-identical bootstrapping key whose TRGSW messages are all zero. -/
noncomputable def generateZeroBootstrappingKey
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
  Fin.mOfFn lweDimension fun _ ↦
    TGSW.encryptZero ringRank tgswLevels errorSampler
      (embedRingSecret q ringSecret) gadget

/-- Generate the real TFHE key-switch key as direct fresh scalar TLWE rows encrypting gadget
multiples of the extracted ring-key coefficients under the scalar TLWE key. -/
def generateKeySwitchKey
    (q targetDimension sourceDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q)) (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension) :
    ProbComp (KeySwitchKey q targetDimension sourceDimension keySwitchLevels) :=
  TLWE.batchEncrypt targetDimension (sourceDimension * keySwitchLevels) errorSampler
    (embedBinarySecret targetSecret)
    (keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret)

/-- Generate a format-identical key-switch key whose direct TLWE messages are all zero. -/
def generateZeroKeySwitchKey
    (q targetDimension sourceDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (targetSecret : BinarySecret targetDimension) :
    ProbComp (KeySwitchKey q targetDimension sourceDimension keySwitchLevels) :=
  TLWE.batchEncrypt targetDimension (sourceDimension * keySwitchLevels) errorSampler
    (embedBinarySecret targetSecret) 0

/-- Generate both real native evaluation-key components for fixed scalar and ring secrets. -/
noncomputable def generateCloudKey
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (CloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let bootstrapKey ← generateBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget lweSecret ringSecret
  let switchKey ← generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret) lweSecret
  return ⟨bootstrapKey, switchKey⟩

/-- Generate the all-zero-message native evaluation-key hybrid for fixed secrets. -/
noncomputable def generateZeroCloudKey
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (CloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let bootstrapKey ← generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget ringSecret
  let switchKey ← generateZeroKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchErrorSampler lweSecret
  return ⟨bootstrapKey, switchKey⟩

/-- Concrete finite-modulus instantiation of the TFHE circular dependency graph. -/
noncomputable def nativeCycleSpec
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    Circular.CycleSpec
      (BinarySecret lweDimension)
      (RingBinarySecret ringRank degree)
      (BinarySecret (ringRank * degree))
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) where
  sampleLweSecret := sampleLweSecret lweDimension
  sampleRingSecret := sampleRingSecret ringRank degree
  extractRingSecret := keyExtract
  bootstrapReal := generateBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget
  bootstrapZero := generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget
  keySwitchReal := generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchErrorSampler keySwitchGadget
  keySwitchZero := generateZeroKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchErrorSampler

/-- Direct native sampler for the real cloud-key-only circular view. -/
noncomputable def realCloudKeyView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (Circular.View Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) := do
  let lweSecret ← sampleLweSecret lweDimension
  let ringSecret ← sampleRingSecret ringRank degree
  let cloudKey ← generateCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret ringSecret
  return ⟨(), cloudKey.bootstrappingKey, cloudKey.keySwitchKey⟩

/-- Direct native sampler for the all-zero-message cloud-key view. -/
noncomputable def zeroCloudKeyView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree) :
    ProbComp (Circular.View Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) := do
  let lweSecret ← sampleLweSecret lweDimension
  let ringSecret ← sampleRingSecret ringRank degree
  let cloudKey ← generateZeroCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget lweSecret ringSecret
  return ⟨(), cloudKey.bootstrappingKey, cloudKey.keySwitchKey⟩

/-- The abstract real circular view instantiated by `nativeCycleSpec` is exactly the direct native
TFHE cloud-key sampler. -/
theorem circular_realView_eq_native
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    Circular.realView
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload =
      realCloudKeyView q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget := by
  simp [Circular.realView, Circular.evaluationKeyOnlyPayload, nativeCycleSpec,
    realCloudKeyView, generateCloudKey, monad_norm]

/-- The abstract zero circular view instantiated by `nativeCycleSpec` is exactly the direct native
all-zero-message cloud-key sampler. -/
theorem circular_zeroView_eq_native
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    Circular.zeroView
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload =
      zeroCloudKeyView q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget := by
  simp [Circular.zeroView, Circular.evaluationKeyOnlyPayload, nativeCycleSpec,
    zeroCloudKeyView, generateZeroCloudKey, monad_norm]

end FormalProof4FHE.TFHE.Native
