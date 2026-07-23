/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialCorrectness
import FormalProof4FHE.TFHE.MonomialKDM
import FormalProof4FHE.TFHE.NativeShiftedResidualBounds

/-!
# Centered-Binomial Bounds under Native Scalar-Key Transport

This module proves the support fact needed by a tight shifted-candidate smudging argument.
Transporting a native bootstrapping key by a scalar XOR mask changes each TGSW row error only by
sign when it is measured against the fully transported scalar secret and the unchanged ring
secret.  Thus a source key generated with centered-binomial width `eta` retains the same exact
row bound after transport.

The theorem deliberately couples the target scalar and ring secrets to the source key.  It does
not apply to an independently resampled target secret pair; that proof boundary uses the
universal modular fallback in `NativeShiftedResidualBounds`.
-/

open Matrix

namespace FormalProof4FHE.TFHE.Native.ShiftedResidualBounds

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Row-error identity for one entry of a scalar-XOR-transported bootstrapping key. -/
theorem rowError_transformBootstrappingKey
    {q degree ringRank levels lweDimension : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (ringSecret : Fin ringRank → RLWE.Rq q (degree + 1))
    (sourceSecret mask : BinarySecret lweDimension)
    (bootstrappingKey :
      BootstrappingKey q (degree + 1) ringRank levels lweDimension)
    (coordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin levels) :
    TGSW.rowError ringSecret gadget
        (embedBit (ScalarSecretRandomization.maskedSecret sourceSecret mask coordinate))
        (ScalarSecretRandomization.transformBootstrappingKey
          gadget mask bootstrappingKey coordinate) index =
      if mask coordinate then
        ShiftedCandidateEvaluator.proofNeg
          (TGSW.rowError ringSecret gadget (embedBit (sourceSecret coordinate))
            (bootstrappingKey coordinate) index)
      else
        TGSW.rowError ringSecret gadget (embedBit (sourceSecret coordinate))
          (bootstrappingKey coordinate) index := by
  change TGSW.rowError ringSecret gadget
      (embedBit (LWE.MultiKeyAffine.maskedBit
        (sourceSecret coordinate) (mask coordinate)))
      (ScalarSecretRandomization.toggleTGSW gadget
        (mask coordinate) (bootstrappingKey coordinate)) index = _
  simpa only [ShiftedCandidateEvaluator.proofNeg] using
    rowError_toggleTGSW ringSecret gadget (sourceSecret coordinate)
      (mask coordinate) (bootstrappingKey coordinate) index

/-- Any source row norm bound is preserved exactly by scalar-key transport. -/
theorem cInfNorm_transformBootstrappingKey_rowError_le
    {q degree ringRank levels lweDimension eta : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (ringSecret : Fin ringRank → RLWE.Rq q (degree + 1))
    (sourceSecret mask : BinarySecret lweDimension)
    (bootstrappingKey :
      BootstrappingKey q (degree + 1) ringRank levels lweDimension)
    (coordinate : Fin lweDimension)
    (hsource : ∀ index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret gadget
        (embedBit (sourceSecret coordinate)) (bootstrappingKey coordinate) index) ≤ eta) :
    ∀ index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret gadget
        (embedBit
          (ScalarSecretRandomization.maskedSecret sourceSecret mask coordinate))
        (ScalarSecretRandomization.transformBootstrappingKey
          gadget mask bootstrappingKey coordinate) index) ≤ eta := by
  intro index
  rw [rowError_transformBootstrappingKey gadget ringSecret sourceSecret mask
    bootstrappingKey coordinate index]
  split_ifs
  · simpa only [cInfNorm_proofNeg] using hsource index
  · exact hsource index

/-- A supported centered-binomial native BRK retains width `eta` after public scalar transport,
when evaluated under its fully transported scalar secret and unchanged ring secret. -/
theorem cInfNorm_transformBootstrappingKey_generate_centeredBinomial_le_eta
    {q degree ringRank levels lweDimension eta : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (sourceSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    {bootstrappingKey :
      BootstrappingKey q (degree + 1) ringRank levels lweDimension}
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey q (degree + 1) ringRank levels lweDimension
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        gadget sourceSecret ringSecret))
    (coordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin levels) :
    LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1))
        (embedRingSecret q ringSecret) gadget
        (embedBit
          (ScalarSecretRandomization.maskedSecret sourceSecret mask coordinate))
        (ScalarSecretRandomization.transformBootstrappingKey
          gadget mask bootstrappingKey coordinate) index) ≤ eta := by
  apply cInfNorm_transformBootstrappingKey_rowError_le gadget
    (embedRingSecret q ringSecret) sourceSecret mask bootstrappingKey coordinate
  intro sourceIndex
  simpa only [BlindRotation.embedConstantBit_eq_embedBit] using
    (CenteredBinomialCorrectness.cInfNorm_bootstrappingKey_rowError_le_eta
      gadget sourceSecret ringSecret hkey coordinate sourceIndex)

/-- The same transported row bound holds for the exact monomial-KDM source sampler used by the
public auxiliary-input circular-search problem.  Its support is transferred through the checked
distribution equality with the native structured generator. -/
theorem cInfNorm_transformMonomialBootstrappingKey_centeredBinomial_le_eta
    {q degree ringRank levels lweDimension eta : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (sourceSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    {bootstrappingKey :
      BootstrappingKey q (degree + 1) ringRank levels lweDimension}
    (hkey : bootstrappingKey ∈ support
      (Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
        q (degree + 1) ringRank levels lweDimension
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        gadget sourceSecret ringSecret))
    (coordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin levels) :
    LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1))
        (embedRingSecret q ringSecret) gadget
        (embedBit
          (ScalarSecretRandomization.maskedSecret sourceSecret mask coordinate))
        (ScalarSecretRandomization.transformBootstrappingKey
          gadget mask bootstrappingKey coordinate) index) ≤ eta := by
  apply cInfNorm_transformBootstrappingKey_generate_centeredBinomial_le_eta
    gadget sourceSecret mask ringSecret
  have hdistribution :
      evalDist
          (Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
            q (degree + 1) ringRank levels lweDimension
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            gadget sourceSecret ringSecret) =
        evalDist
          (Native.generateBootstrappingKey q (degree + 1) ringRank levels lweDimension
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            gadget sourceSecret ringSecret) := by
    rw [Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct]
    exact (Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
      q (degree + 1) ringRank levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      gadget sourceSecret ringSecret).symm
  exact (mem_support_iff_of_evalDist_eq hdistribution bootstrappingKey).mp hkey

end

end FormalProof4FHE.TFHE.Native.ShiftedResidualBounds
