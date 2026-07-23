/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.ConditionalSmudging
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAuxiliaryInput
import FormalProof4FHE.TFHE.NativeShiftedDiscreteGaussianBounds

/-!
# Statistical Smudging of the Complete One-Circular TFHE BRK

The real shared-randomness BRK and its zero-message comparison use the same hidden master key,
the same real suffix KSK, and the same continuation.  Their only row-level difference is the
native TGSW gadget phase.  For each fixed secret, that phase may be moved into the independently
sampled body error.  Data processing and the finite-product hybrid therefore bound the complete
real-versus-zero one-circular advantage by the sum of the error sampler's additive translation
costs over every BRK row.

This is a statistical proof for the actual self-key message, so it covers both the coefficient-
affine diagonal and the square-free outer-product table at once.  It is useful only when the row
error distribution is sufficiently shift tolerant.  In particular, the certified discrete-
Gaussian specialization below is a security-only endpoint and makes no correctness claim.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.CircularSmudging

noncomputable section

/-- A fixed TLWE message vector is equivalently a zero-message vector translated into the fresh
body-error vector. -/
theorem batchEncrypt_eq_batchEncryptWithResidual_zero
    {R : Type} [Fintype R] [DecidableEq R] [Semiring R] [SampleableType R]
    (dimension samples : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (message : Fin samples → R) :
    TLWE.batchEncrypt dimension samples errorSampler secret message =
      TLWE.batchEncryptWithResidual dimension samples errorSampler secret 0 message := by
  unfold TLWE.batchEncrypt TLWE.batchEncryptWithResidual
  congr 1
  funext challenge
  congr 1
  funext error
  congr 1
  apply Prod.ext
  · rfl
  · funext row
    simp [TLWE.batchAssemble, add_assoc]

/-- Rowwise message smudging for an arbitrary native TLWE batch. -/
theorem tvDist_batchEncrypt_message_zero_le_sum
    {R : Type} [Fintype R] [DecidableEq R] [Semiring R] [SampleableType R]
    (dimension samples : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (message : Fin samples → R) :
    tvDist
        (TLWE.batchEncrypt dimension samples errorSampler secret message)
        (TLWE.batchEncrypt dimension samples errorSampler secret 0) ≤
      ∑ row, FormalProof4FHE.FiniteProduct.addShiftDistance
        errorSampler (message row) := by
  rw [batchEncrypt_eq_batchEncryptWithResidual_zero]
  exact TLWE.tvDist_batchEncryptWithResidual_batchEncrypt_le_sum
    dimension samples errorSampler secret 0 message

/-- One native structured TGSW encryption is statistically close to its zero-message
counterpart whenever the row-error sampler is stable under every coordinate of its exact gadget
phase. -/
theorem tvDist_tgswEncrypt_encryptZero_le_sum
    {R : Type} [Fintype R] [DecidableEq R] [CommRing R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    tvDist
        (TGSW.encrypt dimension levels errorSampler secret gadget message)
        (TGSW.encryptZero dimension levels errorSampler secret gadget) ≤
      ∑ row, FormalProof4FHE.FiniteProduct.addShiftDistance
        errorSampler (TGSW.gadgetPhase secret gadget message row) := by
  have hreal := TGSW.encrypt_evalDist_eq_directEncrypt
    dimension levels errorSampler secret gadget message
  have hzero := TGSW.encrypt_evalDist_eq_directEncrypt
    dimension levels errorSampler secret gadget 0
  rw [show tvDist
        (TGSW.encrypt dimension levels errorSampler secret gadget message)
        (TGSW.encryptZero dimension levels errorSampler secret gadget) =
      tvDist
        (TGSW.directEncrypt dimension levels errorSampler secret gadget message)
        (TGSW.directEncrypt dimension levels errorSampler secret gadget 0) by
      unfold tvDist TGSW.encryptZero
      rw [hreal, hzero]]
  unfold TGSW.directEncrypt
  have hphaseZero : TGSW.gadgetPhase secret gadget 0 = 0 := by
    funext row
    simp [TGSW.gadgetPhase, TGSW.gadgetBodyShift, TGSW.gadgetMaskShift,
      Matrix.vecMul, dotProduct]
  rw [hphaseZero]
  exact tvDist_batchEncrypt_message_zero_le_sum
    dimension (TGSW.rowCount dimension levels) errorSampler secret
      (TGSW.gadgetPhase secret gadget message)

/-- Exact sum of all row-translation costs in the honest self-key BRK for one fixed master
secret. -/
noncomputable def bootstrappingMessageShiftCost
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) : ℝ :=
  ∑ coordinate, ∑ row,
    FormalProof4FHE.FiniteProduct.addShiftDistance ringErrorSampler
      (TGSW.gadgetPhase (embedRingSecret q ringSecret) tgswGadget
        (embedConstantBit q (prefixDimension + suffixDimension)
          (prefixSecret ringSecret coordinate)) row)

/-- For one fixed master secret, the complete real self-BRK is close to the native zero BRK by
the sum of the exact row-translation costs. -/
theorem tvDist_generateBootstrappingKey_zero_le_shiftCost
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    tvDist
        (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
          ringErrorSampler tgswGadget ringSecret)
        (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
          ringErrorSampler tgswGadget ringSecret) ≤
      bootstrappingMessageShiftCost q prefixDimension suffixDimension tgswLevels
        ringErrorSampler tgswGadget ringSecret := by
  letI : CommRing (RLWE.Rq q (prefixDimension + suffixDimension)) :=
    LatticeCrypto.vectorNegacyclicRing_instCommRing
      (ZMod q) (prefixDimension + suffixDimension)
  unfold generateBootstrappingKey generateZeroBootstrappingKey
    Native.generateBootstrappingKey Native.generateZeroBootstrappingKey
    bootstrappingMessageShiftCost
  calc
    tvDist
        (Fin.mOfFn prefixDimension fun coordinate ↦
          TGSW.encrypt 1 tgswLevels ringErrorSampler
            (embedRingSecret q ringSecret) tgswGadget
            (embedConstantBit q (prefixDimension + suffixDimension)
              (prefixSecret ringSecret coordinate)))
        (Fin.mOfFn prefixDimension fun _ ↦
          TGSW.encryptZero 1 tgswLevels ringErrorSampler
            (embedRingSecret q ringSecret) tgswGadget) ≤
      ∑ coordinate,
        tvDist
          (TGSW.encrypt 1 tgswLevels ringErrorSampler
            (embedRingSecret q ringSecret) tgswGadget
            (embedConstantBit q (prefixDimension + suffixDimension)
              (prefixSecret ringSecret coordinate)))
          (TGSW.encryptZero 1 tgswLevels ringErrorSampler
            (embedRingSecret q ringSecret) tgswGadget) :=
      FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum prefixDimension _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro coordinate _
      have h := tvDist_tgswEncrypt_encryptZero_le_sum
        1 tgswLevels ringErrorSampler
        (embedRingSecret q ringSecret) tgswGadget
        (embedConstantBit q (prefixDimension + suffixDimension)
          (prefixSecret ringSecret coordinate))
      simpa only [Native.ConditionalSmudging.addShiftDistance_rq_eq_executable] using h

/-- A uniform per-ring-shift translation bound yields a closed expression for the complete
BRK distance. -/
theorem tvDist_generateBootstrappingKey_zero_le_uniformRowBound
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (rowBound : ℝ)
    (hrow : ∀ shift : RLWE.Rq q (prefixDimension + suffixDimension),
      FormalProof4FHE.FiniteProduct.addShiftDistance ringErrorSampler shift ≤ rowBound) :
    tvDist
        (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
          ringErrorSampler tgswGadget ringSecret)
        (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
          ringErrorSampler tgswGadget ringSecret) ≤
      (prefixDimension : ℝ) * (TGSW.rowCount 1 tgswLevels : ℕ) * rowBound := by
  refine (tvDist_generateBootstrappingKey_zero_le_shiftCost q prefixDimension
    suffixDimension tgswLevels ringErrorSampler tgswGadget ringSecret).trans ?_
  unfold bootstrappingMessageShiftCost
  calc
    (∑ coordinate, ∑ row,
      FormalProof4FHE.FiniteProduct.addShiftDistance ringErrorSampler
        (TGSW.gadgetPhase (embedRingSecret q ringSecret) tgswGadget
          (embedConstantBit q (prefixDimension + suffixDimension)
            (prefixSecret ringSecret coordinate)) row)) ≤
      ∑ _coordinate : Fin prefixDimension,
        ∑ _row : Fin (TGSW.rowCount 1 tgswLevels), rowBound := by
      apply Finset.sum_le_sum
      intro coordinate _
      apply Finset.sum_le_sum
      intro row _
      exact hrow _
    _ = (prefixDimension : ℝ) * (TGSW.rowCount 1 tgswLevels : ℕ) * rowBound := by
      simp
      ring

/-- The complete real-versus-zero secret-continuation experiment is statistically bounded by
the same uniform row-translation cost.  The retained real KSK and every subsequent adaptive
operation are handled by data processing. -/
theorem secretContinuationAdvantage_le_uniformRowBound
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels)
    (rowBound : ℝ)
    (hrow : ∀ shift : RLWE.Rq q (prefixDimension + suffixDimension),
      FormalProof4FHE.FiniteProduct.addShiftDistance ringErrorSampler shift ≤ rowBound) :
    secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        continuation ≤
      (prefixDimension : ℝ) * (TGSW.rowCount 1 tgswLevels : ℕ) * rowBound := by
  let bound : ℝ :=
    (prefixDimension : ℝ) * (TGSW.rowCount 1 tgswLevels : ℕ) * rowBound
  let real := realSecretContinuationGame q prefixDimension suffixDimension tgswLevels
    keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    continuation
  let zero := bootstrapZeroSecretContinuationGame q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
    keySwitchGadget continuation
  have htv : tvDist real zero ≤ bound := by
    unfold real zero realSecretContinuationGame bootstrapZeroSecretContinuationGame
    refine tvDist_bind_left_le_const' (m := ProbComp)
      (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) _ _ bound ?_
    intro ringSecret
    let finish := fun bootstrappingKey ↦ do
      let keySwitchKey ← generateKeySwitchKey q prefixDimension suffixDimension
        keySwitchLevels keySwitchErrorSampler keySwitchGadget ringSecret
      continuation ringSecret bootstrappingKey keySwitchKey
    exact (tvDist_bind_right_le finish
      (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
        ringErrorSampler tgswGadget ringSecret)
      (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
        ringErrorSampler tgswGadget ringSecret)).trans
      (tvDist_generateBootstrappingKey_zero_le_uniformRowBound q prefixDimension
        suffixDimension tgswLevels ringErrorSampler tgswGadget ringSecret rowBound hrow)
  exact (abs_probOutput_toReal_sub_le_tvDist real zero).trans htv

/-! ## Certified discrete-Gaussian specialization -/

/-- Universal per-row translation bound for a coefficientwise certified discrete Gaussian.
The `q / 2` factor is unavoidable in this worst-case security-only statement because an exact
native gadget phase may occupy any centered residue. -/
noncomputable def discreteGaussianUniversalRowBound
    (q degree : ℕ) [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha) : ℝ :=
  (degree : ℝ) *
    DiscreteGaussianSampler.scalarLinearShiftBound certificate (q / 2)

/-- Every native ring shift is covered by the universal certified-Gaussian row bound. -/
theorem addShiftDistance_discreteGaussian_le_universalRowBound
    (q degree : ℕ) [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (shift : RLWE.Rq q degree) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (DiscreteGaussianSampler.ringSampler degree certificate) shift ≤
      discreteGaussianUniversalRowBound q degree certificate := by
  exact DiscreteGaussianSampler.addShiftDistance_ringSampler_le_degree_mul_scalarLinearShiftBound
    degree certificate (q / 2) shift (LatticeCrypto.cInfNorm_le_halfq shift)

/-- The same universal translation estimate also bounds distance from exact uniform.  Averaging
all additive translates of the executable Gaussian produces the uniform ring distribution, so
no separate zero-BRK side-information assumption is needed in the sufficiently wide regime. -/
theorem tvDist_discreteGaussian_uniform_le_universalRowBound
    (q degree : ℕ) [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha) :
    tvDist
        (DiscreteGaussianSampler.ringSampler degree certificate)
        ($ᵗ (RLWE.Rq q degree)) ≤
      discreteGaussianUniversalRowBound q degree certificate := by
  apply FormalProof4FHE.FiniteProduct.tvDist_uniform_le_of_addShiftDistance_le
  · simp [DiscreteGaussianSampler.ringSampler,
      DiscreteGaussianSampler.scalarSampler]
  · exact addShiftDistance_discreteGaussian_le_universalRowBound
      q degree certificate

/-- Concrete statistical bound for the actual one-circular secret-continuation advantage under
the certified coefficientwise discrete-Gaussian BRK sampler. -/
theorem secretContinuationAdvantage_discreteGaussian_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels
        keySwitchLevels
        (DiscreteGaussianSampler.ringSampler (prefixDimension + suffixDimension) certificate)
        keySwitchErrorSampler tgswGadget keySwitchGadget continuation ≤
      (prefixDimension : ℝ) * (TGSW.rowCount 1 tgswLevels : ℕ) *
        discreteGaussianUniversalRowBound q (prefixDimension + suffixDimension)
          certificate := by
  apply secretContinuationAdvantage_le_uniformRowBound
  exact addShiftDistance_discreteGaussian_le_universalRowBound
    q (prefixDimension + suffixDimension) certificate

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.CircularSmudging
