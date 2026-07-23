/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharpRotationNoise

/-!
# Quantitative TFHE Bootstrapping Correctness

This file turns the exact blind-rotation and sample-extraction identities into deterministic
correctness theorems.  The compatibility API retains the original fully checked schoolbook bound,
where a trace of `m` rotations carries a factor `N² ^ m`.  The sharp API uses
`TFHE.SharpRotationNoise`: native signed-monomial rotations act as signed coefficient
permutations, `(X^a - 1)` costs at most twice the input norm, and digit-row convolution has an
`N`-term coefficient bound.  Historical errors are therefore charged only once and the trace
budget is linear in `m`.  The one-step budget retains a deterministic worst-case sum over all
gadget rows and digits.

The final theorem isolates the two inputs that a concrete TFHE parameter proof must discharge:

* every bootstrapping-key row error is within the advertised bound; and
* the ideal rotated test-vector coefficient is the desired encoded output bit.

Given those facts and a strict codeword-separation margin, the extracted TLWE phase decrypts to the
desired bit.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.BootstrappingCorrectness

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-! ## Norms of the ideal blind-rotation selectors -/

/-- The conservative cost used for one executable negacyclic product at ring degree `N`. -/
def convolutionCost (degree : ℕ) : ℕ :=
  (degree + 1) * (degree + 1)

/-- The proof-facing positive-degree ring zero has zero centered infinity norm. -/
@[simp]
theorem cInfNorm_rq_zero {q degree : ℕ} [NeZero q] :
    LatticeCrypto.cInfNorm (0 : RLWE.Rq q (degree + 1)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  have hzero := BlindRotation.rq_zero_coefficient (q := q) (degree := degree) coefficient
  change (0 : RLWE.Rq q (degree + 1)).get coefficient = 0 at hzero
  rw [hzero]
  simp [LatticeCrypto.centeredRepr_eq_valMinAbs]

/-- The positive-degree executable ring unit has centered coefficient infinity norm at most one. -/
theorem cInfNorm_one_le {q degree : ℕ} [NeZero q] :
    LatticeCrypto.cInfNorm (1 : RLWE.Rq q (degree + 1)) ≤ 1 := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  have hone := BlindRotation.rq_one_coefficient (q := q) (degree := degree) coefficient
  change (1 : RLWE.Rq q (degree + 1)).get coefficient = _ at hone
  rw [hone]
  split_ifs
  · simpa using NoiseBounds.centeredRepr_natCast_natAbs_le (q := q) 1
  · simp [LatticeCrypto.centeredRepr_eq_valMinAbs]

/-- Every executable signed rotation monomial has centered infinity norm at most one. -/
theorem cInfNorm_rotationMonomial_le {q degree : ℕ} [NeZero q]
    (exponent : Fin (2 * (degree + 1))) :
    LatticeCrypto.cInfNorm (BlindRotation.rotationMonomial q degree exponent) ≤ 1 := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  have hcoefficient :=
    BlindRotation.rotationMonomial_coefficient q degree exponent coefficient
  change (BlindRotation.rotationMonomial q degree exponent).get coefficient = _ at hcoefficient
  rw [hcoefficient]
  split_ifs
  · simpa using NoiseBounds.centeredRepr_natCast_natAbs_le (q := q) 1
  · simp [LatticeCrypto.centeredRepr_eq_valMinAbs]
  · rw [LatticeCrypto.centeredRepr_natAbs_neg]
    simpa using NoiseBounds.centeredRepr_natCast_natAbs_le (q := q) 1
  · simp [LatticeCrypto.centeredRepr_eq_valMinAbs]

/-- Subtracting the ring unit from a signed rotation monomial costs at most two. -/
theorem cInfNorm_rotationMonomial_sub_one_le_two {q degree : ℕ} [NeZero q]
    (exponent : Fin (2 * (degree + 1))) :
    LatticeCrypto.cInfNorm
        (BlindRotation.rotationMonomial q degree exponent -
          (1 : RLWE.Rq q (degree + 1))) ≤ 2 := by
  exact (NoiseBounds.cInfNorm_sub_le
      (BlindRotation.rotationMonomial q degree exponent)
      (1 : RLWE.Rq q (degree + 1))).trans
    (Nat.add_le_add (cInfNorm_rotationMonomial_le exponent)
      (cInfNorm_one_le (q := q) (degree := degree)))

/-- Selecting either a norm-one public factor or the ring unit preserves the norm-one bound. -/
theorem cInfNorm_selectedFactor_le {q degree rank levels : ℕ} [NeZero q]
    (control : BlindRotation.BitControl q degree rank levels)
    (hfactor : LatticeCrypto.cInfNorm control.factor ≤ 1) :
    LatticeCrypto.cInfNorm
        (if control.bit then control.factor else (1 : RLWE.Rq q (degree + 1))) ≤ 1 := by
  cases hbit : control.bit
  · simpa only [hbit, Bool.false_eq_true, ↓reduceIte] using
      (cInfNorm_one_le (q := q) (degree := degree))
  · simpa only [hbit, ↓reduceIte] using hfactor

/-- A product of `m` norm-one selectors has the checked conservative bound `(N²)^m`. -/
theorem cInfNorm_idealMultiplier_le_pow {q degree rank levels : ℕ} [NeZero q]
    (controls : List (BlindRotation.BitControl q degree rank levels))
    (hfactor : ∀ control ∈ controls, LatticeCrypto.cInfNorm control.factor ≤ 1) :
    LatticeCrypto.cInfNorm (BlindRotation.idealMultiplier controls) ≤
      convolutionCost degree ^ controls.length := by
  induction controls with
  | nil =>
      simpa [BlindRotation.idealMultiplier, convolutionCost] using
        (cInfNorm_one_le (q := q) (degree := degree))
  | cons control controls ih =>
      have hhead : LatticeCrypto.cInfNorm control.factor ≤ 1 := hfactor control (by simp)
      have htail : ∀ item ∈ controls, LatticeCrypto.cInfNorm item.factor ≤ 1 := by
        intro item hmem
        exact hfactor item (by simp [hmem])
      have hselected := cInfNorm_selectedFactor_le control hhead
      calc
        LatticeCrypto.cInfNorm
            (BlindRotation.idealMultiplier (control :: controls)) =
            LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                (if control.bit then control.factor
                  else (1 : RLWE.Rq q (degree + 1)))) := by
              rfl
        _ ≤ convolutionCost degree *
              (LatticeCrypto.cInfNorm (BlindRotation.idealMultiplier controls) *
                LatticeCrypto.cInfNorm
                  (if control.bit then control.factor
                    else (1 : RLWE.Rq q (degree + 1)))) := by
              unfold convolutionCost
              convert NoiseBounds.cInfNorm_mul_le
                (BlindRotation.idealMultiplier controls)
                (if control.bit then control.factor
                  else (1 : RLWE.Rq q (degree + 1))) using 1
              rfl
        _ ≤ convolutionCost degree *
              (convolutionCost degree ^ controls.length * 1) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (ih htail) hselected)
        _ = convolutionCost degree ^ (control :: controls).length := by
            simp [pow_succ, Nat.mul_comm]

/-! ## One-step and trace budgets -/

/-- Worst-case error budget for the digit-weighted row errors in one external product. -/
def externalProductNoiseBudget
    (degree rank levels digitBound rowErrorBound : ℕ) : ℕ :=
  ((rank + 1) * levels) *
    (convolutionCost degree * (digitBound * rowErrorBound))

/-- Sharper external-product budget obtained from the executable `N`-term convolution formula. -/
def linearExternalProductNoiseBudget
    (degree rank levels digitBound rowErrorBound : ℕ) : ℕ :=
  ((rank + 1) * levels) *
    ((degree + 1) * (digitBound * rowErrorBound))

/-- Worst-case error budget for one blind-rotation step, including multiplication by `factor-1`. -/
def stepNoiseBudget
    (degree rank levels digitBound factorBound rowErrorBound : ℕ) : ℕ :=
  convolutionCost degree *
    (factorBound *
      externalProductNoiseBudget degree rank levels digitBound rowErrorBound)

/-- Conservative geometric budget for a trace of norm-one selectors with uniformly bounded
steps.  The newest contribution in a trace of length `m` is charged `(N²)^m`. -/
def traceNoiseBudget (degree : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | steps + 1, oneStepBound =>
      convolutionCost degree ^ (steps + 1) * oneStepBound +
        traceNoiseBudget degree steps oneStepBound

/-- Native blind-rotation budget with coefficient digits bounded by `base - 1` and monomial
differences bounded by two. -/
def nativeNoiseBudget
    (degree rank levels base lweDimension rowErrorBound : ℕ) : ℕ :=
  traceNoiseBudget degree lweDimension
    (stepNoiseBudget degree rank levels (base - 1) 2 rowErrorBound)

/-- Native trace budget after exploiting both sparse signed-rotation operations: later ideal
selectors preserve infinity norm, and the current `(X^a - 1)` factor costs at most two.  The
digit-weighted external product uses the executable linear convolution bound. -/
def nativeLinearNoiseBudget
    (degree rank levels base lweDimension rowErrorBound : ℕ) : ℕ :=
  lweDimension *
    (2 * linearExternalProductNoiseBudget degree rank levels
      (base - 1) rowErrorBound)

/-- One concrete blind-rotation step satisfies `stepNoiseBudget`. -/
theorem cInfNorm_stepError_le
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (accumulator : RingCiphertext q (degree + 1) rank)
    (control : BlindRotation.BitControl q degree rank params.levels)
    (factorBound rowErrorBound : ℕ)
    (hfactor : LatticeCrypto.cInfNorm (control.factor - 1) ≤ factorBound)
    (hrows : ∀ index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) control.bit)
        control.bootstrapKeyEntry index) ≤ rowErrorBound) :
    LatticeCrypto.cInfNorm
        (BlindRotation.stepError params secret accumulator control) ≤
      stepNoiseBudget degree rank params.levels (params.base - 1)
        factorBound rowErrorBound := by
  unfold BlindRotation.stepError stepNoiseBudget externalProductNoiseBudget convolutionCost
  exact (NoiseBounds.cInfNorm_mul_le (control.factor - 1)
      (TGSW.externalProductError secret (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) control.bit)
        (Gadget.Base.ringExtendedDigits params accumulator) control.bootstrapKeyEntry)).trans
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul hfactor
      (NoiseBounds.cInfNorm_externalProductError_ringDigits_le params secret
        (embedConstantBit q (degree + 1) control.bit) accumulator
        control.bootstrapKeyEntry rowErrorBound hrows)))

/-- One native signed-rotation step satisfies the sharp linear-convolution budget. -/
theorem cInfNorm_nativeStepError_le_linear
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (accumulator : RingCiphertext q (degree + 1) rank)
    (control : BlindRotation.BitControl q degree rank params.levels)
    (exponent : Fin (2 * (degree + 1)))
    (hfactor : control.factor =
      BlindRotation.rotationMonomial q degree exponent)
    (rowErrorBound : ℕ)
    (hrows : ∀ index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) control.bit)
        control.bootstrapKeyEntry index) ≤ rowErrorBound) :
    LatticeCrypto.cInfNorm
        (BlindRotation.stepError params secret accumulator control) ≤
      2 * linearExternalProductNoiseBudget degree rank params.levels
        (params.base - 1) rowErrorBound := by
  unfold BlindRotation.stepError
  rw [hfactor]
  have hexternal :=
    SharpRotationNoise.cInfNorm_externalProductError_ringDigits_le_linear
      params secret (embedConstantBit q (degree + 1) control.bit)
      accumulator control.bootstrapKeyEntry rowErrorBound hrows
  exact (SharpRotationNoise.cInfNorm_rotationMonomial_sub_one_mul_le_two
      exponent
      (TGSW.externalProductError secret (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) control.bit)
        (Gadget.Base.ringExtendedDigits params accumulator)
        control.bootstrapKeyEntry)).trans
    (by
      simpa only [linearExternalProductNoiseBudget] using
        Nat.mul_le_mul_left 2 hexternal)

/-- The exact accumulated blind-rotation error is bounded by the geometric trace budget whenever
all public factors, factor differences, and TGSW row errors satisfy uniform bounds. -/
theorem cInfNorm_accumulatedError_le
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (accumulator : RingCiphertext q (degree + 1) rank)
    (controls : List (BlindRotation.BitControl q degree rank params.levels))
    (factorBound rowErrorBound : ℕ)
    (hfactor : ∀ control ∈ controls,
      LatticeCrypto.cInfNorm control.factor ≤ 1)
    (hfactorSub : ∀ control ∈ controls,
      LatticeCrypto.cInfNorm (control.factor - 1) ≤ factorBound)
    (hrows : ∀ control ∈ controls, ∀ index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) control.bit)
          control.bootstrapKeyEntry index) ≤ rowErrorBound) :
    LatticeCrypto.cInfNorm
        (BlindRotation.accumulatedError params secret accumulator controls) ≤
      traceNoiseBudget degree controls.length
        (stepNoiseBudget degree rank params.levels (params.base - 1)
          factorBound rowErrorBound) := by
  induction controls generalizing accumulator with
  | nil =>
      simp [BlindRotation.accumulatedError, traceNoiseBudget]
  | cons control controls ih =>
      have hheadFactor : LatticeCrypto.cInfNorm control.factor ≤ 1 :=
        hfactor control (by simp)
      have htailFactor : ∀ item ∈ controls,
          LatticeCrypto.cInfNorm item.factor ≤ 1 := by
        intro item hmem
        exact hfactor item (by simp [hmem])
      have hheadFactorSub :
          LatticeCrypto.cInfNorm (control.factor - 1) ≤ factorBound :=
        hfactorSub control (by simp)
      have htailFactorSub : ∀ item ∈ controls,
          LatticeCrypto.cInfNorm (item.factor - 1) ≤ factorBound := by
        intro item hmem
        exact hfactorSub item (by simp [hmem])
      have hheadRows : ∀ index,
          LatticeCrypto.cInfNorm
            (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
              (Gadget.Base.ringGadget params)
              (embedConstantBit q (degree + 1) control.bit)
              control.bootstrapKeyEntry index) ≤ rowErrorBound :=
        hrows control (by simp)
      have htailRows : ∀ item ∈ controls, ∀ index,
          LatticeCrypto.cInfNorm
            (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
              (Gadget.Base.ringGadget params)
              (embedConstantBit q (degree + 1) item.bit)
              item.bootstrapKeyEntry index) ≤ rowErrorBound := by
        intro item hmem index
        exact hrows item (by simp [hmem]) index
      have hideal := cInfNorm_idealMultiplier_le_pow controls htailFactor
      have hstep := cInfNorm_stepError_le params secret accumulator control
        factorBound rowErrorBound hheadFactorSub hheadRows
      have hterm :
          LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control) ≤
            convolutionCost degree ^ (controls.length + 1) *
              stepNoiseBudget degree rank params.levels (params.base - 1)
                factorBound rowErrorBound := by
        calc
          LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control) ≤
              convolutionCost degree *
                (LatticeCrypto.cInfNorm (BlindRotation.idealMultiplier controls) *
                  LatticeCrypto.cInfNorm
                    (BlindRotation.stepError params secret accumulator control)) := by
            unfold convolutionCost
            convert NoiseBounds.cInfNorm_mul_le
              (BlindRotation.idealMultiplier controls)
              (BlindRotation.stepError params secret accumulator control) using 1
          _ ≤ convolutionCost degree *
                (convolutionCost degree ^ controls.length *
                  stepNoiseBudget degree rank params.levels (params.base - 1)
                    factorBound rowErrorBound) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hideal hstep)
          _ = convolutionCost degree ^ (controls.length + 1) *
                stepNoiseBudget degree rank params.levels (params.base - 1)
                  factorBound rowErrorBound := by
            simp [pow_succ, Nat.mul_assoc, Nat.mul_comm]
      have htail := ih
        (BlindRotation.step params control.factor control.bootstrapKeyEntry accumulator)
        htailFactor htailFactorSub htailRows
      calc
        LatticeCrypto.cInfNorm
            (BlindRotation.accumulatedError params secret accumulator
              (control :: controls)) =
            LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                  BlindRotation.stepError params secret accumulator control +
                BlindRotation.accumulatedError params secret
                  (BlindRotation.step params control.factor
                    control.bootstrapKeyEntry accumulator) controls) := by
              rfl
        _ ≤ LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control) +
            LatticeCrypto.cInfNorm
              (BlindRotation.accumulatedError params secret
                (BlindRotation.step params control.factor
                  control.bootstrapKeyEntry accumulator) controls) := by
            convert NoiseBounds.cInfNorm_add_le
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control)
              (BlindRotation.accumulatedError params secret
                (BlindRotation.step params control.factor
                  control.bootstrapKeyEntry accumulator) controls) using 1
        _ ≤ convolutionCost degree ^ (controls.length + 1) *
              stepNoiseBudget degree rank params.levels (params.base - 1)
                factorBound rowErrorBound +
            traceNoiseBudget degree controls.length
              (stepNoiseBudget degree rank params.levels (params.base - 1)
                factorBound rowErrorBound) :=
          Nat.add_le_add hterm htail
        _ = traceNoiseBudget degree (control :: controls).length
              (stepNoiseBudget degree rank params.levels (params.base - 1)
                factorBound rowErrorBound) := by
          rfl

/-- Generic linear trace lemma for native signed rotations once a uniform one-step bound has
been established.  Later selectors preserve the norm of each earlier step contribution. -/
theorem cInfNorm_accumulatedError_le_signedRotations_of_step
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (accumulator : RingCiphertext q (degree + 1) rank)
    (controls : List (BlindRotation.BitControl q degree rank params.levels))
    (oneStepBound : ℕ)
    (hrotation : ∀ control ∈ controls,
      ∃ exponent : Fin (2 * (degree + 1)),
        control.factor = BlindRotation.rotationMonomial q degree exponent)
    (hstep : ∀ control ∈ controls, ∀ currentAccumulator,
      LatticeCrypto.cInfNorm
          (BlindRotation.stepError params secret currentAccumulator control) ≤
        oneStepBound) :
    LatticeCrypto.cInfNorm
        (BlindRotation.accumulatedError params secret accumulator controls) ≤
      controls.length * oneStepBound := by
  induction controls generalizing accumulator with
  | nil =>
      simp [BlindRotation.accumulatedError]
  | cons control controls ih =>
      have htailRotation : ∀ item ∈ controls,
          ∃ exponent : Fin (2 * (degree + 1)),
            item.factor = BlindRotation.rotationMonomial q degree exponent := by
        intro item hmem
        exact hrotation item (by simp [hmem])
      have hheadStep :
          LatticeCrypto.cInfNorm
              (BlindRotation.stepError params secret accumulator control) ≤
            oneStepBound :=
        hstep control (by simp) accumulator
      have htailStep : ∀ item ∈ controls, ∀ currentAccumulator,
          LatticeCrypto.cInfNorm
              (BlindRotation.stepError params secret currentAccumulator item) ≤
            oneStepBound := by
        intro item hmem currentAccumulator
        exact hstep item (by simp [hmem]) currentAccumulator
      have hterm :
          LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control) ≤
            oneStepBound :=
        (SharpRotationNoise.cInfNorm_idealMultiplier_mul_le controls htailRotation
          (BlindRotation.stepError params secret accumulator control)).trans hheadStep
      have htail := ih
        (BlindRotation.step params control.factor control.bootstrapKeyEntry accumulator)
        htailRotation htailStep
      calc
        LatticeCrypto.cInfNorm
            (BlindRotation.accumulatedError params secret accumulator
              (control :: controls)) =
            LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                  BlindRotation.stepError params secret accumulator control +
                BlindRotation.accumulatedError params secret
                  (BlindRotation.step params control.factor
                    control.bootstrapKeyEntry accumulator) controls) := by
              rfl
        _ ≤ LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control) +
            LatticeCrypto.cInfNorm
              (BlindRotation.accumulatedError params secret
                (BlindRotation.step params control.factor
                  control.bootstrapKeyEntry accumulator) controls) := by
            convert NoiseBounds.cInfNorm_add_le
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control)
              (BlindRotation.accumulatedError params secret
                (BlindRotation.step params control.factor
                  control.bootstrapKeyEntry accumulator) controls) using 1
        _ ≤ oneStepBound + controls.length * oneStepBound :=
          Nat.add_le_add hterm htail
        _ = (control :: controls).length * oneStepBound := by
          simp [Nat.add_mul, Nat.add_comm]

/-- Accumulated-error bound for traces whose public factors are native signed rotations.  The
ideal multiplier acts by successive coefficient permutations, so every historical step error is
charged once rather than multiplied by `(N²)^remainingSteps`. -/
theorem cInfNorm_accumulatedError_le_signedRotations
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (accumulator : RingCiphertext q (degree + 1) rank)
    (controls : List (BlindRotation.BitControl q degree rank params.levels))
    (factorBound rowErrorBound : ℕ)
    (hrotation : ∀ control ∈ controls,
      ∃ exponent : Fin (2 * (degree + 1)),
        control.factor = BlindRotation.rotationMonomial q degree exponent)
    (hfactorSub : ∀ control ∈ controls,
      LatticeCrypto.cInfNorm (control.factor - 1) ≤ factorBound)
    (hrows : ∀ control ∈ controls, ∀ index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) control.bit)
          control.bootstrapKeyEntry index) ≤ rowErrorBound) :
    LatticeCrypto.cInfNorm
        (BlindRotation.accumulatedError params secret accumulator controls) ≤
      controls.length *
        stepNoiseBudget degree rank params.levels (params.base - 1)
          factorBound rowErrorBound := by
  induction controls generalizing accumulator with
  | nil =>
      simp [BlindRotation.accumulatedError]
  | cons control controls ih =>
      have htailRotation : ∀ item ∈ controls,
          ∃ exponent : Fin (2 * (degree + 1)),
            item.factor = BlindRotation.rotationMonomial q degree exponent := by
        intro item hmem
        exact hrotation item (by simp [hmem])
      have hheadFactorSub :
          LatticeCrypto.cInfNorm (control.factor - 1) ≤ factorBound :=
        hfactorSub control (by simp)
      have htailFactorSub : ∀ item ∈ controls,
          LatticeCrypto.cInfNorm (item.factor - 1) ≤ factorBound := by
        intro item hmem
        exact hfactorSub item (by simp [hmem])
      have hheadRows : ∀ index,
          LatticeCrypto.cInfNorm
            (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
              (Gadget.Base.ringGadget params)
              (embedConstantBit q (degree + 1) control.bit)
              control.bootstrapKeyEntry index) ≤ rowErrorBound :=
        hrows control (by simp)
      have htailRows : ∀ item ∈ controls, ∀ index,
          LatticeCrypto.cInfNorm
            (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
              (Gadget.Base.ringGadget params)
              (embedConstantBit q (degree + 1) item.bit)
              item.bootstrapKeyEntry index) ≤ rowErrorBound := by
        intro item hmem index
        exact hrows item (by simp [hmem]) index
      have hstep := cInfNorm_stepError_le params secret accumulator control
        factorBound rowErrorBound hheadFactorSub hheadRows
      have hterm :
          LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control) ≤
            stepNoiseBudget degree rank params.levels (params.base - 1)
              factorBound rowErrorBound :=
        (SharpRotationNoise.cInfNorm_idealMultiplier_mul_le controls htailRotation
          (BlindRotation.stepError params secret accumulator control)).trans hstep
      have htail := ih
        (BlindRotation.step params control.factor control.bootstrapKeyEntry accumulator)
        htailRotation htailFactorSub htailRows
      calc
        LatticeCrypto.cInfNorm
            (BlindRotation.accumulatedError params secret accumulator
              (control :: controls)) =
            LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                  BlindRotation.stepError params secret accumulator control +
                BlindRotation.accumulatedError params secret
                  (BlindRotation.step params control.factor
                    control.bootstrapKeyEntry accumulator) controls) := by
              rfl
        _ ≤ LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control) +
            LatticeCrypto.cInfNorm
              (BlindRotation.accumulatedError params secret
                (BlindRotation.step params control.factor
                  control.bootstrapKeyEntry accumulator) controls) := by
            convert NoiseBounds.cInfNorm_add_le
              (BlindRotation.idealMultiplier controls *
                BlindRotation.stepError params secret accumulator control)
              (BlindRotation.accumulatedError params secret
                (BlindRotation.step params control.factor
                  control.bootstrapKeyEntry accumulator) controls) using 1
        _ ≤ stepNoiseBudget degree rank params.levels (params.base - 1)
              factorBound rowErrorBound +
            controls.length *
              stepNoiseBudget degree rank params.levels (params.base - 1)
                factorBound rowErrorBound :=
          Nat.add_le_add hterm htail
        _ = (control :: controls).length *
              stepNoiseBudget degree rank params.levels (params.base - 1)
                factorBound rowErrorBound := by
          simp [Nat.add_mul, Nat.add_comm]

/-- Native `X^{-a_i}` controls instantiate the generic trace theorem with factor norm one and
`factor - 1` norm at most two. -/
theorem cInfNorm_nativeAccumulatedError_le
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank)
    (rowErrorBound : ℕ)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound) :
    LatticeCrypto.cInfNorm
        (BlindRotation.accumulatedError params ringSecret initialAccumulator
          (BlindRotation.nativeControls params roundExponent input
            bootstrappingKey lweSecret)) ≤
      traceNoiseBudget degree lweDimension
        (stepNoiseBudget degree rank params.levels (params.base - 1) 2 rowErrorBound) := by
  let controls := BlindRotation.nativeControls params roundExponent input
    bootstrappingKey lweSecret
  have hfactor : ∀ control ∈ controls,
      LatticeCrypto.cInfNorm control.factor ≤ 1 := by
    unfold controls BlindRotation.nativeControls
    rw [List.forall_mem_ofFn_iff]
    intro coordinate
    exact cInfNorm_rotationMonomial_le _
  have hfactorSub : ∀ control ∈ controls,
      LatticeCrypto.cInfNorm (control.factor - 1) ≤ 2 := by
    unfold controls BlindRotation.nativeControls
    rw [List.forall_mem_ofFn_iff]
    intro coordinate
    exact cInfNorm_rotationMonomial_sub_one_le_two _
  have hcontrolRows : ∀ control ∈ controls, ∀ index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) control.bit)
          control.bootstrapKeyEntry index) ≤ rowErrorBound := by
    unfold controls BlindRotation.nativeControls
    rw [List.forall_mem_ofFn_iff]
    intro coordinate index
    exact hrows coordinate index
  simpa only [controls, BlindRotation.nativeControls, List.length_ofFn] using
    cInfNorm_accumulatedError_le params ringSecret initialAccumulator controls
      2 rowErrorBound hfactor hfactorSub hcontrolRows

/-- Native accumulated error satisfies the linear signed-rotation budget. -/
theorem cInfNorm_nativeAccumulatedError_le_linear
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank)
    (rowErrorBound : ℕ)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound) :
    LatticeCrypto.cInfNorm
        (BlindRotation.accumulatedError params ringSecret initialAccumulator
          (BlindRotation.nativeControls params roundExponent input
            bootstrappingKey lweSecret)) ≤
      nativeLinearNoiseBudget degree rank params.levels params.base
        lweDimension rowErrorBound := by
  let controls := BlindRotation.nativeControls params roundExponent input
    bootstrappingKey lweSecret
  have hrotation : ∀ control ∈ controls,
      ∃ exponent : Fin (2 * (degree + 1)),
        control.factor = BlindRotation.rotationMonomial q degree exponent := by
    unfold controls BlindRotation.nativeControls
    rw [List.forall_mem_ofFn_iff]
    intro coordinate
    exact ⟨-roundExponent (input.mask coordinate), rfl⟩
  have hcontrolRows : ∀ control ∈ controls, ∀ index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) control.bit)
          control.bootstrapKeyEntry index) ≤ rowErrorBound := by
    unfold controls BlindRotation.nativeControls
    rw [List.forall_mem_ofFn_iff]
    intro coordinate index
    exact hrows coordinate index
  have hsteps : ∀ control ∈ controls, ∀ currentAccumulator,
      LatticeCrypto.cInfNorm
          (BlindRotation.stepError params ringSecret currentAccumulator control) ≤
        2 * linearExternalProductNoiseBudget degree rank params.levels
          (params.base - 1) rowErrorBound := by
    intro control hmem currentAccumulator
    obtain ⟨exponent, hfactor⟩ := hrotation control hmem
    exact cInfNorm_nativeStepError_le_linear params ringSecret currentAccumulator
      control exponent hfactor rowErrorBound (hcontrolRows control hmem)
  simpa only [controls, BlindRotation.nativeControls, List.length_ofFn,
    nativeLinearNoiseBudget] using
    cInfNorm_accumulatedError_le_signedRotations_of_step params ringSecret
      initialAccumulator controls
      (2 * linearExternalProductNoiseBudget degree rank params.levels
        (params.base - 1) rowErrorBound)
      hrotation hsteps

/-! ## From ring error to extracted scalar distance -/

/-- Centered modular distance on the finite torus. -/
def centeredDistance {q : ℕ} [NeZero q] (left right : ZMod q) : ℕ :=
  (LatticeCrypto.centeredRepr (left - right)).natAbs

/-- Centered distance never exceeds half the coefficient modulus. -/
theorem centeredDistance_le_half {q : ℕ} [NeZero q]
    (left right : ZMod q) :
    centeredDistance left right ≤ q / 2 := by
  exact LatticeCrypto.centeredRepr_abs_le (left - right)

@[simp]
theorem centeredDistance_self {q : ℕ} [NeZero q] (value : ZMod q) :
    centeredDistance value value = 0 := by
  simp [centeredDistance, LatticeCrypto.centeredRepr_eq_valMinAbs]

/-- Centered modular distance is symmetric. -/
theorem centeredDistance_symm {q : ℕ} [NeZero q] (left right : ZMod q) :
    centeredDistance left right = centeredDistance right left := by
  unfold centeredDistance
  have hneg : left - right = -(right - left) := by ring
  rw [hneg, LatticeCrypto.centeredRepr_natAbs_neg]

/-- Centered modular distance satisfies the triangle inequality. -/
theorem centeredDistance_triangle {q : ℕ} [NeZero q]
    (left middle right : ZMod q) :
    centeredDistance left right ≤
      centeredDistance left middle + centeredDistance middle right := by
  unfold centeredDistance
  have hadd : left - right = (left - middle) + (middle - right) := by ring
  rw [hadd]
  exact NoiseBounds.centeredRepr_add_natAbs_le (left - middle) (middle - right)

/-- Extracting coefficient zero from `ideal + error` changes the scalar value by at most the
centered infinity norm of `error`. -/
theorem centeredDistance_constantCoefficient_add_le
    {q degree : ℕ} [NeZero q]
    (ideal error : RLWE.Rq q (degree + 1)) :
    centeredDistance
        (SampleExtraction.constantCoefficient (ideal + error))
        (SampleExtraction.constantCoefficient ideal) ≤
      LatticeCrypto.cInfNorm error := by
  have hadd :
      SampleExtraction.constantCoefficient (ideal + error) =
        SampleExtraction.constantCoefficient ideal +
          SampleExtraction.constantCoefficient error := by
    change Gadget.Base.coefficientAddHom (q := q) (degree + 1) 0 (ideal + error) =
      Gadget.Base.coefficientAddHom (degree + 1) 0 ideal +
        Gadget.Base.coefficientAddHom (degree + 1) 0 error
    convert (Gadget.Base.coefficientAddHom (q := q) (degree + 1) 0).map_add ideal error
  unfold centeredDistance
  rw [hadd]
  simp only [add_sub_cancel_left]
  unfold SampleExtraction.constantCoefficient
  exact LatticeCrypto.coeff_le_cInfNorm error 0

/-- The ideal scalar phase after a binary blind-rotation trace, before accumulated error. -/
def idealExtractedPhase
    {q degree rank levels : ℕ} [NeZero q]
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank)
    (controls : List (BlindRotation.BitControl q degree rank levels)) : ZMod q :=
  SampleExtraction.constantCoefficient
    (BlindRotation.idealMultiplier controls *
      TLWE.phase secret initialAccumulator)

/-- Exact blind rotation followed by sample extraction is within the norm of the accumulated ring
error of its ideal extracted phase. -/
theorem centeredDistance_phase_apply_runBits_le
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank)
    (controls : List (BlindRotation.BitControl q degree rank params.levels)) :
    centeredDistance
        (TLWE.phase (SampleExtraction.extractedSecret secret)
          (SampleExtraction.apply
            (BlindRotation.runBits params initialAccumulator controls)))
        (idealExtractedPhase secret initialAccumulator controls) ≤
      LatticeCrypto.cInfNorm
        (BlindRotation.accumulatedError params secret initialAccumulator controls) := by
  rw [SampleExtraction.phase_apply, BlindRotation.phase_runBits]
  exact centeredDistance_constantCoefficient_add_le
    (BlindRotation.idealMultiplier controls * TLWE.phase secret initialAccumulator)
    (BlindRotation.accumulatedError params secret initialAccumulator controls)

/-- Native public blind rotation and sample extraction obey the same scalar error bound. -/
theorem centeredDistance_phase_apply_nativeBlindRotate_le
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank) :
    centeredDistance
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params roundExponent input
              bootstrappingKey initialAccumulator)))
        (idealExtractedPhase ringSecret initialAccumulator
          (BlindRotation.nativeControls params roundExponent input
            bootstrappingKey lweSecret)) ≤
      LatticeCrypto.cInfNorm
        (BlindRotation.accumulatedError params ringSecret initialAccumulator
          (BlindRotation.nativeControls params roundExponent input
            bootstrappingKey lweSecret)) := by
  rw [SampleExtraction.phase_apply,
    BlindRotation.phase_nativeBlindRotate params roundExponent input bootstrappingKey
      lweSecret ringSecret initialAccumulator]
  exact centeredDistance_constantCoefficient_add_le
    (BlindRotation.idealMultiplier
        (BlindRotation.nativeControls params roundExponent input bootstrappingKey lweSecret) *
      TLWE.phase ringSecret initialAccumulator)
    (BlindRotation.accumulatedError params ringSecret initialAccumulator
      (BlindRotation.nativeControls params roundExponent input bootstrappingKey lweSecret))

/-- Native blind rotation followed by sample extraction is within the explicit trace budget. -/
theorem centeredDistance_phase_apply_nativeBlindRotate_le_budget
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank)
    (rowErrorBound : ℕ)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound) :
    centeredDistance
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params roundExponent input
              bootstrappingKey initialAccumulator)))
        (idealExtractedPhase ringSecret initialAccumulator
          (BlindRotation.nativeControls params roundExponent input
            bootstrappingKey lweSecret)) ≤
      traceNoiseBudget degree lweDimension
        (stepNoiseBudget degree rank params.levels (params.base - 1) 2 rowErrorBound) :=
  (centeredDistance_phase_apply_nativeBlindRotate_le params roundExponent input
    bootstrappingKey lweSecret ringSecret initialAccumulator).trans
      (cInfNorm_nativeAccumulatedError_le params roundExponent input bootstrappingKey
        lweSecret ringSecret initialAccumulator rowErrorBound hrows)

/-- Native blind rotation followed by sample extraction is within the linear signed-rotation
budget. -/
theorem centeredDistance_phase_apply_nativeBlindRotate_le_linearBudget
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank)
    (rowErrorBound : ℕ)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound) :
    centeredDistance
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params roundExponent input
              bootstrappingKey initialAccumulator)))
        (idealExtractedPhase ringSecret initialAccumulator
          (BlindRotation.nativeControls params roundExponent input
            bootstrappingKey lweSecret)) ≤
      nativeLinearNoiseBudget degree rank params.levels params.base
        lweDimension rowErrorBound :=
  (centeredDistance_phase_apply_nativeBlindRotate_le params roundExponent input
    bootstrappingKey lweSecret ringSecret initialAccumulator).trans
      (cInfNorm_nativeAccumulatedError_le_linear params roundExponent input
        bootstrappingKey lweSecret ringSecret initialAccumulator rowErrorBound hrows)

/-! ## Nearest-codeword decoding -/

/-- Encode a bit by two caller-selected finite-torus codewords. -/
def encodeBit {q : ℕ} (zeroCode oneCode : ZMod q) (bit : Bool) : ZMod q :=
  if bit then oneCode else zeroCode

/-- Decode to one exactly when the sample is strictly closer to the one-codeword.  Ties decode to
zero. -/
def decodeNearest {q : ℕ} [NeZero q]
    (zeroCode oneCode sample : ZMod q) : Bool :=
  decide (centeredDistance sample oneCode < centeredDistance sample zeroCode)

/-- A sample within `radius` of the zero-codeword decodes to zero when the two codewords are more
than `2 * radius` apart. -/
theorem decodeNearest_eq_false_of_distance_le
    {q : ℕ} [NeZero q] (zeroCode oneCode sample : ZMod q) (radius : ℕ)
    (hmargin : 2 * radius < centeredDistance zeroCode oneCode)
    (hsample : centeredDistance sample zeroCode ≤ radius) :
    decodeNearest zeroCode oneCode sample = false := by
  have hnot : ¬centeredDistance sample oneCode < centeredDistance sample zeroCode := by
    intro hcloser
    have hzeroSample : centeredDistance zeroCode sample ≤ radius := by
      rw [centeredDistance_symm]
      exact hsample
    have honeSample : centeredDistance sample oneCode ≤ radius :=
      (Nat.le_of_lt hcloser).trans hsample
    have htriangle := centeredDistance_triangle zeroCode sample oneCode
    have hupper : centeredDistance zeroCode oneCode ≤ 2 * radius := by
      calc
        centeredDistance zeroCode oneCode ≤
            centeredDistance zeroCode sample + centeredDistance sample oneCode := htriangle
        _ ≤ radius + radius := Nat.add_le_add hzeroSample honeSample
        _ = 2 * radius := by omega
    omega
  simp [decodeNearest, hnot]

/-- Symmetric nearest-codeword correctness for a sample near the one-codeword. -/
theorem decodeNearest_eq_true_of_distance_le
    {q : ℕ} [NeZero q] (zeroCode oneCode sample : ZMod q) (radius : ℕ)
    (hmargin : 2 * radius < centeredDistance zeroCode oneCode)
    (hsample : centeredDistance sample oneCode ≤ radius) :
    decodeNearest zeroCode oneCode sample = true := by
  have hcloser : centeredDistance sample oneCode < centeredDistance sample zeroCode := by
    by_contra hnot
    have hzeroSample : centeredDistance sample zeroCode ≤ radius :=
      (Nat.le_of_not_gt hnot).trans hsample
    have honeSample : centeredDistance oneCode sample ≤ radius := by
      rw [centeredDistance_symm]
      exact hsample
    have htriangle := centeredDistance_triangle oneCode sample zeroCode
    have hupper : centeredDistance zeroCode oneCode ≤ 2 * radius := by
      calc
        centeredDistance zeroCode oneCode = centeredDistance oneCode zeroCode :=
          centeredDistance_symm _ _
        _ ≤ centeredDistance oneCode sample + centeredDistance sample zeroCode := htriangle
        _ ≤ radius + radius := Nat.add_le_add honeSample hzeroSample
        _ = 2 * radius := by omega
    omega
  simp [decodeNearest, hcloser]

/-- Uniform nearest-codeword correctness for either encoded bit. -/
theorem decodeNearest_encodeBit_of_distance_le
    {q : ℕ} [NeZero q] (zeroCode oneCode sample : ZMod q) (radius : ℕ)
    (bit : Bool)
    (hmargin : 2 * radius < centeredDistance zeroCode oneCode)
    (hsample : centeredDistance sample (encodeBit zeroCode oneCode bit) ≤ radius) :
    decodeNearest zeroCode oneCode sample = bit := by
  cases bit with
  | false =>
      apply decodeNearest_eq_false_of_distance_le zeroCode oneCode sample radius hmargin
      simpa [encodeBit] using hsample
  | true =>
      apply decodeNearest_eq_true_of_distance_le zeroCode oneCode sample radius hmargin
      simpa [encodeBit] using hsample

/-! ## End-to-end deterministic bootstrapping criterion -/

/-- **Quantitative native TFHE bootstrapping correctness.** If every native bootstrapping-key row
has bounded error, the ideal rotated test-vector coefficient is the requested codeword, and the
two codewords are separated by more than twice the checked trace budget, then public blind
rotation followed by sample extraction decrypts to the requested bit.

`hlookup` is precisely the remaining functional test-vector/rounded-exponent obligation; no noise
or sample-extraction fact is hidden inside it. -/
theorem decode_nativeBlindRotate_apply
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank)
    (zeroCode oneCode : ZMod q) (outputBit : Bool) (rowErrorBound : ℕ)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound)
    (hlookup :
      idealExtractedPhase ringSecret initialAccumulator
          (BlindRotation.nativeControls params roundExponent input
            bootstrappingKey lweSecret) =
        encodeBit zeroCode oneCode outputBit)
    (hmargin :
      2 * nativeNoiseBudget degree rank params.levels params.base
          lweDimension rowErrorBound <
        centeredDistance zeroCode oneCode) :
    decodeNearest zeroCode oneCode
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params roundExponent input
              bootstrappingKey initialAccumulator))) = outputBit := by
  apply decodeNearest_encodeBit_of_distance_le zeroCode oneCode
    (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
      (SampleExtraction.apply
        (BlindRotation.nativeBlindRotate params roundExponent input
          bootstrappingKey initialAccumulator)))
    (nativeNoiseBudget degree rank params.levels params.base lweDimension rowErrorBound)
    outputBit hmargin
  rw [← hlookup]
  simpa only [nativeNoiseBudget] using
    centeredDistance_phase_apply_nativeBlindRotate_le_budget params roundExponent input
      bootstrappingKey lweSecret ringSecret initialAccumulator rowErrorBound hrows

/-- **Sharp quantitative native TFHE bootstrapping correctness.** This version replaces the
geometric trace margin by `nativeLinearNoiseBudget`, using the exact signed-permutation action of
all native rotation factors. -/
theorem decode_nativeBlindRotate_apply_linear
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank)
    (zeroCode oneCode : ZMod q) (outputBit : Bool) (rowErrorBound : ℕ)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound)
    (hlookup :
      idealExtractedPhase ringSecret initialAccumulator
          (BlindRotation.nativeControls params roundExponent input
            bootstrappingKey lweSecret) =
        encodeBit zeroCode oneCode outputBit)
    (hmargin :
      2 * nativeLinearNoiseBudget degree rank params.levels params.base
          lweDimension rowErrorBound <
        centeredDistance zeroCode oneCode) :
    decodeNearest zeroCode oneCode
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params roundExponent input
              bootstrappingKey initialAccumulator))) = outputBit := by
  apply decodeNearest_encodeBit_of_distance_le zeroCode oneCode
    (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
      (SampleExtraction.apply
        (BlindRotation.nativeBlindRotate params roundExponent input
          bootstrappingKey initialAccumulator)))
    (nativeLinearNoiseBudget degree rank params.levels params.base
      lweDimension rowErrorBound)
    outputBit hmargin
  rw [← hlookup]
  exact centeredDistance_phase_apply_nativeBlindRotate_le_linearBudget params
    roundExponent input bootstrappingKey lweSecret ringSecret initialAccumulator
    rowErrorBound hrows

end

end FormalProof4FHE.TFHE.BootstrappingCorrectness
