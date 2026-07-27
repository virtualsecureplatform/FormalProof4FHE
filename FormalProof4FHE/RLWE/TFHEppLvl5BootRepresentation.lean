/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.TFHEppLvl5BootRenyiObstruction
import FormalProof4FHE.TFHE.FullWidthBalancedDecomposition
import Mathlib.Analysis.Fourier.ZMod

/-!
# TFHEpp Level-5 Double-Decomposition and FFT Representation

This module closes the algebraic representation gap in the level-5 Renyi screen.

* The TFHEpp auxiliary decomposition has `base = 2^16`, `levels = 40`, and coefficient modulus
  `2^640`, so it is full width.
* Its centered offset, signed digit conversion, coefficientwise lift, and `35 * 40 = 1400` row
  reshaping form one explicit equivalence.
* Any FFT implementation with an exact decoder on signed digit polynomials remains injective.
  Consequently the complete reachable FFT view is equivalent to the 35 ordinary rows, and both
  conditional guessing probability and finite Renyi moments are invariant.
* As an unconditional mathematical reference, the exact complex DFT is proved injective and
  packaged as such a round-trip codec.

The actual SPQLIOS/IEEE-754 routine is not modeled as floating-point source code in Lean.  Its
implementation boundary is the single `RoundTripEncoding.decode_encode` field below; no
cryptographic or distributional premise is hidden in it.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.TFHEppLvl5BootRepresentation

open RankOneHNFLossinessRefined
open RankOneHNFLossinessRenyi
open RankOneHNFLossinessRLWENTRU
open TFHE.Gadget.Base
open TFHEppLvl5BootRenyiObstruction

noncomputable section

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-! ## Exact TFHEpp level-5 balanced double decomposition -/

/-- The exact finite-modulus parameters used by `TRLWEBaseBbarDecompose<lvl5bootparam>`. -/
def lvl5DoubleDecompositionParameters : Parameters (2 ^ 640) where
  base := 2 ^ 16
  levels := 40
  one_lt_base := by norm_num
  modulus_le_capacity := by
    rw [← pow_mul]

/-- Forty 16-bit digits cover all 640 coefficient bits, with no discarded remainder. -/
theorem lvl5DoubleDecomposition_exactCapacity :
    2 ^ 640 = lvl5DoubleDecompositionParameters.base ^
      lvl5DoubleDecompositionParameters.levels := by
  change 2 ^ 640 = (2 ^ 16) ^ 40
  rw [← pow_mul]

/-- The implementation's row multiplication is exactly `35 * 40 = 1400`. -/
theorem lvl5DoubleDecomposition_rowCount : 35 * 40 = 1400 := by
  norm_num

/-- One ordinary level-5 HalfTRGSW collection before double decomposition. -/
abbrev Lvl5OrdinaryRows :=
  Fin 35 → Fin 2 → Fin 32768 → ZMod (2 ^ 640)

/-- One signed 16-bit digit polynomial as passed to the digit FFT. -/
abbrev Lvl5DigitPolynomial :=
  Fin 32768 → BalancedDigit (2 ^ 16) (2 ^ 15)

/-- The 1400 double-decomposed two-component rows. -/
abbrev Lvl5DoubleDecomposedRows :=
  Fin 1400 → Fin 2 → Lvl5DigitPolynomial

/-- Exact equivalence implemented by offsetting, balanced base-`2^16` decomposition, and
flattening the `(35, 40)` row indices. -/
def lvl5DoubleDecompositionEquiv :
    Lvl5OrdinaryRows ≃ Lvl5DoubleDecomposedRows := by
  exact balancedRowsEquiv lvl5DoubleDecompositionParameters
    lvl5DoubleDecomposition_exactCapacity (2 ^ 15) 32768 2 35

/-- In particular, TFHEpp's full-width double decomposition is injective. -/
theorem lvl5DoubleDecomposition_injective :
    Function.Injective lvl5DoubleDecompositionEquiv :=
  lvl5DoubleDecompositionEquiv.injective

/-! ## Reconstructible FFT boundary -/

/-- A deterministic representation equipped with an exact decoder on every encoded input. -/
structure RoundTripEncoding (Input Output : Type) where
  encode : Input → Output
  decode : Output → Input
  decode_encode : Function.LeftInverse decode encode

/-- Exact round trips are injective. -/
theorem RoundTripEncoding.injective {Input Output : Type}
    (encoding : RoundTripEncoding Input Output) :
    Function.Injective encoding.encode :=
  encoding.decode_encode.injective

/-- Apply a reconstructible digit FFT to every component of every expanded row. -/
def encodeRowsWithFFT {Spectrum : Type}
    (fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum)
    (ordinary : Lvl5OrdinaryRows) : Fin 1400 → Fin 2 → Spectrum :=
  fun row component ↦
    fft.encode (lvl5DoubleDecompositionEquiv ordinary row component)

/-- Full-width DD followed by any reconstructible FFT remains injective. -/
theorem encodeRowsWithFFT_injective {Spectrum : Type}
    (fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum) :
    Function.Injective (encodeRowsWithFFT fft) := by
  intro left right heq
  apply lvl5DoubleDecompositionEquiv.injective
  funext row component
  apply fft.injective
  exact congrFun (congrFun heq row) component

/-- The 35 ordinary rows are equivalent to the reachable final representations. -/
def lvl5RepresentationEquiv {Spectrum : Type}
    (fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum) :
    Lvl5OrdinaryRows ≃ Set.range (encodeRowsWithFFT fft) :=
  Equiv.ofInjective (encodeRowsWithFFT fft) (encodeRowsWithFFT_injective fft)

/-- Apply an arbitrary deterministic encoder to the public side of a joint sampler. -/
def mapJointSideFunction {Secret Side Encoded : Type} (encode : Side → Encoded)
    (joint : ProbComp (Secret × Side)) : ProbComp (Secret × Encoded) :=
  (fun value ↦ (value.1, encode value.2)) <$> joint

/-- Mapping a joint side through a function is absorbed by precomposing the estimator. -/
theorem guessingSuccess_mapJointSideFunction
    {Secret Side Encoded : Type} [DecidableEq Secret]
    (encode : Side → Encoded) (joint : ProbComp (Secret × Side))
    (estimator : Estimator Secret Encoded) :
    guessingSuccess (mapJointSideFunction encode joint) estimator =
      guessingSuccess joint (fun side ↦ estimator (encode side)) := by
  unfold guessingSuccess guessingGame mapJointSideFunction
  apply probOutput_congr rfl
  simp [map_eq_bind_pure_comp, bind_assoc]

/-- An injective public encoding preserves conditional guessing probability even when its
codomain also contains unreachable values. -/
theorem conditionalGuessingProbability_mapJointSideFunction_of_injective
    {Secret Side Encoded : Type} [DecidableEq Secret] [Nonempty Side]
    (encode : Side → Encoded) (hinjective : Function.Injective encode)
    (joint : ProbComp (Secret × Side)) :
    conditionalGuessingProbability (mapJointSideFunction encode joint) =
      conditionalGuessingProbability joint := by
  apply le_antisymm
  · apply iSup_le
    intro estimator
    rw [guessingSuccess_mapJointSideFunction]
    exact guessingSuccess_le_conditionalGuessingProbability _ _
  · apply iSup_le
    intro estimator
    let encodedEstimator : Estimator Secret Encoded :=
      fun encoded ↦ estimator (Function.invFun encode encoded)
    have hsuccess := guessingSuccess_mapJointSideFunction
      encode joint encodedEstimator
    have hprecompose : (fun side ↦ encodedEstimator (encode side)) = estimator := by
      funext side
      simp only [encodedEstimator]
      rw [Function.leftInverse_invFun hinjective side]
    have heq : guessingSuccess joint estimator =
        guessingSuccess (mapJointSideFunction encode joint) encodedEstimator := by
      rw [hsuccess, hprecompose]
    rw [heq]
    exact guessingSuccess_le_conditionalGuessingProbability _ _

/-- Conditional secret-guessing probability is unchanged by the complete DD/FFT
representation. -/
theorem conditionalGuessingProbability_map_lvl5Representation
    {Secret Spectrum : Type} [DecidableEq Secret]
    (fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum)
    (joint : ProbComp (Secret × Lvl5OrdinaryRows)) :
    conditionalGuessingProbability
        (mapJointSide (lvl5RepresentationEquiv fft) joint) =
      conditionalGuessingProbability joint :=
  conditionalGuessingProbability_mapJointSide (lvl5RepresentationEquiv fft) joint

/-- Direct statement for the actual encoded-row codomain (rather than its reachable subtype). -/
theorem conditionalGuessingProbability_map_lvl5EncodedRows
    {Secret Spectrum : Type} [DecidableEq Secret]
    (fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum)
    (joint : ProbComp (Secret × Lvl5OrdinaryRows)) :
    conditionalGuessingProbability
        (mapJointSideFunction (encodeRowsWithFFT fft) joint) =
      conditionalGuessingProbability joint :=
  conditionalGuessingProbability_mapJointSideFunction_of_injective
    (encodeRowsWithFFT fft) (encodeRowsWithFFT_injective fft) joint

noncomputable instance lvl5RepresentationRangeFintype {Spectrum : Type}
    (fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum) :
    Fintype (Set.range (encodeRowsWithFFT fft)) :=
  Fintype.ofEquiv Lvl5OrdinaryRows (lvl5RepresentationEquiv fft)

/-- Push a finite mass table through the exact public representation. -/
def representedMass {Spectrum : Type}
    (fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum)
    (mass : Lvl5OrdinaryRows → ℝ) : Set.range (encodeRowsWithFFT fft) → ℝ :=
  fun represented ↦ mass ((lvl5RepresentationEquiv fft).symm represented)

/-- Finite Renyi moments are exactly invariant under the complete DD/FFT representation. -/
theorem finiteRenyiMoment_lvl5Representation
    {Spectrum : Type}
    (fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum)
    (alpha : ℝ) (likelihood reference : Lvl5OrdinaryRows → ℝ) :
    finiteRenyiMoment alpha
        (representedMass fft likelihood) (representedMass fft reference) =
      finiteRenyiMoment alpha likelihood reference := by
  unfold finiteRenyiMoment representedMass
  apply Fintype.sum_equiv (lvl5RepresentationEquiv fft).symm
  intro represented
  rfl

/-! ## Unconditional exact-DFT instantiation -/

/-- Reindex the exact DFT on `ZMod degree` as a transform of `Fin degree` vectors. -/
def finDFTEquiv (degree : ℕ) [NeZero degree] :
    (Fin degree → ℂ) ≃ (Fin degree → ℂ) :=
  let reindex : (Fin degree → ℂ) ≃ (ZMod degree → ℂ) :=
    (ZMod.finEquiv degree).toEquiv.piCongrLeft (fun _ ↦ ℂ)
  reindex.trans ((ZMod.dft (N := degree) (E := ℂ)).toEquiv.trans reindex.symm)

/-- Cast the exact signed digit coefficients into the complex FFT input space. -/
def digitPolynomialComplexCast (polynomial : Lvl5DigitPolynomial) :
    Fin 32768 → ℂ :=
  fun coefficient ↦ (polynomial coefficient).val

/-- Casting the signed digit polynomial to complex coefficients loses no information. -/
theorem digitPolynomialComplexCast_injective :
    Function.Injective digitPolynomialComplexCast := by
  intro left right heq
  funext coefficient
  apply Subtype.ext
  have hcoefficient := congrFun heq coefficient
  change ((left coefficient).val : ℂ) = ((right coefficient).val : ℂ) at hcoefficient
  exact_mod_cast hcoefficient

/-- Ideal exact Fourier representation of one signed digit polynomial. -/
def idealDigitFFT (polynomial : Lvl5DigitPolynomial) : Fin 32768 → ℂ :=
  finDFTEquiv 32768 (digitPolynomialComplexCast polynomial)

/-- Fourier inversion proves that the ideal digit FFT is injective. -/
theorem idealDigitFFT_injective : Function.Injective idealDigitFFT :=
  (finDFTEquiv 32768).injective.comp digitPolynomialComplexCast_injective

/-- Reachable exact spectra are equivalent to signed digit polynomials. -/
def idealDigitFFTEquiv :
    Lvl5DigitPolynomial ≃ Set.range idealDigitFFT :=
  Equiv.ofInjective idealDigitFFT idealDigitFFT_injective

/-- The exact mathematical DFT, packaged as a round-trip representation. -/
def idealDigitFFTEncoding :
    RoundTripEncoding Lvl5DigitPolynomial (Set.range idealDigitFFT) where
  encode := idealDigitFFTEquiv
  decode := idealDigitFFTEquiv.symm
  decode_encode := idealDigitFFTEquiv.symm_apply_apply

/-- Unconditional exact-complex-FFT specialization of guessing-probability invariance. -/
theorem conditionalGuessingProbability_map_lvl5IdealFFT
    {Secret : Type} [DecidableEq Secret]
    (joint : ProbComp (Secret × Lvl5OrdinaryRows)) :
    conditionalGuessingProbability
        (mapJointSide (lvl5RepresentationEquiv idealDigitFFTEncoding) joint) =
      conditionalGuessingProbability joint :=
  conditionalGuessingProbability_map_lvl5Representation idealDigitFFTEncoding joint

/-- The already checked arithmetic obstruction therefore applies before or after any exact
round-trip DD/FFT representation; a representation-only data-processing argument cannot remove
the failed first-order margin. -/
theorem lvl5_firstOrderRenyiMargin_after_roundTrip_not_pos
    {Spectrum : Type} (_fft : RoundTripEncoding Lvl5DigitPolynomial Spectrum)
    (meanEnergy : ℝ) (topRow_le_mean : lvl5TopQuadraticEnergy ≤ meanEnergy) :
    ¬0 < Real.log ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) -
      meanEnergy / 2 :=
  lvl5_firstOrderRenyiMargin_not_pos meanEnergy topRow_le_mean

end

end FormalProof4FHE.RLWE.TFHEppLvl5BootRepresentation
