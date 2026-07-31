/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BlindRotation
import FormalProof4FHE.TFHE.InternalProduct
import FormalProof4FHE.TFHE.SampleExtraction
import FormalProof4FHE.TFHE.SubsetKeyTrapdoorTheorems
import Mathlib.Algebra.Order.Chebyshev

/-!
# Source-Aligned Factor Propagation Through TFHE Operations

This file closes the algebraic part of the factor-preserving-bootstrap boundary isolated by
`SubsetKeyTrapdoorTheorems`.  It treats carried factors as proof-only public state and proves exact
recurrences for the operations used by a TFHE bootstrap:

* finite public linear combinations and external products;
* the identity-plus-external-product CMUX normal form;
* iteration of data-dependent CMUX controls;
* coefficient sample extraction, under an explicit ring/scalar gadget compatibility equation; and
* deterministic squared-energy bounds for one external product, one CMUX, and a complete trace.

The native executable blind-rotation step is also proved equal, as a complete ciphertext, to the
same identity-plus-external-product normal form.  Thus the abstract factor recurrence is aligned
with the existing executable TFHE model rather than only with its phase.

This is deliberately a technical layer.  It does not assert that TFHEpp's native TGSW rows have
factor annotations under one common random gadget, that this gadget satisfies the extraction
compatibility equation, or that the resulting trace-energy bound fits a concrete correctness
budget.  Those are the next construction and parameter obligations.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.SourceAlignedFactorPropagation

open SubsetKeyTrapdoorTheorems.SourceAligned

set_option linter.unusedSectionVars false

/-! ## Finite public linear operations -/

namespace FactorCiphertext

section Linear

variable {R Prefix Suffix Factor Index : Type} [CommRing R]
  [Fintype Prefix] [Fintype Suffix] [Fintype Factor] [Fintype Index]

/-- The zero factor-carrying ciphertext. -/
def zero : FactorCiphertext R Prefix Suffix Factor where
  prefixMask := 0
  factor := 0
  body := 0

/-- Public negation of a factor-carrying ciphertext. -/
def neg (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    FactorCiphertext R Prefix Suffix Factor where
  prefixMask := -ciphertext.prefixMask
  factor := -ciphertext.factor
  body := -ciphertext.body

/-- Public subtraction of factor-carrying ciphertexts. -/
def sub (left right : FactorCiphertext R Prefix Suffix Factor) :
    FactorCiphertext R Prefix Suffix Factor :=
  left.add (neg right)

/-- A finite public linear combination.  This is the factor-level analogue of
`TLWE.linearCombination` and hence of a TGSW external product. -/
def linearCombination
    (weights : Index → R)
    (rows : Index → FactorCiphertext R Prefix Suffix Factor) :
    FactorCiphertext R Prefix Suffix Factor where
  prefixMask := fun coordinate ↦
    ∑ index, weights index * (rows index).prefixMask coordinate
  factor := fun coordinate ↦
    ∑ index, weights index * (rows index).factor coordinate
  body := ∑ index, weights index * (rows index).body

@[simp]
theorem zero_factor :
    (zero : FactorCiphertext R Prefix Suffix Factor).factor = 0 := by
  rfl

@[simp]
theorem neg_factor (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    (neg ciphertext).factor = -ciphertext.factor := by
  rfl

@[simp]
theorem sub_factor (left right : FactorCiphertext R Prefix Suffix Factor) :
    (sub left right).factor = left.factor - right.factor := by
  funext coordinate
  simp [sub, FactorCiphertext.add, neg, sub_eq_add_neg]

@[simp]
theorem linearCombination_factor
    (weights : Index → R)
    (rows : Index → FactorCiphertext R Prefix Suffix Factor) :
    (linearCombination weights rows).factor =
      fun coordinate ↦ ∑ index, weights index * (rows index).factor coordinate := by
  rfl

theorem suffixMask_zero
    (gadget : Matrix Suffix Factor R) :
    (zero : FactorCiphertext R Prefix Suffix Factor).suffixMask gadget = 0 := by
  simp [zero, FactorCiphertext.suffixMask]

theorem suffixMask_neg
    (gadget : Matrix Suffix Factor R)
    (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    (neg ciphertext).suffixMask gadget = -ciphertext.suffixMask gadget := by
  ext suffix
  simp [neg, FactorCiphertext.suffixMask, Matrix.mulVec]

theorem suffixMask_linearCombination
    (gadget : Matrix Suffix Factor R)
    (weights : Index → R)
    (rows : Index → FactorCiphertext R Prefix Suffix Factor) :
    (linearCombination weights rows).suffixMask gadget =
      fun suffix ↦ ∑ index, weights index * (rows index).suffixMask gadget suffix := by
  classical
  have hfactor :
      (linearCombination weights rows).factor =
        ∑ index, weights index • (rows index).factor := by
    ext factor
    simp [linearCombination, smul_eq_mul]
  unfold FactorCiphertext.suffixMask
  rw [hfactor]
  calc
    gadget *ᵥ (∑ index, weights index • (rows index).factor) =
        ∑ index, gadget *ᵥ (weights index • (rows index).factor) := by
      simpa using Matrix.mulVec_sum gadget Finset.univ
        (fun index ↦ weights index • (rows index).factor)
    _ = ∑ index, weights index • (gadget *ᵥ (rows index).factor) := by
      apply Finset.sum_congr rfl
      intro index _
      exact Matrix.mulVec_smul gadget (weights index) (rows index).factor
    _ = fun suffix ↦ ∑ index, weights index *
        (gadget *ᵥ (rows index).factor) suffix := by
      ext suffix
      simp [smul_eq_mul]

@[simp]
theorem phase_zero
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R) :
    zero.phase gadget prefixSecret suffixSecret = 0 := by
  simp [zero, FactorCiphertext.phase, FactorCiphertext.suffixMask, dotProduct]

theorem phase_neg
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    (neg ciphertext).phase gadget prefixSecret suffixSecret =
      -ciphertext.phase gadget prefixSecret suffixSecret := by
  unfold FactorCiphertext.phase
  rw [suffixMask_neg]
  simp only [neg, dotProduct_neg]
  ring

theorem phase_sub
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (left right : FactorCiphertext R Prefix Suffix Factor) :
    (sub left right).phase gadget prefixSecret suffixSecret =
      left.phase gadget prefixSecret suffixSecret -
        right.phase gadget prefixSecret suffixSecret := by
  rw [sub, FactorCiphertext.phase_add, phase_neg]
  ring

/-- The phase of a factor-carrying external product is the corresponding weighted sum of row
phases. -/
theorem phase_linearCombination
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (weights : Index → R)
    (rows : Index → FactorCiphertext R Prefix Suffix Factor) :
    (linearCombination weights rows).phase gadget prefixSecret suffixSecret =
      ∑ index, weights index *
        (rows index).phase gadget prefixSecret suffixSecret := by
  classical
  unfold FactorCiphertext.phase
  rw [suffixMask_linearCombination]
  simp only [linearCombination]
  have hprefix :
      dotProduct prefixSecret
          (fun coordinate ↦ ∑ index, weights index * (rows index).prefixMask coordinate) =
        ∑ index, weights index * dotProduct prefixSecret (rows index).prefixMask := by
    unfold dotProduct
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro index _
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  have hsuffix :
      dotProduct suffixSecret
          (fun suffix ↦ ∑ index, weights index *
            (rows index).suffixMask gadget suffix) =
        ∑ index, weights index *
          dotProduct suffixSecret ((rows index).suffixMask gadget) := by
    unfold dotProduct
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro index _
    apply Finset.sum_congr rfl
    intro suffix _
    ring
  rw [hprefix, hsuffix]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

end Linear

end FactorCiphertext

/-! ## External product, CMUX, and blind-rotation folds -/

section ExternalProduct

variable {R Prefix Suffix Factor Row : Type} [CommRing R]
  [Fintype Prefix] [Fintype Suffix] [Fintype Factor] [Fintype Row]

/-- A row-indexed factor-carrying analogue of one TGSW ciphertext. -/
abbrev FactorRows := Row → FactorCiphertext R Prefix Suffix Factor

/-- External product by public gadget digits. -/
def externalProduct
    (digits : Row → R) (rows : FactorRows (R := R) (Prefix := Prefix)
      (Suffix := Suffix) (Factor := Factor) (Row := Row)) :
    FactorCiphertext R Prefix Suffix Factor :=
  FactorCiphertext.linearCombination digits rows

@[simp]
theorem externalProduct_factor
    (digits : Row → R) (rows : FactorRows (R := R) (Prefix := Prefix)
      (Suffix := Suffix) (Factor := Factor) (Row := Row)) :
    (externalProduct digits rows).factor =
      fun factor ↦ ∑ row, digits row * (rows row).factor factor := by
  rfl

theorem externalProduct_phase
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (digits : Row → R) (rows : FactorRows (R := R) (Prefix := Prefix)
      (Suffix := Suffix) (Factor := Factor) (Row := Row)) :
    (externalProduct digits rows).phase gadget prefixSecret suffixSecret =
      ∑ row, digits row * (rows row).phase gadget prefixSecret suffixSecret := by
  exact FactorCiphertext.phase_linearCombination gadget prefixSecret suffixSecret digits rows

/-- Identity-plus-external-product CMUX normal form.  The digits may be any public function of
the current ciphertext; no independence premise is used by the algebra. -/
def cmux
    (accumulator : FactorCiphertext R Prefix Suffix Factor)
    (digits : Row → R)
    (controlRows : FactorRows (R := R) (Prefix := Prefix)
      (Suffix := Suffix) (Factor := Factor) (Row := Row)) :
    FactorCiphertext R Prefix Suffix Factor :=
  accumulator.add (externalProduct digits controlRows)

@[simp]
theorem cmux_factor
    (accumulator : FactorCiphertext R Prefix Suffix Factor)
    (digits : Row → R)
    (controlRows : FactorRows (R := R) (Prefix := Prefix)
      (Suffix := Suffix) (Factor := Factor) (Row := Row)) :
    (cmux accumulator digits controlRows).factor =
      accumulator.factor +
        fun factor ↦ ∑ row, digits row * (controlRows row).factor factor := by
  rfl

theorem cmux_phase
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (accumulator : FactorCiphertext R Prefix Suffix Factor)
    (digits : Row → R)
    (controlRows : FactorRows (R := R) (Prefix := Prefix)
      (Suffix := Suffix) (Factor := Factor) (Row := Row)) :
    (cmux accumulator digits controlRows).phase gadget prefixSecret suffixSecret =
      accumulator.phase gadget prefixSecret suffixSecret +
        ∑ row, digits row *
          (controlRows row).phase gadget prefixSecret suffixSecret := by
  rw [cmux, FactorCiphertext.phase_add, externalProduct_phase]

/-- One data-dependent public CMUX control. -/
structure Control where
  digits : FactorCiphertext R Prefix Suffix Factor → Row → R
  rows : FactorRows (R := R) (Prefix := Prefix) (Suffix := Suffix)
    (Factor := Factor) (Row := Row)

/-- Execute a list of public CMUX controls.  Every digit vector is recomputed from the current
ciphertext, as in native blind rotation. -/
def run : FactorCiphertext R Prefix Suffix Factor →
    List (Control (R := R) (Prefix := Prefix) (Suffix := Suffix)
      (Factor := Factor) (Row := Row)) →
      FactorCiphertext R Prefix Suffix Factor
  | accumulator, [] => accumulator
  | accumulator, control :: controls =>
      run (cmux accumulator (control.digits accumulator) control.rows) controls

/-- Ghost recurrence for the exact factor produced by `run`. -/
def propagatedFactor : FactorCiphertext R Prefix Suffix Factor →
    List (Control (R := R) (Prefix := Prefix) (Suffix := Suffix)
      (Factor := Factor) (Row := Row)) → Factor → R
  | accumulator, [] => accumulator.factor
  | accumulator, control :: controls =>
      propagatedFactor
        (cmux accumulator (control.digits accumulator) control.rows) controls

theorem run_factor
    (accumulator : FactorCiphertext R Prefix Suffix Factor)
    (controls : List (Control (R := R) (Prefix := Prefix) (Suffix := Suffix)
      (Factor := Factor) (Row := Row))) :
    (run accumulator controls).factor = propagatedFactor accumulator controls := by
  induction controls generalizing accumulator with
  | nil => rfl
  | cons control controls ih =>
      exact ih (cmux accumulator (control.digits accumulator) control.rows)

end ExternalProduct

/-! ## Alignment with the executable native blind-rotation step -/

namespace Native

/-- Multiplication by a public signed rotation monomial propagates to the factor vector by the
same public scalar multiplication. -/
noncomputable def rotate
    {q degree : ℕ} [NeZero q]
    {Prefix Suffix Factor : Type}
    (exponent : Fin (2 * (degree + 1)))
    (ciphertext : FactorCiphertext (RLWE.Rq q (degree + 1)) Prefix Suffix Factor) :
    FactorCiphertext (RLWE.Rq q (degree + 1)) Prefix Suffix Factor :=
  ciphertext.scale (BlindRotation.rotationMonomial q degree exponent)

@[simp]
theorem rotate_factor
    {q degree : ℕ} [NeZero q]
    {Prefix Suffix Factor : Type}
    (exponent : Fin (2 * (degree + 1)))
    (ciphertext : FactorCiphertext (RLWE.Rq q (degree + 1)) Prefix Suffix Factor) :
    (rotate exponent ciphertext).factor =
      BlindRotation.rotationMonomial q degree exponent • ciphertext.factor := by
  rfl

theorem rotate_phase
    {q degree : ℕ} [NeZero q]
    {Prefix Suffix Factor : Type}
    [Fintype Prefix] [Fintype Suffix] [Fintype Factor]
    (ringGadget : Matrix Suffix Factor (RLWE.Rq q (degree + 1)))
    (prefixSecret : Prefix → RLWE.Rq q (degree + 1))
    (suffixSecret : Suffix → RLWE.Rq q (degree + 1))
    (exponent : Fin (2 * (degree + 1)))
    (ciphertext : FactorCiphertext (RLWE.Rq q (degree + 1)) Prefix Suffix Factor) :
    (rotate exponent ciphertext).phase ringGadget prefixSecret suffixSecret =
      BlindRotation.rotationMonomial q degree exponent *
        ciphertext.phase ringGadget prefixSecret suffixSecret := by
  exact FactorCiphertext.phase_scale ringGadget prefixSecret suffixSecret
    (BlindRotation.rotationMonomial q degree exponent) ciphertext

/-- The native complete-ciphertext CMUX update exposed by the normal-form theorem below. -/
noncomputable def cmuxStep
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (factor : RLWE.Rq q degree)
    (bootstrapKeyEntry : RingGSWCiphertext q degree rank params.levels)
    (accumulator : RingCiphertext q degree rank) :
    RingCiphertext q degree rank :=
  TLWE.add accumulator
    (TGSW.externalProduct (Gadget.Base.ringExtendedDigits params accumulator)
      (TGSW.scale (factor - 1) bootstrapKeyEntry))

/-- The executable TFHE blind-rotation step is exactly identity plus the external product with
the scaled homogeneous bootstrapping-key rows.  This equality is at complete-ciphertext level,
not merely at phase level. -/
theorem blindRotationStep_eq_add_externalProduct
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (factor : RLWE.Rq q degree)
    (bootstrapKeyEntry : RingGSWCiphertext q degree rank params.levels)
    (accumulator : RingCiphertext q degree rank) :
    BlindRotation.step params factor bootstrapKeyEntry accumulator =
      cmuxStep params factor bootstrapKeyEntry accumulator := by
  cases degree with
  | zero =>
      rw [TLWE.Ciphertext.mk.injEq]
      constructor
      · funext coordinate
        apply LatticeCrypto.Poly.ext_get_eq
        intro coefficient
        exact coefficient.elim0
      · apply LatticeCrypto.Poly.ext_get_eq
        intro coefficient
        exact coefficient.elim0
  | succ degree =>
      simpa only [BlindRotation.step, TGSW.affineFactor, cmuxStep] using
        (TGSW.externalProduct_addGadget_one
          (Gadget.Base.ringGadget params) accumulator
          (Gadget.Base.ringExtendedDigits params accumulator)
          (TGSW.scale (factor - 1) bootstrapKeyEntry)
          (Gadget.Base.ringExtendedDigits_decomposes params accumulator))

/-- Execute the complete native blind-rotation trace using only the CMUX normal form. -/
noncomputable def runCMUX {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) :
    RingCiphertext q degree rank →
      List (BlindRotation.Control q degree rank params.levels) →
        RingCiphertext q degree rank
  | accumulator, [] => accumulator
  | accumulator, control :: controls =>
      runCMUX params
        (cmuxStep params control.factor control.bootstrapKeyEntry accumulator) controls

/-- The existing executable blind-rotation fold and the complete CMUX-normal-form fold agree
exactly. -/
theorem blindRotationRun_eq_runCMUX
    {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (accumulator : RingCiphertext q degree rank)
    (controls : List (BlindRotation.Control q degree rank params.levels)) :
    BlindRotation.run params accumulator controls =
      runCMUX params accumulator controls := by
  induction controls generalizing accumulator with
  | nil => rfl
  | cons control controls ih =>
      rw [BlindRotation.run_cons]
      rw [blindRotationStep_eq_add_externalProduct]
      exact ih (cmuxStep params control.factor control.bootstrapKeyEntry accumulator)

/-- Native TFHE blind rotation is exactly the CMUX-normal-form trace on its public controls. -/
theorem nativeBlindRotate_eq_runCMUX
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (initialAccumulator : RingCiphertext q (degree + 1) rank) :
    BlindRotation.nativeBlindRotate params roundExponent input bootstrappingKey
        initialAccumulator =
      runCMUX params initialAccumulator
        (BlindRotation.publicNativeControls params roundExponent input bootstrappingKey) := by
  unfold BlindRotation.nativeBlindRotate
  exact blindRotationRun_eq_runCMUX params initialAccumulator
    (BlindRotation.publicNativeControls params roundExponent input bootstrappingKey)

end Native

/-! ## Compatible coefficient sample extraction -/

namespace Extraction

/-- Extract the reciprocal coefficient vector used for the mask part of native sample
extraction. -/
def extractVector {q degree rank : ℕ}
    (vector : Fin rank → RLWE.Rq q (degree + 1)) :
    Fin (rank * (degree + 1)) → ZMod q :=
  fun coordinate ↦
    let indexed := finProdFinEquiv.symm coordinate
    SampleExtraction.reciprocalCoefficients
      (LatticeCrypto.Poly.toPi (vector indexed.1)) indexed.2

/-- Sample extraction of a ring-valued factor-carrying ciphertext.  The factor itself is
coefficient-extracted as public ghost state. -/
def apply {q degree prefixRank suffixRank factorRank : ℕ}
    (ciphertext : FactorCiphertext (RLWE.Rq q (degree + 1))
      (Fin prefixRank) (Fin suffixRank) (Fin factorRank)) :
    FactorCiphertext (ZMod q)
      (Fin (prefixRank * (degree + 1)))
      (Fin (suffixRank * (degree + 1)))
      (Fin (factorRank * (degree + 1))) where
  prefixMask := extractVector ciphertext.prefixMask
  factor := extractVector ciphertext.factor
  body := SampleExtraction.constantCoefficient ciphertext.body

@[simp]
theorem apply_factor {q degree prefixRank suffixRank factorRank : ℕ}
    (ciphertext : FactorCiphertext (RLWE.Rq q (degree + 1))
      (Fin prefixRank) (Fin suffixRank) (Fin factorRank)) :
    (apply ciphertext).factor = extractVector ciphertext.factor := by
  rfl

/-- A ring gadget and a scalar gadget are extraction-compatible when scalar multiplication by
the extracted factor reproduces coefficient extraction of the implicit ring suffix mask. -/
def GadgetCompatible {q degree suffixRank factorRank : ℕ}
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1)))
    (scalarGadget : Matrix
      (Fin (suffixRank * (degree + 1)))
      (Fin (factorRank * (degree + 1))) (ZMod q)) : Prop :=
  ∀ factor,
    scalarGadget.mulVec (extractVector factor) =
      extractVector (ringGadget.mulVec factor)

theorem suffixMask_apply
    {q degree prefixRank suffixRank factorRank : ℕ}
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1)))
    (scalarGadget : Matrix
      (Fin (suffixRank * (degree + 1)))
      (Fin (factorRank * (degree + 1))) (ZMod q))
    (compatible : GadgetCompatible ringGadget scalarGadget)
    (ciphertext : FactorCiphertext (RLWE.Rq q (degree + 1))
      (Fin prefixRank) (Fin suffixRank) (Fin factorRank)) :
    (apply ciphertext).suffixMask scalarGadget =
      extractVector (ciphertext.suffixMask ringGadget) := by
  exact compatible ciphertext.factor

/-- The extracted-vector dot product is exactly the constant coefficient of the original ring
dot product. -/
theorem dotProduct_extractedSecret_extractVector
    {q degree rank : ℕ} [NeZero q]
    (secret vector : Fin rank → RLWE.Rq q (degree + 1)) :
    dotProduct (SampleExtraction.extractedSecret secret) (extractVector vector) =
      SampleExtraction.constantCoefficient (dotProduct secret vector) := by
  let ciphertext : RingCiphertext q (degree + 1) rank :=
    ⟨vector, 0⟩
  change dotProduct (SampleExtraction.extractedSecret secret)
      (SampleExtraction.apply ciphertext).mask =
    SampleExtraction.constantCoefficient (dotProduct secret vector)
  exact SampleExtraction.dotProduct_extractedSecret_apply_mask secret ciphertext

/-- Under the explicit gadget compatibility equation, sample extraction preserves the complete
factor-carrying phase exactly. -/
theorem phase_apply
    {q degree prefixRank suffixRank factorRank : ℕ} [NeZero q]
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1)))
    (scalarGadget : Matrix
      (Fin (suffixRank * (degree + 1)))
      (Fin (factorRank * (degree + 1))) (ZMod q))
    (compatible : GadgetCompatible ringGadget scalarGadget)
    (prefixSecret : Fin prefixRank → RLWE.Rq q (degree + 1))
    (suffixSecret : Fin suffixRank → RLWE.Rq q (degree + 1))
    (ciphertext : FactorCiphertext (RLWE.Rq q (degree + 1))
      (Fin prefixRank) (Fin suffixRank) (Fin factorRank)) :
    (apply ciphertext).phase scalarGadget
        (SampleExtraction.extractedSecret prefixSecret)
        (SampleExtraction.extractedSecret suffixSecret) =
      SampleExtraction.constantCoefficient
        (ciphertext.phase ringGadget prefixSecret suffixSecret) := by
  unfold FactorCiphertext.phase
  change SampleExtraction.constantCoefficient ciphertext.body -
      dotProduct (SampleExtraction.extractedSecret prefixSecret)
        (extractVector ciphertext.prefixMask) -
      dotProduct (SampleExtraction.extractedSecret suffixSecret)
        ((apply ciphertext).suffixMask scalarGadget) = _
  rw [suffixMask_apply ringGadget scalarGadget compatible]
  rw [dotProduct_extractedSecret_extractVector]
  rw [dotProduct_extractedSecret_extractVector]
  change Gadget.Base.coefficientAddHom (degree + 1) 0 ciphertext.body -
      Gadget.Base.coefficientAddHom (degree + 1) 0
        (dotProduct prefixSecret ciphertext.prefixMask) -
      Gadget.Base.coefficientAddHom (degree + 1) 0
        (dotProduct suffixSecret (ciphertext.suffixMask ringGadget)) = _
  rw [← map_sub, ← map_sub]
  rfl

end Extraction

/-! ## Deterministic factor-energy bounds -/

namespace Energy

/-- Squared Euclidean energy of a real factor vector. -/
def factorEnergy {Factor : Type} [Fintype Factor] (factor : Factor → ℝ) : ℝ :=
  ∑ coordinate, (factor coordinate) ^ 2

/-- Euclidean cross term between two real factor vectors. -/
def factorInner {Factor : Type} [Fintype Factor]
    (left right : Factor → ℝ) : ℝ :=
  ∑ coordinate, left coordinate * right coordinate

theorem factorInner_self {Factor : Type} [Fintype Factor]
    (factor : Factor → ℝ) :
    factorInner factor factor = factorEnergy factor := by
  simp [factorInner, factorEnergy, pow_two]

/-- Exact polarization identity.  Keeping this term explicit permits a later correlation-aware
trace analysis instead of committing to a triangle-inequality loss. -/
theorem factorEnergy_add_eq
    {Factor : Type} [Fintype Factor]
    (left right : Factor → ℝ) :
    factorEnergy (left + right) =
      factorEnergy left + factorEnergy right + 2 * factorInner left right := by
  unfold factorEnergy factorInner
  simp only [Pi.add_apply, add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross :
      (∑ coordinate, 2 * left coordinate * right coordinate) =
        2 * ∑ coordinate, left coordinate * right coordinate := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [hcross]
  ring

theorem factorEnergy_nonneg {Factor : Type} [Fintype Factor]
    (factor : Factor → ℝ) : 0 ≤ factorEnergy factor := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem factorEnergy_add_le_two
    {Factor : Type} [Fintype Factor]
    (left right : Factor → ℝ) :
    factorEnergy (left + right) ≤
      2 * (factorEnergy left + factorEnergy right) := by
  unfold factorEnergy
  calc
    (∑ coordinate, (left coordinate + right coordinate) ^ 2) ≤
        ∑ coordinate, 2 *
          ((left coordinate) ^ 2 + (right coordinate) ^ 2) := by
      apply Finset.sum_le_sum
      intro coordinate _
      simpa using
        (add_sq_le : (left coordinate + right coordinate) ^ 2 ≤
          2 * ((left coordinate) ^ 2 + (right coordinate) ^ 2))
    _ = 2 * ((∑ coordinate, (left coordinate) ^ 2) +
        ∑ coordinate, (right coordinate) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]

theorem factorEnergy_smul
    {Factor : Type} [Fintype Factor]
    (scalar : ℝ) (factor : Factor → ℝ) :
    factorEnergy (scalar • factor) = scalar ^ 2 * factorEnergy factor := by
  unfold factorEnergy
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]

/-- Cauchy--Schwarz bound for the factor energy of a complete external product. -/
theorem factorEnergy_linearCombination_le
    {Prefix Suffix Factor Row : Type}
    [Fintype Prefix] [Fintype Suffix] [Fintype Factor] [Fintype Row]
    (digits : Row → ℝ)
    (rows : FactorRows (R := ℝ) (Prefix := Prefix) (Suffix := Suffix)
      (Factor := Factor) (Row := Row)) :
    factorEnergy (externalProduct digits rows).factor ≤
      (∑ row, (digits row) ^ 2) *
        ∑ row, factorEnergy (rows row).factor := by
  unfold factorEnergy
  simp only [externalProduct_factor]
  calc
    (∑ factor, (∑ row, digits row * (rows row).factor factor) ^ 2) ≤
        ∑ factor, (∑ row, (digits row) ^ 2) *
          ∑ row, ((rows row).factor factor) ^ 2 := by
      apply Finset.sum_le_sum
      intro factor _
      simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
          digits (fun row ↦ (rows row).factor factor))
    _ = (∑ row, (digits row) ^ 2) *
        ∑ row, ∑ factor, ((rows row).factor factor) ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

/-- One CMUX step has an explicit deterministic energy recurrence. -/
theorem factorEnergy_cmux_le
    {Prefix Suffix Factor Row : Type}
    [Fintype Prefix] [Fintype Suffix] [Fintype Factor] [Fintype Row]
    (accumulator : FactorCiphertext ℝ Prefix Suffix Factor)
    (digits : Row → ℝ)
    (controlRows : FactorRows (R := ℝ) (Prefix := Prefix) (Suffix := Suffix)
      (Factor := Factor) (Row := Row)) :
    factorEnergy (cmux accumulator digits controlRows).factor ≤
      2 * (factorEnergy accumulator.factor +
        (∑ row, (digits row) ^ 2) *
          ∑ row, factorEnergy (controlRows row).factor) := by
  have hadd := factorEnergy_add_le_two accumulator.factor
    (externalProduct digits controlRows).factor
  rw [cmux_factor]
  exact hadd.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (factorEnergy_linearCombination_le digits controlRows))
    (by norm_num))

/-- Exact correlation-aware CMUX factor-energy recurrence. -/
theorem factorEnergy_cmux_eq
    {Prefix Suffix Factor Row : Type}
    [Fintype Prefix] [Fintype Suffix] [Fintype Factor] [Fintype Row]
    (accumulator : FactorCiphertext ℝ Prefix Suffix Factor)
    (digits : Row → ℝ)
    (controlRows : FactorRows (R := ℝ) (Prefix := Prefix) (Suffix := Suffix)
      (Factor := Factor) (Row := Row)) :
    factorEnergy (cmux accumulator digits controlRows).factor =
      factorEnergy accumulator.factor +
        factorEnergy (externalProduct digits controlRows).factor +
        2 * factorInner accumulator.factor
          (externalProduct digits controlRows).factor := by
  rw [cmux_factor]
  exact factorEnergy_add_eq accumulator.factor
    (externalProduct digits controlRows).factor

/-- Uniform deterministic recurrence used to bound a trace of CMUX steps. -/
def traceBound (digitEnergy rowEnergy : ℝ) : ℕ → ℝ → ℝ
  | 0, initial => initial
  | steps + 1, initial =>
      traceBound digitEnergy rowEnergy steps
        (2 * (initial + digitEnergy * rowEnergy))

theorem traceBound_mono_initial
    (digitEnergy rowEnergy : ℝ) (steps : ℕ) :
    Monotone (traceBound digitEnergy rowEnergy steps) := by
  induction steps with
  | zero => exact monotone_id
  | succ steps ih =>
      intro left right hle
      apply ih
      gcongr

/-- Complete deterministic trace bound.  Digit vectors may depend on every intermediate public
ciphertext; only their squared energy and the total control-row factor energy are bounded. -/
theorem factorEnergy_run_le_traceBound
    {Prefix Suffix Factor Row : Type}
    [Fintype Prefix] [Fintype Suffix] [Fintype Factor] [Fintype Row]
    (accumulator : FactorCiphertext ℝ Prefix Suffix Factor)
    (controls : List (Control (R := ℝ) (Prefix := Prefix) (Suffix := Suffix)
      (Factor := Factor) (Row := Row)))
    (digitEnergy rowEnergy initialBound : ℝ)
    (hdigit : 0 ≤ digitEnergy)
    (hinitial : factorEnergy accumulator.factor ≤ initialBound)
    (hdigits : ∀ control ∈ controls,
      ∀ current : FactorCiphertext ℝ Prefix Suffix Factor,
        (∑ row, (control.digits current row) ^ 2) ≤ digitEnergy)
    (hrows : ∀ control ∈ controls,
      (∑ row, factorEnergy (control.rows row).factor) ≤ rowEnergy) :
    factorEnergy (run accumulator controls).factor ≤
      traceBound digitEnergy rowEnergy controls.length initialBound := by
  induction controls generalizing accumulator initialBound with
  | nil => simpa [run, traceBound] using hinitial
  | cons control controls ih =>
      have hstep := factorEnergy_cmux_le accumulator
        (control.digits accumulator) control.rows
      have hdigitControl :
          (∑ row, (control.digits accumulator row) ^ 2) ≤ digitEnergy :=
        hdigits control (by simp) accumulator
      have hrowControl :
          (∑ row, factorEnergy (control.rows row).factor) ≤ rowEnergy :=
        hrows control (by simp)
      have hproduct :
          (∑ row, (control.digits accumulator row) ^ 2) *
              ∑ row, factorEnergy (control.rows row).factor ≤
            digitEnergy * rowEnergy := by
        exact mul_le_mul hdigitControl hrowControl
          (Finset.sum_nonneg fun _ _ ↦ factorEnergy_nonneg _)
          hdigit
      have hnext :
          factorEnergy
              (cmux accumulator (control.digits accumulator) control.rows).factor ≤
            2 * (initialBound + digitEnergy * rowEnergy) := by
        calc
          _ ≤ 2 * (factorEnergy accumulator.factor +
              (∑ row, (control.digits accumulator row) ^ 2) *
                ∑ row, factorEnergy (control.rows row).factor) := hstep
          _ ≤ 2 * (initialBound + digitEnergy * rowEnergy) := by
            gcongr
      have htailDigits : ∀ item ∈ controls,
          ∀ current : FactorCiphertext ℝ Prefix Suffix Factor,
            (∑ row, (item.digits current row) ^ 2) ≤ digitEnergy := by
        intro item hmem
        exact hdigits item (by simp [hmem])
      have htailRows : ∀ item ∈ controls,
          (∑ row, factorEnergy (item.rows row).factor) ≤ rowEnergy := by
        intro item hmem
        exact hrows item (by simp [hmem])
      simpa [run, traceBound] using
        ih (cmux accumulator (control.digits accumulator) control.rows)
          (2 * (initialBound + digitEnergy * rowEnergy)) hnext
          htailDigits htailRows

end Energy

end FormalProof4FHE.TFHE.SourceAlignedFactorPropagation
