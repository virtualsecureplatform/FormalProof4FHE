/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.SampleRestriction
import FormalProof4FHE.RLWE.Basic

/-!
# Finite TLWE and TGSW Syntax

This file formalizes the native algebraic layout of the TLWE and TGSW objects used by TFHE.  The
original TFHE paper works over the real torus.  Here the coefficient domain is an arbitrary finite
ring, and the native finite specialization uses `ZMod q` and the executable negacyclic ring
`RLWE.Rq q degree`.  This is the standard finite-modulus model required by the repository's
`ProbComp` security games; it does not identify a finite sampler with the paper's ideal continuous
Gaussian.

A batch of TLWE rows is represented by the existing matrix-LWE transcript: one public mask per
column and one body coordinate per column.  A TGSW ciphertext of message `message` is exactly

`Z + message * H`,

where `Z` is a batch of `(dimension + 1) * levels` homogeneous TLWE rows and `H` is the block
diagonal gadget matrix.  Keeping this representation exposes both the mask and body shifts of the
structured TGSW distribution; it must not be confused with a batch that merely encrypts the same
scalar message independently in every row.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE

/-- A binary secret with the given number of scalar coordinates. -/
abbrev BinarySecret (dimension : ℕ) := Fin dimension → Bool

/-- Embed a bit as zero or one in a coefficient ring. -/
def embedBit {R : Type} [Zero R] [One R] (bit : Bool) : R :=
  if bit then 1 else 0

/-- Coefficient-wise embedding of a binary secret into a ring-valued secret. -/
def embedBinarySecret {R : Type} [Zero R] [One R] {dimension : ℕ}
    (secret : BinarySecret dimension) : Fin dimension → R :=
  fun index ↦ embedBit (secret index)

namespace TLWE

/-- One TLWE row `(a, b)` over `R`, with `dimension` mask coordinates. -/
structure Ciphertext (R : Type) (dimension : ℕ) where
  mask : Fin dimension → R
  body : R

/-- A TLWE row is exactly its public mask/body pair. -/
def ciphertextEquiv (R : Type) (dimension : ℕ) :
    ((Fin dimension → R) × R) ≃ Ciphertext R dimension where
  toFun value := ⟨value.1, value.2⟩
  invFun ciphertext := (ciphertext.mask, ciphertext.body)
  left_inv value := by cases value; rfl
  right_inv ciphertext := by cases ciphertext; rfl

/-- TLWE rows over a finite coefficient carrier form a finite response type. -/
noncomputable instance instFintypeCiphertext {R : Type} {dimension : ℕ} [Fintype R] :
    Fintype (Ciphertext R dimension) :=
  Fintype.ofEquiv ((Fin dimension → R) × R) (ciphertextEquiv R dimension)

/-- The all-default mask/body pair inhabits every TLWE row type over an inhabited carrier. -/
instance instInhabitedCiphertext {R : Type} {dimension : ℕ} [Inhabited R] :
    Inhabited (Ciphertext R dimension) :=
  ⟨⟨fun _ ↦ default, default⟩⟩

/-- The TLWE phase `b - ⟨s, a⟩`. -/
def phase {R : Type} [Ring R] {dimension : ℕ}
    (secret : Fin dimension → R) (ciphertext : Ciphertext R dimension) : R :=
  ciphertext.body - dotProduct secret ciphertext.mask

/-- Assemble a deterministic TLWE row from its mask, message, and error. -/
def assemble {R : Type} [Semiring R] {dimension : ℕ}
    (secret mask : Fin dimension → R) (message error : R) : Ciphertext R dimension :=
  ⟨mask, dotProduct secret mask + message + error⟩

/-- The phase of an assembled TLWE row is exactly its message plus error. -/
@[simp]
theorem phase_assemble {R : Type} [Ring R] {dimension : ℕ}
    (secret mask : Fin dimension → R) (message error : R) :
    phase secret (assemble secret mask message error) = message + error := by
  simp only [phase, assemble]
  abel

/-- Sample one fresh finite-modulus TLWE encryption. -/
def encrypt {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    {dimension : ℕ} (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (message : R) : ProbComp (Ciphertext R dimension) := do
  let mask ← $ᵗ (Fin dimension → R)
  let error ← errorSampler
  return assemble secret mask message error

/-- A trivial noiseless TLWE row with zero mask. -/
def trivial {R : Type} [Semiring R] {dimension : ℕ} (message : R) : Ciphertext R dimension :=
  ⟨0, message⟩

/-- The phase of a trivial row is its body. -/
@[simp]
theorem phase_trivial {R : Type} [Ring R] {dimension : ℕ}
    (secret : Fin dimension → R) (message : R) :
    phase secret (trivial (dimension := dimension) message) = message := by
  simp [phase, trivial, dotProduct]

/-- A matrix of masks and its corresponding vector of TLWE bodies. -/
abbrev BatchCiphertext (R : Type) (dimension samples : ℕ) :=
  FormalProof4FHE.LWE.BatchTranscript R dimension samples

/-- Read one column of a batched TLWE ciphertext as an individual row. -/
def entry {R : Type} {dimension samples : ℕ}
    (ciphertext : BatchCiphertext R dimension samples) (sample : Fin samples) :
    Ciphertext R dimension :=
  ⟨fun coordinate ↦ ciphertext.1 coordinate sample, ciphertext.2 sample⟩

/-- Compute all TLWE phases in a batch. -/
def batchPhase {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R) (ciphertext : BatchCiphertext R dimension samples) :
    Fin samples → R :=
  ciphertext.2 - vecMul secret ciphertext.1

/-- Assemble a deterministic batch of TLWE rows. -/
def batchAssemble {R : Type} [Semiring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error : Fin samples → R) : BatchCiphertext R dimension samples :=
  (challenge, vecMul secret challenge + message + error)

/-- Batched TLWE assembly has the expected message-plus-error phase vector. -/
@[simp]
theorem batchPhase_batchAssemble {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error : Fin samples → R) :
    batchPhase secret (batchAssemble secret challenge message error) = message + error := by
  funext sample
  simp only [batchPhase, batchAssemble, Pi.sub_apply, Pi.add_apply]
  abel

/-- Assembling a zero-message batch is the ordinary batch-LWE transcript form. -/
@[simp]
theorem batchAssemble_zero {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) :
    batchAssemble secret challenge 0 error =
      (challenge, vecMul secret challenge + error) := by
  apply Prod.ext
  · rfl
  · funext sample
    simp [batchAssemble]

/-- The scalar phase of a selected row agrees with the corresponding batch phase. -/
@[simp]
theorem phase_entry {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R) (ciphertext : BatchCiphertext R dimension samples)
    (sample : Fin samples) :
    phase secret (entry ciphertext sample) = batchPhase secret ciphertext sample := by
  rfl

/-- Sample a fixed-message batch of fresh TLWE rows under one shared secret. -/
def batchEncrypt {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (message : Fin samples → R) :
    ProbComp (BatchCiphertext R dimension samples) := do
  let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
  let error ← ProbComp.sampleIID samples errorSampler
  return batchAssemble secret challenge message error

end TLWE

namespace TGSW

/-- The number of homogeneous TLWE rows in a native TGSW ciphertext. -/
abbrev rowCount (dimension levels : ℕ) := (dimension + 1) * levels

/-- A native TGSW matrix, represented as its batch of TLWE rows. -/
abbrev Ciphertext (R : Type) (dimension levels : ℕ) :=
  TLWE.BatchCiphertext R dimension (rowCount dimension levels)

/-- Recover the extended-coordinate block and gadget level of a flattened TGSW row. -/
def rowIndex {dimension levels : ℕ} (row : Fin (rowCount dimension levels)) :
    Fin (dimension + 1) × Fin levels :=
  finProdFinEquiv.symm row

/-- Mask part of `message * H`.  Blocks `0, ..., dimension - 1` shift their matching mask
coordinate; the final block has no mask shift. -/
def gadgetMaskShift {R : Type} [Zero R] [Mul R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    Matrix (Fin dimension) (Fin (rowCount dimension levels)) R :=
  fun coordinate row ↦
    let indexed := rowIndex row
    if indexed.1.val = coordinate.val then message * gadget indexed.2 else 0

/-- Body part of `message * H`.  Only the final extended-coordinate block shifts the TLWE body. -/
def gadgetBodyShift {R : Type} [Zero R] [Mul R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    Fin (rowCount dimension levels) → R :=
  fun row ↦
    let indexed := rowIndex row
    if indexed.1.val = dimension then message * gadget indexed.2 else 0

/-- Add the block-diagonal gadget matrix `message * H` to homogeneous TLWE rows. -/
def addGadget {R : Type} [Semiring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (homogeneous : Ciphertext R dimension levels) : Ciphertext R dimension levels :=
  (homogeneous.1 + gadgetMaskShift gadget message,
    homogeneous.2 + gadgetBodyShift gadget message)

/-- Adding a zero TGSW message leaves all homogeneous rows unchanged. -/
@[simp]
theorem addGadget_zero {R : Type} [Semiring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (homogeneous : Ciphertext R dimension levels) :
    addGadget gadget 0 homogeneous = homogeneous := by
  apply Prod.ext
  · funext coordinate row
    simp [addGadget, gadgetMaskShift]
  · funext row
    simp [addGadget, gadgetBodyShift]

/-- Sample the native structured TGSW distribution `Z + message * H`. -/
def encrypt {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    ProbComp (Ciphertext R dimension levels) := do
  let homogeneous ← TLWE.batchEncrypt dimension (rowCount dimension levels)
    errorSampler secret 0
  return addGadget gadget message homogeneous

/-- Sample a native TGSW encryption of zero with the same row layout and error distribution. -/
def encryptZero {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) :
    ProbComp (Ciphertext R dimension levels) :=
  encrypt dimension levels errorSampler secret gadget 0

/-- The phase contribution made by the structured gadget matrix. -/
def gadgetPhase {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    Fin (rowCount dimension levels) → R :=
  gadgetBodyShift gadget message - vecMul secret (gadgetMaskShift gadget message)

/-- Adding `message * H` shifts the vector of TLWE phases by exactly its gadget phase. -/
theorem batchPhase_addGadget {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (homogeneous : Ciphertext R dimension levels) :
    TLWE.batchPhase secret (addGadget gadget message homogeneous) =
      TLWE.batchPhase secret homogeneous + gadgetPhase secret gadget message := by
  funext row
  simp only [TLWE.batchPhase, addGadget, gadgetPhase, Pi.sub_apply, Pi.add_apply,
    Matrix.vecMul, dotProduct, Matrix.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  abel

end TGSW

/-- A vector of binary negacyclic polynomials, the native TRLWE secret-key shape. -/
abbrev RingBinarySecret (rank degree : ℕ) := Fin rank → Fin degree → Bool

/-- Embed one binary coefficient polynomial in the executable negacyclic ring. -/
def embedBinaryPolynomial (q degree : ℕ) (polynomial : Fin degree → Bool) :
    RLWE.Rq q degree :=
  LatticeCrypto.Poly.ofPi fun index ↦ embedBit (polynomial index)

/-- Embed a binary TRLWE key coefficient-wise in `Rq`. -/
def embedRingSecret (q : ℕ) {rank degree : ℕ}
    (secret : RingBinarySecret rank degree) : Fin rank → RLWE.Rq q degree :=
  fun component ↦ embedBinaryPolynomial q degree (secret component)

/-- Flatten the coefficients of a TRLWE key in the order used by TFHE `KeyExtract`. -/
def keyExtract {rank degree : ℕ}
    (secret : RingBinarySecret rank degree) : BinarySecret (rank * degree) :=
  fun coordinate ↦
    let indexed := finProdFinEquiv.symm coordinate
    secret indexed.1 indexed.2

/-- Key extraction is coefficient flattening through `finProdFinEquiv`. -/
@[simp]
theorem keyExtract_apply {rank degree : ℕ} (secret : RingBinarySecret rank degree)
    (component : Fin rank) (coefficient : Fin degree) :
    keyExtract secret (finProdFinEquiv (component, coefficient)) = secret component coefficient := by
  simp [keyExtract]

/-- Reassemble a vector in native key-switch order into a vector of binary polynomials. -/
def keyUnextract {rank degree : ℕ}
    (secret : BinarySecret (rank * degree)) : RingBinarySecret rank degree :=
  fun component coefficient ↦ secret (finProdFinEquiv (component, coefficient))

/-- Reassembling the coefficient extraction of a ring key recovers that ring key exactly. -/
@[simp]
theorem keyUnextract_keyExtract {rank degree : ℕ}
    (secret : RingBinarySecret rank degree) :
    keyUnextract (keyExtract secret) = secret := by
  funext component coefficient
  simp [keyUnextract]

/-- Extracting a reassembled flat binary key recovers the original flat key exactly. -/
@[simp]
theorem keyExtract_keyUnextract {rank degree : ℕ}
    (secret : BinarySecret (rank * degree)) :
    keyExtract (keyUnextract secret : RingBinarySecret rank degree) = secret := by
  funext coordinate
  obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
  simp [keyUnextract]

/-- Native coefficient extraction is an equivalence, not a lossy projection. -/
def keyExtractEquiv (rank degree : ℕ) :
    RingBinarySecret rank degree ≃ BinarySecret (rank * degree) where
  toFun := keyExtract
  invFun := keyUnextract
  left_inv := keyUnextract_keyExtract
  right_inv := keyExtract_keyUnextract

/-- Embed a bit as a constant polynomial in the negacyclic ring. -/
def embedConstantBit (q degree : ℕ) (bit : Bool) : RLWE.Rq q degree :=
  embedBinaryPolynomial q degree fun coefficient ↦ coefficient.val = 0 && bit

/-- Scalar finite-modulus TLWE ciphertexts used before and after TFHE bootstrapping. -/
abbrev ScalarCiphertext (q dimension : ℕ) := TLWE.Ciphertext (ZMod q) dimension

/-- Ring TLWE (TRLWE) ciphertexts used by the TFHE accumulator. -/
abbrev RingCiphertext (q degree rank : ℕ) :=
  TLWE.Ciphertext (RLWE.Rq q degree) rank

/-- Ring TGSW (TRGSW) ciphertexts used in a TFHE bootstrapping key. -/
abbrev RingGSWCiphertext (q degree rank levels : ℕ) :=
  TGSW.Ciphertext (RLWE.Rq q degree) rank levels

end FormalProof4FHE.TFHE
