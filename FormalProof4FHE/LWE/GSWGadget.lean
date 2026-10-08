/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWOperations
import FormalProof4FHE.TFHE.GadgetDecomposition
import FormalProof4FHE.TFHE.BootstrappingCorrectness

/-!
# Executable rectangular GSW products with bounded digits

Lift the existing scalar base decomposition to the actual rectangular GSW matrix. Every
ciphertext has a publicly computable digit matrix which reconstructs exactly and has short
unsigned entries. This discharges the reconstruction premise of `GSWOperations.noise_mul`.

The deterministic centered-noise bound retains the multiplication asymmetry. Right-associated
products of bit ciphertexts have a bound linear in the number of inputs, provided each input
has the same noise bound under the same secret. This is a correctness component for the GSW
bootstrap, not a refresh algorithm or an ordinary-LWE proof of the self-key tape's security.
The deterministic digit bounds are weaker than AP14's randomized subgaussian bounds.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWGadget

abbrev Parameters := TFHE.Gadget.Base.Parameters

abbrev Ciphertext {q : ℕ} (params : Parameters q) (rows : ℕ) :=
  Matrix (Fin rows) (Fin (rows * params.levels)) (ZMod q)

/-- Public block-diagonal powers-of-base gadget. Body-first GSW uses `rows=dimension+1`. -/
def gadget {q : ℕ} [NeZero q] (params : Parameters q) (rows : ℕ) : Ciphertext params rows :=
  fun row column ↦
    let position := finProdFinEquiv.symm column
    if row = position.1 then TFHE.Gadget.Base.gadget params position.2 else 0

/-- Digit row indices have the same block/level order as gadget columns. -/
def digitMatrix {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (ciphertext : Ciphertext params rows) :
    Matrix (Fin (rows * params.levels)) (Fin (rows * params.levels)) (ZMod q) :=
  fun encodedRow column ↦
    let position := finProdFinEquiv.symm encodedRow
    TFHE.Gadget.Base.digit params (ciphertext position.1 column) position.2

/-- Every ciphertext is reconstructed by the concrete public decomposition. -/
theorem gadget_mul_digitMatrix {q : ℕ} [NeZero q] {rows : ℕ}
    (params : Parameters q) (ciphertext : Ciphertext params rows) :
    gadget params rows * digitMatrix params ciphertext = ciphertext := by
  ext row column
  simp only [Matrix.mul_apply]
  calc
    _ = ∑ position : Fin rows × Fin params.levels,
        gadget params rows row (finProdFinEquiv position) *
          digitMatrix params ciphertext (finProdFinEquiv position) column := by
      exact (Fintype.sum_equiv finProdFinEquiv _ _ (fun _ ↦ rfl)).symm
    _ = ciphertext row column := by
      simp only [Fintype.sum_prod_type, gadget, digitMatrix, Equiv.symm_apply_apply,
        ite_mul, zero_mul]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      simpa only [TFHE.Gadget.recompose, mul_comm] using
        TFHE.Gadget.Base.recompose params (ciphertext row column)

/-- Centered digit magnitude is at most `base-1`, uniformly over all ciphertexts. -/
theorem digitMatrix_centered_bound {q : ℕ} [NeZero q] {rows : ℕ}
    (params : Parameters q) (ciphertext : Ciphertext params rows)
    (encodedRow column : Fin (rows * params.levels)) :
    (LatticeCrypto.centeredRepr (digitMatrix params ciphertext encodedRow column)).natAbs ≤
      params.base - 1 := by
  let position := finProdFinEquiv.symm encodedRow
  have hsmall := TFHE.Gadget.Base.natDigit_lt_base params
    (ciphertext position.1 column) position.2
  exact (TFHE.NoiseBounds.centeredRepr_natCast_natAbs_le
    (TFHE.Gadget.Base.natDigit params (ciphertext position.1 column) position.2)).trans
    (by omega)

/-- Executable multiplication uses no secret information. -/
def multiply {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (first second : Ciphertext params rows) : Ciphertext params rows :=
  first * digitMatrix params second

/-- The multiplication noise identity now has no unimplemented reconstruction hypothesis. -/
theorem noise_multiply {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (secret : Fin rows → ZMod q) (first second : Ciphertext params rows)
    (firstMessage secondMessage : ZMod q) :
    GSWOperations.noise secret (gadget params rows) (multiply params first second)
        (firstMessage * secondMessage) =
      vecMul (GSWOperations.noise secret (gadget params rows) first firstMessage)
        (digitMatrix params second) +
      firstMessage • GSWOperations.noise secret (gadget params rows) second secondMessage :=
  GSWOperations.noise_mul secret (gadget params rows) first second
    (digitMatrix params second) firstMessage secondMessage (gadget_mul_digitMatrix params second)

/-- A real modular-noise bound on every column, rather than just a ring equality. -/
def NoiseBound {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (secret : Fin rows → ZMod q) (ciphertext : Ciphertext params rows)
    (message : ZMod q) (bound : ℕ) : Prop :=
  ∀ column, (LatticeCrypto.centeredRepr
    (GSWOperations.noise secret (gadget params rows) ciphertext message column)).natAbs ≤ bound

/-- The deterministic cost of multiplying one fresh error vector by a digit matrix. -/
def growth {q : ℕ} (params : Parameters q) (rows : ℕ) : ℕ :=
  (rows * params.levels) * (params.base - 1)

/-- Bounded short digits give an explicit columnwise product bound. -/
theorem vecMul_error_bound {q : ℕ} [NeZero q] {rows : ℕ}
    (params : Parameters q) (error : Fin (rows * params.levels) → ZMod q)
    (ciphertext : Ciphertext params rows) (bound : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ bound)
    (column : Fin (rows * params.levels)) :
    (LatticeCrypto.centeredRepr (vecMul error (digitMatrix params ciphertext) column)).natAbs ≤
      growth params rows * bound := by
  change (LatticeCrypto.centeredRepr (∑ row, error row *
    digitMatrix params ciphertext row column)).natAbs ≤ _
  calc
    _ ≤ ∑ row, (LatticeCrypto.centeredRepr
        (error row * digitMatrix params ciphertext row column)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ Finset.univ
    _ ≤ ∑ _row : Fin (rows * params.levels), bound * (params.base - 1) := by
      apply Finset.sum_le_sum
      intro row _
      exact (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
        (Nat.mul_le_mul (herror row) (digitMatrix_centered_bound params ciphertext row column))
    _ = growth params rows * bound := by
      simp [growth]
      ring

/-- Bit plaintexts are represented as zero or one in the coefficient ring. -/
def bitMessage {R : Type} [Zero R] [One R] (bit : Bool) : R := if bit then 1 else 0

theorem bitMessage_and {R : Type} [Semiring R] (first second : Bool) :
    bitMessage (R := R) (first && second) = bitMessage first * bitMessage second := by
  cases first <;> cases second <;> simp [bitMessage]

/-- The right error enters with coefficient zero or one, preserving asymmetric growth. -/
theorem noiseBound_multiply_bits {q : ℕ} [NeZero q] {rows : ℕ}
    (params : Parameters q) (secret : Fin rows → ZMod q)
    (first second : Ciphertext params rows) (firstBit secondBit : Bool)
    (firstBound secondBound : ℕ)
    (hfirst : NoiseBound params secret first (bitMessage firstBit) firstBound)
    (hsecond : NoiseBound params secret second (bitMessage secondBit) secondBound) :
    NoiseBound params secret (multiply params first second)
      (bitMessage (firstBit && secondBit)) (growth params rows * firstBound + secondBound) := by
  intro column
  rw [bitMessage_and, noise_multiply]
  apply (TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _).trans
  apply Nat.add_le_add
  · exact vecMul_error_bound params _ second firstBound hfirst column
  · cases firstBit with
    | false => simp [bitMessage, LatticeCrypto.centeredRepr_eq_valMinAbs]
    | true => simpa [bitMessage] using hsecond column

/-- Public right-associated product; the fixed final gadget encrypts one with zero noise. -/
def rightProduct {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q) :
    List (Bool × Ciphertext params rows) → Ciphertext params rows
  | [] => gadget params rows
  | entry :: tail => multiply params entry.2 (rightProduct params tail)

def rightMessage {q : ℕ} {rows : ℕ} {params : Parameters q} :
    List (Bool × Ciphertext params rows) → Bool
  | [] => true
  | entry :: tail => entry.1 && rightMessage tail

/-- Linear chain bound under one unchanged secret. The implementation is deterministic;
this theorem assumes no independence among inputs and no ciphertext-security property. -/
theorem noiseBound_rightProduct {q : ℕ} [NeZero q] {rows : ℕ}
    (params : Parameters q) (secret : Fin rows → ZMod q)
    (inputs : List (Bool × Ciphertext params rows)) (bound : ℕ)
    (hinputs : ∀ entry ∈ inputs, NoiseBound params secret entry.2 (bitMessage entry.1) bound) :
    NoiseBound params secret (rightProduct params inputs) (bitMessage (rightMessage inputs))
      (inputs.length * growth params rows * bound) := by
  induction inputs with
  | nil =>
    intro column
    simp [rightProduct, rightMessage, bitMessage, GSWOperations.noise,
      LatticeCrypto.centeredRepr_eq_valMinAbs]
  | cons entry tail ih =>
    have hhead := hinputs entry (List.mem_cons_self ..)
    have htail := ih (fun item hitem ↦ hinputs item (List.mem_cons_of_mem _ hitem))
    simpa only [rightProduct, rightMessage, List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.mul_assoc, Nat.add_comm] using
      noiseBound_multiply_bits params secret entry.2 (rightProduct params tail)
        entry.1 (rightMessage tail) bound (tail.length * growth params rows * bound) hhead htail

/-- Body-first column layout for actual freshly sampled ciphertexts. -/
def layout {q : ℕ} [NeZero q] (params : Parameters q) (dimension : ℕ) :
    GSWSelfKey.Layout (ZMod q) dimension ((dimension + 1) * params.levels) where
  coordinate column :=
    Fin.cases none some (finProdFinEquiv.symm column).1
  weight column := TFHE.Gadget.Base.gadget params (finProdFinEquiv.symm column).2

/-- The concrete block gadget agrees with the gadget in the fresh GSW model. -/
theorem gadgetMatrix_layout {q : ℕ} [NeZero q] (params : Parameters q) (dimension : ℕ) :
    GSWOperations.gadgetMatrix (layout params dimension) = gadget params (dimension + 1) := by
  ext row column
  generalize hblock :
    (finProdFinEquiv.symm column : Fin (dimension + 1) × Fin params.levels).1 = block
  change column.divNat = block at hblock
  cases row using Fin.cases <;> cases block using Fin.cases <;>
    simp [GSWOperations.gadgetMatrix, GSWOperations.ciphertextMatrix,
      GSWSelfKey.maskShift, GSWSelfKey.bodyShift, layout, gadget, hblock,
      eq_comm]

/-- The concrete sampler inherits its sampled error bound under the original secret. -/
theorem noiseBound_fresh {q : ℕ} [NeZero q] {dimension : ℕ} (params : Parameters q)
    (secret : Fin dimension → ZMod q) (bit : Bool)
    (challenge : Matrix (Fin dimension) (Fin ((dimension + 1) * params.levels)) (ZMod q))
    (error : Fin ((dimension + 1) * params.levels) → ZMod q) (bound : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ bound) :
    NoiseBound params (GSWOperations.extendedSecret secret)
      (GSWOperations.ciphertextMatrix (GSWSelfKey.freshTranscript (layout params dimension)
        secret (fun _ ↦ bitMessage bit) challenge error)) (bitMessage bit) bound := by
  intro column
  have hfresh := GSWOperations.fresh_noise (layout params dimension) secret
    (bitMessage bit) challenge error
  rw [gadgetMatrix_layout] at hfresh
  simpa only [NoiseBound, hfresh] using herror column

/-- Any selected gadget column has the claimed secret coordinate as its exact phase. -/
theorem vecMul_gadget_column {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (secret : Fin rows → ZMod q) (row : Fin rows) (level : Fin params.levels) :
    vecMul secret (gadget params rows) (finProdFinEquiv (row, level)) =
      secret row * TFHE.Gadget.Base.gadget params level := by
  simp [vecMul, dotProduct, gadget, mul_ite]

/-- Concrete nearest-codeword decryption at a selected body-gadget level. -/
def decrypt {q : ℕ} [NeZero q] {dimension : ℕ} (params : Parameters q)
    (secret : Fin dimension → ZMod q) (ciphertext : Ciphertext params (dimension + 1))
    (level : Fin params.levels) : Bool :=
  TFHE.BootstrappingCorrectness.decodeNearest 0 (TFHE.Gadget.Base.gadget params level)
    (vecMul (GSWOperations.extendedSecret secret) ciphertext (finProdFinEquiv (0, level)))

/-- Exact nearest-codeword correctness from the concrete noise bound and public separation.
The separation is a computable condition on the actual modulus and selected gadget entry. -/
theorem decrypt_eq_bit {q : ℕ} [NeZero q] {dimension : ℕ} (params : Parameters q)
    (secret : Fin dimension → ZMod q) (ciphertext : Ciphertext params (dimension + 1))
    (bit : Bool) (bound : ℕ) (level : Fin params.levels)
    (hnoise : NoiseBound params (GSWOperations.extendedSecret secret) ciphertext
      (bitMessage bit) bound)
    (hmargin : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance
      0 (TFHE.Gadget.Base.gadget params level)) :
    decrypt params secret ciphertext level = bit := by
  let column : Fin ((dimension + 1) * params.levels) := finProdFinEquiv (0, level)
  have hphase : vecMul (GSWOperations.extendedSecret secret)
      (gadget params (dimension + 1)) column = TFHE.Gadget.Base.gadget params level := by
    rw [vecMul_gadget_column]
    simp [GSWOperations.extendedSecret]
  have hencode : (bitMessage bit : ZMod q) * TFHE.Gadget.Base.gadget params level =
      TFHE.BootstrappingCorrectness.encodeBit 0 (TFHE.Gadget.Base.gadget params level) bit := by
    cases bit <;> simp [bitMessage, TFHE.BootstrappingCorrectness.encodeBit]
  apply TFHE.BootstrappingCorrectness.decodeNearest_encodeBit_of_distance_le
    0 (TFHE.Gadget.Base.gadget params level) _ bound bit hmargin
  simpa only [TFHE.BootstrappingCorrectness.centeredDistance, GSWOperations.noise,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hphase, hencode] using hnoise column

theorem bitMessage_not {R : Type} [Ring R] (bit : Bool) :
    bitMessage (R := R) (!bit) = 1 - bitMessage bit := by
  cases bit <;> simp [bitMessage]

/-- Public NAND on rectangular GSW ciphertexts, keeping the same key. -/
def nand {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (first second : Ciphertext params rows) : Ciphertext params rows :=
  gadget params rows - multiply params first second

/-- Complementing the message negates the error exactly. -/
theorem noise_gadget_sub {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (secret : Fin rows → ZMod q) (ciphertext : Ciphertext params rows) (message : ZMod q) :
    GSWOperations.noise secret (gadget params rows) (gadget params rows - ciphertext)
      (1 - message) = -GSWOperations.noise secret (gadget params rows) ciphertext message := by
  simp only [GSWOperations.noise, vecMul_sub, sub_smul, one_smul]
  abel

/-- The concrete NAND gate has the same asymmetric bound as multiplication. -/
theorem noiseBound_nand {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (secret : Fin rows → ZMod q) (first second : Ciphertext params rows)
    (firstBit secondBit : Bool) (firstBound secondBound : ℕ)
    (hfirst : NoiseBound params secret first (bitMessage firstBit) firstBound)
    (hsecond : NoiseBound params secret second (bitMessage secondBit) secondBound) :
    NoiseBound params secret (nand params first second) (bitMessage (!(firstBit && secondBit)))
      (growth params rows * firstBound + secondBound) := by
  intro column
  simp only [nand, bitMessage_not, noise_gadget_sub, Pi.neg_apply,
    LatticeCrypto.centeredRepr_natAbs_neg]
  exact noiseBound_multiply_bits params secret first second firstBit secondBit
    firstBound secondBound hfirst hsecond column

/-- Correct NAND decryption, with the public digit and modulus constraints made explicit. -/
theorem decrypt_nand {q : ℕ} [NeZero q] {dimension : ℕ} (params : Parameters q)
    (secret : Fin dimension → ZMod q)
    (first second : Ciphertext params (dimension + 1)) (firstBit secondBit : Bool)
    (firstBound secondBound : ℕ) (level : Fin params.levels)
    (hfirst : NoiseBound params (GSWOperations.extendedSecret secret) first
      (bitMessage firstBit) firstBound)
    (hsecond : NoiseBound params (GSWOperations.extendedSecret secret) second
      (bitMessage secondBit) secondBound)
    (hmargin : 2 * (growth params (dimension + 1) * firstBound + secondBound) <
      TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decrypt params secret (nand params first second) level = !(firstBit && secondBit) :=
  decrypt_eq_bit params secret (nand params first second) _ _ level
    (noiseBound_nand params _ first second firstBit secondBit
      firstBound secondBound hfirst hsecond) hmargin

/-- Correct decryption of a right-associated bit product, with a linear error budget. -/
theorem decrypt_rightProduct {q : ℕ} [NeZero q] {dimension : ℕ} (params : Parameters q)
    (secret : Fin dimension → ZMod q)
    (inputs : List (Bool × Ciphertext params (dimension + 1)))
    (bound : ℕ) (level : Fin params.levels)
    (hinputs : ∀ entry ∈ inputs, NoiseBound params (GSWOperations.extendedSecret secret)
      entry.2 (bitMessage entry.1) bound)
    (hmargin : 2 * (inputs.length * growth params (dimension + 1) * bound) <
      TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decrypt params secret (rightProduct params inputs) level = rightMessage inputs :=
  decrypt_eq_bit params secret (rightProduct params inputs) _ _ level
    (noiseBound_rightProduct params _ inputs bound hinputs) hmargin

/-- Subtraction subtracts the exact message-relative errors. -/
theorem noise_sub {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (secret : Fin rows → ZMod q) (first second : Ciphertext params rows)
    (firstMessage secondMessage : ZMod q) :
    GSWOperations.noise secret (gadget params rows) (first - second)
      (firstMessage - secondMessage) =
      GSWOperations.noise secret (gadget params rows) first firstMessage -
        GSWOperations.noise secret (gadget params rows) second secondMessage := by
  simp only [GSWOperations.noise, vecMul_sub, sub_smul]
  abel

/-- Public encrypted selection, consuming a bit ciphertext as the left multiplier. -/
def cmux {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (control first second : Ciphertext params rows) : Ciphertext params rows :=
  second + multiply params control (first - second)

/-- The selected branch keeps its own error; only the control error is multiplied by digits. -/
theorem noise_cmux {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (secret : Fin rows → ZMod q) (control first second : Ciphertext params rows)
    (controlBit : Bool) (firstMessage secondMessage : ZMod q) :
    GSWOperations.noise secret (gadget params rows) (cmux params control first second)
        (if controlBit then firstMessage else secondMessage) =
      vecMul (GSWOperations.noise secret (gadget params rows) control (bitMessage controlBit))
        (digitMatrix params (first - second)) +
      if controlBit then GSWOperations.noise secret (gadget params rows) first firstMessage
      else GSWOperations.noise secret (gadget params rows) second secondMessage := by
  cases controlBit with
  | false =>
    have hmessage : secondMessage = secondMessage + 0 * (firstMessage - secondMessage) := by simp
    rw [if_neg Bool.false_ne_true, cmux, hmessage, GSWOperations.noise_add, noise_multiply]
    simp [bitMessage, add_comm]
  | true =>
    have hmessage : firstMessage = secondMessage + 1 * (firstMessage - secondMessage) := by ring
    rw [if_pos rfl, cmux, hmessage, GSWOperations.noise_add, noise_multiply, noise_sub]
    simp [bitMessage]
    abel

/-- Both branches may already be noisy. The output costs one fresh-control digit product
plus the common branch bound, rather than amplifying the branch bound by the gadget size. -/
theorem noiseBound_cmux {q : ℕ} [NeZero q] {rows : ℕ} (params : Parameters q)
    (secret : Fin rows → ZMod q) (control first second : Ciphertext params rows)
    (controlBit : Bool) (firstMessage secondMessage : ZMod q) (controlBound branchBound : ℕ)
    (hcontrol : NoiseBound params secret control (bitMessage controlBit) controlBound)
    (hfirst : NoiseBound params secret first firstMessage branchBound)
    (hsecond : NoiseBound params secret second secondMessage branchBound) :
    NoiseBound params secret (cmux params control first second)
      (if controlBit then firstMessage else secondMessage)
      (growth params rows * controlBound + branchBound) := by
  intro column
  rw [noise_cmux]
  apply (TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _).trans
  apply Nat.add_le_add
  · exact vecMul_error_bound params _ (first - second) controlBound hcontrol column
  · cases controlBit with
    | false => exact hsecond column
    | true => exact hfirst column

end FormalProof4FHE.LWE.GSWGadget
