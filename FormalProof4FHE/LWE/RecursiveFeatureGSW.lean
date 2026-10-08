/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveMultiplication
import FormalProof4FHE.LWE.GSWGadget

/-!
# GSW evaluation over recursive decryption features

A recursive ciphertext pairs its public coefficients with gamma(s)=(1,s_i,s_i*s_j).
The coefficient representation is bijective. Keeping a GSW matrix of such columns
allows the existing gadget product to stay in the same quadratic decryption format,
without a separate quartic relinearization table or a newly sampled key.

This proves a public algebraic evaluation interface and its exact noise identity.
The companion RecursiveFeaturePublicKey modules establish its full-coordinate public
encryption and fresh-encryption parameters; reusable same-key refresh controls remain unproved.
Nearest-codeword decoding and NAND correctness take explicit input-noise and margin bounds. The
native scalar-key GSW public-key law must not be silently substituted for this one.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.RecursiveFeatureGSW

open RecursiveMultiplication

def rows (n : ℕ) : ℕ := n * n + n + 1

def featureEquiv (n : ℕ) : Feature n ≃ Fin (rows n) :=
  ((Equiv.optionCongr
    ((Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv)).trans
      (finSuccEquiv (n + n * n)).symm).trans (finCongr (by unfold rows; omega))

/-- A representation of the same underlying secret, with no new key sampling. -/
def featureSecret {R : Type} [CommRing R] {n : ℕ} (secret : Fin n → R) : Fin (rows n) → R :=
  fun index ↦ feature secret ((featureEquiv n).symm index)

def flatten {R : Type} [CommRing R] {n : ℕ} (ciphertext : Ciphertext R n) : Fin (rows n) → R :=
  fun index ↦ coefficient ciphertext ((featureEquiv n).symm index)

def unflatten {R : Type} [CommRing R] {n : ℕ} (vector : Fin (rows n) → R) : Ciphertext R n :=
  (fun row column ↦ -vector (featureEquiv n (some (.inr (row, column)))),
    (fun row ↦ vector (featureEquiv n (some (.inl row)))), vector (featureEquiv n none))

theorem coefficient_unflatten {R : Type} [CommRing R] {n : ℕ}
    (vector : Fin (rows n) → R) (index : Feature n) :
    coefficient (unflatten vector) index = vector (featureEquiv n index) := by
  cases index with
  | none => rfl
  | some index => cases index <;> simp [coefficient, unflatten]

theorem flatten_unflatten {R : Type} [CommRing R] {n : ℕ} (vector : Fin (rows n) → R) :
    flatten (unflatten vector) = vector := by
  funext index
  simp only [flatten, coefficient_unflatten, Equiv.apply_symm_apply]

theorem unflatten_flatten {R : Type} [CommRing R] {n : ℕ} (ciphertext : Ciphertext R n) :
    unflatten (flatten ciphertext) = ciphertext := by
  apply Prod.ext
  · funext row column
    simp [unflatten, flatten, coefficient]
  · apply Prod.ext
    · funext row
      simp [unflatten, flatten, coefficient]
    · simp [unflatten, flatten, coefficient]

theorem decrypt_eq_dotProduct {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (ciphertext : Ciphertext R n) :
    RecursiveQuadratic.decrypt secret ciphertext = dotProduct (featureSecret secret) (flatten ciphertext) := by
  rw [phase_eq_pairing]
  unfold dotProduct
  apply Fintype.sum_equiv (featureEquiv n)
  intro index
  simp only [featureSecret, flatten, Equiv.symm_apply_apply]
  ring

abbrev Batch {q : ℕ} (params : Parameters q) (n : ℕ) :=
  Fin (rows n * params.levels) → Ciphertext (ZMod q) n

def matrix {q n : ℕ} (params : Parameters q) (ciphertexts : Batch params n) :
    GSWGadget.Ciphertext params (rows n) := fun row column ↦ flatten (ciphertexts column) row

def ofMatrix {q n : ℕ} (params : Parameters q)
    (ciphertexts : GSWGadget.Ciphertext params (rows n)) : Batch params n :=
  fun column ↦ unflatten (fun row ↦ ciphertexts row column)

theorem matrix_ofMatrix {q n : ℕ} (params : Parameters q)
    (ciphertexts : GSWGadget.Ciphertext params (rows n)) : matrix params (ofMatrix params ciphertexts) = ciphertexts := by
  ext row column
  exact congrFun (flatten_unflatten (fun row ↦ ciphertexts row column)) row

theorem ofMatrix_matrix {q n : ℕ} (params : Parameters q) (ciphertexts : Batch params n) :
    ofMatrix params (matrix params ciphertexts) = ciphertexts := by
  funext column
  exact unflatten_flatten (ciphertexts column)

def phase {q n : ℕ} (params : Parameters q) (secret : Fin n → ZMod q)
    (ciphertexts : Batch params n) : Fin (rows n * params.levels) → ZMod q :=
  fun column ↦ RecursiveQuadratic.decrypt secret (ciphertexts column)

theorem phase_eq_vecMul {q n : ℕ} (params : Parameters q) (secret : Fin n → ZMod q)
    (ciphertexts : Batch params n) :
    phase params secret ciphertexts = vecMul (featureSecret secret) (matrix params ciphertexts) := by
  funext column
  exact decrypt_eq_dotProduct secret (ciphertexts column)

/-- The fixed public GSW gadget in recursive coefficient coordinates. -/
def gadgetBatch {q n : ℕ} [NeZero q] (params : Parameters q) : Batch params n :=
  ofMatrix params (GSWGadget.gadget params (rows n))

def noise {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (ciphertexts : Batch params n) (message : ZMod q) : Fin (rows n * params.levels) → ZMod q :=
  phase params secret ciphertexts - message • phase params secret (gadgetBatch params)

theorem noise_eq_gswNoise {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (ciphertexts : Batch params n) (message : ZMod q) :
    noise params secret ciphertexts message = GSWOperations.noise (featureSecret secret)
      (GSWGadget.gadget params (rows n)) (matrix params ciphertexts) message := by
  simp only [noise, phase_eq_vecMul, gadgetBatch, matrix_ofMatrix, GSWOperations.noise]

/-- Public same-format multiplication, using only gadget decomposition and input ciphertexts. -/
def multiply {q n : ℕ} [NeZero q] (params : Parameters q) (first second : Batch params n) : Batch params n :=
  ofMatrix params (GSWGadget.multiply params (matrix params first) (matrix params second))

theorem matrix_multiply {q n : ℕ} [NeZero q] (params : Parameters q) (first second : Batch params n) :
    matrix params (multiply params first second) =
      GSWGadget.multiply params (matrix params first) (matrix params second) :=
  matrix_ofMatrix _ _

/-- The checked GSW product identity now applies under the original single secret. -/
theorem noise_multiply {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (first second : Batch params n) (firstMessage secondMessage : ZMod q) :
    noise params secret (multiply params first second) (firstMessage * secondMessage) =
      vecMul (noise params secret first firstMessage) (GSWGadget.digitMatrix params (matrix params second)) +
      firstMessage • noise params secret second secondMessage := by
  simp only [noise_eq_gswNoise, matrix_multiply]
  exact GSWGadget.noise_multiply params (featureSecret secret)
    (matrix params first) (matrix params second) firstMessage secondMessage

def NoiseBound {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (ciphertexts : Batch params n) (message : ZMod q) (bound : ℕ) : Prop :=
  ∀ column, (LatticeCrypto.centeredRepr (noise params secret ciphertexts message column)).natAbs ≤ bound

theorem noiseBound_iff_gsw {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (ciphertexts : Batch params n) (message : ZMod q) (bound : ℕ) :
    NoiseBound params secret ciphertexts message bound ↔
      GSWGadget.NoiseBound params (featureSecret secret) (matrix params ciphertexts) message bound := by
  simp only [NoiseBound, GSWGadget.NoiseBound, noise_eq_gswNoise]

/-- Short digits preserve the GSW asymmetric bit-product bound under the original key. -/
theorem noiseBound_multiply_bits {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (first second : Batch params n) (firstBit secondBit : Bool) (firstBound secondBound : ℕ)
    (hfirst : NoiseBound params secret first (GSWGadget.bitMessage firstBit) firstBound)
    (hsecond : NoiseBound params secret second (GSWGadget.bitMessage secondBit) secondBound) :
    NoiseBound params secret (multiply params first second) (GSWGadget.bitMessage (firstBit && secondBit))
      (GSWGadget.growth params (rows n) * firstBound + secondBound) := by
  rw [noiseBound_iff_gsw, matrix_multiply]
  exact GSWGadget.noiseBound_multiply_bits params (featureSecret secret)
    (matrix params first) (matrix params second) firstBit secondBit firstBound secondBound
    ((noiseBound_iff_gsw _ _ _ _ _).mp hfirst) ((noiseBound_iff_gsw _ _ _ _ _).mp hsecond)

/-- One column of the fixed gadget encodes a known multiple of a decryption feature. -/
theorem gadgetBatch_phase {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (index : Feature n) (level : Fin params.levels) :
    phase params secret (gadgetBatch params)
      (finProdFinEquiv (featureEquiv n index, level)) =
        TFHE.Gadget.Base.gadget params level * feature secret index := by
  rw [phase_eq_vecMul]
  simp [gadgetBatch, matrix_ofMatrix, vecMul, dotProduct, GSWGadget.gadget, featureSecret, mul_comm]

/-- Decode at the constant feature's selected gadget column using the original secret. -/
def decode {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (ciphertexts : Batch params n) (level : Fin params.levels) : Bool :=
  TFHE.BootstrappingCorrectness.decodeNearest 0 (TFHE.Gadget.Base.gadget params level)
    (phase params secret ciphertexts (finProdFinEquiv (featureEquiv n none, level)))

theorem decode_eq_bit {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (ciphertexts : Batch params n) (bit : Bool) (bound : ℕ) (level : Fin params.levels)
    (hnoise : NoiseBound params secret ciphertexts (GSWGadget.bitMessage bit) bound)
    (hmargin : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance
      0 (TFHE.Gadget.Base.gadget params level)) : decode params secret ciphertexts level = bit := by
  let column : Fin (rows n * params.levels) := finProdFinEquiv (featureEquiv n none, level)
  have hphase : phase params secret (gadgetBatch params) column = TFHE.Gadget.Base.gadget params level := by
    simpa only [feature, mul_one] using gadgetBatch_phase params secret none level
  have hencode : (GSWGadget.bitMessage bit : ZMod q) * TFHE.Gadget.Base.gadget params level =
      TFHE.BootstrappingCorrectness.encodeBit 0 (TFHE.Gadget.Base.gadget params level) bit := by
    cases bit <;> simp [GSWGadget.bitMessage, TFHE.BootstrappingCorrectness.encodeBit]
  apply TFHE.BootstrappingCorrectness.decodeNearest_encodeBit_of_distance_le
    0 (TFHE.Gadget.Base.gadget params level) _ bound bit hmargin
  simpa only [TFHE.BootstrappingCorrectness.centeredDistance, noise, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, hphase, hencode] using hnoise column

def nand {q n : ℕ} [NeZero q] (params : Parameters q) (first second : Batch params n) : Batch params n :=
  ofMatrix params (GSWGadget.nand params (matrix params first) (matrix params second))

theorem matrix_nand {q n : ℕ} [NeZero q] (params : Parameters q) (first second : Batch params n) :
    matrix params (nand params first second) =
      GSWGadget.nand params (matrix params first) (matrix params second) := matrix_ofMatrix _ _

theorem noiseBound_nand {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (first second : Batch params n) (firstBit secondBit : Bool) (firstBound secondBound : ℕ)
    (hfirst : NoiseBound params secret first (GSWGadget.bitMessage firstBit) firstBound)
    (hsecond : NoiseBound params secret second (GSWGadget.bitMessage secondBit) secondBound) :
    NoiseBound params secret (nand params first second) (GSWGadget.bitMessage (!(firstBit && secondBit)))
      (GSWGadget.growth params (rows n) * firstBound + secondBound) := by
  rw [noiseBound_iff_gsw, matrix_nand]
  exact GSWGadget.noiseBound_nand params (featureSecret secret)
    (matrix params first) (matrix params second) firstBit secondBit firstBound secondBound
    ((noiseBound_iff_gsw _ _ _ _ _).mp hfirst) ((noiseBound_iff_gsw _ _ _ _ _).mp hsecond)

theorem decode_nand {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (first second : Batch params n) (firstBit secondBit : Bool) (firstBound secondBound : ℕ)
    (level : Fin params.levels)
    (hfirst : NoiseBound params secret first (GSWGadget.bitMessage firstBit) firstBound)
    (hsecond : NoiseBound params secret second (GSWGadget.bitMessage secondBit) secondBound)
    (hmargin : 2 * (GSWGadget.growth params (rows n) * firstBound + secondBound) <
      TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decode params secret (nand params first second) level = !(firstBit && secondBit) :=
  decode_eq_bit params secret _ _ _ level
    (noiseBound_nand params secret first second firstBit secondBit firstBound secondBound hfirst hsecond) hmargin

theorem flatten_linear_quadratic_zero {q n : ℕ} (ciphertext : Regev.Ciphertext q n)
    (first second : Fin n) :
    flatten (RecursivePublicKey.embedLinear ciphertext)
      (featureEquiv n (some (.inr (first, second)))) = 0 := by
  simp [flatten, coefficient, RecursivePublicKey.embedLinear]

def linearMaskMatrix {q n : ℕ} (params : Parameters q)
    (raw : Fin (rows n * params.levels) → Regev.Ciphertext q n) :
    GSWGadget.Ciphertext params (rows n) :=
  fun row column ↦ flatten (RecursivePublicKey.embedLinear (raw column)) row

/-- Directly using the previous linear public mask leaks a bit in a quadratic gadget entry.
A full quadratic zero-ciphertext mask sampler is needed for public GSW encryption. -/
theorem linear_mask_exposes_bit {q n : ℕ} [NeZero q] (params : Parameters q)
    (hlevels : 0 < params.levels)
    (raw : Fin (rows n * params.levels) → Regev.Ciphertext q n)
    (first second : Fin n) (bit : Bool) :
    (linearMaskMatrix params raw +
      (GSWGadget.bitMessage bit : ZMod q) • GSWGadget.gadget params (rows n))
        (featureEquiv n (some (.inr (first, second))))
        (finProdFinEquiv (featureEquiv n (some (.inr (first, second))), ⟨0, hlevels⟩)) =
          GSWGadget.bitMessage bit := by
  simp [linearMaskMatrix, flatten, coefficient, RecursivePublicKey.embedLinear, GSWGadget.gadget,
    TFHE.Gadget.Base.gadget]

def linearMaskGuess {q n : ℕ} [NeZero q] (params : Parameters q)
    (hlevels : 0 < params.levels) (ciphertext : GSWGadget.Ciphertext params (rows n))
    (first second : Fin n) : Bool :=
  decide (ciphertext (featureEquiv n (some (.inr (first, second))))
    (finProdFinEquiv (featureEquiv n (some (.inr (first, second))), ⟨0, hlevels⟩)) = 1)

/-- The public-coordinate observer recovers the bit for every choice of the linear encryption coins. -/
theorem linearMaskGuess_eq_bit {q n : ℕ} [NeZero q] [Nontrivial (ZMod q)] (params : Parameters q)
    (hlevels : 0 < params.levels)
    (raw : Fin (rows n * params.levels) → Regev.Ciphertext q n)
    (first second : Fin n) (bit : Bool) :
    linearMaskGuess params hlevels
      (linearMaskMatrix params raw +
        (GSWGadget.bitMessage bit : ZMod q) • GSWGadget.gadget params (rows n)) first second = bit := by
  unfold linearMaskGuess
  rw [linear_mask_exposes_bit]
  cases bit <;> simp [GSWGadget.bitMessage]

/-- Refresh controls for original secret bits must carry bit times gadget-feature phases. -/
def controlMessage {q n : ℕ} [NeZero q] (params : Parameters q) (secret : Fin n → ZMod q)
    (bitIndex : Fin n) (index : Feature n) (level : Fin params.levels) : ZMod q :=
  secret bitIndex * phase params secret (gadgetBatch params)
    (finProdFinEquiv (featureEquiv n index, level))

theorem controlMessage_quadratic {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (bitIndex first second : Fin n) (level : Fin params.levels) :
    controlMessage params secret bitIndex (some (.inr (first, second))) level =
      TFHE.Gadget.Base.gadget params level * secret bitIndex * secret first * secret second := by
  rw [controlMessage, gadgetBatch_phase]
  simp only [feature]
  ring

def corner3 {R : Type} [CommRing R] (a b c : Bool) : Fin 3 → R :=
  ![if a then 1 else 0, if b then 1 else 0, if c then 1 else 0]

def difference3 {R : Type} [CommRing R] (function : (Fin 3 → R) → R) : R :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
    (if a then 1 else -1) * (if b then 1 else -1) * (if c then 1 else -1) * function (corner3 a b c)

set_option maxHeartbeats 800000 in
theorem difference3_quadratic {R : Type} [CommRing R]
    (polynomial : RecursiveQuadratic.Polynomial R 3 1) :
    difference3 (fun secret ↦ RecursiveQuadratic.message polynomial secret 0) = 0 := by
  simp [difference3, corner3, RecursiveQuadratic.message, vecMul, dotProduct, Fin.sum_univ_succ]
  ring

theorem difference3_cubic {R : Type} [CommRing R] :
    difference3 (fun secret : Fin 3 → R ↦ secret 0 * secret 1 * secret 2) = 1 := by
  simp [difference3, corner3]

theorem cubic_not_quadratic_on_corners {R : Type} [CommRing R] [Nontrivial R] :
    ¬ ∃ polynomial : RecursiveQuadratic.Polynomial R 3 1,
      ∀ a b c : Bool, RecursiveQuadratic.message polynomial (corner3 a b c) 0 =
        (corner3 a b c : Fin 3 → R) 0 * (corner3 a b c) 1 * (corner3 a b c) 2 := by
  rintro ⟨polynomial, hpoly⟩
  have hzero := difference3_quadratic polynomial
  unfold difference3 at hzero
  simp_rw [hpoly] at hzero
  change difference3 (fun secret : Fin 3 → R ↦ secret 0 * secret 1 * secret 2) = 0 at hzero
  rw [difference3_cubic] at hzero
  exact one_ne_zero hzero

/-- Even the original-bit control route needs a genuinely cubic message beyond the existing proof. -/
theorem required_control_not_quadratic {q : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    (params : Parameters q) (hlevels : 0 < params.levels) :
    ¬ ∃ polynomial : RecursiveQuadratic.Polynomial (ZMod q) 3 1,
      ∀ a b c : Bool, RecursiveQuadratic.message polynomial (corner3 a b c) 0 =
        controlMessage params (corner3 a b c) 0 (some (.inr (1, 2))) ⟨0, hlevels⟩ := by
  simpa only [controlMessage_quadratic, TFHE.Gadget.Base.gadget, pow_zero, Nat.cast_one, one_mul] using
    (cubic_not_quadratic_on_corners (R := ZMod q))

end FormalProof4FHE.LWE.RecursiveFeatureGSW
