/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursivePublicKey
import FormalProof4FHE.TFHE.GadgetDecomposition

/-!
# Same-format recursive multiplication and its exact hint obligation

The public algorithm relinearizes products into the recursive quadratic format.
Its hint table encrypts gadget multiples of products of two decryption features,
which have degree at most four in the same secret. Correctness and digit/error
bounds are proved from actual private hint generation. Security of publishing
this table together with the public key is NOT established by the existing
fixed quadratic-message reduction. No quartic KDM assumption is introduced.
The half-modulus public bit encoding also needs a separate scaling/rounding
interface; raw phase multiplication alone is not a Boolean NAND or a refresh.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.RecursiveMultiplication

abbrev Feature (n : ℕ) := Option (Fin n ⊕ (Fin n × Fin n))
abbrev Ciphertext (R : Type) (n : ℕ) := RecursiveQuadratic.Ciphertext R n
abbrev Parameters := TFHE.Gadget.Base.Parameters
abbrev HintIndex (n levels : ℕ) := Feature n × Feature n × Fin levels
abbrev HintTable (R : Type) (n levels : ℕ) := HintIndex n levels → Ciphertext R n

def feature {R : Type} [CommRing R] {n : ℕ} (secret : Fin n → R) : Feature n → R
  | none => 1
  | some (.inl row) => secret row
  | some (.inr pair) => secret pair.1 * secret pair.2

def coefficient {R : Type} [CommRing R] {n : ℕ} (ciphertext : Ciphertext R n) : Feature n → R
  | none => ciphertext.2.2
  | some (.inl row) => ciphertext.2.1 row
  | some (.inr pair) => -ciphertext.1 pair.1 pair.2

theorem feature_count (n : ℕ) : Fintype.card (Feature n) = n * n + n + 1 := by
  simp [Feature]
  omega

theorem hint_count (n levels : ℕ) :
    Fintype.card (HintIndex n levels) = (n * n + n + 1) ^ 2 * levels := by
  simp only [HintIndex, Fintype.card_prod, feature_count, Fintype.card_fin]
  ring

/-- The coefficient pairing is the existing recursive decryption phase. -/
theorem phase_eq_pairing {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (ciphertext : Ciphertext R n) :
    RecursiveQuadratic.decrypt secret ciphertext =
      ∑ index : Feature n, coefficient ciphertext index * feature secret index := by
  simp only [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type,
    coefficient, feature, mul_one, neg_mul, Finset.sum_neg_distrib]
  unfold RecursiveQuadratic.decrypt vecMul dotProduct
  simp only [Finset.sum_mul]
  have hquad : (∑ column : Fin n, ∑ row : Fin n,
      secret row * ciphertext.1 row column * secret column) =
      ∑ row : Fin n, ∑ column : Fin n,
        ciphertext.1 row column * (secret row * secret column) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro column _
    ring
  rw [hquad]
  ring

theorem decrypt_add {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (first second : Ciphertext R n) :
    RecursiveQuadratic.decrypt secret (first + second) =
      RecursiveQuadratic.decrypt secret first + RecursiveQuadratic.decrypt secret second := by
  change (first.2.2 + second.2.2) + dotProduct (first.2.1 + second.2.1) secret -
      dotProduct (vecMul secret (first.1 + second.1)) secret = _
  rw [add_dotProduct, vecMul_add, add_dotProduct]
  unfold RecursiveQuadratic.decrypt
  abel

theorem decrypt_zero {R : Type} [CommRing R] {n : ℕ} (secret : Fin n → R) :
    RecursiveQuadratic.decrypt secret (0 : Ciphertext R n) = 0 := by
  simp [RecursiveQuadratic.decrypt]

theorem decrypt_smul {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (scalar : R) (ciphertext : Ciphertext R n) :
    RecursiveQuadratic.decrypt secret (scalar • ciphertext) =
      scalar * RecursiveQuadratic.decrypt secret ciphertext := by
  change scalar * ciphertext.2.2 + dotProduct (scalar • ciphertext.2.1) secret -
      dotProduct (vecMul secret (scalar • ciphertext.1)) secret = _
  rw [smul_dotProduct, vecMul_smul, smul_dotProduct]
  simp only [smul_eq_mul, RecursiveQuadratic.decrypt]
  ring

theorem decrypt_sum {R : Type} [CommRing R] {n : ℕ} {Index : Type} [DecidableEq Index]
    (secret : Fin n → R) (indices : Finset Index) (ciphertexts : Index → Ciphertext R n) :
    RecursiveQuadratic.decrypt secret (∑ index ∈ indices, ciphertexts index) =
      ∑ index ∈ indices, RecursiveQuadratic.decrypt secret (ciphertexts index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, decrypt_zero]
  | @insert index indices hindex ih =>
    rw [Finset.sum_insert hindex, decrypt_add, ih, Finset.sum_insert hindex]

/-- Public multiplication inputs contain no secret key. -/
def multiply {q n : ℕ} [NeZero q] (params : Parameters q)
    (hints : HintTable (ZMod q) n params.levels) (first second : Ciphertext (ZMod q) n) :
    Ciphertext (ZMod q) n :=
  ∑ left : Feature n, ∑ right : Feature n, ∑ level : Fin params.levels,
    TFHE.Gadget.Base.digit params (coefficient first left * coefficient second right) level •
      hints (left, right, level)

def hintMessage {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (index : HintIndex n params.levels) : ZMod q :=
  TFHE.Gadget.Base.gadget params index.2.2 * feature secret index.1 * feature secret index.2.1

def hintError {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (hints : HintTable (ZMod q) n params.levels)
    (index : HintIndex n params.levels) : ZMod q :=
  RecursiveQuadratic.decrypt secret (hints index) - hintMessage params secret index

def relinearizationError {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (hints : HintTable (ZMod q) n params.levels)
    (first second : Ciphertext (ZMod q) n) : ZMod q :=
  ∑ left : Feature n, ∑ right : Feature n, ∑ level : Fin params.levels,
    TFHE.Gadget.Base.digit params (coefficient first left * coefficient second right) level *
      hintError params secret hints (left, right, level)

theorem decomposed_hintMessage {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (value : ZMod q) (left right : Feature n) :
    (∑ level : Fin params.levels, TFHE.Gadget.Base.digit params value level *
      hintMessage params secret (left, right, level)) =
        value * feature secret left * feature secret right := by
  unfold hintMessage
  simp only [← mul_assoc, ← Finset.sum_mul]
  have h := TFHE.Gadget.Base.recompose params value
  unfold TFHE.Gadget.recompose at h
  rw [h]

/-- Exact same-key phase product plus the error of the actual hint table. -/
theorem decrypt_multiply {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (hints : HintTable (ZMod q) n params.levels)
    (first second : Ciphertext (ZMod q) n) :
    RecursiveQuadratic.decrypt secret (multiply params hints first second) =
      RecursiveQuadratic.decrypt secret first * RecursiveQuadratic.decrypt secret second +
        relinearizationError params secret hints first second := by
  unfold multiply
  simp only [decrypt_sum, decrypt_smul]
  have hsplit : ∀ index : HintIndex n params.levels,
      RecursiveQuadratic.decrypt secret (hints index) =
        hintMessage params secret index + hintError params secret hints index := by
    intro index
    unfold hintError
    abel
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib]
  simp only [decomposed_hintMessage]
  rw [phase_eq_pairing, phase_eq_pairing]
  unfold relinearizationError
  rw [Finset.sum_mul]
  apply congrArg (fun value ↦ value + _)
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  ring

/-- One fresh recursive encryption, allowing an arbitrary privately supplied message. -/
def freshCiphertext {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (message : R) (mask : Matrix (Fin n) (Fin n) R)
    (innerMask errors : Fin n → R) (bodyError : R) : Ciphertext R n :=
  (mask, vecMul secret mask - innerMask + errors, dotProduct innerMask secret + message + bodyError)

theorem decrypt_freshCiphertext {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (message : R) (mask : Matrix (Fin n) (Fin n) R)
    (innerMask errors : Fin n → R) (bodyError : R) :
    RecursiveQuadratic.decrypt secret (freshCiphertext secret message mask innerMask errors bodyError) =
      message + bodyError + dotProduct errors secret := by
  simp only [RecursiveQuadratic.decrypt, freshCiphertext, add_dotProduct, sub_dotProduct]
  ring

def freshHints {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q)
    (masks : HintIndex n params.levels → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : HintIndex n params.levels → Fin n → ZMod q)
    (bodyErrors : HintIndex n params.levels → ZMod q) : HintTable (ZMod q) n params.levels :=
  fun index ↦ freshCiphertext secret (hintMessage params secret index)
    (masks index) (innerMasks index) (errors index) (bodyErrors index)

theorem hintError_freshHints {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q)
    (masks : HintIndex n params.levels → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : HintIndex n params.levels → Fin n → ZMod q)
    (bodyErrors : HintIndex n params.levels → ZMod q) (index : HintIndex n params.levels) :
    hintError params secret (freshHints params secret masks innerMasks errors bodyErrors) index =
      bodyErrors index + dotProduct (errors index) secret := by
  rw [hintError, freshHints, decrypt_freshCiphertext]
  ring

/-- In particular the quadratic/quadratic table entries contain genuine quartic monomials. -/
theorem hintMessage_quadratic_pair {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (first second third fourth : Fin n) (level : Fin params.levels) :
    hintMessage params secret
      (some (.inr (first, second)), some (.inr (third, fourth)), level) =
      TFHE.Gadget.Base.gadget params level * secret first * secret second * secret third * secret fourth := by
  simp only [hintMessage, feature]
  ring

theorem digit_centered_bound {q : ℕ} [NeZero q] (params : Parameters q)
    (value : ZMod q) (level : Fin params.levels) :
    (LatticeCrypto.centeredRepr (TFHE.Gadget.Base.digit params value level)).natAbs ≤
      params.base - 1 := by
  exact (TFHE.NoiseBounds.centeredRepr_natCast_natAbs_le
    (TFHE.Gadget.Base.natDigit params value level)).trans
    (by have := TFHE.Gadget.Base.natDigit_lt_base params value level; omega)

theorem centered_sum_bound {q : ℕ} [NeZero q] {Index : Type} [Fintype Index] [DecidableEq Index]
    (values : Index → ZMod q) (bound : ℕ)
    (hbound : ∀ index, (LatticeCrypto.centeredRepr (values index)).natAbs ≤ bound) :
    (LatticeCrypto.centeredRepr (∑ index, values index)).natAbs ≤ Fintype.card Index * bound := by
  exact (TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _).trans (by
    calc
      _ ≤ ∑ _index : Index, bound := Finset.sum_le_sum (fun index _ ↦ hbound index)
      _ = _ := by simp)

theorem relinearizationError_bound {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (hints : HintTable (ZMod q) n params.levels)
    (first second : Ciphertext (ZMod q) n) (bound : ℕ)
    (hhints : ∀ index, (LatticeCrypto.centeredRepr (hintError params secret hints index)).natAbs ≤ bound) :
    (LatticeCrypto.centeredRepr (relinearizationError params secret hints first second)).natAbs ≤
      (n * n + n + 1) ^ 2 * params.levels * (params.base - 1) * bound := by
  have hterm : ∀ left right level, (LatticeCrypto.centeredRepr
      (TFHE.Gadget.Base.digit params (coefficient first left * coefficient second right) level *
        hintError params secret hints (left, right, level))).natAbs ≤ (params.base - 1) * bound := by
    intro left right level
    exact (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
      (Nat.mul_le_mul (digit_centered_bound _ _ _) (hhints _))
  have hlevels := fun left right ↦ centered_sum_bound
    (fun level ↦ TFHE.Gadget.Base.digit params (coefficient first left * coefficient second right) level *
      hintError params secret hints (left, right, level)) ((params.base - 1) * bound) (hterm left right)
  have hright := fun left ↦ centered_sum_bound
    (fun right ↦ ∑ level, TFHE.Gadget.Base.digit params (coefficient first left * coefficient second right) level *
      hintError params secret hints (left, right, level))
    (params.levels * ((params.base - 1) * bound)) (by simpa only [Fintype.card_fin] using hlevels left)
  have hleft := centered_sum_bound
    (fun left ↦ ∑ right, ∑ level,
      TFHE.Gadget.Base.digit params (coefficient first left * coefficient second right) level *
        hintError params secret hints (left, right, level))
    (Fintype.card (Feature n) * (params.levels * ((params.base - 1) * bound))) hright
  unfold relinearizationError
  calc
    _ ≤ _ := hleft
    _ = _ := by rw [feature_count]; ring

theorem hintError_freshHints_bound {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q)
    (masks : HintIndex n params.levels → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : HintIndex n params.levels → Fin n → ZMod q)
    (bodyErrors : HintIndex n params.levels → ZMod q) (bound : ℕ)
    (hsecret : ∀ row, secret row = 0 ∨ secret row = 1)
    (herrors : ∀ index row, (LatticeCrypto.centeredRepr (errors index row)).natAbs ≤ bound)
    (hbody : ∀ index, (LatticeCrypto.centeredRepr (bodyErrors index)).natAbs ≤ bound)
    (index : HintIndex n params.levels) :
    (LatticeCrypto.centeredRepr
      (hintError params secret (freshHints params secret masks innerMasks errors bodyErrors) index)).natAbs ≤
        (n + 1) * bound := by
  rw [hintError_freshHints]
  have hterm : ∀ row, (LatticeCrypto.centeredRepr (errors index row * secret row)).natAbs ≤ bound := by
    intro row
    rcases hsecret row with hz | ho
    · rw [hz, mul_zero]
      simp [LatticeCrypto.centeredRepr_eq_valMinAbs]
    · rw [ho, mul_one]
      exact herrors index row
  have hsum := centered_sum_bound (fun row ↦ errors index row * secret row) bound hterm
  calc
    _ ≤ (LatticeCrypto.centeredRepr (bodyErrors index)).natAbs +
        (LatticeCrypto.centeredRepr (dotProduct (errors index) secret)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _
    _ ≤ bound + n * bound := Nat.add_le_add (hbody _) (by simpa only [dotProduct, Fintype.card_fin] using hsum)
    _ = _ := by ring

def phaseError {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (ciphertext : Ciphertext R n) (message : R) : R :=
  RecursiveQuadratic.decrypt secret ciphertext - message

theorem phaseError_multiply {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (hints : HintTable (ZMod q) n params.levels)
    (first second : Ciphertext (ZMod q) n) (firstMessage secondMessage : ZMod q) :
    phaseError secret (multiply params hints first second) (firstMessage * secondMessage) =
      firstMessage * phaseError secret second secondMessage +
      secondMessage * phaseError secret first firstMessage +
      phaseError secret first firstMessage * phaseError secret second secondMessage +
      relinearizationError params secret hints first second := by
  unfold phaseError
  rw [decrypt_multiply]
  ring

/-- A public first product of linear phases needs no relinearization table. -/
def linearProduct {R : Type} [CommRing R] {n : ℕ}
    (first second : (Fin n → R) × R) : Ciphertext R n :=
  (fun row column ↦ -(first.1 row * second.1 column),
    second.2 • first.1 + first.2 • second.1, first.2 * second.2)

theorem quadratic_outer_product {R : Type} [CommRing R] {n : ℕ}
    (secret first second : Fin n → R) :
    dotProduct (vecMul secret (fun row column ↦ first row * second column)) secret =
      dotProduct first secret * dotProduct second secret := by
  calc
    _ = ∑ column : Fin n, ∑ row : Fin n,
        (first row * secret row) * (second column * secret column) := by
      simp only [dotProduct, vecMul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro column _
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ = ∑ row : Fin n, ∑ column : Fin n,
        (first row * secret row) * (second column * secret column) := Finset.sum_comm
    _ = _ := by simp only [dotProduct, Fintype.sum_mul_sum]

theorem decrypt_linearProduct {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (first second : (Fin n → R) × R) :
    RecursiveQuadratic.decrypt secret (linearProduct first second) =
      (first.2 + dotProduct first.1 secret) * (second.2 + dotProduct second.1 secret) := by
  have hneg : dotProduct
      (vecMul secret (fun row column ↦ -(first.1 row * second.1 column))) secret =
        -(dotProduct first.1 secret * dotProduct second.1 secret) := by
    simpa only [vecMul, dotProduct, mul_neg, neg_mul, Finset.sum_neg_distrib] using
      congrArg Neg.neg (quadratic_outer_product secret first.1 second.1)
  change first.2 * second.2 + dotProduct (second.2 • first.1 + first.2 • second.1) secret -
      dotProduct (vecMul secret (fun row column ↦ -(first.1 row * second.1 column))) secret = _
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hneg]
  simp only [smul_eq_mul]
  ring

/-- Four Boolean cube differences distinguish a quartic monomial from every quadratic. -/
def corner {R : Type} [CommRing R] (a b c d : Bool) : Fin 4 → R :=
  ![if a then 1 else 0, if b then 1 else 0, if c then 1 else 0, if d then 1 else 0]

def difference4 {R : Type} [CommRing R] (function : (Fin 4 → R) → R) : R :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
    (if a then 1 else -1) * (if b then 1 else -1) *
    (if c then 1 else -1) * (if d then 1 else -1) * function (corner a b c d)

set_option maxHeartbeats 800000 in
theorem difference4_quadratic {R : Type} [CommRing R]
    (polynomial : RecursiveQuadratic.Polynomial R 4 1) :
    difference4 (fun secret ↦ RecursiveQuadratic.message polynomial secret 0) = 0 := by
  simp [difference4, corner, RecursiveQuadratic.message, vecMul, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem difference4_quartic {R : Type} [CommRing R] :
    difference4 (fun secret : Fin 4 → R ↦ secret 0 * secret 1 * secret 2 * secret 3) = 1 := by
  simp [difference4, corner]

/-- This particular required quartic cannot be supplied by the fixed quadratic-message theorem. -/
theorem quartic_not_quadratic {R : Type} [CommRing R] [Nontrivial R] :
    ¬ ∃ polynomial : RecursiveQuadratic.Polynomial R 4 1,
      ∀ secret : Fin 4 → R,
        RecursiveQuadratic.message polynomial secret 0 = secret 0 * secret 1 * secret 2 * secret 3 := by
  rintro ⟨polynomial, hpoly⟩
  have hfunction : (fun secret ↦ RecursiveQuadratic.message polynomial secret 0) =
      (fun secret ↦ secret 0 * secret 1 * secret 2 * secret 3) := funext hpoly
  have hzero := difference4_quadratic polynomial
  rw [hfunction, difference4_quartic] at hzero
  exact one_ne_zero hzero

theorem phaseError_multiply_bound {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (hints : HintTable (ZMod q) n params.levels)
    (first second : Ciphertext (ZMod q) n) (firstMessage secondMessage : ZMod q)
    (firstMessageBound secondMessageBound firstBound secondBound hintBound : ℕ)
    (hm1 : (LatticeCrypto.centeredRepr firstMessage).natAbs ≤ firstMessageBound)
    (hm2 : (LatticeCrypto.centeredRepr secondMessage).natAbs ≤ secondMessageBound)
    (hfirst : (LatticeCrypto.centeredRepr (phaseError secret first firstMessage)).natAbs ≤ firstBound)
    (hsecond : (LatticeCrypto.centeredRepr (phaseError secret second secondMessage)).natAbs ≤ secondBound)
    (hhints : ∀ index, (LatticeCrypto.centeredRepr (hintError params secret hints index)).natAbs ≤ hintBound) :
    (LatticeCrypto.centeredRepr
      (phaseError secret (multiply params hints first second) (firstMessage * secondMessage))).natAbs ≤
        firstMessageBound * secondBound + secondMessageBound * firstBound + firstBound * secondBound +
        (n * n + n + 1) ^ 2 * params.levels * (params.base - 1) * hintBound := by
  rw [phaseError_multiply]
  have h1 := (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le firstMessage
    (phaseError secret second secondMessage)).trans (Nat.mul_le_mul hm1 hsecond)
  have h2 := (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le secondMessage
    (phaseError secret first firstMessage)).trans (Nat.mul_le_mul hm2 hfirst)
  have h3 := (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le
    (phaseError secret first firstMessage) (phaseError secret second secondMessage)).trans
      (Nat.mul_le_mul hfirst hsecond)
  have h12 := (TFHE.NoiseBounds.centeredRepr_add_natAbs_le
    (firstMessage * phaseError secret second secondMessage)
    (secondMessage * phaseError secret first firstMessage)).trans (Nat.add_le_add h1 h2)
  have h123 := (TFHE.NoiseBounds.centeredRepr_add_natAbs_le
    (firstMessage * phaseError secret second secondMessage + secondMessage * phaseError secret first firstMessage)
    (phaseError secret first firstMessage * phaseError secret second secondMessage)).trans
      (Nat.add_le_add h12 h3)
  exact (TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _).trans
    (Nat.add_le_add h123 (relinearizationError_bound params secret hints first second hintBound hhints))

theorem relinearizationError_freshHints_bound {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q)
    (masks : HintIndex n params.levels → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : HintIndex n params.levels → Fin n → ZMod q)
    (bodyErrors : HintIndex n params.levels → ZMod q)
    (first second : Ciphertext (ZMod q) n) (bound : ℕ)
    (hsecret : ∀ row, secret row = 0 ∨ secret row = 1)
    (herrors : ∀ index row, (LatticeCrypto.centeredRepr (errors index row)).natAbs ≤ bound)
    (hbody : ∀ index, (LatticeCrypto.centeredRepr (bodyErrors index)).natAbs ≤ bound) :
    (LatticeCrypto.centeredRepr (relinearizationError params secret
      (freshHints params secret masks innerMasks errors bodyErrors) first second)).natAbs ≤
        (n * n + n + 1) ^ 2 * params.levels * (params.base - 1) * ((n + 1) * bound) :=
  relinearizationError_bound params secret _ first second ((n + 1) * bound)
    (hintError_freshHints_bound params secret masks innerMasks errors bodyErrors bound hsecret herrors hbody)

/-- The obstruction persists on the actual binary-secret support. -/
theorem quartic_not_quadratic_on_corners {R : Type} [CommRing R] [Nontrivial R] :
    ¬ ∃ polynomial : RecursiveQuadratic.Polynomial R 4 1,
      ∀ a b c d : Bool, RecursiveQuadratic.message polynomial (corner a b c d) 0 =
        (corner a b c d : Fin 4 → R) 0 * (corner a b c d) 1 * (corner a b c d) 2 * (corner a b c d) 3 := by
  rintro ⟨polynomial, hpoly⟩
  have hzero := difference4_quadratic polynomial
  unfold difference4 at hzero
  simp_rw [hpoly] at hzero
  change difference4 (fun secret : Fin 4 → R ↦ secret 0 * secret 1 * secret 2 * secret 3) = 0 at hzero
  rw [difference4_quartic] at hzero
  exact one_ne_zero hzero

/-- A concrete table entry lies outside the existing quadratic KDM class even for binary secrets. -/
theorem required_hint_not_quadratic {q : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    (params : Parameters q) (hlevels : 0 < params.levels) :
    ¬ ∃ polynomial : RecursiveQuadratic.Polynomial (ZMod q) 4 1,
      ∀ a b c d : Bool, RecursiveQuadratic.message polynomial (corner a b c d) 0 =
        hintMessage params (corner a b c d)
          (some (.inr (0, 1)), some (.inr (2, 3)), ⟨0, hlevels⟩) := by
  simpa only [hintMessage_quadratic_pair, TFHE.Gadget.Base.gadget, pow_zero, Nat.cast_one, one_mul] using
    (quartic_not_quadratic_on_corners (R := ZMod q))

end FormalProof4FHE.LWE.RecursiveMultiplication
