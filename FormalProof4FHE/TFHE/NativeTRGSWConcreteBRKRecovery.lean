/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWConcreteSuffixSeparation
import FormalProof4FHE.TFHE.CenteredBinomialCorrectness
import FormalProof4FHE.TFHE.BootstrappingSecurity

/-!
# Concrete correct-key recovery of native TFHEpp BRK messages

Once the complete level-one ring key is known, one final-block row of each native TRGSW entry
already recovers its encrypted control bit.  This module proves that deterministic fact at the
TFHEpp level-zero-to-level-one gadget and lifts it through the executable centered-binomial ring
sampler.  The proof is independent of the distribution of the ring secret, so it applies equally
to binary, ternary, or shared-prefix/ternary-suffix keys.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.NativeTRGSWConcreteBRKRecovery

noncomputable section

open BootstrappingCorrectness

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-! ## Concrete level-zero-to-level-one TRGSW layout -/

/-- Level-one coefficient modulus (`uint32_t`). -/
abbrev lvl01Modulus : ℕ := 2 ^ 32

/-- The positive-degree presentation uses `1023 + 1 = 1024` coefficients. -/
abbrev lvl01DegreePred : ℕ := 1023

abbrev lvl01Degree : ℕ := lvl01DegreePred + 1

/-- Rank-one level-one ring. -/
abbrev Lvl01Ring := RLWE.Rq lvl01Modulus (lvl01DegreePred + 1)

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Three base-64 gadget levels. -/
abbrev lvl01Levels : ℕ := 3

/-- Number of encrypted level-zero control bits. -/
abbrev lvl01ControlCount : ℕ := 630

/-- Scalar gadget value used by the native implementation. -/
def lvl01ScalarGadget (level : Fin lvl01Levels) : ZMod lvl01Modulus :=
  (2 ^ (32 - (level.val + 1) * 6) : ℕ)

/-- The corresponding constant-polynomial ring gadget. -/
def lvl01RingGadget (level : Fin lvl01Levels) : Lvl01Ring :=
  LatticeCrypto.Poly.ofPi fun coefficient ↦
    if coefficient.val = 0 then lvl01ScalarGadget level else 0

/-- The top level, whose scalar value is `2^26`. -/
def lvl01TopLevel : Fin lvl01Levels := ⟨0, by decide⟩

@[simp]
theorem lvl01ScalarGadget_top :
    lvl01ScalarGadget lvl01TopLevel = (2 ^ 26 : ZMod lvl01Modulus) := by
  norm_num [lvl01ScalarGadget, lvl01TopLevel]

@[simp]
theorem constantCoefficient_lvl01RingGadget (level : Fin lvl01Levels) :
    SampleExtraction.constantCoefficient (lvl01RingGadget level) =
      lvl01ScalarGadget level := by
  simp [SampleExtraction.constantCoefficient, lvl01RingGadget]

@[simp]
theorem constantCoefficient_lvl01_zero :
    SampleExtraction.constantCoefficient (0 : Lvl01Ring) = 0 := by
  exact BlindRotation.rq_zero_coefficient 0

@[simp]
theorem constantCoefficient_lvl01_add (left right : Lvl01Ring) :
    SampleExtraction.constantCoefficient (left + right) =
      SampleExtraction.constantCoefficient left +
        SampleExtraction.constantCoefficient right := by
  change
    Gadget.Base.coefficientAddHom (q := lvl01Modulus) (lvl01DegreePred + 1) 0
        (left + right) =
      Gadget.Base.coefficientAddHom (lvl01DegreePred + 1) 0 left +
        Gadget.Base.coefficientAddHom (lvl01DegreePred + 1) 0 right
  exact (Gadget.Base.coefficientAddHom
    (q := lvl01Modulus) (lvl01DegreePred + 1) 0).map_add left right

/-- Flattened final-block row at the top gadget level. -/
def lvl01BodyTopRow : Fin (TGSW.rowCount 1 lvl01Levels) :=
  finProdFinEquiv (Fin.last 1, lvl01TopLevel)

/-- Scalar constant coefficient of the correct-key phase in the selected body row. -/
def lvl01BodySample
    (secret : Fin 1 → Lvl01Ring)
    (ciphertext : TGSW.Ciphertext Lvl01Ring 1 lvl01Levels) :
    ZMod lvl01Modulus :=
  SampleExtraction.constantCoefficient
    (TLWE.phase secret (TLWE.entry ciphertext lvl01BodyTopRow))

/-- Correct-key decoder for one native TRGSW control bit. -/
def decodeLvl01Entry
    (secret : Fin 1 → Lvl01Ring)
    (ciphertext : TGSW.Ciphertext Lvl01Ring 1 lvl01Levels) : Bool :=
  decodeNearest 0 (2 ^ 26) (lvl01BodySample secret ciphertext)

/-- The selected ideal body-row coefficient is exactly the binary codeword `0` or `2^26`. -/
theorem constantCoefficient_lvl01Message_mul_topGadget (bit : Bool) :
    SampleExtraction.constantCoefficient
        (embedConstantBit lvl01Modulus lvl01Degree bit *
          lvl01RingGadget lvl01TopLevel) =
      encodeBit 0 (2 ^ 26) bit := by
  cases bit <;>
    simp [BlindRotation.embedConstantBit_eq_embedBit, embedBit, encodeBit,
      lvl01Degree, lvl01DegreePred]

/-- The selected phase is the ideal binary codeword plus exactly its native row error. -/
theorem lvl01BodySample_eq_code_add_rowError
    (secret : Fin 1 → Lvl01Ring) (bit : Bool)
    (ciphertext : TGSW.Ciphertext Lvl01Ring 1 lvl01Levels) :
    lvl01BodySample secret ciphertext =
      encodeBit 0 (2 ^ 26) bit +
        SampleExtraction.constantCoefficient
          (TGSW.rowError (R := Lvl01Ring) secret lvl01RingGadget
            (embedConstantBit lvl01Modulus lvl01Degree bit) ciphertext
            (Fin.last 1, lvl01TopLevel)) := by
  have hphase :
      TLWE.phase secret (TLWE.entry ciphertext lvl01BodyTopRow) =
        embedConstantBit lvl01Modulus lvl01Degree bit *
            lvl01RingGadget lvl01TopLevel +
          TGSW.rowError (R := Lvl01Ring) secret lvl01RingGadget
            (embedConstantBit lvl01Modulus lvl01Degree bit) ciphertext
            (Fin.last 1, lvl01TopLevel) := by
    unfold TGSW.rowError lvl01BodyTopRow
    rw [TGSW.gadgetPhase_last]
    ring
  calc
    lvl01BodySample secret ciphertext =
        SampleExtraction.constantCoefficient
          (embedConstantBit lvl01Modulus lvl01Degree bit *
              lvl01RingGadget lvl01TopLevel +
            TGSW.rowError (R := Lvl01Ring) secret lvl01RingGadget
              (embedConstantBit lvl01Modulus lvl01Degree bit) ciphertext
              (Fin.last 1, lvl01TopLevel)) := by
      exact congrArg SampleExtraction.constantCoefficient hphase
    _ = SampleExtraction.constantCoefficient
          (embedConstantBit lvl01Modulus lvl01Degree bit *
            lvl01RingGadget lvl01TopLevel) +
        SampleExtraction.constantCoefficient
          (TGSW.rowError (R := Lvl01Ring) secret lvl01RingGadget
            (embedConstantBit lvl01Modulus lvl01Degree bit) ciphertext
            (Fin.last 1, lvl01TopLevel)) :=
      constantCoefficient_lvl01_add _ _
    _ = _ := by rw [constantCoefficient_lvl01Message_mul_topGadget]

/-- The scalar sample is no farther from its codeword than the infinity norm of the selected
ring-row error. -/
theorem centeredDistance_lvl01BodySample_code_le_rowError
    (secret : Fin 1 → Lvl01Ring) (bit : Bool)
    (ciphertext : TGSW.Ciphertext Lvl01Ring 1 lvl01Levels) :
    centeredDistance (lvl01BodySample secret ciphertext)
        (encodeBit 0 (2 ^ 26) bit) ≤
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := Lvl01Ring) secret lvl01RingGadget
          (embedConstantBit lvl01Modulus lvl01Degree bit) ciphertext
          (Fin.last 1, lvl01TopLevel)) := by
  rw [lvl01BodySample_eq_code_add_rowError]
  rw [NativeTRGSWConcreteSuffixSeparation.centeredDistance_add_self]
  unfold SampleExtraction.constantCoefficient centeredDistance
  simp only [sub_zero]
  exact LatticeCrypto.coeff_le_cInfNorm
    (TGSW.rowError (R := Lvl01Ring) secret lvl01RingGadget
      (embedConstantBit lvl01Modulus lvl01Degree bit) ciphertext
      (Fin.last 1, lvl01TopLevel)) 0

/-- The two selected codewords have exact centered distance `2^26`. -/
theorem lvl01CodeDistance_eq :
    centeredDistance (0 : ZMod lvl01Modulus) (2 ^ 26) = 2 ^ 26 := by
  simp [centeredDistance, LatticeCrypto.centeredRepr_eq_valMinAbs]
  native_decide

/-- Deterministic correct-key recovery from one bounded native TRGSW entry. -/
theorem decodeLvl01Entry_eq
    (secret : Fin 1 → Lvl01Ring) (bit : Bool)
    (ciphertext : TGSW.Ciphertext Lvl01Ring 1 lvl01Levels)
    (radius : ℕ)
    (hrow :
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := Lvl01Ring) secret lvl01RingGadget
          (embedConstantBit lvl01Modulus lvl01Degree bit) ciphertext
          (Fin.last 1, lvl01TopLevel)) ≤ radius)
    (hmargin : 2 * radius < 2 ^ 26) :
    decodeLvl01Entry secret ciphertext = bit := by
  apply decodeNearest_encodeBit_of_distance_le 0 (2 ^ 26)
      (lvl01BodySample secret ciphertext) radius bit
  · simpa [lvl01CodeDistance_eq] using hmargin
  · exact (centeredDistance_lvl01BodySample_code_le_rowError
      secret bit ciphertext).trans hrow

/-! ## Executable centered-binomial BRK recovery -/

/-- The executable sampler for one coordinate of the native BRK. -/
def lvl01EntrySampler
    (eta : ℕ) (message : Fin lvl01ControlCount → Bool)
    (secret : Fin 1 → Lvl01Ring) (coordinate : Fin lvl01ControlCount) :
    ProbComp (TGSW.Ciphertext Lvl01Ring 1 lvl01Levels) :=
  TGSW.encrypt 1 lvl01Levels
    (RLWE.CenteredBinomial.sampler lvl01Modulus lvl01Degree eta)
    secret lvl01RingGadget
    (embedConstantBit lvl01Modulus lvl01Degree (message coordinate))

/-- Native BRK sampler for an arbitrary binary control vector and arbitrary level-one ring key. -/
def lvl01BRKSampler
    (eta : ℕ) (message : Fin lvl01ControlCount → Bool)
    (secret : Fin 1 → Lvl01Ring) :
    ProbComp (Fin lvl01ControlCount →
      TGSW.Ciphertext Lvl01Ring 1 lvl01Levels) :=
  Fin.mOfFn lvl01ControlCount (lvl01EntrySampler eta message secret)

/-- Correct-key coordinatewise BRK decoder. -/
def decodeLvl01BRK
    (secret : Fin 1 → Lvl01Ring)
    (bootstrappingKey : Fin lvl01ControlCount →
      TGSW.Ciphertext Lvl01Ring 1 lvl01Levels) :
    Fin lvl01ControlCount → Bool :=
  fun coordinate ↦ decodeLvl01Entry secret (bootstrappingKey coordinate)

/-- Support of the finite BRK product projects to each encrypted control entry. -/
theorem lvl01Entry_mem_support_of_mem_support_brk
    (eta : ℕ) (message : Fin lvl01ControlCount → Bool)
    (secret : Fin 1 → Lvl01Ring)
    {bootstrappingKey : Fin lvl01ControlCount →
      TGSW.Ciphertext Lvl01Ring 1 lvl01Levels}
    (hkey : bootstrappingKey ∈ support (lvl01BRKSampler eta message secret))
    (coordinate : Fin lvl01ControlCount) :
    bootstrappingKey coordinate ∈
      support (lvl01EntrySampler eta message secret coordinate) := by
  exact CenteredBinomialCorrectness.mem_support_fin_mOfFn_apply
    lvl01ControlCount (lvl01EntrySampler eta message secret)
    bootstrappingKey hkey coordinate

/-- Every selected body-row error in a supported CBD BRK has infinity norm at most the CBD
width. -/
theorem cInfNorm_lvl01SelectedRowError_le_eta_of_mem_support
    (eta : ℕ) (message : Fin lvl01ControlCount → Bool)
    (secret : Fin 1 → Lvl01Ring)
    {bootstrappingKey : Fin lvl01ControlCount →
      TGSW.Ciphertext Lvl01Ring 1 lvl01Levels}
    (hkey : bootstrappingKey ∈ support (lvl01BRKSampler eta message secret))
    (coordinate : Fin lvl01ControlCount) :
    LatticeCrypto.cInfNorm
        (TGSW.rowError (R := Lvl01Ring) secret lvl01RingGadget
          (embedConstantBit lvl01Modulus lvl01Degree (message coordinate))
          (bootstrappingKey coordinate) (Fin.last 1, lvl01TopLevel)) ≤ eta := by
  apply CenteredBinomialCorrectness.cInfNorm_rowError_le_eta_of_mem_support_encrypt
    (q := lvl01Modulus) (degree := lvl01DegreePred)
    secret lvl01RingGadget
    (embedConstantBit lvl01Modulus lvl01Degree (message coordinate))
  exact lvl01Entry_mem_support_of_mem_support_brk
    eta message secret hkey coordinate

/-- Every BRK in the executable CBD sampler support decodes to the complete encrypted message
vector whenever its bounded width fits the top-row margin. -/
theorem decodeLvl01BRK_eq_of_mem_support
    (eta : ℕ) (heta : 2 * eta < 2 ^ 26)
    (message : Fin lvl01ControlCount → Bool)
    (secret : Fin 1 → Lvl01Ring)
    {bootstrappingKey : Fin lvl01ControlCount →
      TGSW.Ciphertext Lvl01Ring 1 lvl01Levels}
    (hkey : bootstrappingKey ∈ support (lvl01BRKSampler eta message secret)) :
    decodeLvl01BRK secret bootstrappingKey = message := by
  funext coordinate
  apply decodeLvl01Entry_eq secret (message coordinate)
      (bootstrappingKey coordinate) eta
  · exact cInfNorm_lvl01SelectedRowError_le_eta_of_mem_support
      eta message secret hkey coordinate
  · exact heta

/-- Correct-key BRK decoding has exactly zero failure probability for the executable bounded
sampler. -/
theorem probEvent_decodeLvl01BRK_ne_eq_zero
    (eta : ℕ) (heta : 2 * eta < 2 ^ 26)
    (message : Fin lvl01ControlCount → Bool)
    (secret : Fin 1 → Lvl01Ring) :
    Pr[(fun bootstrappingKey ↦
        decodeLvl01BRK secret bootstrappingKey ≠ message) |
      lvl01BRKSampler eta message secret] = 0 := by
  apply probEvent_eq_zero
  intro bootstrappingKey hkey hne
  exact hne (decodeLvl01BRK_eq_of_mem_support eta heta message secret hkey)

end

end FormalProof4FHE.TFHE.NativeTRGSWConcreteBRKRecovery
