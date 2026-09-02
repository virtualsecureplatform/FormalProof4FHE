/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CompactCoverCyclicCompiler
import FormalProof4FHE.RLWE.CompactCoverBGVExactNoise
import FormalProof4FHE.RLWE.CompactCoverBGVNoiseSoundness
import FormalProof4FHE.RLWE.CompactCoverBGVScalarSecurity

/-!
# Concrete N=65536 compact-cover BGV manifest and certificate

This module fixes the six native stages used by the executable compact-cover
BGV instantiation. Exact correctness bounds are computed in
`CompactCoverBGVExactNoise`; rational logarithms below are presentation-only
metadata. Attack estimates are likewise kept separate from correctness.
-/

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGV65536

open CompactCoverTechnical CompactCoverCyclicCompiler
open CompactCoverBGVExactNoise

set_option maxRecDepth 100000

/-- The complete scalar thin-BGV bootstrap stage order. -/
inductive Stage where
  | forwardBadDimension
  | homomorphicInnerProduct
  | degreeTwoTrace
  | inverseBadDimension
  | boundedDigitExtraction
  | cyclicReturn
  deriving DecidableEq, Fintype, Repr

def Stage.sourceWidth : Stage → ℕ
  | .forwardBadDimension => 1
  | .homomorphicInnerProduct => 1
  | .degreeTwoTrace => 1
  | .inverseBadDimension => 1
  | .boundedDigitExtraction => 1
  | .cyclicReturn => 1

def Stage.targetWidth : Stage → ℕ
  | .forwardBadDimension => 1
  | .homomorphicInnerProduct => 1
  | .degreeTwoTrace => 1
  | .inverseBadDimension => 1
  | .boundedDigitExtraction => 1
  | .cyclicReturn => 1

def Stage.peakWidth : Stage → ℕ
  | .forwardBadDimension => 368
  | .homomorphicInnerProduct => 4
  | .degreeTwoTrace => 2
  | .inverseBadDimension => 368
  | .boundedDigitExtraction => 8
  | .cyclicReturn => 2

@[simp] theorem stage_card : Fintype.card Stage = 6 := by decide

theorem stage_peak_le (stage : Stage) : stage.peakWidth ≤ 368 := by
  cases stage <;> decide

theorem stage_source_nonzero (stage : Stage) : 0 < stage.sourceWidth := by
  cases stage <;> decide

theorem stage_target_nonzero (stage : Stage) : 0 < stage.targetWidth := by
  cases stage <;> decide

/-- Mixed-radix counts extracted from the reference bad-dimension BSGS
schedule. -/
def babySwitchCount : ℕ := 181
def giantSwitchCount : ℕ := 180
def backwardSwitchCount : ℕ := 1
def traceSwitchCount : ℕ := 1
def distinctSwitchCount : ℕ := 362

@[simp] theorem target_switch_count :
    babySwitchCount + giantSwitchCount + backwardSwitchCount =
      distinctSwitchCount := by decide

@[simp] theorem target_trace_count : traceSwitchCount = 1 := by decide

/-- The trace and bad-dimension backward maps both use exponent 65537 modulo
131072 in this concrete order-two instance. -/
def backwardExponent : ℕ := 65537
def traceExponent : ℕ := 65537

@[simp] theorem backward_eq_trace : backwardExponent = traceExponent := rfl

/-- Every concrete relabel/duplicate/restrict operation is represented by the
same admissible-map constructor used by the cyclic compiler. -/
def manifestAdmissibleMap
    {SourceLabel TargetLabel GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (sourceName : SourceLabel → GroupIndex)
    (targetName : TargetLabel → GroupIndex)
    (sourceForTarget : TargetLabel → SourceLabel) :
    CompactCoverCyclicCompiler.AdmissibleMap R
      (PartialCover SourceLabel R) (PartialCover TargetLabel R) :=
  frontierRelabelAdmissible action sourceName targetName sourceForTarget

/-- Consequently every manifest relabel carries a witness-affine row into the
target frontier exactly. -/
theorem manifest_mapWitnessAffine_value
    {SourceLabel TargetLabel GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (sourceName : SourceLabel → GroupIndex)
    (targetName : TargetLabel → GroupIndex)
    (sourceForTarget : TargetLabel → SourceLabel)
    (form : WitnessAffine (PartialCover SourceLabel R)) (witness : R) :
    (mapWitnessAffine
      (manifestAdmissibleMap action sourceName targetName sourceForTarget)
      form).value
        (restrictedFixedEmbedding action targetName witness) =
      frontierRelabel action sourceName targetName sourceForTarget
        (form.value (restrictedFixedEmbedding action sourceName witness)) := by
  exact mapWitnessAffine_value
    (manifestAdmissibleMap action sourceName targetName sourceForTarget)
    form witness

/-- Proof-carrying numerical summary.  Values are log2 quantities: failure is
stored as a positive exponent, while variances use signed logarithms. -/
structure NativeCertificate where
  modulusBits : ℕ
  limbCount : ℕ
  securityBits : ℚ
  failureExponent : ℚ
  acceptedInputLogVariance : ℚ
  freshOutputLogVariance : ℚ
  digitErrorBound : ℕ
  digitPolynomialDegree : ℕ

def NativeCertificate.Valid (certificate : NativeCertificate) : Prop :=
  certificate.modulusBits = 915 ∧
  certificate.limbCount = 15 ∧
  128 ≤ certificate.securityBits ∧
  128 ≤ certificate.failureExponent ∧
  certificate.freshOutputLogVariance <
    certificate.acceptedInputLogVariance ∧
  certificate.digitPolynomialDegree = 4 * certificate.digitErrorBound + 1

/-- Values emitted by `compact_cover_bgv_certificate.py`, rounded toward the
conservative side at two decimal places. -/
def selectedCertificate : NativeCertificate where
  modulusBits := 915
  limbCount := 15
  securityBits := 24253 / 100
  failureExponent := 13356 / 100
  acceptedInputLogVariance := -900
  freshOutputLogVariance := -94839 / 100
  digitErrorBound := 43
  digitPolynomialDegree := 173

theorem selectedCertificate_valid : selectedCertificate.Valid := by
  norm_num [NativeCertificate.Valid, selectedCertificate]

/-- Exact selected frontier storage remains the previously checked 5.39-GiB
residue count. -/
theorem selected_frontier_residues :
    ciphertextResidues 65536 368 selectedCertificate.limbCount =
      723517440 := by decide

/-! ## Scalar phase lift and its non-contraction boundary -/

/-- Stages of the phase-lift helper.  This helper is not itself a bootstrap. -/
inductive ScalarStage where
  | phaseLift
  | homomorphicDecryptionTransition
  | exactPublicDivision
  deriving DecidableEq, Fintype, Repr

@[simp] theorem scalar_stage_card : Fintype.card ScalarStage = 3 := by decide

def ScalarStage.frontierWidth : ScalarStage → ℕ
  | .phaseLift => 1
  | .homomorphicDecryptionTransition => 1
  | .exactPublicDivision => 1

@[simp] theorem scalar_stage_width (stage : ScalarStage) :
    stage.frontierWidth = 1 := by cases stage <;> rfl

/-- Exact phase identity behind the executable scalar phase lift. -/
theorem scalar_direct_phase
    {R : Type} [CommRing R]
    (p message oldError switchError : R) :
    p * (message + p * oldError) + p ^ 2 * switchError =
      p * message + p ^ 2 * (oldError + switchError) := by
  ring

/-- Exact public division by the unit `p` preserves the old error and adds the
switch error.  In particular, this operation alone is not noise contracting. -/
theorem scalar_direct_div_phase
    {R : Type} [CommRing R]
    (p : Rˣ) (message oldError switchError : R) :
    (↑(p⁻¹) : R) *
        ((p : R) * message + (p : R) ^ 2 * (oldError + switchError)) =
      message + (p : R) * (oldError + switchError) := by
  have hp : (↑(p⁻¹) : R) * p = 1 := by simp
  calc
    _ = ((↑(p⁻¹) : R) * p) * message +
        (((↑(p⁻¹) : R) * p) * p) * (oldError + switchError) := by
          simp only [pow_two]
          ring
    _ = _ := by rw [hp]; simp

/-- The old error appears with coefficient one after phase lift and division. -/
theorem scalar_direct_error_difference
    {R : Type} [CommRing R]
    (oldError switchError : R) :
    (oldError + switchError) - oldError = switchError := by
  abel

/-! ## Genuine low-to-high scalar bootstrap normal form -/

/-- If the low ciphertext modulus is `1 mod p²`, centered scaling creates a
bounded carry in the low p-adic digit. -/
theorem lowToHigh_carry_phase
    {R : Type} [CommRing R]
    (p message oldError carry quotientFactor switchError : R) :
    p * (message + p * oldError) +
        (1 + p ^ 2 * quotientFactor) * carry + p ^ 2 * switchError =
      p * message + carry +
        p ^ 2 * (oldError + quotientFactor * carry + switchError) := by
  ring

/-- Abstract constant projector used by the scalar trace specialization. -/
structure ConstantProjector (R : Type) [CommRing R] where
  project : R →+ R
  constant : R → R
  project_constant : ∀ value, project (constant value) = constant value

/-- After constant projection, only the constant carry remains. -/
theorem project_scaledMessage_add_carry
    {R : Type} [CommRing R]
    (projector : ConstantProjector R)
    (p message carry : R) :
    projector.project (projector.constant (p * message) + carry) =
      projector.constant (p * message) + projector.project carry := by
  rw [map_add, projector.project_constant]

/-- Complete plaintext identity after bounded carry removal. -/
theorem scalarBootstrap_plaintext
    {R : Type} [CommRing R]
    (p : Rˣ) (message carry : R) (remove : R → R)
    (hremove : remove ((p : R) * message + carry) = (p : R) * message) :
    (↑(p⁻¹) : R) * remove ((p : R) * message + carry) = message := by
  rw [hremove, ← mul_assoc]
  simp

/-! ## Concrete split-coordinate trace -/

abbrev ScalarSlot := Bool × Fin 32768

/-- Full Galois trace in the split NTT representation.  The regular action
permutes all slots, so its orbit sum is the constant function containing the
sum of all input coordinates. -/
def fullSplitTrace {R : Type} [CommRing R] :
    (ScalarSlot → R) →+ (ScalarSlot → R) where
  toFun value := fun _ => ∑ slot, value slot
  map_zero' := by funext; simp
  map_add' left right := by funext; simp [Finset.sum_add_distrib]

theorem fullSplitTrace_eq_constant
    {R : Type} [CommRing R] (value : ScalarSlot → R) :
    fullSplitTrace value = fun _ => ∑ slot, value slot := rfl

theorem fullSplitTrace_constant
    {R : Type} [CommRing R] (value : R) :
    fullSplitTrace (fun _ : ScalarSlot => value) =
      fun _ => (65536 : ℕ) • value := by
  funext
  simp [fullSplitTrace, Fintype.card_prod]

/-- The sixteen public automorphism exponents used by the executable trace. -/
def concreteTraceExponents : List ℕ :=
  [5, 25, 625, 128481, 28609, 61313, 7937, 81409,
   31745, 63489, 126977, 122881, 114689, 98305, 65537, 131071]

@[simp] theorem concreteTraceExponents_length :
    concreteTraceExponents.length = 16 := by decide

theorem concreteTraceExponents_odd :
    ∀ exponent ∈ concreteTraceExponents, Odd exponent := by decide

/-- The doubling schedule used by the first fifteen trace stages. -/
def cyclicDoublingTrace {M : Type} [AddCommMonoid M]
    (action : ℕ → M →+ M) : ℕ → M → M
  | 0, value => value
  | steps + 1, value =>
      cyclicDoublingTrace action steps value +
        action (2 ^ steps) (cyclicDoublingTrace action steps value)

/-- Repeated doubling enumerates every binary combination exactly once. -/
theorem cyclicDoublingTrace_eq_sum
    {M : Type} [AddCommMonoid M]
    (action : ℕ → M →+ M)
    (hzero : ∀ value, action 0 value = value)
    (hcomp : ∀ left right value,
      action left (action right value) = action (left + right) value)
    (steps : ℕ) (value : M) :
    cyclicDoublingTrace action steps value =
      ∑ index ∈ Finset.range (2 ^ steps), action index value := by
  induction steps with
  | zero => simp [cyclicDoublingTrace, hzero]
  | succ steps ih =>
      rw [cyclicDoublingTrace, ih, map_sum]
      simp_rw [hcomp]
      rw [show 2 ^ (steps + 1) = 2 ^ steps + 2 ^ steps by omega]
      rw [Finset.sum_range_add]

/-- Resource-only fields of the old phase-lift experiment.  No contraction
claim is included. -/
structure PhaseLiftResourceCertificate where
  modulusBits : ℕ
  limbCount : ℕ
  gadgetDigits : ℕ
  securityBits : ℚ
  outputErrorLogBound : ℚ

def PhaseLiftResourceCertificate.Valid
    (certificate : PhaseLiftResourceCertificate) : Prop :=
  certificate.modulusBits = 1402 ∧
  certificate.limbCount = 23 ∧
  certificate.gadgetDigits = 2 ∧
  128 ≤ certificate.securityBits ∧
  certificate.outputErrorLogBound < certificate.modulusBits - 1

def selectedPhaseLiftResources : PhaseLiftResourceCertificate where
  modulusBits := 1402
  limbCount := 23
  gadgetDigits := 2
  securityBits := 13244 / 100
  outputErrorLogBound := 52

theorem selectedPhaseLiftResources_valid :
    selectedPhaseLiftResources.Valid := by
  norm_num [PhaseLiftResourceCertificate.Valid, selectedPhaseLiftResources]

/-! ## Concrete scalar FHE cycle certificate -/

inductive BootstrapStage where
  | modulusDown
  | lowToHighPhaseLift
  | constantTrace
  | boundedDigitRemoval
  | exactDivision
  | multiplicationClosure
  deriving DecidableEq, Fintype, Repr

@[simp] theorem bootstrap_stage_card : Fintype.card BootstrapStage = 6 := by decide

def traceKeyCount : ℕ := 16
def traceGadgetDigits : ℕ := 23
def traceDropAfter : List ℕ := [8, 16]

@[simp] theorem trace_drop_count : traceDropAfter.length = 2 := by decide

/-- Presentation summary emitted by the deterministic recurrence. Logarithms
are conservative decimal lower/upper bounds represented as rationals; the
actual correctness theorem uses `ExactCycleCertificate`. -/
structure ScalarCycleCertificate where
  fullModulusBits : ℕ
  lowModulusBits : ℕ
  fullLimbs : ℕ
  outputLimbs : ℕ
  carryBound : ℕ
  digitPolynomialDegree : ℕ
  outputErrorLogBound : ℚ
  outputCapacityLogBound : ℚ
  multiplyErrorLogBound : ℚ
  multiplyCapacityLogBound : ℚ
  contractionBits : ℚ

def ScalarCycleCertificate.DisplayConsistent
    (certificate : ScalarCycleCertificate) : Prop :=
  certificate.fullModulusBits = 1402 ∧
  certificate.lowModulusBits = 61 ∧
  certificate.fullLimbs = 23 ∧
  certificate.outputLimbs = 13 ∧
  certificate.carryBound = 23 ∧
  certificate.digitPolynomialDegree = 4 * certificate.carryBound + 1 ∧
  certificate.outputErrorLogBound < certificate.outputCapacityLogBound ∧
  certificate.multiplyErrorLogBound < certificate.multiplyCapacityLogBound ∧
  0 < certificate.contractionBits

def selectedScalarCycleCertificate : ScalarCycleCertificate where
  fullModulusBits := 1402
  lowModulusBits := 61
  fullLimbs := 23
  outputLimbs := 13
  carryBound := 23
  digitPolynomialDegree := 93
  outputErrorLogBound := 64198 / 100
  outputCapacityLogBound := 77560 / 100
  multiplyErrorLogBound := 417 / 100
  multiplyCapacityLogBound := 4399 / 100
  contractionBits := 2741 / 100

theorem selectedScalarCycleCertificate_displayConsistent :
    selectedScalarCycleCertificate.DisplayConsistent := by
  norm_num [ScalarCycleCertificate.DisplayConsistent,
    selectedScalarCycleCertificate]

/-- Computational attack-cost metadata is intentionally not a correctness
certificate and is not used by any cryptographic reduction theorem. -/
structure ScalarSecurityEstimate where
  sourceBits : ℚ
  reductionReserveBits : ℚ
  retainedBits : ℚ

def selectedScalarSecurityEstimate : ScalarSecurityEstimate where
  sourceBits := 13344 / 100
  reductionReserveBits := 1
  retainedBits := 13244 / 100

theorem selectedScalarSecurityEstimate_arithmetic :
    selectedScalarSecurityEstimate.retainedBits =
      selectedScalarSecurityEstimate.sourceBits -
        selectedScalarSecurityEstimate.reductionReserveBits := by
  norm_num [selectedScalarSecurityEstimate]

/-- The exact-natural recurrence, rather than the rounded logarithmic display,
closes both binary gates back into the accepted bootstrap input set. -/
theorem selectedExactCycle_closesAdditionAndMultiplication :
    oneLimbAdditionState.bound ≤ acceptedInputError ∧
      multiplicationState.bound ≤ acceptedInputError :=
  ⟨selectedExactCycleCertificate.additionCloses,
    selectedExactCycleCertificate.multiplicationCloses⟩

/-- Concrete polynomial correctness used by the scalar digit-removal stage. -/
theorem selectedDigitRemoval_correct
    (message : ZMod plaintextSquare) (carry : ℤ)
    (lower : -(digitErrorBound : ℤ) ≤ carry)
    (upper : carry ≤ digitErrorBound) :
    coefficientEval digitRemovalCoefficients
        ((plaintextPrime : ZMod plaintextSquare) * message + carry) =
      (plaintextPrime : ZMod plaintextSquare) * message :=
  digitRemovalPolynomial_correct message carry lower upper

/-- Two phase-lift rows, sixteen level-specific 23-row trace keys, and four
public quadratic-hint elements occupy exactly this many 64-bit residues. -/
@[simp] theorem scalar_bootstrap_key_residues :
    2 * ciphertextResidues 65536 1 23 +
      8 * 23 * ciphertextResidues 65536 1 23 +
      8 * 23 * ciphertextResidues 65536 1 22 +
      4 * elementResidues 65536 23 = 1097334784 := by decide

/-- The complete evaluation-row family is transported jointly; no marginal
or per-row circular-security assumption is introduced. -/
theorem scalarEvaluationRows_uniform
    {Row R : Type} [Finite Row] [DecidableEq Row]
    [CommRing R] [Fintype R]
    [SampleableType R] [SampleableType (Row → R × R)]
    (pivot : Rˣ) (offset : R)
    (message : Row → WitnessAffine R) (publicConstant : Row → R) :
    evalDist (compilerBatch pivot offset message publicConstant <$>
        ($ᵗ (Row → R × R))) = evalDist ($ᵗ (Row → R × R)) :=
  compilerBatch_uniform_evalDist pivot offset message publicConstant

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGV65536
