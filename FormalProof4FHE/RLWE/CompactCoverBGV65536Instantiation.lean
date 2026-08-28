/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CompactCoverCyclicCompiler

/-!
# Concrete N=65536 compact-cover BGV manifest and certificate

This module fixes the six native stages and the integer/rational certificate
fields used by the executable compact-cover BGV instantiation.  Analytic noise
and attack estimates remain explicit certificate inputs; Lean checks their
composition, schedule widths, contraction, and target inequalities.
-/

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGV65536

open CompactCoverTechnical CompactCoverCyclicCompiler

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

/-! ## Scalar-only direct specialization -/

/-- For a scalar payload the p-to-p² phase lift absorbs the old BGV error,
so one full-modulus transition and exact division replace the packed maps. -/
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

/-- Exact phase identity behind the executable scalar refresh. -/
theorem scalar_direct_phase
    {R : Type} [CommRing R]
    (p message oldError switchError : R) :
    p * (message + p * oldError) + p ^ 2 * switchError =
      p * message + p ^ 2 * (oldError + switchError) := by
  ring

/-- Exact public division by the unit `p` returns an ordinary plaintext-p BGV
phase. -/
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

/-- Numeric fields of the deterministic scalar certificate. -/
structure ScalarCertificate where
  modulusBits : ℕ
  limbCount : ℕ
  gadgetDigits : ℕ
  securityBits : ℚ
  acceptedInputLogVariance : ℚ
  outputLogVarianceBound : ℚ
  outputErrorLogBound : ℚ

def ScalarCertificate.Valid (certificate : ScalarCertificate) : Prop :=
  certificate.modulusBits = 915 ∧
  certificate.limbCount = 15 ∧
  certificate.gadgetDigits = 5 ∧
  128 ≤ certificate.securityBits ∧
  certificate.outputLogVarianceBound <
    certificate.acceptedInputLogVariance ∧
  certificate.outputErrorLogBound < certificate.modulusBits - 1

def selectedScalarCertificate : ScalarCertificate where
  modulusBits := 915
  limbCount := 15
  gadgetDigits := 5
  securityBits := 23114 / 100
  acceptedInputLogVariance := -900
  outputLogVarianceBound := -138757 / 100
  outputErrorLogBound := 22065 / 100

theorem selectedScalarCertificate_valid :
    selectedScalarCertificate.Valid := by
  norm_num [ScalarCertificate.Valid, selectedScalarCertificate]

@[simp] theorem scalar_bootstrap_key_residues :
    5 * ciphertextResidues 65536 1 15 = 9830400 := by decide

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGV65536
