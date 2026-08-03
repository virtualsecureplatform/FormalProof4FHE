/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.TFHEppCandidateLvl02CBDParitySecurity

/-!
# Executable source-aligned correlated joint format

This file packages the exact row-reuse formula implemented by TFHEpp's streamed widened KSK.
Given a real BRK body, the generator removes its public prefix contribution, reuses the remaining
suffix body and BRK error, and adds an independently sampled correction.  The resulting complete
view is exactly `SourceAlignedDenseJointLaw.assemble`; this is an equality of the full sampler,
not a marginal or moment comparison.

The theorem deliberately retains the public BRK-contribution map as an argument.  Showing that a
particular native secret-message TRGSW layout supplies such a public linear map is the separate
cryptographic construction boundary.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.SourceAlignedExecutableJointFormat

noncomputable section

open DirectSubsetKeyBRK
open SourceAlignedBRKKSKJointLaw.CompleteView
open SourceAlignedDenseJointLaw

variable {R Prefix Suffix Factor : Type}

/-- Prefix mask actually consumed by the widened key switch: fresh dense mask plus the public
prefix rows induced from the BRK gadget. -/
def effectivePrefixMask [Add R]
    (maps : PrefixMaps R Prefix Suffix Factor)
    (gadget : Matrix Suffix Factor R)
    (independentMask : Matrix Prefix Factor R) : Matrix Prefix Factor R :=
  independentMask + maps.ksk gadget

/-- Recover the suffix body plus reused BRK error by removing the advertised real-BRK prefix
contribution from its complete scalarized body. -/
def sourceBodyFromBRK [Ring R] [Fintype Prefix]
    (maps : PrefixMaps R Prefix Suffix Factor)
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (brkBody : Factor → R) : Factor → R :=
  brkBody - (maps.brk gadget).transpose *ᵥ prefixSecret

/-- Public format generated from an already fixed real BRK.  It mirrors the implementation
formula without resampling or exposing the reused BRK error. -/
def reuseBRKAssemble [CommRing R] [Fintype Prefix]
    (maps : PrefixMaps R Prefix Suffix Factor)
    (gadget : Matrix Suffix Factor R) (brkBody : Factor → R)
    (prefixSecret : Prefix → R)
    (independentMask : Matrix Prefix Factor R)
    (correction : Factor → R) : DenseView R Prefix Suffix Factor :=
  { gadget := gadget
    brkBody := brkBody
    prefixMask := independentMask
    kskBody :=
      (effectivePrefixMask maps gadget independentMask).transpose *ᵥ prefixSecret +
        sourceBodyFromBRK maps gadget prefixSecret brkBody + correction }

/-- Complete real BRK body in the dense joint-law convention. -/
def realBRKBody [CommRing R] [Fintype Prefix] [Fintype Suffix]
    (maps : PrefixMaps R Prefix Suffix Factor)
    (gadget : Matrix Suffix Factor R)
    (suffixSecret : Suffix → R) (brkError : Factor → R)
    (prefixSecret : Prefix → R) : Factor → R :=
  gadget.transpose *ᵥ suffixSecret + brkError +
    (maps.brk gadget).transpose *ᵥ prefixSecret

/-- Removing the prefix contribution from a real BRK body recovers exactly the suffix body and
the original BRK error. -/
theorem sourceBodyFromBRK_real [CommRing R]
    [Fintype Prefix] [Fintype Suffix]
    (maps : PrefixMaps R Prefix Suffix Factor)
    (gadget : Matrix Suffix Factor R)
    (suffixSecret : Suffix → R) (brkError : Factor → R)
    (prefixSecret : Prefix → R) :
    sourceBodyFromBRK maps gadget prefixSecret
        (realBRKBody maps gadget suffixSecret brkError prefixSecret) =
      gadget.transpose *ᵥ suffixSecret + brkError := by
  funext factor
  simp only [sourceBodyFromBRK, realBRKBody, Pi.sub_apply, Pi.add_apply]
  abel

/-- The implementation-oriented reused-body object is definitionally the complete real
correlated view used by the security reduction. -/
theorem reuseBRKAssemble_real_eq_assemble [CommRing R]
    [Fintype Prefix] [Fintype Suffix] [Fintype Factor]
    (maps : PrefixMaps R Prefix Suffix Factor)
    (gadget : Matrix Suffix Factor R)
    (suffixSecret : Suffix → R) (brkError : Factor → R)
    (prefixSecret : Prefix → R)
    (independentMask : Matrix Prefix Factor R)
    (correction : Factor → R) :
    reuseBRKAssemble maps gadget
        (realBRKBody maps gadget suffixSecret brkError prefixSecret)
        prefixSecret independentMask correction =
      assemble maps true true gadget suffixSecret brkError prefixSecret
        independentMask correction := by
  unfold reuseBRKAssemble assemble
  simp only [branchVector, if_true, effectivePrefixMask]
  rw [sourceBodyFromBRK_real]
  unfold realBRKBody
  congr 1
  funext factor
  simp only [Pi.add_apply]
  abel

/-- Scalar row formula used in C++: when the complete BRK contribution splits into the known
prefix mask pairing plus a plaintext phase, the correlated KSK body can be computed as
`<U,p> + brkBody - messagePhase + correction`. -/
theorem reuseBRKAssemble_kskBody_eq_rowFormula [CommRing R]
    [Fintype Prefix]
    (maps : PrefixMaps R Prefix Suffix Factor)
    (gadget : Matrix Suffix Factor R) (brkBody : Factor → R)
    (prefixSecret : Prefix → R)
    (independentMask : Matrix Prefix Factor R)
    (correction messagePhase : Factor → R)
    (contribution_split :
      (maps.brk gadget).transpose *ᵥ prefixSecret =
        (maps.ksk gadget).transpose *ᵥ prefixSecret + messagePhase) :
    (reuseBRKAssemble maps gadget brkBody prefixSecret independentMask
        correction).kskBody =
      independentMask.transpose *ᵥ prefixSecret + brkBody - messagePhase +
        correction := by
  funext factor
  have hsplit := congrFun contribution_split factor
  simp only [reuseBRKAssemble, effectivePrefixMask, sourceBodyFromBRK,
    Matrix.transpose_add, Matrix.add_mulVec, Pi.add_apply, Pi.sub_apply]
  simp only [Pi.add_apply] at hsplit
  rw [hsplit]
  abel

section Sampler

variable [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
  [Fintype Prefix] [DecidableEq Prefix]
  [Fintype Suffix] [DecidableEq Suffix]
  [Fintype Factor] [DecidableEq Factor]
  [SampleableType (Matrix Prefix Factor R)]

/-- Executable sampling order: fix the entire BRK state first, then sample the independent dense
mask and fresh correction used by the correlated KSK. -/
def executableRealSampler
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) :
    ProbComp (DenseView R Prefix Suffix Factor) := do
  let gadget ← gadgetSampler
  let suffixSecret ← suffixSecretSampler
  let brkError ← brkErrorSampler
  let prefixSecret ← prefixSecretSampler
  let independentMask ← $ᵗ (Matrix Prefix Factor R)
  let correction ← correctionSampler
  return reuseBRKAssemble maps gadget
    (realBRKBody maps gadget suffixSecret brkError prefixSecret)
    prefixSecret independentMask correction

/-- The complete executable sampler is exactly the real endpoint of the dense source-aligned
joint law. -/
theorem executableRealSampler_eq_view
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) :
    executableRealSampler gadgetSampler suffixSecretSampler brkErrorSampler
        prefixSecretSampler correctionSampler maps =
      view gadgetSampler suffixSecretSampler brkErrorSampler
        prefixSecretSampler correctionSampler maps true true := by
  simp only [executableRealSampler, view]
  congr 1
  funext gadget
  congr 1
  funext suffixSecret
  congr 1
  funext brkError
  congr 1
  funext prefixSecret
  congr 1
  funext independentMask
  congr 1
  funext correction
  rw [reuseBRKAssemble_real_eq_assemble]

end Sampler

/-! ## Concrete q27/CBD endpoint -/

namespace CandidateCBD27

open TFHEppCandidateLvl02CBDParitySecurity
open TFHEppCandidateLvl02CBDParitySecurity.Parameters

/-- Streamed-format sampler specialized to the exact q27/CBD candidate. -/
def candidateExecutableRealSampler
    (brkContribution : Parameters.ScalarGadget →
      Matrix Parameters.Prefix Parameters.Factor Parameters.Scalar) :
    ProbComp Parameters.View :=
  executableRealSampler
    (SourceAlignedParityTernarySecurity.parityGadgetSampler q rows)
    (SourceAlignedParityTernarySecurity.paritySuffixSecretSampler q)
    (SourceAlignedParityTernarySecurity.parityBRKErrorSampler q rows
      smallErrorSampler)
    (SourceAlignedParityTernarySecurity.prefixSecretSampler q)
    correctionSampler
    (SourceAlignedParityTernarySecurity.parityPrefixMaps q rows
      brkContribution)

/-- The specialized executable sampler is the complete real endpoint whose advantage is bounded
by the q27/CBD ternary-RLWE and binary-LWE theorem. -/
theorem candidateExecutableRealSampler_eq_candidateReal
    (brkContribution : Parameters.ScalarGadget →
      Matrix Parameters.Prefix Parameters.Factor Parameters.Scalar) :
    candidateExecutableRealSampler brkContribution =
      (candidateViews brkContribution).real := by
  exact executableRealSampler_eq_view
    (SourceAlignedParityTernarySecurity.parityGadgetSampler q rows)
    (SourceAlignedParityTernarySecurity.paritySuffixSecretSampler q)
    (SourceAlignedParityTernarySecurity.parityBRKErrorSampler q rows
      smallErrorSampler)
    (SourceAlignedParityTernarySecurity.prefixSecretSampler q)
    correctionSampler
    (SourceAlignedParityTernarySecurity.parityPrefixMaps q rows
      brkContribution)

/-- A literal public row stores 1024 q27 mask coefficients and one body coefficient. -/
def literalRowBytes : ℕ := (1024 + 1) * 4

/-- Exact byte count of the uncompressed widened KSK public rows. -/
def literalKSKBytes : ℕ :=
  TFHEppCandidateLvl02CBDParameterScreen.alignedWidth * literalRowBytes

theorem literalKSKBytes_eq : literalKSKBytes = 223556403200 := by
  norm_num [literalKSKBytes, literalRowBytes,
    TFHEppCandidateLvl02CBDParameterScreen.alignedWidth,
    TFHEppCandidateLvl02CBDParameterScreen.brkRowCount,
    SourceAlignedFactorPropagation.NativeAlignment.controlRowCount,
    TFHEppCandidateLvl02CBDParameterScreen.ringRank,
    TFHEppCandidateLvl02CBDParameterScreen.brkLevels,
    TFHEppCandidateLvl02CBDParameterScreen.prefixDimension,
    TFHEppCandidateLvl02CBDParameterScreen.ringDegree, TGSW.rowCount]

end CandidateCBD27

end

end FormalProof4FHE.TFHE.SourceAlignedExecutableJointFormat
