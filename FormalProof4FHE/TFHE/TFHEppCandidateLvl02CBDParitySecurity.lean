/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SourceAlignedParityTernarySecurity
import FormalProof4FHE.TFHE.TFHEppCandidateLvl02CBDParameterScreen

/-!
# Exact `2^27` CBD parity-security instantiation

This file instantiates the modulus-generic parity theorem with the checked 27-bit lvl02
parameters.  Both computational source problems use the executable centered-binomial law of
width `2048`:

* degree-`1024` centered-ternary RLWE with `53248` ring samples; and
* dimension-`1024` binary-secret prefix LWE at the complete aligned width `54525952`.

The view theorem has the exact loss `2 ε_RLWE + 4 ε_LWE`.  There is no sampler-comparison,
Gaussian, suffix-PRG, or NTRU term.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TFHEppCandidateLvl02CBDParitySecurity

noncomputable section

open DirectSubsetKeyBRK
open SourceAlignedBRKKSKJointLaw.CompleteView

namespace Parameters

abbrev q := TFHEppCandidateLvl02CBDParameterScreen.modulus
abbrev rows := TFHEppCandidateLvl02CBDParameterScreen.brkRowCount
abbrev cbdEta := TFHEppCandidateLvl02CBDParameterScreen.eta

abbrev Scalar := ZMod q
abbrev Prefix := SourceAlignedParityTernarySecurity.Prefix
abbrev Factor := SourceAlignedParityTernarySecurity.Factor rows
abbrev ScalarGadget :=
  SourceAlignedParityTernarySecurity.ScalarGadget q rows
abbrev View := SourceAlignedParityTernarySecurity.View q rows
abbrev SmallRq := SourceAlignedParityTernarySecurity.SmallRq q

/-- Exact CBD-2048 small-ring error law. -/
def smallErrorSampler : ProbComp SmallRq :=
  RLWE.CenteredBinomial.sampler q 1024 cbdEta

/-- Exact CBD-2048 complete correction-vector law. -/
def correctionSampler : ProbComp (Factor → Scalar) :=
  CenteredBinomialProofErrorSampler.modularVectorSampler
    q (rows * 2048) cbdEta

/-- The security theorem and the correctness screen use the same small-ring CBD law. -/
theorem smallErrorSampler_eq_screen :
    smallErrorSampler =
      TFHEppCandidateLvl02CBDParameterScreen.smallRingErrorSampler := by
  rfl

/-- The security theorem and adaptive correctness tail use the same complete correction law. -/
theorem correctionSampler_eq_screen :
    correctionSampler =
      TFHEppCandidateLvl02CBDParameterScreen.correctionSampler := by
  rfl

/-- The correction law is definitionally an IID vector of executable CBD coefficients. -/
theorem correctionSampler_eq_sampleIID :
    correctionSampler =
      ProbComp.sampleIID (rows * 2048)
        (RLWE.CenteredBinomial.coefficientSampler q cbdEta) := by
  exact CenteredBinomialProofErrorSampler.modularVectorSampler_eq_sampleIID
    q (rows * 2048) cbdEta

/-- The exact small ternary-RLWE source used by the security theorem. -/
noncomputable def smallTernaryCBDRLWEProblem :=
  SourceAlignedParityTernarySecurity.smallTernaryRLWEProblem
    q rows smallErrorSampler

/-- The exact complete-width binary-secret CBD-LWE prefix source. -/
noncomputable def binaryCBDPrefixProblem :=
  SourceAlignedParityTernarySecurity.parityPrefixProblem
    q rows correctionSampler

/-- Twice the BRK row count is the estimator-facing small-ring sample count. -/
theorem smallRLWESampleCount_eq : 2 * rows = 53248 := by
  norm_num [rows, TFHEppCandidateLvl02CBDParameterScreen.brkRowCount,
    SourceAlignedFactorPropagation.NativeAlignment.controlRowCount,
    TFHEppCandidateLvl02CBDParameterScreen.ringRank,
    TFHEppCandidateLvl02CBDParameterScreen.brkLevels,
    TFHEppCandidateLvl02CBDParameterScreen.prefixDimension, TGSW.rowCount]

/-- The complete prefix sample count is the checked aligned width. -/
theorem prefixSampleCount_eq : rows * 2048 =
    TFHEppCandidateLvl02CBDParameterScreen.alignedWidth := by
  rfl

end Parameters

open Parameters

/-- Complete q27/CBD parity candidate view. -/
def candidateViews
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  SourceAlignedParityTernarySecurity.parityCandidateViews
    q rows smallErrorSampler correctionSampler brkContribution

noncomputable def suffixConstructor
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  SourceAlignedParityTernarySecurity.paritySuffixConstructor
    q rows smallErrorSampler correctionSampler brkContribution

noncomputable def randomPrefixConstructor
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  SourceAlignedParityTernarySecurity.parityRandomPrefixConstructor
    q rows smallErrorSampler correctionSampler brkContribution

noncomputable def secondPrefixConstructor
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  SourceAlignedParityTernarySecurity.paritySecondPrefixConstructor
    q rows smallErrorSampler correctionSampler brkContribution

noncomputable def smallRLWEReduction
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.Adversary smallTernaryCBDRLWEProblem :=
  SourceAlignedParityTernarySecurity.endpointSmallRLWEReduction
    q rows smallErrorSampler correctionSampler
    brkContribution distinguisher

/-- Exact q27/CBD source theorem before computational hardness bounds. -/
theorem endpointAdvantage_le_CBD_RLWE_and_CBD_LWE
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) :
    targetAdvantage (candidateViews brkContribution).endpoints distinguisher ≤
      2 * LearningWithErrors.advantage smallTernaryCBDRLWEProblem
        (smallRLWEReduction brkContribution distinguisher) +
      2 * LearningWithErrors.advantage binaryCBDPrefixProblem
        ((randomPrefixConstructor brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage binaryCBDPrefixProblem
        ((secondPrefixConstructor brkContribution).reduction distinguisher) := by
  exact SourceAlignedParityTernarySecurity.endpointAdvantage_le_smallRLWE_and_prefix
    q rows smallErrorSampler correctionSampler
    brkContribution distinguisher

/-- Final exact q27/CBD theorem: ordinary ternary-RLWE and binary-LWE bounds give
`2 ε_RLWE + 4 ε_LWE`. -/
theorem endpointAdvantage_le_hardness
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) (epsilonRLWE epsilonLWE : ℝ)
    (hRLWE : ∀ adversary : LearningWithErrors.Adversary
        smallTernaryCBDRLWEProblem,
      LearningWithErrors.advantage smallTernaryCBDRLWEProblem adversary ≤
        epsilonRLWE)
    (hPrefixFirst : LearningWithErrors.advantage binaryCBDPrefixProblem
        ((randomPrefixConstructor brkContribution).reduction distinguisher) ≤
      epsilonLWE)
    (hPrefixSecond : LearningWithErrors.advantage binaryCBDPrefixProblem
        ((secondPrefixConstructor brkContribution).reduction distinguisher) ≤
      epsilonLWE) :
    targetAdvantage (candidateViews brkContribution).endpoints distinguisher ≤
      2 * epsilonRLWE + 4 * epsilonLWE := by
  exact SourceAlignedParityTernarySecurity.endpointAdvantage_le_hardness
    q rows smallErrorSampler correctionSampler
    brkContribution distinguisher epsilonRLWE epsilonLWE
    hRLWE hPrefixFirst hPrefixSecond

end

end FormalProof4FHE.TFHE.TFHEppCandidateLvl02CBDParitySecurity
