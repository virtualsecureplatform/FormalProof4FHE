/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.TFHEppCandidateLvl02DenseSecurity
import FormalProof4FHE.TFHE.SourceAlignedSuffixRLWEReduction

/-!
# Parity-Placed Ternary Security for the TFHEpp lvl02 Candidate

This file replaces the contiguous half-ring suffix of the balanced lvl02 candidate by an
interleaved secret layout:

* the shared binary lvl0 key occupies the even coefficients of the degree-2048 ring key;
* an independent centered-ternary degree-1024 key occupies the odd coefficients; and
* the known-prefix maps select exactly the even rows of the complete scalarized gadget.

The complete source-aligned suffix game is then exactly ordinary degree-1024 ternary RLWE with
twice the number of ring samples.  The equality has no hybrid, statistical, or support loss.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TFHEppCandidateLvl02ParitySecurity

noncomputable section

open DirectSubsetKeyBRK
open DirectSubsetKeyBRK.PublicViewConstructor
open SourceAlignedBRKKSKJointLaw.CompleteView
open SourceAlignedDenseJointLaw

open TFHEppSourceAlignedParameterScreen.CandidateLvl02

instance modulus_gt_one : Fact (1 < 2 ^ 64) := ⟨by norm_num⟩

/-! ## Exact parity secret and error samplers -/

/-- The small ring supplying the odd half of the degree-2048 target secret. -/
abbrev Scalar := ZMod (2 ^ 64)
abbrev RingCoordinate := Fin (1 * (2047 + 1))
abbrev Factor := Fin (brkRowCount * (2047 + 1))
abbrev RingGadget := SourceAlignedSuffixRLWEReduction.RingChallenge
  (2 ^ 64) 2047 brkRowCount
abbrev ScalarGadget := SourceAlignedSuffixRLWEReduction.ScalarChallenge
  (2 ^ 64) 2047 brkRowCount
abbrev SmallRq := RLWE.Rq (2 ^ 64) 1024

/-- Turn 1024 centered-ternary digits into one degree-1024 ring element. -/
def ternarySmallRq (digits : Fin suffixDimension → Fin 3) : SmallRq :=
  (TFHE.Native.CoefficientStructuredLWE.coefficientEquiv (2 ^ 64) 1024).symm
    (fun coordinate ↦
      TFHEppCandidateLvl02DenseSecurity.Parameters.embedTernaryDigit
        (digits (Fin.cast suffixDimension_eq.symm coordinate)))

/-- Rank-one explicit secret corresponding to the small ternary ring element. -/
def ternarySmallSecret (digits : Fin suffixDimension → Fin 3) :
    RLWE.Secret (2 ^ 64) 1024 :=
  fun _ ↦ ternarySmallRq digits

/-- Exact coefficientwise centered-ternary degree-1024 ring-secret sampler. -/
def ternarySmallSecretSampler : ProbComp (RLWE.Secret (2 ^ 64) 1024) :=
  ternarySmallSecret <$> ($ᵗ (Fin suffixDimension → Fin 3))

/-- Place the ternary small-ring secret in the odd coefficients and expose its complete ordinary
coefficient vector. -/
def embedTernaryParity (digits : Fin suffixDimension → Fin 3) :
    RingCoordinate → Scalar :=
  SourceAlignedSuffixRLWEReduction.bodyCoefficientEquiv (2 ^ 64) 2047 1
    (RLWE.OddSecretReduction.oddSecretEmbed (2 ^ 64) 1024
      (ternarySmallSecret digits))

/-- Address an even or odd target-ring coefficient inside the rank-one flattened scalar secret. -/
def parityRingCoordinate (branch : Fin 2) (coordinate : Fin 1024) :
    RingCoordinate :=
  finProdFinEquiv
    (0, Fin.cast (by norm_num)
      (RLWE.EvenOddDecomposition.parityIndexEquiv 1024 (branch, coordinate)))

/-- The ternary suffix contributes zero to every even target-ring coefficient. -/
theorem embedTernaryParity_even (digits : Fin suffixDimension → Fin 3)
    (coordinate : Fin 1024) :
    embedTernaryParity digits (parityRingCoordinate 0 coordinate) = 0 := by
  rw [embedTernaryParity,
    SourceAlignedSuffixRLWEReduction.bodyCoefficientEquiv_apply]
  unfold SourceAlignedBRKKSKJointLaw.Algebra.bodyCoefficients
    SampleExtraction.extractedSecret parityRingCoordinate
    RLWE.OddSecretReduction.oddSecretEmbed
  simp only [Equiv.symm_apply_apply]
  have h := RLWE.EvenOddDecomposition.coefficientEquiv_joinRq_even
    (2 ^ 64) 1024 0 (ternarySmallSecret digits 0) coordinate
  simpa [TFHE.Native.CoefficientStructuredLWE.coefficientEquiv] using h

/-- Every odd target-ring coefficient is exactly its intended centered-ternary digit. -/
theorem embedTernaryParity_odd (digits : Fin suffixDimension → Fin 3)
    (coordinate : Fin 1024) :
    embedTernaryParity digits (parityRingCoordinate 1 coordinate) =
      TFHEppCandidateLvl02DenseSecurity.Parameters.embedTernaryDigit
        (digits (Fin.cast suffixDimension_eq.symm coordinate)) := by
  rw [embedTernaryParity,
    SourceAlignedSuffixRLWEReduction.bodyCoefficientEquiv_apply]
  unfold SourceAlignedBRKKSKJointLaw.Algebra.bodyCoefficients
    SampleExtraction.extractedSecret parityRingCoordinate
    RLWE.OddSecretReduction.oddSecretEmbed ternarySmallSecret ternarySmallRq
  simp only [Equiv.symm_apply_apply]
  have h := RLWE.EvenOddDecomposition.coefficientEquiv_joinRq_odd
    (2 ^ 64) 1024 0
      ((TFHE.Native.CoefficientStructuredLWE.coefficientEquiv (2 ^ 64) 1024).symm
        (fun coordinate ↦
          TFHEppCandidateLvl02DenseSecurity.Parameters.embedTernaryDigit
            (digits (Fin.cast suffixDimension_eq.symm coordinate))))
      coordinate
  simpa [TFHE.Native.CoefficientStructuredLWE.coefficientEquiv] using h

/-- Exact odd-coordinate centered-ternary suffix sampler. -/
def paritySuffixSecretSampler : ProbComp (RingCoordinate → Scalar) :=
  (fun secret ↦
    SourceAlignedSuffixRLWEReduction.bodyCoefficientEquiv (2 ^ 64) 2047 1
      (RLWE.OddSecretReduction.oddSecretEmbed (2 ^ 64) 1024 secret)) <$>
    ternarySmallSecretSampler

/-- The factored definition above is exactly direct coefficientwise parity embedding of the
sampled ternary digit vector. -/
theorem paritySuffixSecretSampler_eq_coefficientwise :
    paritySuffixSecretSampler =
      embedTernaryParity <$> ($ᵗ (Fin suffixDimension → Fin 3)) := by
  simp only [paritySuffixSecretSampler, ternarySmallSecretSampler,
    Functor.map_map]
  congr 1

/-- One degree-2048 error consists of independent even and odd degree-1024 errors.  Flattening
all independently sampled ring errors retains their complete coefficient correlation law. -/
def parityBRKErrorSampler (smallErrorSampler : ProbComp SmallRq) :
    ProbComp (Factor → Scalar) :=
  SourceAlignedSuffixRLWEReduction.bodyCoefficientEquiv (2 ^ 64) 2047 brkRowCount <$>
    ProbComp.sampleIID brkRowCount
      (RLWE.OddSecretReduction.pairedErrorSampler (2 ^ 64) 1024 smallErrorSampler)

/-- The structured scalar challenge induced from all rank-one degree-2048 ring masks. -/
def parityGadgetSampler : ProbComp ScalarGadget :=
  SourceAlignedSuffixRLWEReduction.scalarizeChallenge <$> ($ᵗ RingGadget)

/-- Complete source-aligned scalar suffix problem for the parity layout. -/
noncomputable def paritySuffixProblem (smallErrorSampler : ProbComp SmallRq) :=
  suffixProblem parityGadgetSampler paritySuffixSecretSampler
    (parityBRKErrorSampler smallErrorSampler)

/-- The explicit sampler presentation is exactly the generic scalarization of the odd-secret
ring problem. -/
theorem paritySuffixProblem_eq_scalarProblem
    (smallErrorSampler : ProbComp SmallRq) :
    paritySuffixProblem smallErrorSampler =
      SourceAlignedSuffixRLWEReduction.scalarProblem (2 ^ 64) 2047 brkRowCount
        ternarySmallSecretSampler
        (RLWE.OddSecretReduction.oddSecretEmbed (2 ^ 64) 1024)
        (RLWE.OddSecretReduction.pairedErrorSampler (2 ^ 64) 1024 smallErrorSampler) := by
  rfl

/-! ## Direct reduction to ordinary ternary RLWE -/

/-- The conventional degree-1024 ternary RLWE problem with twice the BRK ring-sample count. -/
noncomputable def smallTernaryRLWEProblem (smallErrorSampler : ProbComp SmallRq) :=
  RLWE.problem (2 ^ 64) 1024 (2 * brkRowCount)
    ternarySmallSecretSampler smallErrorSampler

/-- Compose exact scalar-to-ring transport with the exact odd-secret-to-small-ring reduction. -/
noncomputable def smallRLWEReduction
    {smallErrorSampler : ProbComp SmallRq}
    (adversary : LearningWithErrors.Adversary
      (paritySuffixProblem smallErrorSampler)) :
    LearningWithErrors.Adversary
      (smallTernaryRLWEProblem smallErrorSampler) :=
  RLWE.OddSecretReduction.reduction (q := 2 ^ 64) (half := 1024)
    (samples := brkRowCount) (by norm_num)
    (SourceAlignedSuffixRLWEReduction.ringAdversary adversary)

/-- Exact suffix theorem: the complete source-aligned parity problem has precisely the advantage
of ordinary degree-1024 ternary RLWE with twice as many samples. -/
theorem paritySuffixAdvantage_eq_smallTernaryRLWE
    (smallErrorSampler : ProbComp SmallRq)
    (adversary : LearningWithErrors.Adversary
      (paritySuffixProblem smallErrorSampler)) :
    LearningWithErrors.advantage (paritySuffixProblem smallErrorSampler) adversary =
      LearningWithErrors.advantage
        (smallTernaryRLWEProblem smallErrorSampler)
        (smallRLWEReduction adversary) := by
  calc
    _ = LearningWithErrors.advantage
        (SourceAlignedSuffixRLWEReduction.ringProblem (2 ^ 64) 2047 brkRowCount
          ternarySmallSecretSampler
          (RLWE.OddSecretReduction.oddSecretEmbed (2 ^ 64) 1024)
          (RLWE.OddSecretReduction.pairedErrorSampler (2 ^ 64) 1024 smallErrorSampler))
        (SourceAlignedSuffixRLWEReduction.ringAdversary adversary) :=
      SourceAlignedSuffixRLWEReduction.advantage_eq_ring (2 ^ 64) 2047 brkRowCount
        ternarySmallSecretSampler
        (RLWE.OddSecretReduction.oddSecretEmbed (2 ^ 64) 1024)
        (RLWE.OddSecretReduction.pairedErrorSampler (2 ^ 64) 1024 smallErrorSampler)
        adversary
    _ = _ := RLWE.OddSecretReduction.advantage_eq_smallRLWE (2 ^ 64) 1024 brkRowCount
      (by norm_num) ternarySmallSecretSampler smallErrorSampler
      (SourceAlignedSuffixRLWEReduction.ringAdversary adversary)

/-! ## Complete dense lvl02 view with even binary prefix rows -/

abbrev Prefix := TFHEppCandidateLvl02DenseSecurity.Parameters.Prefix
abbrev View := DenseView Scalar Prefix RingCoordinate Factor

/-- The binary lvl0 coordinate is placed in the even target-ring coefficient with the same
half-ring index. -/
def parityPrefixCoordinate (coordinate : Prefix) : RingCoordinate :=
  parityRingCoordinate 0
    (Fin.cast (by norm_num [prefixDimension]) coordinate)

/-- Exactly the even scalarized-gadget rows pair with the shared binary prefix. -/
def parityKnownPrefixRows (gadget : ScalarGadget) :
    Matrix Prefix Factor Scalar :=
  fun prefixIndex factor ↦ gadget (parityPrefixCoordinate prefixIndex) factor

/-- Candidate public maps for the parity layout. -/
def parityPrefixMaps
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :
    PrefixMaps Scalar Prefix RingCoordinate Factor where
  brk := brkContribution
  ksk := parityKnownPrefixRows

/-- Reuse the exact binary prefix sampler, now paired with the even target-ring coordinates. -/
def prefixSecretSampler : ProbComp (Prefix → Scalar) :=
  TFHEppCandidateLvl02DenseSecurity.Parameters.prefixSecretSampler

/-- Dense prefix-LWE source for either complete correction-error law. -/
noncomputable def parityPrefixProblem
    (correctionSampler : ProbComp (Factor → Scalar)) :=
  SourceAlignedDenseJointLaw.prefixProblem prefixSecretSampler correctionSampler

/-- Complete aligned views for the parity candidate. -/
def parityCandidateViews
    (smallErrorSampler : ProbComp SmallRq)
    (correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :
    AlignedViews View :=
  alignedViews parityGadgetSampler paritySuffixSecretSampler
    (parityBRKErrorSampler smallErrorSampler)
    prefixSecretSampler correctionSampler (parityPrefixMaps brkContribution)

noncomputable def paritySuffixConstructor
    (smallErrorSampler : ProbComp SmallRq)
    (correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  SourceAlignedDenseJointLaw.suffixConstructor
    parityGadgetSampler paritySuffixSecretSampler
    (parityBRKErrorSampler smallErrorSampler)
    prefixSecretSampler correctionSampler (parityPrefixMaps brkContribution)

noncomputable def parityRandomPrefixConstructor
    (smallErrorSampler : ProbComp SmallRq)
    (correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  SourceAlignedDenseJointLaw.randomPrefixConstructor
    parityGadgetSampler paritySuffixSecretSampler
    (parityBRKErrorSampler smallErrorSampler)
    prefixSecretSampler correctionSampler (parityPrefixMaps brkContribution)

noncomputable def paritySecondPrefixConstructor
    (smallErrorSampler : ProbComp SmallRq)
    (correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  SourceAlignedDenseJointLaw.secondPrefixConstructor
    parityGadgetSampler paritySuffixSecretSampler
    (parityBRKErrorSampler smallErrorSampler)
    prefixSecretSampler correctionSampler (parityPrefixMaps brkContribution)

/-- Exact complete-view reduction before discharging any computational assumptions. -/
theorem endpointAdvantage_le_three_sources
    (smallErrorSampler : ProbComp SmallRq)
    (correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) :
    targetAdvantage
        (parityCandidateViews smallErrorSampler correctionSampler
          brkContribution).endpoints distinguisher ≤
      2 * LearningWithErrors.advantage
        (paritySuffixProblem smallErrorSampler)
        ((paritySuffixConstructor smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage
        (parityPrefixProblem correctionSampler)
        ((parityRandomPrefixConstructor smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage
        (parityPrefixProblem correctionSampler)
        ((paritySecondPrefixConstructor smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) := by
  simpa only [parityCandidateViews, paritySuffixConstructor,
    parityRandomPrefixConstructor, paritySecondPrefixConstructor,
    paritySuffixProblem, parityPrefixProblem] using
    (SourceAlignedDenseJointLaw.endpointAdvantage_le_three_sources
      parityGadgetSampler paritySuffixSecretSampler
      (parityBRKErrorSampler smallErrorSampler)
      prefixSecretSampler correctionSampler (parityPrefixMaps brkContribution)
      distinguisher)

/-- Compose the suffix constructor with the exact reduction to ordinary degree-1024 ternary
RLWE. -/
noncomputable def endpointSmallRLWEReduction
    (smallErrorSampler : ProbComp SmallRq)
    (correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.Adversary (smallTernaryRLWEProblem smallErrorSampler) :=
  smallRLWEReduction
    ((paritySuffixConstructor smallErrorSampler correctionSampler
      brkContribution).reduction distinguisher)

/-- Final exact-shape lvl02 theorem.  The former suffix-PRG term is replaced by one conventional
degree-1024 centered-ternary RLWE advantage with `2 * brkRowCount` samples; only the two dense
binary-prefix LWE terms remain separate. -/
theorem endpointAdvantage_le_smallRLWE_and_prefix
    (smallErrorSampler : ProbComp SmallRq)
    (correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) :
    targetAdvantage
        (parityCandidateViews smallErrorSampler correctionSampler
          brkContribution).endpoints distinguisher ≤
      2 * LearningWithErrors.advantage
        (smallTernaryRLWEProblem smallErrorSampler)
        (endpointSmallRLWEReduction smallErrorSampler correctionSampler
          brkContribution distinguisher) +
      2 * LearningWithErrors.advantage
        (parityPrefixProblem correctionSampler)
        ((parityRandomPrefixConstructor smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage
        (parityPrefixProblem correctionSampler)
        ((paritySecondPrefixConstructor smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) := by
  have h := endpointAdvantage_le_three_sources smallErrorSampler correctionSampler
    brkContribution distinguisher
  rw [paritySuffixAdvantage_eq_smallTernaryRLWE] at h
  simpa only [endpointSmallRLWEReduction] using h

/-- A conventional small-ring ternary-RLWE bound and a common bound for the two induced binary
prefix distinguishers give the complete `2 ε_RLWE + 4 ε_prefix` endpoint bound. -/
theorem endpointAdvantage_le_hardness
    (smallErrorSampler : ProbComp SmallRq)
    (correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) (epsilonRLWE epsilonPrefix : ℝ)
    (hRLWE : ∀ adversary : LearningWithErrors.Adversary
        (smallTernaryRLWEProblem smallErrorSampler),
      LearningWithErrors.advantage
        (smallTernaryRLWEProblem smallErrorSampler) adversary ≤ epsilonRLWE)
    (hPrefixFirst : LearningWithErrors.advantage
        (parityPrefixProblem correctionSampler)
        ((parityRandomPrefixConstructor smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) ≤ epsilonPrefix)
    (hPrefixSecond : LearningWithErrors.advantage
        (parityPrefixProblem correctionSampler)
        ((paritySecondPrefixConstructor smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) ≤ epsilonPrefix) :
    targetAdvantage
        (parityCandidateViews smallErrorSampler correctionSampler
          brkContribution).endpoints distinguisher ≤
      2 * epsilonRLWE + 4 * epsilonPrefix := by
  have h := endpointAdvantage_le_smallRLWE_and_prefix smallErrorSampler
    correctionSampler brkContribution distinguisher
  have hSmall := hRLWE (endpointSmallRLWEReduction smallErrorSampler
    correctionSampler brkContribution distinguisher)
  linarith

end

end FormalProof4FHE.TFHE.TFHEppCandidateLvl02ParitySecurity
