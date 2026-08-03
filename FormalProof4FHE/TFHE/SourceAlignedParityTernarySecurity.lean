/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SourceAlignedDenseJointLaw
import FormalProof4FHE.TFHE.SourceAlignedSuffixRLWEReduction

/-!
# Modulus-generic parity-placed ternary source-aligned security

This module factors the exact parity reduction used by the TFHE lvl02 candidate away from a
particular torus modulus and gadget row count.  The target ring has degree `2048`: a binary
degree-`1024` prefix occupies the even coefficients and an independent centered-ternary
degree-`1024` secret occupies the odd coefficients.  For any modulus `q > 1` and any complete
ring-row count, the suffix source is exactly ordinary rank-one ternary RLWE with twice that many
ring samples.  The complete view is bounded by `2 ε_RLWE + 4 ε_prefix`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option linter.unusedSectionVars false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.SourceAlignedParityTernarySecurity

noncomputable section

open DirectSubsetKeyBRK
open DirectSubsetKeyBRK.PublicViewConstructor
open SourceAlignedBRKKSKJointLaw.CompleteView
open SourceAlignedDenseJointLaw

/-- Half of the target degree and the dimension of each secret block. -/
abbrev halfDegree : ℕ := 1024

/-- Degree of the target negacyclic ring. -/
abbrev ringDegree : ℕ := 2048

theorem ringDegree_eq_two_mul_half : ringDegree = 2 * halfDegree := by
  norm_num [ringDegree, halfDegree]

/-- Centered ternary encoding `0, +1, -1` over an arbitrary modulus. -/
def embedTernaryDigit (q : ℕ) (digit : Fin 3) : ZMod q :=
  match digit with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -1

/-- Generic scalar and index types for the complete source-aligned view. -/
abbrev Scalar (q : ℕ) := ZMod q
abbrev Prefix := Fin halfDegree
abbrev RingCoordinate := Fin (1 * (2 * halfDegree))
abbrev Factor (samples : ℕ) := Fin (samples * (2 * halfDegree))
abbrev RingGadget (q samples : ℕ) :=
  SourceAlignedSuffixRLWEReduction.RingChallenge q 2047 samples
abbrev ScalarGadget (q samples : ℕ) :=
  SourceAlignedSuffixRLWEReduction.ScalarChallenge q 2047 samples
abbrev SmallRq (q : ℕ) := RLWE.Rq q halfDegree
abbrev View (q samples : ℕ) :=
  DenseView (Scalar q) Prefix RingCoordinate (Factor samples)

variable (q samples : ℕ) [NeZero q] [Fact (1 < q)]

/-! ## Exact parity secret and error samplers -/

/-- Turn `1024` centered-ternary digits into one small-ring element. -/
def ternarySmallRq (digits : Fin halfDegree → Fin 3) : SmallRq q :=
  (TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q halfDegree).symm
    (fun coordinate ↦ embedTernaryDigit q (digits coordinate))

/-- Rank-one explicit secret corresponding to the small ternary ring element. -/
def ternarySmallSecret (digits : Fin halfDegree → Fin 3) :
    RLWE.Secret q halfDegree :=
  fun _ ↦ ternarySmallRq q digits

/-- Exact coefficientwise centered-ternary small-ring secret sampler. -/
def ternarySmallSecretSampler : ProbComp (RLWE.Secret q halfDegree) :=
  ternarySmallSecret q <$> ($ᵗ (Fin halfDegree → Fin 3))

/-- Place the small-ring ternary secret in the odd target-ring coefficients and expose its
complete scalar coefficient vector. -/
def embedTernaryParity (digits : Fin halfDegree → Fin 3) :
    RingCoordinate → Scalar q :=
  SourceAlignedSuffixRLWEReduction.bodyCoefficientEquiv q 2047 1
    (RLWE.OddSecretReduction.oddSecretEmbed q halfDegree
      (ternarySmallSecret q digits))

/-- Address an even or odd target-ring coefficient in the rank-one flattened scalar secret. -/
def parityRingCoordinate (branch : Fin 2) (coordinate : Fin halfDegree) :
    RingCoordinate :=
  finProdFinEquiv
    (0, RLWE.EvenOddDecomposition.parityIndexEquiv halfDegree
      (branch, coordinate))

/-- Exact odd-coordinate centered-ternary suffix sampler. -/
def paritySuffixSecretSampler : ProbComp (RingCoordinate → Scalar q) :=
  (fun secret ↦
    SourceAlignedSuffixRLWEReduction.bodyCoefficientEquiv q 2047 1
      (RLWE.OddSecretReduction.oddSecretEmbed q halfDegree secret)) <$>
    ternarySmallSecretSampler q

/-- The factored sampler is exactly direct coefficientwise parity embedding. -/
theorem paritySuffixSecretSampler_eq_coefficientwise :
    paritySuffixSecretSampler q =
      embedTernaryParity q <$> ($ᵗ (Fin halfDegree → Fin 3)) := by
  simp only [paritySuffixSecretSampler, ternarySmallSecretSampler,
    Functor.map_map]
  congr 1

/-- A target-ring error consists of independent even and odd small-ring errors. -/
def parityBRKErrorSampler (smallErrorSampler : ProbComp (SmallRq q)) :
    ProbComp (Factor samples → Scalar q) :=
  SourceAlignedSuffixRLWEReduction.bodyCoefficientEquiv q 2047 samples <$>
    ProbComp.sampleIID samples
      (RLWE.OddSecretReduction.pairedErrorSampler q halfDegree smallErrorSampler)

/-- Scalar challenge induced from all rank-one target-ring masks. -/
def parityGadgetSampler : ProbComp (ScalarGadget q samples) :=
  SourceAlignedSuffixRLWEReduction.scalarizeChallenge <$>
    ($ᵗ (RingGadget q samples))

/-- Complete source-aligned scalar suffix problem for the parity layout. -/
noncomputable def paritySuffixProblem (smallErrorSampler : ProbComp (SmallRq q)) :=
  suffixProblem (parityGadgetSampler q samples)
    (paritySuffixSecretSampler q)
    (parityBRKErrorSampler q samples smallErrorSampler)

/-- The explicit sampler presentation is the generic scalarization of the odd-secret ring
problem. -/
theorem paritySuffixProblem_eq_scalarProblem
    (smallErrorSampler : ProbComp (SmallRq q)) :
    paritySuffixProblem q samples smallErrorSampler =
      SourceAlignedSuffixRLWEReduction.scalarProblem q 2047 samples
        (ternarySmallSecretSampler q)
        (RLWE.OddSecretReduction.oddSecretEmbed q halfDegree)
        (RLWE.OddSecretReduction.pairedErrorSampler q halfDegree
          smallErrorSampler) := by
  rfl

/-! ## Direct reduction to ordinary ternary RLWE -/

/-- Conventional small-ring ternary RLWE problem with twice the target ring-row count. -/
noncomputable def smallTernaryRLWEProblem
    (smallErrorSampler : ProbComp (SmallRq q)) :=
  RLWE.problem q halfDegree (2 * samples)
    (ternarySmallSecretSampler q) smallErrorSampler

/-- Compose exact scalar-to-ring transport with exact odd-secret reduction. -/
noncomputable def smallRLWEReduction
    {smallErrorSampler : ProbComp (SmallRq q)}
    (adversary : LearningWithErrors.Adversary
      (paritySuffixProblem q samples smallErrorSampler)) :
    LearningWithErrors.Adversary
      (smallTernaryRLWEProblem q samples smallErrorSampler) :=
  RLWE.OddSecretReduction.reduction (q := q) (half := halfDegree)
    (samples := samples) (by norm_num [halfDegree])
    (SourceAlignedSuffixRLWEReduction.ringAdversary adversary)

/-- Exact suffix theorem at arbitrary modulus and row count. -/
theorem paritySuffixAdvantage_eq_smallTernaryRLWE
    (smallErrorSampler : ProbComp (SmallRq q))
    (adversary : LearningWithErrors.Adversary
      (paritySuffixProblem q samples smallErrorSampler)) :
    LearningWithErrors.advantage
        (paritySuffixProblem q samples smallErrorSampler) adversary =
      LearningWithErrors.advantage
        (smallTernaryRLWEProblem q samples smallErrorSampler)
        (smallRLWEReduction q samples adversary) := by
  calc
    _ = LearningWithErrors.advantage
        (SourceAlignedSuffixRLWEReduction.ringProblem q 2047 samples
          (ternarySmallSecretSampler q)
          (RLWE.OddSecretReduction.oddSecretEmbed q halfDegree)
          (RLWE.OddSecretReduction.pairedErrorSampler q halfDegree
            smallErrorSampler))
        (SourceAlignedSuffixRLWEReduction.ringAdversary adversary) :=
      SourceAlignedSuffixRLWEReduction.advantage_eq_ring q 2047 samples
        (ternarySmallSecretSampler q)
        (RLWE.OddSecretReduction.oddSecretEmbed q halfDegree)
        (RLWE.OddSecretReduction.pairedErrorSampler q halfDegree
          smallErrorSampler) adversary
    _ = _ := RLWE.OddSecretReduction.advantage_eq_smallRLWE
      q halfDegree samples (by norm_num [halfDegree])
      (ternarySmallSecretSampler q) smallErrorSampler
      (SourceAlignedSuffixRLWEReduction.ringAdversary adversary)

/-! ## Complete dense view with even binary prefix rows -/

/-- Embed an exact binary prefix into the modulus. -/
def embedBinaryPrefix (secret : Prefix → Bool) : Prefix → Scalar q :=
  fun coordinate ↦ if secret coordinate then 1 else 0

/-- Exact binary prefix-secret sampler. -/
def prefixSecretSampler : ProbComp (Prefix → Scalar q) :=
  embedBinaryPrefix q <$> ($ᵗ (Prefix → Bool))

/-- The binary prefix coordinate is placed at the corresponding even target-ring position. -/
def parityPrefixCoordinate (coordinate : Prefix) : RingCoordinate :=
  parityRingCoordinate 0 coordinate

/-- Exactly the even scalarized-gadget rows pair with the shared binary prefix. -/
def parityKnownPrefixRows (gadget : ScalarGadget q samples) :
    Matrix Prefix (Factor samples) (Scalar q) :=
  fun prefixIndex factor ↦ gadget (parityPrefixCoordinate prefixIndex) factor

/-- Candidate public maps for the parity layout. -/
def parityPrefixMaps
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q)) :
    PrefixMaps (Scalar q) Prefix RingCoordinate (Factor samples) where
  brk := brkContribution
  ksk := parityKnownPrefixRows q samples

/-- Dense prefix-LWE source for the correction-error law. -/
noncomputable def parityPrefixProblem
    (correctionSampler : ProbComp (Factor samples → Scalar q)) :=
  SourceAlignedDenseJointLaw.prefixProblem
    (prefixSecretSampler q) correctionSampler

/-- Complete aligned views for the generic parity candidate. -/
def parityCandidateViews
    (smallErrorSampler : ProbComp (SmallRq q))
    (correctionSampler : ProbComp (Factor samples → Scalar q))
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q)) :
    AlignedViews (View q samples) :=
  alignedViews (parityGadgetSampler q samples)
    (paritySuffixSecretSampler q)
    (parityBRKErrorSampler q samples smallErrorSampler)
    (prefixSecretSampler q) correctionSampler
    (parityPrefixMaps q samples brkContribution)

noncomputable def paritySuffixConstructor
    (smallErrorSampler : ProbComp (SmallRq q))
    (correctionSampler : ProbComp (Factor samples → Scalar q))
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q)) :=
  SourceAlignedDenseJointLaw.suffixConstructor
    (parityGadgetSampler q samples) (paritySuffixSecretSampler q)
    (parityBRKErrorSampler q samples smallErrorSampler)
    (prefixSecretSampler q) correctionSampler
    (parityPrefixMaps q samples brkContribution)

noncomputable def parityRandomPrefixConstructor
    (smallErrorSampler : ProbComp (SmallRq q))
    (correctionSampler : ProbComp (Factor samples → Scalar q))
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q)) :=
  SourceAlignedDenseJointLaw.randomPrefixConstructor
    (parityGadgetSampler q samples) (paritySuffixSecretSampler q)
    (parityBRKErrorSampler q samples smallErrorSampler)
    (prefixSecretSampler q) correctionSampler
    (parityPrefixMaps q samples brkContribution)

noncomputable def paritySecondPrefixConstructor
    (smallErrorSampler : ProbComp (SmallRq q))
    (correctionSampler : ProbComp (Factor samples → Scalar q))
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q)) :=
  SourceAlignedDenseJointLaw.secondPrefixConstructor
    (parityGadgetSampler q samples) (paritySuffixSecretSampler q)
    (parityBRKErrorSampler q samples smallErrorSampler)
    (prefixSecretSampler q) correctionSampler
    (parityPrefixMaps q samples brkContribution)

/-- Exact complete-view reduction before computational assumptions. -/
theorem endpointAdvantage_le_three_sources
    (smallErrorSampler : ProbComp (SmallRq q))
    (correctionSampler : ProbComp (Factor samples → Scalar q))
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q))
    (distinguisher : Distinguisher (View q samples)) :
    targetAdvantage
        (parityCandidateViews q samples smallErrorSampler correctionSampler
          brkContribution).endpoints distinguisher ≤
      2 * LearningWithErrors.advantage
        (paritySuffixProblem q samples smallErrorSampler)
        ((paritySuffixConstructor q samples smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage
        (parityPrefixProblem q samples correctionSampler)
        ((parityRandomPrefixConstructor q samples smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage
        (parityPrefixProblem q samples correctionSampler)
        ((paritySecondPrefixConstructor q samples smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) := by
  unfold parityCandidateViews paritySuffixConstructor
    parityRandomPrefixConstructor paritySecondPrefixConstructor
    paritySuffixProblem parityPrefixProblem
  convert SourceAlignedDenseJointLaw.endpointAdvantage_le_three_sources
    (parityGadgetSampler q samples) (paritySuffixSecretSampler q)
    (parityBRKErrorSampler q samples smallErrorSampler)
    (prefixSecretSampler q) correctionSampler
    (parityPrefixMaps q samples brkContribution) distinguisher using 1

/-- Compose the suffix constructor with the exact ordinary-RLWE reduction. -/
noncomputable def endpointSmallRLWEReduction
    (smallErrorSampler : ProbComp (SmallRq q))
    (correctionSampler : ProbComp (Factor samples → Scalar q))
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q))
    (distinguisher : Distinguisher (View q samples)) :
    LearningWithErrors.Adversary
      (smallTernaryRLWEProblem q samples smallErrorSampler) :=
  smallRLWEReduction q samples
    ((paritySuffixConstructor q samples smallErrorSampler correctionSampler
      brkContribution).reduction distinguisher)

/-- Final generic exact-shape parity theorem. -/
theorem endpointAdvantage_le_smallRLWE_and_prefix
    (smallErrorSampler : ProbComp (SmallRq q))
    (correctionSampler : ProbComp (Factor samples → Scalar q))
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q))
    (distinguisher : Distinguisher (View q samples)) :
    targetAdvantage
        (parityCandidateViews q samples smallErrorSampler correctionSampler
          brkContribution).endpoints distinguisher ≤
      2 * LearningWithErrors.advantage
        (smallTernaryRLWEProblem q samples smallErrorSampler)
        (endpointSmallRLWEReduction q samples smallErrorSampler correctionSampler
          brkContribution distinguisher) +
      2 * LearningWithErrors.advantage
        (parityPrefixProblem q samples correctionSampler)
        ((parityRandomPrefixConstructor q samples smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage
        (parityPrefixProblem q samples correctionSampler)
        ((paritySecondPrefixConstructor q samples smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) := by
  have h := endpointAdvantage_le_three_sources q samples smallErrorSampler
    correctionSampler brkContribution distinguisher
  rw [paritySuffixAdvantage_eq_smallTernaryRLWE] at h
  simpa only [endpointSmallRLWEReduction] using h

/-- A ternary-RLWE bound and a common binary-prefix LWE bound give
`2 ε_RLWE + 4 ε_prefix`. -/
theorem endpointAdvantage_le_hardness
    (smallErrorSampler : ProbComp (SmallRq q))
    (correctionSampler : ProbComp (Factor samples → Scalar q))
    (brkContribution : ScalarGadget q samples →
      Matrix Prefix (Factor samples) (Scalar q))
    (distinguisher : Distinguisher (View q samples))
    (epsilonRLWE epsilonPrefix : ℝ)
    (hRLWE : ∀ adversary : LearningWithErrors.Adversary
        (smallTernaryRLWEProblem q samples smallErrorSampler),
      LearningWithErrors.advantage
        (smallTernaryRLWEProblem q samples smallErrorSampler) adversary ≤ epsilonRLWE)
    (hPrefixFirst : LearningWithErrors.advantage
        (parityPrefixProblem q samples correctionSampler)
        ((parityRandomPrefixConstructor q samples smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) ≤ epsilonPrefix)
    (hPrefixSecond : LearningWithErrors.advantage
        (parityPrefixProblem q samples correctionSampler)
        ((paritySecondPrefixConstructor q samples smallErrorSampler correctionSampler
          brkContribution).reduction distinguisher) ≤ epsilonPrefix) :
    targetAdvantage
        (parityCandidateViews q samples smallErrorSampler correctionSampler
          brkContribution).endpoints distinguisher ≤
      2 * epsilonRLWE + 4 * epsilonPrefix := by
  have h := endpointAdvantage_le_smallRLWE_and_prefix q samples
    smallErrorSampler correctionSampler brkContribution distinguisher
  have hSmall := hRLWE
    (endpointSmallRLWEReduction q samples smallErrorSampler correctionSampler
      brkContribution distinguisher)
  linarith

end

end FormalProof4FHE.TFHE.SourceAlignedParityTernarySecurity
