/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SourceAlignedDenseJointLaw
import FormalProof4FHE.TFHE.SourceAlignedGadgetConstruction

/-!
# Dense Source-Aligned Security for the Balanced TFHEpp lvl02 Candidate

This file specializes the exact dense BRK/KSK joint-law theorem to the experimental balanced
`lvl02` shape.  The prefix has 1024 binary coefficients.  The target ring has 2048 coefficients;
the first 1024 are the known binary prefix and the remaining 1024 are sampled independently
from the centered ternary alphabet.  A uniform rank-one ring-mask matrix is scalarized to the
complete aligned width.

The two finite error samplers and the public BRK prefix-contribution matrix remain parameters.
Consequently the result identifies the exact three computational source problems required by
the candidate; it does not assert their hardness or identify an executable C++ Gaussian sampler
with an analytic distribution certificate.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TFHEppCandidateLvl02DenseSecurity

noncomputable section

open DirectSubsetKeyBRK
open DirectSubsetKeyBRK.PublicViewConstructor
open SourceAlignedBRKKSKJointLaw.CompleteView
open SourceAlignedDenseJointLaw

namespace Parameters

open TFHEppSourceAlignedParameterScreen.CandidateLvl02

/-- Native 64-bit torus modulus used by the candidate. -/
def modulus : ℕ := 2 ^ 64

instance modulus_neZero : NeZero modulus := ⟨by norm_num [modulus]⟩

abbrev Scalar := ZMod (2 ^ 64)
abbrev Prefix := Fin prefixDimension
abbrev RingCoordinate := Fin 2048
abbrev Factor := Fin (brkRowCount * 2048)
abbrev RingGadget := Matrix (Fin 1) (Fin brkRowCount) (RLWE.Rq (2 ^ 64) 2048)
abbrev ScalarGadget := Matrix RingCoordinate Factor Scalar
abbrev View := DenseView Scalar Prefix RingCoordinate Factor

/-- The chosen prefix and suffix fill the complete rank-one target ring. -/
theorem splitDimension_eq :
    prefixDimension + suffixDimension = 2048 := by
  norm_num [prefixDimension, suffixDimension, ringRank, ringDegree]

/-- The formal dense factor index expression is exactly the selected aligned width. -/
theorem factorWidth_eq_alignedWidth : brkRowCount * 2048 = alignedWidth := by
  rfl

/-- The scalarized structured challenge retains every target-ring coordinate. -/
theorem ringCoordinate_card_eq_ringDegree :
    Fintype.card RingCoordinate = ringDegree := by
  norm_num [ringDegree]

/-- Centered ternary encoding `0, +1, -1` into the torus coefficient ring. -/
def embedTernaryDigit (digit : Fin 3) : Scalar :=
  match digit with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -1

/-- Embed a binary prefix key coefficientwise. -/
def embedBinaryPrefix (secret : Prefix → Bool) : Prefix → Scalar :=
  fun coordinate ↦ if secret coordinate then 1 else 0

/-- Embed an independently sampled ternary suffix into the full ring-coordinate space, with
the prefix coordinates fixed to zero. -/
def embedTernarySuffix (secret : Fin suffixDimension → Fin 3) :
    RingCoordinate → Scalar :=
  fun coordinate ↦
    Fin.addCases (fun _prefix ↦ 0)
      (fun suffix ↦ embedTernaryDigit (secret suffix))
      (Fin.cast splitDimension_eq.symm coordinate)

/-- Exact binary prefix-secret sampler used by both dense prefix-LWE sources. -/
def prefixSecretSampler : ProbComp (Prefix → Scalar) :=
  embedBinaryPrefix <$> ($ᵗ (Prefix → Bool))

/-- Exact coefficientwise centered-ternary suffix-subspace sampler. -/
def suffixSecretSampler : ProbComp (RingCoordinate → Scalar) :=
  embedTernarySuffix <$> ($ᵗ (Fin suffixDimension → Fin 3))

/-- Coefficient scalarization of all rank-one ring masks. -/
noncomputable def scalarizeRingGadget (gadget : RingGadget) : ScalarGadget := by
  exact SourceAlignedFactorPropagation.Extraction.inducedScalarGadget
    (degree := 2047) gadget

/-- The structured suffix challenge mask is the scalar image of one genuinely uniform ring-mask
matrix, rather than a uniformly sampled scalar matrix. -/
def gadgetSampler : ProbComp ScalarGadget :=
  scalarizeRingGadget <$> ($ᵗ RingGadget)

/-- Embed one prefix coordinate into the leading coordinates of the full ring key. -/
def prefixCoordinate (coordinate : Prefix) : RingCoordinate :=
  ⟨coordinate.val, by
    have h := coordinate.isLt
    norm_num [prefixDimension] at h ⊢
    omega⟩

/-- Rows of the scalarized ring gadget paired with the shared binary prefix. -/
def knownPrefixRows (gadget : ScalarGadget) : Matrix Prefix Factor Scalar :=
  fun prefixIndex factor ↦ gadget (prefixCoordinate prefixIndex) factor

/-- Candidate public maps.  `brkContribution` contains the complete known-prefix contribution
to the BRK body (including the BRK plaintext term); the aligned-KSK map is fixed to the leading
rows of the scalarized ring gadget. -/
def prefixMaps
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :
    PrefixMaps Scalar Prefix RingCoordinate Factor where
  brk := brkContribution
  ksk := knownPrefixRows

end Parameters

open Parameters

/-! ## Candidate source problems, views, and exact constructors -/

noncomputable def candidateSuffixProblem
    (brkErrorSampler : ProbComp (Factor → Scalar)) :=
  suffixProblem gadgetSampler suffixSecretSampler brkErrorSampler

noncomputable def candidatePrefixProblem
    (correctionSampler : ProbComp (Factor → Scalar)) :=
  SourceAlignedDenseJointLaw.prefixProblem prefixSecretSampler correctionSampler

def candidateViews
    (brkErrorSampler correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :
    AlignedViews View :=
  alignedViews gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
    correctionSampler (prefixMaps brkContribution)

noncomputable def candidateSuffixConstructor
    (brkErrorSampler correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  suffixConstructor gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
    correctionSampler (prefixMaps brkContribution)

noncomputable def candidateRandomPrefixConstructor
    (brkErrorSampler correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  randomPrefixConstructor gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
    correctionSampler (prefixMaps brkContribution)

noncomputable def candidateSecondPrefixConstructor
    (brkErrorSampler correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar) :=
  secondPrefixConstructor gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
    correctionSampler (prefixMaps brkContribution)

/-! ## Exact lvl02 reduction statements -/

/-- Exact complete-view reduction for the balanced candidate.  The suffix term is the structured
ring-mask problem under the zero-prefix/ternary-suffix secret sampler; both prefix terms are
dense binary-secret LWE at the complete aligned width. -/
theorem endpointAdvantage_le_three_sources
    (brkErrorSampler correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) :
    targetAdvantage
        (candidateViews brkErrorSampler correctionSampler brkContribution).endpoints
        distinguisher ≤
      2 * LearningWithErrors.advantage (candidateSuffixProblem brkErrorSampler)
        ((candidateSuffixConstructor brkErrorSampler correctionSampler
          brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage (candidatePrefixProblem correctionSampler)
        ((candidateRandomPrefixConstructor brkErrorSampler correctionSampler
          brkContribution).reduction distinguisher) +
      2 * LearningWithErrors.advantage (candidatePrefixProblem correctionSampler)
        ((candidateSecondPrefixConstructor brkErrorSampler correctionSampler
          brkContribution).reduction distinguisher) := by
  simpa only [candidateViews, candidateSuffixProblem, candidatePrefixProblem,
    candidateSuffixConstructor, candidateRandomPrefixConstructor,
    candidateSecondPrefixConstructor] using
    (SourceAlignedDenseJointLaw.endpointAdvantage_le_three_sources
      gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler correctionSampler
      (prefixMaps brkContribution) distinguisher)

/-- If the concrete structured suffix problem is bounded by `epsilonSuffix` and both induced
dense prefix reductions are bounded by the common value `epsilonPrefix`, the complete candidate
view has the advertised `2 ε_Z + 4 ε_P` loss. -/
theorem endpointAdvantage_le_hardness
    (brkErrorSampler correctionSampler : ProbComp (Factor → Scalar))
    (brkContribution : ScalarGadget → Matrix Prefix Factor Scalar)
    (distinguisher : Distinguisher View) (epsilonSuffix epsilonPrefix : ℝ)
    (hSuffix : LearningWithErrors.advantage (candidateSuffixProblem brkErrorSampler)
      ((candidateSuffixConstructor brkErrorSampler correctionSampler
        brkContribution).reduction distinguisher) ≤ epsilonSuffix)
    (hPrefixFirst : LearningWithErrors.advantage (candidatePrefixProblem correctionSampler)
      ((candidateRandomPrefixConstructor brkErrorSampler correctionSampler
        brkContribution).reduction distinguisher) ≤ epsilonPrefix)
    (hPrefixSecond : LearningWithErrors.advantage (candidatePrefixProblem correctionSampler)
      ((candidateSecondPrefixConstructor brkErrorSampler correctionSampler
        brkContribution).reduction distinguisher) ≤ epsilonPrefix) :
    targetAdvantage
        (candidateViews brkErrorSampler correctionSampler brkContribution).endpoints
        distinguisher ≤ 2 * epsilonSuffix + 4 * epsilonPrefix := by
  have h := endpointAdvantage_le_three_sources brkErrorSampler correctionSampler
    brkContribution distinguisher
  linarith

end

end FormalProof4FHE.TFHE.TFHEppCandidateLvl02DenseSecurity
