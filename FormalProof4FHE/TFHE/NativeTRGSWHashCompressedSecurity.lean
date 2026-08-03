/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWQuadraticKDMAndTFHET
import FormalProof4FHE.TFHE.JointSubsetKeyBRKRefined
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleSecretRandomization

/-!
# Hash-compressed and block-cycle alternatives to the full-prefix loss

This module formalizes the mathematical claims in `sketch/tthpowerof2.md`.

The existing complete-view match-and-square proof pays the order-`1/2` Renyi concentration of
the leakage supplied to its public builder.  This file proves that, conditioned on any fixed
public hash whose output on a uniform prefix is uniform, leaking only an `r`-bit digest changes
that concentration to exactly `2 ^ r`.  The resulting native bound is

`sigmaPlus + sigmaMinus + sqrt (2 ^ (r + 1) * sourceBound)`.

The builder is typed to receive only the digest and the public source view.  Its diagonal
correctness and its source-game bound remain explicit theorem premises: the file does not assert
the existence of the proposed hash-lossy dual mode.  A composition theorem adds the two mode
switches and the final sampler error.

For the alternative scheme redesign, a telescoping theorem proves the block-cycle bounds and an
exact source-budget lemma replaces the logarithmic heuristic by the equivalent algebraic
condition involving the square of the number of blocks.  The final section exposes the exact
vector-LWE XOR transport already implemented by the scalar-secret randomization machinery and
records the existing native-ring obstruction.

Finally, the translation-only barrier is specialized to hash leakage: at cutoff at most `t - 2`,
no uniform `r`-bit hash with `r < t` can support an exact phase-oblivious aggregate builder.  Thus
hash compression really does require the nonlinear/dual-mode premise isolated above.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWHashCompressedSecurity

noncomputable section

open NativeTRGSWAggregateProjectedLeakage
open NativeTRGSWAggregateSecurityAndComplexityLeveraging
open NativeTRGSWBarrierAndSpectralBoundary
open RGSWCoefficientCircularSecurity

/-! ## Uniform-output public hashes -/

/-- A fixed public hash has uniform output when it sends a uniform prefix exactly to the uniform
digest law.  Full-rank linear hashes over `F₂` satisfy this property; stating the property itself
also permits other balanced public hash families. -/
def HasUniformOutput
    {Prefix Digest : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Digest] [SampleableType Digest]
    (hash : Prefix → Digest) : Prop :=
  evalDist (hash <$> ($ᵗ Prefix)) = evalDist ($ᵗ Digest)

/-- In finite additive groups, surjectivity is the full-rank condition needed for uniform hash
output. -/
theorem hasUniformOutput_of_surjectiveAddHom
    {Prefix Digest : Type}
    [AddGroup Prefix] [Fintype Prefix] [SampleableType Prefix]
    [AddGroup Digest] [Fintype Digest] [DecidableEq Digest]
    [SampleableType Digest]
    (hash : Prefix →+ Digest) (hsurjective : Function.Surjective hash) :
    HasUniformOutput hash := by
  exact JointSubsetKeyBRKRefined.evalDist_map_surjective_addHom_uniform
    hash hsurjective

/-- Binary vector spaces used to represent full-rank linear hashes over `F₂`. -/
abbrev F2Word (count : ℕ) := Fin count → ZMod 2

/-- A surjective `F₂`-linear map is a balanced public hash.  For finite-dimensional binary vector
spaces, surjectivity is equivalent to having output rank `r`. -/
theorem hasUniformOutput_of_surjectiveF2LinearHash
    {prefixCount digestCount : ℕ}
    (hash : F2Word prefixCount →ₗ[ZMod 2] F2Word digestCount)
    (hsurjective : Function.Surjective hash) :
    HasUniformOutput hash := by
  have hsurjective' : Function.Surjective hash.toAddHom := by
    intro output
    obtain ⟨input, hinput⟩ := hsurjective output
    exact ⟨input, hinput⟩
  unfold HasUniformOutput
  change evalDist
      ((hash.toAddHom : F2Word prefixCount → F2Word digestCount) <$>
        ($ᵗ (F2Word prefixCount))) =
    evalDist ($ᵗ (F2Word digestCount))
  exact hasUniformOutput_of_surjectiveAddHom
    (Prefix := F2Word prefixCount) (Digest := F2Word digestCount)
    hash.toAddHom hsurjective'

/-- Leak only the hash of the prefix; the independent suffix is not exposed. -/
def hashedPrefixLeakage
    {Prefix Suffix Digest : Type} (hash : Prefix → Digest) :
    Prefix × Suffix → Digest :=
  fun key ↦ hash key.1

/-- Conditioned on a fixed balanced public hash, the hashed prefix of a uniform product key is
uniform even though the suffix remains part of the hidden complete key. -/
theorem hashedPrefixLeakage_uniform_evalDist
    {Prefix Suffix Digest : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    [Fintype Digest] [SampleableType Digest]
    (hash : Prefix → Digest) (huniform : HasUniformOutput hash) :
    evalDist
        (leakageLaw ($ᵗ (Prefix × Suffix))
          (hashedPrefixLeakage (Suffix := Suffix) hash)) =
      evalDist ($ᵗ Digest) := by
  have hprefix :
      evalDist (Prod.fst <$> ($ᵗ (Prefix × Suffix))) =
        evalDist ($ᵗ Prefix) :=
    evalDist_map_fst_uniformSample_prod
  have hmapped := evalDist_map_eq_of_evalDist_eq hprefix hash
  change evalDist ((fun key : Prefix × Suffix ↦ hash key.1) <$>
      ($ᵗ (Prefix × Suffix))) = evalDist ($ᵗ Digest)
  simpa [Functor.map_map] using hmapped.trans huniform

/-- The projected match-and-square concentration is exactly the digest carrier size. -/
theorem hashedPrefixConcentration_eq_card
    {Prefix Suffix Digest : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    [Fintype Digest] [Nonempty Digest] [SampleableType Digest]
    (hash : Prefix → Digest) (huniform : HasUniformOutput hash) :
    projectedLeakageConcentration
        ($ᵗ (Prefix × Suffix))
        (hashedPrefixLeakage (Suffix := Suffix) hash) =
      Fintype.card Digest := by
  unfold projectedLeakageConcentration
  rw [halfRenyiConcentration_eq_of_evalDist_eq
    (leakageLaw ($ᵗ (Prefix × Suffix))
      (hashedPrefixLeakage (Suffix := Suffix) hash))
    ($ᵗ Digest)
    (hashedPrefixLeakage_uniform_evalDist hash huniform),
    halfRenyiConcentration_uniform]

/-- A balanced `r`-bit hash has exact Renyi-half concentration `2 ^ r`, independently of the
complete prefix length and suffix carrier. -/
theorem hashedBinaryPrefixConcentration_eq_twoPow
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ) (hash : Prefix → (Fin digestCount → Bool))
    (huniform : HasUniformOutput hash) :
    projectedLeakageConcentration
        ($ᵗ (Prefix × Suffix))
        (hashedPrefixLeakage (Suffix := Suffix) hash) =
      (2 : ℝ) ^ digestCount := by
  rw [hashedPrefixConcentration_eq_card hash huniform]
  simp

/-! ## A builder that cannot inspect the complete prefix -/

/-- Run a public builder after sampling its public source view.  The type enforces that the
builder receives the branch bit, the digest, and the public view, but not the complete key.  The
key appears only as an index of the source channel. -/
def hashOnlyExperiment
    {Key Digest SourceView : Type}
    (builder : Bool → Digest → SourceView → ProbComp Bool)
    (source : Bool → Key → ProbComp SourceView)
    (branch : Bool) (digest : Digest) (key : Key) : ProbComp Bool := do
  let view ← source branch key
  builder branch digest view

/-- Exact square-root coefficient associated with an `r`-bit digest.  This is the formal
real-number expression for `2 ^ ((r + 1) / 2)` without introducing rounding through natural
division. -/
def binaryHashSquareRootLoss (digestCount : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ (digestCount + 1))

theorem binaryHashSquareRootLoss_nonneg (digestCount : ℕ) :
    0 ≤ binaryHashSquareRootLoss digestCount :=
  Real.sqrt_nonneg _

theorem binaryHashSquareRootLoss_sq (digestCount : ℕ) :
    binaryHashSquareRootLoss digestCount ^ 2 =
      (2 : ℝ) ^ (digestCount + 1) := by
  unfold binaryHashSquareRootLoss
  rw [Real.sq_sqrt]
  positivity

/-- Hash-compressed match-and-square theorem.  `hdiagonal` is the complete-view correctness
obligation for the proposed builder and `hsource` is its doubled public-source security bound.
Neither is silently postulated by this module. -/
theorem hashOnlyNativeGap_le
    {Prefix Suffix SourceView : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ)
    (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (fakeDigestSampler : ProbComp (Fin digestCount → Bool))
    (builder : Bool → (Fin digestCount → Bool) → SourceView → ProbComp Bool)
    (source : Bool → Prefix × Suffix → ProbComp SourceView)
    (nativeGap sigmaPlus sigmaMinus sourceBound : ℝ)
    (hdiagonal : nativeGap ≤ sigmaPlus + sigmaMinus +
      projectedAggregateAdvantage
        ($ᵗ (Prefix × Suffix))
        (hashedPrefixLeakage (Suffix := Suffix) hash)
        (hashOnlyExperiment builder source true)
        (hashOnlyExperiment builder source false))
    (hsource : projectedMatchSquareAdvantage
        ($ᵗ (Prefix × Suffix)) fakeDigestSampler
        (hashOnlyExperiment builder source true)
        (hashOnlyExperiment builder source false) ≤ sourceBound)
    (hcover : ∀ key,
      probabilityMass ($ᵗ (Prefix × Suffix)) key ≠ 0 →
        probabilityMass fakeDigestSampler
          (hashedPrefixLeakage (Suffix := Suffix) hash key) ≠ 0)
    (hoptimized : ∀ digest,
      probabilityMass fakeDigestSampler digest =
        Real.sqrt
            (probabilityMass
              (leakageLaw ($ᵗ (Prefix × Suffix))
                (hashedPrefixLeakage (Suffix := Suffix) hash)) digest) /
          halfRenyiNormalizer
            ($ᵗ (Prefix × Suffix))
            (hashedPrefixLeakage (Suffix := Suffix) hash)) :
    nativeGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * sourceBound) := by
  have hbound := nativeProjectedAggregateGap_le_defects_add_sqrt
    ($ᵗ (Prefix × Suffix)) fakeDigestSampler
    (hashedPrefixLeakage (Suffix := Suffix) hash)
    (hashOnlyExperiment builder source true)
    (hashOnlyExperiment builder source false)
    nativeGap sigmaPlus sigmaMinus sourceBound
    hdiagonal hsource hcover hoptimized
  rw [hashedBinaryPrefixConcentration_eq_twoPow
    digestCount hash huniformHash] at hbound
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- Equivalent coefficient form of the hash-compressed theorem. -/
theorem hashOnlyNativeGap_le_squareRootLoss
    {Prefix Suffix SourceView : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ)
    (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (fakeDigestSampler : ProbComp (Fin digestCount → Bool))
    (builder : Bool → (Fin digestCount → Bool) → SourceView → ProbComp Bool)
    (source : Bool → Prefix × Suffix → ProbComp SourceView)
    (nativeGap sigmaPlus sigmaMinus sourceBound : ℝ)
    (hdiagonal : nativeGap ≤ sigmaPlus + sigmaMinus +
      projectedAggregateAdvantage
        ($ᵗ (Prefix × Suffix))
        (hashedPrefixLeakage (Suffix := Suffix) hash)
        (hashOnlyExperiment builder source true)
        (hashOnlyExperiment builder source false))
    (hsource : projectedMatchSquareAdvantage
        ($ᵗ (Prefix × Suffix)) fakeDigestSampler
        (hashOnlyExperiment builder source true)
        (hashOnlyExperiment builder source false) ≤ sourceBound)
    (hcover : ∀ key,
      probabilityMass ($ᵗ (Prefix × Suffix)) key ≠ 0 →
        probabilityMass fakeDigestSampler
          (hashedPrefixLeakage (Suffix := Suffix) hash key) ≠ 0)
    (hoptimized : ∀ digest,
      probabilityMass fakeDigestSampler digest =
        Real.sqrt
            (probabilityMass
              (leakageLaw ($ᵗ (Prefix × Suffix))
                (hashedPrefixLeakage (Suffix := Suffix) hash)) digest) /
          halfRenyiNormalizer
            ($ᵗ (Prefix × Suffix))
            (hashedPrefixLeakage (Suffix := Suffix) hash)) :
    nativeGap ≤ sigmaPlus + sigmaMinus +
      binaryHashSquareRootLoss digestCount * Real.sqrt sourceBound := by
  have hbound := hashOnlyNativeGap_le
    digestCount hash huniformHash fakeDigestSampler builder source
    nativeGap sigmaPlus sigmaMinus sourceBound
    hdiagonal hsource hcover hoptimized
  rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ (digestCount + 1))] at hbound
  exact hbound

/-! ## Hash-lossy dual-mode composition -/

/-- Complete dual-mode composition from the note.  `hmodeSwitch` contains the ordinary-to-lossy
and lossy-to-ordinary computational switches and the terminal sampler replacement.  The middle
lossy-mode gap is discharged by the hash-only complete-view theorem. -/
theorem hashLossyDualModeNativeGap_le
    {Prefix Suffix SourceView : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ)
    (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (fakeDigestSampler : ProbComp (Fin digestCount → Bool))
    (builder : Bool → (Fin digestCount → Bool) → SourceView → ProbComp Bool)
    (source : Bool → Prefix × Suffix → ProbComp SourceView)
    (nativeGap lossyGap modeOne modeZero sigmaPlus sigmaMinus
      sourceBound samplerError : ℝ)
    (hmodeSwitch : nativeGap ≤
      modeOne + modeZero + lossyGap + samplerError)
    (hdiagonal : lossyGap ≤ sigmaPlus + sigmaMinus +
      projectedAggregateAdvantage
        ($ᵗ (Prefix × Suffix))
        (hashedPrefixLeakage (Suffix := Suffix) hash)
        (hashOnlyExperiment builder source true)
        (hashOnlyExperiment builder source false))
    (hsource : projectedMatchSquareAdvantage
        ($ᵗ (Prefix × Suffix)) fakeDigestSampler
        (hashOnlyExperiment builder source true)
        (hashOnlyExperiment builder source false) ≤ sourceBound)
    (hcover : ∀ key,
      probabilityMass ($ᵗ (Prefix × Suffix)) key ≠ 0 →
        probabilityMass fakeDigestSampler
          (hashedPrefixLeakage (Suffix := Suffix) hash key) ≠ 0)
    (hoptimized : ∀ digest,
      probabilityMass fakeDigestSampler digest =
        Real.sqrt
            (probabilityMass
              (leakageLaw ($ᵗ (Prefix × Suffix))
                (hashedPrefixLeakage (Suffix := Suffix) hash)) digest) /
          halfRenyiNormalizer
            ($ᵗ (Prefix × Suffix))
            (hashedPrefixLeakage (Suffix := Suffix) hash)) :
    nativeGap ≤
      modeOne + modeZero + sigmaPlus + sigmaMinus +
        binaryHashSquareRootLoss digestCount * Real.sqrt sourceBound +
          samplerError := by
  have hlossy := hashOnlyNativeGap_le_squareRootLoss
    digestCount hash huniformHash fakeDigestSampler builder source
    lossyGap sigmaPlus sigmaMinus sourceBound
    hdiagonal hsource hcover hoptimized
  linarith

/-! ## Translation-only impossibility for a shorter hash -/

/-- At the usual aggregate cutoff, a shorter balanced digest cannot drive an exact
phase-oblivious translation builder.  This is the formal separation between the existing
translation-only proof and the proposed nonlinear/dual-mode construction. -/
theorem no_short_uniformHash_phaseObliviousBuilder
    {Index Suffix : Type}
    [Fintype Index] [DecidableEq Index]
    [Fintype Suffix] [Nonempty Suffix] [SampleableType Suffix]
    [SampleableType (BitVector Index)]
    [Fintype (BitVector Index × Suffix)]
    [SampleableType (BitVector Index × Suffix)]
    (digestCount degree : ℕ)
    (hdigest : digestCount < Fintype.card Index)
    (hdegree : degree + 2 ≤ Fintype.card Index)
    (hash : BitVector Index → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (plaintextLaw : Bool → (Fin digestCount → Bool) → BitVector Index → ℝ) :
    ¬ PhaseObliviousPlaintextCorrect
      degree Prod.fst
      (hashedPrefixLeakage (Suffix := Suffix) hash)
      plaintextLaw := by
  intro hcorrect
  have hlower :=
    twoPow_card_le_projectedLeakageConcentration_of_phaseOblivious
      degree hdegree
      (hashedPrefixLeakage (Suffix := Suffix) hash)
      plaintextLaw hcorrect
  rw [hashedBinaryPrefixConcentration_eq_twoPow
    digestCount hash huniformHash] at hlower
  have hpowNat :
      2 ^ digestCount < 2 ^ Fintype.card Index :=
    Nat.pow_lt_pow_right (by omega : 1 < 2) hdigest
  have hpowReal :
      (2 : ℝ) ^ digestCount < (2 : ℝ) ^ Fintype.card Index := by
    exact_mod_cast hpowNat
  exact (not_lt_of_ge hlower) hpowReal

/-! ## Acyclic block-cycle composition -/

/-- The endpoint gap of a sequence of block hybrids is at most the sum of its adjacent gaps. -/
theorem abs_sub_le_sum_blockGaps (values : ℕ → ℝ) (blockCount : ℕ) :
    |values 0 - values blockCount| ≤
      ∑ block ∈ Finset.range blockCount,
        |values block - values (block + 1)| := by
  rw [← Finset.sum_range_sub' values blockCount]
  exact Finset.abs_sum_le_sum_abs
    (fun block ↦ values block - values (block + 1))
    (Finset.range blockCount)

/-- Blockwise match-and-square composition.  Each adjacent premise must be proved with a local
key cycle; keeping one common circular key does not supply these premises. -/
theorem blockCycleSecurity_le
    (values sigma concentration sourceBound : ℕ → ℝ)
    (blockCount : ℕ)
    (hlocal : ∀ block < blockCount,
      |values block - values (block + 1)| ≤
        sigma block +
          Real.sqrt (2 * concentration block * sourceBound block)) :
    |values 0 - values blockCount| ≤
      ∑ block ∈ Finset.range blockCount,
        (sigma block +
          Real.sqrt (2 * concentration block * sourceBound block)) := by
  calc
    |values 0 - values blockCount| ≤
        ∑ block ∈ Finset.range blockCount,
          |values block - values (block + 1)| :=
      abs_sub_le_sum_blockGaps values blockCount
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro block hblock
      exact hlocal block (Finset.mem_range.mp hblock)

/-- Uniform `b`-bit local cycles give the explicit block loss from equation (6). -/
theorem uniformBinaryBlockCycleSecurity_le
    (values : ℕ → ℝ) (blockCount blockSize : ℕ)
    (sigma sourceBound : ℝ)
    (hlocal : ∀ block < blockCount,
      |values block - values (block + 1)| ≤
        sigma + Real.sqrt ((2 : ℝ) ^ (blockSize + 1) * sourceBound)) :
    |values 0 - values blockCount| ≤
      (blockCount : ℝ) *
        (sigma + Real.sqrt ((2 : ℝ) ^ (blockSize + 1) * sourceBound)) := by
  calc
    |values 0 - values blockCount| ≤
        ∑ block ∈ Finset.range blockCount,
          |values block - values (block + 1)| :=
      abs_sub_le_sum_blockGaps values blockCount
    _ ≤ ∑ _block ∈ Finset.range blockCount,
        (sigma + Real.sqrt ((2 : ℝ) ^ (blockSize + 1) * sourceBound)) := by
      apply Finset.sum_le_sum
      intro block hblock
      exact hlocal block (Finset.mem_range.mp hblock)
    _ = _ := by
      simp
      ring

/-- If the prefix is exactly partitioned into equal blocks, the number of cycles is `t / b`. -/
theorem exactBlockCount_eq_div
    {prefixCount blockSize blockCount : ℕ}
    (hblockSize : 0 < blockSize)
    (hpartition : blockCount * blockSize = prefixCount) :
    blockCount = prefixCount / blockSize := by
  calc
    blockCount = blockCount * blockSize / blockSize := by
      symm
      simpa [Nat.mul_comm] using Nat.mul_div_cancel_left blockCount hblockSize
    _ = prefixCount / blockSize := by rw [hpartition]

/-- Equation (6) with its architectural exact-partition premise made explicit. -/
theorem exactPartitionBinaryBlockCycleSecurity_le
    (values : ℕ → ℝ)
    (prefixCount blockCount blockSize : ℕ)
    (sigma sourceBound : ℝ)
    (hblockSize : 0 < blockSize)
    (hpartition : blockCount * blockSize = prefixCount)
    (hlocal : ∀ block < blockCount,
      |values block - values (block + 1)| ≤
        sigma + Real.sqrt ((2 : ℝ) ^ (blockSize + 1) * sourceBound)) :
    |values 0 - values blockCount| ≤
      (prefixCount / blockSize : ℕ) *
        (sigma + Real.sqrt ((2 : ℝ) ^ (blockSize + 1) * sourceBound)) := by
  rw [← exactBlockCount_eq_div hblockSize hpartition]
  exact uniformBinaryBlockCycleSecurity_le
    values blockCount blockSize sigma sourceBound hlocal

/-! ## Exact source-exponent budget -/

/-- Algebraic sufficient condition corresponding to
`-log₂ epsilon ≥ 2 lambda + b + 1 + 2 log₂(blockCount)`.  This formulation is exact for every
positive block count and avoids introducing a real logarithm into a finite reduction theorem. -/
def perBlockSourceRequirement
    (securityBits blockSize blockCount : ℕ) : ℝ :=
  (((2 : ℝ) ^ (2 * securityBits + blockSize + 1)) *
    (blockCount : ℝ) ^ 2)⁻¹

/-- The logarithmic source requirement is exactly sufficient to make the sum of all block source
terms at most `2 ^ (-securityBits)`. -/
theorem blockSourceRequirement_sufficient
    (securityBits blockSize blockCount : ℕ)
    (sourceBound : ℝ)
    (hblockCount : 0 < blockCount)
    (hsourceBound : 0 ≤ sourceBound)
    (hrequirement : sourceBound ≤
      perBlockSourceRequirement securityBits blockSize blockCount) :
    (blockCount : ℝ) *
        Real.sqrt ((2 : ℝ) ^ (blockSize + 1) * sourceBound) ≤
      ((2 : ℝ) ^ securityBits)⁻¹ := by
  let A : ℝ := (2 : ℝ) ^ (blockSize + 1)
  let B : ℝ := (2 : ℝ) ^ securityBits
  let K : ℝ := blockCount
  have hA : 0 ≤ A := by positivity
  have hApos : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast hblockCount
  have hAK : 0 ≤ A * K ^ 2 := mul_nonneg hA (sq_nonneg K)
  have hscaled :
      A * K ^ 2 * sourceBound ≤ A * K ^ 2 *
        perBlockSourceRequirement securityBits blockSize blockCount :=
    mul_le_mul_of_nonneg_left hrequirement hAK
  have hpow :
      (2 : ℝ) ^ (2 * securityBits + blockSize + 1) = A * B ^ 2 := by
    dsimp [A, B]
    rw [show 2 * securityBits + blockSize + 1 =
        (blockSize + 1) + securityBits * 2 by omega,
      pow_add, pow_mul]
  have hbudget :
      A * K ^ 2 * sourceBound ≤ B⁻¹ ^ 2 := by
    calc
      A * K ^ 2 * sourceBound ≤ A * K ^ 2 *
          perBlockSourceRequirement securityBits blockSize blockCount := hscaled
      _ = B⁻¹ ^ 2 := by
        unfold perBlockSourceRequirement
        change A * K ^ 2 *
            (((2 : ℝ) ^ (2 * securityBits + blockSize + 1) * K ^ 2)⁻¹) =
          B⁻¹ ^ 2
        rw [hpow]
        field_simp [hApos.ne', hB.ne', hK.ne']
  have hleft :
      0 ≤ K * Real.sqrt (A * sourceBound) :=
    mul_nonneg hK.le (Real.sqrt_nonneg _)
  have hright : 0 ≤ B⁻¹ := inv_nonneg.mpr hB.le
  apply (sq_le_sq₀ hleft hright).mp
  calc
    (K * Real.sqrt (A * sourceBound)) ^ 2 =
        A * K ^ 2 * sourceBound := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hA hsourceBound)]
      ring
    _ ≤ B⁻¹ ^ 2 := hbudget

/-- When the number of blocks is itself `2 ^ ell`, the algebraic requirement has precisely the
integer exponent `2 lambda + b + 1 + 2 ell`. -/
theorem perBlockSourceRequirement_powerOfTwoBlocks
    (securityBits blockSize blockExponent : ℕ) :
    perBlockSourceRequirement securityBits blockSize (2 ^ blockExponent) =
      ((2 : ℝ) ^
        (2 * securityBits + blockSize + 1 + 2 * blockExponent))⁻¹ := by
  unfold perBlockSourceRequirement
  congr 1
  norm_num [Nat.cast_pow]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-! ## Exact vector-LWE XOR transport and the native-ring boundary -/

/-- Equation (8) from the note, in the repository's batch-vector orientation.  The public mask
transport preserves the message and the error exactly while replacing `secret` by
`secret xor mask`. -/
theorem vectorLWE_xorTransport_exact
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret mask : BinarySecret dimension)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error : Fin samples → R) :
    Native.ScalarSecretRandomization.transformBatch mask
        (TLWE.batchAssemble (embedBinarySecret secret)
          challenge message error) =
      TLWE.batchAssemble
        (embedBinarySecret
          (Native.ScalarSecretRandomization.maskedSecret secret mask))
        (Native.ScalarSecretRandomization.transformChallenge mask challenge)
        message error := by
  exact Native.ScalarSecretRandomization.transformBatch_batchAssemble
    secret mask challenge message error

/-- The public mask transform is a permutation and therefore preserves a uniform vector-LWE
challenge law exactly. -/
theorem vectorLWE_xorTransport_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ}
    (mask : BinarySecret dimension) :
    evalDist
        (Native.ScalarSecretRandomization.transformChallenge
          (R := R) (samples := samples) mask <$>
          ($ᵗ Matrix (Fin dimension) (Fin samples) R)) =
      evalDist ($ᵗ Matrix (Fin dimension) (Fin samples) R) := by
  exact Native.ScalarSecretRandomization.transformChallenge_uniform_evalDist mask

/-- Native ring multiplication plus an offset implements coefficientwise XOR at modulus greater
than two exactly for the identity mask and the global-complement mask.  This is the formal
convolution-family obstruction to importing arbitrary vector-LWE XOR transport into native
TRLWE. -/
theorem nativeScalarAffineXorTransport_iff_constant
    {q degree : ℕ} (hq : 2 < q)
    (mask : BinarySecret (degree + 1)) :
    Native.SharedRandomnessOneCycle.SecretRandomization.ScalarAffineXorTransport
        q (degree + 1) mask ↔
      (∀ coordinate, mask coordinate = false) ∨
        (∀ coordinate, mask coordinate = true) := by
  exact
    Native.SharedRandomnessOneCycle.SecretRandomization.scalarAffineXorTransport_iff_constant
      hq mask

end

end FormalProof4FHE.TFHE.NativeTRGSWHashCompressedSecurity
