/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SuffixRLWEPRG

/-!
# Exact Dense-Mask Source-Aligned Joint Law

This file installs the concrete dense-mask constructors described in
`sketch/source_aligned_brk_ksk_joint_law.tex`.  The suffix source may use an arbitrary
structured public-gadget sampler; the two prefix sources use genuinely uniform dense masks.

The complete view retains the shared gadget, BRK body, dense aligned-KSK mask, and aligned-KSK
body.  The BRK source error is reused in the KSK and an independent correction is added.  The
three constructors are exact: no complete-view statistical defect and no rowwise hybrid remains.
Computational hardness of the supplied structured suffix problem and dense prefix problem stays
an explicit premise.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.SourceAlignedDenseJointLaw

noncomputable section

open DirectSubsetKeyBRK
open DirectSubsetKeyBRK.PublicViewConstructor
open SourceAlignedBRKKSKJointLaw.CompleteView

/-! ## Source problems and complete dense views -/

/-- Complete scalarized source-aligned cloud-key view. -/
structure DenseView (R Prefix Suffix Factor : Type) where
  gadget : Matrix Suffix Factor R
  brkBody : Factor → R
  prefixMask : Matrix Prefix Factor R
  kskBody : Factor → R

/-- A structured suffix source.  Its challenge sampler need not be uniform over all scalar
matrices; for the lvl02 instantiation it is the scalar image of a uniform ring-mask matrix. -/
def suffixProblem {R Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Suffix] [DecidableEq Suffix] [Fintype Factor] [DecidableEq Factor]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R)) :
    LearningWithErrors.Problem
      (Matrix Suffix Factor R) (Suffix → R) (Factor → R) where
  sampleChallenge := gadgetSampler
  sampleSecret := suffixSecretSampler
  sampleError := brkErrorSampler
  noiseless := fun secret gadget ↦ gadget.transpose *ᵥ secret
  sampleUniform := $ᵗ (Factor → R)

/-- Dense prefix LWE with an arbitrary complete correction-error law. -/
def prefixProblem {R Prefix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix] [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R)) :
    LearningWithErrors.Problem
      (Matrix Prefix Factor R) (Prefix → R) (Factor → R) where
  sampleChallenge := $ᵗ (Matrix Prefix Factor R)
  sampleSecret := prefixSecretSampler
  sampleError := correctionSampler
  noiseless := fun secret mask ↦ mask.transpose *ᵥ secret
  sampleUniform := $ᵗ (Factor → R)

/-- Public prefix-linear terms in the BRK and aligned-KSK bodies.  Both matrices may depend on
the structured suffix gadget.  This covers both the BRK plaintext matrix and a known-prefix
embedding into the ring secret. -/
structure PrefixMaps (R Prefix Suffix Factor : Type) where
  brk : Matrix Suffix Factor R → Matrix Prefix Factor R
  ksk : Matrix Suffix Factor R → Matrix Prefix Factor R

/-- Select a complete vector on one Boolean branch. -/
def branchVector {R Factor : Type} [Zero R]
    (branch : Bool) (value : Factor → R) : Factor → R :=
  if branch then value else 0

/-- Assemble one complete correlated dense view from all underlying coins. -/
def assemble {R Prefix Suffix Factor : Type} [CommRing R]
    [Fintype Prefix] [Fintype Suffix] [Fintype Factor]
    (maps : PrefixMaps R Prefix Suffix Factor)
    (brkBranch suffixBranch : Bool)
    (gadget : Matrix Suffix Factor R)
    (suffixSecret : Suffix → R) (brkError : Factor → R)
    (prefixSecret : Prefix → R) (prefixMask : Matrix Prefix Factor R)
    (correction : Factor → R) : DenseView R Prefix Suffix Factor :=
  let suffixBody := gadget.transpose *ᵥ suffixSecret
  let sourceBody := suffixBody + brkError
  { gadget := gadget
    brkBody := sourceBody +
      branchVector brkBranch ((maps.brk gadget).transpose *ᵥ prefixSecret)
    prefixMask := prefixMask
    kskBody := (prefixMask + maps.ksk gadget).transpose *ᵥ prefixSecret +
      branchVector suffixBranch suffixBody + brkError + correction }

/-- Direct complete-view sampler.  The same `brkError` occurs in both public bodies. -/
def view {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor)
    (brkBranch suffixBranch : Bool) : ProbComp (DenseView R Prefix Suffix Factor) := do
  let gadget ← gadgetSampler
  let suffixSecret ← suffixSecretSampler
  let brkError ← brkErrorSampler
  let prefixSecret ← prefixSecretSampler
  let prefixMask ← $ᵗ (Matrix Prefix Factor R)
  let correction ← correctionSampler
  return assemble maps brkBranch suffixBranch gadget suffixSecret brkError
    prefixSecret prefixMask correction

/-- Real-BRK/real-KSK, zero-BRK/real-KSK, and zero-BRK/zero-KSK endpoints. -/
def alignedViews {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) :
    AlignedViews (DenseView R Prefix Suffix Factor) where
  real := view gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
    correctionSampler maps true true
  middle := view gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
    correctionSampler maps false true
  zero := view gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
    correctionSampler maps false false

/-! ## Exact suffix constructor -/

/-- Coins sampled independently after receiving the suffix challenge. -/
structure SuffixCoins (R Prefix Factor : Type) where
  prefixSecret : Prefix → R
  prefixMask : Matrix Prefix Factor R
  correction : Factor → R

def suffixCoinsSampler {R Prefix Factor : Type}
    [Fintype R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R)) :
    ProbComp (SuffixCoins R Prefix Factor) := do
  let prefixSecret ← prefixSecretSampler
  let prefixMask ← $ᵗ (Matrix Prefix Factor R)
  let correction ← correctionSampler
  return ⟨prefixSecret, prefixMask, correction⟩

/-- Build the first-hop branch from one scalarized suffix transcript. -/
def suffixBuild {R Prefix Suffix Factor : Type} [CommRing R] [Fintype Prefix]
    (maps : PrefixMaps R Prefix Suffix Factor) :
    Bool → SuffixCoins R Prefix Factor →
      (Matrix Suffix Factor R × (Factor → R)) →
        ProbComp (DenseView R Prefix Suffix Factor) :=
  fun branch coins transcript ↦ pure
    { gadget := transcript.1
      brkBody := transcript.2 + branchVector branch
        ((maps.brk transcript.1).transpose *ᵥ coins.prefixSecret)
      prefixMask := coins.prefixMask
      kskBody := (coins.prefixMask + maps.ksk transcript.1).transpose *ᵥ
          coins.prefixSecret + transcript.2 + coins.correction }

/-- The suffix constructor reproduces both correlated real-source endpoints exactly. -/
theorem suffixBuild_real_evalDist
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool) :
    evalDist (constructedView
        (suffixCoinsSampler prefixSecretSampler correctionSampler)
        (LearningWithErrors.distr
          (suffixProblem gadgetSampler suffixSecretSampler brkErrorSampler))
        (suffixBuild maps) branch) =
      evalDist (view gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
        correctionSampler maps branch true) := by
  simp [constructedView, LearningWithErrors.distr, suffixProblem, suffixCoinsSampler,
    suffixBuild, view, assemble, branchVector, bind_assoc, monad_norm, add_assoc]

/-- Constructor with exact real laws and its actual (later computationally explained) uniform
branch gap retained as the structure's bookkeeping distance. -/
noncomputable def suffixConstructor
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) :
    PublicViewConstructor
      (suffixProblem gadgetSampler suffixSecretSampler brkErrorSampler)
      (suffixCoinsSampler prefixSecretSampler correctionSampler)
      (alignedViews gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
        correctionSampler maps).first where
  build := suffixBuild maps
  realError := fun _ ↦ 0
  uniformError := tvDist
    (constructedView (suffixCoinsSampler prefixSecretSampler correctionSampler)
      (LearningWithErrors.uniformDistr
        (suffixProblem gadgetSampler suffixSecretSampler brkErrorSampler))
      (suffixBuild maps) true)
    (constructedView (suffixCoinsSampler prefixSecretSampler correctionSampler)
      (LearningWithErrors.uniformDistr
        (suffixProblem gadgetSampler suffixSecretSampler brkErrorSampler))
      (suffixBuild maps) false)
  realError_nonneg := fun _ ↦ le_rfl
  uniformError_nonneg := tvDist_nonneg _ _
  realDistance := by
    intro branch
    unfold tvDist
    rw [suffixBuild_real_evalDist]
    cases branch <;> simp [alignedViews, AlignedViews.first, branchView]
  uniformDistance := le_rfl

/-! ## Exact first dense-prefix constructor -/

/-- Select a complete prefix mask on one Boolean branch. -/
def branchMatrix {R Prefix Factor : Type} [Zero R]
    (branch : Bool) (value : Matrix Prefix Factor R) : Matrix Prefix Factor R :=
  if branch then value else 0

/-- Translation of a dense public mask by a fixed matrix. -/
def subMatrixEquiv {R Prefix Factor : Type} [AddGroup R]
    (shift : Matrix Prefix Factor R) :
    Matrix Prefix Factor R ≃ Matrix Prefix Factor R where
  toFun matrix := matrix - shift
  invFun matrix := matrix + shift
  left_inv matrix := by simp
  right_inv matrix := by simp

/-- A fixed public translation preserves a genuinely uniform dense-mask law. -/
theorem subMatrix_uniform_evalDist
    {R Prefix Factor : Type} [AddGroup R]
    [Fintype R] [Fintype Prefix] [Fintype Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (shift : Matrix Prefix Factor R) :
    evalDist (subMatrixEquiv shift <$> ($ᵗ (Matrix Prefix Factor R))) =
      evalDist ($ᵗ (Matrix Prefix Factor R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix Prefix Factor R) (β := Matrix Prefix Factor R)
    (subMatrixEquiv shift) (subMatrixEquiv shift).bijective

/-- Translation of a complete body vector by a fixed vector. -/
def addVectorEquiv {R Factor : Type} [AddGroup R] (shift : Factor → R) :
    (Factor → R) ≃ (Factor → R) where
  toFun vector := vector + shift
  invFun vector := vector - shift
  left_inv vector := by simp
  right_inv vector := by simp

/-- A fixed public translation preserves a uniform complete-body law. -/
theorem addVector_uniform_evalDist
    {R Factor : Type} [AddGroup R] [Fintype R] [Fintype Factor]
    [SampleableType (Factor → R)] (shift : Factor → R) :
    evalDist (addVectorEquiv shift <$> ($ᵗ (Factor → R))) =
      evalDist ($ᵗ (Factor → R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Factor → R) (β := Factor → R)
    (addVectorEquiv shift) (addVectorEquiv shift).bijective

/-- Public coins used to explain the two branches produced by a uniform suffix body. -/
structure RandomPrefixCoins (R Suffix Factor : Type) where
  gadget : Matrix Suffix Factor R
  brkBody : Factor → R

def randomPrefixCoinsSampler {R Suffix Factor : Type}
    [Fintype R] [SampleableType R]
    [Fintype Factor] [DecidableEq Factor]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R)) :
    ProbComp (RandomPrefixCoins R Suffix Factor) := do
  let gadget ← gadgetSampler
  let brkBody ← $ᵗ (Factor → R)
  return ⟨gadget, brkBody⟩

/-- Reparameterize a dense prefix-LWE transcript into a random-suffix complete view. -/
def randomPrefixBuild {R Prefix Suffix Factor : Type} [CommRing R]
    (maps : PrefixMaps R Prefix Suffix Factor) :
    Bool → RandomPrefixCoins R Suffix Factor →
      (Matrix Prefix Factor R × (Factor → R)) →
        ProbComp (DenseView R Prefix Suffix Factor) :=
  fun branch coins transcript ↦ pure
    { gadget := coins.gadget
      brkBody := coins.brkBody
      prefixMask := (transcript.1 + branchMatrix branch (maps.brk coins.gadget)) -
        maps.ksk coins.gadget
      kskBody := coins.brkBody + transcript.2 }

/-- Boolean selection commutes with transposed matrix/vector multiplication. -/
theorem branchMatrix_transpose_mulVec
    {R Prefix Factor : Type} [CommRing R] [Fintype Prefix]
    (branch : Bool) (matrix : Matrix Prefix Factor R) (secret : Prefix → R) :
    (branchMatrix branch matrix).transpose *ᵥ secret =
      branchVector branch (matrix.transpose *ᵥ secret) := by
  cases branch <;> simp [branchMatrix, branchVector]

/-- Affine change of the two independent uniform objects used by the first prefix hop.
The source side is `(suffix body, displayed mask)`; the target side is
`(prefix challenge mask, displayed BRK body)`. -/
def randomPrefixPairEquiv {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype Prefix]
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool)
    (gadget : Matrix Suffix Factor R) (prefixSecret : Prefix → R) :
    ((Factor → R) × Matrix Prefix Factor R) ≃
      (Matrix Prefix Factor R × (Factor → R)) where
  toFun pair :=
    (pair.2 + maps.ksk gadget - branchMatrix branch (maps.brk gadget),
      pair.1 + branchVector branch
        ((maps.brk gadget).transpose *ᵥ prefixSecret))
  invFun pair :=
    (pair.2 - branchVector branch
        ((maps.brk gadget).transpose *ᵥ prefixSecret),
      (pair.1 + branchMatrix branch (maps.brk gadget)) - maps.ksk gadget)
  left_inv pair := by
    rcases pair with ⟨body, mask⟩
    apply Prod.ext
    · simp
    · simp
  right_inv pair := by
    rcases pair with ⟨mask, body⟩
    apply Prod.ext
    · simp
    · simp

/-- Deterministic normal form of one uniform-suffix branch. -/
def suffixUniformFinish {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype Prefix]
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool)
    (gadget : Matrix Suffix Factor R) (prefixSecret : Prefix → R)
    (correction : Factor → R)
    (pair : (Factor → R) × Matrix Prefix Factor R) :
    DenseView R Prefix Suffix Factor :=
  { gadget := gadget
    brkBody := pair.1 + branchVector branch
      ((maps.brk gadget).transpose *ᵥ prefixSecret)
    prefixMask := pair.2
    kskBody := (pair.2 + maps.ksk gadget).transpose *ᵥ prefixSecret +
      pair.1 + correction }

/-- Deterministic normal form produced from a real dense-prefix transcript. -/
def randomPrefixFinish {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype Prefix]
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool)
    (gadget : Matrix Suffix Factor R) (prefixSecret : Prefix → R)
    (correction : Factor → R)
    (pair : Matrix Prefix Factor R × (Factor → R)) :
    DenseView R Prefix Suffix Factor :=
  { gadget := gadget
    brkBody := pair.2
    prefixMask := (pair.1 + branchMatrix branch (maps.brk gadget)) - maps.ksk gadget
    kskBody := pair.2 + (pair.1.transpose *ᵥ prefixSecret + correction) }

/-- The affine change of variables identifies the two first-hop normal forms pointwise. -/
theorem randomPrefixFinish_pairEquiv
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype Prefix]
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool)
    (gadget : Matrix Suffix Factor R) (prefixSecret : Prefix → R)
    (correction : Factor → R)
    (pair : (Factor → R) × Matrix Prefix Factor R) :
    randomPrefixFinish maps branch gadget prefixSecret correction
        (randomPrefixPairEquiv maps branch gadget prefixSecret pair) =
      suffixUniformFinish maps branch gadget prefixSecret correction pair := by
  rcases pair with ⟨body, mask⟩
  cases branch with
  | false =>
      simp [randomPrefixFinish, randomPrefixPairEquiv, suffixUniformFinish,
        branchMatrix, branchVector, Matrix.add_mulVec]
      abel
  | true =>
      simp [randomPrefixFinish, randomPrefixPairEquiv, suffixUniformFinish,
        branchMatrix, branchVector, Matrix.add_mulVec, Matrix.sub_mulVec]
      abel

/-- The affine pair change sends the two independently uniform suffix-side objects to the two
independently uniform prefix-side objects. -/
theorem randomPrefixPair_uniform_evalDist
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)] [SampleableType (Factor → R)]
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool)
    (gadget : Matrix Suffix Factor R) (prefixSecret : Prefix → R) :
    evalDist (do
        let prefixMask ← $ᵗ (Matrix Prefix Factor R)
        let brkBody ← $ᵗ (Factor → R)
        return (prefixMask, brkBody)) =
      evalDist (randomPrefixPairEquiv maps branch gadget prefixSecret <$> do
        let suffixBody ← $ᵗ (Factor → R)
        let displayedMask ← $ᵗ (Matrix Prefix Factor R)
        return (suffixBody, displayedMask)) := by
  let suffixPairs : ProbComp ((Factor → R) × Matrix Prefix Factor R) := do
    let suffixBody ← $ᵗ (Factor → R)
    let displayedMask ← $ᵗ (Matrix Prefix Factor R)
    return (suffixBody, displayedMask)
  let prefixPairs : ProbComp (Matrix Prefix Factor R × (Factor → R)) := do
    let prefixMask ← $ᵗ (Matrix Prefix Factor R)
    let brkBody ← $ᵗ (Factor → R)
    return (prefixMask, brkBody)
  have hsuffix :
      evalDist suffixPairs =
        evalDist ($ᵗ ((Factor → R) × Matrix Prefix Factor R)) := by
    exact FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  have hprefix :
      evalDist prefixPairs =
        evalDist ($ᵗ (Matrix Prefix Factor R × (Factor → R))) := by
    exact FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  have hmap := evalDist_map_eq_of_evalDist_eq hsuffix
    (randomPrefixPairEquiv maps branch gadget prefixSecret)
  have hequiv :
      evalDist (randomPrefixPairEquiv maps branch gadget prefixSecret <$>
        ($ᵗ ((Factor → R) × Matrix Prefix Factor R))) =
        evalDist ($ᵗ (Matrix Prefix Factor R × (Factor → R))) :=
    evalDist_map_bijective_uniform_cross
      (α := (Factor → R) × Matrix Prefix Factor R)
      (β := Matrix Prefix Factor R × (Factor → R))
      (randomPrefixPairEquiv maps branch gadget prefixSecret)
      (randomPrefixPairEquiv maps branch gadget prefixSecret).bijective
  change evalDist prefixPairs =
    evalDist (randomPrefixPairEquiv maps branch gadget prefixSecret <$> suffixPairs)
  exact hprefix.trans (hequiv.symm.trans hmap.symm)

/-- Common normal form of the real dense-prefix construction. -/
def randomPrefixNormalized {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Prefix] [Fintype Factor]
    [SampleableType (Matrix Prefix Factor R)] [SampleableType (Factor → R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool) :
    ProbComp (DenseView R Prefix Suffix Factor) := do
  let gadget ← gadgetSampler
  let prefixSecret ← prefixSecretSampler
  let prefixMask ← $ᵗ (Matrix Prefix Factor R)
  let brkBody ← $ᵗ (Factor → R)
  let correction ← correctionSampler
  return randomPrefixFinish maps branch gadget prefixSecret correction
    (prefixMask, brkBody)

/-- Common normal form of the uniform-suffix construction. -/
def suffixUniformNormalized {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Prefix] [Fintype Factor]
    [SampleableType (Matrix Prefix Factor R)] [SampleableType (Factor → R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool) :
    ProbComp (DenseView R Prefix Suffix Factor) := do
  let gadget ← gadgetSampler
  let prefixSecret ← prefixSecretSampler
  let suffixBody ← $ᵗ (Factor → R)
  let displayedMask ← $ᵗ (Matrix Prefix Factor R)
  let correction ← correctionSampler
  return suffixUniformFinish maps branch gadget prefixSecret correction
    (suffixBody, displayedMask)

/-- The two normal forms have exactly the same complete-view distribution. -/
theorem randomPrefixNormalized_evalDist_eq_suffixUniform
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool) :
    evalDist (randomPrefixNormalized gadgetSampler prefixSecretSampler correctionSampler
      maps branch) =
      evalDist (suffixUniformNormalized gadgetSampler prefixSecretSampler correctionSampler
        maps branch) := by
  unfold randomPrefixNormalized suffixUniformNormalized
  refine evalDist_bind_congr' gadgetSampler fun gadget ↦ ?_
  refine evalDist_bind_congr' prefixSecretSampler fun prefixSecret ↦ ?_
  let prefixPairs : ProbComp (Matrix Prefix Factor R × (Factor → R)) := do
    let prefixMask ← $ᵗ (Matrix Prefix Factor R)
    let brkBody ← $ᵗ (Factor → R)
    return (prefixMask, brkBody)
  let suffixPairs : ProbComp ((Factor → R) × Matrix Prefix Factor R) := do
    let suffixBody ← $ᵗ (Factor → R)
    let displayedMask ← $ᵗ (Matrix Prefix Factor R)
    return (suffixBody, displayedMask)
  have hpairs := randomPrefixPair_uniform_evalDist maps branch gadget prefixSecret
  have hnormalized : evalDist (prefixPairs >>= fun pair ↦
      correctionSampler >>= fun correction ↦
        pure (randomPrefixFinish maps branch gadget prefixSecret correction pair)) =
    evalDist (suffixPairs >>= fun pair ↦
      correctionSampler >>= fun correction ↦
        pure (suffixUniformFinish maps branch gadget prefixSecret correction pair)) := by
    calc
      _ = evalDist ((randomPrefixPairEquiv maps branch gadget prefixSecret <$> suffixPairs) >>=
          fun pair ↦ correctionSampler >>= fun correction ↦
            pure (randomPrefixFinish maps branch gadget prefixSecret correction pair)) := by
        rw [evalDist_bind, hpairs, ← evalDist_bind]
      _ = _ := by
        simp only [map_eq_bind_pure_comp, bind_assoc]
        refine evalDist_bind_congr' suffixPairs fun pair ↦ ?_
        refine evalDist_bind_congr' correctionSampler fun correction ↦ ?_
        rw [randomPrefixFinish_pairEquiv]
  simpa [prefixPairs, suffixPairs, bind_assoc] using hnormalized

/-- Reordering the independent dense-prefix challenge, prefix secret, correction, gadget, and
uniform BRK body exposes `randomPrefixNormalized`. -/
theorem randomPrefixBuild_real_evalDist_eq_normalized
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool) :
    evalDist (constructedView
        (randomPrefixCoinsSampler gadgetSampler)
        (LearningWithErrors.distr
          (prefixProblem prefixSecretSampler correctionSampler))
        (randomPrefixBuild maps) branch) =
      evalDist (randomPrefixNormalized gadgetSampler prefixSecretSampler correctionSampler
        maps branch) := by
  let source := LearningWithErrors.distr
    (prefixProblem prefixSecretSampler correctionSampler)
  let coins := randomPrefixCoinsSampler gadgetSampler
  have hswap :
      evalDist (constructedView coins source (randomPrefixBuild maps) branch) =
        evalDist (coins >>= fun coin ↦
          source >>= fun transcript ↦ randomPrefixBuild maps branch coin transcript) := by
    unfold constructedView
    exact OracleComp.DeferredSampling.evalDist_bind_comm source coins _
  rw [hswap]
  simp only [coins, source, randomPrefixCoinsSampler, LearningWithErrors.distr,
    prefixProblem, randomPrefixBuild, randomPrefixNormalized,
    bind_assoc, monad_norm]
  refine evalDist_bind_congr' gadgetSampler fun gadget ↦ ?_
  let finish : (Factor → R) → Matrix Prefix Factor R → (Prefix → R) →
      (Factor → R) → ProbComp (DenseView R Prefix Suffix Factor) :=
    fun brkBody prefixMask
      (prefixSecret : Prefix → R) (correction : Factor → R) ↦
    pure (randomPrefixFinish maps branch gadget prefixSecret correction
      (prefixMask, brkBody))
  calc
    evalDist (($ᵗ (Factor → R)) >>= fun brkBody ↦
        ($ᵗ (Matrix Prefix Factor R)) >>= fun prefixMask ↦
          prefixSecretSampler >>= fun prefixSecret ↦
            correctionSampler >>= fun correction ↦
              finish brkBody prefixMask prefixSecret correction) =
      evalDist (($ᵗ (Matrix Prefix Factor R)) >>= fun prefixMask ↦
        ($ᵗ (Factor → R)) >>= fun brkBody ↦
          prefixSecretSampler >>= fun prefixSecret ↦
            correctionSampler >>= fun correction ↦
              finish brkBody prefixMask prefixSecret correction) :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = evalDist (($ᵗ (Matrix Prefix Factor R)) >>= fun prefixMask ↦
        prefixSecretSampler >>= fun prefixSecret ↦
          ($ᵗ (Factor → R)) >>= fun brkBody ↦
            correctionSampler >>= fun correction ↦
              finish brkBody prefixMask prefixSecret correction) := by
      refine evalDist_bind_congr' ($ᵗ (Matrix Prefix Factor R)) fun prefixMask ↦ ?_
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = evalDist (prefixSecretSampler >>= fun prefixSecret ↦
        ($ᵗ (Matrix Prefix Factor R)) >>= fun prefixMask ↦
          ($ᵗ (Factor → R)) >>= fun brkBody ↦
            correctionSampler >>= fun correction ↦
              finish brkBody prefixMask prefixSecret correction) :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      simp [finish, randomPrefixFinish, branchMatrix]

/-- Reordering the uniform suffix body with the independent prefix secret exposes
`suffixUniformNormalized`. -/
theorem suffixBuild_uniform_evalDist_eq_normalized
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool) :
    evalDist (constructedView
        (suffixCoinsSampler prefixSecretSampler correctionSampler)
        (LearningWithErrors.uniformDistr
          (suffixProblem gadgetSampler suffixSecretSampler brkErrorSampler))
        (suffixBuild maps) branch) =
      evalDist (suffixUniformNormalized gadgetSampler prefixSecretSampler correctionSampler
        maps branch) := by
  simp only [constructedView, LearningWithErrors.uniformDistr, suffixProblem,
    suffixCoinsSampler, suffixBuild, suffixUniformNormalized,
    bind_assoc, monad_norm]
  refine evalDist_bind_congr' gadgetSampler fun gadget ↦ ?_
  simpa [suffixUniformFinish, branchVector, Matrix.transpose_add,
      Matrix.add_mulVec, add_assoc, add_comm, add_left_comm] using
    (OracleComp.DeferredSampling.evalDist_bind_comm
      ($ᵗ (Factor → R)) prefixSecretSampler
      (fun suffixBody prefixSecret ↦
        ($ᵗ (Matrix Prefix Factor R)) >>= fun displayedMask ↦
          correctionSampler >>= fun correction ↦ pure
            (suffixUniformFinish maps branch gadget prefixSecret correction
              (suffixBody, displayedMask))))

/-- A real dense-prefix source reproduces the corresponding uniform-suffix constructed branch
exactly, as a law of the complete correlated view. -/
theorem randomPrefixBuild_real_evalDist
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool) :
    evalDist (constructedView
        (randomPrefixCoinsSampler gadgetSampler)
        (LearningWithErrors.distr
          (prefixProblem prefixSecretSampler correctionSampler))
        (randomPrefixBuild maps) branch) =
      evalDist (uniformConstructedTarget
        (suffixConstructor gadgetSampler suffixSecretSampler brkErrorSampler
          prefixSecretSampler correctionSampler maps) branch) := by
  calc
    _ = evalDist (randomPrefixNormalized gadgetSampler prefixSecretSampler correctionSampler
        maps branch) :=
      randomPrefixBuild_real_evalDist_eq_normalized gadgetSampler prefixSecretSampler
        correctionSampler maps branch
    _ = evalDist (suffixUniformNormalized gadgetSampler prefixSecretSampler correctionSampler
        maps branch) :=
      randomPrefixNormalized_evalDist_eq_suffixUniform gadgetSampler prefixSecretSampler
        correctionSampler maps branch
    _ = _ := by
      rw [← suffixBuild_uniform_evalDist_eq_normalized gadgetSampler suffixSecretSampler
        brkErrorSampler prefixSecretSampler correctionSampler maps branch]
      rfl

/-- On a uniform dense-prefix source, the two first-hop branches differ only by a fixed
translation of the complete dense mask. -/
theorem randomPrefixBuild_uniform_evalDist
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) :
    evalDist (constructedView
        (randomPrefixCoinsSampler gadgetSampler)
        (LearningWithErrors.uniformDistr
          (prefixProblem prefixSecretSampler correctionSampler))
        (randomPrefixBuild maps) true) =
      evalDist (constructedView
        (randomPrefixCoinsSampler gadgetSampler)
        (LearningWithErrors.uniformDistr
          (prefixProblem prefixSecretSampler correctionSampler))
        (randomPrefixBuild maps) false) := by
  let source := LearningWithErrors.uniformDistr
    (prefixProblem prefixSecretSampler correctionSampler)
  let coins := randomPrefixCoinsSampler gadgetSampler
  have hswap (branch : Bool) :
      evalDist (constructedView coins source (randomPrefixBuild maps) branch) =
        evalDist (coins >>= fun coin ↦
          source >>= fun transcript ↦ randomPrefixBuild maps branch coin transcript) := by
    unfold constructedView
    exact OracleComp.DeferredSampling.evalDist_bind_comm source coins _
  rw [hswap true, hswap false]
  simp only [coins, source, randomPrefixCoinsSampler, LearningWithErrors.uniformDistr,
    prefixProblem, randomPrefixBuild, bind_assoc, monad_norm]
  refine evalDist_bind_congr' gadgetSampler fun gadget ↦ ?_
  refine evalDist_bind_congr' ($ᵗ (Factor → R)) fun brkBody ↦ ?_
  let finishFalse : Matrix Prefix Factor R → ProbComp (DenseView R Prefix Suffix Factor) :=
    fun prefixMask ↦ ($ᵗ (Factor → R)) >>= fun body ↦ pure
      { gadget := gadget
        brkBody := brkBody
        prefixMask := prefixMask - maps.ksk gadget
        kskBody := brkBody + body }
  calc
    evalDist (($ᵗ (Matrix Prefix Factor R)) >>= fun prefixMask ↦
        ($ᵗ (Factor → R)) >>= fun body ↦ pure
          { gadget := gadget
            brkBody := brkBody
            prefixMask := (prefixMask + maps.brk gadget) - maps.ksk gadget
            kskBody := brkBody + body }) =
      evalDist ((subMatrixEquiv (-maps.brk gadget) <$>
        ($ᵗ (Matrix Prefix Factor R))) >>= finishFalse) := by
      simp [finishFalse, subMatrixEquiv, map_eq_bind_pure_comp]
    _ = evalDist (($ᵗ (Matrix Prefix Factor R)) >>= finishFalse) := by
      rw [evalDist_bind, subMatrix_uniform_evalDist (-maps.brk gadget), ← evalDist_bind]
    _ = _ := by
      simp [finishFalse, branchMatrix]

/-- Exact public constructor explaining the uniform-suffix branch gap by dense prefix LWE. -/
noncomputable def randomPrefixConstructor
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) :
    PublicViewConstructor
      (prefixProblem prefixSecretSampler correctionSampler)
      (randomPrefixCoinsSampler gadgetSampler)
      (uniformConstructedTarget
        (suffixConstructor gadgetSampler suffixSecretSampler brkErrorSampler
          prefixSecretSampler correctionSampler maps)) :=
  PublicViewConstructor.ofExact (randomPrefixBuild maps)
    (randomPrefixBuild_real_evalDist gadgetSampler suffixSecretSampler brkErrorSampler
      prefixSecretSampler correctionSampler maps)
    (randomPrefixBuild_uniform_evalDist gadgetSampler prefixSecretSampler correctionSampler maps)

/-! ## Exact second dense-prefix constructor -/

/-- Independent suffix state sampled around the second dense-prefix challenge. -/
structure SecondPrefixCoins (R Suffix Factor : Type) where
  gadget : Matrix Suffix Factor R
  suffixSecret : Suffix → R
  brkError : Factor → R

def secondPrefixCoinsSampler {R Suffix Factor : Type}
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R)) :
    ProbComp (SecondPrefixCoins R Suffix Factor) := do
  let gadget ← gadgetSampler
  let suffixSecret ← suffixSecretSampler
  let brkError ← brkErrorSampler
  return ⟨gadget, suffixSecret, brkError⟩

/-- Build the middle/zero KSK branch from one dense prefix-LWE transcript. -/
def secondPrefixBuild {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype Prefix] [Fintype Suffix]
    (maps : PrefixMaps R Prefix Suffix Factor) :
    Bool → SecondPrefixCoins R Suffix Factor →
      (Matrix Prefix Factor R × (Factor → R)) →
        ProbComp (DenseView R Prefix Suffix Factor) :=
  fun branch coins transcript ↦
    let suffixBody := coins.gadget.transpose *ᵥ coins.suffixSecret
    pure
      { gadget := coins.gadget
        brkBody := suffixBody + coins.brkError
        prefixMask := transcript.1 - maps.ksk coins.gadget
        kskBody := transcript.2 + coins.brkError + branchVector branch suffixBody }

/-- The second prefix constructor reproduces the middle/zero endpoints on a real dense-LWE
source.  The proof only commutes independent samples and applies the affine body identity. -/
theorem secondPrefixBuild_real_evalDist
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) (branch : Bool) :
    evalDist (constructedView
        (secondPrefixCoinsSampler gadgetSampler suffixSecretSampler brkErrorSampler)
        (LearningWithErrors.distr
          (prefixProblem prefixSecretSampler correctionSampler))
        (secondPrefixBuild maps) branch) =
      evalDist (view gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
        correctionSampler maps false branch) := by
  let source := LearningWithErrors.distr
    (prefixProblem prefixSecretSampler correctionSampler)
  let coins := secondPrefixCoinsSampler
    gadgetSampler suffixSecretSampler brkErrorSampler
  have hswap :
      evalDist (constructedView coins source (secondPrefixBuild maps) branch) =
        evalDist (coins >>= fun coin ↦
          source >>= fun transcript ↦ secondPrefixBuild maps branch coin transcript) := by
    unfold constructedView
    exact OracleComp.DeferredSampling.evalDist_bind_comm source coins _
  rw [hswap]
  simp only [coins, source, secondPrefixCoinsSampler, LearningWithErrors.distr,
    prefixProblem, secondPrefixBuild, view, assemble, branchVector,
    Bool.false_eq_true, if_false, bind_assoc, monad_norm]
  refine evalDist_bind_congr' gadgetSampler fun gadget ↦ ?_
  refine evalDist_bind_congr' suffixSecretSampler fun suffixSecret ↦ ?_
  refine evalDist_bind_congr' brkErrorSampler fun brkError ↦ ?_
  let leftFinish : Matrix Prefix Factor R → (Prefix → R) →
      ProbComp (DenseView R Prefix Suffix Factor) := fun prefixMask
      (prefixSecret : Prefix → R) ↦
    correctionSampler >>= fun correction ↦ pure
      { gadget := gadget
        brkBody := gadget.transpose *ᵥ suffixSecret + brkError
        prefixMask := prefixMask - maps.ksk gadget
        kskBody := (prefixMask.transpose *ᵥ prefixSecret + correction) + brkError +
          branchVector branch (gadget.transpose *ᵥ suffixSecret) }
  let rightFinish : (Prefix → R) → Matrix Prefix Factor R →
      ProbComp (DenseView R Prefix Suffix Factor) := fun prefixSecret
      (prefixMask : Matrix Prefix Factor R) ↦
    correctionSampler >>= fun correction ↦ pure
      { gadget := gadget
        brkBody := gadget.transpose *ᵥ suffixSecret + brkError
        prefixMask := prefixMask
        kskBody := ((prefixMask + maps.ksk gadget).transpose *ᵥ prefixSecret +
          branchVector branch (gadget.transpose *ᵥ suffixSecret)) + brkError + correction }
  calc
    evalDist (($ᵗ (Matrix Prefix Factor R)) >>= fun prefixMask ↦
        prefixSecretSampler >>= fun prefixSecret ↦ leftFinish prefixMask prefixSecret) =
      evalDist (prefixSecretSampler >>= fun prefixSecret ↦
        ($ᵗ (Matrix Prefix Factor R)) >>= fun prefixMask ↦
          leftFinish prefixMask prefixSecret) :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = evalDist (prefixSecretSampler >>= fun prefixSecret ↦
        (subMatrixEquiv (maps.ksk gadget) <$> ($ᵗ (Matrix Prefix Factor R))) >>=
          rightFinish prefixSecret) := by
      refine evalDist_bind_congr' prefixSecretSampler fun prefixSecret ↦ ?_
      simp only [leftFinish, rightFinish, map_eq_bind_pure_comp, bind_assoc]
      refine evalDist_bind_congr' ($ᵗ (Matrix Prefix Factor R)) fun prefixMask ↦ ?_
      simp [subMatrixEquiv, Matrix.transpose_sub, add_comm, add_left_comm]
    _ = evalDist (prefixSecretSampler >>= fun prefixSecret ↦
        ($ᵗ (Matrix Prefix Factor R)) >>= rightFinish prefixSecret) := by
      refine evalDist_bind_congr' prefixSecretSampler fun prefixSecret ↦ ?_
      rw [evalDist_bind, subMatrix_uniform_evalDist (maps.ksk gadget), ← evalDist_bind]
    _ = _ := by
      simp [rightFinish, branchVector]

/-- On a uniform dense-prefix source, adding or omitting the fixed suffix body is an exact
translation of the complete uniform body vector. -/
theorem secondPrefixBuild_uniform_evalDist
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) :
    evalDist (constructedView
        (secondPrefixCoinsSampler gadgetSampler suffixSecretSampler brkErrorSampler)
        (LearningWithErrors.uniformDistr
          (prefixProblem prefixSecretSampler correctionSampler))
        (secondPrefixBuild maps) true) =
      evalDist (constructedView
        (secondPrefixCoinsSampler gadgetSampler suffixSecretSampler brkErrorSampler)
        (LearningWithErrors.uniformDistr
          (prefixProblem prefixSecretSampler correctionSampler))
        (secondPrefixBuild maps) false) := by
  let source := LearningWithErrors.uniformDistr
    (prefixProblem prefixSecretSampler correctionSampler)
  let coins := secondPrefixCoinsSampler
    gadgetSampler suffixSecretSampler brkErrorSampler
  have hswap (branch : Bool) :
      evalDist (constructedView coins source (secondPrefixBuild maps) branch) =
        evalDist (coins >>= fun coin ↦
          source >>= fun transcript ↦ secondPrefixBuild maps branch coin transcript) := by
    unfold constructedView
    exact OracleComp.DeferredSampling.evalDist_bind_comm source coins _
  rw [hswap true, hswap false]
  simp only [coins, source, secondPrefixCoinsSampler, LearningWithErrors.uniformDistr,
    prefixProblem, secondPrefixBuild, bind_assoc, monad_norm]
  refine evalDist_bind_congr' gadgetSampler fun gadget ↦ ?_
  refine evalDist_bind_congr' suffixSecretSampler fun suffixSecret ↦ ?_
  refine evalDist_bind_congr' brkErrorSampler fun brkError ↦ ?_
  refine evalDist_bind_congr' ($ᵗ (Matrix Prefix Factor R)) fun prefixMask ↦ ?_
  let finishFalse : (Factor → R) → ProbComp (DenseView R Prefix Suffix Factor) :=
    fun body ↦ pure
      { gadget := gadget
        brkBody := gadget.transpose *ᵥ suffixSecret + brkError
        prefixMask := prefixMask - maps.ksk gadget
        kskBody := body + brkError }
  calc
    evalDist (($ᵗ (Factor → R)) >>= fun body ↦ pure
        { gadget := gadget
          brkBody := gadget.transpose *ᵥ suffixSecret + brkError
          prefixMask := prefixMask - maps.ksk gadget
          kskBody := body + brkError + gadget.transpose *ᵥ suffixSecret }) =
      evalDist ((addVectorEquiv (gadget.transpose *ᵥ suffixSecret) <$>
        ($ᵗ (Factor → R))) >>= finishFalse) := by
      simp [finishFalse, addVectorEquiv, map_eq_bind_pure_comp,
        add_comm, add_left_comm]
    _ = evalDist (($ᵗ (Factor → R)) >>= finishFalse) := by
      rw [evalDist_bind, addVector_uniform_evalDist
        (gadget.transpose *ᵥ suffixSecret), ← evalDist_bind]
    _ = _ := by
      simp [finishFalse, branchVector]

/-- Exact public constructor for the real-to-zero aligned-KSK hop. -/
noncomputable def secondPrefixConstructor
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor) :
    PublicViewConstructor
      (prefixProblem prefixSecretSampler correctionSampler)
      (secondPrefixCoinsSampler gadgetSampler suffixSecretSampler brkErrorSampler)
      (alignedViews gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
        correctionSampler maps).second :=
  PublicViewConstructor.ofExact (secondPrefixBuild maps)
    (fun branch ↦ Bool.casesOn branch
      (by simpa [AlignedViews.second, branchView, alignedViews] using
          secondPrefixBuild_real_evalDist gadgetSampler suffixSecretSampler brkErrorSampler
            prefixSecretSampler correctionSampler maps false)
      (by simpa [AlignedViews.second, branchView, alignedViews] using
          secondPrefixBuild_real_evalDist gadgetSampler suffixSecretSampler brkErrorSampler
            prefixSecretSampler correctionSampler maps true))
    (secondPrefixBuild_uniform_evalDist gadgetSampler suffixSecretSampler brkErrorSampler
      prefixSecretSampler correctionSampler maps)

/-! ## Concrete complete-view security bound -/

/-- The dense source-aligned correlated view is reduced exactly to one structured suffix
problem and two dense prefix-LWE problems.  There is no rowwise hybrid, guessed prefix, seeded
mask idealization, or statistical constructor defect in this theorem. -/
theorem endpointAdvantage_le_three_sources
    {R Prefix Suffix Factor : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Prefix] [DecidableEq Prefix]
    [Fintype Suffix] [DecidableEq Suffix]
    [Fintype Factor] [DecidableEq Factor]
    [SampleableType (Matrix Prefix Factor R)]
    (gadgetSampler : ProbComp (Matrix Suffix Factor R))
    (suffixSecretSampler : ProbComp (Suffix → R))
    (brkErrorSampler : ProbComp (Factor → R))
    (prefixSecretSampler : ProbComp (Prefix → R))
    (correctionSampler : ProbComp (Factor → R))
    (maps : PrefixMaps R Prefix Suffix Factor)
    (distinguisher : Distinguisher (DenseView R Prefix Suffix Factor)) :
    targetAdvantage
        (alignedViews gadgetSampler suffixSecretSampler brkErrorSampler prefixSecretSampler
          correctionSampler maps).endpoints distinguisher ≤
      2 * LearningWithErrors.advantage
        (suffixProblem gadgetSampler suffixSecretSampler brkErrorSampler)
        ((suffixConstructor gadgetSampler suffixSecretSampler brkErrorSampler
          prefixSecretSampler correctionSampler maps).reduction distinguisher) +
      2 * LearningWithErrors.advantage
        (prefixProblem prefixSecretSampler correctionSampler)
        ((randomPrefixConstructor gadgetSampler suffixSecretSampler brkErrorSampler
          prefixSecretSampler correctionSampler maps).reduction distinguisher) +
      2 * LearningWithErrors.advantage
        (prefixProblem prefixSecretSampler correctionSampler)
        ((secondPrefixConstructor gadgetSampler suffixSecretSampler brkErrorSampler
          prefixSecretSampler correctionSampler maps).reduction distinguisher) := by
  let views := alignedViews gadgetSampler suffixSecretSampler brkErrorSampler
    prefixSecretSampler correctionSampler maps
  let suffixC := suffixConstructor gadgetSampler suffixSecretSampler brkErrorSampler
    prefixSecretSampler correctionSampler maps
  let randomC := randomPrefixConstructor gadgetSampler suffixSecretSampler brkErrorSampler
    prefixSecretSampler correctionSampler maps
  let secondC := secondPrefixConstructor gadgetSampler suffixSecretSampler brkErrorSampler
    prefixSecretSampler correctionSampler maps
  have h := SourceAlignedBRKKSKJointLaw.CompleteView.alignedJointSecurity_correlated
    views suffixC randomC secondC distinguisher 0
    (fun _branch ↦ rfl) (fun _branch ↦ rfl) rfl
    (by simp [secondC, secondPrefixConstructor, PublicViewConstructor.ofExact])
  simpa only [views, suffixC, randomC, secondC, add_zero] using h

end

end FormalProof4FHE.TFHE.SourceAlignedDenseJointLaw
