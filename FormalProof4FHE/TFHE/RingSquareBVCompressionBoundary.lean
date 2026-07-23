/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareBVQuadraticKDM
import FormalProof4FHE.TFHE.RingSquareRGSWSecurity

/-!
# The Native Two-Component Compression Boundary

The BV quadratic telescope proves ordinary-RLWE security while retaining a third ciphertext
component.  Native rank-one RGSW upper rows have only a mask and a body.  This file isolates the
precise missing bridge: a public transformation from the joint BV-square/ordinary-zero view to
the complete native stripped RGSW view.

The source view is itself an exact public image of `3 * levels` ordinary rank-one RLWE samples:
two samples form each BV quadratic ciphertext and one additional sample supplies each native
lower zero row.  Its uniform image is proved by an explicit bijection with one retained mask per
level.  Consequently any compression that

* maps this real source law to the native narrow-error square law, and
* maps the uniform source carrier to the uniform native carrier

would give a lossless proof of native `RGSW_S(-S)` security from ordinary RLWE.  Those two
distributional obligations are exposed as `ExactNativeCompression`; no witness is assumed here.

The canonical operation that merely drops the third BV component is also analyzed.  Its native
phase contains the uniform second mask times `S²`, rather than the requested gadget times `S²`.
Thus the obvious compression does not preserve the narrow square ciphertext.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.BVCompressionBoundary

noncomputable local instance sampleableCiphertext
    {R : Type} [SampleableType R] {dimension : ℕ} :
    SampleableType (TLWE.Ciphertext R dimension) :=
  SampleableType.ofEquiv (TLWE.ciphertextEquiv R dimension)

/-! ## Why simply deleting the third component fails -/

/-- Interpret the first two BV coefficients as a native row and discard the quadratic
coefficient.  Negating the linear coefficient makes native phase evaluation equal
`c₀ + c₁ S`. -/
def dropThird {R : Type} [Ring R] (ciphertext : BVQuadraticKDM.Ciphertext R) :
    TLWE.Ciphertext R 1 :=
  ⟨fun _ ↦ -ciphertext 1, ciphertext 0⟩

/-- Dropping the third coefficient removes exactly `c₂ S²` from the BV phase. -/
theorem phase_dropThird {R : Type} [CommRing R]
    (secret : R) (ciphertext : BVQuadraticKDM.Ciphertext R) :
    TLWE.phase ![secret] (dropThird ciphertext) =
      BVQuadraticKDM.phase secret ciphertext - ciphertext 2 * secret * secret := by
  simp [TLWE.phase, dropThird, BVQuadraticKDM.phase, dotProduct]
  ring

/-- On a BV telescope ciphertext, deleting the third component replaces the intended gadget
coefficient by the uniform second public mask. -/
theorem phase_dropThird_assemble {R : Type} [CommRing R]
    (secret : R) (challenge : Matrix (Fin 1) (Fin 2) R)
    (error : Fin 2 → R) (gadget : R) :
    TLWE.phase ![secret]
        (dropThird (BVQuadraticKDM.assemble secret challenge error gadget)) =
      challenge 0 1 * secret * secret + error 0 + error 1 * secret := by
  simp [TLWE.phase, dropThird, BVQuadraticKDM.assemble, dotProduct]
  ring

/-- Therefore the dropped row has the desired narrow square phase only if the public second-mask
residual annihilates `S²`. -/
theorem dropThird_residual {R : Type} [CommRing R]
    (secret : R) (challenge : Matrix (Fin 1) (Fin 2) R)
    (error : Fin 2 → R) (gadget : R) :
    TLWE.phase ![secret]
        (dropThird (BVQuadraticKDM.assemble secret challenge error gadget)) -
        (gadget * secret * secret + error 0 + error 1 * secret) =
      (challenge 0 1 - gadget) * secret * secret := by
  rw [phase_dropThird_assemble]
  ring

/-! ## The joint BV-square / native-zero source view -/

/-- One native lower zero row per gadget level. -/
abbrev LowerRows (R : Type) (levels : ℕ) :=
  Fin levels → TLWE.Ciphertext R 1

/-- The source made from secure BV square ciphertexts and ordinary lower zero rows. -/
abbrev SourceView (R : Type) (levels : ℕ) :=
  BVQuadraticKDM.Batch.Ciphertexts R levels × LowerRows R levels

/-- Repackage a rank-one transcript as individual native rows. -/
def lowerRowsEquiv (R : Type) (levels : ℕ) :
    LWE.BatchTranscript R 1 levels ≃ LowerRows R levels where
  toFun transcript := fun level ↦
    ⟨fun _ ↦ transcript.1 0 level, transcript.2 level⟩
  invFun rows :=
    (fun _ level ↦ (rows level).mask 0, fun level ↦ (rows level).body)
  left_inv transcript := by
    rcases transcript with ⟨challenge, output⟩
    apply Prod.ext
    · funext row level
      rw [Subsingleton.elim row 0]
    · rfl
  right_inv rows := by
    funext level
    rw [TLWE.Ciphertext.mk.injEq]
    constructor
    · funext coordinate
      rw [Subsingleton.elim coordinate 0]
    · rfl

/-- Split `3 * levels` ordinary samples into the first two BV blocks and the final native-zero
block, then telescope the BV portion. -/
def sourceTelescope {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (transcript : LWE.BatchTranscript R 1 ((levels + levels) + levels)) :
    SourceView R levels :=
  let blocks := LWE.splitBatchTranscriptAt transcript
  (BVQuadraticKDM.Batch.telescope gadget blocks.1,
    lowerRowsEquiv R levels blocks.2)

/-- First BV sample position inside the complete `3 * levels` ordinary transcript. -/
def firstBVIndex {levels : ℕ} (level : Fin levels) :
    Fin ((levels + levels) + levels) :=
  Fin.castAdd levels (BVQuadraticKDM.Batch.firstIndex level)

/-- Second BV sample position inside the complete ordinary transcript. -/
def secondBVIndex {levels : ℕ} (level : Fin levels) :
    Fin ((levels + levels) + levels) :=
  Fin.castAdd levels (BVQuadraticKDM.Batch.secondIndex level)

/-- Native lower-row position inside the complete ordinary transcript. -/
def lowerIndex {levels : ℕ} (level : Fin levels) :
    Fin ((levels + levels) + levels) :=
  Fin.natAdd (levels + levels) level

/-- The upper part of a real source transcript has exactly the gadget-scaled square phase and
the two original narrow errors. -/
theorem phase_sourceTelescope_upper {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R)
    (challenge : Matrix (Fin 1) (Fin ((levels + levels) + levels)) R)
    (error : Fin ((levels + levels) + levels) → R)
    (gadget : Fin levels → R) (level : Fin levels) :
    BVQuadraticKDM.phase (secret 0)
        ((sourceTelescope gadget (challenge, vecMul secret challenge + error)).1 level) =
      gadget level * secret 0 * secret 0 + error (firstBVIndex level) +
        error (secondBVIndex level) * secret 0 := by
  simp [sourceTelescope, LWE.splitBatchTranscriptAt, LWE.splitBatchColumns,
    LWE.splitBatchOutput, BVQuadraticKDM.Batch.telescope,
    BVQuadraticKDM.Batch.levelTranscript, BVQuadraticKDM.Batch.levelChallenge,
    BVQuadraticKDM.Batch.levelOutput, BVQuadraticKDM.telescope,
    BVQuadraticKDM.phase, firstBVIndex, secondBVIndex,
    BVQuadraticKDM.Batch.firstIndex, BVQuadraticKDM.Batch.secondIndex,
    Matrix.vecMul, dotProduct]
  ring

/-- Each lower source row is an ordinary zero-message row with its original narrow error. -/
theorem phase_sourceTelescope_lower {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R)
    (challenge : Matrix (Fin 1) (Fin ((levels + levels) + levels)) R)
    (error : Fin ((levels + levels) + levels) → R)
    (gadget : Fin levels → R) (level : Fin levels) :
    TLWE.phase secret
        ((sourceTelescope gadget (challenge, vecMul secret challenge + error)).2 level) =
      error (lowerIndex level) := by
  simp [sourceTelescope, lowerRowsEquiv, LWE.splitBatchTranscriptAt,
    LWE.splitBatchColumns, LWE.splitBatchOutput, TLWE.phase, lowerIndex,
    Matrix.vecMul, dotProduct]

/-- Retain the unused first BV mask at every level. -/
def sourceTelescopeWithFiber {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (transcript : LWE.BatchTranscript R 1 ((levels + levels) + levels)) :
    SourceView R levels × (Fin levels → R) :=
  let blocks := LWE.splitBatchTranscriptAt transcript
  let bv := BVQuadraticKDM.Batch.telescopeWithFiber gadget blocks.1
  ((bv.1, lowerRowsEquiv R levels blocks.2), bv.2)

/-- Inverse of the joint telescope with its retained BV fiber. -/
def unsourceTelescopeWithFiber {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R)
    (output : SourceView R levels × (Fin levels → R)) :
    LWE.BatchTranscript R 1 ((levels + levels) + levels) :=
  LWE.appendBatchTranscriptAt
    (BVQuadraticKDM.Batch.untelescopeWithFiber gadget (output.1.1, output.2),
      (lowerRowsEquiv R levels).symm output.1.2)

@[simp]
theorem unsourceTelescopeWithFiber_sourceTelescopeWithFiber
    {R : Type} [Ring R] {levels : ℕ} (gadget : Fin levels → R)
    (transcript : LWE.BatchTranscript R 1 ((levels + levels) + levels)) :
    unsourceTelescopeWithFiber gadget (sourceTelescopeWithFiber gadget transcript) =
      transcript := by
  simp [sourceTelescopeWithFiber, unsourceTelescopeWithFiber]

@[simp]
theorem sourceTelescopeWithFiber_unsourceTelescopeWithFiber
    {R : Type} [Ring R] {levels : ℕ} (gadget : Fin levels → R)
    (output : SourceView R levels × (Fin levels → R)) :
    sourceTelescopeWithFiber gadget (unsourceTelescopeWithFiber gadget output) = output := by
  rcases output with ⟨⟨bv, lower⟩, fiber⟩
  simp [sourceTelescopeWithFiber, unsourceTelescopeWithFiber]

/-- The joint source telescope plus one first-mask fiber per level is bijective. -/
theorem sourceTelescopeWithFiber_bijective
    {R : Type} [Ring R] {levels : ℕ} (gadget : Fin levels → R) :
    Function.Bijective (sourceTelescopeWithFiber gadget :
      LWE.BatchTranscript R 1 ((levels + levels) + levels) →
        SourceView R levels × (Fin levels → R)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unsourceTelescopeWithFiber gadget,
      unsourceTelescopeWithFiber_sourceTelescopeWithFiber gadget,
      sourceTelescopeWithFiber_unsourceTelescopeWithFiber gadget⟩

/-- The joint public telescope maps a uniform `3 * levels` ordinary transcript to a uniform
BV-square/native-zero source view. -/
theorem sourceTelescope_uniform_evalDist {R : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (gadget : Fin levels → R) :
    evalDist (sourceTelescope gadget <$>
        ($ᵗ (LWE.BatchTranscript R 1 ((levels + levels) + levels)))) =
      evalDist ($ᵗ (SourceView R levels)) := by
  have hFiber :
      evalDist (sourceTelescopeWithFiber gadget <$>
          ($ᵗ (LWE.BatchTranscript R 1 ((levels + levels) + levels)))) =
        evalDist ($ᵗ (SourceView R levels × (Fin levels → R))) :=
    evalDist_map_bijective_uniform_cross
      (α := LWE.BatchTranscript R 1 ((levels + levels) + levels))
      (β := SourceView R levels × (Fin levels → R))
      (sourceTelescopeWithFiber gadget)
      (sourceTelescopeWithFiber_bijective gadget)
  calc
    evalDist (sourceTelescope gadget <$>
        ($ᵗ (LWE.BatchTranscript R 1 ((levels + levels) + levels)))) =
      evalDist (Prod.fst <$> (sourceTelescopeWithFiber gadget <$>
        ($ᵗ (LWE.BatchTranscript R 1 ((levels + levels) + levels))))) := by
        apply congrArg evalDist
        rw [Functor.map_map]
        rfl
    _ = evalDist (Prod.fst <$>
        ($ᵗ (SourceView R levels × (Fin levels → R)))) :=
      evalDist_map_eq_of_evalDist_eq hFiber Prod.fst
    _ = evalDist ($ᵗ (SourceView R levels)) := evalDist_map_fst_uniformSample_prod

/-! ## The explicit native compression interface -/

/-- One native upper row per gadget level. -/
abbrev UpperRows (R : Type) (levels : ℕ) :=
  Fin levels → TLWE.Ciphertext R 1

/-- A public candidate for compressing all three-component BV square ciphertexts to native
two-component upper rows. -/
abbrev UpperCompression (R : Type) (levels : ℕ) :=
  BVQuadraticKDM.Batch.Ciphertexts R levels → UpperRows R levels

/-- Install compressed upper rows and pass the ordinary lower zero rows through unchanged. -/
def compressView {R : Type} {levels : ℕ}
    (compression : UpperCompression R levels) (view : SourceView R levels) :
    PreimageCompiler.Full.TargetBatch R levels :=
  TLWE.batchOfRows fun row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then compression view.1 indexed.2 else view.2 indexed.2

@[simp]
theorem entry_compressView_upper {R : Type} {levels : ℕ}
    (compression : UpperCompression R levels) (view : SourceView R levels)
    (level : Fin levels) :
    TLWE.entry (compressView compression view) (PreimageCompiler.Full.upperRow level) =
      compression view.1 level := by
  simp [compressView]

@[simp]
theorem entry_compressView_lower {R : Type} {levels : ℕ}
    (compression : UpperCompression R levels) (view : SourceView R levels)
    (level : Fin levels) :
    TLWE.entry (compressView compression view) (PreimageCompiler.Full.lowerRow level) =
      view.2 level := by
  simp [compressView]

/-- The canonical but unsuccessful component-deletion candidate. -/
def dropThirdBatch {R : Type} [Ring R] {levels : ℕ} : UpperCompression R levels :=
  fun ciphertexts level ↦ dropThird (ciphertexts level)

/-- Its upper-row phase has the exact third-component residual already exposed above. -/
theorem phase_dropThirdBatch {R : Type} [CommRing R] {levels : ℕ}
    (secret : R) (ciphertexts : BVQuadraticKDM.Batch.Ciphertexts R levels)
    (level : Fin levels) :
    TLWE.phase ![secret] (dropThirdBatch ciphertexts level) =
      BVQuadraticKDM.phase secret (ciphertexts level) -
        ciphertexts level 2 * secret * secret :=
  phase_dropThird secret (ciphertexts level)

/-- Ordinary rank-one RLWE source problem: two samples per BV upper row and one per native lower
row. -/
abbrev ordinaryProblem {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) :=
  LWE.embeddedBatchProblem 1 ((levels + levels) + levels)
    secretSampler embed errorSampler

/-- Real joint source law obtained by publicly telescoping ordinary RLWE. -/
def sourceSampler {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    ProbComp (SourceView R levels) := do
  let transcript ← LearningWithErrors.distr
    (ordinaryProblem levels secretSampler embed errorSampler)
  pure (sourceTelescope gadget transcript)

/-- Apply a proposed native compression to the secure joint source law. -/
def compressedSampler {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels) :
    ProbComp (PreimageCompiler.Full.TargetBatch R levels) := do
  let view ← sourceSampler levels secretSampler embed errorSampler gadget
  pure (compressView compression view)

/-- Uniform preservation required of a valid public two-component compression. -/
def UniformPreserving {R : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (compression : UpperCompression R levels) : Prop :=
  evalDist (compressView compression <$> ($ᵗ (SourceView R levels))) =
    evalDist ($ᵗ (PreimageCompiler.Full.TargetBatch R levels))

/-- Exact bridge required to identify the compressed real law with fresh native narrow-error
square rows.  This is the unresolved research obligation, stated separately from ordinary RLWE. -/
structure ExactNativeCompression {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels) : Prop where
  uniform_preserving : UniformPreserving compression
  real_evalDist :
    evalDist (compressedSampler levels secretSampler embed errorSampler gadget compression) =
      evalDist (PreimageCompiler.Full.actualSquareBatchSampler
        levels secretSampler embed errorSampler gadget)

/-- Feed a native distinguisher through a proposed compression and the public source telescope. -/
def reduction {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} {secretSampler : ProbComp Secret} {embed : Secret → Fin 1 → R}
    {errorSampler : ProbComp R} (gadget : Fin levels → R)
    (compression : UpperCompression R levels)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) :
    LearningWithErrors.Adversary
      (ordinaryProblem levels secretSampler embed errorSampler) :=
  fun transcript ↦
    distinguisher (compressView compression (sourceTelescope gadget transcript))

/-- Canonical uniform transcript form for the `3 * levels` ordinary problem. -/
theorem ordinary_uniformDistr_eq_uniformSample {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (ordinaryProblem levels secretSampler embed errorSampler) =
      ($ᵗ (LWE.BatchTranscript R 1 ((levels + levels) + levels))) := by
  unfold LearningWithErrors.uniformDistr ordinaryProblem LWE.embeddedBatchProblem
  have uniformProduct :
      ($ᵗ (LWE.BatchTranscript R 1 ((levels + levels) + levels)) :
        ProbComp (LWE.BatchTranscript R 1 ((levels + levels) + levels))) =
      Prod.mk <$> ($ᵗ Matrix (Fin 1) (Fin ((levels + levels) + levels)) R) <*>
        ($ᵗ (Fin ((levels + levels) + levels) → R)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The reduction's real game is the compressed source sampler followed by the native
distinguisher. -/
theorem reduction_game0_evalDist_eq_compressedSampler_bind {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) :
    evalDist (LearningWithErrors.game0
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget compression distinguisher)) =
      evalDist (compressedSampler levels secretSampler embed errorSampler gadget compression >>=
        distinguisher) := by
  apply congrArg evalDist
  simp [LearningWithErrors.game0, reduction, compressedSampler, sourceSampler,
    bind_assoc, monad_norm]

/-- A uniform-preserving compression makes the reduction's uniform branch exactly the native
uniform target game. -/
theorem reduction_game1_evalDist_eq_uniformGame {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels)
    (hCompression : UniformPreserving compression) :
    evalDist (LearningWithErrors.game1
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget compression distinguisher)) =
      evalDist (PreimageCompiler.Full.uniformGame distinguisher) := by
  rw [LearningWithErrors.game1,
    ordinary_uniformDistr_eq_uniformSample levels secretSampler embed errorSampler]
  simp only [reduction, PreimageCompiler.Full.uniformGame]
  let transcripts : ProbComp
      (LWE.BatchTranscript R 1 ((levels + levels) + levels)) :=
    $ᵗ (LWE.BatchTranscript R 1 ((levels + levels) + levels))
  let sources : ProbComp (SourceView R levels) := $ᵗ (SourceView R levels)
  let targets : ProbComp (PreimageCompiler.Full.TargetBatch R levels) :=
    $ᵗ (PreimageCompiler.Full.TargetBatch R levels)
  have hSource :
      evalDist (sourceTelescope gadget <$> transcripts) = evalDist sources := by
    simpa only [transcripts, sources] using sourceTelescope_uniform_evalDist gadget
  have hCompressed :
      evalDist (compressView compression <$>
          (sourceTelescope gadget <$> transcripts)) = evalDist targets := by
    calc
      _ = evalDist (compressView compression <$> sources) :=
        evalDist_map_eq_of_evalDist_eq hSource (compressView compression)
      _ = _ := by
        simpa [sources, targets, UniformPreserving] using hCompression
  rw [show
      (transcripts >>= fun transcript ↦
        distinguisher (compressView compression (sourceTelescope gadget transcript))) =
      ((compressView compression <$> (sourceTelescope gadget <$> transcripts)) >>=
        distinguisher) by simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, hCompressed, ← evalDist_bind]

/-- An exact compression identifies the native real game with the reduction's real game. -/
theorem actualSquareGame_evalDist_eq_reduction_game0_of_exactCompression
    {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels)
    (hCompression : ExactNativeCompression levels secretSampler embed errorSampler
      gadget compression) :
    evalDist (PreimageCompiler.Full.actualSquareGame levels secretSampler embed errorSampler
        gadget distinguisher) =
      evalDist (LearningWithErrors.game0
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget compression distinguisher)) := by
  rw [reduction_game0_evalDist_eq_compressedSampler_bind]
  unfold PreimageCompiler.Full.actualSquareGame
  simp only [evalDist_bind]
  rw [hCompression.real_evalDist]

/-- **Conditional completion theorem.**  Any witness of the explicit native two-component
compression obligations proves the stripped native square game losslessly from ordinary
rank-one RLWE with `3 * levels` samples. -/
theorem actualSquareAdvantage_eq_batchRLWE_of_exactCompression
    {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels)
    (hCompression : ExactNativeCompression levels secretSampler embed errorSampler
      gadget compression) :
    PreimageCompiler.Full.actualSquareAdvantage levels secretSampler embed errorSampler
        gadget distinguisher =
      LearningWithErrors.advantage
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget compression distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold PreimageCompiler.Full.actualSquareAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (actualSquareGame_evalDist_eq_reduction_game0_of_exactCompression levels secretSampler
        embed errorSampler gadget compression distinguisher hCompression) true,
    evalDist_ext_iff.mp
      (reduction_game1_evalDist_eq_uniformGame levels secretSampler embed errorSampler gadget
        compression distinguisher hCompression.uniform_preserving) true]

/-! ## Approximate compression: the remaining term as a literal distance -/

/-- Statistical gap between the compressed secure source view and fresh native narrow-error
square rows. -/
noncomputable def compressionGap {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels) : ℝ :=
  tvDist
    (PreimageCompiler.Full.actualSquareBatchSampler
      levels secretSampler embed errorSampler gadget)
    (compressedSampler levels secretSampler embed errorSampler gadget compression)

/-- Distinguisher game for the compressed secure source law. -/
def compressedGame {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) : ProbComp Bool :=
  compressedSampler levels secretSampler embed errorSampler gadget compression >>=
    distinguisher

/-- Under uniform preservation, the compressed-view advantage is exactly ordinary batch RLWE. -/
theorem compressedAdvantage_eq_batchRLWE {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels)
    (hCompression : UniformPreserving compression) :
    (compressedGame levels secretSampler embed errorSampler gadget compression
        distinguisher).boolDistAdvantage
        (PreimageCompiler.Full.uniformGame distinguisher) =
      LearningWithErrors.advantage
        (ordinaryProblem levels secretSampler embed errorSampler)
        (reduction gadget compression distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage compressedGame
  rw [evalDist_ext_iff.mp
      (reduction_game0_evalDist_eq_compressedSampler_bind levels secretSampler embed
        errorSampler gadget compression distinguisher).symm true,
    evalDist_ext_iff.mp
      (reduction_game1_evalDist_eq_uniformGame levels secretSampler embed errorSampler gadget
        compression distinguisher hCompression) true]

/-- **Quantitative compression boundary.**  Native stripped-square security is ordinary RLWE plus
exactly the statistical price of compressing the BV source law to the native narrow-error law. -/
theorem actualSquareAdvantage_le_compressionGap_add_batchRLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (compression : UpperCompression R levels)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels)
    (hCompression : UniformPreserving compression) :
    PreimageCompiler.Full.actualSquareAdvantage levels secretSampler embed errorSampler
        gadget distinguisher ≤
      compressionGap levels secretSampler embed errorSampler gadget compression +
        LearningWithErrors.advantage
          (ordinaryProblem levels secretSampler embed errorSampler)
          (reduction gadget compression distinguisher) := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (PreimageCompiler.Full.actualSquareGame levels secretSampler embed errorSampler gadget
      distinguisher)
    (compressedGame levels secretSampler embed errorSampler gadget compression distinguisher)
    (PreimageCompiler.Full.uniformGame distinguisher)
  have hComparison :
      (PreimageCompiler.Full.actualSquareGame levels secretSampler embed errorSampler gadget
          distinguisher).boolDistAdvantage
          (compressedGame levels secretSampler embed errorSampler gadget compression
            distinguisher) ≤
        compressionGap levels secretSampler embed errorSampler gadget compression := by
    refine (abs_probOutput_toReal_sub_le_tvDist _ _).trans ?_
    unfold PreimageCompiler.Full.actualSquareGame compressedGame compressionGap
    exact tvDist_bind_right_le distinguisher
      (PreimageCompiler.Full.actualSquareBatchSampler
        levels secretSampler embed errorSampler gadget)
      (compressedSampler levels secretSampler embed errorSampler gadget compression)
  calc
    PreimageCompiler.Full.actualSquareAdvantage levels secretSampler embed errorSampler
        gadget distinguisher ≤
      (PreimageCompiler.Full.actualSquareGame levels secretSampler embed errorSampler gadget
          distinguisher).boolDistAdvantage
          (compressedGame levels secretSampler embed errorSampler gadget compression
            distinguisher) +
        (compressedGame levels secretSampler embed errorSampler gadget compression
          distinguisher).boolDistAdvantage
          (PreimageCompiler.Full.uniformGame distinguisher) := by
      simpa only [PreimageCompiler.Full.actualSquareAdvantage] using hTriangle
    _ ≤ compressionGap levels secretSampler embed errorSampler gadget compression +
        (compressedGame levels secretSampler embed errorSampler gadget compression
          distinguisher).boolDistAdvantage
          (PreimageCompiler.Full.uniformGame distinguisher) :=
      add_le_add hComparison le_rfl
    _ = _ := congrArg
      (fun value ↦ compressionGap levels secretSampler embed errorSampler gadget compression +
        value)
      (compressedAdvantage_eq_batchRLWE levels secretSampler embed errorSampler gadget
        compression distinguisher hCompression)

end FormalProof4FHE.TFHE.TGSW.RingSquare.BVCompressionBoundary
