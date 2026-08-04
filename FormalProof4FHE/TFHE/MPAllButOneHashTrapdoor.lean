/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BlockCategoricalHashCMUXSelfCircular
import FormalProof4FHE.TFHE.SubsetKeyTrapdoorTheorems
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Micciancio--Peikert All-But-One Hash Tags

This file installs the finite algebraic layer connecting a full-rank-difference digest encoding
to the tagged `G`-trapdoor identities in `SubsetKeyTrapdoorTheorems`.

For an encoding `F`, a programmed digest `yStar`, and a candidate digest `y`, the tag is

`D(y,yStar) = F(y) - F(yStar)`.

The corresponding tagged mask satisfies

`B_y + R A = D(y,yStar) G`.

Consequently the programmed candidate has an exact short-kernel relation, while every distinct
candidate has an invertible tag and can be normalized to an ordinary `G`-trapdoor.  The same
normalization removes the tag from the exact phase identity.  A determinant interface packages
the usual matrix full-rank-difference condition, including lifting invertibility through a local
ring homomorphism such as reduction to a residue field.

The last section composes a separately supplied tagged-mode defect with the existing hash-CMUX
and direct-projected security bounds.  This file deliberately does not assert:

* a concrete full-rank-difference family for the production ring;
* regularity of the trapdoor-generated public matrix;
* a finite CBD/Gaussian correction theorem; or
* a compiler from the tagged complete view to native nonce rows.

Those are cryptographic or analytic premises, not consequences of the all-but-one algebra.
-/

set_option autoImplicit false

open Matrix

namespace FormalProof4FHE.TFHE.MPAllButOneHashTrapdoor

noncomputable section

open SubsetKeyTrapdoorTheorems
open Native.BlockCategoricalHashCMUXSelfCircular

/-! ## Full-rank-difference encodings -/

/-- A linear full-rank-difference encoding.  Distinct digest values have a bijective difference
endomorphism.  Injectivity is retained explicitly so that the unique zero-tag statement does not
need an additional nontriviality assumption on the target module. -/
structure FullRankDifferenceEncoding
    (R Digest Target : Type)
    [CommRing R] [AddCommGroup Target] [Module R Target] where
  encode : Digest → Target →ₗ[R] Target
  encode_injective : Function.Injective encode
  difference_bijective : ∀ {left right : Digest}, left ≠ right →
    Function.Bijective (encode left - encode right)

namespace FullRankDifferenceEncoding

variable {R Digest Target : Type}
  [CommRing R] [AddCommGroup Target] [Module R Target]

/-- Candidate tag relative to the digest programmed as lossy. -/
def tagDifference
    (encoding : FullRankDifferenceEncoding R Digest Target)
    (candidate programmed : Digest) : Target →ₗ[R] Target :=
  encoding.encode candidate - encoding.encode programmed

@[simp]
theorem tagDifference_self
    (encoding : FullRankDifferenceEncoding R Digest Target)
    (digest : Digest) :
    encoding.tagDifference digest digest = 0 := by
  simp [tagDifference]

/-- The programmed digest is the unique candidate whose tag is zero. -/
theorem tagDifference_eq_zero_iff
    (encoding : FullRankDifferenceEncoding R Digest Target)
    (candidate programmed : Digest) :
    encoding.tagDifference candidate programmed = 0 ↔ candidate = programmed := by
  constructor
  · intro hzero
    apply encoding.encode_injective
    exact sub_eq_zero.mp hzero
  · rintro rfl
    simp

theorem tagDifference_ne_zero
    (encoding : FullRankDifferenceEncoding R Digest Target)
    {candidate programmed : Digest} (hne : candidate ≠ programmed) :
    encoding.tagDifference candidate programmed ≠ 0 := by
  exact (encoding.tagDifference_eq_zero_iff candidate programmed).not.mpr hne

theorem tagDifference_bijective
    (encoding : FullRankDifferenceEncoding R Digest Target)
    {candidate programmed : Digest} (hne : candidate ≠ programmed) :
    Function.Bijective (encoding.tagDifference candidate programmed) :=
  encoding.difference_bijective hne

/-- The invertible tag attached to a wrong candidate. -/
noncomputable def differenceEquiv
    (encoding : FullRankDifferenceEncoding R Digest Target)
    {candidate programmed : Digest} (hne : candidate ≠ programmed) :
    Target ≃ₗ[R] Target :=
  LinearEquiv.ofBijective
    (encoding.tagDifference candidate programmed)
    (encoding.tagDifference_bijective hne)

@[simp]
theorem differenceEquiv_apply
    (encoding : FullRankDifferenceEncoding R Digest Target)
    {candidate programmed : Digest} (hne : candidate ≠ programmed)
    (value : Target) :
    encoding.differenceEquiv hne value =
      encoding.tagDifference candidate programmed value :=
  rfl

@[simp]
theorem differenceEquiv_symm_apply_tagDifference
    (encoding : FullRankDifferenceEncoding R Digest Target)
    {candidate programmed : Digest} (hne : candidate ≠ programmed)
    (value : Target) :
    (encoding.differenceEquiv hne).symm
        (encoding.tagDifference candidate programmed value) = value := by
  exact (encoding.differenceEquiv hne).symm_apply_apply value

end FullRankDifferenceEncoding

/-! ## Matrix determinant interface -/

/-- Matrix form of a full-rank-difference encoding.  A unit determinant is the condition used by
the MP/module-trapdoor literature for every distinct pair of tags. -/
structure MatrixFullRankDifferenceEncoding
    (R Digest Index : Type)
    [CommRing R] [Fintype Index] [DecidableEq Index] where
  encode : Digest → Matrix Index Index R
  encode_injective : Function.Injective encode
  difference_det_isUnit : ∀ {left right : Digest}, left ≠ right →
    IsUnit (encode left - encode right).det

namespace MatrixFullRankDifferenceEncoding

variable {R Digest Index : Type}
  [CommRing R] [Fintype Index] [DecidableEq Index]

/-- A unit-determinant matrix encoding induces the abstract linear
full-rank-difference encoding on column vectors. -/
noncomputable def toLinear
    (encoding : MatrixFullRankDifferenceEncoding R Digest Index) :
    FullRankDifferenceEncoding R Digest (Index → R) where
  encode digest := Matrix.toLin' (encoding.encode digest)
  encode_injective := by
    intro left right heq
    apply encoding.encode_injective
    exact Matrix.toLin'.injective heq
  difference_bijective := by
    intro left right hne
    have hmatrix : IsUnit (encoding.encode left - encoding.encode right) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (encoding.difference_det_isUnit hne)
    have hlinear :
        Matrix.toLin' (encoding.encode left) -
            Matrix.toLin' (encoding.encode right) =
          Matrix.toLin' (encoding.encode left - encoding.encode right) := by
      exact (Matrix.toLin' :
        Matrix Index Index R ≃ₗ[R] ((Index → R) →ₗ[R] (Index → R))).map_sub _ _ |>.symm
    rw [hlinear]
    constructor
    · exact Matrix.mulVec_injective_of_isUnit hmatrix
    · exact (Matrix.mulVec_surjective_iff_isUnit).2 hmatrix

@[simp]
theorem toLinear_encode
    (encoding : MatrixFullRankDifferenceEncoding R Digest Index)
    (digest : Digest) :
    (encoding.toLinear.encode digest) = Matrix.toLin' (encoding.encode digest) :=
  rfl

/-- A local map reflects the unit determinant of every tag difference.  This is the reusable
step for lifting full-rank-difference matrices from a residue field to a power-of-two base ring. -/
def ofLocalMap
    {S : Type} [CommRing S]
    (hom : R →+* S) [IsLocalHom hom]
    (encode : Digest → Matrix Index Index R)
    (encode_injective : Function.Injective encode)
    (mapped_difference_det_isUnit : ∀ {left right : Digest}, left ≠ right →
      IsUnit (((encode left - encode right).map hom).det)) :
    MatrixFullRankDifferenceEncoding R Digest Index where
  encode := encode
  encode_injective := encode_injective
  difference_det_isUnit := by
    intro left right hne
    exact IsUnit.of_map hom _ (by
      rw [hom.map_det]
      exact mapped_difference_det_isUnit hne)

end MatrixFullRankDifferenceEncoding

/-! ## Digest-indexed MP masks and phases -/

section TaggedFamily

variable {R Digest Secret SourceRow TargetRow : Type}
  [CommRing R]
  [AddCommGroup Secret] [Module R Secret]
  [AddCommGroup SourceRow] [Module R SourceRow]
  [AddCommGroup TargetRow] [Module R TargetRow]

/-- MP mask `B_y = (F(y)-F(yStar))G - R A` for a candidate digest and a programmed digest. -/
def candidateMask
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    (candidate programmed : Digest) : Secret →ₗ[R] TargetRow :=
  taggedMask source gadget trapdoor
    (encoding.tagDifference candidate programmed)

/-- Exact candidate-tagged preimage identity
`B_y + R A = (F(y)-F(yStar))G`. -/
theorem candidateMask_add_trapdoor_comp_source
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    (candidate programmed : Digest) :
    candidateMask encoding source gadget trapdoor candidate programmed +
        trapdoor.comp source =
      (encoding.tagDifference candidate programmed).comp gadget := by
  exact taggedMask_add_trapdoor_comp_source source gadget trapdoor
    (encoding.tagDifference candidate programmed)

/-- The programmed candidate exposes an exact short-kernel relation.  Shortness is inherited
from the supplied trapdoor; this statement is the exact modular relation only. -/
theorem programmedCandidate_kernelRelation
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    (programmed : Digest) :
    candidateMask encoding source gadget trapdoor programmed programmed +
        trapdoor.comp source = 0 := by
  rw [candidateMask_add_trapdoor_comp_source]
  simp

@[simp]
theorem candidateMask_programmed
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    (programmed : Digest) :
    candidateMask encoding source gadget trapdoor programmed programmed =
      -trapdoor.comp source := by
  apply LinearMap.ext
  intro secret
  have hrelation := DFunLike.congr_fun
    (programmedCandidate_kernelRelation
      encoding source gadget trapdoor programmed) secret
  simpa only [LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, LinearMap.zero_apply, add_eq_zero_iff_eq_neg] using hrelation

/-- Exact tagged phase for every candidate digest. -/
theorem candidatePhase
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    (candidate programmed : Digest)
    (secret : Secret) (sourceError : SourceRow) (correction : TargetRow) :
    taggedBody trapdoor (source secret + sourceError) correction -
        candidateMask encoding source gadget trapdoor candidate programmed secret =
      -encoding.tagDifference candidate programmed (gadget secret) +
        correction - trapdoor sourceError := by
  exact taggedPhase source gadget trapdoor
    (encoding.tagDifference candidate programmed) secret sourceError correction

/-- In the programmed mode, the tag message vanishes exactly and only the transformed source
error and correction remain. -/
theorem programmedCandidate_phase
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    (programmed : Digest)
    (secret : Secret) (sourceError : SourceRow) (correction : TargetRow) :
    taggedBody trapdoor (source secret + sourceError) correction -
        candidateMask encoding source gadget trapdoor programmed programmed secret =
      correction - trapdoor sourceError := by
  simpa using candidatePhase encoding source gadget trapdoor programmed programmed
    secret sourceError correction

/-- Normalize a wrong candidate's tagged mask by the inverse tag. -/
noncomputable def normalizedCandidateMask
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    {candidate programmed : Digest} (hne : candidate ≠ programmed) :
    Secret →ₗ[R] TargetRow :=
  (encoding.differenceEquiv hne).symm.toLinearMap.comp
    (candidateMask encoding source gadget trapdoor candidate programmed)

/-- Normalize the retained trapdoor by the same inverse tag. -/
noncomputable def normalizedTrapdoor
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    {candidate programmed : Digest} (hne : candidate ≠ programmed) :
    SourceRow →ₗ[R] TargetRow :=
  (encoding.differenceEquiv hne).symm.toLinearMap.comp trapdoor

/-- Every wrong candidate normalizes to an ordinary `G`-preimage relation. -/
theorem wrongCandidate_normalized_preimage
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    {candidate programmed : Digest} (hne : candidate ≠ programmed) :
    normalizedCandidateMask encoding source gadget trapdoor hne +
        (normalizedTrapdoor encoding trapdoor hne).comp source = gadget := by
  apply LinearMap.ext
  intro secret
  have hrelation := DFunLike.congr_fun
    (candidateMask_add_trapdoor_comp_source
      encoding source gadget trapdoor candidate programmed) secret
  have hrelation' :
      candidateMask encoding source gadget trapdoor candidate programmed secret +
          trapdoor (source secret) =
        encoding.tagDifference candidate programmed (gadget secret) := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply] using hrelation
  change
    (encoding.differenceEquiv hne).symm
          (candidateMask encoding source gadget trapdoor candidate programmed secret) +
        (encoding.differenceEquiv hne).symm (trapdoor (source secret)) =
      gadget secret
  calc
    _ = (encoding.differenceEquiv hne).symm
        (candidateMask encoding source gadget trapdoor candidate programmed secret +
          trapdoor (source secret)) := by rw [map_add]
    _ = (encoding.differenceEquiv hne).symm
        (encoding.tagDifference candidate programmed (gadget secret)) := by
          rw [hrelation']
    _ = gadget secret :=
      encoding.differenceEquiv_symm_apply_tagDifference hne (gadget secret)

/-- Applying the inverse tag to a wrong candidate's phase removes the tag exactly. -/
theorem wrongCandidate_normalized_phase
    (encoding : FullRankDifferenceEncoding R Digest TargetRow)
    (source : Secret →ₗ[R] SourceRow) (gadget : Secret →ₗ[R] TargetRow)
    (trapdoor : SourceRow →ₗ[R] TargetRow)
    {candidate programmed : Digest} (hne : candidate ≠ programmed)
    (secret : Secret) (sourceError : SourceRow) (correction : TargetRow) :
    (encoding.differenceEquiv hne).symm
        (taggedBody trapdoor (source secret + sourceError) correction -
          candidateMask encoding source gadget trapdoor candidate programmed secret) =
      -gadget secret +
        (encoding.differenceEquiv hne).symm
          (correction - trapdoor sourceError) := by
  rw [candidatePhase encoding source gadget trapdoor candidate programmed
    secret sourceError correction]
  simp only [map_sub, map_add, map_neg]
  rw [encoding.differenceEquiv_symm_apply_tagDifference hne]
  abel

end TaggedFamily

/-! ## Security-loss composition -/

/-- Hash-CMUX composition with the all-but-one mode-switch defect displayed separately and
charged exactly once.  Construction of that mode switch remains a premise. -/
theorem allButOneHashCMUXSecurity_le
    (digestCount : ℕ)
    (securityGap predictionExcess contextualAdvantage
      taggedModeDefect equalityDefect cmuxSanitizerDefect endpointDefect : ℝ)
    (hgap : securityGap ≤
      (2 : ℝ) ^ digestCount * predictionExcess +
        (taggedModeDefect + equalityDefect + cmuxSanitizerDefect + endpointDefect))
    (hsecondMoment : predictionExcess ^ 2 ≤
      2 * (2 : ℝ) ^ digestCount * contextualAdvantage) :
    securityGap ≤
      binaryHashCMUXContextualLoss digestCount *
          Real.sqrt contextualAdvantage +
        taggedModeDefect + equalityDefect + cmuxSanitizerDefect + endpointDefect := by
  have hbound := sanitizedSelfCircularSecurity_le
    digestCount securityGap predictionExcess contextualAdvantage
    equalityDefect (taggedModeDefect + cmuxSanitizerDefect) endpointDefect
    (by linarith) hsecondMoment
  linarith

/-- Direct projected composition with the all-but-one mode-switch defect displayed separately.
Unlike candidate guessing, this route has no additional digest-cardinality multiplier. -/
theorem allButOneDirectProjectedSecurity_le
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ) (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : NativeTRGSWHashCompressedSecurity.HasUniformOutput hash)
    (securityGap lossyGap fidelityOne fidelityZero realSecondMoment
      projectedAdvantage taggedModeDefect equalityDefect sanitizerDefect endpointDefect : ℝ)
    (houter : securityGap ≤ lossyGap + taggedModeDefect +
      equalityDefect + sanitizerDefect + endpointDefect)
    (hdiagonal : lossyGap ≤ fidelityOne + fidelityZero +
      Real.sqrt
        (NativeTRGSWAggregateProjectedLeakage.projectedLeakageConcentration
          ($ᵗ (Prefix × Suffix))
          (NativeTRGSWHashCompressedSecurity.hashedPrefixLeakage
            (Suffix := Suffix) hash) * realSecondMoment))
    (hsource : |realSecondMoment| ≤ 2 * projectedAdvantage) :
    securityGap ≤ fidelityOne + fidelityZero +
      Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * projectedAdvantage) +
      taggedModeDefect + equalityDefect + sanitizerDefect + endpointDefect := by
  have hlossy := directProjectedUniformBinaryGap_le
    digestCount hash huniformHash lossyGap fidelityOne fidelityZero
    realSecondMoment projectedAdvantage hdiagonal hsource
  linarith

end

end FormalProof4FHE.TFHE.MPAllButOneHashTrapdoor
