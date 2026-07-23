/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveCandidateTape

set_option autoImplicit false

/-!
# Uniform-Tape Preservation by Relative/Anchor Randomization

The direct FHE CircLWE decision problem has two branches with the same real evaluation material:
a real target-key tape and a uniform tape.  A valid PKC-style shifted evaluator must therefore
transport both branches.  This file proves that the normalized-relative material interface plus
the checked global anchor does exactly that.

Uniform tapes are invariant under every coefficientwise target-key XOR transform.  Consequently
the uniform branch pays exactly the same material and global-anchor error as the real branch, with
no new query-count or scalar-noise term.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

/-- Every nested-key tape transport is a permutation of the complete tape space, so it preserves
the uniform tape distribution exactly. -/
theorem transformTargetTape_uniform_evalDist
    (q degree sourceRank suffixRank queryCount : ℕ) [NeZero q]
    (mask : Mask sourceRank suffixRank degree) :
    evalDist (transformTargetTape mask <$>
        ($ᵗ (Challenge q degree sourceRank suffixRank queryCount))) =
      evalDist ($ᵗ (Challenge q degree sourceRank suffixRank queryCount)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Challenge q degree sourceRank suffixRank queryCount)
    (β := Challenge q degree sourceRank suffixRank queryCount)
    (transformTargetTape mask)
    (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBatch_bijective
      (targetScalarMask mask))

namespace RelativeEvaluationMaterialEvaluator

/-- Lifting a normalized material evaluator across an independent uniform tape preserves its
error unchanged. -/
theorem completeRelativeUniformDistance_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (secret : Secret 1 suffixRank (degree + 1))
    (relativeMask : RelativeNestedMask suffixRank degree) :
    tvDist
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
          evaluator.evaluateCompleteRelative relativeMask)
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget
          (act secret (liftRelativeNestedMask relativeMask))) ≤ evaluator.error := by
  let nestedMask := liftRelativeNestedMask relativeMask
  let targetSecret := act secret nestedMask
  let uniformTape : ProbComp (Challenge q (degree + 1) 1 suffixRank queryCount) :=
    $ᵗ (Challenge q (degree + 1) 1 suffixRank queryCount)
  let transformedTape := transformTargetTape nestedMask <$> uniformTape
  let evaluatedMaterial :=
    sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
        narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
      evaluator.evaluateRelative relativeMask
  let targetMaterial := sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
    wideBootstrapErrorSampler wideExtensionErrorSampler gadget targetSecret
  have htape : tvDist transformedTape uniformTape = 0 := by
    unfold tvDist
    rw [show evalDist transformedTape = evalDist uniformTape by
      exact transformTargetTape_uniform_evalDist q (degree + 1) 1 suffixRank
        queryCount nestedMask]
    exact SPMF.tvDist_self _
  have hsource :
      sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
          evaluator.evaluateCompleteRelative relativeMask =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedTape evaluatedMaterial Prod.mk := by
    simp [sampleUniformTapeMaterialView, evaluateCompleteRelative,
      transformedTape, uniformTape, evaluatedMaterial, nestedMask,
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      map_eq_bind_pure_comp, bind_assoc, monad_norm]
  have htarget :
      sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget targetSecret =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          uniformTape targetMaterial Prod.mk := by
    simp [sampleUniformTapeMaterialView, uniformTape, targetMaterial,
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair]
  rw [hsource, show act secret (liftRelativeNestedMask relativeMask) =
      targetSecret by rfl, htarget]
  calc
    tvDist
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedTape evaluatedMaterial Prod.mk)
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          uniformTape targetMaterial Prod.mk) ≤
      tvDist transformedTape uniformTape + tvDist evaluatedMaterial targetMaterial :=
      FormalProof4FHE.TFHE.SamplerReplacement.tvDist_independentPair_le
        transformedTape uniformTape evaluatedMaterial targetMaterial Prod.mk
    _ ≤ 0 + evaluator.error := add_le_add (le_of_eq htape)
      (evaluator.materialDistance_le secret relativeMask)
    _ = evaluator.error := zero_add _

end RelativeEvaluationMaterialEvaluator

/-- Global complementation of a uniform-tape view pays only the already checked material shear
term; the tape remains exactly uniform. -/
theorem transformCompleteViewGlobalComplement_uniform_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        extensionErrorSampler)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1)) :
    tvDist
        (transformCompleteViewGlobalComplement gadget <$>
          sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler gadget secret)
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler gadget
          (act secret (nestedGlobalMask 1 suffixRank (degree + 1)))) ≤
      globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) bootstrapErrorSampler := by
  let mask := nestedGlobalMask 1 suffixRank (degree + 1)
  let targetSecret := act secret mask
  let uniformTape : ProbComp (Challenge q (degree + 1) 1 suffixRank queryCount) :=
    $ᵗ (Challenge q (degree + 1) 1 suffixRank queryCount)
  let transformedTape := transformTargetTape mask <$> uniformTape
  let transformedMaterial := transformEvaluationMaterialGlobalComplement gadget <$>
    sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
      bootstrapErrorSampler extensionErrorSampler gadget secret
  let targetMaterial := sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
    bootstrapErrorSampler extensionErrorSampler gadget targetSecret
  have htape : tvDist transformedTape uniformTape = 0 := by
    unfold tvDist
    rw [show evalDist transformedTape = evalDist uniformTape by
      exact transformTargetTape_uniform_evalDist q (degree + 1) 1 suffixRank
        queryCount mask]
    exact SPMF.tvDist_self _
  have hmaterial : tvDist transformedMaterial targetMaterial ≤
      globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) bootstrapErrorSampler := by
    simpa only [transformedMaterial, targetMaterial, targetSecret, mask,
      globalComplementViewError] using
      (transformEvaluationMaterialGlobalComplement_tvDist_le
        bootstrapErrorSampler extensionErrorSampler hextensionSymmetric gadget secret)
  have hsource :
      transformCompleteViewGlobalComplement gadget <$>
          sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler gadget secret =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedTape transformedMaterial Prod.mk := by
    simp [sampleUniformTapeMaterialView, transformCompleteViewGlobalComplement,
      transformedTape, transformedMaterial, uniformTape, mask,
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      map_eq_bind_pure_comp, bind_assoc, monad_norm]
  have htarget :
      sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler gadget targetSecret =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          uniformTape targetMaterial Prod.mk := by
    simp [sampleUniformTapeMaterialView, uniformTape, targetMaterial,
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair]
  rw [hsource, show act secret (nestedGlobalMask 1 suffixRank (degree + 1)) =
      targetSecret by rfl, htarget]
  exact
    (FormalProof4FHE.TFHE.SamplerReplacement.tvDist_independentPair_le
      transformedTape uniformTape transformedMaterial targetMaterial Prod.mk).trans
      (by simpa only [zero_add] using add_le_add (le_of_eq htape) hmaterial)

/-- Applying the global anchor conditionally has the same bound on the uniform-tape branch. -/
theorem transformCompleteViewByAnchor_uniform_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        extensionErrorSampler)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1))
    (toggle : Bool) :
    tvDist
        (transformCompleteViewByAnchor gadget toggle <$>
          sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler gadget secret)
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler gadget
          (if toggle then
            act secret (nestedGlobalMask 1 suffixRank (degree + 1))
          else secret)) ≤
      globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) bootstrapErrorSampler := by
  cases toggle
  · have htransform :
        transformCompleteViewByAnchor (suffixRank := suffixRank)
            (queryCount := queryCount) gadget false =
          (id : View q (degree + 1) 1 suffixRank levels queryCount →
            View q (degree + 1) 1 suffixRank levels queryCount) := by
      funext view
      simp [transformCompleteViewByAnchor]
    rw [htransform]
    simpa using
      (globalComplementViewError_nonneg
        (suffixRank := suffixRank) (levels := levels) bootstrapErrorSampler)
  · have htransform :
        transformCompleteViewByAnchor (suffixRank := suffixRank)
            (queryCount := queryCount) gadget true =
          transformCompleteViewGlobalComplement (suffixRank := suffixRank)
            (queryCount := queryCount) gadget := by
      funext view
      simp [transformCompleteViewByAnchor]
    rw [htransform]
    exact transformCompleteViewGlobalComplement_uniform_tvDist_le
      (queryCount := queryCount) bootstrapErrorSampler extensionErrorSampler
      hextensionSymmetric gadget secret

namespace RelativeEvaluationMaterialEvaluator

/-- The normalized relative evaluator followed by the checked anchor transports the uniform-tape
branch with exactly the same summed error as the real branch. -/
theorem relativeThenGlobalUniformDistance_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (secret : Secret 1 suffixRank (degree + 1))
    (mask : RelativeNestedMask suffixRank degree × Bool) :
    tvDist
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
          evaluator.evaluateRelativeThenGlobal mask)
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget
          (relativeThenGlobalAct secret mask)) ≤
      evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := by
  let relativeSecret := act secret (liftRelativeNestedMask mask.1)
  let afterRelative :=
    sampleUniformTapeMaterialView q degree suffixRank levels queryCount
        narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
      evaluator.evaluateCompleteRelative mask.1
  let wideRelative :=
    sampleUniformTapeMaterialView q degree suffixRank levels queryCount
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget relativeSecret
  let finish := fun view : View q (degree + 1) 1 suffixRank levels queryCount ↦
    (pure (transformCompleteViewByAnchor gadget mask.2 view) :
      ProbComp (View q (degree + 1) 1 suffixRank levels queryCount))
  let afterGlobal := afterRelative >>= finish
  let wideAfterGlobal := wideRelative >>= finish
  have hrelative : tvDist afterRelative wideRelative ≤ evaluator.error := by
    exact evaluator.completeRelativeUniformDistance_le secret mask.1
  have hpost : tvDist afterGlobal wideAfterGlobal ≤
      tvDist afterRelative wideRelative :=
    tvDist_bind_right_le finish afterRelative wideRelative
  have hglobal :
      tvDist wideAfterGlobal
          (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            wideBootstrapErrorSampler wideExtensionErrorSampler gadget
            (relativeThenGlobalAct secret mask)) ≤
        globalComplementViewError
          (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := by
    have h := transformCompleteViewByAnchor_uniform_tvDist_le
      (queryCount := queryCount) wideBootstrapErrorSampler wideExtensionErrorSampler
      hextensionSymmetric gadget relativeSecret mask.2
    have hsecret :
        (if mask.2 then
          act relativeSecret (nestedGlobalMask 1 suffixRank (degree + 1))
        else relativeSecret) = relativeThenGlobalAct secret mask := by
      rcases mask with ⟨relativeMask, toggle⟩
      cases toggle <;> rfl
    have hmap :
        transformCompleteViewByAnchor gadget mask.2 <$> wideRelative =
          wideAfterGlobal := by
      unfold wideAfterGlobal finish
      rw [map_eq_bind_pure_comp]
      rfl
    rw [hmap] at h
    rw [hsecret] at h
    exact h
  have hsource :
      (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
        evaluator.evaluateRelativeThenGlobal mask) = afterGlobal := by
    change
      (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
        fun view ↦ evaluator.evaluateCompleteRelative mask.1 view >>= finish) =
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
          evaluator.evaluateCompleteRelative mask.1) >>= finish
    rw [bind_assoc]
  rw [hsource]
  calc
    tvDist afterGlobal
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget
          (relativeThenGlobalAct secret mask)) ≤
      tvDist afterGlobal wideAfterGlobal +
        tvDist wideAfterGlobal
          (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
            wideBootstrapErrorSampler wideExtensionErrorSampler gadget
            (relativeThenGlobalAct secret mask)) := tvDist_triangle _ _ _
    _ ≤ evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler :=
      add_le_add (hpost.trans hrelative) hglobal

/-- Package the same evaluator as a fresh-secret randomizer for the uniform-tape branch. -/
def toUniformTapeViewRandomization
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (Secret 1 suffixRank (degree + 1))
      (RelativeNestedMask suffixRank degree × Bool)
      (View q (degree + 1) 1 suffixRank levels queryCount) where
  sampleMask := $ᵗ (RelativeNestedMask suffixRank degree × Bool)
  act := relativeThenGlobalAct
  sampleFreshSecret := sampleNestedSecret 1 suffixRank (degree + 1)
  sampleNarrowView := sampleUniformTapeMaterialView q degree suffixRank levels queryCount
    narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget
  sampleWideView := sampleUniformTapeMaterialView q degree suffixRank levels queryCount
    wideBootstrapErrorSampler wideExtensionErrorSampler gadget
  evaluateAndSmudge := evaluator.evaluateRelativeThenGlobal
  error := evaluator.error + globalComplementViewError
    (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler
  error_nonneg := add_nonneg evaluator.error_nonneg
    (globalComplementViewError_nonneg wideBootstrapErrorSampler)
  secretLaw := relativeThenGlobalAct_uniform_evalDist suffixRank degree
  viewDistance_le := evaluator.relativeThenGlobalUniformDistance_le hextensionSymmetric

@[simp]
theorem toUniformTapeViewRandomization_error
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :
    (evaluator.toUniformTapeViewRandomization
      (queryCount := queryCount) hextensionSymmetric).error =
      evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := rfl

end RelativeEvaluationMaterialEvaluator

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
