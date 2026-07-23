/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.ConditionalSmudging
import FormalProof4FHE.TFHE.MonomialKDM
import FormalProof4FHE.TFHE.SamplerReplacement

/-!
# Conditional Smudging for the Native TFHE Evaluation-Key Layout

This module lifts the pointwise TLWE/TGSW body-smudging theorem to the complete native TFHE
bootstrapping-key and key-switch-key types.  An algebraic evaluator may leave a fixed residual in
every native row.  Fresh wide errors absorb those residuals with the explicit cost

* `∑ scalar-coordinate ∑ TGSW-row translationDistance` for the BRK, and
* `∑ key-switch-row translationDistance` for the KSK.

The two independent components compose by a two-step hybrid.  The target BRK is the exact
degree-two monomial presentation used by the auxiliary-input CircLWE problem, so this is directly
usable by the widened search-to-decision layer.

No claim is made here that the missing homomorphic candidate evaluator has the required residual
normal form.  This file proves the complete statistical smudging implication once that algebraic
statement is supplied.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ConditionalSmudging

noncomputable section

/- The executable polynomial backend exposes primitive additive instances as well as the
additive projections of its bundled ring.  Select the bundled-ring path locally so residual
addition uses the same operation instance as the generic `Ring`-parameterized TLWE theorems. -/
local instance rqAddFromSemiring (q degree : ℕ) : Add (RLWE.Rq q degree) :=
  (inferInstance : Distrib (RLWE.Rq q degree)).toAdd

local instance rqAddCommGroupFromRing (q degree : ℕ) :
    AddCommGroup (RLWE.Rq q degree) :=
  (inferInstance : Ring (RLWE.Rq q degree)).toAddCommGroup

local instance rqNegFromRing (q degree : ℕ) : Neg (RLWE.Rq q degree) :=
  (rqAddCommGroupFromRing q degree).toNeg

local instance rqZeroFromRing (q degree : ℕ) : Zero (RLWE.Rq q degree) :=
  (rqAddCommGroupFromRing q degree).toZero

/-- The additive zero selected by the bundled-ring path used in native residual addition.
Naming it explicitly lets downstream modules instantiate the zero-noise sampler without relying
on typeclass-instance definitional equality. -/
def ringAdditiveZero (q degree : ℕ) : RLWE.Rq q degree :=
  @Zero.zero (RLWE.Rq q degree) (rqZeroFromRing q degree)

/-- One fixed ring residual for every scalar-key coordinate and native TGSW row. -/
abbrev BootstrappingResidual
    (q degree ringRank tgswLevels lweDimension : ℕ) :=
  Fin lweDimension → Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree

/-- Complete public-mask tensor of a native bootstrapping key.  Keeping this type separate from
the bodies makes it possible to state the exact mask-only normal form used after native CMux
evaluation. -/
abbrev BootstrappingMask
    (q degree ringRank tgswLevels lweDimension : ℕ) :=
  Fin lweDimension →
    Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels)) (RLWE.Rq q degree)

/-- Read every public mask from a complete native bootstrapping key. -/
def bootstrappingMask
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (bootstrappingKey : BootstrappingKey q degree ringRank tgswLevels lweDimension) :
    BootstrappingMask q degree ringRank tgswLevels lweDimension :=
  fun coordinate ↦ (bootstrappingKey coordinate).1

/-- Assemble a complete residual BRK from a supplied public-mask tensor.  The target secret,
gadget message, and complete evaluator residual determine every body once the mask is fixed. -/
def assembleResidualBootstrappingKey
    (q degree ringRank tgswLevels lweDimension : ℕ)
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (mask : BootstrappingMask q degree ringRank tgswLevels lweDimension) :
    BootstrappingKey q degree ringRank tgswLevels lweDimension :=
  fun coordinate ↦
    TLWE.batchAssemble (embedRingSecret q ringSecret) (mask coordinate)
      (TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
        (embedConstantBit q degree (lweSecret coordinate)))
      (residual coordinate)

/-- Product sampler matching the independent public masks used by direct native BRK generation. -/
noncomputable def sampleFreshBootstrappingMask
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q] :
    ProbComp (BootstrappingMask q degree ringRank tgswLevels lweDimension) :=
  Fin.mOfFn lweDimension fun _coordinate ↦
    $ᵗ (Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
      (RLWE.Rq q degree))

/-- The product sampler used by direct BRK generation is exactly uniform on the complete mask
tensor. -/
theorem sampleFreshBootstrappingMask_evalDist_eq_uniform
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q] :
    evalDist
        (sampleFreshBootstrappingMask
          q degree ringRank tgswLevels lweDimension) =
      evalDist
        ($ᵗ (BootstrappingMask q degree ringRank tgswLevels lweDimension)) := by
  simpa only [sampleFreshBootstrappingMask, ProbComp.sampleIID] using
    (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree)) lweDimension)

@[simp]
theorem bootstrappingMask_assembleResidualBootstrappingKey
    (q degree ringRank tgswLevels lweDimension : ℕ)
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (mask : BootstrappingMask q degree ringRank tgswLevels lweDimension) :
    bootstrappingMask
        (assembleResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
          gadget lweSecret ringSecret residual mask) =
      mask := by
  rfl

/-- One fixed scalar residual for every row of the native key-switch table. -/
abbrev KeySwitchResidual
    (q ringRank degree keySwitchLevels : ℕ) :=
  Fin ((ringRank * degree) * keySwitchLevels) → ZMod q

/-! ## Executable post-evaluation BRK smudging -/

/-- Add one public ring-noise value to every body row of a complete native bootstrapping key.
The public masks and gadget layout are left unchanged. -/
def addBootstrappingBodyNoise
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (noise : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (bootstrappingKey : BootstrappingKey q degree ringRank tgswLevels lweDimension) :
    BootstrappingKey q degree ringRank tgswLevels lweDimension :=
  fun coordinate ↦
    TLWE.addBatchBodyNoise (noise coordinate) (bootstrappingKey coordinate)

/-- Independently sample one public body-noise value for every BRK row. -/
def sampleBootstrappingBodyNoise
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree)) :
    ProbComp (BootstrappingResidual q degree ringRank tgswLevels lweDimension) :=
  Fin.mOfFn lweDimension fun _coordinate ↦
    ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) wideNoise

/-- Add fresh independent wide noise after a native BRK has already been computed.  This is the
post-evaluation smudging operation required by the CircLWE search-to-decision argument. -/
def smudgeBootstrappingKey
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (bootstrappingKey : BootstrappingKey q degree ringRank tgswLevels lweDimension) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
  (fun noise ↦ addBootstrappingBodyNoise noise bootstrappingKey) <$>
    sampleBootstrappingBodyNoise (ringRank := ringRank)
      (tgswLevels := tgswLevels) (lweDimension := lweDimension) wideNoise

@[simp]
theorem addBootstrappingBodyNoise_apply
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (noise : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (bootstrappingKey : BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (coordinate : Fin lweDimension) :
    addBootstrappingBodyNoise noise bootstrappingKey coordinate =
      TLWE.addBatchBodyNoise (noise coordinate) (bootstrappingKey coordinate) :=
  rfl

/-- Adding a fixed body-noise tensor is a permutation of the complete BRK space. -/
theorem addBootstrappingBodyNoise_bijective
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (noise : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    Function.Bijective
      (addBootstrappingBodyNoise noise :
        BootstrappingKey q degree ringRank tgswLevels lweDimension →
          BootstrappingKey q degree ringRank tgswLevels lweDimension) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨addBootstrappingBodyNoise (-noise), ?_, ?_⟩
  · intro bootstrappingKey
    funext coordinate
    apply Prod.ext
    · rfl
    · funext row
      simp only [addBootstrappingBodyNoise, TLWE.addBatchBodyNoise, Pi.neg_apply,
        Pi.add_apply]
      exact @add_neg_cancel_right (RLWE.Rq q degree)
        (rqAddCommGroupFromRing q degree).toAddGroup _ _
  · intro bootstrappingKey
    funext coordinate
    apply Prod.ext
    · rfl
    · funext row
      simp only [addBootstrappingBodyNoise, TLWE.addBatchBodyNoise, Pi.neg_apply,
        Pi.add_apply]
      have hcancel : -noise coordinate row + noise coordinate row =
          (0 : RLWE.Rq q degree) :=
        @neg_add_cancel (RLWE.Rq q degree)
          (rqAddCommGroupFromRing q degree).toAddGroup _
      rw [add_assoc, hcancel, add_zero]

/-- A fixed post-evaluation body shift leaves an exactly uniform BRK exactly uniform. -/
theorem addBootstrappingBodyNoise_uniform_evalDist
    {q degree ringRank tgswLevels lweDimension : ℕ} [NeZero q]
    (noise : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    evalDist
        (addBootstrappingBodyNoise noise <$>
          ($ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension))) =
      evalDist ($ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)) :=
  evalDist_map_bijective_uniform_cross
    (α := BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (β := BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (addBootstrappingBodyNoise noise)
    (addBootstrappingBodyNoise_bijective noise)

/-- Mixing over any independent post-evaluation noise law still leaves a uniform BRK uniform. -/
theorem smudge_uniformBootstrappingKey_evalDist
    {q degree ringRank tgswLevels lweDimension : ℕ} [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree)) :
    evalDist (do
        let bootstrappingKey ←
          $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
        smudgeBootstrappingKey wideNoise bootstrappingKey) =
      evalDist ($ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)) := by
  let noiseSampler :
      ProbComp (BootstrappingResidual q degree ringRank tgswLevels lweDimension) :=
    sampleBootstrappingBodyNoise (ringRank := ringRank)
      (tgswLevels := tgswLevels) (lweDimension := lweDimension) wideNoise
  calc
    _ = evalDist (noiseSampler >>= fun noise ↦
          addBootstrappingBodyNoise noise <$>
            ($ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension))) := by
      simp only [smudgeBootstrappingKey, noiseSampler, map_eq_bind_pure_comp]
      exact evalDist_bind_bind_swap
        ($ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension))
        noiseSampler
        (fun bootstrappingKey noise ↦
          pure (addBootstrappingBodyNoise noise bootstrappingKey))
    _ = evalDist (noiseSampler >>= fun _noise ↦
          ($ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension))) := by
      refine evalDist_bind_congr' noiseSampler fun noise ↦ ?_
      exact addBootstrappingBodyNoise_uniform_evalDist noise
    _ = _ := by
      apply evalDist_ext
      intro bootstrappingKey
      rw [probOutput_bind_const]
      simp

/-- Exact additive translation cost of all residual rows in a native bootstrapping key. -/
noncomputable def bootstrappingSmudgingCost
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension) : ℝ :=
  ∑ coordinate, ∑ row,
    FormalProof4FHE.FiniteProduct.addShiftDistance wideNoise (residual coordinate row)

/-- A fixed public-mask native BRK with a pre-existing residual and fresh body noise.  This is
the correct post-evaluation order: the evaluator fixes the mask and residual first, and only then
is the independent wide noise sampled. -/
def fixedMaskResidualSmudgedKey
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (mask : BootstrappingMask q degree ringRank tgswLevels lweDimension) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
  (fun noise ↦
      assembleResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
        gadget lweSecret ringSecret
          (fun coordinate row ↦ residual coordinate row + noise coordinate row) mask) <$>
    sampleBootstrappingBodyNoise (ringRank := ringRank)
      (tgswLevels := tgswLevels) (lweDimension := lweDimension) wideNoise

/-- The corresponding fixed-mask view after erasing the evaluator residual, while retaining the
same independently sampled wide body noise. -/
def fixedMaskWideKey
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (mask : BootstrappingMask q degree ringRank tgswLevels lweDimension) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
  (fun noise ↦
      assembleResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
        gadget lweSecret ringSecret noise mask) <$>
    sampleBootstrappingBodyNoise (ringRank := ringRank)
      (tgswLevels := tgswLevels) (lweDimension := lweDimension) wideNoise

/-- Executable body smudging of an assembled residual key is exactly the fixed-mask residual
view above. -/
theorem smudgeBootstrappingKey_assembleResidual_evalDist
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (mask : BootstrappingMask q degree ringRank tgswLevels lweDimension) :
    evalDist
        (smudgeBootstrappingKey wideNoise
          (assembleResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
            gadget lweSecret ringSecret residual mask)) =
      evalDist
        (fixedMaskResidualSmudgedKey wideNoise gadget lweSecret ringSecret residual mask) := by
  unfold smudgeBootstrappingKey fixedMaskResidualSmudgedKey
  apply congrArg evalDist
  congr 1
  funext noise
  unfold addBootstrappingBodyNoise assembleResidualBootstrappingKey
  funext coordinate
  exact TLWE.addBatchBodyNoise_batchAssemble
    (embedRingSecret q ringSecret) (mask coordinate)
    (TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate)))
    (residual coordinate) (noise coordinate)

/-- Once wide noise is sampled after evaluation, erasing a fixed residual costs only the sum of
its scalar translation distances.  Crucially, no residual is retained as side information in
this comparison. -/
theorem tvDist_fixedMaskResidualSmudgedKey_fixedMaskWideKey_le
    {q degree ringRank tgswLevels lweDimension : ℕ}
    [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (mask : BootstrappingMask q degree ringRank tgswLevels lweDimension) :
    tvDist
        (fixedMaskResidualSmudgedKey wideNoise gadget lweSecret ringSecret residual mask)
        (fixedMaskWideKey wideNoise gadget lweSecret ringSecret mask) ≤
      bootstrappingSmudgingCost wideNoise residual := by
  let Rows := TGSW.rowCount ringRank tgswLevels
  let RowNoise : ProbComp (Fin Rows → RLWE.Rq q degree) :=
    ProbComp.sampleIID Rows wideNoise
  let Noise : ProbComp
      (BootstrappingResidual q degree ringRank tgswLevels lweDimension) :=
    Fin.mOfFn lweDimension fun _coordinate ↦ RowNoise
  let addResidual :
      BootstrappingResidual q degree ringRank tgswLevels lweDimension →
        BootstrappingResidual q degree ringRank tgswLevels lweDimension :=
    fun noise coordinate row ↦ residual coordinate row + noise coordinate row
  let assemble := fun errors ↦
    assembleResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
      gadget lweSecret ringSecret errors mask
  have hnoise : tvDist (addResidual <$> Noise) Noise ≤
      ∑ coordinate, ∑ row,
        FormalProof4FHE.FiniteProduct.addShiftDistance
          wideNoise (residual coordinate row) := by
    rw [show addResidual <$> Noise =
        Fin.mOfFn lweDimension (fun coordinate ↦
          (fun values row ↦ residual coordinate row + values row) <$> RowNoise) by
      simpa only [addResidual, Noise] using
        (FormalProof4FHE.FiniteProduct.map_fin_mOfFn lweDimension
          (fun _coordinate ↦ RowNoise)
          (fun coordinate values row ↦ residual coordinate row + values row))]
    calc
      tvDist
          (Fin.mOfFn lweDimension (fun coordinate ↦
            (fun values row ↦ residual coordinate row + values row) <$> RowNoise))
          Noise ≤
        ∑ coordinate, tvDist
          ((fun values row ↦ residual coordinate row + values row) <$> RowNoise)
          RowNoise := by
            simpa only [Noise] using
              (FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
                lweDimension
                (fun coordinate ↦
                  (fun values row ↦ residual coordinate row + values row) <$> RowNoise)
                (fun _coordinate ↦ RowNoise))
      _ ≤ ∑ coordinate, ∑ row,
          FormalProof4FHE.FiniteProduct.addShiftDistance
            wideNoise (residual coordinate row) := by
        apply Finset.sum_le_sum
        intro coordinate _
        simpa only [RowNoise, ProbComp.sampleIID] using
          (FormalProof4FHE.FiniteProduct.tvDist_add_fin_mOfFn_le_sum
            Rows wideNoise (residual coordinate))
  have hdata := tvDist_map_le (m := ProbComp) assemble
    (addResidual <$> Noise) Noise
  unfold fixedMaskResidualSmudgedKey fixedMaskWideKey
    sampleBootstrappingBodyNoise bootstrappingSmudgingCost
  simpa only [Noise, RowNoise, Rows, addResidual, assemble,
    Functor.map_map, Function.comp_apply] using hdata.trans hnoise

/-- The full native BRK smudging cost vanishes for the pointwise zero residual. -/
@[simp]
theorem bootstrappingSmudgingCost_zero
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree)) :
    bootstrappingSmudgingCost wideNoise
        (fun _coordinate _row ↦ ringAdditiveZero q degree :
          BootstrappingResidual q degree ringRank tgswLevels lweDimension) = 0 := by
  unfold bootstrappingSmudgingCost
  apply Finset.sum_eq_zero
  intro coordinate _
  apply Finset.sum_eq_zero
  intro row _
  unfold ringAdditiveZero
  exact FormalProof4FHE.FiniteProduct.addShiftDistance_zero wideNoise

/-- At one fixed mask, the residual-smudged view with zero residual is exactly the wide-only
view. -/
theorem fixedMaskResidualSmudgedKey_zero_evalDist_eq_fixedMaskWideKey
    {q degree ringRank tgswLevels lweDimension : ℕ} [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (mask : BootstrappingMask q degree ringRank tgswLevels lweDimension) :
    evalDist
        (fixedMaskResidualSmudgedKey wideNoise gadget lweSecret ringSecret
          (fun _coordinate _row ↦ ringAdditiveZero q degree) mask) =
      evalDist (fixedMaskWideKey wideNoise gadget lweSecret ringSecret mask) := by
  have hbound := tvDist_fixedMaskResidualSmudgedKey_fixedMaskWideKey_le
    wideNoise gadget lweSecret ringSecret
    (fun _coordinate _row ↦ ringAdditiveZero q degree) mask
  have hzero : tvDist
      (fixedMaskResidualSmudgedKey wideNoise gadget lweSecret ringSecret
        (fun _coordinate _row ↦ ringAdditiveZero q degree) mask)
      (fixedMaskWideKey wideNoise gadget lweSecret ringSecret mask) = 0 :=
    le_antisymm (by simpa using hbound) (tvDist_nonneg _ _)
  exact (tvDist_eq_zero_iff _ _).mp hzero

/-- Exact additive translation cost of all residual rows in a native key-switch key. -/
noncomputable def keySwitchSmudgingCost
    {q ringRank degree keySwitchLevels : ℕ}
    (wideNoise : ProbComp (ZMod q))
    (residual : KeySwitchResidual q ringRank degree keySwitchLevels) : ℝ :=
  ∑ row, FormalProof4FHE.FiniteProduct.addShiftDistance wideNoise (residual row)

/-- Sum of the heterogeneous BRK and KSK conditional smudging costs. -/
noncomputable def evaluationKeySmudgingCost
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (ringResidual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : KeySwitchResidual q ringRank degree keySwitchLevels) : ℝ :=
  bootstrappingSmudgingCost ringWideNoise ringResidual +
    keySwitchSmudgingCost keySwitchWideNoise keySwitchResidual

theorem bootstrappingSmudgingCost_nonneg
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    0 ≤ bootstrappingSmudgingCost wideNoise residual := by
  unfold bootstrappingSmudgingCost
  apply Finset.sum_nonneg
  intro coordinate _
  apply Finset.sum_nonneg
  intro row _
  exact tvDist_nonneg _ _

theorem keySwitchSmudgingCost_nonneg
    {q ringRank degree keySwitchLevels : ℕ}
    (wideNoise : ProbComp (ZMod q))
    (residual : KeySwitchResidual q ringRank degree keySwitchLevels) :
    0 ≤ keySwitchSmudgingCost wideNoise residual := by
  unfold keySwitchSmudgingCost
  apply Finset.sum_nonneg
  intro row _
  exact tvDist_nonneg _ _

theorem evaluationKeySmudgingCost_nonneg
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (ringResidual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : KeySwitchResidual q ringRank degree keySwitchLevels) :
    0 ≤ evaluationKeySmudgingCost ringWideNoise keySwitchWideNoise
      ringResidual keySwitchResidual :=
  add_nonneg (bootstrappingSmudgingCost_nonneg ringWideNoise ringResidual)
    (keySwitchSmudgingCost_nonneg keySwitchWideNoise keySwitchResidual)

/-- Direct-row native bootstrapping-key generation with one fixed evaluator residual per row. -/
noncomputable def generateResidualBootstrappingKey
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
  Fin.mOfFn lweDimension fun coordinate ↦
    TGSW.directEncryptWithResidual ringRank tgswLevels wideNoise
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate)) (residual coordinate)

/-- With deterministic zero fresh error, residual BRK generation is exactly: sample the complete
public-mask tensor independently and assemble every body from the target phase and residual.
This is the mask-only endpoint needed by the full-key conditional-collision reduction. -/
theorem generateResidualBootstrappingKey_zero_evalDist_eq_assembleFreshMask
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    evalDist
        (generateResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
          (pure (ringAdditiveZero q degree)) gadget lweSecret ringSecret residual) =
      evalDist
        (assembleResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
            gadget lweSecret ringSecret residual <$>
          sampleFreshBootstrappingMask q degree ringRank tgswLevels lweDimension) := by
  let Challenge :=
    Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
      (RLWE.Rq q degree)
  let Challenges : Fin lweDimension → ProbComp Challenge :=
    fun _coordinate ↦ $ᵗ Challenge
  let ZeroErrors : ProbComp
      (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels)
      (pure (ringAdditiveZero q degree))
  let Entry := fun coordinate : Fin lweDimension ↦
    TGSW.directEncryptWithResidual ringRank tgswLevels
      (pure (ringAdditiveZero q degree))
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate)) (residual coordinate)
  let Assemble := fun (coordinate : Fin lweDimension) (challenge : Challenge) ↦
    TLWE.batchAssemble (embedRingSecret q ringSecret) challenge
      (TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
        (embedConstantBit q degree (lweSecret coordinate)))
      (residual coordinate)
  have hZeroProduct :
      evalDist ZeroErrors =
        evalDist (pure (fun _ ↦ ringAdditiveZero q degree) :
          ProbComp (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)) := by
    unfold ZeroErrors ProbComp.sampleIID
    apply evalDist_ext
    intro values
    rw [FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn, probOutput_pure]
    classical
    simp only [probOutput_pure]
    by_cases hzero : values = fun _ ↦ ringAdditiveZero q degree
    · subst values
      simp
    · rw [if_neg hzero]
      have hexists : ∃ row,
          values row ≠ ringAdditiveZero q degree := by
        by_contra hall
        apply hzero
        funext row
        exact not_ne_iff.mp (fun hne ↦ hall ⟨row, hne⟩)
      obtain ⟨row, hrow⟩ := hexists
      exact Finset.prod_eq_zero (Finset.mem_univ row) (by
        simp only [hrow, if_false])
  have hEntry : ∀ coordinate,
      evalDist (Entry coordinate) =
        evalDist (Assemble coordinate <$> Challenges coordinate) := by
    intro coordinate
    unfold Entry TGSW.directEncryptWithResidual TLWE.batchEncryptWithResidual
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    change evalDist (Challenges coordinate >>= fun challenge ↦
        ZeroErrors >>= fun zeroErrors ↦
          pure (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge
            (TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
              (embedConstantBit q degree (lweSecret coordinate)))
            (residual coordinate + zeroErrors))) =
      evalDist (Challenges coordinate >>= fun challenge ↦
        pure (Assemble coordinate challenge))
    refine evalDist_bind_congr' (Challenges coordinate) fun challenge ↦ ?_
    calc
      evalDist (ZeroErrors >>= fun zeroErrors ↦
          pure (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge
            (TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
              (embedConstantBit q degree (lweSecret coordinate)))
            (residual coordinate + zeroErrors))) =
        evalDist ((pure (fun _ ↦ ringAdditiveZero q degree) :
            ProbComp (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)) >>=
          fun zeroErrors ↦
            pure (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge
              (TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
                (embedConstantBit q degree (lweSecret coordinate)))
              (residual coordinate + zeroErrors))) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hZeroProduct _
      _ = evalDist (pure (Assemble coordinate challenge)) := by
        simp only [pure_bind]
        apply congrArg evalDist
        apply congrArg pure
        unfold Assemble
        apply congrArg
        funext row
        simp only [Pi.add_apply]
        unfold ringAdditiveZero
        exact @add_zero (RLWE.Rq q degree)
          (rqAddCommGroupFromRing q degree).toAddZeroClass (residual coordinate row)
  unfold generateResidualBootstrappingKey sampleFreshBootstrappingMask
  change evalDist (Fin.mOfFn lweDimension Entry) =
    evalDist
      ((fun values coordinate ↦ Assemble coordinate (values coordinate)) <$>
        Fin.mOfFn lweDimension Challenges)
  rw [FormalProof4FHE.FiniteProduct.map_fin_mOfFn
    lweDimension Challenges Assemble]
  exact FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
    lweDimension Entry _ hEntry

/-- Generating a residual BRK with zero fresh error and then applying the executable body
smudger is exactly direct residual generation with the smudger's wide-error law.  This identity
is the bridge that factors post-evaluation smudging through a mask-only normal form. -/
theorem generateResidualBootstrappingKey_zero_then_smudge_evalDist
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    evalDist (do
        let zeroResidualKey ←
          generateResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
            (pure (ringAdditiveZero q degree)) gadget lweSecret ringSecret residual
        smudgeBootstrappingKey wideNoise zeroResidualKey) =
      evalDist
        (generateResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
          wideNoise gadget lweSecret ringSecret residual) := by
  let ZeroEntry := fun coordinate : Fin lweDimension ↦
    TGSW.directEncryptWithResidual ringRank tgswLevels
      (pure (ringAdditiveZero q degree))
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate)) (residual coordinate)
  let Noise := fun _coordinate : Fin lweDimension ↦
    ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) wideNoise
  let Process := fun (coordinate : Fin lweDimension)
      (entry : RingGSWCiphertext q degree ringRank tgswLevels) ↦
    (fun noise ↦ TLWE.addBatchBodyNoise noise entry) <$> Noise coordinate
  let TargetEntry := fun coordinate : Fin lweDimension ↦
    TGSW.directEncryptWithResidual ringRank tgswLevels wideNoise
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate)) (residual coordinate)
  have hZeroProduct : ∀ count,
      evalDist (Fin.mOfFn count
          (fun _ ↦ (pure (ringAdditiveZero q degree) :
            ProbComp (RLWE.Rq q degree)))) =
        evalDist (pure (fun _ ↦ ringAdditiveZero q degree) :
          ProbComp (Fin count → RLWE.Rq q degree)) := by
    intro count
    apply evalDist_ext
    intro values
    rw [FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn, probOutput_pure]
    classical
    simp only [probOutput_pure]
    by_cases hzero : values = fun _ ↦ ringAdditiveZero q degree
    · subst values
      simp
    · rw [if_neg hzero]
      have hexists : ∃ coordinate,
          values coordinate ≠ ringAdditiveZero q degree := by
        by_contra hall
        apply hzero
        funext coordinate
        exact not_ne_iff.mp (fun hne ↦ hall ⟨coordinate, hne⟩)
      obtain ⟨coordinate, hcoordinate⟩ := hexists
      exact Finset.prod_eq_zero (Finset.mem_univ coordinate) (by
        simp only [hcoordinate, if_false])
  have hEntry : ∀ coordinate,
      evalDist (ZeroEntry coordinate >>= Process coordinate) =
        evalDist (TargetEntry coordinate) := by
    intro coordinate
    let Challenges : ProbComp
        (Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
          (RLWE.Rq q degree)) :=
      $ᵗ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree)
    let ZeroErrors : ProbComp
        (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree) :=
      ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels)
        (pure (ringAdditiveZero q degree))
    let WideErrors : ProbComp
        (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree) :=
      ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) wideNoise
    let message := TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate))
    unfold ZeroEntry Process Noise TargetEntry TGSW.directEncryptWithResidual
      TLWE.batchEncryptWithResidual
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    change evalDist (Challenges >>= fun challenge ↦
        ZeroErrors >>= fun zeroErrors ↦
        WideErrors >>= fun wideErrors ↦
        pure (TLWE.addBatchBodyNoise wideErrors
          (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge message
            (residual coordinate + zeroErrors)))) =
      evalDist (Challenges >>= fun challenge ↦
        WideErrors >>= fun wideErrors ↦
        pure (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge message
          (residual coordinate + wideErrors)))
    calc
      _ = evalDist (Challenges >>= fun challenge ↦
          (pure (fun _ ↦ ringAdditiveZero q degree) : ProbComp
            (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)) >>=
          fun zeroErrors ↦
          WideErrors >>= fun wideErrors ↦
          pure (TLWE.addBatchBodyNoise wideErrors
            (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge message
              (residual coordinate + zeroErrors)))) := by
        refine evalDist_bind_congr' Challenges fun challenge ↦ ?_
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (by simpa only [ZeroErrors, ProbComp.sampleIID] using
            hZeroProduct (TGSW.rowCount ringRank tgswLevels)) _
      _ = _ := by
        simp only [pure_bind]
        refine evalDist_bind_congr' Challenges fun challenge ↦ ?_
        refine evalDist_bind_congr' WideErrors fun wideErrors ↦ ?_
        apply congrArg evalDist
        apply congrArg pure
        rw [TLWE.addBatchBodyNoise_batchAssemble]
        apply congrArg
        funext row
        simp only [Pi.add_apply]
        unfold ringAdditiveZero
        apply congrArg (fun value ↦ value + wideErrors row)
        exact @add_zero (RLWE.Rq q degree)
          (rqAddCommGroupFromRing q degree).toAddZeroClass (residual coordinate row)
  have hMap (key : BootstrappingKey q degree ringRank tgswLevels lweDimension) :
      (fun noise ↦ addBootstrappingBodyNoise noise key) <$>
          Fin.mOfFn lweDimension Noise =
        Fin.mOfFn lweDimension fun coordinate ↦ Process coordinate (key coordinate) := by
    unfold Process
    change ((fun noise coordinate ↦
        TLWE.addBatchBodyNoise (noise coordinate) (key coordinate)) <$>
          Fin.mOfFn lweDimension Noise) = _
    exact
      (FormalProof4FHE.FiniteProduct.map_fin_mOfFn lweDimension Noise
        (fun coordinate noise ↦ TLWE.addBatchBodyNoise noise (key coordinate)))
  unfold generateResidualBootstrappingKey smudgeBootstrappingKey
    sampleBootstrappingBodyNoise
  change evalDist (Fin.mOfFn lweDimension ZeroEntry >>= fun key ↦
      (fun noise ↦ addBootstrappingBodyNoise noise key) <$>
        Fin.mOfFn lweDimension Noise) =
    evalDist (Fin.mOfFn lweDimension TargetEntry)
  calc
    _ = evalDist (Fin.mOfFn lweDimension ZeroEntry >>= fun key ↦
          Fin.mOfFn lweDimension fun coordinate ↦
            Process coordinate (key coordinate)) := by
      refine evalDist_bind_congr' (Fin.mOfFn lweDimension ZeroEntry) fun key ↦ ?_
      exact congrArg evalDist (hMap key)
    _ = evalDist (Fin.mOfFn lweDimension fun coordinate ↦
          ZeroEntry coordinate >>= Process coordinate) :=
      FormalProof4FHE.FiniteProduct.evalDist_presample_fin_mOfFn
        lweDimension ZeroEntry Process
    _ = _ :=
      FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
        lweDimension _ _ hEntry

/-- The complete residual BRK is close to the fresh direct-row native BRK by the sum of all
pointwise row-translation costs. -/
theorem tvDist_generateResidualBootstrappingKey_generateDirect_le
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    tvDist
        (generateResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
          wideNoise gadget lweSecret ringSecret residual)
        (BootstrapSecurity.generateDirectBootstrappingKey
          q degree ringRank tgswLevels lweDimension wideNoise gadget
          lweSecret ringSecret) ≤
      bootstrappingSmudgingCost wideNoise residual := by
  unfold generateResidualBootstrappingKey
    BootstrapSecurity.generateDirectBootstrappingKey bootstrappingSmudgingCost
  calc
    tvDist
        (Fin.mOfFn lweDimension fun coordinate ↦
          TGSW.directEncryptWithResidual ringRank tgswLevels wideNoise
            (embedRingSecret q ringSecret) gadget
            (embedConstantBit q degree (lweSecret coordinate)) (residual coordinate))
        (Fin.mOfFn lweDimension fun coordinate ↦
          TGSW.directEncrypt ringRank tgswLevels wideNoise
            (embedRingSecret q ringSecret) gadget
            (embedConstantBit q degree (lweSecret coordinate))) ≤
      ∑ coordinate, tvDist
        (TGSW.directEncryptWithResidual ringRank tgswLevels wideNoise
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q degree (lweSecret coordinate)) (residual coordinate))
        (TGSW.directEncrypt ringRank tgswLevels wideNoise
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q degree (lweSecret coordinate))) :=
      FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum lweDimension _ _
    _ ≤ ∑ coordinate, ∑ row,
        FormalProof4FHE.FiniteProduct.addShiftDistance
          wideNoise (residual coordinate row) := by
      apply Finset.sum_le_sum
      intro coordinate _
      simpa only [TGSW.directEncrypt,
          FormalProof4FHE.FiniteProduct.addShiftDistance] using
        (TGSW.tvDist_directEncryptWithResidual_directEncrypt_le_sum
          ringRank tgswLevels wideNoise (embedRingSecret q ringSecret) gadget
          (embedConstantBit q degree (lweSecret coordinate)) (residual coordinate))

/-- The same BRK bound against the exact monomial presentation used by native auxiliary-input
CircLWE. -/
theorem tvDist_generateResidualBootstrappingKey_generateMonomial_le
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    tvDist
        (generateResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
          wideNoise gadget lweSecret ringSecret residual)
        (BootstrapSecurity.MonomialKDM.generateBootstrappingKey
          q degree ringRank tgswLevels lweDimension wideNoise gadget
          lweSecret ringSecret) ≤
      bootstrappingSmudgingCost wideNoise residual := by
  rw [BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct]
  exact tvDist_generateResidualBootstrappingKey_generateDirect_le
    q degree ringRank tgswLevels lweDimension wideNoise gadget
      lweSecret ringSecret residual

/-- Sampling a fresh complete mask and then independent wide row noise is exactly direct native
BRK generation.  This is the endpoint needed when residual erasure precedes mask replacement. -/
theorem sampleFreshBootstrappingMask_fixedMaskWideKey_evalDist_eq_generateDirect
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist
        (sampleFreshBootstrappingMask q degree ringRank tgswLevels lweDimension >>=
          fixedMaskWideKey wideNoise gadget lweSecret ringSecret) =
      evalDist
        (BootstrapSecurity.generateDirectBootstrappingKey
          q degree ringRank tgswLevels lweDimension wideNoise gadget
          lweSecret ringSecret) := by
  let Zero : BootstrappingResidual q degree ringRank tgswLevels lweDimension :=
    fun _coordinate _row ↦ ringAdditiveZero q degree
  let Fresh := sampleFreshBootstrappingMask
    q degree ringRank tgswLevels lweDimension
  let AssembleZero :=
    assembleResidualBootstrappingKey q degree ringRank tgswLevels lweDimension
      gadget lweSecret ringSecret Zero
  let ZeroKey := generateResidualBootstrappingKey
    q degree ringRank tgswLevels lweDimension
      (pure (ringAdditiveZero q degree)) gadget lweSecret ringSecret Zero
  let Smudge := smudgeBootstrappingKey
    (ringRank := ringRank) (tgswLevels := tgswLevels)
    (lweDimension := lweDimension) wideNoise
  let WideResidualKey := generateResidualBootstrappingKey
    q degree ringRank tgswLevels lweDimension wideNoise gadget
      lweSecret ringSecret Zero
  let Direct := BootstrapSecurity.generateDirectBootstrappingKey
    q degree ringRank tgswLevels lweDimension wideNoise gadget
      lweSecret ringSecret
  have hZero : evalDist ZeroKey = evalDist (AssembleZero <$> Fresh) := by
    simpa only [ZeroKey, AssembleZero, Fresh, Zero] using
      (generateResidualBootstrappingKey_zero_evalDist_eq_assembleFreshMask
        q degree ringRank tgswLevels lweDimension gadget lweSecret ringSecret Zero)
  have hSmudgedZero :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hZero Smudge
  have hFixed : evalDist ((AssembleZero <$> Fresh) >>= Smudge) =
      evalDist (Fresh >>= fixedMaskWideKey wideNoise gadget lweSecret ringSecret) := by
    simp only [map_eq_bind_pure_comp, bind_assoc]
    refine evalDist_bind_congr' Fresh fun mask ↦ ?_
    have hresidual := smudgeBootstrappingKey_assembleResidual_evalDist
      wideNoise gadget lweSecret ringSecret Zero mask
    exact hresidual.trans
      (by simpa only [Zero] using
        (fixedMaskResidualSmudgedKey_zero_evalDist_eq_fixedMaskWideKey
          wideNoise gadget lweSecret ringSecret mask))
  have hZeroThen : evalDist (ZeroKey >>= Smudge) = evalDist WideResidualKey := by
    simpa only [ZeroKey, Smudge, WideResidualKey, Zero] using
      (generateResidualBootstrappingKey_zero_then_smudge_evalDist
        q degree ringRank tgswLevels lweDimension wideNoise gadget
        lweSecret ringSecret Zero)
  have hResidualDirect : evalDist WideResidualKey = evalDist Direct := by
    have hbound := tvDist_generateResidualBootstrappingKey_generateDirect_le
      q degree ringRank tgswLevels lweDimension wideNoise gadget
      lweSecret ringSecret Zero
    have hle : tvDist WideResidualKey Direct ≤
        bootstrappingSmudgingCost wideNoise Zero := by
      simpa only [WideResidualKey, Direct, Zero] using hbound
    have hzero : tvDist WideResidualKey Direct = 0 :=
      le_antisymm (by
        exact hle.trans_eq
          (bootstrappingSmudgingCost_zero
            (ringRank := ringRank) (tgswLevels := tgswLevels)
            (lweDimension := lweDimension) wideNoise))
        (tvDist_nonneg _ _)
    exact (tvDist_eq_zero_iff _ _).mp hzero
  exact hFixed.symm.trans
    (hSmudgedZero.symm.trans (hZeroThen.trans hResidualDirect))

/-- Monomial native BRK generation is the same fresh-mask/wide-noise endpoint. -/
theorem sampleFreshBootstrappingMask_fixedMaskWideKey_evalDist_eq_generateMonomial
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist
        (sampleFreshBootstrappingMask q degree ringRank tgswLevels lweDimension >>=
          fixedMaskWideKey wideNoise gadget lweSecret ringSecret) =
      evalDist
        (BootstrapSecurity.MonomialKDM.generateBootstrappingKey
          q degree ringRank tgswLevels lweDimension wideNoise gadget
          lweSecret ringSecret) := by
  rw [BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct]
  exact sampleFreshBootstrappingMask_fixedMaskWideKey_evalDist_eq_generateDirect
    q degree ringRank tgswLevels lweDimension wideNoise gadget
    lweSecret ringSecret

/-- Native key-switch generation with a fixed residual added before every fresh wide error. -/
def generateResidualKeySwitchKey
    (q degree ringRank lweDimension keySwitchLevels : ℕ) [NeZero q]
    (wideNoise : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank degree)
    (lweSecret : BinarySecret lweDimension)
    (residual : KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
  TLWE.batchEncryptWithResidual lweDimension ((ringRank * degree) * keySwitchLevels)
    wideNoise (embedBinarySecret lweSecret)
    (keySwitchMessages (ringRank * degree) keySwitchLevels gadget (keyExtract ringSecret))
    residual

/-- Conditional smudging for the complete real native key-switch table. -/
theorem tvDist_generateResidualKeySwitchKey_generateKeySwitchKey_le
    (q degree ringRank lweDimension keySwitchLevels : ℕ) [NeZero q]
    (wideNoise : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank degree)
    (lweSecret : BinarySecret lweDimension)
    (residual : KeySwitchResidual q ringRank degree keySwitchLevels) :
    tvDist
        (generateResidualKeySwitchKey q degree ringRank lweDimension keySwitchLevels
          wideNoise gadget ringSecret lweSecret residual)
        (generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
          wideNoise gadget (keyExtract ringSecret) lweSecret) ≤
      keySwitchSmudgingCost wideNoise residual := by
  unfold generateResidualKeySwitchKey generateKeySwitchKey keySwitchSmudgingCost
  exact TLWE.tvDist_batchEncryptWithResidual_batchEncrypt_le_sum
    lweDimension ((ringRank * degree) * keySwitchLevels) wideNoise
    (embedBinarySecret lweSecret)
    (keySwitchMessages (ringRank * degree) keySwitchLevels gadget (keyExtract ringSecret))
    residual

/-- Complete fixed-secret BRK+KSK residual normal form.  The two components use independent wide
noise, as in native evaluation-key generation. -/
noncomputable def generateResidualEvaluationKeyPair
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (ringResidual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension ×
      KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) := do
  let bootstrappingKey ← generateResidualBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringWideNoise tgswGadget
    lweSecret ringSecret ringResidual
  let keySwitchKey ← generateResidualKeySwitchKey
    q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
    ringSecret lweSecret keySwitchResidual
  return (bootstrappingKey, keySwitchKey)

/-- Fixed-secret widened real pair in the exact monomial-CircLWE presentation. -/
noncomputable def generateMonomialEvaluationKeyPair
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension ×
      KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) := do
  let bootstrappingKey ← BootstrapSecurity.MonomialKDM.generateBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringWideNoise tgswGadget
    lweSecret ringSecret
  let keySwitchKey ← generateKeySwitchKey
    q lweDimension (ringRank * degree) keySwitchLevels keySwitchWideNoise keySwitchGadget
    (keyExtract ringSecret) lweSecret
  return (bootstrappingKey, keySwitchKey)

/-- The full native fixed-secret residual pair is close to its fresh widened real target by the
sum of the heterogeneous BRK and KSK translation costs. -/
theorem tvDist_generateResidualEvaluationKeyPair_generateMonomial_le
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (ringResidual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : KeySwitchResidual q ringRank degree keySwitchLevels) :
    tvDist
        (generateResidualEvaluationKeyPair q degree ringRank tgswLevels lweDimension
          keySwitchLevels ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
          lweSecret ringSecret ringResidual keySwitchResidual)
        (generateMonomialEvaluationKeyPair q degree ringRank tgswLevels lweDimension
          keySwitchLevels ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
          lweSecret ringSecret) ≤
      evaluationKeySmudgingCost ringWideNoise keySwitchWideNoise
        ringResidual keySwitchResidual := by
  let residualBootstrap := generateResidualBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringWideNoise tgswGadget
    lweSecret ringSecret ringResidual
  let targetBootstrap := BootstrapSecurity.MonomialKDM.generateBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringWideNoise tgswGadget
    lweSecret ringSecret
  let residualSwitch := generateResidualKeySwitchKey
    q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
    ringSecret lweSecret keySwitchResidual
  let targetSwitch := generateKeySwitchKey
    q lweDimension (ringRank * degree) keySwitchLevels keySwitchWideNoise keySwitchGadget
    (keyExtract ringSecret) lweSecret
  have hpair := SamplerReplacement.tvDist_independentPair_le
    residualBootstrap targetBootstrap residualSwitch targetSwitch
      (fun bootstrap switchKey ↦ (bootstrap, switchKey))
  have hbootstrap : tvDist residualBootstrap targetBootstrap ≤
      bootstrappingSmudgingCost ringWideNoise ringResidual :=
    tvDist_generateResidualBootstrappingKey_generateMonomial_le
      q degree ringRank tgswLevels lweDimension ringWideNoise tgswGadget
      lweSecret ringSecret ringResidual
  have hswitch : tvDist residualSwitch targetSwitch ≤
      keySwitchSmudgingCost keySwitchWideNoise keySwitchResidual :=
    tvDist_generateResidualKeySwitchKey_generateKeySwitchKey_le
      q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
      ringSecret lweSecret keySwitchResidual
  have h := hpair.trans (add_le_add hbootstrap hswitch)
  simpa [generateResidualEvaluationKeyPair, generateMonomialEvaluationKeyPair,
      SamplerReplacement.independentPair, residualBootstrap, targetBootstrap,
      residualSwitch, targetSwitch, evaluationKeySmudgingCost,
      map_eq_bind_pure_comp, Function.comp_apply, monad_norm] using h

end

end FormalProof4FHE.TFHE.Native.ConditionalSmudging
