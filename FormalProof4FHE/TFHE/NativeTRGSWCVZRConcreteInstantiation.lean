/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomialMoment
import FormalProof4FHE.TFHE.CenteredBinomialInstantiation
import FormalProof4FHE.TFHE.CutCycleSecurity
import FormalProof4FHE.TFHE.NativeTRGSWCVZRReduction
import FormalProof4FHE.TFHE.SharedRandomnessOneCycle

/-!
# Concrete native CVZR source layout and CBD side builder

This module instantiates the technical part of the known-suffix CVZR reduction for the native
shared-prefix/suffix TFHE layout.  It makes three implementation-facing facts explicit.

* The complete source batch is partitioned injectively into every homogeneous BRK row and every
  suffix-only native KSK row.
* Extracting a fixed public coefficient from independent coefficientwise-CBD ring errors gives
  exactly the complete IID scalar-CBD KSK error vector.  This is a joint-vector equality, not a
  collection of marginal claims.
* The corresponding extracted KSK sampler has exactly the native `generateKeySwitchKey` law for
  every fixed prefix and suffix key.

Thus the native affine KSK no longer remains an abstract `SideBuild` premise.  What remains after
this module is the cryptographic prefix-subspace RLWE assumption and any auxiliary object beyond
the native suffix-only KSK.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.NativeTRGSWCVZRConcreteInstantiation

noncomputable section

open Native.CoefficientStructuredLWE
open NativeTRGSWCVZRReduction
open Native.SharedRandomnessOneCycle

/-! ## Exact source-row partition -/

/-- Number of homogeneous ring rows in one native zero-message BRK. -/
abbrev brkSourceRowCount (prefixDimension tgswLevels : ℕ) : ℕ :=
  prefixDimension * TGSW.rowCount 1 tgswLevels

/-- Number of ring source rows consumed by the native suffix-only KSK builder. -/
abbrev kskSourceRowCount (suffixDimension keySwitchLevels : ℕ) : ℕ :=
  suffixDimension * keySwitchLevels

/-- Total number of disjoint prefix-RLWE rows required for one native CVZR view. -/
abbrev sourceRowCount
    (prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) : ℕ :=
  brkSourceRowCount prefixDimension tgswLevels +
    kskSourceRowCount suffixDimension keySwitchLevels

/-- Address one BRK row in the first source block. -/
def brkSourceIndex
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (coordinate : Fin prefixDimension) (row : Fin (TGSW.rowCount 1 tgswLevels)) :
    Fin (sourceRowCount prefixDimension suffixDimension tgswLevels keySwitchLevels) :=
  Fin.castAdd (kskSourceRowCount suffixDimension keySwitchLevels)
    (finProdFinEquiv (coordinate, row))

/-- Address one KSK row in the second source block. -/
def kskSourceIndex
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (coordinate : Fin suffixDimension) (level : Fin keySwitchLevels) :
    Fin (sourceRowCount prefixDimension suffixDimension tgswLevels keySwitchLevels) :=
  Fin.natAdd (brkSourceRowCount prefixDimension tgswLevels)
    (finProdFinEquiv (coordinate, level))

/-- The two native row families form an explicit equivalence with the complete source index. -/
def sourceIndexEquiv
    (prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :
    ((Fin prefixDimension × Fin (TGSW.rowCount 1 tgswLevels)) ⊕
      (Fin suffixDimension × Fin keySwitchLevels)) ≃
      Fin (sourceRowCount prefixDimension suffixDimension tgswLevels keySwitchLevels) :=
  (Equiv.sumCongr
      (finProdFinEquiv (m := prefixDimension) (n := TGSW.rowCount 1 tgswLevels))
      (finProdFinEquiv (m := suffixDimension) (n := keySwitchLevels))).trans
    finSumFinEquiv

@[simp]
theorem sourceIndexEquiv_inl
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (coordinate : Fin prefixDimension) (row : Fin (TGSW.rowCount 1 tgswLevels)) :
    sourceIndexEquiv prefixDimension suffixDimension tgswLevels keySwitchLevels
        (Sum.inl (coordinate, row)) =
      brkSourceIndex (suffixDimension := suffixDimension)
        (keySwitchLevels := keySwitchLevels) coordinate row := by
  rfl

@[simp]
theorem sourceIndexEquiv_inr
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (coordinate : Fin suffixDimension) (level : Fin keySwitchLevels) :
    sourceIndexEquiv prefixDimension suffixDimension tgswLevels keySwitchLevels
        (Sum.inr (coordinate, level)) =
      kskSourceIndex (prefixDimension := prefixDimension)
        (tgswLevels := tgswLevels) coordinate level := by
  rfl

theorem brkSourceIndex_injective
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} :
    Function.Injective
      (fun pair : Fin prefixDimension × Fin (TGSW.rowCount 1 tgswLevels) ↦
        brkSourceIndex (suffixDimension := suffixDimension)
          (keySwitchLevels := keySwitchLevels) pair.1 pair.2) := by
  intro left right heq
  have hindexed :
      sourceIndexEquiv prefixDimension suffixDimension tgswLevels keySwitchLevels
          (Sum.inl left) =
        sourceIndexEquiv prefixDimension suffixDimension tgswLevels keySwitchLevels
          (Sum.inl right) := by
    change brkSourceIndex (suffixDimension := suffixDimension)
        (keySwitchLevels := keySwitchLevels) left.1 left.2 =
      brkSourceIndex (suffixDimension := suffixDimension)
        (keySwitchLevels := keySwitchLevels) right.1 right.2
    exact heq
  exact Sum.inl.inj
    ((sourceIndexEquiv prefixDimension suffixDimension tgswLevels
      keySwitchLevels).injective hindexed)

theorem kskSourceIndex_injective
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} :
    Function.Injective
      (fun pair : Fin suffixDimension × Fin keySwitchLevels ↦
        kskSourceIndex (prefixDimension := prefixDimension)
          (tgswLevels := tgswLevels) pair.1 pair.2) := by
  intro left right heq
  have hindexed :
      sourceIndexEquiv prefixDimension suffixDimension tgswLevels keySwitchLevels
          (Sum.inr left) =
        sourceIndexEquiv prefixDimension suffixDimension tgswLevels keySwitchLevels
          (Sum.inr right) := by
    change kskSourceIndex (prefixDimension := prefixDimension)
        (tgswLevels := tgswLevels) left.1 left.2 =
      kskSourceIndex (prefixDimension := prefixDimension)
        (tgswLevels := tgswLevels) right.1 right.2
    exact heq
  exact Sum.inr.inj
    ((sourceIndexEquiv prefixDimension suffixDimension tgswLevels
      keySwitchLevels).injective hindexed)

theorem brkSourceIndex_ne_kskSourceIndex
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (brkCoordinate : Fin prefixDimension)
    (brkRow : Fin (TGSW.rowCount 1 tgswLevels))
    (kskCoordinate : Fin suffixDimension) (kskLevel : Fin keySwitchLevels) :
    brkSourceIndex (suffixDimension := suffixDimension)
        (keySwitchLevels := keySwitchLevels) brkCoordinate brkRow ≠
      kskSourceIndex (prefixDimension := prefixDimension)
        (tgswLevels := tgswLevels) kskCoordinate kskLevel := by
  intro heq
  have hindexed :
      sourceIndexEquiv prefixDimension suffixDimension tgswLevels keySwitchLevels
          (Sum.inl (brkCoordinate, brkRow)) =
        sourceIndexEquiv prefixDimension suffixDimension tgswLevels keySwitchLevels
          (Sum.inr (kskCoordinate, kskLevel)) := by
    change brkSourceIndex (suffixDimension := suffixDimension)
        (keySwitchLevels := keySwitchLevels) brkCoordinate brkRow =
      kskSourceIndex (prefixDimension := prefixDimension)
        (tgswLevels := tgswLevels) kskCoordinate kskLevel
    exact heq
  have hfalse := (sourceIndexEquiv prefixDimension suffixDimension tgswLevels
    keySwitchLevels).injective hindexed
  cases hfalse

/-! ## Whole-batch extracted masks -/

/-- Row-major collection of all prefix masks extracted from independent ring masks. -/
def extractedMaskRows
    {q prefixDimension suffixDegree rowCount : ℕ}
    (output : Fin rowCount → Fin (prefixDimension + (suffixDegree + 1)))
    (challenge : Fin rowCount →
      AmbientCoefficients q prefixDimension suffixDegree) :
    Fin rowCount → (Fin prefixDimension → ZMod q) :=
  fun row ↦ prefixExtractedMask (output row) (challenge row)

/-- Transpose row-major extracted masks into the native TLWE batch-matrix convention. -/
def extractedMaskMatrix
    {q prefixDimension suffixDegree rowCount : ℕ}
    (output : Fin rowCount → Fin (prefixDimension + (suffixDegree + 1)))
    (challenge : Fin rowCount →
      AmbientCoefficients q prefixDimension suffixDegree) :
    Matrix (Fin prefixDimension) (Fin rowCount) (ZMod q) :=
  fun coordinate row ↦ prefixExtractedMask (output row) (challenge row) coordinate

/-- Swapping the two function arguments is an equivalence. -/
def functionFlipEquiv (A B C : Type) : (A → B → C) ≃ (B → A → C) where
  toFun values b a := values a b
  invFun values a b := values b a
  left_inv _ := rfl
  right_inv _ := rfl

theorem extractedMaskMatrix_eq_flip
    {q prefixDimension suffixDegree rowCount : ℕ}
    (output : Fin rowCount → Fin (prefixDimension + (suffixDegree + 1)))
    (challenge : Fin rowCount →
      AmbientCoefficients q prefixDimension suffixDegree) :
    extractedMaskMatrix output challenge =
      functionFlipEquiv (Fin rowCount) (Fin prefixDimension) (ZMod q)
        (extractedMaskRows output challenge) := by
  rfl

/-- All extracted KSK masks are jointly uniform.  Outputs may select different public
coefficients in different rows. -/
theorem extractedMaskRows_uniform_evalDist
    (q prefixDimension suffixDegree rowCount : ℕ) [NeZero q]
    (output : Fin rowCount → Fin (prefixDimension + (suffixDegree + 1))) :
    evalDist (extractedMaskRows output <$>
        ($ᵗ (Fin rowCount → AmbientCoefficients q prefixDimension suffixDegree))) =
      evalDist ($ᵗ (Fin rowCount → (Fin prefixDimension → ZMod q))) := by
  let RingMask := AmbientCoefficients q prefixDimension suffixDegree
  let PrefixMask := Fin prefixDimension → ZMod q
  have hsource :=
    (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := RingMask) rowCount).symm
  have hmapped := evalDist_map_eq_of_evalDist_eq hsource (extractedMaskRows output)
  have hcommute := FormalProof4FHE.FiniteProduct.map_fin_mOfFn rowCount
    (fun _ ↦ ($ᵗ RingMask : ProbComp RingMask))
    (fun row value ↦ prefixExtractedMask (output row) value)
  have hrows :
      evalDist (Fin.mOfFn rowCount fun row ↦
          prefixExtractedMask (output row) <$> ($ᵗ RingMask)) =
        evalDist (Fin.mOfFn rowCount fun _ ↦ ($ᵗ PrefixMask)) := by
    apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
    intro row
    exact prefixExtractedMask_uniform_evalDist
      q prefixDimension suffixDegree (output row)
  calc
    evalDist (extractedMaskRows output <$> ($ᵗ (Fin rowCount → RingMask))) =
        evalDist (extractedMaskRows output <$>
          ProbComp.sampleIID rowCount ($ᵗ RingMask)) := hmapped
    _ = evalDist (Fin.mOfFn rowCount fun row ↦
          prefixExtractedMask (output row) <$> ($ᵗ RingMask)) := by
      change evalDist
          ((fun values row ↦ prefixExtractedMask (output row) (values row)) <$>
            Fin.mOfFn rowCount (fun _ ↦ ($ᵗ RingMask : ProbComp RingMask))) = _
      exact congrArg evalDist hcommute
    _ = evalDist (Fin.mOfFn rowCount fun _ ↦ ($ᵗ PrefixMask)) := hrows
    _ = evalDist ($ᵗ (Fin rowCount → PrefixMask)) :=
      FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform rowCount

/-- Native matrix form of the preceding joint-uniformity theorem. -/
theorem extractedMaskMatrix_uniform_evalDist
    (q prefixDimension suffixDegree rowCount : ℕ) [NeZero q]
    (output : Fin rowCount → Fin (prefixDimension + (suffixDegree + 1))) :
    evalDist (extractedMaskMatrix output <$>
        ($ᵗ (Fin rowCount → AmbientCoefficients q prefixDimension suffixDegree))) =
      evalDist ($ᵗ (Matrix (Fin prefixDimension) (Fin rowCount) (ZMod q))) := by
  have hrows := extractedMaskRows_uniform_evalDist
    q prefixDimension suffixDegree rowCount output
  have hflip :
      evalDist ((functionFlipEquiv (Fin rowCount) (Fin prefixDimension) (ZMod q) :
          (Fin rowCount → (Fin prefixDimension → ZMod q)) →
            Matrix (Fin prefixDimension) (Fin rowCount) (ZMod q)) <$>
        ($ᵗ (Fin rowCount → (Fin prefixDimension → ZMod q)))) =
      evalDist ($ᵗ (Matrix (Fin prefixDimension) (Fin rowCount) (ZMod q))) :=
    evalDist_map_bijective_uniform_cross
      (α := Fin rowCount → (Fin prefixDimension → ZMod q))
      (β := Matrix (Fin prefixDimension) (Fin rowCount) (ZMod q))
      (functionFlipEquiv (Fin rowCount) (Fin prefixDimension) (ZMod q))
      (functionFlipEquiv (Fin rowCount) (Fin prefixDimension) (ZMod q)).bijective
  have hdefinition :
      evalDist (extractedMaskMatrix output <$>
          ($ᵗ (Fin rowCount → AmbientCoefficients q prefixDimension suffixDegree))) =
        evalDist ((functionFlipEquiv (Fin rowCount) (Fin prefixDimension) (ZMod q) :
            (Fin rowCount → (Fin prefixDimension → ZMod q)) →
              Matrix (Fin prefixDimension) (Fin rowCount) (ZMod q)) <$>
          (extractedMaskRows output <$>
            ($ᵗ (Fin rowCount → AmbientCoefficients q prefixDimension suffixDegree)))) := by
    simp only [Functor.map_map]
    congr 1
  have hmapped :
      evalDist ((functionFlipEquiv (Fin rowCount) (Fin prefixDimension) (ZMod q) :
          (Fin rowCount → (Fin prefixDimension → ZMod q)) →
            Matrix (Fin prefixDimension) (Fin rowCount) (ZMod q)) <$>
        (extractedMaskRows output <$>
          ($ᵗ (Fin rowCount → AmbientCoefficients q prefixDimension suffixDegree)))) =
      evalDist ((functionFlipEquiv (Fin rowCount) (Fin prefixDimension) (ZMod q) :
          (Fin rowCount → (Fin prefixDimension → ZMod q)) →
            Matrix (Fin prefixDimension) (Fin rowCount) (ZMod q)) <$>
        ($ᵗ (Fin rowCount → (Fin prefixDimension → ZMod q)))) :=
    evalDist_map_eq_of_evalDist_eq hrows
      (functionFlipEquiv (Fin rowCount) (Fin prefixDimension) (ZMod q))
  exact hdefinition.trans (hmapped.trans hflip)

/-! ## Exact joint CBD extraction law -/

/-- Select one public coefficient from every coefficient-form ring error. -/
def selectedErrorVector
    {q degree rowCount : ℕ}
    (output : Fin rowCount → Fin degree)
    (errors : Fin rowCount → Coefficients q degree) : Fin rowCount → ZMod q :=
  fun row ↦ errors row (output row)

/-- One coefficient of the ring CBD sampler has exactly the native scalar CBD law. -/
theorem selectedCoefficient_cbd_evalDist
    (q degree eta : ℕ) [NeZero q] (output : Fin degree) :
    evalDist ((fun error : RLWE.Rq q degree ↦
        coefficientEquiv q degree error output) <$>
      RLWE.CenteredBinomial.sampler q degree eta) =
      evalDist (CenteredBinomial.scalarSampler q eta) := by
  let select := fun coefficients : Fin degree → ZMod q ↦ coefficients output
  have hvectors := RLWE.CenteredBinomial.coefficientVector_sampler_evalDist q degree eta
  have hselect := evalDist_map_eq_of_evalDist_eq hvectors select
  have hcoordinate := FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply
    degree (fun _ ↦ RLWE.CenteredBinomial.coefficientSampler q eta) output id
  calc
    evalDist ((fun error : RLWE.Rq q degree ↦
        coefficientEquiv q degree error output) <$>
      RLWE.CenteredBinomial.sampler q degree eta) =
      evalDist (select <$> (RLWE.CenteredBinomial.coefficientVector <$>
        RLWE.CenteredBinomial.sampler q degree eta)) := by
          simp only [Functor.map_map]
          congr 1
    _ = evalDist (select <$> ProbComp.sampleIID degree
          (RLWE.CenteredBinomial.coefficientSampler q eta)) := hselect
    _ = evalDist (RLWE.CenteredBinomial.coefficientSampler q eta) := by
      simpa [ProbComp.sampleIID, select] using hcoordinate
    _ = evalDist (CenteredBinomial.scalarSampler q eta) := by
      congr 1
      simp [RLWE.CenteredBinomial.coefficientSampler,
        CenteredBinomial.scalarSampler, CenteredBinomial.scalarErrorFromCoins,
        map_eq_bind_pure_comp, monad_norm]

/-- Selecting coefficients from the complete IID ring-CBD error batch gives exactly the complete
IID scalar-CBD KSK error vector. -/
theorem selectedErrorVector_cbd_evalDist
    (q degree rowCount eta : ℕ) [NeZero q]
    (output : Fin rowCount → Fin degree) :
    evalDist (selectedErrorVector output <$>
        ProbComp.sampleIID rowCount
          (coefficientEquiv q degree <$> RLWE.CenteredBinomial.sampler q degree eta)) =
      evalDist (ProbComp.sampleIID rowCount
        (CenteredBinomial.scalarSampler q eta)) := by
  have hcommute := FormalProof4FHE.FiniteProduct.map_fin_mOfFn rowCount
    (fun _ ↦ coefficientEquiv q degree <$>
      RLWE.CenteredBinomial.sampler q degree eta)
    (fun row coefficients ↦ coefficients (output row))
  calc
    evalDist (selectedErrorVector output <$>
        ProbComp.sampleIID rowCount
          (coefficientEquiv q degree <$> RLWE.CenteredBinomial.sampler q degree eta)) =
      evalDist (Fin.mOfFn rowCount fun row ↦
        (fun coefficients : Coefficients q degree ↦ coefficients (output row)) <$>
          (coefficientEquiv q degree <$>
            RLWE.CenteredBinomial.sampler q degree eta)) := by
        change evalDist
            ((fun values row ↦ values row (output row)) <$>
              Fin.mOfFn rowCount (fun _ ↦ coefficientEquiv q degree <$>
                RLWE.CenteredBinomial.sampler q degree eta)) = _
        exact congrArg evalDist hcommute
    _ = evalDist (Fin.mOfFn rowCount fun _ ↦
          CenteredBinomial.scalarSampler q eta) := by
      apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
      intro row
      simpa only [Functor.map_map, Function.comp_apply] using
        selectedCoefficient_cbd_evalDist q degree eta (output row)
    _ = _ := by rfl

/-! ## Native suffix-only KSK instantiated from coefficient-form source rows -/

/-- The fixed coefficient selected from every KSK source ring row.  The ambient degree is
positive because the suffix block has size `suffixDegree + 1`. -/
def nativeKSKOutput
    (prefixDimension suffixDegree rowCount : ℕ) :
    Fin rowCount → Fin (prefixDimension + (suffixDegree + 1)) :=
  fun _ ↦ 0

/-- Public native suffix-only KSK builder from its disjoint coefficient-form source block. -/
def buildNativeKSK
    {q prefixDimension suffixDegree keySwitchLevels : ℕ}
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (suffixKey : BinarySecret (suffixDegree + 1))
    (samples : Fin ((suffixDegree + 1) * keySwitchLevels) →
      AmbientCoefficients q prefixDimension suffixDegree ×
        AmbientCoefficients q prefixDimension suffixDegree) :
    SharedKeySwitchKey q prefixDimension (suffixDegree + 1) keySwitchLevels :=
  extractKSKBatch
    (nativeKSKOutput prefixDimension suffixDegree
      ((suffixDegree + 1) * keySwitchLevels))
    (Native.keySwitchMessages (suffixDegree + 1) keySwitchLevels
      keySwitchGadget suffixKey)
    samples

/-- Pointwise real-source identity for the complete native KSK. -/
theorem buildNativeKSK_real
    {q prefixDimension suffixDegree keySwitchLevels : ℕ}
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1))
    (challenge error : Fin ((suffixDegree + 1) * keySwitchLevels) →
      AmbientCoefficients q prefixDimension suffixDegree) :
    buildNativeKSK keySwitchGadget suffixKey
        (fun row ↦ (challenge row,
          negacyclicProduct
              (prefixCoefficients q prefixDimension suffixDegree prefixKey)
              (challenge row) + error row)) =
      TLWE.batchAssemble (embedBinarySecret prefixKey)
        (extractedMaskMatrix
          (nativeKSKOutput prefixDimension suffixDegree
            ((suffixDegree + 1) * keySwitchLevels)) challenge)
        (Native.keySwitchMessages (suffixDegree + 1) keySwitchLevels
          keySwitchGadget suffixKey)
        (selectedErrorVector
          (nativeKSKOutput prefixDimension suffixDegree
            ((suffixDegree + 1) * keySwitchLevels)) error) := by
  exact extractKSKBatch_real prefixKey challenge error
    (nativeKSKOutput prefixDimension suffixDegree
      ((suffixDegree + 1) * keySwitchLevels))
    (Native.keySwitchMessages (suffixDegree + 1) keySwitchLevels
      keySwitchGadget suffixKey)

/-- Coefficient presentation of the ring CBD sampler used by the KSK source rows. -/
def coefficientCBDRingSampler
    (q degree eta : ℕ) [NeZero q] : ProbComp (Coefficients q degree) :=
  coefficientEquiv q degree <$> RLWE.CenteredBinomial.sampler q degree eta

/-- Fixed-key native KSK generated entirely from disjoint prefix-RLWE-form ring rows. -/
def extractedNativeKSKSampler
    (q prefixDimension suffixDegree keySwitchLevels eta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    ProbComp (SharedKeySwitchKey q prefixDimension (suffixDegree + 1) keySwitchLevels) := do
  let challenge ← $ᵗ (Fin ((suffixDegree + 1) * keySwitchLevels) →
    AmbientCoefficients q prefixDimension suffixDegree)
  let error ← ProbComp.sampleIID ((suffixDegree + 1) * keySwitchLevels)
    (coefficientCBDRingSampler q (prefixDimension + (suffixDegree + 1)) eta)
  return buildNativeKSK keySwitchGadget suffixKey
    (fun row ↦
      (challenge row,
        negacyclicProduct
            (prefixCoefficients q prefixDimension suffixDegree prefixKey)
            (challenge row) + error row))

/-- The native affine KSK `SideBuild` premise is exact for coefficientwise CBD errors.  The
statement compares the complete KSK sampler, so mask and error independence and every rowwise
correlation are included in one distributional equality. -/
theorem extractedNativeKSKSampler_evalDist_eq_generateKeySwitchKey
    (q prefixDimension suffixDegree keySwitchLevels eta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    evalDist (extractedNativeKSKSampler q prefixDimension suffixDegree
        keySwitchLevels eta keySwitchGadget prefixKey suffixKey) =
      evalDist (generateKeySwitchKey q prefixDimension (suffixDegree + 1)
        keySwitchLevels (CenteredBinomial.scalarSampler q eta) keySwitchGadget
        (nestedRingSecret prefixKey suffixKey)) := by
  let count := (suffixDegree + 1) * keySwitchLevels
  let degree := prefixDimension + (suffixDegree + 1)
  let output := nativeKSKOutput prefixDimension suffixDegree count
  let challenges : ProbComp (Fin count → AmbientCoefficients q prefixDimension suffixDegree) :=
    $ᵗ (Fin count → AmbientCoefficients q prefixDimension suffixDegree)
  let errors : ProbComp (Fin count → AmbientCoefficients q prefixDimension suffixDegree) :=
    ProbComp.sampleIID count (coefficientCBDRingSampler q degree eta)
  let maskSampler : ProbComp (Matrix (Fin prefixDimension) (Fin count) (ZMod q)) :=
    extractedMaskMatrix output <$> challenges
  let selectedErrors : ProbComp (Fin count → ZMod q) :=
    selectedErrorVector output <$> errors
  let messages := Native.keySwitchMessages (suffixDegree + 1) keySwitchLevels
    keySwitchGadget suffixKey
  let finish : Matrix (Fin prefixDimension) (Fin count) (ZMod q) →
      (Fin count → ZMod q) →
      ProbComp (SharedKeySwitchKey q prefixDimension (suffixDegree + 1)
        keySwitchLevels) :=
    fun mask error ↦
      pure (TLWE.batchAssemble (embedBinarySecret prefixKey) mask messages error)
  have hnormalize :
      evalDist (extractedNativeKSKSampler q prefixDimension suffixDegree
          keySwitchLevels eta keySwitchGadget prefixKey suffixKey) =
        evalDist (maskSampler >>= fun mask ↦ selectedErrors >>= finish mask) := by
    unfold extractedNativeKSKSampler
    change evalDist (challenges >>= fun challenge ↦ errors >>= fun error ↦
      pure (buildNativeKSK keySwitchGadget suffixKey
        (fun row ↦ (challenge row,
          negacyclicProduct
              (prefixCoefficients q prefixDimension suffixDegree prefixKey)
              (challenge row) + error row)))) = _
    simp only [maskSampler, selectedErrors, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
    refine evalDist_bind_congr' challenges fun challenge ↦ ?_
    refine evalDist_bind_congr' errors fun error ↦ ?_
    exact congrArg evalDist (congrArg pure
      (buildNativeKSK_real keySwitchGadget prefixKey suffixKey challenge error))
  have hmask : evalDist maskSampler =
      evalDist ($ᵗ (Matrix (Fin prefixDimension) (Fin count) (ZMod q))) := by
    exact extractedMaskMatrix_uniform_evalDist
      q prefixDimension suffixDegree count output
  have herror : evalDist selectedErrors =
      evalDist (ProbComp.sampleIID count (CenteredBinomial.scalarSampler q eta)) := by
    exact selectedErrorVector_cbd_evalDist q degree count eta output
  rw [hnormalize]
  calc
    evalDist (maskSampler >>= fun mask ↦ selectedErrors >>= finish mask) =
      evalDist (($ᵗ (Matrix (Fin prefixDimension) (Fin count) (ZMod q))) >>=
        fun mask ↦ selectedErrors >>= finish mask) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hmask (fun mask ↦ selectedErrors >>= finish mask)
    _ = evalDist (($ᵗ (Matrix (Fin prefixDimension) (Fin count) (ZMod q))) >>=
        fun mask ↦ ProbComp.sampleIID count (CenteredBinomial.scalarSampler q eta) >>=
          finish mask) := by
      apply evalDist_bind_congr'
      intro mask
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        herror (finish mask)
    _ = evalDist (generateKeySwitchKey q prefixDimension (suffixDegree + 1)
        keySwitchLevels (CenteredBinomial.scalarSampler q eta) keySwitchGadget
        (nestedRingSecret prefixKey suffixKey)) := by
      simp [generateKeySwitchKey, Native.generateKeySwitchKey, TLWE.batchEncrypt,
        count, messages, finish, monad_norm]

/-! ## Concrete homogeneous BRK transport -/

/-- Coefficient-form challenge/body storage for every row of a complete native rank-one BRK. -/
abbrev CoefficientZeroBRK
    (q prefixDimension suffixDegree tgswLevels : ℕ) :=
  Fin prefixDimension → HomogeneousRowBlock
    (AmbientCoefficients q prefixDimension suffixDegree)
    (TGSW.rowCount 1 tgswLevels)

/-- Convert one coefficient-form homogeneous row block to a native rank-one ciphertext. -/
def coefficientBlockToNative
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (block : HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree)
      (TGSW.rowCount 1 tgswLevels)) :
    TGSW.Ciphertext (RLWE.Rq q (prefixDimension + (suffixDegree + 1))) 1 tgswLevels :=
  (fun _component row ↦
      (coefficientEquiv q (prefixDimension + (suffixDegree + 1))).symm
        (block.1 row),
    fun row ↦
      (coefficientEquiv q (prefixDimension + (suffixDegree + 1))).symm
        (block.2 row))

/-- Convert a coefficient-form complete rank-one BRK to the literal native ring carrier. -/
def coefficientZeroBRKToNative
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (view : CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels) :
    SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels :=
  fun coordinate ↦ coefficientBlockToNative q prefixDimension suffixDegree tgswLevels
    (view coordinate)

/-- Recover coefficient-form storage from the native rank-one carrier. -/
def nativeZeroBRKToCoefficient
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (view : SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels) :
    CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels :=
  fun coordinate ↦
    (fun row ↦ coefficientEquiv q (prefixDimension + (suffixDegree + 1))
        ((view coordinate).1 0 row),
      fun row ↦ coefficientEquiv q (prefixDimension + (suffixDegree + 1))
        ((view coordinate).2 row))

@[simp]
theorem nativeZeroBRKToCoefficient_toNative
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (view : CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels) :
    nativeZeroBRKToCoefficient q prefixDimension suffixDegree tgswLevels
        (coefficientZeroBRKToNative q prefixDimension suffixDegree tgswLevels view) = view := by
  funext coordinate
  apply Prod.ext
  · funext row
    simp [nativeZeroBRKToCoefficient, coefficientZeroBRKToNative,
      coefficientBlockToNative]
  · funext row
    simp [nativeZeroBRKToCoefficient, coefficientZeroBRKToNative,
      coefficientBlockToNative]

@[simp]
theorem coefficientZeroBRKToNative_toCoefficient
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (view : SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels) :
    coefficientZeroBRKToNative q prefixDimension suffixDegree tgswLevels
        (nativeZeroBRKToCoefficient q prefixDimension suffixDegree tgswLevels view) = view := by
  funext coordinate
  apply Prod.ext
  · funext component row
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    simp [nativeZeroBRKToCoefficient, coefficientZeroBRKToNative,
      coefficientBlockToNative]
  · funext row
    simp [nativeZeroBRKToCoefficient, coefficientZeroBRKToNative,
      coefficientBlockToNative]

theorem coefficientZeroBRKToNative_bijective
    (q prefixDimension suffixDegree tgswLevels : ℕ) :
    Function.Bijective
      (coefficientZeroBRKToNative q prefixDimension suffixDegree tgswLevels) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨nativeZeroBRKToCoefficient q prefixDimension suffixDegree tgswLevels,
      nativeZeroBRKToCoefficient_toNative q prefixDimension suffixDegree tgswLevels,
      coefficientZeroBRKToNative_toCoefficient q prefixDimension suffixDegree tgswLevels⟩

/-- Coefficient and native complete-BRK carriers have the same canonical uniform law. -/
theorem coefficientZeroBRKToNative_uniform_evalDist
    (q prefixDimension suffixDegree tgswLevels : ℕ) [NeZero q] :
    evalDist (coefficientZeroBRKToNative q prefixDimension suffixDegree tgswLevels <$>
        ($ᵗ (CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels))) =
      evalDist ($ᵗ (SharedBootstrappingKey q prefixDimension
        (suffixDegree + 1) tgswLevels)) :=
  evalDist_map_bijective_uniform_cross
    (α := CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels)
    (β := SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels)
    (coefficientZeroBRKToNative q prefixDimension suffixDegree tgswLevels)
    (coefficientZeroBRKToNative_bijective q prefixDimension suffixDegree tgswLevels)

/-- Coefficients of the concrete nested binary ring key are exactly the prefix/suffix split used
by the CVZR source. -/
theorem coefficientEquiv_embedNestedRingSecret
    (q prefixDimension suffixDegree : ℕ)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    coefficientEquiv q (prefixDimension + (suffixDegree + 1))
        (embedRingSecret q (nestedRingSecret prefixKey suffixKey) 0) =
      splitSecretCoefficients q prefixDimension suffixDegree prefixKey
        (embedBinarySecret suffixKey) := by
  funext coordinate
  refine Fin.addCases ?_ ?_ coordinate
  · intro prefixCoordinate
    simp [embedRingSecret, nestedRingSecret, splitSecretCoefficients,
      binaryCoefficients, embedBinarySecret]
  · intro suffixCoordinate
    simp [embedRingSecret, nestedRingSecret, splitSecretCoefficients,
      binaryCoefficients, embedBinarySecret]

/-- Convert one coefficient-form rank-one challenge to the native one-component matrix. -/
def coefficientChallengeToNative
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (challenge : Fin (TGSW.rowCount 1 tgswLevels) →
      AmbientCoefficients q prefixDimension suffixDegree) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 tgswLevels))
      (RLWE.Rq q (prefixDimension + (suffixDegree + 1))) :=
  fun _component row ↦
    (coefficientEquiv q (prefixDimension + (suffixDegree + 1))).symm
      (challenge row)

/-- Convert one coefficient-form error vector to the native ring carrier. -/
def coefficientErrorToNative
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (error : Fin (TGSW.rowCount 1 tgswLevels) →
      AmbientCoefficients q prefixDimension suffixDegree) :
    Fin (TGSW.rowCount 1 tgswLevels) →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)) :=
  fun row ↦
    (coefficientEquiv q (prefixDimension + (suffixDegree + 1))).symm (error row)

/-- Pointwise conversion of a full-secret coefficient row block is the literal native rank-one
homogeneous TLWE assembly. -/
theorem coefficientFullSecretBlock_toNative
    {q prefixDimension suffixDegree tgswLevels : ℕ} [NeZero q]
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1))
    (challenge error : Fin (TGSW.rowCount 1 tgswLevels) →
      AmbientCoefficients q prefixDimension suffixDegree) :
    coefficientBlockToNative q prefixDimension suffixDegree tgswLevels
        (challenge, fun row ↦
          negacyclicProduct
              (splitSecretCoefficients q prefixDimension suffixDegree prefixKey
                (embedBinarySecret suffixKey))
              (challenge row) + error row) =
      TLWE.batchAssemble
        (embedRingSecret q (nestedRingSecret prefixKey suffixKey))
        (coefficientChallengeToNative challenge) 0
        (coefficientErrorToNative error) := by
  apply Prod.ext
  · funext component row
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    rfl
  · funext row
    apply (coefficientEquiv q (prefixDimension + (suffixDegree + 1))).injective
    simp only [coefficientBlockToNative, TLWE.batchAssemble, Pi.add_apply,
      Matrix.vecMul, dotProduct, coefficientErrorToNative]
    rw [Fin.sum_univ_one]
    simp [coefficientChallengeToNative, coefficientEquiv_add, coefficientEquiv_mul,
      coefficientEquiv_embedNestedRingSecret]

/-- Coefficient-form public masks for the complete native BRK. -/
abbrev CoefficientBRKChallenge
    (q prefixDimension suffixDegree tgswLevels : ℕ) :=
  Fin prefixDimension → Fin (TGSW.rowCount 1 tgswLevels) →
    AmbientCoefficients q prefixDimension suffixDegree

/-- Native ring-matrix public masks for the complete BRK. -/
abbrev NativeBRKChallenge
    (q prefixDimension suffixDegree tgswLevels : ℕ) :=
  Fin prefixDimension →
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 tgswLevels))
      (RLWE.Rq q (prefixDimension + (suffixDegree + 1)))

/-- Convert every coefficient-form BRK public mask to the literal native ring matrix. -/
def coefficientBRKChallengeToNative
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (challenge : CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels) :
    NativeBRKChallenge q prefixDimension suffixDegree tgswLevels :=
  fun coordinate ↦ coefficientChallengeToNative (challenge coordinate)

/-- Inverse public-mask representation map. -/
def nativeBRKChallengeToCoefficient
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (challenge : NativeBRKChallenge q prefixDimension suffixDegree tgswLevels) :
    CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels :=
  fun coordinate row ↦
    coefficientEquiv q (prefixDimension + (suffixDegree + 1))
      (challenge coordinate 0 row)

@[simp]
theorem nativeBRKChallengeToCoefficient_toNative
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (challenge : CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels) :
    nativeBRKChallengeToCoefficient q prefixDimension suffixDegree tgswLevels
        (coefficientBRKChallengeToNative q prefixDimension suffixDegree tgswLevels
          challenge) = challenge := by
  funext coordinate row
  simp [nativeBRKChallengeToCoefficient, coefficientBRKChallengeToNative,
    coefficientChallengeToNative]

@[simp]
theorem coefficientBRKChallengeToNative_toCoefficient
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (challenge : NativeBRKChallenge q prefixDimension suffixDegree tgswLevels) :
    coefficientBRKChallengeToNative q prefixDimension suffixDegree tgswLevels
        (nativeBRKChallengeToCoefficient q prefixDimension suffixDegree tgswLevels
          challenge) = challenge := by
  funext coordinate component row
  have hcomponent : component = 0 := Subsingleton.elim _ _
  subst component
  simp [nativeBRKChallengeToCoefficient, coefficientBRKChallengeToNative,
    coefficientChallengeToNative]

theorem coefficientBRKChallengeToNative_bijective
    (q prefixDimension suffixDegree tgswLevels : ℕ) :
    Function.Bijective
      (coefficientBRKChallengeToNative q prefixDimension suffixDegree tgswLevels) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨nativeBRKChallengeToCoefficient q prefixDimension suffixDegree tgswLevels,
      nativeBRKChallengeToCoefficient_toNative q prefixDimension suffixDegree tgswLevels,
      coefficientBRKChallengeToNative_toCoefficient q prefixDimension suffixDegree tgswLevels⟩

/-- Uniform coefficient-form BRK masks are exactly uniform native ring-matrix masks jointly. -/
theorem coefficientBRKChallengeToNative_uniform_evalDist
    (q prefixDimension suffixDegree tgswLevels : ℕ) [NeZero q] :
    evalDist
        (coefficientBRKChallengeToNative q prefixDimension suffixDegree tgswLevels <$>
          ($ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels))) =
      evalDist ($ᵗ (NativeBRKChallenge q prefixDimension suffixDegree tgswLevels)) :=
  evalDist_map_bijective_uniform_cross
    (α := CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
    (β := NativeBRKChallenge q prefixDimension suffixDegree tgswLevels)
    (coefficientBRKChallengeToNative q prefixDimension suffixDegree tgswLevels)
    (coefficientBRKChallengeToNative_bijective q prefixDimension suffixDegree tgswLevels)

/-- Publicly add the sampled binary suffix to every homogeneous BRK row and convert the result
to the literal native carrier. -/
def buildNativeZeroBRK
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (suffixKey : BinarySecret (suffixDegree + 1))
    (samples : Fin prefixDimension → HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree)
      (TGSW.rowCount 1 tgswLevels)) :
    SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels :=
  coefficientZeroBRKToNative q prefixDimension suffixDegree tgswLevels
    (fun coordinate ↦ addKnownSuffixCoefficientBlock
      (embedBinarySecret suffixKey) (samples coordinate))

/-- Complete pointwise real-source law for all homogeneous BRK rows. -/
theorem buildNativeZeroBRK_real
    {q prefixDimension suffixDegree tgswLevels : ℕ} [NeZero q]
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1))
    (challenge error : CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels) :
    buildNativeZeroBRK suffixKey
        (fun coordinate ↦
          (challenge coordinate, fun row ↦
            negacyclicProduct
                (prefixCoefficients q prefixDimension suffixDegree prefixKey)
                (challenge coordinate row) + error coordinate row)) =
      fun coordinate ↦
        TLWE.batchAssemble
          (embedRingSecret q (nestedRingSecret prefixKey suffixKey))
          (coefficientChallengeToNative (challenge coordinate)) 0
          (coefficientErrorToNative (error coordinate)) := by
  funext coordinate
  unfold buildNativeZeroBRK coefficientZeroBRKToNative
  change coefficientBlockToNative q prefixDimension suffixDegree tgswLevels
      (addKnownSuffixCoefficientBlock (embedBinarySecret suffixKey)
        (challenge coordinate, fun row ↦
          negacyclicProduct
              (prefixCoefficients q prefixDimension suffixDegree prefixKey)
              (challenge coordinate row) + error coordinate row)) = _
  rw [addKnownSuffixCoefficientBlock_real prefixKey
    (embedBinarySecret suffixKey) (challenge coordinate) (error coordinate)]
  exact coefficientFullSecretBlock_toNative prefixKey suffixKey
    (challenge coordinate) (error coordinate)

/-- Apply known-suffix transport simultaneously to every coordinate of a coefficient BRK. -/
def addKnownSuffixCoefficientBRK
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (suffixKey : BinarySecret (suffixDegree + 1))
    (view : CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels) :
    CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels :=
  fun coordinate ↦
    addKnownSuffixCoefficientBlock (embedBinarySecret suffixKey) (view coordinate)

/-- Inverse whole-BRK known-suffix transport. -/
def removeKnownSuffixCoefficientBRK
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (suffixKey : BinarySecret (suffixDegree + 1))
    (view : CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels) :
    CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels :=
  fun coordinate ↦
    removeKnownSuffixCoefficientBlock (embedBinarySecret suffixKey) (view coordinate)

@[simp]
theorem removeKnownSuffixCoefficientBRK_add
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (suffixKey : BinarySecret (suffixDegree + 1))
    (view : CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels) :
    removeKnownSuffixCoefficientBRK suffixKey
        (addKnownSuffixCoefficientBRK suffixKey view) = view := by
  funext coordinate
  exact removeKnownSuffixCoefficientBlock_add
    (embedBinarySecret suffixKey) (view coordinate)

@[simp]
theorem addKnownSuffixCoefficientBRK_remove
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (suffixKey : BinarySecret (suffixDegree + 1))
    (view : CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels) :
    addKnownSuffixCoefficientBRK suffixKey
        (removeKnownSuffixCoefficientBRK suffixKey view) = view := by
  funext coordinate
  exact addKnownSuffixCoefficientBlock_remove
    (embedBinarySecret suffixKey) (view coordinate)

theorem addKnownSuffixCoefficientBRK_bijective
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    Function.Bijective
      (addKnownSuffixCoefficientBRK suffixKey :
        CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels →
          CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeKnownSuffixCoefficientBRK suffixKey,
      removeKnownSuffixCoefficientBRK_add suffixKey,
      addKnownSuffixCoefficientBRK_remove suffixKey⟩

/-- For every fixed suffix key, the complete concrete BRK compiler is a permutation of the
coefficient row-pair carrier onto the literal native BRK carrier. -/
theorem buildNativeZeroBRK_bijective
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    Function.Bijective
      (buildNativeZeroBRK (q := q) (prefixDimension := prefixDimension)
        (suffixDegree := suffixDegree) (tgswLevels := tgswLevels) suffixKey) := by
  change Function.Bijective
    (coefficientZeroBRKToNative q prefixDimension suffixDegree tgswLevels ∘
      addKnownSuffixCoefficientBRK suffixKey)
  exact (coefficientZeroBRKToNative_bijective q prefixDimension suffixDegree
    tgswLevels).comp (addKnownSuffixCoefficientBRK_bijective suffixKey)

/-- A canonical uniform coefficient row-pair block is carried to the canonical uniform native
BRK law by the concrete compiler. -/
theorem buildNativeZeroBRK_uniform_evalDist
    (q prefixDimension suffixDegree tgswLevels : ℕ) [NeZero q]
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    evalDist (buildNativeZeroBRK suffixKey <$>
        ($ᵗ (CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels))) =
      evalDist ($ᵗ (SharedBootstrappingKey q prefixDimension
        (suffixDegree + 1) tgswLevels)) :=
  evalDist_map_bijective_uniform_cross
    (α := CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels)
    (β := SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels)
    (buildNativeZeroBRK suffixKey)
    (buildNativeZeroBRK_bijective q prefixDimension suffixDegree tgswLevels suffixKey)

/-- Reassociate separate complete challenge and body functions into coefficient BRK row pairs. -/
def coefficientBRKPairEquiv
    (q prefixDimension suffixDegree tgswLevels : ℕ) :
    (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels ×
      CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels) ≃
      CoefficientZeroBRK q prefixDimension suffixDegree tgswLevels :=
  (Equiv.arrowProdEquivProdArrow (Fin prefixDimension)
    (fun _ ↦ Fin (TGSW.rowCount 1 tgswLevels) →
      AmbientCoefficients q prefixDimension suffixDegree)
    (fun _ ↦ Fin (TGSW.rowCount 1 tgswLevels) →
      AmbientCoefficients q prefixDimension suffixDegree)).symm

@[simp]
theorem coefficientBRKPairEquiv_apply
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (challenge body : CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels) :
    coefficientBRKPairEquiv q prefixDimension suffixDegree tgswLevels (challenge, body) =
      fun coordinate ↦ (challenge coordinate, body coordinate) := by
  rfl

/-- Complete native BRK compiler with challenge and body supplied as two separate functions. -/
def buildNativeZeroBRKFromPair
    {q prefixDimension suffixDegree tgswLevels : ℕ}
    (suffixKey : BinarySecret (suffixDegree + 1))
    (pair : CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels ×
      CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels) :
    SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels :=
  buildNativeZeroBRK suffixKey
    (coefficientBRKPairEquiv q prefixDimension suffixDegree tgswLevels pair)

theorem buildNativeZeroBRKFromPair_bijective
    (q prefixDimension suffixDegree tgswLevels : ℕ)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    Function.Bijective
      (buildNativeZeroBRKFromPair (q := q) (prefixDimension := prefixDimension)
        (suffixDegree := suffixDegree) (tgswLevels := tgswLevels) suffixKey) :=
  (buildNativeZeroBRK_bijective q prefixDimension suffixDegree tgswLevels suffixKey).comp
    (coefficientBRKPairEquiv q prefixDimension suffixDegree tgswLevels).bijective

/-- Separately sampled uniform coefficient challenges and bodies compile to one exactly uniform
native BRK.  This is the concrete uniform-source branch-erasure fact used below. -/
theorem buildNativeZeroBRK_independent_uniform_evalDist
    (q prefixDimension suffixDegree tgswLevels : ℕ) [NeZero q]
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    evalDist (do
      let challenge ←
        $ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
      let body ←
        $ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
      return buildNativeZeroBRK suffixKey
        (fun coordinate ↦ (challenge coordinate, body coordinate))) =
      evalDist ($ᵗ (SharedBootstrappingKey q prefixDimension
        (suffixDegree + 1) tgswLevels)) := by
  let PairCarrier :=
    CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels ×
      CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels
  let pairSampler : ProbComp PairCarrier := do
    let challenge ←
      $ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
    let body ←
      $ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
    return (challenge, body)
  have hpairs : evalDist pairSampler = evalDist ($ᵗ PairCarrier) :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  calc
    _ = evalDist (buildNativeZeroBRKFromPair suffixKey <$> pairSampler) := by
      simp [pairSampler, buildNativeZeroBRKFromPair,
        map_eq_bind_pure_comp, monad_norm]
    _ = evalDist (buildNativeZeroBRKFromPair suffixKey <$> ($ᵗ PairCarrier)) :=
      evalDist_map_eq_of_evalDist_eq hpairs (buildNativeZeroBRKFromPair suffixKey)
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := PairCarrier)
      (β := SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels)
      (buildNativeZeroBRKFromPair suffixKey)
      (buildNativeZeroBRKFromPair_bijective q prefixDimension suffixDegree
        tgswLevels suffixKey)

/-- Fixed-key complete homogeneous BRK generated from coefficient-form prefix-RLWE rows.  The
underlying native CBD errors are exposed before coefficient conversion so their eventual return
to the native carrier is exact rather than a distributional approximation. -/
def extractedNativeZeroBRKSampler
    (q prefixDimension suffixDegree tgswLevels eta : ℕ) [NeZero q]
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    ProbComp (SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels) := do
  let challenge ←
    $ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
  let nativeError ← Fin.mOfFn prefixDimension fun _ ↦
    ProbComp.sampleIID (TGSW.rowCount 1 tgswLevels)
      (RLWE.CenteredBinomial.sampler q
        (prefixDimension + (suffixDegree + 1)) eta)
  let coefficientError := fun coordinate row ↦
    coefficientEquiv q (prefixDimension + (suffixDegree + 1))
      (nativeError coordinate row)
  return buildNativeZeroBRK suffixKey
    (fun coordinate ↦
      (challenge coordinate, fun row ↦
        negacyclicProduct
            (prefixCoefficients q prefixDimension suffixDegree prefixKey)
            (challenge coordinate row) + coefficientError coordinate row))

/-- The complete coefficient-form known-suffix BRK builder has exactly the native zero-message
BRK law for every fixed nested key and coefficientwise CBD error sampler. -/
theorem extractedNativeZeroBRKSampler_evalDist_eq_generateZeroBootstrappingKey
    (q prefixDimension suffixDegree tgswLevels eta : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    evalDist (extractedNativeZeroBRKSampler q prefixDimension suffixDegree
        tgswLevels eta prefixKey suffixKey) =
      evalDist (generateZeroBootstrappingKey q prefixDimension (suffixDegree + 1)
        tgswLevels
        (RLWE.CenteredBinomial.sampler q
          (prefixDimension + (suffixDegree + 1)) eta)
        tgswGadget (nestedRingSecret prefixKey suffixKey)) := by
  let degree := prefixDimension + (suffixDegree + 1)
  let coefficientChallenges : ProbComp
      (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels) :=
    $ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
  let nativeChallenges : ProbComp
      (NativeBRKChallenge q prefixDimension suffixDegree tgswLevels) :=
    coefficientBRKChallengeToNative q prefixDimension suffixDegree tgswLevels <$>
      coefficientChallenges
  let nativeErrors : ProbComp
      (Fin prefixDimension → Fin (TGSW.rowCount 1 tgswLevels) →
        RLWE.Rq q degree) :=
    Fin.mOfFn prefixDimension fun _ ↦
      ProbComp.sampleIID (TGSW.rowCount 1 tgswLevels)
        (RLWE.CenteredBinomial.sampler q degree eta)
  let fullSecret := embedRingSecret q (nestedRingSecret prefixKey suffixKey)
  let finish : NativeBRKChallenge q prefixDimension suffixDegree tgswLevels →
      (Fin prefixDimension → Fin (TGSW.rowCount 1 tgswLevels) →
        RLWE.Rq q degree) →
      ProbComp (SharedBootstrappingKey q prefixDimension (suffixDegree + 1)
        tgswLevels) := fun challenge error ↦
      pure (fun coordinate ↦ TLWE.batchAssemble fullSecret
        (challenge coordinate) 0 (error coordinate))
  have hnormalize :
      evalDist (extractedNativeZeroBRKSampler q prefixDimension suffixDegree
          tgswLevels eta prefixKey suffixKey) =
        evalDist (nativeChallenges >>= fun challenge ↦ nativeErrors >>= finish challenge) := by
    unfold extractedNativeZeroBRKSampler
    change evalDist (coefficientChallenges >>= fun challenge ↦
      nativeErrors >>= fun nativeError ↦
      pure (buildNativeZeroBRK suffixKey
        (fun coordinate ↦
          (challenge coordinate, fun row ↦
            negacyclicProduct
                (prefixCoefficients q prefixDimension suffixDegree prefixKey)
                (challenge coordinate row) +
              coefficientEquiv q degree (nativeError coordinate row))))) = _
    simp only [nativeChallenges, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
    refine evalDist_bind_congr' coefficientChallenges fun challenge ↦ ?_
    refine evalDist_bind_congr' nativeErrors fun nativeError ↦ ?_
    apply congrArg evalDist
    apply congrArg pure
    calc
      buildNativeZeroBRK suffixKey
          (fun coordinate ↦
            (challenge coordinate, fun row ↦
              negacyclicProduct
                  (prefixCoefficients q prefixDimension suffixDegree prefixKey)
                  (challenge coordinate row) +
                coefficientEquiv q degree (nativeError coordinate row))) =
        fun coordinate ↦
          TLWE.batchAssemble fullSecret
            (coefficientChallengeToNative (challenge coordinate)) 0
            (coefficientErrorToNative
              (fun row ↦ coefficientEquiv q degree (nativeError coordinate row))) :=
        buildNativeZeroBRK_real prefixKey suffixKey challenge
          (fun coordinate row ↦ coefficientEquiv q degree (nativeError coordinate row))
      _ = (fun coordinate ↦ TLWE.batchAssemble fullSecret
          ((coefficientBRKChallengeToNative q prefixDimension suffixDegree tgswLevels
            challenge) coordinate) 0 (nativeError coordinate)) := by
        funext coordinate
        congr 1
        funext row
        simp [coefficientErrorToNative, degree]
      _ = _ := rfl
  have hchallenge : evalDist nativeChallenges =
      evalDist ($ᵗ (NativeBRKChallenge q prefixDimension suffixDegree tgswLevels)) :=
    coefficientBRKChallengeToNative_uniform_evalDist
      q prefixDimension suffixDegree tgswLevels
  let nativeChallengeProduct : ProbComp
      (NativeBRKChallenge q prefixDimension suffixDegree tgswLevels) :=
    Fin.mOfFn prefixDimension fun _ ↦
      $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 tgswLevels))
        (RLWE.Rq q degree)
  have hchallengeProduct : evalDist nativeChallengeProduct =
      evalDist ($ᵗ (NativeBRKChallenge q prefixDimension suffixDegree tgswLevels)) := by
    exact FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform prefixDimension
  rw [hnormalize]
  calc
    evalDist (nativeChallenges >>= fun challenge ↦ nativeErrors >>= finish challenge) =
      evalDist (($ᵗ (NativeBRKChallenge q prefixDimension suffixDegree tgswLevels)) >>=
        fun challenge ↦ nativeErrors >>= finish challenge) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hchallenge (fun challenge ↦ nativeErrors >>= finish challenge)
    _ = evalDist (nativeChallengeProduct >>= fun challenge ↦
        nativeErrors >>= finish challenge) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hchallengeProduct.symm (fun challenge ↦ nativeErrors >>= finish challenge)
    _ = evalDist (Native.BootstrapCutSecurity.sampleParallelZeroBootstrap
        q degree 1 tgswLevels prefixDimension
        (RLWE.CenteredBinomial.sampler q degree eta)
        (nestedRingSecret prefixKey suffixKey)) := by
      simp [Native.BootstrapCutSecurity.sampleParallelZeroBootstrap,
        Native.BootstrapCutSecurity.sampleParallelHomogeneous,
        Native.BootstrapCutSecurity.transcriptToBootstrappingKey,
        Native.BootstrapCutSecurity.semiringRqPiAdd_eq_add,
        nativeChallengeProduct, nativeErrors, finish, fullSecret, degree, monad_norm]
      apply bind_congr
      intro challenge
      apply bind_congr
      intro error
      congr 1
    _ = evalDist (generateZeroBootstrappingKey q prefixDimension (suffixDegree + 1)
        tgswLevels (RLWE.CenteredBinomial.sampler q degree eta)
        tgswGadget (nestedRingSecret prefixKey suffixKey)) :=
      (Native.BootstrapCutSecurity.generateZeroBootstrappingKey_evalDist_eq_parallel
        q degree 1 tgswLevels prefixDimension
        (RLWE.CenteredBinomial.sampler q degree eta) tgswGadget
        (nestedRingSecret prefixKey suffixKey)).symm

/-! ## Complete fixed-key native CVZR endpoints -/

/-- The concrete prefix-RLWE side construction for one complete zero-BRK cloud key.  Its two
source blocks are sampled independently: the first supplies every homogeneous BRK row and the
second supplies every suffix-only KSK row. -/
def extractedNativeZeroCloudKeySampler
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) := do
  let bootstrappingKey ← extractedNativeZeroBRKSampler q prefixDimension suffixDegree
    tgswLevels brkEta prefixKey suffixKey
  let keySwitchKey ← extractedNativeKSKSampler q prefixDimension suffixDegree
    keySwitchLevels keySwitchEta keySwitchGadget prefixKey suffixKey
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- The complete concrete side construction has exactly the native zero-BRK-plus-genuine-KSK
law for every fixed split key.  This equality is joint: it includes every mask, both complete
error batches, their independence, and the common prefix/suffix key. -/
theorem extractedNativeZeroCloudKeySampler_evalDist_eq_generateBootstrapZeroCloudKey
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    evalDist (extractedNativeZeroCloudKeySampler q prefixDimension suffixDegree
        tgswLevels keySwitchLevels brkEta keySwitchEta keySwitchGadget
        prefixKey suffixKey) =
      evalDist (generateBootstrapZeroCloudKey q prefixDimension (suffixDegree + 1)
        tgswLevels keySwitchLevels
        (RLWE.CenteredBinomial.sampler q
          (prefixDimension + (suffixDegree + 1)) brkEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (nestedRingSecret prefixKey suffixKey)) := by
  unfold extractedNativeZeroCloudKeySampler generateBootstrapZeroCloudKey
  rw [evalDist_bind,
    extractedNativeZeroBRKSampler_evalDist_eq_generateZeroBootstrappingKey
      q prefixDimension suffixDegree tgswLevels brkEta tgswGadget prefixKey suffixKey,
    ← evalDist_bind]
  refine evalDist_bind_congr' _ fun bootstrappingKey ↦ ?_
  rw [evalDist_bind,
    extractedNativeKSKSampler_evalDist_eq_generateKeySwitchKey
      q prefixDimension suffixDegree keySwitchLevels keySwitchEta
      keySwitchGadget prefixKey suffixKey,
    ← evalDist_bind]

/-- Uniform-BRK comparison endpoint built from the same genuine extracted suffix-only KSK. -/
def extractedNativeUniformBRKCloudKeySampler
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels keySwitchEta : ℕ)
    [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) := do
  let bootstrappingKey ← $ᵗ (SharedBootstrappingKey q prefixDimension
    (suffixDegree + 1) tgswLevels)
  let keySwitchKey ← extractedNativeKSKSampler q prefixDimension suffixDegree
    keySwitchLevels keySwitchEta keySwitchGadget prefixKey suffixKey
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- Literal native uniform-BRK comparison endpoint, retaining an honestly generated KSK. -/
def nativeUniformBRKCloudKeySampler
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels keySwitchEta : ℕ)
    [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) := do
  let bootstrappingKey ← $ᵗ (SharedBootstrappingKey q prefixDimension
    (suffixDegree + 1) tgswLevels)
  let keySwitchKey ← generateKeySwitchKey q prefixDimension (suffixDegree + 1)
    keySwitchLevels (CenteredBinomial.scalarSampler q keySwitchEta)
    keySwitchGadget (nestedRingSecret prefixKey suffixKey)
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- Extracted and literal native uniform-BRK endpoints agree as complete cloud-key laws. -/
theorem extractedNativeUniformBRKCloudKeySampler_evalDist_eq_native
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels keySwitchEta : ℕ)
    [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    evalDist (extractedNativeUniformBRKCloudKeySampler q prefixDimension suffixDegree
        tgswLevels keySwitchLevels keySwitchEta keySwitchGadget prefixKey suffixKey) =
      evalDist (nativeUniformBRKCloudKeySampler q prefixDimension suffixDegree
        tgswLevels keySwitchLevels keySwitchEta keySwitchGadget prefixKey suffixKey) := by
  unfold extractedNativeUniformBRKCloudKeySampler nativeUniformBRKCloudKeySampler
  refine evalDist_bind_congr' _ fun bootstrappingKey ↦ ?_
  rw [evalDist_bind,
    extractedNativeKSKSampler_evalDist_eq_generateKeySwitchKey
      q prefixDimension suffixDegree keySwitchLevels keySwitchEta
      keySwitchGadget prefixKey suffixKey,
    ← evalDist_bind]

/-- Key-sampled CVZR endpoint produced by the coefficient-form source construction. -/
def extractedNativeCVZRView
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) (branch : Bool) :
    ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  let suffixKey ← Native.sampleLweSecret (suffixDegree + 1)
  if branch then
    extractedNativeZeroCloudKeySampler q prefixDimension suffixDegree
      tgswLevels keySwitchLevels brkEta keySwitchEta keySwitchGadget
      prefixKey suffixKey
  else
    extractedNativeUniformBRKCloudKeySampler q prefixDimension suffixDegree
      tgswLevels keySwitchLevels keySwitchEta keySwitchGadget prefixKey suffixKey

/-- Literal native CVZR target: a native zero-message BRK in branch one and an independent
uniform BRK in branch zero, with the genuine suffix-only KSK retained in both branches. -/
def nativeCVZRView
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) (branch : Bool) :
    ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  let suffixKey ← Native.sampleLweSecret (suffixDegree + 1)
  if branch then
    generateBootstrapZeroCloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels
      (RLWE.CenteredBinomial.sampler q
        (prefixDimension + (suffixDegree + 1)) brkEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget (nestedRingSecret prefixKey suffixKey)
  else
    nativeUniformBRKCloudKeySampler q prefixDimension suffixDegree
      tgswLevels keySwitchLevels keySwitchEta keySwitchGadget prefixKey suffixKey

/-- The source-built and literal native CVZR views agree for both branches. -/
theorem extractedNativeCVZRView_evalDist_eq_native
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) (branch : Bool) :
    evalDist (extractedNativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta keySwitchGadget branch) =
      evalDist (nativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta tgswGadget keySwitchGadget branch) := by
  unfold extractedNativeCVZRView nativeCVZRView
  refine evalDist_bind_congr' (Native.sampleLweSecret prefixDimension) fun prefixKey ↦ ?_
  refine evalDist_bind_congr' (Native.sampleLweSecret (suffixDegree + 1)) fun suffixKey ↦ ?_
  cases branch
  · exact extractedNativeUniformBRKCloudKeySampler_evalDist_eq_native
      q prefixDimension suffixDegree tgswLevels keySwitchLevels keySwitchEta
      keySwitchGadget prefixKey suffixKey
  · exact extractedNativeZeroCloudKeySampler_evalDist_eq_generateBootstrapZeroCloudKey
      q prefixDimension suffixDegree tgswLevels keySwitchLevels brkEta keySwitchEta
      tgswGadget keySwitchGadget prefixKey suffixKey

/-! ## One explicit disjoint prefix-RLWE source -/

/-- Coefficient-form public masks for all KSK source rows. -/
abbrev CoefficientKSKChallenge
    (q prefixDimension suffixDegree keySwitchLevels : ℕ) :=
  Fin ((suffixDegree + 1) * keySwitchLevels) →
    AmbientCoefficients q prefixDimension suffixDegree

/-- The complete public source mask is the disjoint BRK/KSK product. -/
abbrev NativeCVZRSourceChallenge
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels : ℕ) :=
  CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels ×
    CoefficientKSKChallenge q prefixDimension suffixDegree keySwitchLevels

/-- The complete source body/error carrier has the same disjoint product shape. -/
abbrev NativeCVZRSourceOutput
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels : ℕ) :=
  CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels ×
    CoefficientKSKChallenge q prefixDimension suffixDegree keySwitchLevels

/-- Independent canonical uniform samplers for the two public source-mask blocks. -/
def nativeCVZRSourceChallengeSampler
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels : ℕ) [NeZero q] :
    ProbComp (NativeCVZRSourceChallenge q prefixDimension suffixDegree
      tgswLevels keySwitchLevels) := do
  let brkChallenge ←
    $ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
  let kskChallenge ←
    $ᵗ (CoefficientKSKChallenge q prefixDimension suffixDegree keySwitchLevels)
  return (brkChallenge, kskChallenge)

/-- Independent canonical uniform body samplers for the two source blocks. -/
def nativeCVZRSourceUniformSampler
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels : ℕ) [NeZero q] :
    ProbComp (NativeCVZRSourceOutput q prefixDimension suffixDegree
      tgswLevels keySwitchLevels) := do
  let brkBody ←
    $ᵗ (CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels)
  let kskBody ←
    $ᵗ (CoefficientKSKChallenge q prefixDimension suffixDegree keySwitchLevels)
  return (brkBody, kskBody)

/-- Complete implementation-aligned error sampler.  Native ring CBD is retained for every BRK
row; independent coefficient-form ring CBD rows supply the KSK, whose selected coefficients were
proved above to have exactly the scalar CBD law. -/
def nativeCVZRJointErrorSampler
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q] :
    ProbComp (NativeCVZRSourceOutput q prefixDimension suffixDegree
      tgswLevels keySwitchLevels) := do
  let nativeBRKError ← Fin.mOfFn prefixDimension fun _ ↦
    ProbComp.sampleIID (TGSW.rowCount 1 tgswLevels)
      (RLWE.CenteredBinomial.sampler q
        (prefixDimension + (suffixDegree + 1)) brkEta)
  let coefficientBRKError := fun coordinate row ↦
    coefficientEquiv q (prefixDimension + (suffixDegree + 1))
      (nativeBRKError coordinate row)
  let coefficientKSKError ←
    ProbComp.sampleIID ((suffixDegree + 1) * keySwitchLevels)
      (coefficientCBDRingSampler q (prefixDimension + (suffixDegree + 1))
        keySwitchEta)
  return (coefficientBRKError, coefficientKSKError)

/-- Prefix-supported negacyclic signal for every disjoint BRK and KSK row. -/
def nativeCVZRNoiseless
    {q prefixDimension suffixDegree tgswLevels keySwitchLevels : ℕ}
    (prefixKey : BinarySecret prefixDimension)
    (challenge : NativeCVZRSourceChallenge q prefixDimension suffixDegree
      tgswLevels keySwitchLevels) :
    NativeCVZRSourceOutput q prefixDimension suffixDegree
      tgswLevels keySwitchLevels :=
  (fun coordinate row ↦
      negacyclicProduct
        (prefixCoefficients q prefixDimension suffixDegree prefixKey)
        (challenge.1 coordinate row),
    fun row ↦
      negacyclicProduct
        (prefixCoefficients q prefixDimension suffixDegree prefixKey)
        (challenge.2 row))

/-- The fully concrete non-auxiliary source problem.  Its only hidden key is the binary prefix;
the BRK and KSK rows occupy separate sampler blocks and use the exact implementation-facing CBD
laws above. -/
def nativeCVZRPrefixRLWEProblem
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q] :
    LearningWithErrors.Problem
      (NativeCVZRSourceChallenge q prefixDimension suffixDegree
        tgswLevels keySwitchLevels)
      (BinarySecret prefixDimension)
      (NativeCVZRSourceOutput q prefixDimension suffixDegree
        tgswLevels keySwitchLevels) where
  sampleChallenge := nativeCVZRSourceChallengeSampler q prefixDimension suffixDegree
    tgswLevels keySwitchLevels
  sampleSecret := Native.sampleLweSecret prefixDimension
  sampleError := nativeCVZRJointErrorSampler q prefixDimension suffixDegree
    tgswLevels keySwitchLevels brkEta keySwitchEta
  noiseless := nativeCVZRNoiseless
  sampleUniform := nativeCVZRSourceUniformSampler q prefixDimension suffixDegree
    tgswLevels keySwitchLevels

/-- Public branch compiler.  Branch one transports the BRK rows by the sampled known suffix;
branch zero replaces only the BRK by fresh uniform native storage.  Both branches construct the
same KSK from the disjoint KSK source block. -/
def nativeCVZRBuild
    {q prefixDimension suffixDegree tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    Bool → BinarySecret (suffixDegree + 1) →
      (NativeCVZRSourceChallenge q prefixDimension suffixDegree
          tgswLevels keySwitchLevels ×
        NativeCVZRSourceOutput q prefixDimension suffixDegree
          tgswLevels keySwitchLevels) →
      ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
        tgswLevels keySwitchLevels) :=
  fun branch suffixKey source ↦
    let keySwitchKey := buildNativeKSK keySwitchGadget suffixKey
      (fun row ↦ (source.1.2 row, source.2.2 row))
    if branch then
      pure ⟨buildNativeZeroBRK suffixKey
        (fun coordinate ↦ (source.1.1 coordinate, source.2.1 coordinate)),
        keySwitchKey⟩
    else do
      let bootstrappingKey ← $ᵗ (SharedBootstrappingKey q prefixDimension
        (suffixDegree + 1) tgswLevels)
      return ⟨bootstrappingKey, keySwitchKey⟩

/-- Source-aligned target pair used to package the exact compiler before identifying it with the
literal native endpoint. -/
def sourceAlignedNativeCVZRView
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) (branch : Bool) :
    ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) :=
  DirectSubsetKeyBRK.constructedView
    (Native.sampleLweSecret (suffixDegree + 1))
    (LearningWithErrors.distr
      (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta))
    (nativeCVZRBuild keySwitchGadget) branch

/-- On the uniform source, the translated complete BRK and the freshly sampled complete BRK have
the same law while the KSK source block is forwarded identically. -/
theorem nativeCVZRBuild_uniform_evalDist_eq
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist (DirectSubsetKeyBRK.constructedView
      (Native.sampleLweSecret (suffixDegree + 1))
      (LearningWithErrors.uniformDistr
        (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
          keySwitchLevels brkEta keySwitchEta))
      (nativeCVZRBuild keySwitchGadget) true) =
    evalDist (DirectSubsetKeyBRK.constructedView
      (Native.sampleLweSecret (suffixDegree + 1))
      (LearningWithErrors.uniformDistr
      (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
          keySwitchLevels brkEta keySwitchEta))
      (nativeCVZRBuild keySwitchGadget) false) := by
  let source := LearningWithErrors.uniformDistr
    (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
      keySwitchLevels brkEta keySwitchEta)
  let suffixSampler := Native.sampleLweSecret (suffixDegree + 1)
  have hswap (branch : Bool) :
      evalDist (DirectSubsetKeyBRK.constructedView suffixSampler source
          (nativeCVZRBuild keySwitchGadget) branch) =
        evalDist (suffixSampler >>= fun suffixKey ↦
          source >>= nativeCVZRBuild keySwitchGadget branch suffixKey) := by
    unfold DirectSubsetKeyBRK.constructedView
    exact OracleComp.DeferredSampling.evalDist_bind_comm source suffixSampler _
  rw [hswap true, hswap false]
  refine evalDist_bind_congr' suffixSampler fun suffixKey ↦ ?_
  let BRKCarrier := CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels
  let KSKCarrier := CoefficientKSKChallenge q prefixDimension suffixDegree keySwitchLevels
  let brkChallenge : ProbComp BRKCarrier := $ᵗ BRKCarrier
  let kskChallenge : ProbComp KSKCarrier := $ᵗ KSKCarrier
  let brkBody : ProbComp BRKCarrier := $ᵗ BRKCarrier
  let kskBody : ProbComp KSKCarrier := $ᵗ KSKCarrier
  let uniformBRK : ProbComp
      (SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels) :=
    $ᵗ (SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels)
  let finish := fun
      (bootstrappingKey : SharedBootstrappingKey q prefixDimension
        (suffixDegree + 1) tgswLevels)
      (kskMask kskOutput : KSKCarrier) ↦
    (pure ⟨bootstrappingKey,
      buildNativeKSK keySwitchGadget suffixKey
        (fun row ↦ (kskMask row, kskOutput row))⟩ :
      ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
        tgswLevels keySwitchLevels))
  let canonical : ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) :=
    kskChallenge >>= fun kskMask ↦
      kskBody >>= fun kskOutput ↦
        uniformBRK >>= fun bootstrappingKey ↦
          finish bootstrappingKey kskMask kskOutput
  have hcompiled :
      evalDist (do
        let challenge ← brkChallenge
        let body ← brkBody
        return buildNativeZeroBRK suffixKey
          (fun coordinate ↦ (challenge coordinate, body coordinate))) =
        evalDist uniformBRK := by
    exact buildNativeZeroBRK_independent_uniform_evalDist
      q prefixDimension suffixDegree tgswLevels suffixKey
  have hleft :
      evalDist (brkChallenge >>= fun brkMask ↦
        kskChallenge >>= fun kskMask ↦
          brkBody >>= fun brkOutput ↦
            kskBody >>= fun kskOutput ↦
              finish
                (buildNativeZeroBRK suffixKey
                  (fun coordinate ↦ (brkMask coordinate, brkOutput coordinate)))
                kskMask kskOutput) =
        evalDist canonical := by
    calc
      _ = evalDist (brkChallenge >>= fun brkMask ↦
          brkBody >>= fun brkOutput ↦
            kskChallenge >>= fun kskMask ↦
              kskBody >>= fun kskOutput ↦
                finish
                  (buildNativeZeroBRK suffixKey
                    (fun coordinate ↦ (brkMask coordinate, brkOutput coordinate)))
                  kskMask kskOutput) := by
        refine evalDist_bind_congr' brkChallenge fun brkMask ↦ ?_
        exact evalDist_bind_bind_swap kskChallenge brkBody
          (fun kskMask brkOutput ↦
            kskBody >>= fun kskOutput ↦
              finish
                (buildNativeZeroBRK suffixKey
                  (fun coordinate ↦ (brkMask coordinate, brkOutput coordinate)))
                kskMask kskOutput)
      _ = evalDist ((do
          let brkMask ← brkChallenge
          let brkOutput ← brkBody
          return buildNativeZeroBRK suffixKey
            (fun coordinate ↦ (brkMask coordinate, brkOutput coordinate))) >>=
            fun bootstrappingKey ↦
              kskChallenge >>= fun kskMask ↦
                kskBody >>= fun kskOutput ↦
                  finish bootstrappingKey kskMask kskOutput) := by
        simp only [bind_assoc, pure_bind]
      _ = evalDist (uniformBRK >>= fun bootstrappingKey ↦
          kskChallenge >>= fun kskMask ↦
            kskBody >>= fun kskOutput ↦
              finish bootstrappingKey kskMask kskOutput) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          hcompiled (fun bootstrappingKey ↦
            kskChallenge >>= fun kskMask ↦
              kskBody >>= fun kskOutput ↦
                finish bootstrappingKey kskMask kskOutput)
      _ = evalDist (kskChallenge >>= fun kskMask ↦
          uniformBRK >>= fun bootstrappingKey ↦
            kskBody >>= fun kskOutput ↦
              finish bootstrappingKey kskMask kskOutput) :=
        evalDist_bind_bind_swap uniformBRK kskChallenge _
      _ = evalDist canonical := by
        refine evalDist_bind_congr' kskChallenge fun kskMask ↦ ?_
        exact evalDist_bind_bind_swap uniformBRK kskBody _
  have hright :
      evalDist (brkChallenge >>= fun _brkMask ↦
        kskChallenge >>= fun kskMask ↦
          brkBody >>= fun _brkOutput ↦
            kskBody >>= fun kskOutput ↦
              uniformBRK >>= fun bootstrappingKey ↦
                finish bootstrappingKey kskMask kskOutput) =
        evalDist canonical := by
    calc
      _ = evalDist (brkChallenge >>= fun _brkMask ↦
          brkBody >>= fun _brkOutput ↦
            kskChallenge >>= fun kskMask ↦
              kskBody >>= fun kskOutput ↦
                uniformBRK >>= fun bootstrappingKey ↦
                  finish bootstrappingKey kskMask kskOutput) := by
        refine evalDist_bind_congr' brkChallenge fun _brkMask ↦ ?_
        exact evalDist_bind_bind_swap kskChallenge brkBody _
      _ = evalDist (brkBody >>= fun _brkOutput ↦ canonical) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          brkChallenge (by simp [brkChallenge]) _
      _ = evalDist canonical :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          brkBody (by simp [brkBody]) _
  simp only [source, LearningWithErrors.uniformDistr,
    nativeCVZRPrefixRLWEProblem, nativeCVZRSourceChallengeSampler,
    nativeCVZRSourceUniformSampler, nativeCVZRBuild,
    Bool.false_eq_true, if_false, if_true, bind_assoc, pure_bind]
  exact hleft.trans hright.symm

/-- Exact public CVZR compiler for the concrete disjoint prefix-RLWE source.  At this layer the
target is written in source sampling order; the next theorem identifies it with the ordinary
native key-generation order. -/
def sourceAlignedNativeCVZRCompiler
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ExactCVZRCompiler
      (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta)
      (Native.sampleLweSecret (suffixDegree + 1))
      (sourceAlignedNativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta keySwitchGadget) where
  build := nativeCVZRBuild keySwitchGadget
  realLaw := fun _branch ↦ rfl
  uniformLaw := nativeCVZRBuild_uniform_evalDist_eq q prefixDimension suffixDegree
    tgswLevels keySwitchLevels brkEta keySwitchEta keySwitchGadget

/-- The concrete source reduction has exactly the generic factor-two loss and no multiplier for
the number of BRK or KSK rows. -/
theorem sourceAlignedNativeCVZRAdvantage_le_two_prefixRLWE
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : DirectSubsetKeyBRK.Distinguisher
      (CloudKey q prefixDimension (suffixDegree + 1)
        tgswLevels keySwitchLevels)) :
    DirectSubsetKeyBRK.targetAdvantage
        (sourceAlignedNativeCVZRView q prefixDimension suffixDegree tgswLevels
          keySwitchLevels brkEta keySwitchEta keySwitchGadget)
        distinguisher ≤
      2 * LearningWithErrors.advantage
        (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
          keySwitchLevels brkEta keySwitchEta)
        ((sourceAlignedNativeCVZRCompiler q prefixDimension suffixDegree tgswLevels
          keySwitchLevels brkEta keySwitchEta keySwitchGadget).reduction
            distinguisher) :=
  (sourceAlignedNativeCVZRCompiler q prefixDimension suffixDegree tgswLevels
    keySwitchLevels brkEta keySwitchEta keySwitchGadget).targetAdvantage_le_two_source
      distinguisher

/-! ## Identification with native key-generation order -/

/-- Real prefix-RLWE sampling with both split keys fixed.  This exposes the sole remaining
difference from native key generation as an ordering of independent random draws. -/
def fixedKeySourceNativeCVZRView
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (branch : Bool) (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) := do
  let challenge ← nativeCVZRSourceChallengeSampler q prefixDimension suffixDegree
    tgswLevels keySwitchLevels
  let error ← nativeCVZRJointErrorSampler q prefixDimension suffixDegree
    tgswLevels keySwitchLevels brkEta keySwitchEta
  nativeCVZRBuild keySwitchGadget branch suffixKey
    (challenge, nativeCVZRNoiseless prefixKey challenge + error)

/-- For fixed split keys, the source-row program is exactly the extracted native endpoint in
both branches. -/
theorem fixedKeySourceNativeCVZRView_evalDist_eq_extracted
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (branch : Bool) (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret (suffixDegree + 1)) :
    evalDist (fixedKeySourceNativeCVZRView q prefixDimension suffixDegree
        tgswLevels keySwitchLevels brkEta keySwitchEta keySwitchGadget
        branch prefixKey suffixKey) =
      evalDist (if branch then
        extractedNativeZeroCloudKeySampler q prefixDimension suffixDegree
          tgswLevels keySwitchLevels brkEta keySwitchEta keySwitchGadget
          prefixKey suffixKey
      else
        extractedNativeUniformBRKCloudKeySampler q prefixDimension suffixDegree
          tgswLevels keySwitchLevels keySwitchEta keySwitchGadget
          prefixKey suffixKey) := by
  cases branch <;>
    simp only [fixedKeySourceNativeCVZRView, nativeCVZRSourceChallengeSampler,
      nativeCVZRJointErrorSampler, nativeCVZRBuild, nativeCVZRNoiseless,
      Bool.false_eq_true, if_false, if_true, bind_assoc, pure_bind,
      Prod.fst_add, Prod.snd_add, Pi.add_apply]
  · unfold extractedNativeUniformBRKCloudKeySampler extractedNativeKSKSampler
    simp only [bind_assoc, pure_bind]
    let BRKCarrier :=
      CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels
    let KSKCarrier :=
      CoefficientKSKChallenge q prefixDimension suffixDegree keySwitchLevels
    let brkChallenge : ProbComp BRKCarrier := $ᵗ BRKCarrier
    let kskChallenge : ProbComp KSKCarrier := $ᵗ KSKCarrier
    let nativeBRKError : ProbComp
        (Fin prefixDimension → Fin (TGSW.rowCount 1 tgswLevels) →
          RLWE.Rq q (prefixDimension + (suffixDegree + 1))) :=
      Fin.mOfFn prefixDimension fun _ ↦
        ProbComp.sampleIID (TGSW.rowCount 1 tgswLevels)
          (RLWE.CenteredBinomial.sampler q
            (prefixDimension + (suffixDegree + 1)) brkEta)
    let kskError : ProbComp KSKCarrier :=
      ProbComp.sampleIID ((suffixDegree + 1) * keySwitchLevels)
        (coefficientCBDRingSampler q (prefixDimension + (suffixDegree + 1))
          keySwitchEta)
    let uniformBRK : ProbComp
        (SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels) :=
      $ᵗ (SharedBootstrappingKey q prefixDimension (suffixDegree + 1) tgswLevels)
    let finish := fun
        (bootstrappingKey : SharedBootstrappingKey q prefixDimension
          (suffixDegree + 1) tgswLevels)
        (kskMask kskNoise : KSKCarrier) ↦
      (pure ⟨bootstrappingKey,
        buildNativeKSK keySwitchGadget suffixKey
          (fun row ↦ (kskMask row,
            negacyclicProduct
                (prefixCoefficients q prefixDimension suffixDegree prefixKey)
                (kskMask row) + kskNoise row))⟩ :
        ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
          tgswLevels keySwitchLevels))
    change evalDist (brkChallenge >>= fun _ ↦
        kskChallenge >>= fun kskMask ↦
          nativeBRKError >>= fun _ ↦
            kskError >>= fun kskNoise ↦
              uniformBRK >>= fun bootstrappingKey ↦
                finish bootstrappingKey kskMask kskNoise) =
      evalDist (uniformBRK >>= fun bootstrappingKey ↦
        kskChallenge >>= fun kskMask ↦
          kskError >>= fun kskNoise ↦
            finish bootstrappingKey kskMask kskNoise)
    calc
      _ = evalDist (kskChallenge >>= fun kskMask ↦
          nativeBRKError >>= fun _ ↦
            kskError >>= fun kskNoise ↦
              uniformBRK >>= fun bootstrappingKey ↦
                finish bootstrappingKey kskMask kskNoise) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          brkChallenge (by simp [brkChallenge]) _
      _ = evalDist (kskChallenge >>= fun kskMask ↦
          kskError >>= fun kskNoise ↦
            uniformBRK >>= fun bootstrappingKey ↦
              finish bootstrappingKey kskMask kskNoise) := by
        refine evalDist_bind_congr' kskChallenge fun kskMask ↦ ?_
        exact
          FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
            nativeBRKError (by simp [nativeBRKError]) _
      _ = evalDist (kskChallenge >>= fun kskMask ↦
          uniformBRK >>= fun bootstrappingKey ↦
            kskError >>= fun kskNoise ↦
              finish bootstrappingKey kskMask kskNoise) := by
        refine evalDist_bind_congr' kskChallenge fun kskMask ↦ ?_
        exact evalDist_bind_bind_swap kskError uniformBRK _
      _ = _ := evalDist_bind_bind_swap kskChallenge uniformBRK _
  · unfold extractedNativeZeroCloudKeySampler extractedNativeZeroBRKSampler
      extractedNativeKSKSampler
    simp only [bind_assoc, pure_bind]
    let BRKCarrier :=
      CoefficientBRKChallenge q prefixDimension suffixDegree tgswLevels
    let KSKCarrier :=
      CoefficientKSKChallenge q prefixDimension suffixDegree keySwitchLevels
    let brkChallenge : ProbComp BRKCarrier := $ᵗ BRKCarrier
    let kskChallenge : ProbComp KSKCarrier := $ᵗ KSKCarrier
    let nativeBRKError : ProbComp
        (Fin prefixDimension → Fin (TGSW.rowCount 1 tgswLevels) →
          RLWE.Rq q (prefixDimension + (suffixDegree + 1))) :=
      Fin.mOfFn prefixDimension fun _ ↦
        ProbComp.sampleIID (TGSW.rowCount 1 tgswLevels)
          (RLWE.CenteredBinomial.sampler q
            (prefixDimension + (suffixDegree + 1)) brkEta)
    let kskError : ProbComp KSKCarrier :=
      ProbComp.sampleIID ((suffixDegree + 1) * keySwitchLevels)
        (coefficientCBDRingSampler q (prefixDimension + (suffixDegree + 1))
          keySwitchEta)
    let finish := fun (brkMask : BRKCarrier)
        (brkNoise : Fin prefixDimension → Fin (TGSW.rowCount 1 tgswLevels) →
          RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
        (kskMask kskNoise : KSKCarrier) ↦
      (pure ⟨
        buildNativeZeroBRK suffixKey
          (fun coordinate ↦ (brkMask coordinate, fun row ↦
            negacyclicProduct
                (prefixCoefficients q prefixDimension suffixDegree prefixKey)
                (brkMask coordinate row) +
              coefficientEquiv q (prefixDimension + (suffixDegree + 1))
                (brkNoise coordinate row))),
        buildNativeKSK keySwitchGadget suffixKey
          (fun row ↦ (kskMask row,
            negacyclicProduct
                (prefixCoefficients q prefixDimension suffixDegree prefixKey)
                (kskMask row) + kskNoise row))⟩ :
        ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
          tgswLevels keySwitchLevels))
    change evalDist (brkChallenge >>= fun brkMask ↦
        kskChallenge >>= fun kskMask ↦
          nativeBRKError >>= fun brkNoise ↦
            kskError >>= fun kskNoise ↦
              finish brkMask brkNoise kskMask kskNoise) =
      evalDist (brkChallenge >>= fun brkMask ↦
        nativeBRKError >>= fun brkNoise ↦
          kskChallenge >>= fun kskMask ↦
            kskError >>= fun kskNoise ↦
              finish brkMask brkNoise kskMask kskNoise)
    refine evalDist_bind_congr' brkChallenge fun brkMask ↦ ?_
    exact evalDist_bind_bind_swap kskChallenge nativeBRKError _

/-- Key-first presentation of the same source experiment. -/
def keyFirstSourceNativeCVZRView
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) (branch : Bool) :
    ProbComp (CloudKey q prefixDimension (suffixDegree + 1)
      tgswLevels keySwitchLevels) := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  let suffixKey ← Native.sampleLweSecret (suffixDegree + 1)
  fixedKeySourceNativeCVZRView q prefixDimension suffixDegree tgswLevels
    keySwitchLevels brkEta keySwitchEta keySwitchGadget branch prefixKey suffixKey

/-- Deferred sampling moves the independent prefix and suffix keys before the public masks and
errors.  No distributional approximation or cryptographic premise is used. -/
theorem sourceAlignedNativeCVZRView_evalDist_eq_keyFirst
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) (branch : Bool) :
    evalDist (sourceAlignedNativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta keySwitchGadget branch) =
      evalDist (keyFirstSourceNativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta keySwitchGadget branch) := by
  unfold sourceAlignedNativeCVZRView DirectSubsetKeyBRK.constructedView
    LearningWithErrors.distr nativeCVZRPrefixRLWEProblem
    keyFirstSourceNativeCVZRView fixedKeySourceNativeCVZRView
  simp only [bind_assoc, pure_bind]
  let challenges := nativeCVZRSourceChallengeSampler q prefixDimension suffixDegree
    tgswLevels keySwitchLevels
  let prefixes := Native.sampleLweSecret prefixDimension
  let errors := nativeCVZRJointErrorSampler q prefixDimension suffixDegree
    tgswLevels keySwitchLevels brkEta keySwitchEta
  let suffixes := Native.sampleLweSecret (suffixDegree + 1)
  let finish := fun
      (challenge : NativeCVZRSourceChallenge q prefixDimension suffixDegree
        tgswLevels keySwitchLevels)
      (prefixKey : BinarySecret prefixDimension)
      (error : NativeCVZRSourceOutput q prefixDimension suffixDegree
        tgswLevels keySwitchLevels)
      (suffixKey : BinarySecret (suffixDegree + 1)) ↦
    nativeCVZRBuild keySwitchGadget branch suffixKey
      (challenge, nativeCVZRNoiseless prefixKey challenge + error)
  change evalDist (challenges >>= fun challenge ↦
      prefixes >>= fun prefixKey ↦
        errors >>= fun error ↦
          suffixes >>= fun suffixKey ↦
            finish challenge prefixKey error suffixKey) =
    evalDist (prefixes >>= fun prefixKey ↦
      suffixes >>= fun suffixKey ↦
        challenges >>= fun challenge ↦
          errors >>= fun error ↦
            finish challenge prefixKey error suffixKey)
  calc
    _ = evalDist (prefixes >>= fun prefixKey ↦
        challenges >>= fun challenge ↦
          errors >>= fun error ↦
            suffixes >>= fun suffixKey ↦
              finish challenge prefixKey error suffixKey) :=
      evalDist_bind_bind_swap challenges prefixes _
    _ = evalDist (prefixes >>= fun prefixKey ↦
        challenges >>= fun challenge ↦
          suffixes >>= fun suffixKey ↦
            errors >>= fun error ↦
              finish challenge prefixKey error suffixKey) := by
      refine evalDist_bind_congr' prefixes fun prefixKey ↦ ?_
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      exact evalDist_bind_bind_swap errors suffixes _
    _ = _ := by
      refine evalDist_bind_congr' prefixes fun prefixKey ↦ ?_
      exact evalDist_bind_bind_swap challenges suffixes _

/-- The source-aligned target pair is exactly the extracted native CVZR pair. -/
theorem sourceAlignedNativeCVZRView_evalDist_eq_extracted
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) (branch : Bool) :
    evalDist (sourceAlignedNativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta keySwitchGadget branch) =
      evalDist (extractedNativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta keySwitchGadget branch) := by
  rw [sourceAlignedNativeCVZRView_evalDist_eq_keyFirst]
  unfold keyFirstSourceNativeCVZRView extractedNativeCVZRView
  refine evalDist_bind_congr' (Native.sampleLweSecret prefixDimension) fun prefixKey ↦ ?_
  refine evalDist_bind_congr' (Native.sampleLweSecret (suffixDegree + 1)) fun suffixKey ↦ ?_
  exact fixedKeySourceNativeCVZRView_evalDist_eq_extracted
    q prefixDimension suffixDegree tgswLevels keySwitchLevels brkEta keySwitchEta
    keySwitchGadget branch prefixKey suffixKey

/-- Final endpoint identification: the concrete prefix-RLWE compiler's target is the literal
native CVZR view with native ring CBD BRK errors and scalar CBD KSK errors. -/
theorem sourceAlignedNativeCVZRView_evalDist_eq_native
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) (branch : Bool) :
    evalDist (sourceAlignedNativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta keySwitchGadget branch) =
      evalDist (nativeCVZRView q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta tgswGadget keySwitchGadget branch) :=
  (sourceAlignedNativeCVZRView_evalDist_eq_extracted q prefixDimension suffixDegree
    tgswLevels keySwitchLevels brkEta keySwitchEta keySwitchGadget branch).trans
  (extractedNativeCVZRView_evalDist_eq_native q prefixDimension suffixDegree
    tgswLevels keySwitchLevels brkEta keySwitchEta tgswGadget keySwitchGadget branch)

/-! ## Literal native compiler and security theorem -/

/-- Exact CVZR compiler whose target is the literal native cloud-key endpoint rather than an
intermediate source-order presentation. -/
def nativeCVZRCompiler
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ExactCVZRCompiler
      (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
        keySwitchLevels brkEta keySwitchEta)
      (Native.sampleLweSecret (suffixDegree + 1))
      (nativeCVZRView q prefixDimension suffixDegree tgswLevels keySwitchLevels
        brkEta keySwitchEta tgswGadget keySwitchGadget) where
  build := nativeCVZRBuild keySwitchGadget
  realLaw := fun branch ↦
    sourceAlignedNativeCVZRView_evalDist_eq_native q prefixDimension suffixDegree
      tgswLevels keySwitchLevels brkEta keySwitchEta tgswGadget keySwitchGadget branch
  uniformLaw := nativeCVZRBuild_uniform_evalDist_eq q prefixDimension suffixDegree
    tgswLevels keySwitchLevels brkEta keySwitchEta keySwitchGadget

/-- Concrete native CVZR security from one non-auxiliary prefix-subspace RLWE game.  The complete
BRK and KSK batches are handled in one source instance, hence the only reduction loss is two. -/
theorem nativeCVZRAdvantage_le_two_prefixRLWE
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : DirectSubsetKeyBRK.Distinguisher
      (CloudKey q prefixDimension (suffixDegree + 1)
        tgswLevels keySwitchLevels)) :
    DirectSubsetKeyBRK.targetAdvantage
        (nativeCVZRView q prefixDimension suffixDegree tgswLevels keySwitchLevels
          brkEta keySwitchEta tgswGadget keySwitchGadget)
        distinguisher ≤
      2 * LearningWithErrors.advantage
        (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
          keySwitchLevels brkEta keySwitchEta)
        ((nativeCVZRCompiler q prefixDimension suffixDegree tgswLevels keySwitchLevels
          brkEta keySwitchEta tgswGadget keySwitchGadget).reduction distinguisher) :=
  (nativeCVZRCompiler q prefixDimension suffixDegree tgswLevels keySwitchLevels
    brkEta keySwitchEta tgswGadget keySwitchGadget).targetAdvantage_le_two_source
      distinguisher

/-- The selected source distinguisher's advantage is exactly one half of the native CVZR
advantage; the displayed factor two is not accumulated rowwise. -/
theorem nativeCVZR_reduction_advantage_eq_half
    (q prefixDimension suffixDegree tgswLevels keySwitchLevels
      brkEta keySwitchEta : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq q (prefixDimension + (suffixDegree + 1)))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : DirectSubsetKeyBRK.Distinguisher
      (CloudKey q prefixDimension (suffixDegree + 1)
        tgswLevels keySwitchLevels)) :
    LearningWithErrors.advantage
        (nativeCVZRPrefixRLWEProblem q prefixDimension suffixDegree tgswLevels
          keySwitchLevels brkEta keySwitchEta)
        ((nativeCVZRCompiler q prefixDimension suffixDegree tgswLevels keySwitchLevels
          brkEta keySwitchEta tgswGadget keySwitchGadget).reduction distinguisher) =
      DirectSubsetKeyBRK.targetAdvantage
        (nativeCVZRView q prefixDimension suffixDegree tgswLevels keySwitchLevels
          brkEta keySwitchEta tgswGadget keySwitchGadget)
        distinguisher / 2 :=
  (nativeCVZRCompiler q prefixDimension suffixDegree tgswLevels keySwitchLevels
    brkEta keySwitchEta tgswGadget keySwitchGadget).reduction_advantage_eq_half_targetAdvantage
      distinguisher

end

end FormalProof4FHE.TFHE.NativeTRGSWCVZRConcreteInstantiation
