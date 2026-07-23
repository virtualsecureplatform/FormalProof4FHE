/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.InternalProduct

/-!
# Extending a TFHE Bootstrapping Key Along Nested Ring Keys

This module formalizes the source-to-target key relation used by shared-randomness secret keys.
The source ring key is a prefix of the target ring key,

`targetSecret = sourceSecret || suffixSecret`,

and the plaintext messages of the bootstrapping key are kept fixed.  An individual TLWE/GLWE
row under the source key can be moved to the target key for free by appending zero mask
coordinates.  A complete native TGSW ciphertext needs more: its target layout has one additional
gadget block for every new suffix coordinate.  Those missing rows must encrypt
`-(suffixSecret j * (message * gadget level))`.

The main construction below fills a missing row by externally multiplying a source-key TGSW
encryption of `message` with the corresponding suffix-only KSK row, negating the result, and then
appending zero mask coordinates.  Its phase is exactly the target TGSW gadget phase plus the
displayed KSK and external-product errors.  Thus it gives the precise formal version of

`BRK(messages, sourceRingKey) -> BRK(messages, targetRingKey)`.

The resulting target BRK is a *derived* evaluation key.  This module does not identify its
distribution with a freshly sampled native target-key TGSW ciphertext; that would require an
additional rerandomization statement.

The KSK used by this converter is ring-valued: it contains TLWE-over-`Rq` rows under the source
ring key.  It is not definitionally the standard TFHE scalar KSK over `ZMod q` under
`keyExtract(sourceRingKey)`.  Starting with only that scalar KSK would additionally require a
checked LWE-to-GLWE packing conversion.  Accordingly this file formalizes a precise modified
evaluation-key construction, not a free reinterpretation of the native scalar KSK.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.SharedRandomnessKeyExtension

namespace TLWE

/-- Publicly extend a source-key row to a nested target key by appending zero mask coordinates. -/
def extendCiphertext {R : Type} [Zero R] {sourceDimension suffixDimension : ℕ}
    (ciphertext : TFHE.TLWE.Ciphertext R sourceDimension) :
    TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension) :=
  ⟨Fin.append ciphertext.mask 0, ciphertext.body⟩

/-- Extending a row preserves its phase exactly when the source key is the target-key prefix. -/
@[simp]
theorem phase_extendCiphertext {R : Type} [Ring R]
    {sourceDimension suffixDimension : ℕ}
    (sourceSecret : Fin sourceDimension → R)
    (suffixSecret : Fin suffixDimension → R)
    (ciphertext : TFHE.TLWE.Ciphertext R sourceDimension) :
    TFHE.TLWE.phase (Fin.append sourceSecret suffixSecret)
        (extendCiphertext (suffixDimension := suffixDimension) ciphertext) =
      TFHE.TLWE.phase sourceSecret ciphertext := by
  simp [TFHE.TLWE.phase, extendCiphertext, dotProduct, Fin.sum_univ_add]

/-- Negate one TLWE row componentwise. -/
def negateCiphertext {R : Type} [Neg R] {dimension : ℕ}
    (ciphertext : TFHE.TLWE.Ciphertext R dimension) :
    TFHE.TLWE.Ciphertext R dimension :=
  ⟨-ciphertext.mask, -ciphertext.body⟩

/-- Componentwise negation negates the TLWE phase. -/
@[simp]
theorem phase_negateCiphertext {R : Type} [CommRing R] {dimension : ℕ}
    (secret : Fin dimension → R) (ciphertext : TFHE.TLWE.Ciphertext R dimension) :
    TFHE.TLWE.phase secret (negateCiphertext ciphertext) =
      -TFHE.TLWE.phase secret ciphertext := by
  simp [TFHE.TLWE.phase, negateCiphertext, dotProduct, Finset.sum_neg_distrib]
  ring

end TLWE

namespace TGSW

/-- The target-key row assembled from either a source TGSW row or a supplied suffix row. -/
def extendedRow {R : Type} [Zero R]
    {sourceDimension suffixDimension levels : ℕ}
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (suffixRow : Fin suffixDimension → Fin levels →
      TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension))
    (index : Fin (sourceDimension + suffixDimension + 1) × Fin levels) :
    TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension) :=
  Fin.lastCases
    (TLWE.extendCiphertext (suffixDimension := suffixDimension)
      (TFHE.TLWE.entry source
        (finProdFinEquiv (Fin.last sourceDimension, index.2))))
    (fun coordinate ↦
      Fin.addCases
        (fun sourceCoordinate ↦
          TLWE.extendCiphertext (suffixDimension := suffixDimension)
            (TFHE.TLWE.entry source
              (finProdFinEquiv (Fin.castSucc sourceCoordinate, index.2))))
        (fun suffixCoordinate ↦ suffixRow suffixCoordinate index.2)
        coordinate)
    index.1

/-- Assemble a full target-layout TGSW ciphertext from the source rows and the missing suffix
gadget rows. -/
def assembleExtension {R : Type} [Zero R]
    {sourceDimension suffixDimension levels : ℕ}
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (suffixRow : Fin suffixDimension → Fin levels →
      TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension)) :
    TFHE.TGSW.Ciphertext R (sourceDimension + suffixDimension) levels :=
  TFHE.TLWE.batchOfRows fun row ↦
    extendedRow source suffixRow (TFHE.TGSW.rowIndex row)

/-- Prefix gadget rows are source rows with zero suffix masks. -/
@[simp]
theorem entry_assembleExtension_prefix {R : Type} [Zero R]
    {sourceDimension suffixDimension levels : ℕ}
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (suffixRow : Fin suffixDimension → Fin levels →
      TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension))
    (coordinate : Fin sourceDimension) (level : Fin levels) :
    TFHE.TLWE.entry (assembleExtension source suffixRow)
        (finProdFinEquiv
          (Fin.castSucc (Fin.castAdd suffixDimension coordinate), level)) =
      TLWE.extendCiphertext (suffixDimension := suffixDimension)
        (TFHE.TLWE.entry source
          (finProdFinEquiv (Fin.castSucc coordinate, level))) := by
  change extendedRow source suffixRow
      (TFHE.TGSW.rowIndex
        (finProdFinEquiv
          (Fin.castSucc (Fin.castAdd suffixDimension coordinate), level))) = _
  rw [show TFHE.TGSW.rowIndex
      (finProdFinEquiv
        (Fin.castSucc (Fin.castAdd suffixDimension coordinate), level)) =
      (Fin.castSucc (Fin.castAdd suffixDimension coordinate), level) by
    exact Equiv.symm_apply_apply finProdFinEquiv _]
  simp only [extendedRow, Fin.lastCases_castSucc, Fin.addCases_left]

/-- New suffix gadget rows are exactly the caller-supplied completion rows. -/
@[simp]
theorem entry_assembleExtension_suffix {R : Type} [Zero R]
    {sourceDimension suffixDimension levels : ℕ}
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (suffixRow : Fin suffixDimension → Fin levels →
      TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension))
    (coordinate : Fin suffixDimension) (level : Fin levels) :
    TFHE.TLWE.entry (assembleExtension source suffixRow)
        (finProdFinEquiv
          (Fin.castSucc (Fin.natAdd sourceDimension coordinate), level)) =
      suffixRow coordinate level := by
  change extendedRow source suffixRow
      (TFHE.TGSW.rowIndex
        (finProdFinEquiv
          (Fin.castSucc (Fin.natAdd sourceDimension coordinate), level))) = _
  rw [show TFHE.TGSW.rowIndex
      (finProdFinEquiv
        (Fin.castSucc (Fin.natAdd sourceDimension coordinate), level)) =
      (Fin.castSucc (Fin.natAdd sourceDimension coordinate), level) by
    exact Equiv.symm_apply_apply finProdFinEquiv _]
  simp only [extendedRow, Fin.lastCases_castSucc, Fin.addCases_right]

/-- The final body gadget rows are source body rows with zero suffix masks. -/
@[simp]
theorem entry_assembleExtension_last {R : Type} [Zero R]
    {sourceDimension suffixDimension levels : ℕ}
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (suffixRow : Fin suffixDimension → Fin levels →
      TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension))
    (level : Fin levels) :
    TFHE.TLWE.entry (assembleExtension source suffixRow)
        (finProdFinEquiv (Fin.last (sourceDimension + suffixDimension), level)) =
      TLWE.extendCiphertext (suffixDimension := suffixDimension)
        (TFHE.TLWE.entry source
          (finProdFinEquiv (Fin.last sourceDimension, level))) := by
  change extendedRow source suffixRow
      (TFHE.TGSW.rowIndex
        (finProdFinEquiv (Fin.last (sourceDimension + suffixDimension), level))) = _
  rw [show TFHE.TGSW.rowIndex
      (finProdFinEquiv (Fin.last (sourceDimension + suffixDimension), level)) =
      (Fin.last (sourceDimension + suffixDimension), level) by
    exact Equiv.symm_apply_apply finProdFinEquiv _]
  simp only [extendedRow, Fin.lastCases_last]

/-- Source-prefix TGSW row errors are preserved exactly by key extension. -/
theorem rowError_assembleExtension_prefix {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels : ℕ}
    (sourceSecret : Fin sourceDimension → R)
    (suffixSecret : Fin suffixDimension → R)
    (gadget : Fin levels → R) (message : R)
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (suffixRow : Fin suffixDimension → Fin levels →
      TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension))
    (coordinate : Fin sourceDimension) (level : Fin levels) :
    TFHE.TGSW.rowError (Fin.append sourceSecret suffixSecret) gadget message
        (assembleExtension source suffixRow)
        (Fin.castSucc (Fin.castAdd suffixDimension coordinate), level) =
      TFHE.TGSW.rowError sourceSecret gadget message source
        (Fin.castSucc coordinate, level) := by
  unfold TFHE.TGSW.rowError
  rw [entry_assembleExtension_prefix, TLWE.phase_extendCiphertext,
    TFHE.TGSW.gadgetPhase_castSucc, TFHE.TGSW.gadgetPhase_castSucc]
  simp

/-- The final body-block TGSW row errors are preserved exactly by key extension. -/
theorem rowError_assembleExtension_last {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels : ℕ}
    (sourceSecret : Fin sourceDimension → R)
    (suffixSecret : Fin suffixDimension → R)
    (gadget : Fin levels → R) (message : R)
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (suffixRow : Fin suffixDimension → Fin levels →
      TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension))
    (level : Fin levels) :
    TFHE.TGSW.rowError (Fin.append sourceSecret suffixSecret) gadget message
        (assembleExtension source suffixRow)
        (Fin.last (sourceDimension + suffixDimension), level) =
      TFHE.TGSW.rowError sourceSecret gadget message source
        (Fin.last sourceDimension, level) := by
  unfold TFHE.TGSW.rowError
  rw [entry_assembleExtension_last, TLWE.phase_extendCiphertext,
    TFHE.TGSW.gadgetPhase_last, TFHE.TGSW.gadgetPhase_last]

/-- A supplied suffix row completes the target TGSW semantics exactly when its phase encrypts
the missing bilinear gadget message. -/
theorem rowError_assembleExtension_suffix {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels : ℕ}
    (sourceSecret : Fin sourceDimension → R)
    (suffixSecret : Fin suffixDimension → R)
    (gadget : Fin levels → R) (message : R)
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (suffixRow : Fin suffixDimension → Fin levels →
      TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension))
    (coordinate : Fin suffixDimension) (level : Fin levels) :
    TFHE.TGSW.rowError (Fin.append sourceSecret suffixSecret) gadget message
        (assembleExtension source suffixRow)
        (Fin.castSucc (Fin.natAdd sourceDimension coordinate), level) =
      TFHE.TLWE.phase (Fin.append sourceSecret suffixSecret)
          (suffixRow coordinate level) +
        suffixSecret coordinate * (message * gadget level) := by
  unfold TFHE.TGSW.rowError
  rw [entry_assembleExtension_suffix, TFHE.TGSW.gadgetPhase_castSucc]
  simp

/-! ## Completing the missing rows with a shared-randomness KSK -/

/-- A missing target TGSW row obtained from the source TGSW ciphertext and the corresponding
suffix-only KSK row. -/
def suffixRowFromKeySwitch {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels : ℕ}
    (decompose : TFHE.TLWE.Ciphertext R sourceDimension →
      Fin (sourceDimension + 1) → Fin levels → R)
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (keySwitchKey : TFHE.TLWE.BatchCiphertext R sourceDimension
      (suffixDimension * levels))
    (coordinate : Fin suffixDimension) (level : Fin levels) :
    TFHE.TLWE.Ciphertext R (sourceDimension + suffixDimension) :=
  TLWE.extendCiphertext (suffixDimension := suffixDimension)
    (TLWE.negateCiphertext
      (TFHE.TGSW.externalProduct
        (decompose (TFHE.TGSW.KeySwitch.row keySwitchKey (coordinate, level)))
        source))

/-- Assemble the derived target-key TGSW ciphertext.  The plaintext message is unchanged; the
suffix-only KSK supplies the gadget blocks introduced by the larger target key. -/
def extendWithKeySwitch {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels : ℕ}
    (decompose : TFHE.TLWE.Ciphertext R sourceDimension →
      Fin (sourceDimension + 1) → Fin levels → R)
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (keySwitchKey : TFHE.TLWE.BatchCiphertext R sourceDimension
      (suffixDimension * levels)) :
    TFHE.TGSW.Ciphertext R (sourceDimension + suffixDimension) levels :=
  assembleExtension source (suffixRowFromKeySwitch decompose source keySwitchKey)

/-- Exact completion formula for every new suffix gadget row.  Its only deviations from an ideal
target-key TGSW row are the source KSK row error and the source-BRK external-product error. -/
theorem rowError_extendWithKeySwitch_suffix {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels : ℕ}
    (sourceSecret : Fin sourceDimension → R)
    (suffixSecret : Fin suffixDimension → R)
    (gadget : Fin levels → R) (message : R)
    (decompose : TFHE.TLWE.Ciphertext R sourceDimension →
      Fin (sourceDimension + 1) → Fin levels → R)
    (source : TFHE.TGSW.Ciphertext R sourceDimension levels)
    (keySwitchKey : TFHE.TLWE.BatchCiphertext R sourceDimension
      (suffixDimension * levels))
    (coordinate : Fin suffixDimension) (level : Fin levels)
    (hDecomposes : TFHE.Gadget.Decomposes gadget
      (TFHE.TGSW.KeySwitch.row keySwitchKey (coordinate, level))
      (decompose (TFHE.TGSW.KeySwitch.row keySwitchKey (coordinate, level)))) :
    TFHE.TGSW.rowError (Fin.append sourceSecret suffixSecret) gadget message
        (extendWithKeySwitch decompose source keySwitchKey)
        (Fin.castSucc (Fin.natAdd sourceDimension coordinate), level) =
      -(message * TFHE.TGSW.KeySwitch.rowError sourceSecret suffixSecret gadget
          keySwitchKey (coordinate, level)) -
        TFHE.TGSW.externalProductError sourceSecret gadget message
          (decompose (TFHE.TGSW.KeySwitch.row keySwitchKey (coordinate, level)))
          source := by
  rw [extendWithKeySwitch, rowError_assembleExtension_suffix]
  simp only [suffixRowFromKeySwitch, TLWE.phase_extendCiphertext,
    TLWE.phase_negateCiphertext]
  rw [TFHE.TGSW.phase_externalProduct_eq_mul_add_error sourceSecret gadget message
    (TFHE.TGSW.KeySwitch.row keySwitchKey (coordinate, level))
    (decompose (TFHE.TGSW.KeySwitch.row keySwitchKey (coordinate, level)))
    source hDecomposes]
  unfold TFHE.TGSW.KeySwitch.rowError
  ring

/-- Apply the source-to-target conversion independently to every plaintext entry of a BRK. -/
def extendBootstrappingKeyWithKeySwitch {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels messageCount : ℕ}
    (decompose : TFHE.TLWE.Ciphertext R sourceDimension →
      Fin (sourceDimension + 1) → Fin levels → R)
    (sourceBootstrappingKey :
      Fin messageCount → TFHE.TGSW.Ciphertext R sourceDimension levels)
    (keySwitchKey : TFHE.TLWE.BatchCiphertext R sourceDimension
      (suffixDimension * levels)) :
    Fin messageCount →
      TFHE.TGSW.Ciphertext R (sourceDimension + suffixDimension) levels :=
  fun messageCoordinate ↦
    extendWithKeySwitch decompose
      (sourceBootstrappingKey messageCoordinate) keySwitchKey

/-! ## Security is inherited by deterministic post-processing -/

/-- Public source view: a source-key BRK together with the suffix-only ring KSK used to complete
the target gadget rows. -/
abbrev SourceView (R : Type)
    (sourceDimension suffixDimension levels messageCount : ℕ) :=
  (Fin messageCount → TFHE.TGSW.Ciphertext R sourceDimension levels) ×
    TFHE.TLWE.BatchCiphertext R sourceDimension (suffixDimension * levels)

/-- Public converted view: the derived target-key BRK, with the same KSK retained. -/
abbrev TargetView (R : Type)
    (sourceDimension suffixDimension levels messageCount : ℕ) :=
  (Fin messageCount →
      TFHE.TGSW.Ciphertext R (sourceDimension + suffixDimension) levels) ×
    TFHE.TLWE.BatchCiphertext R sourceDimension (suffixDimension * levels)

/-- Deterministically convert the complete source public view to the nested target-key view. -/
def convertView {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels messageCount : ℕ}
    (decompose : TFHE.TLWE.Ciphertext R sourceDimension →
      Fin (sourceDimension + 1) → Fin levels → R)
    (view : SourceView R sourceDimension suffixDimension levels messageCount) :
    TargetView R sourceDimension suffixDimension levels messageCount :=
  (extendBootstrappingKeyWithKeySwitch decompose view.1 view.2, view.2)

/-- Any distinguishing distance between converted target views is at most the distance between
their source BRK-plus-KSK views.  This is the security content of the public arrow: conversion
cannot create a new distinguishing advantage. -/
theorem tvDist_convertView_le {R : Type} [CommRing R]
    {sourceDimension suffixDimension levels messageCount : ℕ}
    (decompose : TFHE.TLWE.Ciphertext R sourceDimension →
      Fin (sourceDimension + 1) → Fin levels → R)
    (left right : ProbComp
      (SourceView R sourceDimension suffixDimension levels messageCount)) :
    tvDist (convertView decompose <$> left) (convertView decompose <$> right) ≤
      tvDist left right :=
  tvDist_map_le (m := ProbComp) (convertView decompose) left right

/-- The same lossless security transfer holds after any common randomized continuation.  In
particular, an evaluator or adversary using the derived target BRK cannot obtain more
distinguishing advantage than was already present in the source BRK-plus-KSK view. -/
theorem tvDist_convertView_bind_le {R Output : Type} [CommRing R]
    {sourceDimension suffixDimension levels messageCount : ℕ}
    (decompose : TFHE.TLWE.Ciphertext R sourceDimension →
      Fin (sourceDimension + 1) → Fin levels → R)
    (left right : ProbComp
      (SourceView R sourceDimension suffixDimension levels messageCount))
    (continuation :
      TargetView R sourceDimension suffixDimension levels messageCount → ProbComp Output) :
    tvDist
        ((convertView decompose <$> left) >>= continuation)
        ((convertView decompose <$> right) >>= continuation) ≤
      tvDist left right := by
  exact (tvDist_bind_right_le continuation _ _).trans
    (tvDist_convertView_le decompose left right)

end TGSW

/-! ## Native ring-key specialization -/

namespace Native

/-- A target ring key formed by appending fresh ring components to its source ring-key prefix. -/
def appendRingSecret {sourceRank suffixRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    RingBinarySecret (sourceRank + suffixRank) degree :=
  Fin.append sourceSecret suffixSecret

/-- Ring embedding respects the source/suffix concatenation exactly. -/
@[simp]
theorem embedRingSecret_appendRingSecret
    (q : ℕ) {sourceRank suffixRank degree : ℕ}
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    embedRingSecret q (appendRingSecret sourceSecret suffixSecret) =
      Fin.append (embedRingSecret q sourceSecret) (embedRingSecret q suffixSecret) := by
  funext component
  refine Fin.addCases ?_ ?_ component
  · intro sourceComponent
    simp [embedRingSecret, appendRingSecret]
  · intro suffixComponent
    simp [embedRingSecret, appendRingSecret]

/-- Ring-valued suffix-only KSK used by source-to-target BRK conversion. -/
abbrev RingKeySwitchKey
    (q degree sourceRank suffixRank levels : ℕ) :=
  TFHE.TLWE.BatchCiphertext (RLWE.Rq q degree) sourceRank (suffixRank * levels)

/-- Gadget-scaled suffix-ring-key messages in the ring KSK. -/
def ringKeySwitchMessages
    (q degree suffixRank levels : ℕ)
    (gadget : Fin levels → RLWE.Rq q degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    Fin (suffixRank * levels) → RLWE.Rq q degree :=
  fun row ↦
    let indexed := finProdFinEquiv.symm row
    embedBinaryPolynomial q degree (suffixSecret indexed.1) * gadget indexed.2

/-- Generate the ring KSK rows that encrypt only the fresh suffix components under the source
ring key. -/
noncomputable def generateRingKeySwitchKey
    (q degree sourceRank suffixRank levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    ProbComp (RingKeySwitchKey q degree sourceRank suffixRank levels) :=
  TFHE.TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler
    (embedRingSecret q sourceSecret)
    (ringKeySwitchMessages q degree suffixRank levels gadget suffixSecret)

/-- Convert a native source-ring BRK to the derived native target-ring BRK while keeping its
plaintext message vector unchanged. -/
noncomputable def deriveTargetBootstrappingKey
    (q degree sourceRank suffixRank levels messageCount : ℕ)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin levels → RLWE.Rq q degree)
    (sourceBootstrappingKey :
      TFHE.Native.BootstrappingKey q degree sourceRank levels messageCount)
    (keySwitchKey : RingKeySwitchKey q degree sourceRank suffixRank levels) :
    TFHE.Native.BootstrappingKey q degree (sourceRank + suffixRank) levels messageCount :=
  TGSW.extendBootstrappingKeyWithKeySwitch decompose
    sourceBootstrappingKey keySwitchKey

/-- The one-circular source BRK that remains after the shared-randomness conversion: its
plaintext bits are the coefficient extraction of the same source ring key used for encryption. -/
noncomputable def generateSourceCircularBootstrappingKey
    (q degree sourceRank levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree) :
    ProbComp (TFHE.Native.BootstrappingKey q degree sourceRank levels
      (sourceRank * degree)) :=
  TFHE.Native.generateBootstrappingKey q degree sourceRank levels
    (sourceRank * degree) errorSampler gadget
    (keyExtract sourceSecret) sourceSecret

/-- Public source view for the one-circular construction before BRK key extension. -/
abbrev SourceCircularView
    (q degree sourceRank suffixRank levels : ℕ) :=
  TGSW.SourceView (RLWE.Rq q degree) sourceRank suffixRank levels
    (sourceRank * degree)

/-- Public target view after applying the source-to-target BRK conversion. -/
abbrev DerivedTargetView
    (q degree sourceRank suffixRank levels : ℕ) :=
  TGSW.TargetView (RLWE.Rq q degree) sourceRank suffixRank levels
    (sourceRank * degree)

/-- Real one-circular source view.  The source BRK encrypts `keyExtract(sourceSecret)` under
`sourceSecret`; the ring KSK encrypts only the independent target-key suffix under that same
source key. -/
noncomputable def realSourceCircularView
    (q degree sourceRank suffixRank levels : ℕ) [NeZero q]
    (bootstrapErrorSampler keySwitchErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree) :
    ProbComp (SourceCircularView q degree sourceRank suffixRank levels) := do
  let sourceSecret ← TFHE.Native.sampleRingSecret sourceRank degree
  let suffixSecret ← TFHE.Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ← generateSourceCircularBootstrappingKey q degree
    sourceRank levels bootstrapErrorSampler gadget sourceSecret
  let keySwitchKey ← generateRingKeySwitchKey q degree sourceRank suffixRank levels
    keySwitchErrorSampler gadget sourceSecret suffixSecret
  return (sourceBootstrappingKey, keySwitchKey)

/-- Zero-message comparison source view with the identical nested-key KSK. -/
noncomputable def zeroSourceCircularView
    (q degree sourceRank suffixRank levels : ℕ) [NeZero q]
    (bootstrapErrorSampler keySwitchErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree) :
    ProbComp (SourceCircularView q degree sourceRank suffixRank levels) := do
  let sourceSecret ← TFHE.Native.sampleRingSecret sourceRank degree
  let suffixSecret ← TFHE.Native.sampleRingSecret suffixRank degree
  let sourceBootstrappingKey ← TFHE.Native.generateZeroBootstrappingKey q degree
    sourceRank levels (sourceRank * degree) bootstrapErrorSampler gadget sourceSecret
  let keySwitchKey ← generateRingKeySwitchKey q degree sourceRank suffixRank levels
    keySwitchErrorSampler gadget sourceSecret suffixSecret
  return (sourceBootstrappingKey, keySwitchKey)

/-- Derived target-key real view. -/
noncomputable def realDerivedTargetView
    (q degree sourceRank suffixRank levels : ℕ) [NeZero q]
    (bootstrapErrorSampler keySwitchErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin levels → RLWE.Rq q degree) :
    ProbComp (DerivedTargetView q degree sourceRank suffixRank levels) :=
  TGSW.convertView decompose <$>
    realSourceCircularView q degree sourceRank suffixRank levels
      bootstrapErrorSampler keySwitchErrorSampler gadget

/-- Derived target-key zero-message comparison view. -/
noncomputable def zeroDerivedTargetView
    (q degree sourceRank suffixRank levels : ℕ) [NeZero q]
    (bootstrapErrorSampler keySwitchErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin levels → RLWE.Rq q degree) :
    ProbComp (DerivedTargetView q degree sourceRank suffixRank levels) :=
  TGSW.convertView decompose <$>
    zeroSourceCircularView q degree sourceRank suffixRank levels
      bootstrapErrorSampler keySwitchErrorSampler gadget

/-- **One-circular source-to-target security transfer.**  The real-versus-zero distance of the
derived target-key BRK is no larger than that of the source one-circular BRK with its shared KSK.
No target-key circular assumption is introduced by the public conversion. -/
theorem tvDist_realDerivedTarget_zero_le_sourceCircular
    (q degree sourceRank suffixRank levels : ℕ) [NeZero q]
    (bootstrapErrorSampler keySwitchErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin levels → RLWE.Rq q degree) :
    tvDist
        (realDerivedTargetView q degree sourceRank suffixRank levels
          bootstrapErrorSampler keySwitchErrorSampler gadget decompose)
        (zeroDerivedTargetView q degree sourceRank suffixRank levels
          bootstrapErrorSampler keySwitchErrorSampler gadget decompose) ≤
      tvDist
        (realSourceCircularView q degree sourceRank suffixRank levels
          bootstrapErrorSampler keySwitchErrorSampler gadget)
        (zeroSourceCircularView q degree sourceRank suffixRank levels
          bootstrapErrorSampler keySwitchErrorSampler gadget) :=
  TGSW.tvDist_convertView_le decompose _ _

/-- The one-circular transfer remains valid for an arbitrary randomized use of the derived
target-key BRK, including a TFHE evaluator followed by a distinguisher. -/
theorem tvDist_realDerivedTarget_bind_zero_le_sourceCircular {Output : Type}
    (q degree sourceRank suffixRank levels : ℕ) [NeZero q]
    (bootstrapErrorSampler keySwitchErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q degree) sourceRank →
      Fin (sourceRank + 1) → Fin levels → RLWE.Rq q degree)
    (continuation : DerivedTargetView q degree sourceRank suffixRank levels →
      ProbComp Output) :
    tvDist
        (realDerivedTargetView q degree sourceRank suffixRank levels
          bootstrapErrorSampler keySwitchErrorSampler gadget decompose >>= continuation)
        (zeroDerivedTargetView q degree sourceRank suffixRank levels
          bootstrapErrorSampler keySwitchErrorSampler gadget decompose >>= continuation) ≤
      tvDist
        (realSourceCircularView q degree sourceRank suffixRank levels
          bootstrapErrorSampler keySwitchErrorSampler gadget)
        (zeroSourceCircularView q degree sourceRank suffixRank levels
          bootstrapErrorSampler keySwitchErrorSampler gadget) := by
  exact (tvDist_bind_right_le continuation _ _).trans
    (tvDist_realDerivedTarget_zero_le_sourceCircular q degree sourceRank suffixRank levels
      bootstrapErrorSampler keySwitchErrorSampler gadget decompose)

end Native

end FormalProof4FHE.TFHE.SharedRandomnessKeyExtension
