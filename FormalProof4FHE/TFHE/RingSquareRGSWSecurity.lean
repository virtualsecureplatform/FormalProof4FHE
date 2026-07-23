/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInput
import FormalProof4FHE.LWE.TwoBlock
import FormalProof4FHE.Probability.FiniteCenteredSupport
import FormalProof4FHE.TFHE.InternalProduct
import FormalProof4FHE.TFHE.SharpRotationNoise

/-!
# The Standalone Circular-Security Problem for `RGSW_S(-S)`

This file isolates the smallest nonlinear object needed by the narrow-noise RLWE-to-RGSW
conversion: one rank-one RGSW encryption of the negative of its own ring secret.

For a rank-one secret `S`, the two row blocks of `RGSW_S(-S)` have ideal phases

* `S * S * gadget level` in the mask block; and
* `-S * gadget level` in the final block.

The second family is not a circular-security obstacle.  Subtracting the public gadget element
from the row mask changes its phase by `S * gadget level`, cancelling that linear message.
This public transformation is invertible and does not change any row error.  Consequently the
security of `RGSW_S(-S)` is exactly the security of a batch containing only the gadget-scaled
ring-square messages `S^2 * gadget level`, together with ordinary zero-message RLWE rows.

The reduction in this file is exact and algebraic.  It deliberately does not claim that the
remaining narrow-noise ring-square distribution follows from ordinary RLWE; that implication is
the standalone research problem exposed by the final game equivalences.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TGSW.RingSquare

/-! ## A public rank-one mask translation -/

namespace Row

/-- Subtract one public ring element from the unique mask coordinate of a rank-one row. -/
def subtractMask {R : Type} [Sub R] (offset : R) (ciphertext : TLWE.Ciphertext R 1) :
    TLWE.Ciphertext R 1 :=
  ⟨fun _ ↦ ciphertext.mask 0 - offset, ciphertext.body⟩

/-- Undo `subtractMask`. -/
def addMask {R : Type} [Add R] (offset : R) (ciphertext : TLWE.Ciphertext R 1) :
    TLWE.Ciphertext R 1 :=
  ⟨fun _ ↦ ciphertext.mask 0 + offset, ciphertext.body⟩

@[simp]
theorem addMask_subtractMask {R : Type} [AddGroup R]
    (offset : R) (ciphertext : TLWE.Ciphertext R 1) :
    addMask offset (subtractMask offset ciphertext) = ciphertext := by
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    rw [Subsingleton.elim coordinate 0]
    simp [addMask, subtractMask]
  · rfl

@[simp]
theorem subtractMask_addMask {R : Type} [AddGroup R]
    (offset : R) (ciphertext : TLWE.Ciphertext R 1) :
    subtractMask offset (addMask offset ciphertext) = ciphertext := by
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    rw [Subsingleton.elim coordinate 0]
    simp [addMask, subtractMask]
  · rfl

/-- For every public offset, mask subtraction is a permutation of the full rank-one row
carrier. -/
theorem subtractMask_bijective {R : Type} [AddGroup R] (offset : R) :
    Function.Bijective (subtractMask offset : TLWE.Ciphertext R 1 → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨addMask offset, addMask_subtractMask offset, subtractMask_addMask offset⟩

/-- Removing an offset from the public mask adds `secret * offset` to the phase. -/
theorem phase_subtractMask {R : Type} [CommRing R]
    (secret : Fin 1 → R) (offset : R) (ciphertext : TLWE.Ciphertext R 1) :
    TLWE.phase secret (subtractMask offset ciphertext) =
      TLWE.phase secret ciphertext + secret 0 * offset := by
  simp [TLWE.phase, subtractMask, dotProduct]
  ring

/-- Restoring an offset to the public mask subtracts `secret * offset` from the phase. -/
theorem phase_addMask {R : Type} [CommRing R]
    (secret : Fin 1 → R) (offset : R) (ciphertext : TLWE.Ciphertext R 1) :
    TLWE.phase secret (addMask offset ciphertext) =
      TLWE.phase secret ciphertext - secret 0 * offset := by
  simp [TLWE.phase, addMask, dotProduct]
  ring

end Row

/-! ## Strip the linear block from an RGSW ciphertext -/

/-- Strip the publicly removable linear message from one indexed rank-one RGSW row. -/
def strippedRow {R : Type} [Sub R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels)
    (index : Fin 2 × Fin levels) : TLWE.Ciphertext R 1 :=
  Fin.lastCases
    (Row.subtractMask (gadget index.2)
      (TLWE.entry ciphertext (finProdFinEquiv index)))
    (fun _ ↦ TLWE.entry ciphertext (finProdFinEquiv index)) index.1

/-- Apply `strippedRow` to every row of a rank-one RGSW ciphertext. -/
def stripLinearBlock {R : Type} [Sub R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels) :
    Ciphertext R 1 levels :=
  TLWE.batchOfRows fun row ↦
    strippedRow gadget ciphertext (finProdFinEquiv.symm row)

/-- Restore the publicly removable linear message to one indexed row. -/
def restoredRow {R : Type} [Add R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels)
    (index : Fin 2 × Fin levels) : TLWE.Ciphertext R 1 :=
  Fin.lastCases
    (Row.addMask (gadget index.2)
      (TLWE.entry ciphertext (finProdFinEquiv index)))
    (fun _ ↦ TLWE.entry ciphertext (finProdFinEquiv index)) index.1

/-- Inverse public transformation to `stripLinearBlock`. -/
def restoreLinearBlock {R : Type} [Add R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels) :
    Ciphertext R 1 levels :=
  TLWE.batchOfRows fun row ↦
    restoredRow gadget ciphertext (finProdFinEquiv.symm row)

@[simp]
theorem entry_strip_castSucc {R : Type} [Sub R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels)
    (coordinate : Fin 1) (level : Fin levels) :
    TLWE.entry (stripLinearBlock gadget ciphertext)
        (finProdFinEquiv (Fin.castSucc coordinate, level)) =
      TLWE.entry ciphertext (finProdFinEquiv (Fin.castSucc coordinate, level)) := by
  change strippedRow gadget ciphertext
      (finProdFinEquiv.symm (finProdFinEquiv (Fin.castSucc coordinate, level))) = _
  rw [Equiv.symm_apply_apply]
  simp [strippedRow]

@[simp]
theorem entry_strip_last {R : Type} [Sub R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels)
    (level : Fin levels) :
    TLWE.entry (stripLinearBlock gadget ciphertext)
        (finProdFinEquiv (Fin.last 1, level)) =
      Row.subtractMask (gadget level)
        (TLWE.entry ciphertext (finProdFinEquiv (Fin.last 1, level))) := by
  change strippedRow gadget ciphertext
      (finProdFinEquiv.symm (finProdFinEquiv (Fin.last 1, level))) = _
  rw [Equiv.symm_apply_apply]
  change @Fin.lastCases 1 (fun _ ↦ TLWE.Ciphertext R 1)
      (Row.subtractMask (gadget level)
        (TLWE.entry ciphertext (finProdFinEquiv (Fin.last 1, level))))
      (fun _ : Fin 1 ↦ TLWE.entry ciphertext
        (finProdFinEquiv (Fin.last 1, level))) (Fin.last 1) = _
  rw [Fin.lastCases_last]

@[simp]
theorem entry_restore_castSucc {R : Type} [Add R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels)
    (coordinate : Fin 1) (level : Fin levels) :
    TLWE.entry (restoreLinearBlock gadget ciphertext)
        (finProdFinEquiv (Fin.castSucc coordinate, level)) =
      TLWE.entry ciphertext (finProdFinEquiv (Fin.castSucc coordinate, level)) := by
  change restoredRow gadget ciphertext
      (finProdFinEquiv.symm (finProdFinEquiv (Fin.castSucc coordinate, level))) = _
  rw [Equiv.symm_apply_apply]
  simp [restoredRow]

@[simp]
theorem entry_restore_last {R : Type} [Add R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels)
    (level : Fin levels) :
    TLWE.entry (restoreLinearBlock gadget ciphertext)
        (finProdFinEquiv (Fin.last 1, level)) =
      Row.addMask (gadget level)
        (TLWE.entry ciphertext (finProdFinEquiv (Fin.last 1, level))) := by
  change restoredRow gadget ciphertext
      (finProdFinEquiv.symm (finProdFinEquiv (Fin.last 1, level))) = _
  rw [Equiv.symm_apply_apply]
  change @Fin.lastCases 1 (fun _ ↦ TLWE.Ciphertext R 1)
      (Row.addMask (gadget level)
        (TLWE.entry ciphertext (finProdFinEquiv (Fin.last 1, level))))
      (fun _ : Fin 1 ↦ TLWE.entry ciphertext
        (finProdFinEquiv (Fin.last 1, level))) (Fin.last 1) = _
  rw [Fin.lastCases_last]

@[simp]
theorem entry_restore_strip {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels)
    (row : Fin (rowCount 1 levels)) :
    TLWE.entry (restoreLinearBlock gadget (stripLinearBlock gadget ciphertext)) row =
      TLWE.entry ciphertext row := by
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases
  · rw [entry_restore_last, entry_strip_last, Row.addMask_subtractMask]
  · simp

@[simp]
theorem entry_strip_restore {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels)
    (row : Fin (rowCount 1 levels)) :
    TLWE.entry (stripLinearBlock gadget (restoreLinearBlock gadget ciphertext)) row =
      TLWE.entry ciphertext row := by
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases
  · rw [entry_strip_last, entry_restore_last, Row.subtractMask_addMask]
  · simp

@[simp]
theorem restore_strip {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels) :
    restoreLinearBlock gadget (stripLinearBlock gadget ciphertext) = ciphertext := by
  apply Prod.ext
  · funext coordinate row
    exact congrArg (fun selected ↦ selected.mask coordinate)
      (entry_restore_strip gadget ciphertext row)
  · funext row
    exact congrArg TLWE.Ciphertext.body
      (entry_restore_strip gadget ciphertext row)

@[simp]
theorem strip_restore {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R) (ciphertext : Ciphertext R 1 levels) :
    stripLinearBlock gadget (restoreLinearBlock gadget ciphertext) = ciphertext := by
  apply Prod.ext
  · funext coordinate row
    exact congrArg (fun selected ↦ selected.mask coordinate)
      (entry_strip_restore gadget ciphertext row)
  · funext row
    exact congrArg TLWE.Ciphertext.body
      (entry_strip_restore gadget ciphertext row)

/-- The public stripping map is a permutation of the complete ciphertext carrier. -/
theorem stripLinearBlock_bijective {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R) :
    Function.Bijective (stripLinearBlock gadget : Ciphertext R 1 levels → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨restoreLinearBlock gadget, restore_strip gadget, strip_restore gadget⟩

/-- The inverse public restoration map is likewise a permutation of the ciphertext carrier. -/
theorem restoreLinearBlock_bijective {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R) :
    Function.Bijective (restoreLinearBlock gadget : Ciphertext R 1 levels → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨stripLinearBlock gadget, strip_restore gadget, restore_strip gadget⟩

/-! ## Exact ring-square phase normal form -/

/-- Ideal phase vector after the linear final block has been stripped. -/
def squarePhase {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) :
    Fin (rowCount 1 levels) → R :=
  fun row ↦
    let index := finProdFinEquiv.symm row
    Fin.lastCases 0
      (fun _ ↦ secret 0 * secret 0 * gadget index.2) index.1

@[simp]
theorem squarePhase_castSucc {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R)
    (coordinate : Fin 1) (level : Fin levels) :
    squarePhase secret gadget (finProdFinEquiv (Fin.castSucc coordinate, level)) =
      secret 0 * secret 0 * gadget level := by
  simp [squarePhase]

@[simp]
theorem squarePhase_last {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (level : Fin levels) :
    squarePhase secret gadget (finProdFinEquiv (Fin.last 1, level)) = 0 := by
  unfold squarePhase
  rw [Equiv.symm_apply_apply]
  exact Fin.lastCases_last

/-- Every stripped mask-block row has exactly the `S^2` gadget phase plus its original RGSW
row error. -/
theorem phase_entry_strip_castSucc_eq_square_add_error
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R)
    (ciphertext : Ciphertext R 1 levels) (coordinate : Fin 1) (level : Fin levels) :
    TLWE.phase secret
        (TLWE.entry (stripLinearBlock gadget ciphertext)
          (finProdFinEquiv (Fin.castSucc coordinate, level))) =
      squarePhase secret gadget
          (finProdFinEquiv (Fin.castSucc coordinate, level)) +
        rowError secret gadget (-secret 0) ciphertext (Fin.castSucc coordinate, level) := by
  rw [entry_strip_castSucc, squarePhase_castSucc]
  unfold rowError
  rw [gadgetPhase_castSucc]
  rw [Subsingleton.elim coordinate 0]
  ring

/-- Every stripped final-block row is an ordinary zero-message RLWE row with exactly its
original RGSW row error. -/
theorem phase_entry_strip_last_eq_error
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R)
    (ciphertext : Ciphertext R 1 levels) (level : Fin levels) :
    TLWE.phase secret
        (TLWE.entry (stripLinearBlock gadget ciphertext)
          (finProdFinEquiv (Fin.last 1, level))) =
      rowError secret gadget (-secret 0) ciphertext (Fin.last 1, level) := by
  rw [entry_strip_last, Row.phase_subtractMask]
  unfold rowError
  rw [gadgetPhase_last]
  ring

/-! ## The noisy secret-approximation reduction template -/

/-- Publicly subtract a purported approximation to `gadget * S` from an ordinary RLWE mask.
If the approximation is `gadget * S + eta`, the resulting row encrypts `gadget * S^2` with the
additional multiplicative error `S * eta`. -/
def squareFromApproximation {R : Type} [Sub R]
    (approximation : R) (ordinaryRow : TLWE.Ciphertext R 1) : TLWE.Ciphertext R 1 :=
  Row.subtractMask approximation ordinaryRow

/-- Exact phase identity behind the only direct public coefficient-shift construction of a
ring-square row. -/
theorem phase_squareFromApproximation
    {R : Type} [CommRing R]
    (secret : Fin 1 → R) (gadget approximation eta : R)
    (ordinaryRow : TLWE.Ciphertext R 1)
    (hApproximation : approximation = gadget * secret 0 + eta) :
    TLWE.phase secret (squareFromApproximation approximation ordinaryRow) =
      secret 0 * secret 0 * gadget +
        TLWE.phase secret ordinaryRow + secret 0 * eta := by
  rw [squareFromApproximation, Row.phase_subtractMask, hApproximation]
  ring

/-- After removing the intended square message, the new residual is exactly the old RLWE phase
plus `S * eta`.  Thus statistical hiding by a wide `eta` and TFHE correctness pull in opposite
directions; no noise term is suppressed by notation. -/
theorem residual_squareFromApproximation
    {R : Type} [CommRing R]
    (secret : Fin 1 → R) (gadget approximation eta : R)
    (ordinaryRow : TLWE.Ciphertext R 1)
    (hApproximation : approximation = gadget * secret 0 + eta) :
    TLWE.phase secret (squareFromApproximation approximation ordinaryRow) -
        secret 0 * secret 0 * gadget =
      TLWE.phase secret ordinaryRow + secret 0 * eta := by
  rw [phase_squareFromApproximation secret gadget approximation eta ordinaryRow hApproximation]
  ring

/-! ## A conditional compiler from ordinary RLWE rows

The following construction records a concrete possible reduction rather than postulating a
square ciphertext outright.  Given public weights whose linear combination of ordinary RLWE
masks is one fixed gadget element `g`, the same combination of the public bodies is

`g * S + (the weighted ordinary-RLWE errors)`.

It can therefore be used as the approximation in `squareFromApproximation`.  The resulting
square row has residual

`targetError + S * (the weighted source errors)`.

All transformations below are public and deterministic.  The missing cryptographic obligation
is exactly an efficient way to find such weights with a sufficiently small weighted error for
uniform challenger-supplied masks.  This file does not assume that ordinary RLWE supplies that
short-preimage algorithm.
-/

/-- Public linear combination used to seek a fixed gadget preimage among ordinary RLWE masks. -/
def preimageCombination {R Index : Type} [Semiring R] [Fintype Index]
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1) :
    TLWE.Ciphertext R 1 :=
  TLWE.linearCombination weight sourceRows

/-- The public weights recompose the requested gadget element in the unique rank-one mask
coordinate. -/
def HasGadgetPreimage {R Index : Type} [Semiring R] [Fintype Index]
    (gadget : R) (weight : Index → R)
    (sourceRows : Index → TLWE.Ciphertext R 1) : Prop :=
  (preimageCombination weight sourceRows).mask 0 = gadget

/-- The weighted public bodies attached to a candidate gadget preimage. -/
def gadgetApproximation {R Index : Type} [Semiring R] [Fintype Index]
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1) : R :=
  (preimageCombination weight sourceRows).body

/-- A genuine mask preimage makes the weighted body exactly `g * S` plus the weighted source
phase. -/
theorem gadgetApproximation_eq_mul_add_phase
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret : Fin 1 → R) (gadget : R) (weight : Index → R)
    (sourceRows : Index → TLWE.Ciphertext R 1)
    (hPreimage : HasGadgetPreimage gadget weight sourceRows) :
    gadgetApproximation weight sourceRows =
      gadget * secret 0 +
        TLWE.phase secret (preimageCombination weight sourceRows) := by
  unfold gadgetApproximation TLWE.phase
  unfold HasGadgetPreimage at hPreimage
  have hdot :
      dotProduct secret (preimageCombination weight sourceRows).mask =
        secret 0 * gadget := by
    rw [show dotProduct secret (preimageCombination weight sourceRows).mask =
        secret 0 * (preimageCombination weight sourceRows).mask 0 by
      simp [dotProduct]]
    rw [hPreimage]
  rw [hdot]
  ring

/-- The error in the public approximation is visibly the weighted sum of the ordinary source
phases. -/
theorem phase_preimageCombination_eq_weighted
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret : Fin 1 → R) (weight : Index → R)
    (sourceRows : Index → TLWE.Ciphertext R 1) :
    TLWE.phase secret (preimageCombination weight sourceRows) =
      ∑ index, weight index * TLWE.phase secret (sourceRows index) := by
  exact TLWE.phase_linearCombination secret weight sourceRows

/-- Compile a target ordinary RLWE row into a gadget-scaled square row using only the public
body of a source-row gadget preimage. -/
def squareFromPreimage {R Index : Type} [CommRing R] [Fintype Index]
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1) : TLWE.Ciphertext R 1 :=
  squareFromApproximation (gadgetApproximation weight sourceRows) targetRow

/-- Exact phase of the short-preimage square compiler. -/
theorem phase_squareFromPreimage
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret : Fin 1 → R) (gadget : R) (weight : Index → R)
    (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (hPreimage : HasGadgetPreimage gadget weight sourceRows) :
    TLWE.phase secret (squareFromPreimage weight sourceRows targetRow) =
      secret 0 * secret 0 * gadget + TLWE.phase secret targetRow +
        secret 0 * TLWE.phase secret (preimageCombination weight sourceRows) := by
  apply phase_squareFromApproximation secret gadget
    (gadgetApproximation weight sourceRows)
    (TLWE.phase secret (preimageCombination weight sourceRows)) targetRow
  exact gadgetApproximation_eq_mul_add_phase secret gadget weight sourceRows hPreimage

/-- Removing the intended square term leaves the target error plus `S` times the weighted
source error. -/
theorem residual_squareFromPreimage
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret : Fin 1 → R) (gadget : R) (weight : Index → R)
    (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (hPreimage : HasGadgetPreimage gadget weight sourceRows) :
    TLWE.phase secret (squareFromPreimage weight sourceRows targetRow) -
        secret 0 * secret 0 * gadget =
      TLWE.phase secret targetRow +
        secret 0 * TLWE.phase secret (preimageCombination weight sourceRows) := by
  rw [phase_squareFromPreimage secret gadget weight sourceRows targetRow hPreimage]
  ring

/-- Abstract checked noise budget for the short-preimage compiler.  Any subadditive norm with a
stated multiplication cost can be plugged in; the only construction-specific premise is the
bound on the weighted source phase. -/
theorem norm_squareFromPreimageResidual_le
    {R Index : Type} [CommRing R] [Fintype Index]
    (norm : R → ℕ) (multiplicationCost : ℕ)
    (hAdd : ∀ left right, norm (left + right) ≤ norm left + norm right)
    (hMul : ∀ left right,
      norm (left * right) ≤ multiplicationCost * (norm left * norm right))
    (secret : Fin 1 → R) (gadget : R) (weight : Index → R)
    (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (targetBound secretBound weightedSourceBound : ℕ)
    (hPreimage : HasGadgetPreimage gadget weight sourceRows)
    (hTarget : norm (TLWE.phase secret targetRow) ≤ targetBound)
    (hSecret : norm (secret 0) ≤ secretBound)
    (hWeightedSource :
      norm (TLWE.phase secret (preimageCombination weight sourceRows)) ≤
        weightedSourceBound) :
    norm (TLWE.phase secret (squareFromPreimage weight sourceRows targetRow) -
        secret 0 * secret 0 * gadget) ≤
      targetBound + multiplicationCost * (secretBound * weightedSourceBound) := by
  rw [residual_squareFromPreimage secret gadget weight sourceRows targetRow hPreimage]
  exact (hAdd _ _).trans
    (Nat.add_le_add hTarget
      ((hMul _ _).trans
        (Nat.mul_le_mul_left multiplicationCost
          (Nat.mul_le_mul hSecret hWeightedSource))))

/-! ## Lossless reduction of the compiler output to ordinary batch RLWE

The source rows used to manufacture the approximation are internal to the reduction.  The output
contains only a fresh target row whose uniform mask is translated by the derived approximation.
Consequently the compiled uniform branch is exactly uniform for *every* deterministic public
selector, whether or not that selector finds a useful preimage.  Preimage success and small
weighted error are needed for the output to be a correct narrow square encryption, but not for
its computational pseudorandomness reduction.
-/

namespace PreimageCompiler

/-- Internal ordinary-RLWE source rows consumed to compile one square row. -/
abbrev SourceRows (R : Type) (sourceCount : ℕ) :=
  Fin sourceCount → TLWE.Ciphertext R 1

/-- The unequal two-block ordinary-LWE transcript: `sourceCount` internal rows followed by one
fresh target row. -/
abbrev InputTranscript (R : Type) (sourceCount : ℕ) :=
  LWE.TwoBlock.Transcript R 1 sourceCount 1

/-- A deterministic public algorithm selecting ring weights from only the source masks. -/
abbrev Selector (R : Type) (sourceCount : ℕ) :=
  (Fin sourceCount → R) → Fin sourceCount → R

/-- Repackage the two-block matrix/output transcript as individual source rows and one target
row. -/
def transcriptRowsEquiv (R : Type) (sourceCount : ℕ) :
    InputTranscript R sourceCount ≃
      (SourceRows R sourceCount × TLWE.Ciphertext R 1) where
  toFun transcript :=
    (fun source ↦
      ⟨fun _ ↦ transcript.1.1 0 source, transcript.2.1 source⟩,
    ⟨fun _ ↦ transcript.1.2 0 0, transcript.2.2 0⟩)
  invFun rows :=
    ((fun _ source ↦ (rows.1 source).mask 0,
      fun _ _ ↦ rows.2.mask 0),
    (fun source ↦ (rows.1 source).body,
      fun _ ↦ rows.2.body))
  left_inv transcript := by
    rcases transcript with ⟨⟨firstChallenge, secondChallenge⟩,
      firstOutput, secondOutput⟩
    apply Prod.ext
    · apply Prod.ext
      · funext coordinate source
        rw [Subsingleton.elim coordinate 0]
      · funext coordinate sample
        rw [Subsingleton.elim coordinate 0, Subsingleton.elim sample 0]
    · apply Prod.ext
      · rfl
      · funext sample
        rw [Subsingleton.elim sample 0]
  right_inv rows := by
    apply Prod.ext
    · funext source
      rw [TLWE.Ciphertext.mk.injEq]
      constructor
      · funext coordinate
        rw [Subsingleton.elim coordinate 0]
      · rfl
    · rw [TLWE.Ciphertext.mk.injEq]
      constructor
      · funext coordinate
        rw [Subsingleton.elim coordinate 0]
      · rfl

/-- Extract the public source-mask vector inspected by a selector. -/
def sourceMasks {R : Type} {sourceCount : ℕ}
    (sourceRows : SourceRows R sourceCount) : Fin sourceCount → R :=
  fun source ↦ (sourceRows source).mask 0

/-- Compile one row after the transcript has been split into internal sources and a fresh target. -/
def compileRows {R : Type} [CommRing R] {sourceCount : ℕ}
    (selector : Selector R sourceCount)
    (rows : SourceRows R sourceCount × TLWE.Ciphertext R 1) :
    TLWE.Ciphertext R 1 :=
  squareFromPreimage (selector (sourceMasks rows.1)) rows.1 rows.2

/-- Public deterministic preprocessing of one ordinary two-block RLWE transcript. -/
def compileTranscript {R : Type} [CommRing R] {sourceCount : ℕ}
    (selector : Selector R sourceCount) (transcript : InputTranscript R sourceCount) :
    TLWE.Ciphertext R 1 :=
  compileRows selector (transcriptRowsEquiv R sourceCount transcript)

/-- For fixed internal sources, compilation is just a public translation of the target mask and
is therefore a permutation of the complete target-row carrier. -/
theorem compileRows_target_bijective
    {R : Type} [CommRing R] {sourceCount : ℕ}
    (selector : Selector R sourceCount) (sourceRows : SourceRows R sourceCount) :
    Function.Bijective
      (fun targetRow ↦ compileRows selector (sourceRows, targetRow)) := by
  exact Row.subtractMask_bijective (gadgetApproximation
    (selector (sourceMasks sourceRows)) sourceRows)

noncomputable local instance sampleableCiphertext
    {R : Type} [SampleableType R] {dimension : ℕ} :
    SampleableType (TLWE.Ciphertext R dimension) :=
  SampleableType.ofEquiv (TLWE.ciphertextEquiv R dimension)

/-- Compiling a canonical uniform two-block transcript produces an exactly uniform target row.
This is unconditional in the selector: the internal source rows may determine an arbitrary mask
translation, because the independent target mask is a one-time pad. -/
theorem compileTranscript_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {sourceCount : ℕ} (selector : Selector R sourceCount) :
    evalDist
        (compileTranscript selector <$>
          ($ᵗ (InputTranscript R sourceCount))) =
      evalDist ($ᵗ (TLWE.Ciphertext R 1)) := by
  let Rows := SourceRows R sourceCount
  let Target := TLWE.Ciphertext R 1
  have hRepackage :
      evalDist
          (transcriptRowsEquiv R sourceCount <$>
            ($ᵗ (InputTranscript R sourceCount))) =
        evalDist ($ᵗ (Rows × Target)) := by
    exact evalDist_map_bijective_uniform_cross
      (α := InputTranscript R sourceCount) (β := Rows × Target)
      (transcriptRowsEquiv R sourceCount)
      (transcriptRowsEquiv R sourceCount).bijective
  have hFiber (sourceRows : Rows) :
      evalDist
          ((fun targetRow ↦ compileRows selector (sourceRows, targetRow)) <$>
            ($ᵗ Target)) =
        evalDist ($ᵗ Target) := by
    exact evalDist_map_bijective_uniform_cross
      (α := Target) (β := Target)
      (fun targetRow ↦ compileRows selector (sourceRows, targetRow))
      (compileRows_target_bijective selector sourceRows)
  have hPair :
      evalDist (compileRows selector <$> ($ᵗ (Rows × Target))) =
        evalDist ($ᵗ Target) := by
    have uniformPair :
        ($ᵗ (Rows × Target) : ProbComp (Rows × Target)) =
          Prod.mk <$> ($ᵗ Rows) <*> ($ᵗ Target) := rfl
    rw [uniformPair, map_seq, Functor.map_map, seq_eq_bind_map,
      map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind, Function.comp_apply]
    calc
      evalDist
          (($ᵗ Rows) >>= fun sourceRows ↦
            (fun targetRow ↦ compileRows selector (sourceRows, targetRow)) <$>
              ($ᵗ Target)) =
          evalDist (($ᵗ Rows) >>= fun _sourceRows ↦ ($ᵗ Target)) := by
        exact evalDist_bind_congr' ($ᵗ Rows) hFiber
      _ = evalDist ($ᵗ Target) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          ($ᵗ Rows) (by simp) ($ᵗ Target)
  calc
    evalDist
        (compileTranscript selector <$>
          ($ᵗ (InputTranscript R sourceCount))) =
      evalDist
        (compileRows selector <$>
          (transcriptRowsEquiv R sourceCount <$>
            ($ᵗ (InputTranscript R sourceCount)))) := by
        apply congrArg evalDist
        rw [Functor.map_map]
        rfl
    _ = evalDist (compileRows selector <$> ($ᵗ (Rows × Target))) := by
      exact evalDist_map_eq_of_evalDist_eq hRepackage (compileRows selector)
    _ = evalDist ($ᵗ Target) := hPair

/-- A public Boolean distinguisher for one compiled rank-one row. -/
abbrev Distinguisher (R : Type) := TLWE.Ciphertext R 1 → ProbComp Bool

/-- Feed a two-block ordinary-LWE transcript through the hidden-source compiler before invoking
the row distinguisher. -/
def reduction {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    {sourceCount : ℕ} {secretSampler : ProbComp Secret}
    {embed : Secret → Fin 1 → R} {errorSampler : ProbComp R}
    (selector : Selector R sourceCount) (distinguisher : Distinguisher R) :
    LearningWithErrors.Adversary
      (LWE.TwoBlock.problem 1 sourceCount 1 secretSampler embed errorSampler) :=
  fun transcript ↦ distinguisher (compileTranscript selector transcript)

/-- Real compiled-row game obtained from `sourceCount + 1` ordinary LWE samples sharing one
secret.  The source rows remain internal; only the translated target row reaches the
distinguisher. -/
def realGame {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selector : Selector R sourceCount) (distinguisher : Distinguisher R) : ProbComp Bool :=
  LearningWithErrors.game0
    (LWE.TwoBlock.problem 1 sourceCount 1 secretSampler embed errorSampler)
    (reduction selector distinguisher)

/-- Canonical uniform-row endpoint for the compiler game. -/
noncomputable def uniformGame {R : Type} [SampleableType R]
    (distinguisher : Distinguisher R) : ProbComp Bool := do
  let row ← $ᵗ (TLWE.Ciphertext R 1)
  distinguisher row

/-- The compiler's real-versus-uniform distinguishing advantage. -/
noncomputable def advantage {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selector : Selector R sourceCount) (distinguisher : Distinguisher R) : ℝ :=
  (realGame sourceCount secretSampler embed errorSampler selector distinguisher).boolDistAdvantage
    (uniformGame distinguisher)

/-- The uniform branch of the two-block LWE reduction is exactly the canonical uniform-row
game.  No preimage-success or shortness hypothesis occurs in this theorem. -/
theorem reduction_game1_evalDist_eq_uniformGame
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selector : Selector R sourceCount) (distinguisher : Distinguisher R) :
    evalDist
        (LearningWithErrors.game1
          (LWE.TwoBlock.problem 1 sourceCount 1 secretSampler embed errorSampler)
          (reduction selector distinguisher)) =
      evalDist (uniformGame distinguisher) := by
  rw [LearningWithErrors.game1,
    LWE.TwoBlock.uniformDistr_eq_uniformSample]
  simp only [reduction, uniformGame]
  rw [show
      (($ᵗ (InputTranscript R sourceCount)) >>= fun transcript ↦
        distinguisher (compileTranscript selector transcript)) =
        ((compileTranscript selector <$>
          ($ᵗ (InputTranscript R sourceCount))) >>= distinguisher) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, compileTranscript_uniform_evalDist, ← evalDist_bind]

/-- **Lossless compiler reduction.**  Distinguishing the compiler-induced row from uniform has
exactly the advantage of its deterministic reduction against the unequal two-block ordinary-LWE
problem. -/
theorem advantage_eq_twoBlockLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selector : Selector R sourceCount) (distinguisher : Distinguisher R) :
    advantage sourceCount secretSampler embed errorSampler selector distinguisher =
      LearningWithErrors.advantage
        (LWE.TwoBlock.problem 1 sourceCount 1 secretSampler embed errorSampler)
        (reduction selector distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold advantage ProbComp.boolDistAdvantage realGame
  rw [evalDist_ext_iff.mp
    (reduction_game1_evalDist_eq_uniformGame sourceCount secretSampler embed errorSampler
      selector distinguisher) true]

/-- The same lossless theorem stated directly against ordinary batch LWE with
`sourceCount + 1` samples. -/
theorem advantage_eq_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selector : Selector R sourceCount) (distinguisher : Distinguisher R) :
    advantage sourceCount secretSampler embed errorSampler selector distinguisher =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.embeddedBatchProblem 1 (sourceCount + 1)
          secretSampler embed errorSampler)
        (LWE.TwoBlock.reduction (reduction selector distinguisher)) := by
  rw [advantage_eq_twoBlockLWE sourceCount secretSampler embed errorSampler
    selector distinguisher]
  exact LWE.TwoBlock.advantage_eq_batch 1 sourceCount 1
    secretSampler embed errorSampler (reduction selector distinguisher)

/-- A selector succeeds for `gadget` on a source family exactly when its selected public weights
recompose that gadget in the source masks. -/
def SelectorSucceeds {R : Type} [CommRing R] {sourceCount : ℕ}
    (gadget : R) (selector : Selector R sourceCount)
    (sourceRows : SourceRows R sourceCount) : Prop :=
  HasGadgetPreimage gadget (selector (sourceMasks sourceRows)) sourceRows

/-- On every successful source family, the compiled real row has the desired square phase and
the explicit target-plus-weighted-source residual. -/
theorem phase_compileRows
    {R : Type} [CommRing R] {sourceCount : ℕ}
    (secret : Fin 1 → R) (gadget : R) (selector : Selector R sourceCount)
    (sourceRows : SourceRows R sourceCount) (targetRow : TLWE.Ciphertext R 1)
    (hSuccess : SelectorSucceeds gadget selector sourceRows) :
    TLWE.phase secret (compileRows selector (sourceRows, targetRow)) =
      secret 0 * secret 0 * gadget + TLWE.phase secret targetRow +
        secret 0 * TLWE.phase secret
          (preimageCombination (selector (sourceMasks sourceRows)) sourceRows) := by
  exact phase_squareFromPreimage secret gadget
    (selector (sourceMasks sourceRows)) sourceRows targetRow hSuccess

/-! ### The exact one-source inversion route

For one source row, an invertible public mask makes the preimage equation algebraically trivial:
multiply by the inverse mask.  The construction below deliberately accepts an explicit inverse
function.  Thus its security reduction remains executable whenever ring inversion is executable;
the theorem does not hide inversion behind a noncomputable choice.

This route exposes rather than solves the narrow-noise problem.  Its weighted source phase is
exactly `gadget * inverse(mask) * sourceError`, so a generic inverse of a uniform mask need not be
short in the coefficient norm used by TFHE.
-/

namespace SingleSourceInverse

/-- With one source mask `a`, select the unique evident weight `g * inverse(a)`. -/
def selector {R : Type} [Mul R]
    (gadget : R) (inverse : R → R) : Selector R 1 :=
  fun masks _source ↦ gadget * inverse (masks 0)

/-- The one-source selector recomposes the gadget whenever the supplied inverse is a left
inverse of the observed public mask. -/
theorem selectorSucceeds_of_inverse_mul_mask
    {R : Type} [CommRing R]
    (gadget : R) (inverse : R → R) (sourceRows : SourceRows R 1)
    (hInverse :
      inverse ((sourceRows 0).mask 0) * (sourceRows 0).mask 0 = 1) :
    SelectorSucceeds gadget (selector gadget inverse) sourceRows := by
  classical
  unfold SelectorSucceeds HasGadgetPreimage preimageCombination
  simp [TLWE.linearCombination, selector, sourceMasks, mul_assoc, hInverse]

/-- The weighted source phase of the one-source inversion compiler is exactly the source error
multiplied by the inverse-mask weight. -/
theorem phase_preimageCombination_selector
    {R : Type} [CommRing R]
    (secret : Fin 1 → R) (gadget : R) (inverse : R → R)
    (sourceRows : SourceRows R 1) :
    TLWE.phase secret
        (preimageCombination
          (selector gadget inverse (sourceMasks sourceRows)) sourceRows) =
      (gadget * inverse ((sourceRows 0).mask 0)) *
        TLWE.phase secret (sourceRows 0) := by
  rw [phase_preimageCombination_eq_weighted]
  simp [selector, sourceMasks]

/-- Exact square-row phase produced by one invertible source mask. -/
theorem phase_compileRows
    {R : Type} [CommRing R]
    (secret : Fin 1 → R) (gadget : R) (inverse : R → R)
    (sourceRows : SourceRows R 1) (targetRow : TLWE.Ciphertext R 1)
    (hInverse :
      inverse ((sourceRows 0).mask 0) * (sourceRows 0).mask 0 = 1) :
    TLWE.phase secret
        (compileRows (selector gadget inverse) (sourceRows, targetRow)) =
      secret 0 * secret 0 * gadget + TLWE.phase secret targetRow +
        secret 0 *
          ((gadget * inverse ((sourceRows 0).mask 0)) *
            TLWE.phase secret (sourceRows 0)) := by
  rw [PreimageCompiler.phase_compileRows secret gadget
    (selector gadget inverse) sourceRows targetRow
    (selectorSucceeds_of_inverse_mul_mask gadget inverse sourceRows hInverse)]
  rw [phase_preimageCombination_selector]

/-- After removing the intended `S² g` message, the precise residual is the target error plus
the source error multiplied by `S * g * inverse(mask)`. -/
theorem residual_compileRows
    {R : Type} [CommRing R]
    (secret : Fin 1 → R) (gadget : R) (inverse : R → R)
    (sourceRows : SourceRows R 1) (targetRow : TLWE.Ciphertext R 1)
    (hInverse :
      inverse ((sourceRows 0).mask 0) * (sourceRows 0).mask 0 = 1) :
    TLWE.phase secret
          (compileRows (selector gadget inverse) (sourceRows, targetRow)) -
        secret 0 * secret 0 * gadget =
      TLWE.phase secret targetRow +
        secret 0 *
          ((gadget * inverse ((sourceRows 0).mask 0)) *
            TLWE.phase secret (sourceRows 0)) := by
  rw [phase_compileRows secret gadget inverse sourceRows targetRow hInverse]
  ring

/-- The one-source route's complete abstract noise budget.  In addition to the usual target,
secret, gadget, and source-error bounds, it necessarily contains a bound on the inverse of the
uniform source mask.  This is the quantitative obstruction specific to the evident inversion
strategy. -/
theorem norm_residual_compileRows_le
    {R : Type} [CommRing R]
    (norm : R → ℕ) (multiplicationCost : ℕ)
    (hAdd : ∀ left right, norm (left + right) ≤ norm left + norm right)
    (hMul : ∀ left right,
      norm (left * right) ≤ multiplicationCost * (norm left * norm right))
    (secret : Fin 1 → R) (gadget : R) (inverse : R → R)
    (sourceRows : SourceRows R 1) (targetRow : TLWE.Ciphertext R 1)
    (targetBound secretBound gadgetBound inverseBound sourceBound : ℕ)
    (hInverse :
      inverse ((sourceRows 0).mask 0) * (sourceRows 0).mask 0 = 1)
    (hTarget : norm (TLWE.phase secret targetRow) ≤ targetBound)
    (hSecret : norm (secret 0) ≤ secretBound)
    (hGadget : norm gadget ≤ gadgetBound)
    (hInverseBound : norm (inverse ((sourceRows 0).mask 0)) ≤ inverseBound)
    (hSource : norm (TLWE.phase secret (sourceRows 0)) ≤ sourceBound) :
    norm
        (TLWE.phase secret
            (compileRows (selector gadget inverse) (sourceRows, targetRow)) -
          secret 0 * secret 0 * gadget) ≤
      targetBound + multiplicationCost *
        (secretBound *
          (multiplicationCost *
            ((multiplicationCost * (gadgetBound * inverseBound)) * sourceBound))) := by
  rw [residual_compileRows secret gadget inverse sourceRows targetRow hInverse]
  refine (hAdd _ _).trans (Nat.add_le_add hTarget ?_)
  refine (hMul _ _).trans
    (Nat.mul_le_mul_left multiplicationCost (Nat.mul_le_mul hSecret ?_))
  refine (hMul _ _).trans
    (Nat.mul_le_mul_left multiplicationCost (Nat.mul_le_mul ?_ hSource))
  exact (hMul _ _).trans
    (Nat.mul_le_mul_left multiplicationCost (Nat.mul_le_mul hGadget hInverseBound))

/-! #### Distribution of the inverse multiplier

Conditioning a uniform source mask to be a unit does not make its inverse small.  Multiplication
by a fixed unit followed by inversion is a permutation of the unit group.  In particular, at the
TFHE gadget level `g = 1`, the evident preimage weight is uniformly distributed over all units.
-/

/-- The unit-valued version of the one-source weight. -/
def unitWeight {R : Type} [Monoid R] (gadgetUnit sourceUnit : Rˣ) : Rˣ :=
  (Equiv.divLeft gadgetUnit) sourceUnit

/-- For a fixed unit gadget, taking the inverse-mask weight permutes the unit group. -/
theorem unitWeight_bijective {R : Type} [CommMonoid R] (gadgetUnit : Rˣ) :
    Function.Bijective (unitWeight gadgetUnit : Rˣ → Rˣ) := by
  exact (Equiv.divLeft gadgetUnit : Rˣ ≃ Rˣ).bijective

/-- A uniform unit mask gives an exactly uniform inverse-mask weight. -/
theorem unitWeight_uniform_evalDist
    {R : Type} [CommMonoid R] [Fintype Rˣ] [SampleableType Rˣ]
    (gadgetUnit : Rˣ) :
    evalDist (unitWeight gadgetUnit <$> ($ᵗ Rˣ)) =
      evalDist ($ᵗ Rˣ) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Rˣ) (β := Rˣ)
    (unitWeight gadgetUnit) (unitWeight_bijective gadgetUnit)

/-- Consequently, every proposed coefficient-shortness predicate holds for the inverse weight
with exactly its density in the unit group. -/
theorem probEvent_unitWeight_eq_uniformUnit
    {R : Type} [CommRing R] [Fintype Rˣ] [SampleableType Rˣ]
    (gadgetUnit : Rˣ) (short : R → Prop) [DecidablePred short] :
    Pr[(fun sourceUnit : Rˣ ↦ short (unitWeight gadgetUnit sourceUnit : R)) |
        ($ᵗ Rˣ)] =
      Pr[(fun weightUnit : Rˣ ↦ short (weightUnit : R)) | ($ᵗ Rˣ)] := by
  calc
    Pr[(fun sourceUnit : Rˣ ↦ short (unitWeight gadgetUnit sourceUnit : R)) |
        ($ᵗ Rˣ)] =
        Pr[(fun weightUnit : Rˣ ↦ short (weightUnit : R)) |
          unitWeight gadgetUnit <$> ($ᵗ Rˣ)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[(fun weightUnit : Rˣ ↦ short (weightUnit : R)) | ($ᵗ Rˣ)] := by
      exact probEvent_congr' (fun _ _ ↦ Iff.rfl)
        (unitWeight_uniform_evalDist gadgetUnit)

/-- Cardinality form of the preceding identity.  For `gadgetUnit = 1`, this is the exact success
probability of hoping that the inverse of a uniform unit mask lies in a chosen short set. -/
theorem probEvent_unitWeight_eq_shortUnitDensity
    {R : Type} [CommRing R] [Fintype Rˣ] [SampleableType Rˣ]
    (gadgetUnit : Rˣ) (short : R → Prop) [DecidablePred short] :
      Pr[(fun sourceUnit : Rˣ ↦ short (unitWeight gadgetUnit sourceUnit : R)) |
        ($ᵗ Rˣ)] =
      (Finset.univ.filter
          (fun weightUnit : Rˣ ↦ short (weightUnit : R))).card /
        (Fintype.card Rˣ : ENNReal) := by
  rw [probEvent_unitWeight_eq_uniformUnit gadgetUnit short,
    probEvent_uniformSample]

namespace NativeShortness

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Units of a native positive-degree RLWE ring whose centered coefficient norm is bounded. -/
abbrev BoundedUnit (q degree bound : ℕ) [NeZero q] :=
  {unit : (RLWE.Rq q (degree + 1))ˣ //
    LatticeCrypto.cInfNorm (unit : RLWE.Rq q (degree + 1)) ≤ bound}

noncomputable instance instFintypeBoundedUnit
    (q degree bound : ℕ) [NeZero q] :
    Fintype (BoundedUnit q degree bound) := by
  classical
  exact Fintype.ofFinite _

/-- Forgetting invertibility injects bounded units into the complete centered coefficient box. -/
def boundedUnitToBoundedPolynomial
    {q degree bound : ℕ} [NeZero q]
    (unit : BoundedUnit q degree bound) :
    FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial
      q (degree + 1) bound :=
  ⟨(unit.1 : RLWE.Rq q (degree + 1)), unit.2⟩

theorem boundedUnitToBoundedPolynomial_injective
    {q degree bound : ℕ} [NeZero q] :
    Function.Injective
      (boundedUnitToBoundedPolynomial :
        BoundedUnit q degree bound →
          FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial
            q (degree + 1) bound) := by
  intro left right heq
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val heq

/-- At most `(2B+1)^N` units can have centered coefficient norm at most `B`. -/
theorem card_boundedUnit_le
    (q degree bound : ℕ) [NeZero q] :
    Fintype.card (BoundedUnit q degree bound) ≤
      (2 * bound + 1) ^ (degree + 1) := by
  exact (Fintype.card_le_of_injective boundedUnitToBoundedPolynomial
    boundedUnitToBoundedPolynomial_injective).trans
      (FormalProof4FHE.FiniteCenteredSupport.card_boundedPolynomial_le
        q (degree + 1) bound)

/-- Exact inverse-weight uniformity plus the centered-box count.  This is a rigorous upper bound
on the chance that the evident one-source mask inverse has a usable coefficient norm. -/
theorem probEvent_unitWeight_cInfNorm_le
    {q degree : ℕ} [NeZero q]
    [SampleableType (RLWE.Rq q (degree + 1))ˣ]
    (gadgetUnit : (RLWE.Rq q (degree + 1))ˣ) (bound : ℕ) :
    Pr[(fun sourceUnit : (RLWE.Rq q (degree + 1))ˣ ↦
          LatticeCrypto.cInfNorm
            (unitWeight gadgetUnit sourceUnit : RLWE.Rq q (degree + 1)) ≤ bound) |
        ($ᵗ (RLWE.Rq q (degree + 1))ˣ)] ≤
      (((2 * bound + 1) ^ (degree + 1) : ℕ) : ENNReal) /
        Fintype.card (RLWE.Rq q (degree + 1))ˣ := by
  rw [probEvent_unitWeight_eq_shortUnitDensity gadgetUnit
    (fun value : RLWE.Rq q (degree + 1) ↦
      LatticeCrypto.cInfNorm value ≤ bound)]
  apply ENNReal.div_le_div_right
  exact_mod_cast (show
    (Finset.univ.filter fun weightUnit : (RLWE.Rq q (degree + 1))ˣ ↦
      LatticeCrypto.cInfNorm
        (weightUnit : RLWE.Rq q (degree + 1)) ≤ bound).card ≤
        (2 * bound + 1) ^ (degree + 1) by
      rw [← Fintype.card_subtype]
      exact card_boundedUnit_le q degree bound)

end

end NativeShortness

end SingleSourceInverse

/-! ## The exact remaining native-error gap -/

/-- Deterministically assemble one honest square-message row with a fresh public mask. -/
def assembleSquareRow {R : Type} [CommRing R]
    (secret : Fin 1 → R) (gadget error : R) (mask : Fin 1 → R) :
    TLWE.Ciphertext R 1 :=
  TLWE.assemble secret mask (secret 0 * secret 0 * gadget) error

@[simp]
theorem phase_assembleSquareRow {R : Type} [CommRing R]
    (secret : Fin 1 → R) (gadget error : R) (mask : Fin 1 → R) :
    TLWE.phase secret (assembleSquareRow secret gadget error mask) =
      secret 0 * secret 0 * gadget + error := by
  exact TLWE.phase_assemble secret mask (secret 0 * secret 0 * gadget) error

/-- Native fresh square-row distribution with the requested error sampler. -/
def nativeSquareRowSampler {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R) : ProbComp (TLWE.Ciphertext R 1) := do
  let secretValue ← secretSampler
  let mask ← $ᵗ (Fin 1 → R)
  let error ← errorSampler
  return assembleSquareRow (embed secretValue) gadget error mask

/-- Row distribution actually emitted by the hidden-source compiler on a real ordinary-LWE
transcript. -/
def compiledRowSampler {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selector : Selector R sourceCount) : ProbComp (TLWE.Ciphertext R 1) := do
  let transcript ← LearningWithErrors.distr
    (LWE.TwoBlock.problem 1 sourceCount 1 secretSampler embed errorSampler)
  return compileTranscript selector transcript

/-- The only information-theoretic term left by the lossless LWE reduction: distance between
the native narrow square row and the compiler-induced row.  Establishing a negligible bound on
this term entails both high-probability gadget-preimage success and closeness of the induced
residual `targetError + S * weightedSourceError` to the requested native error law. -/
noncomputable def nativeDistributionGap {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : R) (selector : Selector R sourceCount) : ℝ :=
  tvDist
    (nativeSquareRowSampler secretSampler embed errorSampler gadget)
    (compiledRowSampler sourceCount secretSampler embed errorSampler selector)

/-- Native square-row distinguishing game. -/
def nativeSquareGame {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) : ProbComp Bool :=
  nativeSquareRowSampler secretSampler embed errorSampler gadget >>= distinguisher

/-- Native square-row real-versus-uniform advantage. -/
noncomputable def nativeSquareAdvantage {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : R)
    (distinguisher : Distinguisher R) : ℝ :=
  (nativeSquareGame secretSampler embed errorSampler gadget distinguisher).boolDistAdvantage
    (uniformGame distinguisher)

/-- The real two-block game is exactly postprocessing of the compiler-induced row sampler. -/
theorem realGame_eq_compiledRowSampler_bind
    {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selector : Selector R sourceCount) (distinguisher : Distinguisher R) :
    realGame sourceCount secretSampler embed errorSampler selector distinguisher =
      compiledRowSampler sourceCount secretSampler embed errorSampler selector >>=
        distinguisher := by
  simp [realGame, compiledRowSampler, LearningWithErrors.game0, reduction,
    bind_assoc, monad_norm]

/-- Native square security is bounded by the exact induced-distribution gap plus the compiler's
ordinary-LWE advantage. -/
theorem nativeSquareAdvantage_le_nativeDistributionGap_add_advantage
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : R) (selector : Selector R sourceCount)
    (distinguisher : Distinguisher R) :
    nativeSquareAdvantage secretSampler embed errorSampler gadget distinguisher ≤
      nativeDistributionGap sourceCount secretSampler embed errorSampler gadget selector +
        advantage sourceCount secretSampler embed errorSampler selector distinguisher := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (nativeSquareGame secretSampler embed errorSampler gadget distinguisher)
    (realGame sourceCount secretSampler embed errorSampler selector distinguisher)
    (uniformGame distinguisher)
  have hComparison :
      (nativeSquareGame secretSampler embed errorSampler gadget distinguisher).boolDistAdvantage
          (realGame sourceCount secretSampler embed errorSampler selector distinguisher) ≤
        nativeDistributionGap sourceCount secretSampler embed errorSampler gadget selector := by
    refine (abs_probOutput_toReal_sub_le_tvDist _ _).trans ?_
    rw [nativeSquareGame,
      realGame_eq_compiledRowSampler_bind sourceCount secretSampler embed errorSampler
        selector distinguisher]
    exact tvDist_bind_right_le distinguisher
      (nativeSquareRowSampler secretSampler embed errorSampler gadget)
      (compiledRowSampler sourceCount secretSampler embed errorSampler selector)
  simpa only [nativeSquareAdvantage, advantage] using
    hTriangle.trans (add_le_add hComparison le_rfl)

/-- Final one-row reduction statement: native square-row security follows from ordinary batch
LWE, up to exactly the native-versus-induced row-distribution gap. -/
theorem nativeSquareAdvantage_le_nativeDistributionGap_add_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : R) (selector : Selector R sourceCount)
    (distinguisher : Distinguisher R) :
    nativeSquareAdvantage secretSampler embed errorSampler gadget distinguisher ≤
      nativeDistributionGap sourceCount secretSampler embed errorSampler gadget selector +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1 (sourceCount + 1)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction (reduction selector distinguisher)) := by
  calc
    nativeSquareAdvantage secretSampler embed errorSampler gadget distinguisher ≤
        nativeDistributionGap sourceCount secretSampler embed errorSampler gadget selector +
          advantage sourceCount secretSampler embed errorSampler selector distinguisher :=
      nativeSquareAdvantage_le_nativeDistributionGap_add_advantage
        sourceCount secretSampler embed errorSampler gadget selector distinguisher
    _ = _ := congrArg
      (fun value ↦
        nativeDistributionGap sourceCount secretSampler embed errorSampler gadget selector +
          value)
      (advantage_eq_batchLWE sourceCount secretSampler embed errorSampler selector distinguisher)

/-! ## Full stripped RGSW compiler -/

namespace Full

/-- Internal ordinary-RLWE rows: one independent source pool for every gadget level. -/
abbrev SourceBatch (R : Type) (levels sourceCount : ℕ) :=
  TLWE.BatchCiphertext R 1 (levels * sourceCount)

/-- The complete stripped target has one upper square row and one lower zero row per level. -/
abbrev TargetBatch (R : Type) (levels : ℕ) :=
  TGSW.Ciphertext R 1 levels

/-- Unequal ordinary-LWE input for the full compiler. -/
abbrev InputTranscript (R : Type) (levels sourceCount : ℕ) :=
  LWE.TwoBlock.Transcript R 1 (levels * sourceCount) (TGSW.rowCount 1 levels)

/-- A possibly level-dependent public preimage selector. -/
abbrev Selectors (R : Type) (levels sourceCount : ℕ) :=
  Fin levels → Selector R sourceCount

/-- Read the source pool assigned to one gadget level. -/
def sourceRowsAt {R : Type} {levels sourceCount : ℕ}
    (sourceBatch : SourceBatch R levels sourceCount) (level : Fin levels) :
    SourceRows R sourceCount :=
  fun source ↦ TLWE.entry sourceBatch (finProdFinEquiv (level, source))

/-- Public approximation selected at one gadget level. -/
def approximationAt {R : Type} [Semiring R] {levels sourceCount : ℕ}
    (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount) (level : Fin levels) : R :=
  gadgetApproximation
    (selectors level (sourceMasks (sourceRowsAt sourceBatch level)))
    (sourceRowsAt sourceBatch level)

/-- For fixed internal sources, compile every upper row and leave every lower zero row intact. -/
def compileTargets {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount)
    (targets : TargetBatch R levels) : TargetBatch R levels :=
  TLWE.batchOfRows fun row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      compileRows (selectors indexed.2)
        (sourceRowsAt sourceBatch indexed.2, TLWE.entry targets row)
    else
      TLWE.entry targets row

/-- Inverse target-row transformation for fixed internal sources. -/
def restoreTargets {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount)
    (targets : TargetBatch R levels) : TargetBatch R levels :=
  TLWE.batchOfRows fun row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      Row.addMask (approximationAt selectors sourceBatch indexed.2)
        (TLWE.entry targets row)
    else
      TLWE.entry targets row

/-- A batch transcript is equivalent to its function of individual rows. -/
def batchRowsEquiv (R : Type) (dimension samples : ℕ) :
    TLWE.BatchCiphertext R dimension samples ≃
      (Fin samples → TLWE.Ciphertext R dimension) where
  toFun := TLWE.entry
  invFun := TLWE.batchOfRows
  left_inv ciphertext := by cases ciphertext; rfl
  right_inv rows := by funext row; exact TLWE.entry_batchOfRows rows row

@[simp]
theorem compileTargets_restoreTargets
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount)
    (targets : TargetBatch R levels) :
    compileTargets selectors sourceBatch
      (restoreTargets selectors sourceBatch targets) = targets := by
  apply (batchRowsEquiv R 1 (TGSW.rowCount 1 levels)).injective
  funext row
  by_cases hUpper : (TGSW.rowIndex row).1 = 0
  · simp [batchRowsEquiv, compileTargets, restoreTargets, hUpper,
      compileRows, squareFromPreimage, squareFromApproximation, approximationAt]
  · simp [batchRowsEquiv, compileTargets, restoreTargets, hUpper]

@[simp]
theorem restoreTargets_compileTargets
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount)
    (targets : TargetBatch R levels) :
    restoreTargets selectors sourceBatch
      (compileTargets selectors sourceBatch targets) = targets := by
  apply (batchRowsEquiv R 1 (TGSW.rowCount 1 levels)).injective
  funext row
  by_cases hUpper : (TGSW.rowIndex row).1 = 0
  · simp [batchRowsEquiv, compileTargets, restoreTargets, hUpper,
      compileRows, squareFromPreimage, squareFromApproximation, approximationAt]
  · simp [batchRowsEquiv, compileTargets, restoreTargets, hUpper]

/-- For each fixed internal source batch, full compilation permutes the complete stripped target
carrier. -/
theorem compileTargets_bijective
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount) :
    Function.Bijective (compileTargets selectors sourceBatch) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨restoreTargets selectors sourceBatch,
      restoreTargets_compileTargets selectors sourceBatch,
      compileTargets_restoreTargets selectors sourceBatch⟩

/-- Repackage the unequal two-block transcript into its internal source batch and complete target
batch. -/
def transcriptPairEquiv (R : Type) (levels sourceCount : ℕ) :
    InputTranscript R levels sourceCount ≃
      (SourceBatch R levels sourceCount × TargetBatch R levels) where
  toFun := LWE.TwoBlock.toTranscriptPair
  invFun := LWE.TwoBlock.ofTranscriptPair
  left_inv := LWE.TwoBlock.ofTranscriptPair_toTranscriptPair
  right_inv := LWE.TwoBlock.toTranscriptPair_ofTranscriptPair

/-- Full deterministic preprocessing of one unequal ordinary-LWE transcript. -/
def compileTranscript {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Selectors R levels sourceCount)
    (transcript : InputTranscript R levels sourceCount) : TargetBatch R levels :=
  let batches := transcriptPairEquiv R levels sourceCount transcript
  compileTargets selectors batches.1 batches.2

/-- The full compiler maps a canonical uniform unequal transcript to an exactly uniform stripped
RGSW carrier, for arbitrary deterministic level selectors. -/
theorem compileTranscript_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} (selectors : Selectors R levels sourceCount) :
    evalDist
        (compileTranscript selectors <$>
          ($ᵗ (InputTranscript R levels sourceCount))) =
      evalDist ($ᵗ (TargetBatch R levels)) := by
  let Sources := SourceBatch R levels sourceCount
  let Target := TargetBatch R levels
  have hRepackage :
      evalDist
          (transcriptPairEquiv R levels sourceCount <$>
            ($ᵗ (InputTranscript R levels sourceCount))) =
        evalDist ($ᵗ (Sources × Target)) := by
    exact evalDist_map_bijective_uniform_cross
      (α := InputTranscript R levels sourceCount) (β := Sources × Target)
      (transcriptPairEquiv R levels sourceCount)
      (transcriptPairEquiv R levels sourceCount).bijective
  have hFiber (sources : Sources) :
      evalDist (compileTargets selectors sources <$> ($ᵗ Target)) =
        evalDist ($ᵗ Target) := by
    exact evalDist_map_bijective_uniform_cross
      (α := Target) (β := Target)
      (compileTargets selectors sources)
      (compileTargets_bijective selectors sources)
  have hPair :
      evalDist
          ((fun batches ↦ compileTargets selectors batches.1 batches.2) <$>
            ($ᵗ (Sources × Target))) =
        evalDist ($ᵗ Target) := by
    have uniformPair :
        ($ᵗ (Sources × Target) : ProbComp (Sources × Target)) =
          Prod.mk <$> ($ᵗ Sources) <*> ($ᵗ Target) := rfl
    rw [uniformPair, map_seq, Functor.map_map, seq_eq_bind_map,
      map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind, Function.comp_apply]
    calc
      evalDist
          (($ᵗ Sources) >>= fun sources ↦
            compileTargets selectors sources <$> ($ᵗ Target)) =
          evalDist (($ᵗ Sources) >>= fun _sources ↦ ($ᵗ Target)) := by
        exact evalDist_bind_congr' ($ᵗ Sources) hFiber
      _ = evalDist ($ᵗ Target) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          ($ᵗ Sources) (by simp) ($ᵗ Target)
  calc
    evalDist
        (compileTranscript selectors <$>
          ($ᵗ (InputTranscript R levels sourceCount))) =
      evalDist
        ((fun batches ↦ compileTargets selectors batches.1 batches.2) <$>
          (transcriptPairEquiv R levels sourceCount <$>
            ($ᵗ (InputTranscript R levels sourceCount)))) := by
        apply congrArg evalDist
        rw [Functor.map_map]
        rfl
    _ = evalDist
        ((fun batches ↦ compileTargets selectors batches.1 batches.2) <$>
          ($ᵗ (Sources × Target))) := by
      exact evalDist_map_eq_of_evalDist_eq hRepackage _
    _ = evalDist ($ᵗ Target) := hPair

/-- Flattened upper row at one gadget level. -/
def upperRow {levels : ℕ} (level : Fin levels) : Fin (TGSW.rowCount 1 levels) :=
  finProdFinEquiv ((0 : Fin (1 + 1)), level)

/-- Flattened lower row at one gadget level. -/
def lowerRow {levels : ℕ} (level : Fin levels) : Fin (TGSW.rowCount 1 levels) :=
  finProdFinEquiv (Fin.last 1, level)

@[simp]
theorem rowIndex_upperRow {levels : ℕ} (level : Fin levels) :
    TGSW.rowIndex (upperRow level) = ((0 : Fin (1 + 1)), level) := by
  exact Equiv.symm_apply_apply finProdFinEquiv _

@[simp]
theorem rowIndex_lowerRow {levels : ℕ} (level : Fin levels) :
    TGSW.rowIndex (lowerRow level) = (Fin.last 1, level) := by
  exact Equiv.symm_apply_apply finProdFinEquiv _

/-- Successful public gadget preimage at a selected level. -/
def SelectorSucceedsAt {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (gadget : Fin levels → R) (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount) (level : Fin levels) : Prop :=
  SelectorSucceeds (gadget level) (selectors level)
    (sourceRowsAt sourceBatch level)

/-- Every successful upper row has the exact square phase and explicit induced residual. -/
theorem phase_entry_compileTargets_upper
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R)
    (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount)
    (targets : TargetBatch R levels) (level : Fin levels)
    (hSuccess : SelectorSucceedsAt gadget selectors sourceBatch level) :
    TLWE.phase secret
        (TLWE.entry (compileTargets selectors sourceBatch targets) (upperRow level)) =
      secret 0 * secret 0 * gadget level +
        TLWE.phase secret (TLWE.entry targets (upperRow level)) +
          secret 0 * TLWE.phase secret
            (preimageCombination
              (selectors level (sourceMasks (sourceRowsAt sourceBatch level)))
              (sourceRowsAt sourceBatch level)) := by
  simpa [compileTargets] using
    (phase_compileRows secret (gadget level) (selectors level)
      (sourceRowsAt sourceBatch level) (TLWE.entry targets (upperRow level)) hSuccess)

/-- Lower rows pass through unchanged and remain ordinary zero-message RLWE rows. -/
@[simp]
theorem entry_compileTargets_lower
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Selectors R levels sourceCount)
    (sourceBatch : SourceBatch R levels sourceCount)
    (targets : TargetBatch R levels) (level : Fin levels) :
    TLWE.entry (compileTargets selectors sourceBatch targets) (lowerRow level) =
      TLWE.entry targets (lowerRow level) := by
  simp [compileTargets]

/-- Intended square/zero message vector of the stripped rank-one RGSW matrix. -/
def squareMessages {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) :
    Fin (TGSW.rowCount 1 levels) → R :=
  fun row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then secret 0 * secret 0 * gadget indexed.2 else 0

@[simp]
theorem squareMessages_upper {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (level : Fin levels) :
    squareMessages secret gadget (upperRow level) =
      secret 0 * secret 0 * gadget level := by
  simp [squareMessages]

@[simp]
theorem squareMessages_lower {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (level : Fin levels) :
    squareMessages secret gadget (lowerRow level) = 0 := by
  simp [squareMessages]

/-- Fresh native stripped square/zero rows with the requested narrow error sampler. -/
def nativeSquareBatchSampler {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) : ProbComp (TargetBatch R levels) := do
  let secretValue ← secretSampler
  TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler (embed secretValue)
    (squareMessages (embed secretValue) gadget)

/-- Full target batch actually emitted by the compiler on a real ordinary-LWE transcript. -/
def compiledBatchSampler {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selectors : Selectors R levels sourceCount) : ProbComp (TargetBatch R levels) := do
  let transcript ← LearningWithErrors.distr
    (LWE.TwoBlock.problem 1 (levels * sourceCount) (TGSW.rowCount 1 levels)
      secretSampler embed errorSampler)
  return compileTranscript selectors transcript

/-- Boolean distinguisher for a complete stripped rank-one RGSW matrix. -/
abbrev Distinguisher (R : Type) (levels : ℕ) :=
  TargetBatch R levels → ProbComp Bool

/-- Deterministic full-compiler reduction against the unequal ordinary-LWE problem. -/
def reduction {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} {secretSampler : ProbComp Secret}
    {embed : Secret → Fin 1 → R} {errorSampler : ProbComp R}
    (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) :
    LearningWithErrors.Adversary
      (LWE.TwoBlock.problem 1 (levels * sourceCount) (TGSW.rowCount 1 levels)
        secretSampler embed errorSampler) :=
  fun transcript ↦ distinguisher (compileTranscript selectors transcript)

/-- Real full-compiler game. -/
def realGame {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) : ProbComp Bool :=
  LearningWithErrors.game0
    (LWE.TwoBlock.problem 1 (levels * sourceCount) (TGSW.rowCount 1 levels)
      secretSampler embed errorSampler)
    (reduction selectors distinguisher)

/-- Canonical uniform full-matrix endpoint. -/
def uniformGame {R : Type} [SampleableType R] {levels : ℕ}
    (distinguisher : Distinguisher R levels) : ProbComp Bool := do
  let target ← $ᵗ (TargetBatch R levels)
  distinguisher target

/-- Full compiler real-versus-uniform advantage. -/
noncomputable def advantage {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) : ℝ :=
  (realGame levels sourceCount secretSampler embed errorSampler selectors
      distinguisher).boolDistAdvantage
    (uniformGame distinguisher)

/-- Full compiler uniform-game equality. -/
theorem reduction_game1_evalDist_eq_uniformGame
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) :
    evalDist
        (LearningWithErrors.game1
          (LWE.TwoBlock.problem 1 (levels * sourceCount) (TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (reduction selectors distinguisher)) =
      evalDist (uniformGame distinguisher) := by
  rw [LearningWithErrors.game1, LWE.TwoBlock.uniformDistr_eq_uniformSample]
  simp only [reduction, uniformGame]
  rw [show
      (($ᵗ (InputTranscript R levels sourceCount)) >>= fun transcript ↦
        distinguisher (compileTranscript selectors transcript)) =
        ((compileTranscript selectors <$>
          ($ᵗ (InputTranscript R levels sourceCount))) >>= distinguisher) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, compileTranscript_uniform_evalDist, ← evalDist_bind]

/-- Exact full-compiler reduction to the unequal two-block ordinary-LWE problem. -/
theorem advantage_eq_twoBlockLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) :
    advantage levels sourceCount secretSampler embed errorSampler selectors distinguisher =
      LearningWithErrors.advantage
        (LWE.TwoBlock.problem 1 (levels * sourceCount) (TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (reduction selectors distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold advantage ProbComp.boolDistAdvantage realGame
  rw [evalDist_ext_iff.mp
    (reduction_game1_evalDist_eq_uniformGame levels sourceCount secretSampler embed
      errorSampler selectors distinguisher) true]

/-- Exact full-compiler reduction to ordinary batch LWE. -/
theorem advantage_eq_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) :
    advantage levels sourceCount secretSampler embed errorSampler selectors distinguisher =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.embeddedBatchProblem 1
          (levels * sourceCount + TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (LWE.TwoBlock.reduction (reduction selectors distinguisher)) := by
  rw [advantage_eq_twoBlockLWE levels sourceCount secretSampler embed errorSampler
    selectors distinguisher]
  exact LWE.TwoBlock.advantage_eq_batch 1 (levels * sourceCount)
    (TGSW.rowCount 1 levels) secretSampler embed errorSampler
    (reduction selectors distinguisher)

/-- Exact information-theoretic gap between native fresh square rows and compiler-induced rows. -/
noncomputable def nativeDistributionGap {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Selectors R levels sourceCount) : ℝ :=
  tvDist
    (nativeSquareBatchSampler levels secretSampler embed errorSampler gadget)
    (compiledBatchSampler levels sourceCount secretSampler embed errorSampler selectors)

/-- Native stripped-square distinguishing game. -/
def nativeSquareGame {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) : ProbComp Bool :=
  nativeSquareBatchSampler levels secretSampler embed errorSampler gadget >>= distinguisher

/-- Native stripped-square real-versus-uniform advantage. -/
noncomputable def nativeSquareAdvantage {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) : ℝ :=
  (nativeSquareGame levels secretSampler embed errorSampler gadget
      distinguisher).boolDistAdvantage
    (uniformGame distinguisher)

/-- The real full-compiler game is postprocessing of the compiler-induced batch sampler. -/
theorem realGame_eq_compiledBatchSampler_bind
    {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) :
    realGame levels sourceCount secretSampler embed errorSampler selectors distinguisher =
      compiledBatchSampler levels sourceCount secretSampler embed errorSampler selectors >>=
        distinguisher := by
  simp [realGame, compiledBatchSampler, LearningWithErrors.game0, reduction,
    bind_assoc, monad_norm]

/-- Full native stripped-square security reduces to ordinary batch LWE plus the one explicit
native-versus-induced matrix-distribution gap. -/
theorem nativeSquareAdvantage_le_nativeDistributionGap_add_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) :
    nativeSquareAdvantage levels secretSampler embed errorSampler gadget distinguisher ≤
      nativeDistributionGap levels sourceCount secretSampler embed errorSampler gadget selectors +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction (reduction selectors distinguisher)) := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (nativeSquareGame levels secretSampler embed errorSampler gadget distinguisher)
    (realGame levels sourceCount secretSampler embed errorSampler selectors distinguisher)
    (uniformGame distinguisher)
  have hComparison :
      (nativeSquareGame levels secretSampler embed errorSampler gadget
          distinguisher).boolDistAdvantage
          (realGame levels sourceCount secretSampler embed errorSampler selectors
            distinguisher) ≤
        nativeDistributionGap levels sourceCount secretSampler embed errorSampler gadget
          selectors := by
    refine (abs_probOutput_toReal_sub_le_tvDist _ _).trans ?_
    rw [nativeSquareGame,
      realGame_eq_compiledBatchSampler_bind levels sourceCount secretSampler embed
        errorSampler selectors distinguisher]
    exact tvDist_bind_right_le distinguisher
      (nativeSquareBatchSampler levels secretSampler embed errorSampler gadget)
      (compiledBatchSampler levels sourceCount secretSampler embed errorSampler selectors)
  have hCompiler :
      advantage levels sourceCount secretSampler embed errorSampler selectors distinguisher =
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction (reduction selectors distinguisher)) :=
    advantage_eq_batchLWE levels sourceCount secretSampler embed errorSampler selectors
      distinguisher
  calc
    nativeSquareAdvantage levels secretSampler embed errorSampler gadget distinguisher ≤
        (nativeSquareGame levels secretSampler embed errorSampler gadget
          distinguisher).boolDistAdvantage
            (realGame levels sourceCount secretSampler embed errorSampler selectors
              distinguisher) +
          advantage levels sourceCount secretSampler embed errorSampler selectors
            distinguisher := by
      simpa only [nativeSquareAdvantage, advantage] using hTriangle
    _ ≤ nativeDistributionGap levels sourceCount secretSampler embed errorSampler gadget
          selectors +
        advantage levels sourceCount secretSampler embed errorSampler selectors
          distinguisher := add_le_add hComparison le_rfl
    _ = _ := congrArg
      (fun value ↦
        nativeDistributionGap levels sourceCount secretSampler embed errorSampler gadget
          selectors + value) hCompiler

end Full

end PreimageCompiler

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Checked small-noise cost of the approximation route.  For ring degree `N = degree + 1`,
the new residual `ordinaryError + S * eta` is bounded by
`ordinaryBound + N * secretBound * etaBound`. -/
theorem cInfNorm_squareApproximationResidual_le
    {q degree : ℕ} [NeZero q]
    (ordinaryError secret eta : RLWE.Rq q (degree + 1))
    (ordinaryBound secretBound etaBound : ℕ)
    (hOrdinary : LatticeCrypto.cInfNorm ordinaryError ≤ ordinaryBound)
    (hSecret : LatticeCrypto.cInfNorm secret ≤ secretBound)
    (hEta : LatticeCrypto.cInfNorm eta ≤ etaBound) :
    LatticeCrypto.cInfNorm (ordinaryError + secret * eta) ≤
      ordinaryBound + (degree + 1) * (secretBound * etaBound) := by
  exact (NoiseBounds.cInfNorm_add_le ordinaryError (secret * eta)).trans
    (Nat.add_le_add hOrdinary
      ((SharpRotationNoise.cInfNorm_mul_le_linear secret eta).trans
        (Nat.mul_le_mul_left (degree + 1) (Nat.mul_le_mul hSecret hEta))))

end

/-! ## Structured and direct samplers have the same square-only distribution -/

/-- Strip the linear block after sampling the native structured RGSW encryption of `-S`. -/
def encryptSquareView {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) : ProbComp (Ciphertext R 1 levels) :=
  stripLinearBlock gadget <$>
    TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0)

/-- The same square-only view starting from the fresh direct-RLWE-row presentation. -/
def directEncryptSquareView {R : Type} [CommRing R] [DecidableEq R]
    [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) : ProbComp (Ciphertext R 1 levels) :=
  stripLinearBlock gadget <$>
    TGSW.directEncrypt 1 levels errorSampler secret gadget (-secret 0)

/-- Native structured `RGSW_S(-S)` and fresh direct rows give exactly the same stripped
ring-square distribution. -/
theorem encryptSquareView_evalDist_eq_direct
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) :
    evalDist (encryptSquareView levels errorSampler secret gadget) =
      evalDist (directEncryptSquareView levels errorSampler secret gadget) := by
  exact evalDist_map_eq_of_evalDist_eq
    (TGSW.encrypt_evalDist_eq_directEncrypt
      1 levels errorSampler secret gadget (-secret 0))
    (stripLinearBlock gadget)

/-- Uniform ciphertexts remain uniform after stripping the linear block. -/
theorem strip_uniform_evalDist {R : Type} [Fintype R] [SampleableType R]
    [AddCommGroup R] {levels : ℕ} (gadget : Fin levels → R) :
    evalDist
        (stripLinearBlock gadget <$>
          ($ᵗ (Ciphertext R 1 levels))) =
      evalDist ($ᵗ (Ciphertext R 1 levels)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Ciphertext R 1 levels) (β := Ciphertext R 1 levels)
    (stripLinearBlock gadget) (stripLinearBlock_bijective gadget)

/-- Uniform ciphertexts also remain uniform under the inverse restoration map. -/
theorem restore_uniform_evalDist {R : Type} [Fintype R] [SampleableType R]
    [AddCommGroup R] {levels : ℕ} (gadget : Fin levels → R) :
    evalDist
        (restoreLinearBlock gadget <$>
          ($ᵗ (Ciphertext R 1 levels))) =
      evalDist ($ᵗ (Ciphertext R 1 levels)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Ciphertext R 1 levels) (β := Ciphertext R 1 levels)
    (restoreLinearBlock gadget) (restoreLinearBlock_bijective gadget)

/-! ## Direct connection of the full compiler to actual `RGSW_S(-S)` -/

namespace PreimageCompiler.Full

/-- The exact stripped distribution obtained from a genuine native `RGSW_S(-S)` sampler. -/
def actualSquareBatchSampler {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) : ProbComp (TargetBatch R levels) := do
  let secretValue ← secretSampler
  encryptSquareView levels errorSampler (embed secretValue) gadget

/-- Exact gap between the actual stripped `RGSW_S(-S)` law and the full compiler-induced law. -/
noncomputable def actualDistributionGap {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Selectors R levels sourceCount) : ℝ :=
  tvDist
    (actualSquareBatchSampler levels secretSampler embed errorSampler gadget)
    (compiledBatchSampler levels sourceCount secretSampler embed errorSampler selectors)

/-- Actual stripped-square distinguishing game. -/
def actualSquareGame {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) : ProbComp Bool :=
  actualSquareBatchSampler levels secretSampler embed errorSampler gadget >>= distinguisher

/-- Actual stripped-square real-versus-uniform advantage. -/
noncomputable def actualSquareAdvantage {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) : ℝ :=
  (actualSquareGame levels secretSampler embed errorSampler gadget
      distinguisher).boolDistAdvantage
    (uniformGame distinguisher)

/-- Security of the exact stripped native distribution reduces to ordinary batch LWE plus its
literal distance from the compiler-induced distribution. -/
theorem actualSquareAdvantage_le_actualDistributionGap_add_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) :
    actualSquareAdvantage levels secretSampler embed errorSampler gadget distinguisher ≤
      actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget selectors +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction (reduction selectors distinguisher)) := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (actualSquareGame levels secretSampler embed errorSampler gadget distinguisher)
    (realGame levels sourceCount secretSampler embed errorSampler selectors distinguisher)
    (uniformGame distinguisher)
  have hComparison :
      (actualSquareGame levels secretSampler embed errorSampler gadget
          distinguisher).boolDistAdvantage
          (realGame levels sourceCount secretSampler embed errorSampler selectors
            distinguisher) ≤
        actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget
          selectors := by
    refine (abs_probOutput_toReal_sub_le_tvDist _ _).trans ?_
    rw [actualSquareGame,
      realGame_eq_compiledBatchSampler_bind levels sourceCount secretSampler embed
        errorSampler selectors distinguisher]
    exact tvDist_bind_right_le distinguisher
      (actualSquareBatchSampler levels secretSampler embed errorSampler gadget)
      (compiledBatchSampler levels sourceCount secretSampler embed errorSampler selectors)
  have hCompiler := advantage_eq_batchLWE levels sourceCount secretSampler embed errorSampler
    selectors distinguisher
  calc
    actualSquareAdvantage levels secretSampler embed errorSampler gadget distinguisher ≤
        (actualSquareGame levels secretSampler embed errorSampler gadget
          distinguisher).boolDistAdvantage
            (realGame levels sourceCount secretSampler embed errorSampler selectors
              distinguisher) +
          advantage levels sourceCount secretSampler embed errorSampler selectors
            distinguisher := by
      simpa only [actualSquareAdvantage, advantage] using hTriangle
    _ ≤ actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget
          selectors +
        advantage levels sourceCount secretSampler embed errorSampler selectors
          distinguisher := add_le_add hComparison le_rfl
    _ = _ := congrArg
      (fun value ↦
        actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget
          selectors + value) hCompiler

/-- Restore a distinguisher on the original RGSW layout from the stripped square layout. -/
def restoreDistinguisher {R : Type} [Add R] {levels : ℕ}
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) :
    Distinguisher R levels :=
  fun squareView ↦ distinguisher (restoreLinearBlock gadget squareView)

/-- Exact genuine `RGSW_S(-S)` sampler before public stripping. -/
def rgswMinusSecretSampler {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) : ProbComp (TargetBatch R levels) := do
  let secretValue ← secretSampler
  let secret := embed secretValue
  TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0)

/-- Genuine unstripped `RGSW_S(-S)` distinguishing game. -/
def rgswMinusSecretGame {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) : ProbComp Bool :=
  rgswMinusSecretSampler levels secretSampler embed errorSampler gadget >>= distinguisher

/-- Genuine unstripped `RGSW_S(-S)` real-versus-uniform advantage. -/
noncomputable def rgswMinusSecretAdvantage {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) : ℝ :=
  (rgswMinusSecretGame levels secretSampler embed errorSampler gadget
      distinguisher).boolDistAdvantage
    (uniformGame distinguisher)

/-- Restoring the exact stripped real game recovers the original RGSW real game pointwise. -/
theorem actualSquareGame_restoreDistinguisher_eq_rgswMinusSecretGame
    {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) :
    actualSquareGame levels secretSampler embed errorSampler gadget
        (restoreDistinguisher gadget distinguisher) =
      rgswMinusSecretGame levels secretSampler embed errorSampler gadget distinguisher := by
  simp [actualSquareGame, actualSquareBatchSampler, encryptSquareView,
    restoreDistinguisher, rgswMinusSecretGame, rgswMinusSecretSampler,
    bind_assoc, monad_norm]

/-- Restoring a uniform stripped challenge preserves its full output distribution. -/
theorem uniformGame_restoreDistinguisher_evalDist_eq
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) :
    evalDist (uniformGame (restoreDistinguisher gadget distinguisher)) =
      evalDist (uniformGame distinguisher) := by
  unfold uniformGame restoreDistinguisher
  rw [show
      (($ᵗ (TargetBatch R levels)) >>= fun target ↦
        distinguisher (restoreLinearBlock gadget target)) =
        ((restoreLinearBlock gadget <$> ($ᵗ (TargetBatch R levels))) >>=
          distinguisher) by simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, restore_uniform_evalDist, ← evalDist_bind]

/-- Public strip/restore gives an exact lossless equivalence between genuine unstripped
`RGSW_S(-S)` security and the actual square-view game. -/
theorem rgswMinusSecretAdvantage_eq_actualSquareAdvantage_restore
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : Distinguisher R levels) :
    rgswMinusSecretAdvantage levels secretSampler embed errorSampler gadget distinguisher =
      actualSquareAdvantage levels secretSampler embed errorSampler gadget
        (restoreDistinguisher gadget distinguisher) := by
  unfold rgswMinusSecretAdvantage actualSquareAdvantage ProbComp.boolDistAdvantage
  rw [actualSquareGame_restoreDistinguisher_eq_rgswMinusSecretGame,
    evalDist_ext_iff.mp
      (uniformGame_restoreDistinguisher_evalDist_eq gadget distinguisher) true]

/-- **Full standalone theorem for genuine `RGSW_S(-S)`.**  Its advantage is at most ordinary
batch RLWE plus the explicit distance between the actual narrow-error square view and the
short-preimage compiler distribution. -/
theorem rgswMinusSecretAdvantage_le_actualDistributionGap_add_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) :
    rgswMinusSecretAdvantage levels secretSampler embed errorSampler gadget distinguisher ≤
      actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget selectors +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction
            (reduction selectors (restoreDistinguisher gadget distinguisher))) := by
  rw [rgswMinusSecretAdvantage_eq_actualSquareAdvantage_restore]
  exact actualSquareAdvantage_le_actualDistributionGap_add_batchLWE
    levels sourceCount secretSampler embed errorSampler gadget selectors
    (restoreDistinguisher gadget distinguisher)

/-- Clean conditional security statement for the remaining research task.  A bound `ε` on the
actual narrow-error compiler gap and a bound `δ` on the induced ordinary batch-RLWE adversary
give an `ε + δ` bound for genuine `RGSW_S(-S)`. -/
theorem rgswMinusSecretAdvantage_le_of_gap_of_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Selectors R levels sourceCount)
    (distinguisher : Distinguisher R levels) (ε δ : ℝ)
    (hGap :
      actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget
        selectors ≤ ε)
    (hBatchLWE :
      LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction
            (reduction selectors (restoreDistinguisher gadget distinguisher))) ≤ δ) :
    rgswMinusSecretAdvantage levels secretSampler embed errorSampler gadget distinguisher ≤
      ε + δ := by
  exact
    (rgswMinusSecretAdvantage_le_actualDistributionGap_add_batchLWE
      levels sourceCount secretSampler embed errorSampler gadget selectors distinguisher).trans
      (add_le_add hGap hBatchLWE)

end PreimageCompiler.Full

end FormalProof4FHE.TFHE.TGSW.RingSquare

namespace FormalProof4FHE.TFHE.Native.RingSquareRGSW

noncomputable section

open TGSW.RingSquare

/- The executable negacyclic carrier exposes direct `Add`/`Sub` instances as well as the
operations inherited through its bundled commutative ring.  These wrappers deliberately select
one coherent bundled dictionary, so the public stripping permutation has a definitional inverse
in the native security games. -/

noncomputable def nativeStripLinearBlock
    {q degree levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
    (ciphertext : TGSW.Ciphertext (RLWE.Rq q degree) 1 levels) :
    TGSW.Ciphertext (RLWE.Rq q degree) 1 levels :=
  @stripLinearBlock (RLWE.Rq q degree)
    ((LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAddGroup.toSub)
    levels gadget ciphertext

noncomputable def nativeRestoreLinearBlock
    {q degree levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
    (ciphertext : TGSW.Ciphertext (RLWE.Rq q degree) 1 levels) :
    TGSW.Ciphertext (RLWE.Rq q degree) 1 levels :=
  @restoreLinearBlock (RLWE.Rq q degree)
    ((LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAddGroup.toAdd)
    levels gadget ciphertext

@[simp]
theorem nativeRestore_strip
    {q degree levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
    (ciphertext : TGSW.Ciphertext (RLWE.Rq q degree) 1 levels) :
    nativeRestoreLinearBlock gadget (nativeStripLinearBlock gadget ciphertext) = ciphertext := by
  exact @TGSW.RingSquare.restore_strip (RLWE.Rq q degree)
    (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAddGroup
    levels gadget ciphertext

@[simp]
theorem nativeStrip_restore
    {q degree levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
    (ciphertext : TGSW.Ciphertext (RLWE.Rq q degree) 1 levels) :
    nativeStripLinearBlock gadget (nativeRestoreLinearBlock gadget ciphertext) = ciphertext := by
  exact @TGSW.RingSquare.strip_restore (RLWE.Rq q degree)
    (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAddGroup
    levels gadget ciphertext

/-- The native stripping operation is a public permutation. -/
theorem nativeStrip_bijective
    {q degree levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree) :
    Function.Bijective
      (nativeStripLinearBlock gadget :
        TGSW.Ciphertext (RLWE.Rq q degree) 1 levels → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨nativeRestoreLinearBlock gadget, nativeRestore_strip gadget,
      nativeStrip_restore gadget⟩

/-- The native restoration operation is the inverse public permutation. -/
theorem nativeRestore_bijective
    {q degree levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree) :
    Function.Bijective
      (nativeRestoreLinearBlock gadget :
        TGSW.Ciphertext (RLWE.Rq q degree) 1 levels → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨nativeStripLinearBlock gadget, nativeStrip_restore gadget,
      nativeRestore_strip gadget⟩

/-- A standalone rank-one RGSW circular-security challenge. -/
abbrev Challenge (q degree levels : ℕ) := RingGSWCiphertext q degree 1 levels

/-- A public distinguisher for the standalone RGSW challenge. -/
abbrev Distinguisher (q degree levels : ℕ) :=
  Challenge q degree levels → ProbComp Bool

/-- Native stripping preserves the uniform standalone challenge distribution. -/
theorem nativeStrip_uniform_evalDist
    {q degree levels : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q degree) :
    evalDist
        (nativeStripLinearBlock gadget <$> ($ᵗ (Challenge q degree levels))) =
      evalDist ($ᵗ (Challenge q degree levels)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Challenge q degree levels) (β := Challenge q degree levels)
    (nativeStripLinearBlock gadget) (nativeStrip_bijective gadget)

/-- Native restoration preserves the uniform standalone challenge distribution. -/
theorem nativeRestore_uniform_evalDist
    {q degree levels : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q degree) :
    evalDist
        (nativeRestoreLinearBlock gadget <$> ($ᵗ (Challenge q degree levels))) =
      evalDist ($ᵗ (Challenge q degree levels)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Challenge q degree levels) (β := Challenge q degree levels)
    (nativeRestoreLinearBlock gadget) (nativeRestore_bijective gadget)

/-- Honest `RGSW_S(-S)` experiment for a uniformly sampled binary ring secret. -/
def realGame
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) : ProbComp Bool := do
  let binarySecret ← Native.sampleRingSecret 1 degree
  let secret := embedRingSecret q binarySecret
  let ciphertext ← TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0)
  distinguisher ciphertext

/-- Format-identical zero-message RGSW experiment under the same binary ring-secret law. -/
def zeroGame
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) : ProbComp Bool := do
  let binarySecret ← Native.sampleRingSecret 1 degree
  let ciphertext ← TGSW.encryptZero 1 levels errorSampler
    (embedRingSecret q binarySecret) gadget
  distinguisher ciphertext

/-- Uniform endpoint for standalone circular-RLWE pseudorandomness. -/
def uniformGame
    (q degree levels : ℕ) [NeZero q]
    (distinguisher : Distinguisher q degree levels) : ProbComp Bool := do
  let ciphertext ← $ᵗ (Challenge q degree levels)
  distinguisher ciphertext

/-- Exact ring-square normal-form experiment obtained by the public stripping map. -/
def squareGame
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) : ProbComp Bool := do
  let binarySecret ← Native.sampleRingSecret 1 degree
  let secret := embedRingSecret q binarySecret
  let ciphertext ← TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0)
  distinguisher (nativeStripLinearBlock gadget ciphertext)

/-- Compile a distinguisher on ordinary RGSW ciphertexts into one on the square-only normal
form. -/
def restoreDistinguisher
    {q degree levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
  (distinguisher : Distinguisher q degree levels) :
    Distinguisher q degree levels :=
  fun ciphertext ↦ distinguisher (nativeRestoreLinearBlock gadget ciphertext)

/-- Compile a square-normal-form distinguisher back into one on ordinary RGSW ciphertexts. -/
def stripDistinguisher
    {q degree levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
  (distinguisher : Distinguisher q degree levels) :
    Distinguisher q degree levels :=
  fun ciphertext ↦ distinguisher (nativeStripLinearBlock gadget ciphertext)

/-- The honest RGSW game is exactly the square-only game followed by public restoration. -/
theorem squareGame_restore_eq_realGame
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) :
    squareGame q degree levels errorSampler gadget
        (restoreDistinguisher gadget distinguisher) =
      realGame q degree levels errorSampler gadget distinguisher := by
  unfold squareGame realGame restoreDistinguisher
  apply bind_congr
  intro binarySecret
  apply bind_congr
  intro ciphertext
  rw [nativeRestore_strip]

/-- Conversely, stripping inside the honest game gives exactly the square normal form. -/
theorem realGame_strip_eq_squareGame
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) :
    realGame q degree levels errorSampler gadget
        (stripDistinguisher gadget distinguisher) =
      squareGame q degree levels errorSampler gadget distinguisher := by
  rfl

/-- Restoring a uniformly sampled normal-form challenge before running a distinguisher does not
change its output distribution. -/
theorem uniformGame_restore_evalDist_eq
    (q degree levels : ℕ) [NeZero q]
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) :
    evalDist
        (uniformGame q degree levels
          (restoreDistinguisher gadget distinguisher)) =
      evalDist (uniformGame q degree levels distinguisher) := by
  have huniform := nativeRestore_uniform_evalDist gadget
  have hbind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    huniform distinguisher
  simpa only [uniformGame, restoreDistinguisher, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind] using hbind

/-- Stripping a uniformly sampled ordinary challenge before running a normal-form distinguisher
also leaves its output distribution unchanged. -/
theorem uniformGame_strip_evalDist_eq
    (q degree levels : ℕ) [NeZero q]
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) :
    evalDist
        (uniformGame q degree levels
          (stripDistinguisher gadget distinguisher)) =
      evalDist (uniformGame q degree levels distinguisher) := by
  have huniform := nativeStrip_uniform_evalDist gadget
  have hbind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    huniform distinguisher
  simpa only [uniformGame, stripDistinguisher, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind] using hbind

/-- Real-versus-zero security of the standalone circular RGSW ciphertext. -/
def kdmAdvantage
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) : ℝ :=
  (realGame q degree levels errorSampler gadget distinguisher).boolDistAdvantage
    (zeroGame q degree levels errorSampler gadget distinguisher)

/-- Real-versus-uniform ring-square circular-RLWE advantage. -/
def circularLweAdvantage
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) : ℝ :=
  (realGame q degree levels errorSampler gadget distinguisher).boolDistAdvantage
    (uniformGame q degree levels distinguisher)

/-- Ring-square normal-form distinguishing advantage. -/
def squareAdvantage
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) : ℝ :=
  (squareGame q degree levels errorSampler gadget distinguisher).boolDistAdvantage
    (uniformGame q degree levels distinguisher)

/-- Exact standalone security equivalence in the forward direction: an ordinary RGSW
distinguisher has precisely the same advantage against the square normal form after public
restoration. -/
theorem circularLweAdvantage_eq_squareAdvantage_restore
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) :
    circularLweAdvantage q degree levels errorSampler gadget distinguisher =
      squareAdvantage q degree levels errorSampler gadget
        (restoreDistinguisher gadget distinguisher) := by
  unfold circularLweAdvantage squareAdvantage ProbComp.boolDistAdvantage
  rw [squareGame_restore_eq_realGame]
  rw [probOutput_congr rfl
    (uniformGame_restore_evalDist_eq q degree levels gadget distinguisher)]

/-- Exact converse: every square-normal-form distinguisher has precisely the same advantage
after public stripping of the original `RGSW_S(-S)` challenge. -/
theorem squareAdvantage_eq_circularLweAdvantage_strip
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) :
    squareAdvantage q degree levels errorSampler gadget distinguisher =
      circularLweAdvantage q degree levels errorSampler gadget
        (stripDistinguisher gadget distinguisher) := by
  unfold circularLweAdvantage squareAdvantage ProbComp.boolDistAdvantage
  rw [realGame_strip_eq_squareGame]
  rw [probOutput_congr rfl
    (uniformGame_strip_evalDist_eq q degree levels gadget distinguisher)]

/-- Zero-message RGSW versus uniform advantage, the ordinary RLWE term needed to convert the
real-versus-uniform formulation into real-versus-zero KDM security. -/
def zeroLweAdvantage
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) : ℝ :=
  (zeroGame q degree levels errorSampler gadget distinguisher).boolDistAdvantage
    (uniformGame q degree levels distinguisher)

/-- The standalone KDM goal is bounded by the ring-square goal plus the ordinary zero-message
RGSW/RLWE term. -/
theorem kdmAdvantage_le_circularLwe_add_zeroLwe
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree levels) :
    kdmAdvantage q degree levels errorSampler gadget distinguisher ≤
      circularLweAdvantage q degree levels errorSampler gadget distinguisher +
        zeroLweAdvantage q degree levels errorSampler gadget distinguisher := by
  have h := ProbComp.boolDistAdvantage_triangle
    (realGame q degree levels errorSampler gadget distinguisher)
    (uniformGame q degree levels distinguisher)
    (zeroGame q degree levels errorSampler gadget distinguisher)
  unfold kdmAdvantage circularLweAdvantage zeroLweAdvantage
  rw [show (uniformGame q degree levels distinguisher).boolDistAdvantage
      (zeroGame q degree levels errorSampler gadget distinguisher) =
      (zeroGame q degree levels errorSampler gadget distinguisher).boolDistAdvantage
        (uniformGame q degree levels distinguisher) by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]] at h
  exact h

/-! ## The precise standalone hardness statements -/

/-- Concrete standalone KDM security against a selected efficient-distinguisher class. -/
def KDMHardAgainst
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (allowed : Distinguisher q degree levels → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    kdmAdvantage q degree levels errorSampler gadget distinguisher ≤ bound

/-- Concrete real-versus-uniform circular-RLWE security of `RGSW_S(-S)`. -/
def CircularLWEHardAgainst
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (allowed : Distinguisher q degree levels → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    circularLweAdvantage q degree levels errorSampler gadget distinguisher ≤ bound

/-- Concrete hardness of the exact ring-square normal form. -/
def SquareHardAgainst
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (allowed : Distinguisher q degree levels → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    squareAdvantage q degree levels errorSampler gadget distinguisher ≤ bound

/-- Square-normal-form hardness implies standalone `RGSW_S(-S)` circular hardness with exactly
the same bound, provided the selected efficiency class is closed under public restoration. -/
theorem circularLWEHardAgainst_of_square
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (circularAllowed squareAllowed : Distinguisher q degree levels → Prop)
    (bound : ℝ)
    (hClosed : ∀ distinguisher, circularAllowed distinguisher →
      squareAllowed (restoreDistinguisher gadget distinguisher))
    (hSquare : SquareHardAgainst q degree levels errorSampler gadget
      squareAllowed bound) :
    CircularLWEHardAgainst q degree levels errorSampler gadget
      circularAllowed bound := by
  intro distinguisher hAllowed
  rw [circularLweAdvantage_eq_squareAdvantage_restore]
  exact hSquare _ (hClosed distinguisher hAllowed)

/-- Conversely, standalone circular hardness implies square-normal-form hardness with the same
bound when the efficiency class is closed under public stripping. -/
theorem squareHardAgainst_of_circularLWE
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (squareAllowed circularAllowed : Distinguisher q degree levels → Prop)
    (bound : ℝ)
    (hClosed : ∀ distinguisher, squareAllowed distinguisher →
      circularAllowed (stripDistinguisher gadget distinguisher))
    (hCircular : CircularLWEHardAgainst q degree levels errorSampler gadget
      circularAllowed bound) :
    SquareHardAgainst q degree levels errorSampler gadget squareAllowed bound := by
  intro distinguisher hAllowed
  rw [squareAdvantage_eq_circularLweAdvantage_strip]
  exact hCircular _ (hClosed distinguisher hAllowed)

/-- The final standalone KDM theorem schema: prove the square normal form and the ordinary
zero-message RGSW term, then add their concrete bounds. -/
theorem kdmHardAgainst_of_circularLWE_and_zeroLWE
    (q degree levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (allowed : Distinguisher q degree levels → Prop)
    (circularBound zeroBound : ℝ)
    (hCircular : CircularLWEHardAgainst q degree levels errorSampler gadget
      allowed circularBound)
    (hZero : ∀ distinguisher, allowed distinguisher →
      zeroLweAdvantage q degree levels errorSampler gadget distinguisher ≤ zeroBound) :
    KDMHardAgainst q degree levels errorSampler gadget allowed
      (circularBound + zeroBound) := by
  intro distinguisher hAllowed
  exact (kdmAdvantage_le_circularLwe_add_zeroLwe
    q degree levels errorSampler gadget distinguisher).trans
      (add_le_add
        (hCircular distinguisher hAllowed)
        (hZero distinguisher hAllowed))

end

end FormalProof4FHE.TFHE.Native.RingSquareRGSW
