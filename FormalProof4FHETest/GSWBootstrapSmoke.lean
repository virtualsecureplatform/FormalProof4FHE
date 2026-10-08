/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWBootstrapParameters

/-! Small executable correctness diagnostics, with no security claim. Exercise public
scaled reduction and two successive NAND/refresh operations with one unchanged secret,
dense masks, and nonzero signed errors. Use concrete stored outputs between operations. -/

namespace FormalProof4FHETest.GSWBootstrapSmoke

open FormalProof4FHE.LWE
open GSWGadget GSWAccumulator GSWBootstrap

private def params : Parameters (16384 * 16) where
  base := 2
  levels := 18
  one_lt_base := by decide
  modulus_le_capacity := by decide

private def level : Fin params.levels := ⟨17, by decide⟩

private def challenge (offset : ℕ) : Matrix (Fin 1) (Fin (2 * params.levels)) (ZMod (16384 * 16)) :=
  fun row column ↦ offset + 17 * row.val + 29 * column.val + 5

private def error (column : Fin (2 * params.levels)) : ZMod (16384 * 16) :=
  if column.val % 2 = 0 then 1 else -1

private def fresh (secret : Fin 1 → ZMod (16384 * 16)) (bit : Bool) (offset : ℕ) :
    Ciphertext params 2 :=
  GSWOperations.ciphertextMatrix
    (GSWSelfKey.freshTranscript (layout params 1) secret (fun _ ↦ bitMessage bit)
      (challenge offset) error)

/-- Both diagnostic margins hold for the advertised post-NAND noise bound. -/
example :
    2 * ((growth params 2 + 1) * (16 * 1 * growth params 2 * 1) + 2 * (16384 - 1)) <
      16384 * FormalProof4FHE.TFHE.BootstrappingCorrectness.centeredDistance (0 : ZMod 16) 8 ∧
    2 * (16 * 1 * growth params 2 * 1) <
      FormalProof4FHE.TFHE.BootstrappingCorrectness.centeredDistance
        0 (FormalProof4FHE.TFHE.Gadget.Base.gadget params level) := by
  decide

private def testCase (secretBit firstBit secondBit : Bool) : Bool :=
  let bits : Fin 1 → Bool := fun _ ↦ secretBit
  let secret := GSWSelfKey.binaryEmbed (R := ZMod (16384 * 16)) bits
  let controlData := storeCiphertext params (fresh secret secretBit 31)
  let controls : Fin 1 → Ciphertext params 2 := fun _ ↦ ciphertextView params controlData
  let firstData := storeCiphertext params (fresh secret firstBit 47)
  let secondData := storeCiphertext params (fresh secret secondBit 71)
  let first := ciphertextView params firstData
  let second := ciphertextView params secondData
  let refreshedData := bootstrapStored params controls (nand params first second) level (8 : ZMod 16)
  let refreshed := ciphertextView params refreshedData
  let nextData := bootstrapStored params controls (nand params refreshed first) level (8 : ZMod 16)
  let next := ciphertextView params nextData
  let expected := !(firstBit && secondBit)
  (decrypt params secret refreshed level == expected) &&
    (decrypt params secret next level == !(expected && firstBit))

/-- info: true -/
#guard_msgs in
#eval [false, true].all (fun secretBit ↦
  [false, true].all (fun firstBit ↦
    [false, true].all (testCase secretBit firstBit)))

end FormalProof4FHETest.GSWBootstrapSmoke
