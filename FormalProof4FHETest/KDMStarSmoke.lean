/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.KDMStarGSW

/-! Executable diagnostics for the new law, with dense masks, nonbinary u,
and signed nonzero errors. Tiny parameters have no security claim. This tests
public encryption and same-format NAND, not full decryption-key bootstrapping. -/

namespace FormalProof4FHETest.KDMStarSmoke

open Matrix FormalProof4FHE.LWE
open KDMStarGSW

private def params : Parameters 4096 where
  base := 2
  levels := 12
  one_lt_base := by decide
  modulus_le_capacity := by decide

private def secret : Fin 2 → ZMod 4096 := ![173, 2981]
private def count := 2 + rows 2 * params.levels

private def mask : Matrix (Fin 2) (Fin count) (ZMod 4096) :=
  fun row column ↦ 23 * row.val + 29 * column.val + 7

private def error : Fin count → ZMod 4096 :=
  fun column ↦ if column.val % 2 = 0 then 1 else -1

private def extra : Extra (ZMod 4096) 2 count :=
  (fun column ↦ 11 * column.val + 5,
    fun row column ↦ 17 * row.val + 31 * column.val + 9)

private def selectors : Matrix (Fin 2) (Fin (rows 2 * params.levels)) (ZMod 4096) :=
  fun sample column ↦ if (sample.val + column.val) % 2 = 0 then 1 else 0

private def decode (bit : Bool) (ciphertext : GSWGadget.Ciphertext params (rows 2)) : Bool :=
  FormalProof4FHE.TFHE.BootstrappingCorrectness.decodeNearest 0
    (FormalProof4FHE.TFHE.Gadget.Base.gadget params ⟨11, by decide⟩)
    (vecMul (key bit secret) ciphertext
      (finProdFinEquiv (featureEquiv 2 none, ⟨11, by decide⟩)))

private def testCase (anchorBit messageBit : Bool) : Bool :=
  let sampled := fresh (joinedPlan params 2) anchorBit secret mask error extra
  let rawView := maskingViewEquiv params 2 sampled
  let stored := storeView params rawView
  let view := readStoredView params stored
  let table : Matrix (Fin (rows 2)) (Fin 2) (ZMod 4096) :=
    fun row sample ↦ view.1 sample row
  let encrypted := encryptInputs params table (GSWGadget.bitMessage messageBit) selectors
  let output := GSWGadget.nand params view.2 encrypted
  let controlErrors := GSWOperations.noise (key anchorBit secret)
    (GSWGadget.gadget params (rows 2)) view.2 (anchor anchorBit)
  let controlNoiseOK := (List.finRange (rows 2 * params.levels)).all
    (fun column ↦ controlErrors column == error (finSumFinEquiv (.inr column)))
  controlNoiseOK && (decode anchorBit encrypted == messageBit) &&
    (decode anchorBit output == !(anchorBit && messageBit))

/-- info: true -/
#guard_msgs in
#eval [(false, false), (false, true), (true, false), (true, true)].all
  (fun bits ↦ testCase bits.1 bits.2)

end FormalProof4FHETest.KDMStarSmoke
