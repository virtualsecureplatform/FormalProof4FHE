/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWLinkedDisclosure

/-! Exercise the actual stored public-link transcript and challenge attack.
Small dimensions and fixed coins are correctness diagnostics, with no security claim.
The attacker gets P,Z, a fresh stored challenge, and its own receiver key;
no sender secret, subset bits or encryption coins are attack inputs. -/

namespace FormalProof4FHETest.GSWDisclosureSmoke

open FormalProof4FHE.LWE
open GSWGadget GSWPublicKey GSWLinkedDisclosure GSWAccumulator

private def params : Parameters 4096 where
  base := 2
  levels := 12
  one_lt_base := by decide
  modulus_le_capacity := by decide

private def seed : Matrix (Fin 2) (Fin 2) (ZMod 4096) :=
  fun row pad ↦ if (row.val + pad.val) % 2 = 0 then
    31 + 13 * row.val + 17 * pad.val else -(19 + 11 * row.val + 23 * pad.val)

private def pads : Fin 2 → Columns 2 params.levels → Bool :=
  fun pad column ↦ decide ((pad.val + column.1.val + 2 * column.2.1.val +
    3 * column.2.2.val) % 3 = 0)

private def coins : Fin 2 → Columns 2 params.levels → SelectorCoins 2 (2 * params.levels) :=
  fun pad column ↦ Vector.ofFn fun sample ↦ Vector.ofFn fun gadgetColumn ↦
    decide ((pad.val + column.1.val + column.2.1.val + column.2.2.val + sample.val +
      2 * gadgetColumn.val) % 5 < 2)

private def challengeCoins : SelectorCoins 2 (2 * params.levels) :=
  Vector.ofFn fun sample ↦ Vector.ofFn fun column ↦ decide ((sample.val + column.val) % 3 = 0)

private def runCase (senderValue receiverValue : ZMod 4096) : Bool :=
  let sender : Fin 1 → ZMod 4096 := ![senderValue]
  let receiver : Fin 1 → ZMod 4096 := ![receiverValue]
  let senderPublic := freshPublicKey sender ![![137, -93]] ![1, -1]
  let receiverPublic := freshPublicKey receiver ![![101, -57]] ![1, -1]
  let encryptedData : Vector (Vector (StoredCiphertext params 2) (2 * (2 * params.levels))) 2 :=
    Vector.ofFn fun pad ↦ Vector.ofFn fun index ↦
      let column := (columnEquiv 2 params.levels).symm index
      encryptStored params receiverPublic (coins pad column) (pads pad column)
  let encryptedPads := fun pad column ↦ ciphertextView params
    ((encryptedData.get pad).get (columnEquiv 2 params.levels column))
  let publicHint := storeHint params
    (subsetMask params seed pads + tensorHint params (GSWOperations.extendedSecret sender))
  let publicLink := storeHint params (sourceLink params seed encryptedPads)
  let recovered := recoverStoredSender params (GSWOperations.extendedSecret receiver) 0 publicHint publicLink
  let keyRecovered := (List.finRange 2).all fun row ↦
    recovered.get row == GSWOperations.extendedSecret sender row
  keyRecovered && [false, true].all fun message ↦
    let challenge := encryptStored params senderPublic challengeCoins message
    decodeStoredChallenge params (GSWOperations.extendedSecret receiver) 0 publicHint publicLink
      challenge ⟨11, by decide⟩ == message

/-- Both public-pad and fresh-challenge margins fit this diagnostic modulus. -/
example : 4 * (2 * growth params 2 * (2 * 1)) < 4096 ∧
    2 * (2 * 1) < FormalProof4FHE.TFHE.BootstrappingCorrectness.centeredDistance
      0 (FormalProof4FHE.TFHE.Gadget.Base.gadget params ⟨11, by decide⟩) := by
  decide

/-- info: true -/
#guard_msgs in
#eval runCase 5 7 && runCase (-13) (-11)

end FormalProof4FHETest.GSWDisclosureSmoke
