/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWAccumulator
import FormalProof4FHE.LWE.GSWLinkedMask

/-! Executable correctness diagnostics only. These tiny dimensions have no security claim.
The control ciphertexts use dense public masks and nonzero errors of both signs. -/

namespace FormalProof4FHETest.GSWAccumulatorSmoke

open FormalProof4FHE.LWE
open GSWGadget GSWAccumulator

private def params : Parameters 4096 where
  base := 2
  levels := 12
  one_lt_base := by decide
  modulus_le_capacity := by decide

private def challenges (index : Fin 2) :
    Matrix (Fin 2) (Fin (3 * params.levels)) (ZMod 4096) :=
  fun row column ↦ 17 * index.val + 23 * row.val + 29 * column.val + 5

private def errors (index : Fin 2) (column : Fin (3 * params.levels)) : ZMod 4096 :=
  if (index.val + column.val) % 2 = 0 then 1 else -1

private def testCase (first second : Bool) (body : ZMod 5) : Bool :=
  let bits : Fin 2 → Bool := ![first, second]
  let weights : Fin 2 → ZMod 5 := ![1, 2]
  let function := fun value : ZMod 5 ↦ decide (value.val = 1 ∨ value.val = 3)
  let controls := freshBootKey params bits challenges errors
  let outputData := refreshStored params controls weights body function
  let output := ciphertextView params outputData
  let actual := decrypt params (GSWSelfKey.binaryEmbed bits) output ⟨11, by decide⟩
  let expected := function (body - dotProduct (GSWSelfKey.binaryEmbed bits) weights)
  actual == expected

/-- The diagnostic's output margin satisfies the proved bound with unit errors. -/
example : 2 * (5 * 2 * growth params 3 * 1) <
    FormalProof4FHE.TFHE.BootstrappingCorrectness.centeredDistance
      0 (FormalProof4FHE.TFHE.Gadget.Base.gadget params ⟨11, by decide⟩) := by
  decide

/-- info: true -/
#guard_msgs in
#eval [(false, false), (false, true), (true, false), (true, true)].all
  (fun bits ↦ ([0, 1, 4] : List (ZMod 5)).all (testCase bits.1 bits.2))

private def nandCase (first second : Bool) : Bool :=
  let bits : Fin 2 → Bool := ![first, second]
  let controls := freshBootKey params bits challenges errors
  let actual := decrypt params (GSWSelfKey.binaryEmbed bits)
    (nand params (controls 0) (controls 1)) ⟨11, by decide⟩
  actual == !(first && second)

/-- info: true -/
#guard_msgs in
#eval [(false, false), (false, true), (true, false), (true, true)].all
  (fun bits ↦ nandCase bits.1 bits.2)

end FormalProof4FHETest.GSWAccumulatorSmoke

/-! Public linked controls are exercised separately from direct private controls.
The two-sample public key is only a correctness diagnostic, with no security claim. -/
namespace FormalProof4FHETest.GSWLinkedMaskSmoke

open FormalProof4FHE.LWE
open GSWGadget GSWAccumulator GSWPublicKey GSWLinkedMask

private def params : Parameters 16777216 where
  base := 2
  levels := 24
  one_lt_base := by decide
  modulus_le_capacity := by decide

private def seed : Seed params 2 2 :=
  fun index row column ↦ 11 * index.val + 13 * row.val + 19 * column.val + 7

private def coins : Fin 2 → SelectorCoins 2 (3 * params.levels) :=
  fun index ↦ Vector.ofFn fun sample ↦ Vector.ofFn fun column ↦
    decide ((index.val + sample.val + column.val) % 3 = 0)

private def key (bits : Fin 2 → Bool) : PublicKey 16777216 2 2 :=
  freshPublicKey (GSWSelfKey.binaryEmbed bits)
    (fun row sample ↦ 23 * row.val + 17 * sample.val + 5) ![1, -1]

private def controls (bits padBits : Fin 2 → Bool) :
    Vector (StoredCiphertext params 3) 2 :=
  let encryptedPads : Vector (StoredCiphertext params 3) 2 :=
    Vector.ofFn fun index ↦ encryptStored params (key bits) (coins index) (padBits index)
  Vector.ofFn fun index ↦ storeCiphertext params
    (compiled params seed (masked params seed padBits (bitMessage (bits index)))
      (fun pad ↦ ciphertextView params (encryptedPads.get pad)))

private def refreshCase (bits : Fin 2 → Bool) (body : ZMod 5) : Bool :=
  let stored := controls bits ![false, true]
  let weights : Fin 2 → ZMod 5 := ![1, 2]
  let function := fun value : ZMod 5 ↦ decide (value.val = 1 ∨ value.val = 3)
  let output := refresh params (fun index ↦ ciphertextView params (stored.get index))
    weights body function
  decrypt params (GSWSelfKey.binaryEmbed bits) output ⟨23, by decide⟩ ==
    function (body - dotProduct (GSWSelfKey.binaryEmbed bits) weights)

/-- Linked control noise and subsequent accumulator noise fit this test modulus. -/
example : 2 * (5 * 2 * growth params 3 * (2 * growth params 3 * (2 * 1))) <
    FormalProof4FHE.TFHE.BootstrappingCorrectness.centeredDistance
      0 (FormalProof4FHE.TFHE.Gadget.Base.gadget params ⟨23, by decide⟩) := by
  decide

private def bitPairs : List (Fin 2 → Bool) :=
  [![false, false], ![false, true], ![true, false], ![true, true]]

/-- info: true -/
#guard_msgs in
#eval bitPairs.all fun bits ↦ ([0, 1, 4] : List (ZMod 5)).all (refreshCase bits)

end FormalProof4FHETest.GSWLinkedMaskSmoke
