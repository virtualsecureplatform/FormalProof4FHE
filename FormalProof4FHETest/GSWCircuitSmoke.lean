/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWPublicKey

/-! Executable correctness and storage diagnostics. The cryptographic dimensions are
deliberately tiny and insecure. Test public encryption followed by a DAG that repeatedly
reuses an encrypted intermediate, and separately exercise 256 gates sharing the preceding
wire. The latter checks the actual finite-data path without expanding a Boolean tree. -/

namespace FormalProof4FHETest.GSWCircuitSmoke

open FormalProof4FHE.LWE
open GSWGadget GSWAccumulator GSWCircuit GSWPublicKey

private def params : Parameters (16384 * 16) where
  base := 2
  levels := 18
  one_lt_base := by decide
  modulus_le_capacity := by decide

private def level : Fin params.levels := ⟨17, by decide⟩

/-- Wire 2 is used twice by gate 1 and again by gate 2. -/
private def shared : Program 2 5 :=
  .nand (.nand (.nand .start ⟨0, by decide⟩ ⟨1, by decide⟩)
    ⟨2, by decide⟩ ⟨2, by decide⟩) ⟨2, by decide⟩ ⟨3, by decide⟩

private def publicChallenge : Matrix (Fin 1) (Fin 5) (ZMod (16384 * 16)) :=
  fun row sample ↦ 101 + 13 * row.val + 31 * sample.val

private def publicError (sample : Fin 5) : ZMod (16384 * 16) :=
  if sample.val % 2 = 0 then 1 else -1

private def controlChallenge : Matrix (Fin 1) (Fin (2 * params.levels)) (ZMod (16384 * 16)) :=
  fun row column ↦ 47 + 17 * row.val + 23 * column.val

private def controlError (column : Fin (2 * params.levels)) : ZMod (16384 * 16) :=
  if column.val % 2 = 0 then 1 else -1

private def selection (offset : ℕ) : SelectorCoins 5 (2 * params.levels) :=
  Vector.ofFn fun sample ↦ Vector.ofFn fun column ↦
    decide ((offset + sample.val + 17 * column.val) % 3 = 0)

private def testCase (secretBit firstBit secondBit : Bool) : Bool :=
  let bits : Fin 1 → Bool := fun _ ↦ secretBit
  let secret := GSWSelfKey.binaryEmbed (R := ZMod (16384 * 16)) bits
  let publicKey := freshPublicKey secret publicChallenge publicError
  let controls := storedFreshBootKey params bits (fun _ ↦ controlChallenge) (fun _ ↦ controlError)
  let messages := Vector.ofFn fun index : Fin 2 ↦ if index.val = 0 then firstBit else secondBit
  let coins := Vector.ofFn fun index : Fin 2 ↦ selection index.val
  let inputs := encryptInputsStored params publicKey coins messages
  let output := evaluateWires params level (8 : ZMod 16) controls inputs shared
  let expected := runBits messages shared
  (List.ofFn fun index : Fin 5 ↦ index).all fun index ↦
    decrypt params secret (ciphertextView params (output.get index)) level == expected.get index

/-- info: true -/
#guard_msgs in
#eval [false, true].all (fun secretBit ↦ [false, true].all (fun firstBit ↦
  [false, true].all (testCase secretBit firstBit)))

private def repeated : (gates : ℕ) → Program 1 (gates + 1)
  | 0 => .start
  | gates + 1 => .nand (repeated gates) (Fin.last gates) (Fin.last gates)

/-- info: true -/
#guard_msgs in
#eval
  let initial : Vector Bool 1 := Vector.ofFn fun _ ↦ false
  let result := runCounted (fun first second ↦ !(first && second)) initial (repeated 256)
  result.2 == 256 && result.1.toArray.size == 257 &&
    result.1.get ⟨256, by decide⟩ == false

end FormalProof4FHETest.GSWCircuitSmoke
