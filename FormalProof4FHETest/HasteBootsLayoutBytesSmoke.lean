module
import FormalProof4FHE.HasteBoots.NativeLayoutBytes

namespace FormalProof4FHETest.HasteBootsLayoutBytesSmoke
open FormalProof4FHE.HasteBoots
open NativeLayoutBytes

private def words : Words := ⟨⟨24,by decide⟩,⟨8,by decide⟩⟩
private def ready (bytes : List NativeByteMemory.Byte) (length : Nat := 16) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64,by decide⟩ ⟨16,8⟩),.raw (.writeBytes 0 8 bytes),.borrow 0 .shared ⟨length,8⟩]).getD NativeReferenceMachine.empty

example : encode words = [8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0] := by decide
example : decode (encode words) = some words := by decide
example : decode (NativeWord64Memory.encode words.size ++ NativeWord64Memory.encode words.alignment) = none := by decide
example : decode (List.replicate 15 0) = none := by decide
example : decode (encode ⟨⟨24,by decide⟩,⟨3,by decide⟩⟩) = none := by decide
example : decode (encode ⟨⟨0,by decide⟩,⟨2^63,by decide⟩⟩) = some ⟨⟨0,by decide⟩,⟨2^63,by decide⟩⟩ := by decide

example : (match NativeLayoutBytes.read (ready (encode words)) 0 with
    | .value value world => (value,world.outputs,world.pointers.registers.length,
      world.pointers.heap == (ready (encode words)).pointers.heap)
    | _ => (⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,[],99,false)) =
    (words,[encode words],2,true) := by decide

private def bad : Words := ⟨⟨24,by decide⟩,⟨3,by decide⟩⟩
example : (match NativeLayoutBytes.read (ready (encode bad)) 0 with
    | .invalid world => (world.outputs,world.pointers.registers.length,
      world.pointers.heap == (ready (encode bad)).pointers.heap,world.nextTag)
    | _ => ([],99,false,99)) = ([encode bad],2,true,1) := by decide

example : NativeLayoutBytes.read (ready (encode words)) 99 = .invalid (ready (encode words)) := by decide
example : NativeLayoutBytes.read (ready (encode words) 8) 0 = .invalid (ready (encode words) 8) := by decide

example : (do
    let ended ← NativeReferenceMachine.execute (ready (encode words)) (.endBorrow 0)
    pure (NativeLayoutBytes.read ended 0 == .invalid ended)) = some true := by decide

private def blocked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64,by decide⟩ ⟨16,8⟩),.raw (.writeBytes 0 8 (encode words)),
     .borrow 0 .exclusive ⟨16,8⟩,.reborrow 0 0 .exclusive ⟨16,8⟩]).getD NativeReferenceMachine.empty
example : NativeLayoutBytes.read blocked 1 = .invalid blocked := by decide

end FormalProof4FHETest.HasteBootsLayoutBytesSmoke
