module
import all FormalProof4FHE.HasteBoots.NativeSliceLLBC

namespace HasteBootsSliceLLBCSmoke
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC

private def ready : Option NativeReferenceMachine.State := NativeReferenceMachine.run NativeReferenceMachine.empty
  [.raw (.allocate ⟨64, by decide⟩ ⟨32, 8⟩), .raw (.writeBytes 0 8 (List.replicate 32 0))]
private def choose (condition : Bool) : Function := ⟨"constant_branch", [.usize, .usize], 1,
  .storageLive 0 (.constIf condition (.unsupported "retained" .done) .done (.assign 0 (.use (.copy 1)) .ret))⟩
private def makeParts : Function := ⟨"pointer_parts", [.raw true, .raw false, .usize], 2,
  .storageLive 0 (.parts 0 (.copy 1) (.copy 2) .abort .ret)⟩
private def makeReference (next : Body) : Function := ⟨"reference", [.reference true, .raw false, .usize, .raw true], 2,
  .storageLive 0 (.storageLive 3 (.parts 3 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 3) next)))⟩

example : invoke (choose false) NativeReferenceMachine.empty [.usize ⟨7, by decide⟩] =
    .returned (.usize ⟨7, by decide⟩) NativeReferenceMachine.empty := by decide
example : invoke (choose true) NativeReferenceMachine.empty [.usize ⟨7, by decide⟩] =
    .unsupported "retained" NativeReferenceMachine.empty := by decide
example : (do
    let world ← ready
    pure (match invoke makeParts world [.rawRegister 0, .usize ⟨3, by decide⟩] with
      | .returned (.raw pointer) next => (pointer.storage.address.val, pointer.length.map Fin.val, next == world)
      | _ => (0, none, false))) = some (64, some 3, true) := by decide
example : (do
    let world ← ready
    pure (match invoke (makeReference .ret) world [.rawRegister 0, .usize ⟨3, by decide⟩] with
      | .returned (.reference mutable reference length) next => (mutable, reference.tag, length.val, next.nextTag)
      | _ => (false, 99, 0, 0))) = some (true, 0, 3, 1) := by decide
example : (do
    let world ← ready
    pure (invoke (makeReference .ret) world [.rawRegister 0, .usize ⟨5, by decide⟩] == .invalid world)) = some true := by decide
example : (do
    let world ← ready
    pure (invoke (makeReference .ret) world [.rawRegister 0, .usize ⟨2^64-1, by decide⟩] == .invalid world)) = some true := by decide
example : (do
    let world ← ready
    pure (match invoke (makeReference (.unsupported "later" .ret)) world [.rawRegister 0, .usize ⟨3, by decide⟩] with
      | .unsupported "later" next => (next.nextTag, next.leases.length, next.pointers.heap == world.pointers.heap)
      | _ => (0, 0, false))) = some (1, 1, true) := by decide
example : invoke makeParts NativeReferenceMachine.empty [.rawRegister 0, .usize ⟨0, by decide⟩] = .invalid NativeReferenceMachine.empty := by decide
example : invoke (choose false) NativeReferenceMachine.empty [] = .invalid NativeReferenceMachine.empty := by decide

end HasteBootsSliceLLBCSmoke
