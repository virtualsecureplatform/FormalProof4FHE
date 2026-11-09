module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC

namespace FormalProof4FHETest.HasteBootsRawVecMutBorrowSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 128 ⟨16,8⟩),.raw (.writeBytes 0 8 (List.replicate 16 0)),
     .borrow 0 .exclusive ⟨16,8⟩]).getD NativeReferenceMachine.empty
private def frame : Frame := ⟨[.scalar .unit,.scalar (.reference true),.scalar (.reference true)],
  [.live none,.live (some (.scalar (.reference true ⟨0⟩ 2))),.live none],ready⟩
private def plan : NativeRawVecMutBorrow.Reservation := ⟨⟨0⟩,⟨128,some ⟨128,0⟩⟩⟩
private def prepared : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.raw (.withAddress 0 128))).getD NativeReferenceMachine.empty

example : ready.nextTag = 1 := by decide
example : NativeRawVecMutBorrow.reserve ready (.reference true ⟨0⟩ 2) = .value plan prepared := by decide
example : prepared.nextTag = 1 ∧ prepared.leases = ready.leases ∧ prepared.births = ready.births := by decide
example : (match NativeRawVecMutBorrow.activate prepared plan with
    | .value value next => (value,next.nextTag,next.leases.head?.map NativeByteBorrow.Lease.parent)
    | _ => (.unit,99,none)) = (.reference true ⟨1⟩ 2,2,some (some 0)) := by decide
example : NativeRawVecMutBorrow.reserve ready (.reference false ⟨0⟩ 2) = .invalid ready := by decide
example : NativeRawVecMutBorrow.reserve ready (.reference true ⟨0⟩ 3) = .invalid ready := by decide
example : NativeRawVecMutBorrow.reserve ready (.reference true ⟨99⟩ 2) = .invalid ready := by decide
example : NativeRawVecMutBorrow.activate ready ⟨⟨0⟩,⟨128,none⟩⟩ = .invalid ready := by decide
example : evalOperand frame (.copy 1 []) = none := by decide
example : (match evalRvalue frame (.borrowRawVecMut 1 []) with
    | .value value next => (value,next.world.nextTag)
    | _ => (.uninit,99)) = (.scalar (.reference true ⟨1⟩ 2),2) := by decide

private def callee : Body := .live 0 (.assign 0 .unit .ret)
private def types : List NativeRecordValues.Ty := [.scalar .unit,.scalar (.reference true),.scalar .usize]
private def delayed (rest : List Operand) : Body :=
  .twoPhaseRawVecCall 1 [] 2 "adjacent" .transparent types 2 0 rest callee .resume .ret
private def early : Body := .assign 2 (.borrowRawVecMut 1 [])
  (.call "ordinary" .transparent types 2 0 [.move 2 [],.copy 99 []] callee .resume .ret)
example : (match eval (delayed [.copy 99 []]) frame with
    | .invalid next => (next.nextTag,next.leases == ready.leases,next.pointers.registers.length)
    | _ => (99,false,99)) = (1,true,2) := by decide
example : (match eval early frame with
    | .invalid next => (next.nextTag,next.leases.length)
    | _ => (99,99)) = (2,2) := by decide
example : (match eval (delayed [.usize 7]) frame with
    | .returned (.scalar .unit) next => (next.nextTag,next.leases.map NativeByteBorrow.Lease.tag)
    | _ => (99,[])) = (2,[1,0]) := by decide
private def occupied : Frame := {frame with slots := [.live none,.live (some (.scalar (.reference true ⟨0⟩ 2))),.live (some (.scalar (.reference true ⟨0⟩ 2)))]}
example : eval (delayed [.usize 7]) occupied = .invalid ready := by decide
private def sharedChild : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.reborrow 0 0 .shared ⟨16,8⟩)).getD NativeReferenceMachine.empty
example : (match NativeRawVecMutBorrow.reserve sharedChild (.reference true ⟨0⟩ 2) with
    | .value reservation next => (next.nextTag,NativeRawVecMutBorrow.activate next reservation == .invalid next)
    | _ => (99,false)) = (2,true) := by decide
example : evalOperand frame (.layoutLiteral 1 1 9 11 12) = some
  (.record 9 (.pair (.scalar (.usize 1)) (.pair (.record 11 (.pair (.enumeration 12 1) (.scalar .unit))) (.scalar .unit))),frame) := by decide

end FormalProof4FHETest.HasteBootsRawVecMutBorrowSmoke
