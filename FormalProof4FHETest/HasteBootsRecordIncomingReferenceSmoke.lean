module
import FormalProof4FHE.HasteBoots.NativeRecordIncomingReference
namespace FormalProof4FHETest.HasteBootsRecordIncomingReferenceSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC (Frame Flow Body Function)
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 128 ⟨16,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .raw (.fromAddress 1),.raw (.withAddress 1 136),.raw (.store 0 1),.borrow 2 .exclusive ⟨16,8⟩]).getD NativeReferenceMachine.empty
private def caller : Frame :=
  ⟨[.scalar .unit,.scalar (.reference true),.scalar (.reference true)],
    [.live none,.live (some (.scalar (.reference true ⟨0⟩ 2))),.live none],ready⟩
private def body : Body := .assign 2 (.borrowRawVecMut 1 []) (.assign 0 (.aggregate none none []) .ret)
private def outcome := NativeRecordLLBC.eval body caller
example : outcome = .returned (.scalar .unit) outcome.world ∧ outcome.world.nextTag = 2 ∧
    outcome.world.leases.map NativeByteBorrow.Lease.tag = [1,0] := by decide
example : NativeIncomingReference.Preserves ready outcome.world := NativeRecordLLBC.eval_incoming_projects body caller
private def settled := NativeRecordLLBC.settle ready outcome
example : settled = .returned (.scalar .unit) settled.world ∧ settled.world.nextTag = 2 ∧
    settled.world.leases.map NativeByteBorrow.Lease.tag = [0] := by decide
example : NativeIncomingReference.Preserves ready settled.world :=
  NativeRecordLLBC.settle_incoming_projects ready outcome (NativeRecordLLBC.eval_incoming_projects body caller)
example : NativeByteBorrow.lookup settled.world.leases 0 = NativeByteBorrow.lookup ready.leases 0 :=
  (NativeRecordLLBC.settle_incoming_projects ready outcome (NativeRecordLLBC.eval_incoming_projects body caller)).lookup 0 (by decide)
private def rejected : Body := .assign 2 (.borrowRawVecMut 1 []) .abort
private def failed := NativeRecordLLBC.eval rejected caller
example : failed = .invalid failed.world ∧ failed.world.leases.map NativeByteBorrow.Lease.tag = [1,0] := by decide
example : NativeIncomingReference.Preserves ready failed.world := NativeRecordLLBC.eval_incoming_projects rejected caller
-- Failed outcomes keep their already issued child; normal cleanup ends it.
example : NativeRecordLLBC.settle ready failed = failed := by decide
end FormalProof4FHETest.HasteBootsRecordIncomingReferenceSmoke
