module
import FormalProof4FHE.HasteBoots.NativeRecordDropCalls
namespace FormalProof4FHETest.HasteBootsRecordDropCallsSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordDropCalls
private def ready : NativeReferenceMachine.State := NativeReferenceMachine.empty
private def frame : NativeRecordLLBC.Frame := ⟨[.scalar .unit],[.dead],ready⟩
example : Runs (.native (.live 0 (.assign 0 .unit .ret)) .done) frame (.returned (.scalar .unit) ready) :=
  .nativeStop _ _ _ _ rfl rfl
example : Runs (.native (.unsupported "foreign") .done) frame (.unsupported "foreign" ready) :=
  .nativeStop _ _ _ _ rfl rfl
example : Runs (.call "missing" .transparent [.scalar .unit] 1 0 [] .done .done .done) frame (.invalid ready) :=
  .callInvalid _ _ _ _ _ _ _ _ _ _ rfl
example : loopArgument frame = none := by decide
example : fromLoop (.returned .unit ⟨[],[],ready⟩) = .returned (.scalar .unit) ready := rfl
example : resumeCall ready frame 0 (.unwind ready) = .unwind frame := rfl
example : resumeCall ready frame 0 (.normal frame) = .invalid ready := rfl
example : resumeCall ready frame 0 (.unsupported "foreign" ready) = .unsupported "foreign" ready := rfl
private def parentWorld : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run ready [.raw (.allocate 128 ⟨24,8⟩),
    .raw (.writeBytes 0 8 (List.replicate 24 0)),.borrow 0 .exclusive ⟨24,8⟩]).getD ready
private def childWorld : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute parentWorld (.reborrow 0 0 .exclusive ⟨24,8⟩)).getD ready
private def childFrame : NativeRecordLLBC.Frame := {frame with world := childWorld}
example : (resumeScope parentWorld (.normal childFrame)).world.nextTag = 2 ∧
    (resumeScope parentWorld (.normal childFrame)).world.leases.map NativeByteBorrow.Lease.tag = [0] := by decide
example : resumeScope parentWorld (.invalid childWorld) = .invalid childWorld := rfl
example : (resumeScope childWorld (.normal childFrame)).world.leases = childWorld.leases := by decide
end FormalProof4FHETest.HasteBootsRecordDropCallsSmoke
