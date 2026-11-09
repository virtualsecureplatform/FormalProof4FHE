module
import FormalProof4FHE.HasteBoots.NativeRecordCallValues
namespace FormalProof4FHETest.HasteBootsRecordCallValuesSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC (Frame Flow Function Body)
open NativeRecordCallValues
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute NativeReferenceMachine.empty (.raw (.allocate 64 ⟨8,1⟩))).getD NativeReferenceMachine.empty
private def buffer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def unitFunction : Function :=
  ⟨"unit",.transparent,[.scalar .unit,.scalar (.reference true)],1,
    .live 0 (.assign 0 (.aggregate none none []) .ret)⟩
private def caller : Frame := ⟨unitFunction.types,
  [.live none,.live (some (.scalar (.reference true ⟨0⟩ 2)))],ready⟩
example : invokeValues unitFunction ready [] = .invalid ready := by decide
example : invokeValues unitFunction ready [.scalar (.usize 1)] = .invalid ready := by decide
example : invokeValues unitFunction ready [.scalar (.reference true ⟨0⟩ 2)] = .returned (.scalar .unit) ready := by decide
-- The normal successor receives the consumed caller frame.
example : NativeRecordLLBC.eval (.call unitFunction.name unitFunction.classification unitFunction.types 1 0
    [.move 1 []] unitFunction.body .abort (.assign 0 (.use (.move 1 []) false) .ret)) caller = .invalid ready := by decide
private def unwinding : Function := {unitFunction with body := .resume}
example : NativeRecordLLBC.eval (.call unwinding.name unwinding.classification unwinding.types 1 0
    [.move 1 []] unwinding.body .abort .ret) caller = .invalid ready := by decide
private def unsupported : Function := {unitFunction with body := .unsupported "retained helper"}
example : NativeRecordLLBC.eval (.call unsupported.name unsupported.classification unsupported.types 1 0
    [.move 1 []] unsupported.body .abort .ret) caller = .unsupported "retained helper" ready := by decide

private def releasing : Function :=
  ⟨"release",.externalBody,[.scalar .unit,.scalar (.raw false),.scalar .usize,.enumeration 12 [1]],3,
    .deallocate (.move 1 []) (.move 2 []) (.move 3 []) 12⟩
private def releaseCaller : Frame := ⟨releasing.types,
  [.dead,.live (some (.scalar (.raw ⟨buffer,none⟩))),.live (some (.scalar (.usize 8))),.live (some (.enumeration 12 1))],ready⟩
private def released : NativeReferenceMachine.State :=
  (NativeByteDeallocation.execute ready ⟨buffer,none⟩ 8 1).getD NativeReferenceMachine.empty
-- Failure to write the callee result retains its already executed free.
example : NativeRecordLLBC.eval (.call releasing.name releasing.classification releasing.types 3 0
    [.move 1 [],.move 2 [],.move 3 []] releasing.body .abort .ret) releaseCaller = .invalid released := by decide
example : released.pointers.heap.memory.blocks.length = 0 := by decide
example : UnitResult (invokeValues releasing ready [.scalar (.raw ⟨buffer,none⟩),.scalar (.usize 8),.enumeration 12 1]) := by
  have returned : invokeValues releasing ready [.scalar (.raw ⟨buffer,none⟩),.scalar (.usize 8),.enumeration 12 1] =
      .returned (.scalar .unit) released := by decide
  rw [returned]
  rfl
end FormalProof4FHETest.HasteBootsRecordCallValuesSmoke
