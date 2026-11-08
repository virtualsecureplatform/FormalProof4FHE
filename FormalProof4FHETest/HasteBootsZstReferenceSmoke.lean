module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC

namespace FormalProof4FHETest.HasteBootsZstReferenceSmoke
open FormalProof4FHE.HasteBoots
private def shared : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.fromAddress ⟨1,by decide⟩),.borrow 0 .shared ⟨0,1⟩]).getD NativeReferenceMachine.empty
private def exclusive : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.fromAddress ⟨1,by decide⟩),.borrow 0 .exclusive ⟨0,1⟩]).getD NativeReferenceMachine.empty
private def nonzero : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64,by decide⟩ ⟨8,8⟩),.raw (.writeBytes 0 8 (List.replicate 8 0)),.borrow 0 .shared ⟨1,1⟩]).getD NativeReferenceMachine.empty
private def aligned : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.fromAddress ⟨64,by decide⟩),.borrow 0 .shared ⟨0,8⟩]).getD NativeReferenceMachine.empty

example : NativeZstReference.decode shared 0 = some (.reference false ⟨0⟩ ⟨0,by decide⟩) := by decide
example : NativeRecordLLBC.decode shared (.zstSharedReference 0) = some (.scalar (.reference false ⟨0⟩ ⟨0,by decide⟩)) := by decide
example : NativeZstReference.decode shared 99 = none := by decide
example : NativeZstReference.decode exclusive 0 = none := by decide
example : NativeZstReference.decode nonzero 0 = none := by decide
example : NativeZstReference.decode aligned 0 = none := by decide
example : (do
    let ended ← NativeReferenceMachine.execute shared (.endBorrow 0)
    pure (NativeZstReference.decode ended 0)) = some none := by decide

end FormalProof4FHETest.HasteBootsZstReferenceSmoke
