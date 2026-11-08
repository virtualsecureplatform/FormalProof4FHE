namespace HasteBootsRetagDisabledControl
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC HasteBootsReferenceRetagBody

-- This file is checked only against the mutated original identity body with
-- its Use flag changed from WithRetag.Yes to WithRetag.No.
example : (do
    let world ← NativeReferenceMachine.run NativeReferenceMachine.empty
      [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0))]
    pure (match invoke f2 world [.rawRegister 0, .usize ⟨3, by decide⟩] with
      | .returned .unit next => (next.nextTag, next.leases.length)
      | _ => (99,99))) = some (3,3) := by decide

end HasteBootsRetagDisabledControl
