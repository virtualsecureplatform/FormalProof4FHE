module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC

namespace FormalProof4FHETest.HasteBootsRecordLLBCSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeRecordValues (Value)

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64,by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0)),
     .borrow 0 .shared ⟨3,1⟩, .reborrow 0 0 .shared ⟨3,1⟩, .endBorrow 0]).getD NativeReferenceMachine.empty

private def value : Value := .record 7 (.pair (.scalar (.usize ⟨11,by decide⟩)) (.scalar (.usize ⟨22,by decide⟩)))
private def frame : Frame := ⟨[.scalar .unit,.record 7 (.pair (.scalar .usize) (.scalar .usize))],
  [.dead,.live (some value)],ready⟩

example : (do
    let (_,changed) ← evalOperand frame (.move 1 [.unwrap 7,.left])
    pure (read changed 1 [.unwrap 7,.left], read changed 1 [.unwrap 7,.right], read changed 1 [], changed.world == ready)) =
    some (none,some (.scalar (.usize ⟨22,by decide⟩)),none,true) := by decide

example : (match retag ready (.record 8 (.pair
    (.scalar (.reference false ⟨0⟩ ⟨3,by decide⟩))
    (.scalar (.reference false ⟨1⟩ ⟨3,by decide⟩)))) true .byte with
    | .invalid world => (world.nextTag,world.leases.map NativeByteBorrow.Lease.tag,
      world.pointers.heap == ready.pointers.heap)
    | _ => (99,[],false)) = (3,[2,0],true) := by decide

example : (match retag ready (.record 8 (.pair
    (.scalar (.reference false ⟨0⟩ ⟨3,by decide⟩))
    (.scalar (.reference false ⟨1⟩ ⟨3,by decide⟩)))) false .byte with
    | .value _ world => world == ready
    | _ => false) = true := by decide

example : evalOperand ⟨[.scalar (.reference true)],[.live (some (.scalar (.reference true ⟨0⟩ ⟨3,by decide⟩)))],ready⟩
    (.copy 0 []) = none := by decide

example : (match eval (.switchUsize (.usize ⟨0,by decide⟩) ⟨0,by decide⟩ .abort (.unsupported "other") .done) frame with
    | .invalid world => world == ready
    | _ => false) = true := by decide

example : (match eval (.switchUsize (.usize ⟨1,by decide⟩) ⟨0,by decide⟩ .abort (.unsupported "other") .done) frame with
    | .unsupported source world => (source,world == ready)
    | _ => ("wrong",false)) = ("other",true) := by decide

example : decode ready (.record 9 (.pair (.scalar (.rawRegister 0)) .unit)) =
    some (.record 9 (.pair (.scalar (.raw ⟨⟨⟨64,by decide⟩,some ⟨64,0⟩⟩,none⟩)) (.scalar .unit))) := by decide

example : decode ready (.record 9 (.pair (.scalar (.rawRegister 99)) .unit)) = none := by decide

end FormalProof4FHETest.HasteBootsRecordLLBCSmoke
