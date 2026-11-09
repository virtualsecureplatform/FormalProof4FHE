module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC
import FormalProof4FHE.HasteBoots.NativeVariantValues

namespace FormalProof4FHETest.HasteBootsChoiceLLBCSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def world := NativeReferenceMachine.empty
private def type : NativeRecordValues.Ty := .record 4 (.choice (.scalar .unit)
  (.pair (.scalar .usize) (.scalar .usize)))
private def value : NativeRecordValues.Value := .record 4 (.choice true
  (.pair (.scalar (.usize 11)) (.scalar (.usize 22))))
private def frame : Frame := ⟨[.scalar .unit,type],[.live none,.live (some value)],world⟩
private def path : NativeRecordValues.Path := [.unwrap 4,.active true,.left]

example : selectChoice frame 1 [] 4 = some true := by decide
example : selectChoice frame 1 [] 5 = none := by decide
example : read frame 1 [.unwrap 4,.active false] = none := by decide
example : read frame 1 path = some (.scalar (.usize 11)) := by decide
example : (do
    let (_,changed) ← evalOperand frame (.move 1 path)
    pure (selectChoice changed 1 [] 4, read changed 1 path,
      read changed 1 [.unwrap 4,.active true,.right], read changed 1 [],changed.world == world)) =
    some (some true,none,some (.scalar (.usize 22)),none,true) := by decide
example : eval (.matchChoice 1 [] 4 (.unsupported "left") .done (.unsupported "suffix")) frame =
    .unsupported "suffix" world := by decide
example : eval (.matchChoice 1 [] 4 .done .abort (.unsupported "suffix")) frame =
    .invalid world := by decide
example : eval (.matchChoice 1 [] 4 .done .resume (.unsupported "suffix")) frame =
    .unwind world := by decide
example : eval (.matchChoice 1 [] 5 .done .done (.unsupported "suffix")) frame =
    .invalid world := by decide
example : selectChoice {frame with slots := [.live none,.dead]} 1 [] 4 = none := by decide
example : selectChoice {frame with slots := [.live none,.live (some (.record 4 .uninit))]} 1 [] 4 = none := by decide
example : evalRvalue frame (.aggregate (some 4) (some true) [.usize 1,.usize 2]) =
    .value (.record 4 (.choice true (.pair (.scalar (.usize 1))
      (.pair (.scalar (.usize 2)) (.scalar .unit))))) frame := by decide
example : decode world (.record 4 (.choice false .unit)) =
    some (.record 4 (.choice false (.scalar .unit))) := by decide
example : NativeRecordValues.copyable (.choice (.scalar .usize) (.scalar (.reference true))) = false := by decide
example : (do
    let (_,changed) ← evalOperand frame (.move 1 path)
    pure (eval (.matchChoice 1 [] 4 .abort .done (.unsupported "partial tag")) changed)) =
    some (.unsupported "partial tag" world) := by decide

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0)),
     .borrow 0 .shared ⟨3,1⟩, .reborrow 0 0 .shared ⟨3,1⟩, .endBorrow 0]).getD NativeReferenceMachine.empty

example : (match retag ready (.choice true (.pair
    (.scalar (.reference false ⟨0⟩ 3)) (.scalar (.reference false ⟨1⟩ 3)))) true .byte with
    | .invalid world => (world.nextTag,world.leases.map NativeByteBorrow.Lease.tag,
      world.pointers.heap == ready.pointers.heap)
    | _ => (99,[],false)) = (3,[2,0],true) := by decide
example : retag world (.choice false (.scalar .unit)) true .byte =
    .value (.choice false (.scalar .unit)) world := by decide

end FormalProof4FHETest.HasteBootsChoiceLLBCSmoke
