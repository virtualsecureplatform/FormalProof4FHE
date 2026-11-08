module
import FormalProof4FHE.HasteBoots.NativeByteDropCalls

namespace FormalProof4FHETest.HasteBootsByteDropCallsSmoke
open FormalProof4FHE.HasteBoots
open NativeByteDropCalls
open NativeSliceLLBC (Frame Value)

private def nested : Option (NativeReferenceMachine.State × NativeReferenceMachine.State) := do
  let entered ← NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0)), .borrow 0 .exclusive ⟨3,1⟩]
  let child ← NativeReferenceMachine.execute entered (.reborrow 0 0 .exclusive ⟨3,1⟩)
  pure (entered,child)
private def caller (world : NativeReferenceMachine.State) : Frame :=
  ⟨[.unit,.usize],[.live none,.live (some (.usize ⟨7, by decide⟩))],world⟩

example : (do
    let (entered,child) ← nested
    pure (match resumeCall entered (caller entered) 0 (.returned .unit child) with
      | .next frame => (frame.world.leases.map NativeByteBorrow.Lease.tag,NativeSliceLLBC.readLocal frame 0,
          NativeSliceLLBC.readLocal frame 1)
      | _ => ([],none,none))) = some ([0],some .unit,some (.usize ⟨7, by decide⟩)) := by decide

example : (do
    let (entered,child) ← nested
    let start : Frame := ⟨[.reference true],[.live none],entered⟩
    pure (match resumeCall entered start 0 (.returned (.reference true ⟨1⟩ ⟨3, by decide⟩) child) with
      | .next frame => (frame.world == child,NativeSliceLLBC.readLocal frame 0)
      | _ => (false,none))) = some (true,some (.reference true ⟨1⟩ ⟨3, by decide⟩)) := by decide

example : (do
    let (entered,child) ← nested
    pure (match resumeCall entered (caller entered) 0 (.unwind child) with
      | .unwind frame => (frame.world == child,NativeSliceLLBC.readLocal frame 1)
      | _ => (false,none))) = some (true,some (.usize ⟨7, by decide⟩)) := by decide

example : (do
    let (entered,child) ← nested
    pure (resumeCall entered (caller entered) 0 (.continued (caller child)) == .invalid child)) = some true := by decide

example : (do
    let (entered,child) ← nested
    pure (resumeCall entered (caller entered) 99 (.returned .unit child)).world.leases.length) = some 1 := by decide

example : (do
    let (entered,child) ← nested
    let malformed := {child with references := []}
    pure (resumeCall entered (caller entered) 0 (.returned .unit malformed) == .invalid malformed)) = some true := by decide

example : (do
    let (entered,_) ← nested
    let start : Frame := ⟨[.unit,.usize],[.dead,.live (some (.usize ⟨7, by decide⟩))],entered⟩
    let (moved,called) ← prepareCall start [.unit,.usize] 1 [.move 1]
    pure (NativeSliceLLBC.readLocal moved 1,NativeSliceLLBC.readLocal called 1,called.world == entered)) =
    some (none,some (.usize ⟨7, by decide⟩),true) := by decide

example : (do
    let (entered,_) ← nested
    let start : Frame := ⟨[.unit,.usize],[.dead,.live (some (.usize ⟨7, by decide⟩))],entered⟩
    prepareCall start [.unit,.reference true] 1 [.move 1]) = none := by decide

end FormalProof4FHETest.HasteBootsByteDropCallsSmoke
