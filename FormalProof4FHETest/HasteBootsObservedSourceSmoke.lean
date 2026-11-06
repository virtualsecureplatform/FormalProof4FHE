module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchSourceRisk
import all FormalProof4FHETest.HasteBootsBatchExposureSmoke
open FormalProof4FHE.HasteBoots
open NativeRootMessage (Digest)
open InputIndexedOracle (Input World)
open OracleProgram (run)
namespace HasteBootsObservedSourceSmoke
noncomputable section
open HasteBootsBatchExposureSmoke (dummy input first)
def state (history : List NativeTranscript.Observation) :=
  NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy history

example (history : List NativeTranscript.Observation) : NativeRootFamilyHistory.Covered (state history) :=
  NativeRootFamilyHistory.reconstruct_covered _ _ _
example : (state first).2.checkpoints.checkpoints.length = 64 := by decide +kernel
example : ((state first).2.checkpoints.checkpoints.all (fun checkpoint => checkpoint.2.cumulativeLog.length == 1)) = true := by decide +kernel
example : (state [.start input,.output input 7 []]).2.checkpoints.checkpoints.length = 0 := by decide +kernel
example : (state (first ++ [.hash [9] (List.replicate 64 42),.output input 0 [1,2]])).2.checkpoints.checkpoints.length = 64 := by decide +kernel
example : ((state (first ++ [.hash [9] (List.replicate 64 42),.output input 0 [1,2]])).2.checkpoints.checkpoints.all
    (fun checkpoint => checkpoint.2.cumulativeLog.length == 1)) = true := by decide +kernel

def capturedPhase := HasteBootsBatchPcsSmoke.Accepted.context.map (fun ctx =>
  match (run (NativeGoldBatchPcsProgram.prepareProgram ctx) HasteBootsBatchPcsSmoke.Accepted.world).run.1 with
  | .prepared work => some (NativeGoldBatchReadExposure.phase ctx work).pending.input
  | _ => none)
example : capturedPhase = some (some HasteBootsBatchPcsSmoke.Accepted.start0) := by decide +kernel
example : HasteBootsBatchPcsSmoke.Accepted.context.map (fun ctx =>
    128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length) = some 198 := by decide +kernel

-- The first canonical candidate rejects; its bytes are nevertheless exposed and retained.
def profile : Digest := fun _ => 0
def parent := NativeTranscript.new [] profile
def rejectFirst : World := fun query => match query with
  | .inl (_,position) => if position < 8 then 255 else 0
  | .inr _ => 0

def request := NativePrimeRequest.request NativeFields.goldilocksModulus 2 parent .vector [] ⟨1,by decide⟩
def field := NativePrimeRequest.phase NativeFields.goldilocksModulus parent .vector [] ⟨1,by decide⟩
example : (run request rejectFirst).run.2.take 3 =
    [.start field.pending.input,.output field.pending.input 0 (List.replicate 8 255),.output field.pending.input 8 (List.replicate 8 0)] := by decide +kernel
example : (match (run request rejectFirst).run.1 with
    | .finished state _ => some (state.values,state.chunks.length)
    | .suspended _ => none) = some ([0],2) := by decide +kernel
example : (match (run (NativePrimeRequest.request NativeFields.goldilocksModulus 1 parent .vector [] ⟨1,by decide⟩) rejectFirst).run.1 with
    | .finished _ _ => none
    | .suspended state => some (state.remaining,state.values,state.chunks.length,state.phase.consumed.length)) =
    some (1,[],1,8) := by decide +kernel

-- The real accepted verifier remains between arbitrary causal prefix/suffix calls.
def extended := HasteBootsBatchPcsSmoke.Accepted.context.map (fun ctx =>
  (run (NativeGoldBatchSourceRisk.program (.hash [9] (fun _ => .pure ctx))
    (HasteBootsBatchPcsSmoke.choose false) 6 ()
    (fun _ _ => .read [11] 7 1 (fun _ => .pure ()))) HasteBootsBatchPcsSmoke.Accepted.world).run)
example : extended.map (fun packet => HasteBootsBatchPcsSmoke.tag packet.1.2) = some 1 := by decide +kernel
example : extended.map Prod.snd = some
    ([.hash [9] (List.replicate 64 255)] ++ HasteBootsBatchPcsSmoke.Accepted.expected ++ [.output [11] 7 [255]]) := by decide +kernel

end
end HasteBootsObservedSourceSmoke
