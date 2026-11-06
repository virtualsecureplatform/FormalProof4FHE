module
import all FormalProof4FHE.HasteBoots.NativeRegisteredLookup
import all FormalProof4FHE.HasteBoots.NativeSharedSourceClaims
import all FormalProof4FHE.HasteBoots.NativeDeferredBatchVerification
import all FormalProof4FHETest.HasteBootsRegistryAncestrySmoke
import all FormalProof4FHETest.HasteBootsSourceGroupsSmoke
open FormalProof4FHE.HasteBoots
open OracleProgram (run)
open HasteBootsRegistryAncestrySmoke (usize digest description registry expected world parent helper requests request)
namespace HasteBootsDeferredRegistrySmoke
noncomputable section
def sealTag : Except NativeDeferredOpeningBatch.Error Unit → ℕ
  | .ok () => 0
  | .error .packetCount => 1
  | .error .noClaims => 2
  | .error _ => 3

def metadata : NativeSourceRegistry.Initialized := ⟨expected,parent⟩
def initial := NativeDeferredOpeningBatch.initial metadata
def matrix : NativeGoldPcsWire.Matrix := ⟨usize 4,⟨List.replicate 16 (usize 0),by decide⟩⟩
def query : NativeGoldPcsWire.Query := ⟨[(matrix,matrix)],by decide⟩
def row (value : ℕ) : NativeLookupRequestWire.Row := ⟨[usize value,usize 0,usize 0,usize 0],by change 4 < 2^64; decide⟩
def values : NativeLookupRequestWire.Table := ⟨[row 0,row NativeFields.goldilocksModulus,row 0],by decide⟩
def allRequests : NativePrefixCodec.Vector NativeLookupRequestWire.Request :=
  ⟨[{request with sourceSlots := ⟨[usize 0,usize 1,usize 2],by decide⟩}],by decide⟩
def collected (requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request) (values : NativeLookupRequestWire.Table) :=
  (run (NativeSharedSourceClaims.program description registry requests query values initial) world).run

def state := (collected requests values).1.progress.state
example : state.claims.val.map (fun claim => claim.slot.val) = [1] := by decide +kernel
example : (NativeDeferredOpeningBatch.usedGroups state).map Fin.val = [0] := by decide +kernel
example : state.claims.val.map (fun claim => claim.values.val.map Fin.val) = [[NativeFields.goldilocksModulus,0,0,0]] := by decide +kernel
example : (collected requests values).2.length = 1 := by decide +kernel
example : state.parent.input = (NativeDeferredOpeningBatch.bindClaim initial (usize 1) query (row NativeFields.goldilocksModulus)).input := by decide +kernel
example : (collected allRequests values).1.progress.state.claims.val.map (fun claim => claim.slot.val) = [0,2] := by decide +kernel
example : (collected allRequests values).2.length = 3 := by decide +kernel
example : (collected allRequests values).1.progress.seen.map NativeSharedSourceClaims.Seen.slot = [0,2] := by decide +kernel

def badValues : NativeLookupRequestWire.Table := ⟨[row 0,row 1,row 0],by decide⟩
def stopped : NativeSharedSourceClaims.Result → Bool
  | .stopped _ .alias => true
  | _ => false
example : stopped (collected allRequests badValues).1 = true := by decide +kernel
example : (collected allRequests badValues).2.length = 2 := by decide +kernel
example : (collected allRequests badValues).1.progress.state.claims.val.map (fun claim => claim.slot.val) = [0] := by decide +kernel
example : (collected ⟨[],by decide⟩ values).2 = [] := by decide +kernel
example : sealTag (NativeDeferredOpeningBatch.sealBatch initial 0).2 = 2 := by decide +kernel
example : sealTag (NativeDeferredOpeningBatch.sealBatch initial 1).2 = 1 := by decide +kernel
example : (NativeDeferredOpeningBatch.sealBatch state 0).1.parent.input = state.parent.input ∧
    sealTag (NativeDeferredOpeningBatch.sealBatch state 0).2 = 1 := by decide +kernel
example : sealTag (NativeDeferredOpeningBatch.sealBatch state 1).2 = 0 := by decide +kernel
example : (NativeDeferredOpeningBatch.sealBatch state 1).1.parent.input.length > state.parent.input.length := by decide +kernel
example : (run (NativeRegisteredLookup.prepare description registry helper parent requests) world).run.1.2.map (fun (_,metadata) => metadata.sources.val.length) = some 3 := by decide +kernel
example : ((run (NativeRegisteredLookup.prepare description registry helper parent requests) world).run.1.1,
    (run (NativeRegisteredLookup.prepare description registry helper parent requests) world).run.1.2.map Prod.fst,
    (run (NativeRegisteredLookup.prepare description registry helper parent requests) world).run.2) =
    ((run (NativeSharedLookupParent.prepare description registry helper parent requests) world).run.1.1,
    (run (NativeSharedLookupParent.prepare description registry helper parent requests) world).run.1.2,
    (run (NativeSharedLookupParent.prepare description registry helper parent requests) world).run.2) := by
  exact congrArg (fun packet => (packet.1.1,packet.1.2,packet.2))
    (NativeRegisteredLookup.prepare_erasure description registry helper parent requests world)

-- Synthetic complete-key collisions may identify different parameter objects.
-- Dispatch must still use original slot 0, even though only slot 1 was used.
def typedRegistry : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored) :=
  ⟨[⟨HasteBootsSourceGroupsSmoke.batchParameters,digest 7⟩,
    ⟨{HasteBootsSourceGroupsSmoke.batchParameters with queries := usize 99},digest 7⟩,
    ⟨HasteBootsSourceGroupsSmoke.batchParameters,digest 7⟩],by decide⟩
def opening : NativeGoldBatchOpening.Opening := ⟨⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩⟩
def firstCall := NativeDeferredBatchVerification.call typedRegistry state ⟨0,by decide +kernel⟩ opening
example : firstCall.map NativeDeferredBatchVerification.Call.slot = some 0 := by decide +kernel
example : firstCall.map (fun call => call.oracle.parameters.queries.val) = some HasteBootsSourceGroupsSmoke.batchParameters.queries.val := by decide +kernel
example : firstCall.map (fun call => call.values.val.map (fun row => row.val.map Fin.val)) = some [[NativeFields.goldilocksModulus,0,0,0]] := by decide +kernel
end
end HasteBootsDeferredRegistrySmoke
