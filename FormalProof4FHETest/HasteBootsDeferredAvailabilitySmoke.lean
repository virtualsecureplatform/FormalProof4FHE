module
import all FormalProof4FHE.HasteBoots.NativeGoldLookupLifetimeAvailability
import all FormalProof4FHETest.HasteBootsDeferredRegistrySmoke
import all FormalProof4FHETest.HasteBootsBatchPcsSmoke
open FormalProof4FHE.HasteBoots
open NativePrefixCodec (Vector)
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (run)
namespace HasteBootsDeferredAvailabilitySmoke
noncomputable section

def native := HasteBootsBatchPcsSmoke.Accepted.context.get (by decide +kernel)
def digest := HasteBootsSourceGroupsSmoke.nativeDigest
def registry : Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored) :=
  ⟨[⟨native.parameters,native.root⟩,⟨{native.parameters with queries := ⟨99,by decide⟩},native.root⟩],by decide⟩
def metadata : NativeSourceRegistry.Initialized := ⟨⟨[(digest,native.root),(digest,native.root)],by decide⟩,native.parent⟩
def claims := (native.queries.val.zip native.values.val).foldl
  (fun state pair => (NativeDeferredOpeningBatch.push registry state ⟨1,by decide⟩ pair.1 pair.2).1)
  (NativeDeferredOpeningBatch.initial metadata)
def ctx : NativeDeferredBatchVerification.Context :=
  ⟨native.tables,registry,claims,⟨[native.opening],by decide⟩,native.fieldFuel,6⟩

-- Reuse captured native rows, columns and hash answers. Only the enclosing
-- transcript has changed; these explicit test-world streams are not a freshness claim.
def world : World
  | .inr query => HasteBootsBatchPcsSmoke.Accepted.world (.inr query)
  | .inl (input,offset) =>
    match (TranscriptFrame.decodeAll input).bind List.getLast? with
    | some frame => if frame.kind = 4 ∧ frame.label = NativeGoldBatchPrelude.randomLabel then
        HasteBootsBatchPcsSmoke.Accepted.stream0[offset]?.getD 255
      else if frame.kind = 2 ∧ frame.label = NativeGoldBatchColumns.label then
        HasteBootsBatchPcsSmoke.Accepted.stream2[offset]?.getD 255
      else HasteBootsBatchPcsSmoke.Accepted.world (.inl (input,offset))
    | none => HasteBootsBatchPcsSmoke.Accepted.world (.inl (input,offset))

def execution (cancel : Bool) := (run (NativeDeferredBatchVerification.program ctx (HasteBootsBatchPcsSmoke.choose cancel) ()) world).run
def resultTag : NativeDeferredBatchVerification.Outcome Unit → ℕ
  | .sealRejected _ _ => 0
  | .verification (.done _) => 1
  | .verification (.stopped _ _ _) => 2
  | _ => 3

def receipts : List (NativeDeferredBatchVerification.Receipt Unit) := match (execution false).1 with
  | .verification result => result.progress.receipts
  | _ => []

example : claims.claims.val.map (fun claim => claim.slot.val) = [1,1,1,1] := by decide +kernel
example : resultTag (execution false).1 = 1 := by decide +kernel
example : receipts.map (fun receipt => receipt.call.slot) = [0] := by decide +kernel
example : receipts.map (fun receipt => receipt.call.queries.val.length) = [4] := by decide +kernel
example : receipts.map (fun receipt => receipt.call.oracle.parameters.queries.val) = [1] := by decide +kernel
example : (execution false).2.length = 14 := by decide +kernel
example : resultTag (execution true).1 = 2 := by decide +kernel
-- A later rejected root must retain the earlier accepted receipt.
def rootTwo : NativeRootMessage.Digest := fun index => if index.val = 0 then
  ⟨((native.root index).val+1)%256,Nat.mod_lt _ (by decide)⟩ else native.root index
def registryTwo : Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored) :=
  ⟨registry.val ++ [⟨native.parameters,rootTwo⟩],by decide +kernel⟩
def metadataTwo : NativeSourceRegistry.Initialized :=
  ⟨⟨[(digest,native.root),(digest,native.root),(digest,rootTwo)],by decide⟩,native.parent⟩
def claimsTwo :=
  let first := (native.queries.val.zip native.values.val).foldl
    (fun state pair => (NativeDeferredOpeningBatch.push registryTwo state ⟨1,by decide⟩ pair.1 pair.2).1)
    (NativeDeferredOpeningBatch.initial metadataTwo)
  (native.queries.val.zip native.values.val).foldl
    (fun state pair => (NativeDeferredOpeningBatch.push registryTwo state ⟨2,by decide⟩ pair.1 pair.2).1) first
def ctxTwo : NativeDeferredBatchVerification.Context :=
  ⟨native.tables,registryTwo,claimsTwo,⟨[native.opening,native.opening],by decide⟩,native.fieldFuel,6⟩
def executionTwo := (run (NativeDeferredBatchVerification.program ctxTwo (HasteBootsBatchPcsSmoke.choose false) ()) world).run
def receiptsOf : NativeDeferredBatchVerification.Outcome Unit → List (NativeDeferredBatchVerification.Receipt Unit)
  | .verification result => result.progress.receipts
  | _ => []
example : rootTwo ≠ native.root := by decide +kernel
example : (NativeDeferredOpeningBatch.usedGroups claimsTwo).map Fin.val = [0,1] := by decide +kernel
example : resultTag executionTwo.1 = 2 := by decide +kernel
example : (receiptsOf executionTwo.1).map (fun receipt => receipt.call.slot) = [0] := by decide +kernel
example : (match executionTwo.1 with | .verification (.stopped _ call _) => some call.slot | _ => none) = some 2 := by decide +kernel
example : executionTwo.2.length = 28 := by decide +kernel

end
end HasteBootsDeferredAvailabilitySmoke
