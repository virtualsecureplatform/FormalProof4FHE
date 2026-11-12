module
import all FormalProof4FHE.HasteBoots.RebuiltCallerLookupCoverage
import all FormalProof4FHE.HasteBoots.LookupParentPayloadBound

namespace HasteBootsRebuiltLookupSmoke
open FormalProof4FHE.HasteBoots
open NativeLookupRequestWire (Request)
open NativePrefixCodec (Vector)
noncomputable section

def lazyZero : NativeFieldRepresentation.GoldWord := ⟨NativeFields.goldilocksModulus,by decide +kernel⟩
abbrev requestA : Request := ⟨⟨⟨3,by decide⟩,⟨[⟨[lazyZero,0],by decide⟩,⟨[1,2],by decide⟩],by decide⟩,⟨2,by decide⟩⟩,
  ⟨[⟨1,by decide⟩,⟨1,by decide⟩],by decide⟩⟩
abbrev requestB : Request := ⟨⟨⟨2,by decide⟩,⟨[⟨[7],by decide⟩,⟨[8],by decide⟩],by decide⟩,⟨1,by decide⟩⟩,
  ⟨[⟨0,by decide⟩],by decide⟩⟩
abbrev original : Vector Request := ⟨[requestA,requestB],by decide⟩
abbrev ragged : Request := {requestA with config := {requestA.config with table := ⟨[⟨[0,0],by decide⟩,⟨[1],by decide⟩],by decide⟩}}
abbrev duplicate : Request := {requestB with config := {requestB.config with table := ⟨[⟨[0],by decide⟩,⟨[lazyZero],by decide⟩],by decide⟩}}

theorem malformed_rejected : (LookupRequestRebuild.rebuild .retain ⟨[ragged],by decide⟩).isNone = true ∧
    (LookupRequestRebuild.rebuild .retain ⟨[{requestB with config := {requestB.config with repetitions := ⟨0,by decide⟩}}],by decide⟩).isNone = true := by decide +kernel

/-- Distinct raw u64 spellings of the same field row are semantic duplicates. -/
theorem semantic_duplicates_rejected : (LookupRequestRebuild.rebuild .retain ⟨[duplicate],by decide⟩).isNone = true ∧
    (LookupRequestRebuild.rebuild .canonical ⟨[duplicate],by decide⟩).isNone = true := by decide +kernel

theorem normalization_preserves_requests :
    (LookupRequestRebuild.rebuild .canonical original).map (fun requests =>
      (requests.val.map (fun request => request.sourceSlots.val.map Fin.val),
        requests.val.map (fun request => request.config.repetitions.val),
        requests.val.map (fun request => request.config.table.values.map (List.map Fin.val)))) =
      some ([[1,1],[0]],[2,1],[[[0,0],[1,2]],[[7],[8]]]) := by decide +kernel

/-- Native power/zip/fold agrees on the original lazy public row and the
next row without a row permutation or an extra padded table entry. -/
theorem native_hash_rows :
    (NativeGoldLookup.tableAt requestA.toModel.table requestA.toModel.columns NativeGoldLookup.one).map
      (fun word => List.ofFn (fun coordinate => NativeFieldRepresentation.goldCanonical (word coordinate))) = [[0,0,0],[3,0,0]] := by decide +kernel

theorem variable_payload_sizes : (NativeLookupRequestWire.tableCodec.encode requestA.config.table).length = 15 ∧
    (NativeLookupRequestWire.requestsCodec.encode original).length = 30 ∧
    (NativeLookupRequestWire.requestsCodec.encode (LookupRequestRebuild.normalized .canonical original)).length = 22 := by decide +kernel

/-- Invalid constructor data skips allocation and both verifier schedulers. -/
theorem invalid_entry_log_empty {Memory : Type} (template : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (world : InputIndexedOracle.World) :
    (OracleProgram.run (RebuiltLookupExecution.program .retain ⟨[ragged],by decide⟩ [] 0 ⟨[],by decide⟩ template
      chooseHelper chooseBatch memory) world).run = (.invalid,[]) := by
  exact RebuiltLookupExecution.rejected _ _ _ _ _ _ _ _ _ _ (by decide +kernel)

end
end HasteBootsRebuiltLookupSmoke
