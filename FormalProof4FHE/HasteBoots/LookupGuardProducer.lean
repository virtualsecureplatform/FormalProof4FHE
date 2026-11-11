module
public import FormalProof4FHE.HasteBoots.LookupNativeTerminal
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPrelude
@[expose] public section

/-! The original job ordinal selects its actual native terminal record and
its actual completed producer. Neither association is supplied separately. -/
namespace FormalProof4FHE.HasteBoots.LookupGuardProducer
open NativeSharedLookupStatement (Request Prepared)
open NativeSharedLookupPrelude (Ready guardInputs)
open NativeSharedLookupGuard (Inputs Checked Result)
open NativeFieldRepresentation (GoldWord)
open NativeGoldExtensionArithmetic (Word)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
noncomputable section

/-- Every original prepared job has its own actual guarded record at the
same ordinal, including repeated requests and aliased source slots. -/
theorem job_checked {count dimension : ℕ} (requests : Fin count → Request) (ready : Ready dimension)
    (sourceValues : List (List GoldWord)) (helperValues : List Word) (claims : List NativeScalarBatchVerifier.SubClaim)
    (sourceVars width : ℕ) (result : Result)
    (passed : NativeSharedLookupGuard.guard (guardInputs requests ready sourceValues helperValues) claims sourceVars width = some result)
    (index : Fin ready.jobs.length) :
    ∃ checked : Checked, result.checked[index.val]? = some checked ∧ checked.ordinal = index.val ∧
      checked.job = NativeSharedLookupGuard.Job.fromProduced (ready.jobs.get index).tag.ordinal.val (ready.jobs.get index).output ∧
      NativeSharedLookupGuard.Evidence (guardInputs requests ready sourceValues helperValues) claims result.point result.pulled width checked := by
  have accepted := NativeSharedLookupGuard.guard_spec _ claims sourceVars width result passed
  have length : result.checked.length = ready.jobs.length := by
    simpa only [guardInputs,NativeSharedLookupPrepared.guardJobs,List.length_map] using accepted.count
  have bound : index.val < result.checked.length := by rw [length]; exact index.isLt
  let checked := result.checked[index.val]'bound
  have checkedAt : result.checked[index.val]? = some checked := List.getElem?_eq_getElem bound
  have ordinal := congrArg (fun values : List ℕ => values[index.val]?) accepted.ordinals
  have job := congrArg (fun values : List NativeSharedLookupGuard.Job => values[index.val]?) accepted.jobs
  have originalAt : ready.jobs[index.val]? = some (ready.jobs.get index) := List.getElem?_eq_getElem index.isLt
  have originalBound : index.val < (guardInputs requests ready sourceValues helperValues).jobs.length := by
    simpa only [guardInputs,NativeSharedLookupPrepared.guardJobs,List.length_map] using index.isLt
  have ordinalEq : checked.ordinal = index.val := by
    simpa only [List.getElem?_map,checkedAt,Option.map_some,List.getElem?_range',originalBound,ite_true,Nat.zero_add,one_mul,Option.some.injEq] using ordinal
  have jobEq : checked.job = NativeSharedLookupGuard.Job.fromProduced (ready.jobs.get index).tag.ordinal.val (ready.jobs.get index).output := by
    simpa only [guardInputs,NativeSharedLookupPrepared.guardJobs,List.getElem?_map,checkedAt,originalAt,Option.map_some,Option.some.injEq] using job
  exact ⟨checked,checkedAt,ordinalEq,jobEq,accepted.checked checked (List.mem_of_getElem? checkedAt)⟩

/-- Successful original preparation and sampling identify a completed producer
for each original job. Its literal width is the original request's columns. -/
theorem protocol_producer {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : NativeUsizeMessage.Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World) (ready : Ready n.val)
    (success : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits
      w lookupFuel equalityFuel transcript) world).run.1 = some ready) (index : Fin ready.jobs.length) :
    ∃ completed : NativeLookupBatch.Completed NativeFields.goldilocksModulus Goldilocks3,
      completed ∈ (NativeLookupBatch.execute goldilocksBasis w lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed ∧
      completed.job = (ready.jobs.get index).tag.job ∧
      NativeGoldLookupProducer.produce (ready.jobs.get index).tag.request.columns (ready.jobs.get index).tag.request.table
        completed.selection = some (ready.jobs.get index).output := by
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests n multiplicities roots rootFits w lookupFuel equalityFuel
    transcript world ready success
  have prepared := NativeSharedLookupPrepared.prepare_spec _ _ _ contract.prepared
  obtain ⟨final,finished,_,_⟩ := contract.lookup
  have jobs := NativeSharedLookupStatement.finished_jobs fits requests w lookupFuel transcript world final finished
  rw [← prepared.1,List.map_map] at jobs
  have bound : index.val < (NativeLookupBatch.execute goldilocksBasis w lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed.length := by
    have countEq := prepared.2.length_eq
    omega
  let completed := (NativeLookupBatch.execute goldilocksBasis w lookupFuel
    (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed[index.val]'bound
  have aligned := congrArg (fun values : List (NativeLookupBatch.Job NativeFields.goldilocksModulus) => values[index.val]?) jobs
  have completedAt : (NativeLookupBatch.execute goldilocksBasis w lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed[index.val]? = some completed :=
    List.getElem?_eq_getElem bound
  have originalAt : ready.jobs[index.val]? = some (ready.jobs.get index) := List.getElem?_eq_getElem index.isLt
  have sameJob : completed.job = (ready.jobs.get index).tag.job := by
    simpa only [List.getElem?_map,completedAt,originalAt,Option.map_some,Option.some.injEq,Function.comp_def] using aligned
  have produced := prepared.2.get bound index.isLt
  have result : NativeGoldLookupProducer.produce completed.job.request.width (ready.jobs.get index).tag.request.table completed.selection =
      some (ready.jobs.get index).output := by
    simpa only [List.get_eq_getElem,completed] using produced
  refine ⟨completed,List.mem_of_getElem? completedAt,sameJob,?_⟩
  rw [sameJob] at result
  exact result

end
end FormalProof4FHE.HasteBoots.LookupGuardProducer
