module
public import FormalProof4FHE.HasteBoots.LookupGuardProducer
public import FormalProof4FHE.HasteBoots.NativeSharedLookupProofShape
@[expose] public section

/-! Original preflight, proof-shape checking and executed preparation recover
full-width typed source vectors from the actual guarded original job. -/
namespace FormalProof4FHE.HasteBoots.LookupGuardSources
open NativeSharedLookupStatement (Request)
open NativeSharedLookupPrelude (Ready guardInputs)
open NativeSharedLookupGuard (Checked Result)
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupProofShape (Values)
open NativeFieldRepresentation (GoldWord)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
noncomputable section

theorem vectors {count padding : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : Values)
    (shape : NativeSharedLookupProofShape.check registry (List.ofFn requests) geometry openingCount values = true)
    (width : geometry.geometry.2.val = 3+padding)
    (rootFits : values.roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (ready : Ready geometry.geometry.1.val)
    (prepared : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities
      values.roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (claims : List NativeScalarBatchVerifier.SubClaim) (sourceVars : ℕ) (result : Result)
    (passed : NativeSharedLookupGuard.guard (guardInputs requests ready values.sources values.helpers)
      claims sourceVars geometry.geometry.2.val = some result)
    (index : Fin ready.jobs.length) :
    ∃ checked : Checked, result.checked[index.val]? = some checked ∧ checked.ordinal = index.val ∧
      checked.job = NativeSharedLookupGuard.Job.fromProduced (ready.jobs.get index).tag.ordinal.val (ready.jobs.get index).output ∧
      checked.request = (ready.jobs.get index).tag.request.terminal ∧
      NativeSharedLookupGuard.Evidence (guardInputs requests ready values.sources values.helpers) claims result.point result.pulled
        geometry.geometry.2.val checked ∧
      ∃ inputs : Fin (ready.jobs.get index).tag.request.columns → Fin (3+padding) → GoldWord,
        List.ofFn (fun i => List.ofFn (inputs i)) = checked.values ∧
        List.Forall₂ (fun slot value => values.sources[slot]? = some value)
          (ready.jobs.get index).tag.request.terminal.sourceSlots checked.values := by
  obtain ⟨checked,checkedAt,ordinal,job,evidence⟩ := LookupGuardProducer.job_checked requests ready values.sources values.helpers
    claims sourceVars geometry.geometry.2.val result passed index
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
    w lookupFuel equalityFuel transcript world ready prepared
  have tags := (NativeSharedLookupPrepared.prepare_spec _ _ _ contract.prepared).1
  have tagMember : (ready.jobs.get index).tag ∈ NativeSharedLookupStatement.tags fits requests := by
    rw [← tags]
    exact List.mem_map.mpr ⟨ready.jobs.get index,List.get_mem _ _,rfl⟩
  have requestAt := (NativeSharedLookupProofShape.tag_request fits requests _ tagMember).2
  have originalRequest : checked.request = (ready.jobs.get index).tag.request.terminal := by
    have found := evidence.request
    rw [job] at found
    change ((List.ofFn requests).map Request.terminal)[(ready.jobs.get index).tag.ordinal.val]? = some checked.request at found
    simpa only [List.getElem?_map,requestAt,Option.map_some,Option.some.injEq] using found.symm
  obtain ⟨copies,gathered,countEq,related,lengths⟩ := NativeSharedLookupProofShape.source_getters registry helper (List.ofFn requests)
    geometry preflight openingCount values shape (ready.jobs.get index).tag.request (List.mem_of_getElem? requestAt)
  have copiesEq : copies = checked.values := by
    rw [← originalRequest] at gathered
    exact Option.some.inj (gathered.symm.trans evidence.values)
  subst copies
  have sourceBound (i : Fin (ready.jobs.get index).tag.request.columns) : i.val < checked.values.length := by
    rw [countEq]; exact i.isLt
  have laneLength (i : Fin (ready.jobs.get index).tag.request.columns) : (checked.values[i.val]'(sourceBound i)).length = 3+padding :=
    (lengths _ (List.getElem_mem (sourceBound i))).trans width
  let inputs : Fin (ready.jobs.get index).tag.request.columns → Fin (3+padding) → GoldWord :=
    fun i j => (checked.values[i.val]'(sourceBound i))[j.val]'(by rw [laneLength]; exact j.isLt)
  refine ⟨checked,checkedAt,ordinal,job,originalRequest,evidence,inputs,?_,related⟩
  apply List.ext_getElem (by simp only [List.length_ofFn,countEq])
  intro i leftBound rightBound
  simp only [List.getElem_ofFn]
  apply List.ext_getElem (by rw [List.length_ofFn]; exact ((lengths _ (List.getElem_mem rightBound)).trans width).symm)
  intro j leftLane rightLane
  simp only [List.getElem_ofFn,inputs]

end
end FormalProof4FHE.HasteBoots.LookupGuardSources
