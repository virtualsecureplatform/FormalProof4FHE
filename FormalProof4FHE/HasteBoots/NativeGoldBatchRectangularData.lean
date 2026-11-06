module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularWeights
public import FormalProof4FHE.HasteBoots.NativeGoldBatchOpeningView
public import FormalProof4FHE.HasteBoots.RectangularBatchOpeningKernel
@[expose] public section

/-! The native batch's actual response groups and original queries, expressed
with independent packing and code widths. These are analysis projections of
execution, not additional verifier inputs or supplied encoding certificates. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularData
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (encoding logSize Tables)
open NativeGoldBatchResponseMeaning (Lane Domain)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFields (Goldilocks)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

abbrev Query (work : Prepared) := Fin work.binding.queries.val.length
abbrev Group (ctx : Context) (work : Prepared) := Fin (NativeGoldQueryGroups.groupCount ctx.parameters.leftVariables.val work.binding.queries)
abbrev groupOf (ctx : Context) (work : Prepared) := NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries
abbrev owner (ctx : Context) (work : Prepared) := NativeGoldQueryGroups.representative ctx.parameters.leftVariables.val work.binding.queries

theorem owner_group (ctx : Context) (work : Prepared) (group : Group ctx work) :
    groupOf ctx work (owner ctx work group) = group := by
  have same := (NativeGoldQueryGroups.group_key ctx.parameters.leftVariables.val work.binding.queries (owner ctx work group)).trans
    (NativeGoldQueryGroups.representative_key ctx.parameters.leftVariables.val work.binding.queries group)
  apply Fin.ext
  exact (BatchGrouping.representatives_nodup _).getElem_inj.mp (by simpa only [List.get_eq_getElem] using same)

def evaluationIndex (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (group : Group ctx work) : Fin work.evaluations.length :=
  ⟨group.val,by rw [(NativeGoldBatchPcsProgram.prepared_counts ctx world work prepared).2.1,
    (NativeGoldBatchPcsProgram.prepared_counts ctx world work prepared).1]; exact group.isLt⟩

def weightIndex (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (group : Group ctx work) : Fin work.weights.length :=
  ⟨group.val,by rw [(NativeGoldBatchPcsProgram.prepared_counts ctx world work prepared).1]; exact group.isLt⟩

def encoded (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (group : Group ctx work) :=
  fun lane : Fin ctx.parameters.width.val => Lane ctx work (work.evaluations.get (evaluationIndex ctx world work prepared group)) lane.val

def raw (ctx : Context) (group : ℕ) : List GoldWord :=
  ((ctx.opening.evaluations.val[group]?).map (fun row => row.val)).getD []

def messages (ctx : Context) (work : Prepared) (group : Group ctx work) (lane : Fin ctx.parameters.width.val) :=
  NativeGoldResponseMessages.message (encoding ctx.parameters.code work.planRoot) (raw ctx group.val) lane.val

def testMessages (ctx : Context) (work : Prepared) (lane : Fin ctx.parameters.width.val) :=
  NativeGoldResponseMessages.message (encoding ctx.parameters.code work.planRoot) ctx.opening.test.val lane.val

def left (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (group : Group ctx work) :=
  NativeGoldBatchRectangularWeights.left ctx world work prepared (owner ctx work group)

/-- The owner's left weights are exactly the original query's ordered
weights, after transport to the one checked left-cell type. -/
theorem original_left (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (query : Query work) :
    left ctx world work prepared (groupOf ctx work query) = NativeGoldBatchRectangularWeights.left ctx world work prepared query := by
  have prefixes := NativeGoldQueryWeightMeaning.representative_prefix ctx.parameters.width.val ctx.parameters.leftVariables.val work.binding.queries query
  have transfer (first second : List (MatrixFold.Pair (F := Goldilocks) (Lane := Fin ctx.parameters.width.val)))
      (same : first = second) (firstSize : first.length = ctx.parameters.leftVariables.val)
      (secondSize : second.length = ctx.parameters.leftVariables.val) (cell : Fin (2^ctx.parameters.leftVariables.val)) :
      FlatMatrixFold.weights first (Fin.cast (congrArg (fun n => 2^n) firstSize.symm) cell) =
        FlatMatrixFold.weights second (Fin.cast (congrArg (fun n => 2^n) secondSize.symm) cell) := by
    subst second
    rfl
  funext cell
  exact transfer _ _ prefixes
    (NativeGoldBatchRectangularWeights.prefix_length ctx world work prepared (owner ctx work (groupOf ctx work query)))
    (NativeGoldBatchRectangularWeights.prefix_length ctx world work prepared query) cell

def right (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (query : Query work) :=
  NativeGoldSuffixFinishing.encodedRight ctx.parameters (work.binding.queries.val.get query) (encoding ctx.parameters.code work.planRoot)
    (NativeGoldBatchFinishingMeaning.prepared_query_length ctx world work prepared query)
    (NativeGoldBatchFinishingMeaning.prepared_message_length ctx world work prepared)

def claimed (ctx : Context) (work : Prepared) (query : Query work) (lane : Fin ctx.parameters.width.val) : Goldilocks :=
  goldValue ((((work.binding.values.val[query.val]?).map (fun row => row.val)).getD [])[lane.val]?.getD 0)

theorem encoded_messages (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (group : Group ctx work) :
    encoded ctx world work prepared group = fun lane => BlockEncoder.encode (Domain ctx primitive)
      (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (messages ctx work group lane)) := by
  obtain ⟨response,read,computed⟩ := NativeGoldBatchFinishingMeaning.prepared_encoding ctx world work prepared (evaluationIndex ctx world work prepared group)
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup ctx.parameters.code constructed
  have meaning := NativeGoldResponseMessages.lanes_padded (encoding ctx.parameters.code work.planRoot) ctx.parameters.code.messageBlocks.val ctx.parameters.width.val
    response.val _ computed (Nat.le_of_lt dimensions.2.1) dimensions.2.2.1 primitive
  simp only [evaluationIndex] at read
  have rawRead : raw ctx group.val = response.val := by
    unfold raw
    rw [read]
    rfl
  funext lane
  change NativeGoldResponseMeaning.laneWord (encoding ctx.parameters.code work.planRoot) (work.evaluations.get (evaluationIndex ctx world work prepared group)) lane.val = _
  unfold messages
  rw [rawRead]
  exact meaning lane

theorem test_encoded_messages (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :
    (fun lane : Fin ctx.parameters.width.val => Lane ctx work work.test lane.val) = fun lane => BlockEncoder.encode (Domain ctx primitive)
      (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (testMessages ctx work lane)) := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,computed,_,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work prepared
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup ctx.parameters.code constructed
  exact funext (NativeGoldResponseMessages.lanes_padded (encoding ctx.parameters.code planRoot) ctx.parameters.code.messageBlocks.val ctx.parameters.width.val
    ctx.opening.test.val test computed (Nat.le_of_lt dimensions.2.1) dimensions.2.2.1 primitive)

theorem group_pair (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (group : Group ctx work) :
    (work.weights.get (weightIndex ctx world work prepared group),work.evaluations.get (evaluationIndex ctx world work prepared group)) ∈ work.groups := by
  have a := (weightIndex ctx world work prepared group).isLt
  have b := (evaluationIndex ctx world work prepared group).isLt
  have bound : group.val < work.groups.length := by
    simp only [NativeGoldBatchPcsProgram.Prepared.groups,List.length_zip]
    exact Nat.lt_min.mpr ⟨a,b⟩
  have member := List.getElem_mem bound
  simpa only [NativeGoldBatchPcsProgram.Prepared.groups,List.getElem_zip,List.get_eq_getElem,weightIndex,evaluationIndex] using member
/-- Each original accepted value is the message finishing of its actual
shared response group; distinct right queries remain distinct functions. -/
theorem accepted_claim {Memory : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (completion : NativeGoldBatchPcsProgram.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent) (query : Query work) :
    claimed ctx work query = RectangularBatchOpeningKernel.finishMessage (groupOf ctx work) (right ctx world work prepared) (messages ctx work) query := by
  obtain ⟨response,value,responseRead,valueRead,verified⟩ := NativeGoldBatchPcsProgram.accepted_claims ctx choose fuel memory world work completion executed parent accepted query
  have native := NativeGoldSuffixFinishing.claim_message ctx.parameters (work.binding.queries.val.get query) response.val value
    (NativeGoldBatchPcsProgram.prepared_query_valid ctx world work prepared query) verified
  have transport := NativeGoldSuffixFinishing.transport_message ctx.parameters (work.binding.queries.val.get query)
    (encoding ctx.parameters.code work.planRoot) response.val
    (NativeGoldBatchFinishingMeaning.prepared_query_length ctx world work prepared query)
    (NativeGoldBatchFinishingMeaning.prepared_message_length ctx world work prepared)
  rw [← transport] at native
  have rawRead : raw ctx (groupOf ctx work query).val = response.val := by
    unfold raw
    rw [responseRead]
    rfl
  funext lane
  have entry := congrArg (fun words => (words[lane.val]?).getD (goldValue 0)) native
  change claimed ctx work query lane = RectangularMatrixResponse.finishMessage (right ctx world work prepared query) (messages ctx work (groupOf ctx work query)) lane
  unfold claimed messages
  rw [valueRead,rawRead]
  simpa only [Option.map_some,Option.getD_some,List.getElem?_map,Option.getD_map,List.getElem?_ofFn,lane.isLt,reduceDIte,right] using entry

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularData
