module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchDraws
@[expose] public section

/-! Native batch source equations hold on the original ordered with-replacement
column vector. All random and grouped structured checks share that vector and
one complete frozen word. Freshness and the probability composition remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchOrderedChecks
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (Tables logSize description)
open NativeUsizeMessage (Usize)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open NativeGoldBatchResponseMeaning (Lane)
open NativeGoldBatchLinearEquations (Weights Word Frozen)
open NativeMerkleShapeFamily (height)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem prepared_group (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    ∃ response, response ∈ work.groups := by
  have counts := NativeGoldBatchPcsProgram.prepared_counts ctx world work executed
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,same⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have bound := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.1
  have nonempty := (NativeGoldBatchBinding.check_iff _ _ _).mp (NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound).1 |>.1
  have queries : 0 < work.binding.queries.val.length := by
    rw [(NativeGoldBatchPcsProgram.prepared_binding ctx world work executed).2.2.1]
    exact List.length_pos_iff.mpr nonempty
  have grouped := (NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries ⟨0,queries⟩).isLt
  have positive : 0 < work.groups.length := by
    simp only [NativeGoldBatchPcsProgram.Prepared.groups,List.length_zip,counts.2.1,Nat.min_self,counts.1]
    omega
  exact ⟨work.groups[0],List.getElem_mem positive⟩

/-- Deduplicated raw requests cover every occurrence of the original vector,
so acceptance checks use its full quota without multiplying group events. -/
theorem requests_agree (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (context : Digest) (requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request height))
    (computed : NativeGoldBatchFamilyRequests.prepare context work = some requests)
    (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code)))
    (ordered : (List.ofFn draw).map Fin.val = work.sample.draws)
    (values : ℕ → ℕ → NativeFields.Goldilocks)
    (checks : ∀ entry ∈ requests, ∃ bound : entry.2.position.val < 2^(logSize ctx.parameters.code),
      ∀ response ∈ work.groups, ∀ lane : Fin work.width,
        StructuredOpening.combine (Weights work work.random lane) (Word ctx work values) ⟨entry.2.position.val,bound⟩ = Lane ctx work work.test lane.val ⟨entry.2.position.val,bound⟩ ∧
        StructuredOpening.combine (Weights work response.1 lane) (Word ctx work values) ⟨entry.2.position.val,bound⟩ = Lane ctx work response.2 lane.val ⟨entry.2.position.val,bound⟩) :
    (∀ lane : Fin work.width, ColumnOpening.Agrees
      (StructuredOpening.combine (Weights work work.random lane) (Word ctx work values)) (Lane ctx work work.test lane.val) draw) ∧
    ∀ response ∈ work.groups, ∀ lane : Fin work.width, ColumnOpening.Agrees
      (StructuredOpening.combine (Weights work response.1 lane) (Word ctx work values)) (Lane ctx work response.2 lane.val) draw := by
  have each (response : NativeGoldBatchColumnWorker.Response) (member : response ∈ work.groups) (lane : Fin work.width) (index : Fin ctx.parameters.queries.val) :
      StructuredOpening.combine (Weights work work.random lane) (Word ctx work values) (draw index) = Lane ctx work work.test lane.val (draw index) ∧
      StructuredOpening.combine (Weights work response.1 lane) (Word ctx work values) (draw index) = Lane ctx work response.2 lane.val (draw index) := by
    obtain ⟨entry,present,same⟩ := NativeGoldBatchDraws.draw_request ctx world work executed context requests computed draw ordered index
    obtain ⟨bound,checked⟩ := checks entry present
    have position : (⟨entry.2.position.val,bound⟩ : Fin (2^(logSize ctx.parameters.code))) = draw index := Fin.ext same
    exact position ▸ checked response member lane
  constructor
  · obtain ⟨response,member⟩ := prepared_group ctx world work executed
    intro lane index
    exact (each response member lane index).1
  · intro response member lane index
    exact (each response member lane index).2

/-- One actual context/root checkpoint supplies the same immutable matrix for
all ordered draws and every response group. The typed vector is computed. -/
theorem source_agrees (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (history : List Observation) (source : NativeGoldBatchAnySourceRisk.HasSource dummy ctx work history world) :
    ∃ (context : Digest) (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest)
      (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code))),
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 = some context ∧
      (∀ index : NativeMerkleShapeFamily.Height,
        ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints) ∧
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      (∀ lane : Fin work.width, ColumnOpening.Agrees
        (StructuredOpening.combine (Weights work work.random lane) (Word ctx work (Frozen dummy context work log))) (Lane ctx work work.test lane.val) draw) ∧
      ∀ response ∈ work.groups, ∀ lane : Fin work.width, ColumnOpening.Agrees
        (StructuredOpening.combine (Weights work response.1 lane) (Word ctx work (Frozen dummy context work log))) (Lane ctx work response.2 lane.val) draw := by
  obtain ⟨context,requests,log,hashed,computed,snapshots,checks⟩ := NativeGoldBatchLinearEquations.source_combinations dummy ctx world work executed constructorTables message block blowup constructed history source
  obtain ⟨draw,typed,ordered,_⟩ := NativeGoldBatchDraws.prepared_typed ctx world work executed constructorTables message block blowup constructed
  obtain ⟨random,structured⟩ := requests_agree ctx world work executed context requests computed draw ordered _ checks
  exact ⟨context,log,draw,hashed,snapshots,typed,ordered,random,structured⟩
/-- Actual accepted native execution supplies both source availability and
preparation; the ordered agreement statement inserts no extra oracle call. -/
theorem accepted_agrees {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (history : List Observation) (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history)
    (noDisagreement : ¬CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history)) :
    ∃ (context : Digest) (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest)
      (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code))),
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 = some context ∧
      (∀ index : NativeMerkleShapeFamily.Height,
        ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints) ∧
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      (∀ lane : Fin work.width, ColumnOpening.Agrees
        (StructuredOpening.combine (Weights work work.random lane) (Word ctx work (Frozen dummy context work log))) (Lane ctx work work.test lane.val) draw) ∧
      ∀ response ∈ work.groups, ∀ lane : Fin work.width, ColumnOpening.Agrees
        (StructuredOpening.combine (Weights work response.1 lane) (Word ctx work (Frozen dummy context work log))) (Lane ctx work response.2 lane.val) draw := by
  have source := NativeGoldBatchAnySourceRisk.accepted_has_source dummy world history truthful ctx choose fuel memory work accepted noDisagreement
  obtain ⟨_,completion,parent,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  exact source_agrees dummy ctx world work prepared constructorTables message block blowup constructed history source

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchOrderedChecks
