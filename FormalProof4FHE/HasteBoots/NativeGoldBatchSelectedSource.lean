module
public import FormalProof4FHE.HasteBoots.NativeRootFamilySourceSelection
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFieldExposure
public import FormalProof4FHE.HasteBoots.NativeGoldBatchAnySourceRisk
@[expose] public section

/-! One earlier-history-selected source log for actual accepted native
column payloads and equations. No future source-log witness is selected.
This is source availability, not independent public application extraction
or the final false-claim/physical-work security theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedSource
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (Height height shape tag)
open NativeGoldRawRequests (Request)
open NativeGoldBatchRawAvailability (Equations view)
open NativeGoldBatchFieldInputView (View)
open NativeGoldBatchFamilyAvailability (reconstructed)
open MerkleTreeMultiExtractability
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- All arguments are available in the original selecting history. -/
def log (dummy : Digest) (before : List Observation) (field : View) : NativeRootFamilySourceSelection.Log :=
  NativeRootFamilySourceSelection.select (NativeRootFamilyHistory.reconstruct encoding dummy before) (field.data.context,field.data.root)

theorem selected_snapshot (dummy : Digest) (before after : List Observation) (input : Input) (field : View)
    (parsed : NativeGoldBatchFieldInputView.parse input = some field)
    (offset : ℕ) (values : Input) (positive : values ≠ []) :
    ∀ index : Height, ⟨(field.data.context,index),⟨field.data.root,log dummy before field⟩⟩ ∈
      (reconstructed dummy (before++ .output input offset values :: after)).checkpoints.checkpoints := by
  exact NativeRootFamilySourceSelection.selected_history encoding dummy before after _ input offset values positive
    (NativeGoldBatchFieldExposure.parsed_resolved input field parsed _ _)

/-- Every recorded common log may be used for the accepted payloads; the
selection theorem above supplies the particular earlier-history log. -/
theorem accepted_at_log {Memory : Type} (dummy context : Digest) (ctx : Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldBatchPcsProgram.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (requests : List (NativeGoldColumnWorker.Job × Request height)) (computed : NativeGoldBatchFamilyRequests.prepare context work = some requests)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history)
    (sourceLog : NativeRootFamilySourceSelection.Log)
    (snapshots : ∀ index : Height, ⟨(context,index),⟨work.root,sourceLog⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints)
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history)) :
    ∀ entry ∈ requests,
      entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,sourceLog⟩ entry.2.position ∧
      Equations (view work requests) (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,sourceLog⟩ entry.2.position) entry.2.position.val := by
  have noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (requests.map Prod.snd) (reconstructed dummy history) :=
    fun failure => noDisagreement (ParallelColumnAvailability.failure_implies_disagreement encoding dummy height _ _ failure)
  have spec := NativeGoldBatchRawRequests.prepare_spec height (tag context work) work requests computed
  have each := NativeGoldBatchFamilyRequests.accepted_replays context ctx choose fuel memory world work completion
    executed parent accepted requests computed history truthful observed
  intro entry member
  have recorded : ⟨entry.2.tag,⟨entry.2.root,sourceLog⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints := by
    obtain ⟨bound,leaf,siblings,_,same⟩ := NativeGoldRawRequests.fromJob_spec height (tag context work) work.root entry.1 entry.2 (spec.2 entry member)
    rw [same]
    exact snapshots (tag context work).2
  have replayed : ParallelColumnAvailability.Replays encoding height entry.2 (reconstructed dummy history).hash.cache := by
    rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
    exact (each entry member).1
  refine ⟨NativeGoldRawAvailability.payload_of_no_failure dummy height (requests.map Prod.snd) entry.2
    (List.mem_map.mpr ⟨entry,member,rfl⟩) (reconstructed dummy history) replayed ⟨entry.2.root,sourceLog⟩ recorded rfl noFailure,?_⟩
  exact NativeGoldBatchFamilyAvailability.accepted_equations dummy context ctx choose fuel memory world work completion
    executed parent accepted requests computed history truthful observed noFailure entry member ⟨entry.2.root,sourceLog⟩ recorded rfl

/-- An actual parsed native field read fixes one common source before that
read. Every later accepted native column and group uses exactly that source. -/
theorem accepted_selected {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (before after : List Observation) (field : View)
    (parsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchRandomLaw.phase work).pending.input = some field)
    (offset : ℕ) (values : Input) (positive : values ≠ [])
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world
      (before++ .output (NativeGoldBatchRandomLaw.phase work).pending.input offset values :: after) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (before++ .output (NativeGoldBatchRandomLaw.phase work).pending.input offset values :: after))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape
      (reconstructed dummy (before++ .output (NativeGoldBatchRandomLaw.phase work).pending.input offset values :: after))) :
    ∃ requests : List (NativeGoldColumnWorker.Job × Request height),
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some field.data.context ∧
      NativeGoldBatchFamilyRequests.prepare field.data.context work = some requests ∧
      (∀ index : Height, ⟨(field.data.context,index),⟨work.root,log dummy before field⟩⟩ ∈
        (reconstructed dummy (before++ .output (NativeGoldBatchRandomLaw.phase work).pending.input offset values :: after)).checkpoints.checkpoints) ∧
      ∀ entry ∈ requests,
        entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,log dummy before field⟩ entry.2.position ∧
        Equations (view work requests) (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log dummy before field⟩ entry.2.position) entry.2.position.val := by
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,next,executed,status,observed⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨context,hashed,_,native⟩ := NativeGoldBatchFieldExposure.prepared_phase ctx world work prepared frames parent valid fits
  have equal := Option.some.inj (parsed.symm.trans native)
  have contextEq : field.data.context = context := congrArg (fun value => value.data.context) equal
  have rootEq : field.data.root = work.root := by
    rw [equal]
    exact (NativeGoldBatchPcsProgram.prepared_binding ctx world work prepared).1.symm
  obtain ⟨requests,computed⟩ := NativeGoldBatchFamilyRequests.prepare_complete field.data.context ctx world work prepared
  have snapshots := selected_snapshot dummy before after _ field parsed offset values positive
  rw [rootEq] at snapshots
  refine ⟨requests,by rw [contextEq]; exact hashed,computed,snapshots,?_⟩
  exact accepted_at_log dummy field.data.context ctx choose fuel memory world work completion executed next status requests computed _ truthful observed
    (log dummy before field) snapshots noDisagreement
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedSource
