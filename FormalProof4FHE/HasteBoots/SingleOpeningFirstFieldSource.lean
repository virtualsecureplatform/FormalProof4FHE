module
public import FormalProof4FHE.HasteBoots.SingleOpeningChallengeLink
public import FormalProof4FHE.HasteBoots.NativeRootFamilySourceSelection
public import FormalProof4FHE.HasteBoots.CausalFirstStreamPrefix
@[expose] public section

/-! Select the single-opening source from the exact pre-first-field-read
history. Later hashes, receipt reads and accepted work do not replace that log.
Actual accepted payloads and both coordinate families use this same source. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFirstFieldSource
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (Height height shape)
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open NativeGoldRawRequests (Request)
open NativeGoldBatchFamilyAvailability (reconstructed)
open SingleOpeningFieldInputView (View)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def input (field : View) : Input := TranscriptFrame.encodeMany field.frames

def selectedLog (dummy : Digest) (before : List Observation) (field : View) : Log :=
  NativeRootFamilySourceSelection.select (NativeRootFamilyHistory.reconstruct encoding dummy before) (field.data.context,field.data.root)

/-- The exact parsed adjacent binding resolves through the shared parent ledger. -/
theorem parsed_resolved (bytes : Input) (field : View) (parsed : SingleOpeningFieldInputView.parse bytes = some field)
    (ledger : NativeParentLedger.State) (cache : NativeShakeCache.Cache) :
    (field.data.context,field.data.root) ∈ NativeParentLedger.resolve ledger cache bytes := by
  have sound := SingleOpeningFieldInputView.parse_sound bytes field parsed (fun _ => 0)
  have framesEq : field.frames = SingleOpeningExposure.frames field.before (SingleOpeningExposure.suffix field.count)
      field.data.context field.data.root field.data.query field.data.claimed := rfl
  have valid : ∀ entry ∈ SingleOpeningExposure.frames field.before (SingleOpeningExposure.suffix field.count)
      field.data.context field.data.root field.data.query field.data.claimed, TranscriptFrame.Valid entry := by
    rw [← framesEq]
    exact sound.2.2
  have same : SingleOpeningExposure.input field.before (SingleOpeningExposure.suffix field.count)
      field.data.context field.data.root field.data.query field.data.claimed = bytes := by
    change TranscriptFrame.encodeMany _ = bytes
    rw [← framesEq,← SingleOpeningFieldInputView.phase_input field (fun _ => 0)]
    exact sound.1
  have mentioned := SingleOpeningExposure.mentioned field.before (SingleOpeningExposure.suffix field.count)
    field.data.context field.data.root field.data.query field.data.claimed valid
  rw [same] at mentioned
  unfold NativeParentLedger.resolve
  exact List.mem_append_left _ mentioned

theorem selected_snapshot (dummy : Digest) (before after : List Observation) (bytes : Input) (field : View)
    (parsed : SingleOpeningFieldInputView.parse bytes = some field) (offset : ℕ) (values : Input) (positive : values ≠ []) :
    ∀ index : Height, ⟨(field.data.context,index),⟨field.data.root,selectedLog dummy before field⟩⟩ ∈
      (reconstructed dummy (before++ .output bytes offset values :: after)).checkpoints.checkpoints :=
  NativeRootFamilySourceSelection.selected_history encoding dummy before after _ bytes offset values positive
    (parsed_resolved bytes field parsed _ _)

def recover (dummy : Digest) (history : List Observation) (field : View) : Option Log :=
  (CausalFirstStreamPrefix.recover (input field) history).map (fun before => selectedLog dummy before field)

theorem recover_none (dummy : Digest) (history : List Observation) (field : View) :
    recover dummy history field = none ↔ CausalStreamExposure.seen history (input field) = false := by
  simp only [recover,Option.map_eq_none_iff,CausalFirstStreamPrefix.recover_none]

theorem recover_exists (dummy : Digest) (history : List Observation) (field : View)
    (seen : CausalStreamExposure.seen history (input field) = true) : ∃ sourceLog, recover dummy history field = some sourceLog := by
  cases found : recover dummy history field with
  | none =>
    have unseen := (recover_none dummy history field).mp found
    rw [seen] at unseen
    contradiction
  | some sourceLog => exact ⟨sourceLog,rfl⟩

theorem recover_at (dummy : Digest) (before after : List Observation) (field : View) (offset : ℕ) (values : Input)
    (unseen : CausalStreamExposure.seen before (input field) = false) (positive : values ≠ []) :
    recover dummy (before++ .output (input field) offset values :: after) field = some (selectedLog dummy before field) := by
  unfold recover
  rw [CausalFirstStreamPrefix.recover_at _ _ _ _ unseen (by simp [CausalStreamExposure.touches,List.length_pos_iff,positive])]
  rfl

/-- Even later authenticated queries cannot move the selected pre-read log. -/
theorem recover_append (dummy : Digest) (before after : List Observation) (field : View) (sourceLog : Log)
    (found : recover dummy before field = some sourceLog) : recover dummy (before++after) field = some sourceLog := by
  obtain ⟨prefixLog,first,equal⟩ := Option.map_eq_some_iff.mp found
  simp only [recover,CausalFirstStreamPrefix.recover_append _ before after prefixLog first,Option.map_some,equal]

theorem recover_sound (dummy : Digest) (history : List Observation) (field : View) (sourceLog : Log)
    (found : recover dummy history field = some sourceLog) :
    ∃ before offset values after, CausalStreamExposure.seen before (input field) = false ∧ values ≠ [] ∧
      history = before++ .output (input field) offset values :: after ∧ sourceLog = selectedLog dummy before field := by
  obtain ⟨before,first,equal⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨unseen,offset,values,after,positive,split⟩ := CausalFirstStreamPrefix.recover_sound _ history before first
  exact ⟨before,offset,values,after,unseen,positive,split,equal.symm⟩

theorem recover_snapshot (dummy : Digest) (history : List Observation) (field : View)
    (parsed : SingleOpeningFieldInputView.parse (input field) = some field) (sourceLog : Log)
    (found : recover dummy history field = some sourceLog) :
    ∀ index : Height, ⟨(field.data.context,index),⟨field.data.root,sourceLog⟩⟩ ∈
      (reconstructed dummy history).checkpoints.checkpoints := by
  obtain ⟨before,offset,values,after,_,positive,split,same⟩ := recover_sound dummy history field sourceLog found
  rw [split,same]
  exact selected_snapshot dummy before after _ field parsed offset values positive

theorem linked_field_parsed (columnInput : Input) (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse columnInput = some decoded) :
    SingleOpeningFieldInputView.parse (input decoded.field) = some decoded.field := by
  obtain ⟨column,_,linked⟩ := Option.bind_eq_some_iff.mp parsed
  have field := (SingleOpeningChallengeLink.readColumn_sound column decoded linked).2.2.1
  have same := (SingleOpeningFieldInputView.parse_sound _ decoded.field field (fun _ => 0)).1
  rw [SingleOpeningFieldInputView.phase_input] at same
  change input decoded.field = _ at same
  rw [same]
  exact field

/-- Use a specific earlier selected log for the actual accepted payloads;
no existential source log is chosen from the later acceptance. -/
theorem accepted_at_log {Memory : Type} (dummy context : Digest) (ctx : Context) (choose : Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (requests : List (NativeGoldColumnWorker.Job × Request height)) (computed : SingleOpeningAvailability.prepare context work = some requests)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history)
    (sourceLog : Log)
    (snapshots : ∀ index : Height, ⟨(context,index),⟨work.root,sourceLog⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints)
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history)) :
    ∀ entry ∈ requests,
      entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,sourceLog⟩ entry.2.position ∧
      NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
        (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,sourceLog⟩ entry.2.position) entry.2.position.val := by
  have noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (requests.map Prod.snd) (reconstructed dummy history) :=
    fun failure => noDisagreement (ParallelColumnAvailability.failure_implies_disagreement encoding dummy height _ _ failure)
  have spec := NativeGoldRawRequests.entries_spec height (SingleOpeningAvailability.tag context work) work.root work.jobs requests computed
  have each := SingleOpeningAvailability.accepted_replays context ctx choose fuel memory world work completion executed parent accepted requests computed history truthful observed
  intro entry member
  have recorded : ⟨entry.2.tag,⟨entry.2.root,sourceLog⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints := by
    obtain ⟨bound,leaf,siblings,_,same⟩ := NativeGoldRawRequests.fromJob_spec height (SingleOpeningAvailability.tag context work) work.root entry.1 entry.2 (spec.2 entry member)
    rw [same]
    exact snapshots (SingleOpeningAvailability.tag context work).2
  have replayed : ParallelColumnAvailability.Replays encoding height entry.2 (reconstructed dummy history).hash.cache := by
    rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
    exact (each entry member).1
  refine ⟨NativeGoldRawAvailability.payload_of_no_failure dummy height (requests.map Prod.snd) entry.2
    (List.mem_map.mpr ⟨entry,member,rfl⟩) (reconstructed dummy history) replayed ⟨entry.2.root,sourceLog⟩ recorded rfl noFailure,?_⟩
  exact NativeGoldRawAvailability.equations_of_no_failure dummy height (requests.map Prod.snd) entry.2
    (List.mem_map.mpr ⟨entry,member,rfl⟩) (reconstructed dummy history) replayed ⟨entry.2.root,sourceLog⟩ recorded rfl noFailure
    work.geometry work.width work.random work.structured work.test work.evaluation (each entry member).2

/-- An actually parsed field read fixes the source used by every later accepted
native column. The actual parameter context and root association are derived. -/
theorem accepted_selected {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    {sample : NativeIndexRequest.Result} (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (before after : List Observation) (field : View)
    (parsed : SingleOpeningFieldInputView.parse (SingleOpeningRandomLaw.phase receipt).pending.input = some field)
    (offset : ℕ) (values : Input) (positive : values ≠ [])
    (accepted : SingleOpeningAvailability.Accepted world
      (before++ .output (SingleOpeningRandomLaw.phase receipt).pending.input offset values :: after) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (before++ .output (SingleOpeningRandomLaw.phase receipt).pending.input offset values :: after))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape
      (reconstructed dummy (before++ .output (SingleOpeningRandomLaw.phase receipt).pending.input offset values :: after))) :
    ∃ requests : List (NativeGoldColumnWorker.Job × Request height),
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some field.data.context ∧
      SingleOpeningAvailability.prepare field.data.context work = some requests ∧
      (∀ index : Height, ⟨(field.data.context,index),⟨work.root,selectedLog dummy before field⟩⟩ ∈
        (reconstructed dummy (before++ .output (SingleOpeningRandomLaw.phase receipt).pending.input offset values :: after)).checkpoints.checkpoints) ∧
      ∀ entry ∈ requests,
        entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,selectedLog dummy before field⟩ entry.2.position ∧
        NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
          (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,selectedLog dummy before field⟩ entry.2.position) entry.2.position.val := by
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,next,executed,status,observed⟩ := accepted
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨context,hashed,native⟩ := SingleOpeningFieldInputView.receipt_parse receipt prepared frames parent valid fits
  have equal := Option.some.inj (parsed.symm.trans native)
  have contextEq : field.data.context = context := congrArg (fun value => value.data.context) equal
  have rootEq : field.data.root = work.root := by
    rw [equal]
    exact (NativeGoldPcsOpeningChecks.prepared_parameters ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
      ctx.opening ctx.fieldFuel world work prepared).2.2.symm
  obtain ⟨requests,computed⟩ := SingleOpeningAvailability.prepare_complete field.data.context ctx world work prepared
  have snapshots := selected_snapshot dummy before after _ field parsed offset values positive
  rw [rootEq] at snapshots
  refine ⟨requests,by rw [contextEq]; exact hashed,computed,snapshots,?_⟩
  exact accepted_at_log dummy field.data.context ctx choose fuel memory world work completion executed next status requests computed _ truthful observed
    (selectedLog dummy before field) snapshots noDisagreement

end
end FormalProof4FHE.HasteBoots.SingleOpeningFirstFieldSource
