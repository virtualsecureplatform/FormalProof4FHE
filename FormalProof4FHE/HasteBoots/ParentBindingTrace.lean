module
public import FormalProof4FHE.HasteBoots.NativeLookupParentFraming
import all Init.Data.String.Defs
@[expose] public section

/-! Successful native preflight emits one literal canonical binding per
original request, in order. Each binding retains the request configuration,
helper context and original gathered slot sequence. -/
namespace FormalProof4FHE.HasteBoots.ParentBindingTrace
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription Parameters)
open NativeLookupRequestWire (Request)
open NativeCanonicalLookupWire (Binding)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def frame (binding : Binding) : TranscriptFrame.Frame := ⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩

def ForRequest {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (world : World) (request : Request) (binding : Binding) : Prop :=
  ∃ selected, NativeSharedLookupParent.gather registry request.toModel.terminal.sourceSlots = some selected ∧
    binding.config = request.config ∧
    (run (NativeBrakedownContext.context row helper) world).run.1 = some binding.helper ∧
    (run (NativeSharedLookupParent.contexts row selected) world).run.1 = some binding.sources.val

theorem frame_origin {C : Type} (row : RowDescription C) (helper : Parameters C) (selected : List (Oracle C))
    (parent : Transcript) (request : Request) (world : World) (next : Transcript)
    (success : (run (NativeSharedLookupParent.frame row helper selected parent request) world).run.1 = some next) :
    ∃ binding : Binding, next = NativeCanonicalLookupWire.bind parent binding ∧ binding.config = request.config ∧
      (run (NativeBrakedownContext.context row helper) world).run.1 = some binding.helper ∧
      (run (NativeSharedLookupParent.contexts row selected) world).run.1 = some binding.sources.val := by
  simp only [NativeSharedLookupParent.frame,OracleProgram.run_bind,ObservationReplay.run_bind] at success
  cases contexts : (run (NativeSharedLookupParent.contexts row selected) world).run.1 with
  | none => simp only [contexts,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some sources =>
    simp only [contexts,OracleProgram.run_bind,ObservationReplay.run_bind] at success
    cases helperContext : (run (NativeBrakedownContext.context row helper) world).run.1 with
    | none => simp only [helperContext,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some digest =>
      simp only [helperContext] at success
      split at success
      next fits => exact ⟨⟨request.config,digest,⟨sources,fits⟩⟩,(Option.some.inj success).symm,rfl,rfl,rfl⟩
      next => contradiction

theorem step {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (request : Request) (world : World)
    (next : NativeSharedLookupPreflight.State)
    (success : (run (NativeSharedLookupParent.step row registry helper state parent request) world).run.1.2 = some next) :
    ∃ binding : Binding, ForRequest row registry helper world request binding ∧
      (run (NativeSharedLookupParent.step row registry helper state parent request) world).run.1.1 = NativeCanonicalLookupWire.bind parent binding := by
  unfold NativeSharedLookupParent.step at success ⊢
  cases selected : NativeSharedLookupParent.gather registry request.toModel.terminal.sourceSlots with
  | none => simp only [selected,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some entries =>
    simp only [selected] at success ⊢
    cases geometry : NativeLookupBindGeometry.bind request.toModel.columns request.toModel.terminal.logicalLength helper.geometry (entries.map Oracle.geometry) with
    | none => simp only [geometry,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some geometry =>
      simp only [geometry,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
      cases framed : (run (NativeSharedLookupParent.frame row helper entries parent request) world).run.1 with
      | none => simp only [framed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
      | some after =>
        obtain ⟨binding,same,config,helperContext,contexts⟩ := frame_origin row helper entries parent request world after framed
        refine ⟨binding,⟨entries,selected,config,helperContext,contexts⟩,?_⟩
        simp only []
        split
        · cases NativeSharedLookupPreflight.addRepetitions state.repetitions request.toModel.repetitions <;> exact same
        · exact same

theorem loop {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (requests : List Request) (world : World)
    (next : NativeSharedLookupPreflight.State)
    (success : (run (NativeSharedLookupParent.loop row registry helper state parent requests) world).run.1.2 = some next) :
    ∃ bindings : List Binding, List.Forall₂ (ForRequest row registry helper world) requests bindings ∧
      (run (NativeSharedLookupParent.loop row registry helper state parent requests) world).run.1.1.input =
        parent.input ++ TranscriptFrame.encodeMany (bindings.map frame) := by
  induction requests generalizing state parent with
  | nil => exact ⟨[],.nil,(List.append_nil _).symm⟩
  | cons request rest ih =>
    simp only [NativeSharedLookupParent.loop,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
    cases updated : (run (NativeSharedLookupParent.step row registry helper state parent request) world).run.1.2 with
    | none => simp only [updated,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some after =>
      obtain ⟨binding,related,first⟩ := step row registry helper state parent request world after updated
      obtain ⟨bindings,relations,bytes⟩ := ih after _ (by simpa only [updated] using success)
      refine ⟨binding::bindings,.cons related relations,?_⟩
      simp only []
      rw [bytes,first,NativeCanonicalLookupWire.bind_input]
      simp only [List.map_cons,TranscriptFrame.encodeMany,frame,List.append_assoc]

/-- The successful preflight prefix consists of the original request vector
frame followed by exactly its own binding sequence. -/
theorem preflight {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (world : World) (next : NativeSharedLookupPreflight.Output)
    (success : (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.1.2 = some next) :
    ∃ bindings : List Binding, List.Forall₂ (ForRequest row registry helper world) requests.val bindings ∧
      (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.1.1.input =
        (NativeLookupRequestWire.bindRequests parent requests).input ++ TranscriptFrame.encodeMany (bindings.map frame) := by
  unfold NativeSharedLookupParent.preflight at success ⊢
  split
  next passed =>
    simp only [passed,ite_true] at success
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
    cases finished : (run (NativeSharedLookupParent.loop row registry helper NativeSharedLookupPreflight.initial
      (NativeLookupRequestWire.bindRequests parent requests) requests.val) world).run.1.2 with
    | none => simp only [finished,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some after =>
      obtain ⟨bindings,relations,bytes⟩ := loop row registry helper NativeSharedLookupPreflight.initial _ requests.val world after finished
      exact ⟨bindings,relations,bytes⟩
  next failed => simp only [failed] at success; contradiction

theorem binding_valid {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (world : World) (request : Request) (binding : Binding) (related : ForRequest row registry helper world request binding)
    (fits : NativeLookupParentFraming.CallsFit registry [request]) : TranscriptFrame.Valid (frame binding) := by
  obtain ⟨selected,gathered,config,_,contexts⟩ := related
  constructor
  · change NativeCanonicalLookupWire.label.length < _
    unfold NativeCanonicalLookupWire.label NativeTranscript.utf8
    decide +kernel
  · apply lt_of_le_of_lt (NativeCanonicalMessageBounds.payload_length binding)
    rw [config,NativeCanonicalMessageBounds.contexts_length row selected world binding.sources.val contexts]
    exact fits request (by simp) selected gathered

end
end FormalProof4FHE.HasteBoots.ParentBindingTrace
