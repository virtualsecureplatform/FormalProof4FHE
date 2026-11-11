module
public import FormalProof4FHE.HasteBoots.AllocatedBindingsData
@[expose] public section

/-! Every original registry slot's context computation occurs in a successful
native preparation and therefore in its actual enclosing allocated run. This
is complete-history coverage, not an assertion about an earlier prefix. -/
namespace FormalProof4FHE.HasteBoots.RegistryContextObservation
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription Parameters)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (Program run)
noncomputable section

theorem bind_left {A B : Type} (first : Program A) (next : A → Program B) (world : World) :
    (run first world).run.2.Sublist (run (OracleProgram.bind first next) world).run.2 := by
  rw [OracleProgram.run_bind,ObservationReplay.run_bind]
  exact List.sublist_append_left _ _

theorem contexts {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (world : World)
    (sources : List NativeCanonicalLookupWire.Source)
    (success : (run (NativeSharedLookupParent.contexts row registry) world).run.1 = some sources)
    (entry : Oracle C) (member : entry ∈ registry) :
    (run (NativeBrakedownContext.context row entry.parameters) world).run.2.Sublist
      (run (NativeSharedLookupParent.contexts row registry) world).run.2 := by
  induction registry generalizing sources with
  | nil => cases member
  | cons first rest ih =>
    simp only [NativeSharedLookupParent.contexts,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
    cases computed : (run (NativeBrakedownContext.context row first.parameters) world).run.1 with
    | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some digest =>
      simp only [computed,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil] at success ⊢
      rcases List.mem_cons.mp member with rfl | tail
      · exact List.sublist_append_left _ _
      · obtain ⟨remaining,found,_⟩ := Option.map_eq_some_iff.mp success
        exact (ih remaining found tail).trans (List.sublist_append_right _ _)

theorem register {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript) (world : World)
    (result : Transcript) (success : (run (NativeSharedLookupParent.register row registry parent) world).run.1 = some result) :
    (run (NativeSharedLookupParent.contexts row registry.val) world).run.2.Sublist
      (run (NativeSharedLookupParent.register row registry parent) world).run.2 := by
  unfold NativeSharedLookupParent.register at success ⊢
  split
  next empty => simp only [empty,ite_true,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  next nonempty => exact bind_left _ _ world

theorem prepare {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (world : World) (geometry : NativeSharedLookupPreflight.Output)
    (success : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 = some geometry) :
    (run (NativeSharedLookupParent.contexts row registry.val) world).run.2.Sublist
      (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.2 := by
  simp only [NativeSharedLookupParent.prepare,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
  cases pref : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 with
  | none => simp only [pref,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some output =>
    simp only [pref,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
    cases registered : (run (NativeSharedLookupParent.register row registry
        (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 with
    | none => simp only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some next =>
      have included := register row registry _ world next registered
      simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
      exact included.trans (List.sublist_append_right _ _)

theorem protocol {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result))
    (entry : Oracle C) (member : entry ∈ registry.val) :
    (run (NativeBrakedownContext.context row entry.parameters) world).run.2.Sublist
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2 := by
  obtain ⟨geometry,launched,began,_,_,_⟩ := NativeSharedLookupExecution.bound_origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  obtain ⟨g,l,_,prepared,_,_⟩ := NativeSharedLookupParent.begin_spec row registry helper parent requests proof lookupFuel equalityFuel world _ began
  obtain ⟨sources,computed,_⟩ := NativeRegistryAncestry.prepare_registered row registry helper parent requests world g prepared
  have inPrepare := (contexts row registry.val world sources.val computed entry member).trans (prepare row registry helper parent requests world g prepared)
  exact (inPrepare.trans (bind_left _ _ world)).trans (bind_left _ _ world)


theorem helper_frame {C : Type} (row : RowDescription C) (helper : Parameters C) (selected : List (Oracle C))
    (parent : Transcript) (request : Request) (world : World) (next : Transcript)
    (success : (run (NativeSharedLookupParent.frame row helper selected parent request) world).run.1 = some next) :
    (run (NativeBrakedownContext.context row helper) world).run.2.Sublist
      (run (NativeSharedLookupParent.frame row helper selected parent request) world).run.2 := by
  simp only [NativeSharedLookupParent.frame,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
  cases computed : (run (NativeSharedLookupParent.contexts row selected) world).run.1 with
  | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some sources =>
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)

theorem helper_step {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (request : Request) (world : World)
    (next : NativeSharedLookupPreflight.State)
    (success : (run (NativeSharedLookupParent.step row registry helper state parent request) world).run.1.2 = some next) :
    (run (NativeBrakedownContext.context row helper) world).run.2.Sublist
      (run (NativeSharedLookupParent.step row registry helper state parent request) world).run.2 := by
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
      | some after => exact (helper_frame row helper entries parent request world after framed).trans (List.sublist_append_left _ _)

theorem helper_preflight {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (world : World) (next : NativeSharedLookupPreflight.Output)
    (success : (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.1.2 = some next) :
    (run (NativeBrakedownContext.context row helper) world).run.2.Sublist
      (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.2 := by
  unfold NativeSharedLookupParent.preflight at success ⊢
  split
  next passed =>
    simp only [passed,ite_true,OracleProgram.run_bind,ObservationReplay.run_bind] at success
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    cases reqs : requests.val with
    | nil =>
      simp only [reqs,NativeSharedLookupParent.loop,OracleProgram.run,CanonicalTranscriptSampler.run_pure,
        NativeSharedLookupPreflight.initial,Option.bind_some,Option.map_none] at success
      contradiction
    | cons request rest =>
      simp only [reqs,NativeSharedLookupParent.loop,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
      cases stepped : (run (NativeSharedLookupParent.step row registry helper NativeSharedLookupPreflight.initial
          (NativeLookupRequestWire.bindRequests parent requests) request) world).run.1.2 with
      | none => simp only [stepped,OracleProgram.run,CanonicalTranscriptSampler.run_pure,Option.bind_none] at success; contradiction
      | some state =>
        exact ((helper_step row registry helper _ _ request world state stepped).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)
  next failed => simp only [failed] at success; contradiction

theorem helper_protocol {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    (run (NativeBrakedownContext.context row helper) world).run.2.Sublist
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2 := by
  obtain ⟨geometry,launched,began,_,_,_⟩ := NativeSharedLookupExecution.bound_origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  obtain ⟨g,l,_,prepared,_,_⟩ := NativeSharedLookupParent.begin_spec row registry helper parent requests proof lookupFuel equalityFuel world _ began
  have preflight := AllocatedBindingsData.preflight_of_prepare row registry helper parent requests world g prepared
  have inPrepare : (run (NativeBrakedownContext.context row helper) world).run.2.Sublist
      (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.2 :=
    (helper_preflight row registry.val helper parent requests world g preflight).trans (bind_left _ _ world)
  exact (inPrepare.trans (bind_left _ _ world)).trans (bind_left _ _ world)

end
end FormalProof4FHE.HasteBoots.RegistryContextObservation
