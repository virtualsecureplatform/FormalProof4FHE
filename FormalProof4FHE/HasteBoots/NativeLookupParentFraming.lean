module

public import FormalProof4FHE.HasteBoots.NativeCanonicalMessageBounds
import all Init.Data.String.Defs
@[expose] public section

/-! The original parent preflight preserves framed ancestry on successful
and rejected numeric/context branches. All size bounds are on original
request/configuration bytes and selected slot counts, before any oracle answer. -/
namespace FormalProof4FHE.HasteBoots.NativeLookupParentFraming
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription Parameters)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def FrameFits {C : Type} (selected : List (Oracle C)) (request : Request) : Prop :=
  (NativeLookupRequestWire.configCodec.encode request.config).length + 65 + (9 + 128 * selected.length) < TranscriptFrame.lengthLimit

def CallsFit {C : Type} (registry : List (Oracle C)) (requests : List Request) : Prop :=
  ∀ request ∈ requests, ∀ selected, NativeSharedLookupParent.gather registry request.toModel.terminal.sourceSlots = some selected → FrameFits selected request

def Domain {C : Type} (registry : List (Oracle C)) (requests : Vector Request) : Prop :=
  (NativeLookupRequestWire.requestsCodec.encode requests).length < TranscriptFrame.lengthLimit ∧ CallsFit registry requests.val

theorem frame {C : Type} (row : RowDescription C) (helper : Parameters C) (selected : List (Oracle C))
    (parent : Transcript) (request : Request) (world : World) (next : Transcript)
    (success : (run (NativeSharedLookupParent.frame row helper selected parent request) world).run.1 = some next)
    (fits : FrameFits selected request) : Extends parent next := by
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
      next count =>
        have same := Option.some.inj success
        rw [← same]
        apply NativeCanonicalMessageBounds.bind_extension
        change (NativeLookupRequestWire.configCodec.encode request.config).length + 65 + (9 + 128 * sources.length) < _
        rw [NativeCanonicalMessageBounds.contexts_length row selected world sources contexts]
        exact fits
      next => contradiction

theorem step {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (request : Request) (world : World)
    (fits : CallsFit registry [request]) :
    Extends parent (run (NativeSharedLookupParent.step row registry helper state parent request) world).run.1.1 := by
  unfold NativeSharedLookupParent.step
  cases selected : NativeSharedLookupParent.gather registry request.toModel.terminal.sourceSlots with
  | none => exact Extends.refl _
  | some entries =>
    simp only []
    cases geometry : NativeLookupBindGeometry.bind request.toModel.columns request.toModel.terminal.logicalLength helper.geometry (entries.map Oracle.geometry) with
    | none => exact Extends.refl _
    | some geometry =>
      simp only []
      simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
      cases framed : (run (NativeSharedLookupParent.frame row helper entries parent request) world).run.1 with
      | none => exact Extends.refl _
      | some next =>
        have extended := frame row helper entries parent request world next framed (fits request (by simp) entries selected)
        simp only []
        split
        · cases NativeSharedLookupPreflight.addRepetitions state.repetitions request.toModel.repetitions <;> exact extended
        · exact extended

theorem loop {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (requests : List Request) (world : World)
    (fits : CallsFit registry requests) :
    Extends parent (run (NativeSharedLookupParent.loop row registry helper state parent requests) world).run.1.1 := by
  induction requests generalizing state parent with
  | nil => exact Extends.refl _
  | cons request rest ih =>
    have first := step row registry helper state parent request world (fun selected member => fits selected (by rcases List.mem_singleton.mp member with rfl; exact List.mem_cons_self))
    simp only [NativeSharedLookupParent.loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    cases updated : (run (NativeSharedLookupParent.step row registry helper state parent request) world).run.1.2 with
    | none => exact first
    | some next =>
      exact first.trans (ih next _ (fun selected member => fits selected (List.mem_cons_of_mem request member)))

theorem preflight {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (world : World) (domain : Domain registry requests) :
    Extends parent (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.1.1 := by
  unfold NativeSharedLookupParent.preflight
  split
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    apply Extends.trans ?_ (loop row registry helper NativeSharedLookupPreflight.initial _ requests.val world domain.2)
    apply NativeTranscriptExtension.absorb parent 1 NativeLookupRequestWire.requestsLabel _
    exact ⟨by change NativeLookupRequestWire.requestsLabel.length < _; decide +kernel,domain.1⟩
  · exact Extends.refl _

theorem register {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript)
    (world : World) (next : Transcript)
    (success : (run (NativeSharedLookupParent.register row registry parent) world).run.1 = some next)
    (fits : 9 + 128 * registry.val.length < TranscriptFrame.lengthLimit) : Extends parent next := by
  obtain ⟨sources,computed,rfl⟩ := NativeRegistryAncestry.register_spec row registry parent world next success
  apply NativeCanonicalMessageBounds.registry_extension
  rw [NativeCanonicalMessageBounds.contexts_length row registry.val world sources.val computed]
  exact fits

theorem prepared {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (world : World)
    (domain : Domain registry.val requests) (registryFits : 9 + 128 * registry.val.length < TranscriptFrame.lengthLimit) :
    Extends parent (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 := by
  have earlier := preflight row registry.val helper parent requests world domain
  simp only [NativeSharedLookupParent.prepare,OracleProgram.run_bind,ObservationReplay.run_bind]
  cases numeric : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 with
  | none => exact earlier
  | some geometry =>
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    cases registered : (run (NativeSharedLookupParent.register row registry (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 with
    | none => exact earlier
    | some next => exact earlier.trans (register row registry _ world next registered registryFits)
end
end FormalProof4FHE.HasteBoots.NativeLookupParentFraming
