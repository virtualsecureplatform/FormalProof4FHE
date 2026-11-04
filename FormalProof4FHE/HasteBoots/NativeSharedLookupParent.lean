module

public import FormalProof4FHE.HasteBoots.NativeBrakedownContext
public import FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire
public import FormalProof4FHE.HasteBoots.NativeSharedLookupChild

@[expose] public section

/-!
# Ordered native shared-lookup parent preflight

For already rebuilt trusted requests, execute each numeric bind, compute
selected contexts and helper context, append the bind tuple, then check
common geometry and checked repetition addition. Errors retain the actual
parent prefix. Registry construction recomputes all source contexts before
absorbing the ordered registry. This is the Goldilocks Brakedown branch.
Trusted row-code serialization/parameter validity, alias-group construction,
full child-body orchestration and PCS authentication remain separate.
-/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupParent

open NativeBrakedownContext (Parameters RowDescription)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeLookupRequestWire (Request)
open NativeSharedLookupPreflight (State Output)
open OracleProgram (Program bind run)

structure Oracle (Code : Type) where
  parameters : Parameters Code
  root : NativeRootMessage.Digest

def Oracle.geometry {C : Type} (oracle : Oracle C) : NativeLookupBindGeometry.Parameters := oracle.parameters.geometry

def gather {C : Type} (registry : List (Oracle C)) : List ℕ → Option (List (Oracle C))
  | [] => some []
  | slot :: tail => registry[slot]?.bind (fun source => (gather registry tail).map (fun rest => source :: rest))

def contexts {C : Type} (row : RowDescription C) : List (Oracle C) → Program (Option (List NativeCanonicalLookupWire.Source))
  | [] => .pure (some [])
  | source :: tail => bind (NativeBrakedownContext.context row source.parameters) (fun context =>
    match context with
    | none => .pure none
    | some digest => bind (contexts row tail) (fun rest => .pure (rest.map (fun rest => (digest,source.root) :: rest))))

/-- No frame is emitted until every source and helper context succeeds. -/
def frame {C : Type} (row : RowDescription C) (helper : Parameters C) (selected : List (Oracle C))
    (parent : Transcript) (request : Request) : Program (Option Transcript) :=
  bind (contexts row selected) (fun sources =>
    match sources with
    | none => .pure none
    | some sources => bind (NativeBrakedownContext.context row helper) (fun helper =>
      match helper with
      | none => .pure none
      | some helper =>
        if fits : sources.length < 2^64 then
          .pure (some (NativeCanonicalLookupWire.bind parent ⟨request.config,helper,⟨sources,fits⟩⟩))
        else .pure none))

def step {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : State) (parent : Transcript) (request : Request) : Program (Transcript × Option State) :=
  match gather registry request.toModel.terminal.sourceSlots with
  | none => .pure (parent,none)
  | some selected =>
    match NativeLookupBindGeometry.bind request.toModel.columns request.toModel.terminal.logicalLength helper.geometry (selected.map Oracle.geometry) with
    | none => .pure (parent,none)
    | some geometry => bind (frame row helper selected parent request) (fun framed =>
      match framed with
      | none => .pure (parent,none)
      | some nextParent =>
        if NativeSharedLookupPreflight.agrees state.geometry (NativeSharedLookupPreflight.key geometry) then
          match NativeSharedLookupPreflight.addRepetitions state.repetitions request.toModel.repetitions with
          | none => .pure (nextParent,none)
          | some count => .pure (nextParent,some ⟨some (NativeSharedLookupPreflight.key geometry),count,
              state.bindings ++ [⟨request.toModel,selected.map Oracle.geometry,geometry⟩]⟩)
        else .pure (nextParent,none))

def loop {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C) :
    State → Transcript → List Request → Program (Transcript × Option State)
  | state,parent,[] => .pure (parent,some state)
  | state,parent,request :: tail => bind (step row registry helper state parent request) (fun (parent,next) =>
    match next with
    | none => .pure (parent,none)
    | some next => loop row registry helper next parent tail)

def preflight {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) : Program (Transcript × Option Output) :=
  if NativeSharedLookupPreflight.registryDimensions (registry.map Oracle.geometry) (requests.val.map Request.toModel) &&
      NativeSharedLookupPreflight.uniform (registry.map Oracle.geometry) then
    bind (loop row registry helper NativeSharedLookupPreflight.initial (NativeLookupRequestWire.bindRequests parent requests) requests.val)
      (fun (parent,state) => .pure (parent,state.bind (fun state => state.geometry.map (fun geometry =>
        ⟨geometry,state.repetitions,state.bindings⟩))))
  else .pure (parent,none)

/-- Native CanonicalOpeningBatch::new recomputes every registry context.
The grouping of aliases does not add a transcript message. -/
def register {C : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C))
    (parent : Transcript) : Program (Option Transcript) :=
  if registry.val = [] then .pure none else
    bind (contexts row registry.val) (fun sources =>
      match sources with
      | none => .pure none
      | some sources =>
        if fits : sources.length < 2^64 then .pure (some (NativeCanonicalLookupWire.registry parent ⟨sources,fits⟩)) else .pure none)

def prepare {C : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) : Program (Transcript × Option Output) :=
  bind (preflight row registry.val helper parent requests) (fun (parent,result) =>
    match result with
    | none => .pure (parent,none)
    | some result => bind (register row registry parent) (fun registered =>
      match registered with
      | none => .pure (parent,none)
      | some next => .pure (next,some result)))

theorem gather_geometry {C : Type} (registry : List (Oracle C)) (slots : List ℕ) :
    (gather registry slots).map (List.map Oracle.geometry) = NativeSharedLookupPreflight.gather (registry.map Oracle.geometry) slots := by
  induction slots with
  | nil => rfl
  | cons slot tail ih =>
    simp only [gather,NativeSharedLookupPreflight.gather,List.getElem?_map]
    cases found : registry[slot]? <;> simp only [Option.map_none,Option.bind_none,Option.map_some,Option.bind_some]
    rw [← ih]
    cases gather registry tail <;> rfl

/-- A successful framed step erases to the existing numeric step on the
same original request and selected sources. -/
theorem step_numeric {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state next : State) (parent : Transcript) (request : Request) (world : World)
    (success : (run (step row registry helper state parent request) world).run.1.2 = some next) :
    NativeSharedLookupPreflight.step (registry.map Oracle.geometry) helper.geometry state request.toModel = some next := by
  unfold step at success
  cases selected : gather registry request.toModel.terminal.sourceSlots with
  | none => simp only [selected,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some selectedSources =>
    have gathered := gather_geometry registry request.toModel.terminal.sourceSlots
    rw [selected,Option.map_some] at gathered
    unfold NativeSharedLookupPreflight.step
    rw [← gathered,Option.bind_some]
    cases geometry : NativeLookupBindGeometry.bind request.toModel.columns request.toModel.terminal.logicalLength helper.geometry (selectedSources.map Oracle.geometry) with
    | none => simp only [selected,geometry,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some geometry =>
      simp only [selected,geometry,OracleProgram.run_bind,ObservationReplay.run_bind] at success
      cases framed : (run (frame row helper selectedSources parent request) world).run.1 with
      | none => simp only [framed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
      | some framedParent =>
        simp only [framed] at success
        split at success
        next agreed =>
          rw [Option.bind_some,ite_eq_left agreed]
          cases added : NativeSharedLookupPreflight.addRepetitions state.repetitions request.toModel.repetitions with
          | none => simp only [added,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
          | some count =>
            simp only [added,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
            simpa only [added,Option.map_some] using success
        next disagreed => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction

theorem loop_numeric {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (requests : List Request) (state next : State) (parent : Transcript) (world : World)
    (success : (run (loop row registry helper state parent requests) world).run.1.2 = some next) :
    NativeSharedLookupPreflight.loop (registry.map Oracle.geometry) helper.geometry state (requests.map Request.toModel) = some next := by
  induction requests generalizing state parent with
  | nil => exact success
  | cons request tail ih =>
    simp only [loop,OracleProgram.run_bind,ObservationReplay.run_bind] at success
    cases executed : (run (step row registry helper state parent request) world).run.1.2 with
    | none => simp only [executed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some intermediate =>
      simp only [executed] at success
      have numeric := step_numeric row registry helper state intermediate parent request world executed
      simp only [List.map_cons,NativeSharedLookupPreflight.loop,numeric,Option.bind_some]
      exact ih intermediate (run (step row registry helper state parent request) world).run.1.1 success

theorem preflight_numeric {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (world : World) (output : Output)
    (success : (run (preflight row registry helper parent requests) world).run.1.2 = some output) :
    NativeSharedLookupPreflight.preflight (registry.map Oracle.geometry) helper.geometry (requests.val.map Request.toModel) = some output := by
  unfold preflight at success
  split at success
  next dimensions =>
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
    obtain ⟨state,completed,result⟩ := Option.bind_eq_some_iff.mp success
    have numeric := loop_numeric row registry helper requests.val NativeSharedLookupPreflight.initial state
      (NativeLookupRequestWire.bindRequests parent requests) world completed
    simp only [NativeSharedLookupPreflight.preflight,dimensions,ite_true,numeric,Option.bind_some]
    exact result
  next rejected => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction

theorem prepare_numeric {C : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (world : World) (output : Output)
    (success : (run (prepare row registry helper parent requests) world).run.1.2 = some output) :
    NativeSharedLookupPreflight.preflight (registry.val.map Oracle.geometry) helper.geometry (requests.val.map Request.toModel) = some output := by
  simp only [prepare,OracleProgram.run_bind,ObservationReplay.run_bind] at success
  cases pref : (run (preflight row registry.val helper parent requests) world).run.1.2 with
  | none => simp only [pref,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some result =>
    simp only [pref,OracleProgram.run_bind,ObservationReplay.run_bind] at success
    cases registered : (run (register row registry (run (preflight row registry.val helper parent requests) world).run.1.1) world).run.1 with
    | none => simp only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some finalParent =>
      simp only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
      have same := Option.some.inj success
      subst output
      exact preflight_numeric row registry.val helper parent requests world result pref

theorem contexts_length {C : Type} (row : RowDescription C) (sources : List (Oracle C)) (world : World)
    (result : List NativeCanonicalLookupWire.Source)
    (success : (run (contexts row sources) world).run.1 = some result) : result.length = sources.length := by
  induction sources generalizing result with
  | nil => have same := Option.some.inj success; subst result; rfl
  | cons source tail ih =>
    simp only [contexts,OracleProgram.run_bind,ObservationReplay.run_bind] at success
    cases computed : (run (NativeBrakedownContext.context row source.parameters) world).run.1 with
    | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some digest =>
      simp only [computed,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
      obtain ⟨rest,remaining,same⟩ := Option.map_eq_some_iff.mp success
      rw [← same,List.length_cons,ih rest remaining,List.length_cons]

/-- The original ordered typed request list determines the finite request
family passed into the existing child launcher. -/
def models (requests : NativePrefixCodec.Vector Request) : Fin requests.val.length → NativeSharedLookupStatement.Request :=
  fun index => (requests.val[index.val]).toModel

theorem models_list (requests : NativePrefixCodec.Vector Request) : List.ofFn (models requests) = requests.val.map Request.toModel := by
  change List.ofFn (Request.toModel ∘ fun index : Fin requests.val.length => requests.val[index.val]) = _
  rw [← List.map_ofFn,List.ofFn_getElem]

noncomputable section

def begin {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request)
    (proof : NativeSharedLookupProofData.Proof S B) (lookupFuel equalityFuel : ℕ) :
    Program (Option (Σ geometry : Output, NativeSharedLookupChild.State × NativeSharedLookupPrelude.Ready geometry.geometry.1.val)) :=
  bind (prepare row registry helper parent requests) (fun (parent,result) =>
    match result with
    | none => .pure none
    | some geometry => bind (NativeSharedLookupChild.launch requests.property.le (models requests) .retain
        (registry.val.map Oracle.geometry) geometry proof lookupFuel equalityFuel parent)
      (fun launched => .pure (launched.map (fun ready => ⟨geometry,ready⟩))))

/-- Success comes from the actual framed/registered parent and actual child
launcher, with numeric geometry derived from that same preparation. -/
theorem begin_spec {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request)
    (proof : NativeSharedLookupProofData.Proof S B) (lookupFuel equalityFuel : ℕ) (world : World)
    (result : Σ geometry : Output, NativeSharedLookupChild.State × NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1 = some result) :
    ∃ geometry launched, result = ⟨geometry,launched⟩ ∧
      (run (prepare row registry helper parent requests) world).run.1.2 = some geometry ∧
      NativeSharedLookupPreflight.preflight (registry.val.map Oracle.geometry) helper.geometry (List.ofFn (models requests)) = some geometry ∧
      (run (NativeSharedLookupChild.launch requests.property.le (models requests) .retain (registry.val.map Oracle.geometry)
        geometry proof lookupFuel equalityFuel (run (prepare row registry helper parent requests) world).run.1.1) world).run.1 = some launched := by
  simp only [begin,OracleProgram.run_bind,ObservationReplay.run_bind] at success
  cases prepared : (run (prepare row registry helper parent requests) world).run.1.2 with
  | none => simp only [prepared,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some geometry =>
    simp only [prepared,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
    obtain ⟨launched,executed,same⟩ := Option.map_eq_some_iff.mp success
    refine ⟨geometry,launched,same.symm,rfl,?_,executed⟩
    rw [models_list]
    exact prepare_numeric row registry helper parent requests world geometry prepared

/-- Rebuilt public configurations and success of the actual parent/child
entry point discharge scalar preflight on the same algebra proof. -/
theorem begin_beginVerify {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request)
    (original : List NativeSharedLookupStatement.Request)
    (rebuilt : NativeSharedLookupConfig.rebuild .retain original = some (List.ofFn (models requests)))
    (proof : NativeSharedLookupProofData.Proof S B) (lookupFuel equalityFuel : ℕ) (world : World)
    (result : Σ geometry : Output, NativeSharedLookupChild.State × NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1 = some result)
    (shape : NativeScalarBatchPreflight.proofShape result.2.2.statement proof.algebra = true) :
    NativeScalarBatchPreflight.beginVerify result.2.2.equality.transcript result.2.2.statement proof.algebra =
      .ok (NativeScalarBatchWire.bindStatement result.2.2.equality.transcript result.2.2.statement) := by
  obtain ⟨geometry,launched,same,_,numeric,executed⟩ := begin_spec row registry helper parent requests proof lookupFuel equalityFuel world result success
  subst result
  exact NativeSharedLookupChild.launch_beginVerify requests.property.le (models requests) .retain original rebuilt
    (registry.val.map Oracle.geometry) helper.geometry geometry numeric proof lookupFuel equalityFuel
    (run (prepare row registry helper parent requests) world).run.1.1 world launched.1 launched.2 executed shape

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupParent
