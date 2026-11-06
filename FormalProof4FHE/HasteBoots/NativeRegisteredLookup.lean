module

public import FormalProof4FHE.HasteBoots.NativeSourceRegistry
@[expose] public section

/-! Retain original registry metadata through the actual lookup preparation,
child execution and helper loop. Erasure preserves the original result and
every oracle observation. No context is recomputed to recover metadata. -/
namespace FormalProof4FHE.HasteBoots.NativeRegisteredLookup
open InputIndexedOracle (World)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle models)
open NativeBrakedownContext (Parameters RowDescription)
open NativeTranscript (Transcript)
open NativeLookupRequestWire (Request)
open NativeSharedLookupProofData (Proof)
open NativeSourceRegistry (Initialized)
open OracleProgram (Program bind run)
noncomputable section

abbrev Registered := NativeSharedLookupPreflight.Output × Initialized

/-- Keep the metadata from the original initializer, before any child or helper challenge. -/
def prepare {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) : Program (Transcript × Option Registered) :=
  bind (NativeSharedLookupParent.preflight row registry.val helper parent requests) (fun (parent,geometry) => match geometry with
    | none => .pure (parent,none)
    | some geometry => bind (NativeSourceRegistry.startRegistry row registry parent) (fun initialized => match initialized with
      | none => .pure (parent,none)
      | some initialized => .pure (initialized.parent,some (geometry,initialized))))

theorem prepare_erasure {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (world : World) :
    (((run (prepare row registry helper parent requests) world).run.1.1,
        (run (prepare row registry helper parent requests) world).run.1.2.map Prod.fst),
      (run (prepare row registry helper parent requests) world).run.2) =
      (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run := by
  simp only [prepare,NativeSharedLookupParent.prepare,OracleProgram.run_bind,ObservationReplay.run_bind]
  cases numeric : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 with
  | none => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,Option.map_none]
  | some geometry =>
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    have erased := NativeSourceRegistry.initialize_erasure row registry
      (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1 world
    have value := congrArg Prod.fst erased
    have log := congrArg Prod.snd erased
    rw [← value,← log]
    cases (run (NativeSourceRegistry.startRegistry row registry
      (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 with
    | none => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,Option.map_none]
    | some initialized => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,Option.map_some]

/-- Returned metadata is from the actual initializer at the original preflight parent. -/
theorem prepare_origin {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (world : World)
    (geometry : NativeSharedLookupPreflight.Output) (metadata : Initialized)
    (executed : (run (prepare row registry helper parent requests) world).run.1.2 = some (geometry,metadata)) :
    (run (NativeSourceRegistry.startRegistry row registry
      (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 = some metadata ∧
      (run (prepare row registry helper parent requests) world).run.1.1 = metadata.parent ∧
      (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 = some geometry := by
  simp only [prepare,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
  cases numeric : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 with
  | none => simp only [numeric,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | some actual =>
    simp only [numeric,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
    cases registered : (run (NativeSourceRegistry.startRegistry row registry
      (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 with
    | none => simp only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | some initialized =>
      simp only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed ⊢
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj executed)
      exact ⟨rfl,rfl,rfl⟩

/-- Lookup/equality launch uses the same registered parent while preserving its original source metadata. -/
def begin {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel : ℕ) :
    Program (Option NativeSharedLookupExecution.Preparation × Option Initialized) :=
  bind (prepare row registry helper parent requests) (fun (parent,prepared) => match prepared with
    | none => .pure (none,none)
    | some (geometry,metadata) => bind (NativeSharedLookupChild.launch requests.property.le (models requests) .retain
        (registry.val.map Oracle.geometry) geometry proof lookupFuel equalityFuel parent)
      (fun launched => .pure (launched.map (fun ready => ⟨geometry,ready⟩),some metadata)))

theorem begin_erasure {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel : ℕ) (world : World) :
    ((run (begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1.1,
      (run (begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.2) =
      (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run := by
  simp only [begin,NativeSharedLookupParent.begin,OracleProgram.run_bind,ObservationReplay.run_bind]
  have erased := prepare_erasure row registry helper parent requests world
  have value := congrArg Prod.fst erased
  have parentEq := congrArg Prod.fst value
  have preparedEq := congrArg Prod.snd value
  have log := congrArg Prod.snd erased
  rw [← parentEq,← preparedEq,← log]
  cases (run (prepare row registry helper parent requests) world).run.1.2 with
  | none => simp only [Option.map_none,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
  | some prepared =>
    obtain ⟨geometry,metadata⟩ := prepared
    simp only [Option.map_some,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

/-- Successful launch retains the original registered metadata, rather than reconstructing it later. -/
theorem begin_metadata {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel : ℕ) (world : World)
    (prepared : NativeSharedLookupExecution.Preparation)
    (executed : (run (begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1.1 = some prepared) :
    ∃ metadata geometry,
      (run (begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1.2 = some metadata ∧
      (run (prepare row registry helper parent requests) world).run.1.2 = some (geometry,metadata) := by
  simp only [begin,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
  cases selected : (run (prepare row registry helper parent requests) world).run.1.2 with
  | none => simp only [selected,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | some actual =>
    obtain ⟨geometry,metadata⟩ := actual
    refine ⟨metadata,geometry,?_,rfl⟩
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

/-- The completed or rejected body retains metadata computed by the original registry initialization. -/
def protocol {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel scalarFuel : ℕ) :
    Program (Option NativeSharedLookupBody.Outcome × Option Initialized) :=
  bind (begin row registry helper parent requests proof lookupFuel equalityFuel) (fun (prepared,metadata) => match prepared with
    | none => .pure (none,metadata)
    | some prepared => bind (NativeSharedLookupExecution.continueBody registry requests proof scalarFuel prepared)
        (fun result => .pure (some result,metadata)))

theorem protocol_erasure {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) :
    ((run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1.1,
      (run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2) =
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run := by
  simp only [protocol,NativeSharedLookupExecution.protocol,OracleProgram.run_bind,ObservationReplay.run_bind]
  have erased := begin_erasure row registry helper parent requests proof lookupFuel equalityFuel world
  have value := congrArg Prod.fst erased
  have log := congrArg Prod.snd erased
  rw [← value,← log]
  cases (run (begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1.1 with
  | none => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure]
  | some prepared => simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

/-- Every returned body outcome retains the metadata established before launch. -/
theorem protocol_metadata {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel scalarFuel : ℕ) (world : World)
    (result : NativeSharedLookupBody.Outcome)
    (executed : (run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1.1 = some result) :
    ∃ metadata geometry,
      (run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1.2 = some metadata ∧
      (run (prepare row registry helper parent requests) world).run.1.2 = some (geometry,metadata) := by
  simp only [protocol,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
  cases selected : (run (begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1.1 with
  | none => simp only [selected,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | some prepared =>
    obtain ⟨metadata,geometry,retained,original⟩ := begin_metadata row registry helper parent requests proof lookupFuel equalityFuel world prepared selected
    refine ⟨metadata,geometry,?_,original⟩
    simp only [retained,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

/-- Existing helper verification receives the same body and handoff, with no later registry-context recomputation. -/
def helpers {B Memory : Type} (ctx : NativeGoldHelperVerification.Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) : Program (NativeGoldHelperVerification.Outcome Memory × Option Initialized) :=
  bind (protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel)
    (fun (body,metadata) =>
      let packet := (body,NativeSharedLookupHelpers.handoff ctx.helper.width ctx.proof body)
      match packet.1,packet.2 with
      | some (.bound result),some plan => bind
          (NativeGoldHelperVerification.loop ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel plan.calls ⟨result.parent,memory,[]⟩)
          (fun resultStatus => .pure (.helpers result plan resultStatus,metadata))
      | _,_ => .pure (.prior packet,metadata))

theorem helpers_erasure {B Memory : Type} (ctx : NativeGoldHelperVerification.Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) :
    ((run (helpers ctx choose memory) world).run.1.1,(run (helpers ctx choose memory) world).run.2) =
      (run (NativeGoldHelperVerification.program ctx choose memory) world).run := by
  simp only [helpers,NativeGoldHelperVerification.program,OracleProgram.run_bind,ObservationReplay.run_bind]
  have erased := protocol_erasure NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world
  have value := congrArg Prod.fst erased
  have log := congrArg Prod.snd erased
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol]
  rw [← value,← log]
  cases (run (protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1.1 with
  | none => simp only [NativeSharedLookupHelpers.handoff,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
  | some body =>
    cases body with
    | suspended machine => simp only [NativeSharedLookupHelpers.handoff,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    | rejected reason machine => simp only [NativeSharedLookupHelpers.handoff,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    | bound result =>
      cases NativeSharedLookupHelpers.handoff ctx.helper.width ctx.proof (some (.bound result)) with
      | none => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure]
      | some plan => simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
/-- Helper outcomes retain exactly the original registered metadata through every helper step. -/
theorem helpers_metadata {B Memory : Type} (ctx : NativeGoldHelperVerification.Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (result : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (helpers ctx choose memory) world).run.1.1 = .helpers result plan status) :
    ∃ metadata geometry,
      (run (helpers ctx choose memory) world).run.1.2 = some metadata ∧
      (run (prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.2 = some (geometry,metadata) := by
  simp only [helpers,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
  cases body : (run (protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1.1 with
  | none => simp only [body,NativeSharedLookupHelpers.handoff,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | some actual =>
    cases actual with
    | suspended machine => simp only [body,NativeSharedLookupHelpers.handoff,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | rejected reason machine => simp only [body,NativeSharedLookupHelpers.handoff,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | bound actual =>
      cases handoff : NativeSharedLookupHelpers.handoff ctx.helper.width ctx.proof (some (.bound actual)) with
      | none => simp only [body,handoff,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
      | some calls =>
        obtain ⟨metadata,geometry,retained,prepared⟩ := protocol_metadata NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
          ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world (.bound actual) body
        refine ⟨metadata,geometry,?_,prepared⟩
        simp only [retained,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

end
end FormalProof4FHE.HasteBoots.NativeRegisteredLookup
