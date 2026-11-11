module
public import FormalProof4FHE.HasteBoots.LookupScalarTrace
public import FormalProof4FHE.HasteBoots.LookupPreludeReceiptLogs
@[expose] public section

/-! The original lookup/EQ prelude is an actual segment of the complete native
caller log. Recovery is functional, so the inclusion applies to the original
job view already used by the arithmetic and receipt-binding reductions. -/
namespace FormalProof4FHE.HasteBoots.LookupPreludeTrace
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeSharedLookupParent (Oracle models)
open OracleProgram (run)
noncomputable section

theorem launch_log {S B : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → NativeSharedLookupStatement.Request)
    (policy : NativeSharedLookupValues.Policy) (registry : List NativeLookupBindGeometry.Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (proof : NativeSharedLookupProofData.Proof S B) (lookupFuel equalityFuel : ℕ) (parent : Transcript) (world : World)
    (state : NativeSharedLookupChild.State) (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (NativeSharedLookupChild.launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run.1 = some (state,ready)) :
    (run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 proof.values.multiplicities proof.values.roots proof.roots.property
      7 lookupFuel equalityFuel (NativeSharedLookupChild.startExecute world parent proof.multiplicities).1.2) world).run.2.Sublist
      (run (NativeSharedLookupChild.launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run.2 := by
  cases checked : NativeSharedLookupValidated.checks policy registry (List.ofFn requests) geometry proof.helperOpenings.val.length proof.values with
  | false =>
    rw [NativeSharedLookupChild.launch_rejected fits requests policy registry geometry proof lookupFuel equalityFuel parent world checked] at success
    contradiction
  | true =>
    change List.Sublist _ (run (NativeSharedLookupValidated.withChildState fits requests policy registry geometry proof.helperOpenings.val.length proof.values proof.roots.property
      7 lookupFuel equalityFuel (NativeSharedLookupChild.start parent proof.multiplicities)) world).run.2
    rw [NativeSharedLookupValidated.withChildState_accepted fits requests policy registry geometry proof.helperOpenings.val.length proof.values proof.roots.property
      7 lookupFuel equalityFuel (NativeSharedLookupChild.start parent proof.multiplicities) world checked,NativeSharedLookupChild.run_start]
    exact List.sublist_append_right _ _

open NativeBrakedownContext (RowDescription Parameters)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open LookupExecutionOrigin (Origin childStart)
variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : NativeSharedLookupBody.Bound}

def Logged (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result) : Prop :=
  (run (NativeSharedLookupPrelude.protocol requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world)) world).run.2.Sublist
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2

theorem recover (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    ∃ origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result, Logged origin := by
  obtain ⟨geometry,launched,began,numeric,executed,body⟩ := NativeSharedLookupExecution.bound_origin row registry helper parent requests proof
    lookupFuel equalityFuel scalarFuel world result success
  have launch := NativeSharedLookupChild.launch_spec requests.property.le (models requests) .retain (registry.val.map Oracle.geometry)
    geometry proof lookupFuel equalityFuel (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1
    world launched.1 launched.2 executed
  have contract := NativeSharedLookupBody.body_bound (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val
    launched.1 launched.2 proof scalarFuel world result body
  have completed := contract.2.scalar
  rw [contract.1] at completed
  let origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result :=
    ⟨geometry,numeric,launched.2,launch.2.2.2,LookupExecutionOrigin.shape_complete _ _ _ _ _ launch.2.1,completed,contract.2.guarded,contract.2.source⟩
  have prepared : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 = some geometry := by
    have original := began
    simp only [NativeSharedLookupParent.begin,OracleProgram.run_bind,ObservationReplay.run_bind] at original
    cases found : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 with
    | none => simp only [found,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at original; contradiction
    | some actual =>
      simp only [found,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at original
      obtain ⟨value,_,same⟩ := Option.map_eq_some_iff.mp original
      have equal : actual = geometry := congrArg Sigma.fst same
      rw [← equal]
  have launchInBegin :
      (run (NativeSharedLookupChild.launch requests.property.le (models requests) .retain (registry.val.map Oracle.geometry) geometry proof lookupFuel equalityFuel
        (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1) world).run.2.Sublist
      (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.2 := by
    simp only [NativeSharedLookupParent.begin,OracleProgram.run_bind,ObservationReplay.run_bind,prepared,
      OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
    exact List.sublist_append_right _ _
  have beginInCaller : (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.2.Sublist
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2 := by
    rw [NativeSharedLookupExecution.run_protocol]
    dsimp only
    rw [began]
    exact List.sublist_append_left _ _
  have retained := launch_log requests.property.le (models requests) .retain (registry.val.map Oracle.geometry) geometry proof lookupFuel equalityFuel
    (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 world launched.1 launched.2 executed
  exact ⟨origin,retained.trans (launchInBegin.trans beginInCaller)⟩

theorem logged_of_success (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) : Logged origin := by
  obtain ⟨actual,logged⟩ := recover row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  exact LookupScalarTrace.origin_unique actual origin ▸ logged

/-- Every retained original lookup draw has its actual receipt observations
inside the complete native caller log. -/
theorem lookup_reads (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result))
    (completed : NativeLookupBatch.Completed NativeFields.goldilocksModulus NativeExtensionFields.Goldilocks3)
    (member : completed ∈ (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
        (childStart row registry helper parent requests proof world)) world).1.completed) :
    LookupReceiptLogs.Reads world completed.selection.draws
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2 := by
  have reads := (LookupPreludeReceiptLogs.protocol requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared).1 completed member
  exact LookupReceiptLogs.mono world _ _ _ reads (logged_of_success origin success)

/-- All original equality points retain their native receipt observations. -/
theorem equality_reads (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    EqualityReceiptLogs.Reads world origin.ready.machine.draws
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2 := by
  have reads := (LookupPreludeReceiptLogs.protocol requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared).2
  exact fun draw member => (reads draw member).trans (logged_of_success origin success)

end
end FormalProof4FHE.HasteBoots.LookupPreludeTrace
