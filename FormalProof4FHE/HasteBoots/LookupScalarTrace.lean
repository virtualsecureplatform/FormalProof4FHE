module
public import FormalProof4FHE.HasteBoots.LookupExecutionOrigin
public import FormalProof4FHE.HasteBoots.ScalarReadExposure
@[expose] public section

/-! The native caller's recovered original scalar execution is an actual
segment of its raw log. Completed-record exposure witnesses therefore survive
embedding in the caller or an arbitrary containing raw history. -/
namespace FormalProof4FHE.HasteBoots.LookupScalarTrace
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (World)
open NativeSharedLookupBody (Bound)
open LookupExecutionOrigin (Origin)
open OracleProgram (run)
noncomputable section

variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : Bound}

def Logged (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result) : Prop :=
  (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
    (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).2.Sublist
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2

theorem recover (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    ∃ origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result, Logged origin := by
  obtain ⟨geometry,launched,began,preflight,executed,body⟩ := NativeSharedLookupExecution.bound_origin row registry helper parent requests proof
    lookupFuel equalityFuel scalarFuel world result success
  have launch := NativeSharedLookupChild.launch_spec requests.property.le (models requests) .retain (registry.val.map Oracle.geometry)
    geometry proof lookupFuel equalityFuel (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1
    world launched.1 launched.2 executed
  have contract := NativeSharedLookupBody.body_bound (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val
    launched.1 launched.2 proof scalarFuel world result body
  have completed := contract.2.scalar
  rw [contract.1] at completed
  let origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result :=
    ⟨geometry,preflight,launched.2,launch.2.2.2,LookupExecutionOrigin.shape_complete _ _ _ _ _ launch.2.1,completed,contract.2.guarded,contract.2.source⟩
  have scalarLog : (NativeScalarBatchVerifier.execute launched.2.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial launched.2.equality.transcript launched.2.statement proof.algebra) world).2.Sublist
      (run (NativeSharedLookupBody.body (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val launched.1 launched.2 proof scalarFuel) world).run.2 := by
    rw [NativeSharedLookupBody.run_body]
    exact List.sublist_append_left _ _
  have bodyLog : (run (NativeSharedLookupBody.body (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val launched.1 launched.2 proof scalarFuel) world).run.2.Sublist
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2 := by
    simp only [NativeSharedLookupExecution.run_protocol,began]
    exact List.sublist_append_right _ _
  exact ⟨origin,scalarLog.trans bodyLog⟩

/-- Recovery is functional: preflight fixes the geometry and native prelude
execution fixes the ready state. All remaining origin fields are propositions. -/
theorem origin_unique (left right : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result) : left = right := by
  rcases left with ⟨leftGeometry,leftNumeric,leftReady,leftPrepared,leftShape,leftScalar,leftGuard,leftSource⟩
  rcases right with ⟨rightGeometry,rightNumeric,rightReady,rightPrepared,rightShape,rightScalar,rightGuard,rightSource⟩
  have sameGeometry := Option.some.inj (leftNumeric.symm.trans rightNumeric)
  subst rightGeometry
  have sameReady := Option.some.inj (leftPrepared.symm.trans rightPrepared)
  subst rightReady
  rfl

theorem logged_of_success (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    Logged origin := by
  obtain ⟨actual,logged⟩ := recover row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  exact origin_unique actual origin ▸ logged

/-- The containing history may have earlier positive reads of the same input.
The result is an actual occurrence; no freshness or native-first assumption is made. -/
theorem completed_in (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (history : List Observation)
    (observed : (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).2.Sublist history)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ∃ position offset : ℕ, history[position]? = some (Observation.output entry.coefficients.phase.pending.input offset
      (InputIndexedOracle.bytes world entry.coefficients.phase.pending.input offset 8)) := by
  obtain ⟨position,offset,atPosition⟩ := ScalarReadExposure.completed origin.ready.equality.transcript origin.ready.statement proof.algebra scalarFuel world entry member
  have retained := observed.subset (List.mem_of_getElem? atPosition)
  obtain ⟨index,same⟩ := List.mem_iff_get.mp retained
  exact ⟨index.val,offset,(List.getElem?_eq_getElem index.isLt).trans (congrArg some same)⟩

end
end FormalProof4FHE.HasteBoots.LookupScalarTrace
