module
public import FormalProof4FHE.HasteBoots.NativeSharedLookupExecution
@[expose] public section

/-! The shared lookup retains its original parent profile through context
registration, child launch and successful detached-child finish. This does
not require checkpoint injectivity or a scalar soundness assumption. -/
namespace FormalProof4FHE.HasteBoots.LookupProfileLineage
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle)
open NativeLookupRequestWire (Request)
open OracleProgram (run)
noncomputable section

theorem frame_profile {C : Type} (row : RowDescription C) (helper : Parameters C) (selected : List (Oracle C))
    (parent : Transcript) (request : Request) (world : World) (next : Transcript)
    (success : (run (NativeSharedLookupParent.frame row helper selected parent request) world).run.1 = some next) :
    next.profile = parent.profile := by
  simp only [NativeSharedLookupParent.frame,OracleProgram.run_bind,ObservationReplay.run_bind] at success
  split at success
  · contradiction
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind] at success
    split at success
    · contradiction
    · split at success
      · cases Option.some.inj success; rfl
      · contradiction

theorem step_profile {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (request : Request) (world : World) :
    (run (NativeSharedLookupParent.step row registry helper state parent request) world).run.1.1.profile = parent.profile := by
  unfold NativeSharedLookupParent.step
  split
  · rfl
  · split
    · rfl
    · simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
      split
      · rfl
      next next success =>
        have same := frame_profile row helper _ parent request world next success
        split
        · split <;> exact same
        · exact same

theorem loop_profile {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (requests : List Request) (world : World) :
    (run (NativeSharedLookupParent.loop row registry helper state parent requests) world).run.1.1.profile = parent.profile := by
  induction requests generalizing state parent with
  | nil => rfl
  | cons request rest ih =>
    simp only [NativeSharedLookupParent.loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    split
    · exact step_profile row registry helper state parent request world
    · exact (ih _ _).trans (step_profile row registry helper state parent request world)

theorem preflight_profile {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (world : World) :
    (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.1.1.profile = parent.profile := by
  unfold NativeSharedLookupParent.preflight
  split
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    exact loop_profile row registry helper _ _ requests.val world
  · rfl

theorem register_profile {C : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C))
    (parent : Transcript) (world : World) (next : Transcript)
    (success : (run (NativeSharedLookupParent.register row registry parent) world).run.1 = some next) :
    next.profile = parent.profile := by
  unfold NativeSharedLookupParent.register at success
  split at success
  · contradiction
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind] at success
    split at success
    · contradiction
    · split at success
      · cases Option.some.inj success; rfl
      · contradiction

theorem prepare_profile {C : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (world : World) :
    (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1.profile = parent.profile := by
  simp only [NativeSharedLookupParent.prepare,OracleProgram.run_bind,ObservationReplay.run_bind]
  split
  · exact preflight_profile row registry.val helper parent requests world
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    split
    · exact preflight_profile row registry.val helper parent requests world
    next next success =>
      exact (register_profile row registry _ world next success).trans (preflight_profile row registry.val helper parent requests world)

theorem finish_parent_profile (world : World) (parent : Transcript) (child : TypedTranscriptChild.Child) :
    ((TypedTranscriptChild.finishExecute world (some parent) child).1.parent.map Transcript.profile) = some parent.profile := by
  rcases child with ⟨bytes,binding⟩
  cases binding with
  | none => rfl
  | some binding =>
    cases bytes with
    | none => rfl
    | some bytes =>
      simp only [TypedTranscriptChild.finishExecute]
      split_ifs <;> rfl

theorem bound_profile {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    result.parent.profile = parent.profile := by
  obtain ⟨geometry,launched,_,_,executed,body⟩ := NativeSharedLookupExecution.bound_origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  have launch := NativeSharedLookupChild.launch_spec requests.property.le (NativeSharedLookupParent.models requests) .retain (registry.val.map Oracle.geometry)
    geometry proof lookupFuel equalityFuel _ world launched.1 launched.2 executed
  have contract := (NativeSharedLookupBody.body_bound (NativeSharedLookupParent.models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val
    launched.1 launched.2 proof scalarFuel world result body).2
  have retained := finish_parent_profile world launched.1.parent ⟨some (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof),some launched.1.binding⟩
  have finished := contract.finished
  rw [NativeSharedLookupBody.finish,NativeSharedLookupChild.finish,TypedTranscriptChild.run_finish] at finished
  rw [finished] at retained
  have profile := Option.some.inj retained
  rw [launch.1] at profile
  exact profile.trans (prepare_profile row registry helper parent requests world)

end
end FormalProof4FHE.HasteBoots.LookupProfileLineage
