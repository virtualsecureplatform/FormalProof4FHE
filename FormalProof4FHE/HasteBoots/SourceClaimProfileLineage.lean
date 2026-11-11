module
public import FormalProof4FHE.HasteBoots.NativeSharedSourceClaims
@[expose] public section

/-! Claim insertion and batch sealing preserve the parent profile on success
and on every rejection, retaining original alias and slot decisions. -/
namespace FormalProof4FHE.HasteBoots.SourceClaimProfileLineage
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Request Row)
open NativeSharedSourceClaims (Progress)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem push_profile {C : Type} (registry : Vector (Oracle C)) (state : NativeDeferredOpeningBatch.State)
    (slot : NativeUsizeMessage.Usize) (query : Query) (values : Row) :
    (NativeDeferredOpeningBatch.push registry state slot query values).1.parent.profile = state.parent.profile := by
  unfold NativeDeferredOpeningBatch.push
  split
  · rfl
  · split_ifs <;> rfl

theorem seal_profile (state : NativeDeferredOpeningBatch.State) (packets : ℕ) :
    (NativeDeferredOpeningBatch.sealBatch state packets).1.parent.profile = state.parent.profile := by
  unfold NativeDeferredOpeningBatch.sealBatch
  split_ifs <;> rfl

theorem afterContext_profile {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) (context : Option NativeRootMessage.Digest) :
    (NativeSharedSourceClaims.afterContext registry query values slot before context).progress.state.parent.profile = before.state.parent.profile := by
  cases context with
  | none => rfl
  | some digest =>
    simp only [NativeSharedSourceClaims.afterContext]
    split
    · rfl
    · split
      · split <;> rfl
      · split <;> exact push_profile _ _ _ _ _

theorem step_profile {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World) :
    (run (NativeSharedSourceClaims.step row registry requests query values slot before) world).run.1.progress.state.parent.profile = before.state.parent.profile := by
  unfold NativeSharedSourceClaims.step
  split
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    exact afterContext_profile _ _ _ _ _ _
  · rfl

theorem loop_profile {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length)) (before : Progress) (world : World) :
    (run (NativeSharedSourceClaims.loop row registry requests query values slots before) world).run.1.progress.state.parent.profile = before.state.parent.profile := by
  induction slots generalizing before with
  | nil => rfl
  | cons slot rest ih =>
    simp only [NativeSharedSourceClaims.loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    have same := step_profile row registry requests query values slot before world
    cases current : (run (NativeSharedSourceClaims.step row registry requests query values slot before) world).run.1 with
    | stopped progress reason => simpa only [current,OracleProgram.run,CanonicalTranscriptSampler.run_pure] using same
    | done after => exact (ih after).trans (by simpa only [current,NativeSharedSourceClaims.Result.progress] using same)

theorem program_profile {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World) :
    (run (NativeSharedSourceClaims.program row registry requests query values state) world).run.1.progress.state.parent.profile = state.parent.profile :=
  loop_profile row registry requests query values _ ⟨state,[]⟩ world

end
end FormalProof4FHE.HasteBoots.SourceClaimProfileLineage
