module
public import FormalProof4FHE.HasteBoots.CheckedBatchMetadataSize
@[expose] public section

/-! Original source-claim pushes emit bounded frames when their literal
binding check succeeds. Parameter initialization and existing profile widths
supply the required header bounds; no future source-parent frames are inputs. -/
namespace FormalProof4FHE.HasteBoots.AllocatedSourceClaimFraming
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row Request)
open NativeTranscriptExtension (Extends)
open NativeSharedSourceClaims (Progress)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def RegistrySmall {C : Type} (registry : Vector (Oracle C)) : Prop :=
  ∀ slot : Fin registry.val.length, (registry.val.get slot).parameters.width.val ≤ 4 ∧
    (registry.val.get slot).parameters.numVariables.val < 64

theorem checked_fits {C : Type} (parameters : NativeBrakedownContext.Parameters C) (query : Query) (values : Row)
    (small : parameters.width.val ≤ 4 ∧ parameters.numVariables.val < 64)
    (checked : NativeGoldPcsBinding.check parameters query values = true) : NativeSourceClaimFraming.Fits query values := by
  have bound := CheckedPcsMetadataSize.opening_length parameters (fun _ => 0) query values small.1 small.2 checked
  rw [NativeGoldPcsWire.opening_encode] at bound
  simp only [List.length_append,List.length_ofFn] at bound
  apply lt_of_le_of_lt (show 18+(NativeGoldPcsWire.queryCodec.encode query).length+
    (NativeLookupRequestWire.rowCodec.encode values).length ≤ 20548 from by omega)
    (by decide +kernel : 20548 < TranscriptFrame.lengthLimit)

theorem push_extension {C : Type} (registry : Vector (Oracle C)) (small : RegistrySmall registry)
    (state : NativeDeferredOpeningBatch.State) (slot : NativeUsizeMessage.Usize) (query : Query) (values : Row) :
    Extends state.parent (NativeDeferredOpeningBatch.push registry state slot query values).1.parent := by
  cases found : registry.val[slot.val]? with
  | none =>
    simp only [NativeDeferredOpeningBatch.push,found]
    exact Extends.refl _
  | some oracle =>
    by_cases checked : NativeGoldPcsBinding.check oracle.parameters query values = true
    · obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp found
      have bounds : oracle.parameters.width.val ≤ 4 ∧ oracle.parameters.numVariables.val < 64 := by
        simpa only [List.get_eq_getElem,same] using small ⟨slot.val,inside⟩
      exact NativeSourceClaimFraming.push_extension registry state slot query values (checked_fits oracle.parameters query values bounds checked)
    · simp only [NativeDeferredOpeningBatch.push,found,checked]
      exact Extends.refl _

theorem after_context {C : Type} (registry : Vector (Oracle C)) (small : RegistrySmall registry)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress)
    (context : Option NativeRootMessage.Digest) :
    Extends before.state.parent (NativeSharedSourceClaims.afterContext registry query values slot before context).progress.state.parent := by
  cases context with
  | none => exact Extends.refl _
  | some digest =>
    simp only [NativeSharedSourceClaims.afterContext]
    split
    · exact Extends.refl _
    next row found =>
      split
      · split <;> exact Extends.refl _
      · have extended := push_extension registry small before.state ⟨slot.val,lt_of_lt_of_le slot.isLt registry.property.le⟩ query row
        split <;> exact extended

theorem step {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (small : RegistrySmall registry)
    (requests : Vector Request) (query : Query) (values : Vector Row) (slot : Fin registry.val.length)
    (before : Progress) (world : World) :
    Extends before.state.parent (run (NativeSharedSourceClaims.step description registry requests query values slot before) world).run.1.progress.state.parent := by
  unfold NativeSharedSourceClaims.step
  split
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    exact after_context registry small query values slot before _
  · exact Extends.refl _

theorem loop {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (small : RegistrySmall registry)
    (requests : Vector Request) (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length))
    (before : Progress) (world : World) :
    Extends before.state.parent (run (NativeSharedSourceClaims.loop description registry requests query values slots before) world).run.1.progress.state.parent := by
  induction slots generalizing before with
  | nil => exact Extends.refl _
  | cons slot rest ih =>
    have extended := step description registry small requests query values slot before world
    simp only [NativeSharedSourceClaims.loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    cases outcome : (run (NativeSharedSourceClaims.step description registry requests query values slot before) world).run.1 with
    | stopped progress reason => simpa only [outcome,OracleProgram.run,CanonicalTranscriptSampler.run_pure,NativeSharedSourceClaims.Result.progress] using extended
    | done after =>
      have first : Extends before.state.parent after.state.parent := by
        simpa only [outcome,NativeSharedSourceClaims.Result.progress] using extended
      exact first.trans (ih after)

theorem program {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (small : RegistrySmall registry)
    (requests : Vector Request) (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World) :
    Extends state.parent (run (NativeSharedSourceClaims.program description registry requests query values state) world).run.1.progress.state.parent :=
  loop description registry small requests query values _ ⟨state,[]⟩ world

theorem allocated_small {ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening)}
    (allocation : AllocatedFamilyFunctions.Allocation ctx)
    (widths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4) :
    RegistrySmall ctx.registry := by
  have collected := (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1
  intro slot
  obtain ⟨geometry,built⟩ := NativeGoldParameterStore.registry_geometry allocation.entries allocation.reachable allocation.references ctx.registry collected slot
  exact ⟨widths slot,(NativeBrakedownParameters.build_spec NativeGoldBlockCode.description _ geometry built).basic.2.2.1⟩

end
end FormalProof4FHE.HasteBoots.AllocatedSourceClaimFraming
