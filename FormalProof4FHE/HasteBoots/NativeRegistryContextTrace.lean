module
public import FormalProof4FHE.HasteBoots.NativeSourceRegistry
@[expose] public section

/-! Context executions of every original registry slot are included in the
successful initializer trace. This includes unused entries and repeated aliases;
no filtered registry or independent context execution is supplied as evidence. -/
namespace FormalProof4FHE.HasteBoots.NativeRegistryContextTrace
open InputIndexedOracle (World)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript)
open OracleProgram (run)
noncomputable section

theorem contexts_member {C : Type} (row : RowDescription C) (registry : List (Oracle C))
    (world : World) (sources : List NativeCanonicalLookupWire.Source)
    (success : (run (NativeSharedLookupParent.contexts row registry) world).run.1 = some sources)
    (entry : Oracle C) (member : entry ∈ registry) :
    (run (NativeBrakedownContext.context row entry.parameters) world).run.2.Sublist
      (run (NativeSharedLookupParent.contexts row registry) world).run.2 := by
  induction registry generalizing sources with
  | nil => simp only [List.not_mem_nil] at member
  | cons head tail ih =>
    simp only [NativeSharedLookupParent.contexts,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
    cases computed : (run (NativeBrakedownContext.context row head.parameters) world).run.1 with
    | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some digest =>
      simp only [computed,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,
        CanonicalTranscriptSampler.run_pure,List.append_nil] at success ⊢
      obtain ⟨rest,remaining,_⟩ := Option.map_eq_some_iff.mp success
      rcases List.mem_cons.mp member with same | later
      · subst entry
        exact List.sublist_append_left _ _
      · exact (ih rest remaining later).trans (List.sublist_append_right _ _)

theorem initialized_slot {C : Type} (row : RowDescription C) (registry : Vector (Oracle C))
    (parent : Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry row registry parent) world).run.1 = some initialized)
    (slot : Fin registry.val.length) :
    (run (NativeBrakedownContext.context row (registry.val.get slot).parameters) world).run.2.Sublist
      (run (NativeSourceRegistry.startRegistry row registry parent) world).run.2 := by
  have origin := NativeSourceRegistry.initialized_origin row registry parent world initialized executed
  rw [origin.2.2.2]
  exact contexts_member row registry.val world initialized.sources.val origin.2.1
    (registry.val.get slot) (List.get_mem _ _)

end
end FormalProof4FHE.HasteBoots.NativeRegistryContextTrace
