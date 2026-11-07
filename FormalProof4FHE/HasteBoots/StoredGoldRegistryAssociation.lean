module
public import FormalProof4FHE.HasteBoots.NativeRegistryContextTrace
public import FormalProof4FHE.HasteBoots.StoredRegistryOwnerCost
public import FormalProof4FHE.HasteBoots.ObservedGoldFieldExtraction
public import FormalProof4FHE.HasteBoots.StoredSourceVectorCost
public import FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
@[expose] public section

/-! The measured complete-key owner lookup selects the actual first original
registry entry. Context evidence comes from that initializer's own trace.
The stored registry must still be related to the actual computed source vector;
this module does not supply a native wire/physical dispatcher refinement. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldRegistryAssociation
open InputIndexedOracle (Input Byte World)
open NativeSharedLookupParent (Oracle)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript Observation)
open StoredSourceVectorReadCost (Sources view sourceView)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem original_owner (registry : Vector (Oracle NativeGoldBlockCode.Stored)) (parent : Transcript)
    (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (sources : Sources) (retained : view sources = initialized.sources) (index : Fin sources.val.length) :
    ∃ original : Fin registry.val.length,
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧
      original.val ≤ index.val ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (registry.val.get original).parameters) world).run.1 =
        some (sources.val.get index).1.get ∧
      (registry.val.get original).root = (sources.val.get index).2.get ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (registry.val.get original).parameters) world).run.2.Sublist
        (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2 := by
  rcases initialized with ⟨nativeSources,nativeParent⟩
  dsimp only at retained
  subst nativeSources
  let initialized : NativeSourceRegistry.Initialized := ⟨view sources,nativeParent⟩
  let position := StoredRegistryOwnerCost.position sources index
  obtain ⟨original,selected,before,computed,root⟩ := NativeSourceRegistry.initialized_owner
    NativeGoldBlockCode.description.row registry parent world initialized executed position
  have sameOwner : (NativeSourceRegistry.owner initialized.sources position).val =
      (NativeSourceRegistry.owner (view sources) (StoredRegistryOwnerCost.position sources index)).val := by
    rfl
  have sameSource : initialized.sources.val.get position = sourceView (sources.val.get index) := by
    exact StoredRegistryOwnerCost.view_get sources index
  refine ⟨original,?_,before,?_,?_,?_⟩
  · rw [StoredRegistryOwnerCost.owner_value,selected,sameOwner]
  · simpa only [sameSource,sourceView] using computed
  · simpa only [sameSource,sourceView] using root
  · exact NativeRegistryContextTrace.initialized_slot NativeGoldBlockCode.description.row registry parent world initialized executed original

theorem extraction_original_parameters (registry : Vector (Oracle NativeGoldBlockCode.Stored)) (parent : Transcript)
    (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (sources : Sources) (retained : view sources = initialized.sources) (index : Fin sources.val.length)
    (history : List Observation) (included : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2.Sublist history)
    (input : Input) (dummy : Vector Byte 64) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index)
    (truthful : ObservationReplay.Agrees world history)
    (noCollision : ¬OracleComp.CacheHasCollision (JointHashCache.project history).cache) :
    ∃ original : Fin registry.val.length,
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧
      original.val ≤ index.val ∧ ctx.parameters = (registry.val.get original).parameters ∧
      (registry.val.get original).root = output.1.data.source.2.get := by
  obtain ⟨original,selected,before,computed,root,trace⟩ := original_owner registry parent world initialized executed sources retained index
  refine ⟨original,selected,before,?_,?_⟩
  · apply ObservedGoldFieldExtraction.parameters_eq_native_initializer history input dummy ctx radius output accepted
      (registry.val.get original).parameters world truthful
    · simpa only [key] using computed
    · exact trace.trans included
    · exact noCollision
  · simpa only [key] using root

/-- The stored registry relation is derived by decoding the actual initializer's
complete source-vector bytes, preserving all original positions and aliases. -/
theorem decoded_sources (initialized : NativeSourceRegistry.Initialized) (sources : Sources)
    (decoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources) :
    view sources = initialized.sources := by
  have native := StoredSourceVectorCost.decode_value (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)
  rw [decoded,Option.map_some,NativeExactCodec.read_encode] at native
  exact Option.some.inj native

/-- Collision exclusion uses the existing persistent source/hash bad event. -/
theorem no_collision_of_not_bad (dummy : NativeRootMessage.Digest) (history : List Observation)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy history) :
    ¬OracleComp.CacheHasCollision (JointHashCache.project history).cache := by
  rw [← NativeGoldBatchFamilyAvailability.reconstructed_hash dummy history]
  exact fun collision => safe (Or.inr collision)

theorem extraction_decoded_original (registry : Vector (Oracle NativeGoldBlockCode.Stored)) (parent : Transcript)
    (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (sources : Sources)
    (decoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (history : List Observation)
    (included : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2.Sublist history)
    (input : Input) (dummy : Vector Byte 64) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index)
    (truthful : ObservationReplay.Agrees world history)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history) :
    ∃ original : Fin registry.val.length,
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧
      original.val ≤ index.val ∧ ctx.parameters = (registry.val.get original).parameters ∧
      (registry.val.get original).root = output.1.data.source.2.get :=
  extraction_original_parameters registry parent world initialized executed sources
    (decoded_sources initialized sources decoded) index history included input dummy ctx radius output accepted key truthful
    (no_collision_of_not_bad dummy.get history safe)

/-- Successful preparation supplies the initializer's included trace itself. -/
theorem extraction_prepared_original (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (helper : StoredGoldContextEncodingCost.Parameters) (parent : Transcript)
    (requests : Vector NativeLookupRequestWire.Request) (world : World)
    (geometry : NativeSharedLookupPreflight.Output)
    (prepared : (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row registry helper parent requests) world).run.1.2 = some geometry)
    (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry
      (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row registry.val helper parent requests) world).run.1.1) world).run.1 = some initialized)
    (sources : Sources)
    (decoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (history : List Observation)
    (included : (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row registry helper parent requests) world).run.2.Sublist history)
    (input : Input) (dummy : Vector Byte 64) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index)
    (truthful : ObservationReplay.Agrees world history)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history) :
    ∃ original : Fin registry.val.length,
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧
      original.val ≤ index.val ∧ ctx.parameters = (registry.val.get original).parameters ∧
      (registry.val.get original).root = output.1.data.source.2.get := by
  obtain ⟨actual,annotated,_,trace⟩ := NativeSourceRegistry.prepared_metadata
    NativeGoldBlockCode.description.row registry helper parent requests world geometry prepared
  have same := Option.some.inj (annotated.symm.trans executed)
  subst actual
  exact extraction_decoded_original registry _ world initialized executed sources decoded index history
    (trace.trans included) input dummy ctx radius output accepted key truthful safe

end
end FormalProof4FHE.HasteBoots.StoredGoldRegistryAssociation
