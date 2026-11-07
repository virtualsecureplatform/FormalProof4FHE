/-! Accepted modeled field associations reach actual original source reads.
Causal histories include initialization and arbitrary prequeries/continuations;
misassociation is covered by the existing joint persistent bad event. This is
an ideal-oracle association reduction, not native initializer/heap/physical-work
or complete protocol refinement. -/
namespace HasteBootsExtractedRegistryAssociation
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedRegistryDecode (Source Model decode root)
open HasteBootsExtractedRegistry (registry registry_slot)
open HasteBootsExtractedParametersDecode (decodeParameters)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (Input Byte World)
open OracleProgram (Program bind run)
open formalproof4fhe_native_registry_fixture (registry_get)

structure Setup (S : Type) where
  localState : S
  source : Slice Source
  parent : Transcript

abbrev Ready := NativePrefixCodec.Vector Model × NativeSourceRegistry.Initialized
abbrev State (S : Type) := Setup S × Option Ready

def initRegistry {S : Type} (setup : Setup S) : Program (Option Ready) :=
  match registry setup.source with
  | none => .pure none
  | some models => bind (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models setup.parent)
      (fun initialized => .pure (initialized.map (fun initialized => (models,initialized))))

def prelude {S : Type} (prior : Program (Setup S)) : Program (State S) :=
  bind prior (fun setup => bind (initRegistry setup) (fun initialized => .pure (setup,initialized)))

def history {S A : Type} (prior : Program (Setup S))
    (step : State S → OracleMachine.Command (State S) A) (fuel : ℕ) (world : World) : List Observation :=
  (run (NativeRootFamilyLifetime.program (prelude prior) step fuel) world).run.2

theorem initialization_run {S : Type} (setup : Setup S) (world : World) :
    (run (initRegistry setup) world).run =
      match registry setup.source with
      | none => (none,[])
      | some models =>
        let result := (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models setup.parent) world).run
        (result.1.map (fun initialized => (models,initialized)),result.2) := by
  cases decoded : registry setup.source <;>
    simp only [initRegistry,decoded,OracleProgram.run_bind,ObservationReplay.run_bind,
      OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem initialization_origin {S : Type} (setup : Setup S) (world : World)
    (models : NativePrefixCodec.Vector Model) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (initRegistry setup) world).run.1 = some (models,initialized)) :
    registry setup.source = some models ∧
      (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models setup.parent) world).run.1 = some initialized ∧
      (run (initRegistry setup) world).run.2 =
        (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models setup.parent) world).run.2 := by
  rw [initialization_run] at executed
  cases decoded : registry setup.source with
  | none => simp only [decoded] at executed; cases executed
  | some actual =>
    simp only [decoded] at executed
    cases started : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row actual setup.parent) world).run.1 with
    | none => simp only [started,Option.map_none] at executed; cases executed
    | some result =>
      simp only [started,Option.map_some] at executed
      have same := Prod.mk.inj (Option.some.inj executed)
      cases same.1
      cases same.2
      exact ⟨rfl,started,by rw [initialization_run,decoded]⟩

theorem prelude_run {S : Type} (prior : Program (Setup S)) (world : World) :
    (run (prelude prior) world).run =
      let setup := (run prior world).run.1
      let initialized := (run (initRegistry setup) world).run
      ((setup,initialized.1),(run prior world).run.2 ++ initialized.2) := by
  simp only [prelude,OracleProgram.run_bind,ObservationReplay.run_bind,
    OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem prelude_origin {S : Type} (prior : Program (Setup S)) (world : World) (setup : Setup S)
    (models : NativePrefixCodec.Vector Model) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (prelude prior) world).run.1 = (setup,some (models,initialized))) :
    registry setup.source = some models ∧
      (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models setup.parent) world).run.1 = some initialized ∧
      (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models setup.parent) world).run.2.Sublist
        (run (prelude prior) world).run.2 := by
  rw [prelude_run] at executed
  have setupEq := congrArg Prod.fst executed
  have initializedEq := congrArg Prod.snd executed
  dsimp only at setupEq initializedEq
  rw [setupEq] at initializedEq
  obtain ⟨decoded,started,trace⟩ := initialization_origin setup world models initialized initializedEq
  refine ⟨decoded,started,?_⟩
  rw [prelude_run]
  change (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models setup.parent) world).run.2.Sublist
    ((run prior world).run.2 ++ (run (initRegistry ((run prior world).run.1)) world).run.2)
  rw [setupEq,trace]
  exact List.sublist_append_right _ _

theorem prelude_included {S A : Type} (prior : Program (Setup S))
    (step : State S → OracleMachine.Command (State S) A) (fuel : ℕ) (world : World) :
    (run (prelude prior) world).run.2.Sublist (history prior step fuel world) := by
  unfold history NativeRootFamilyLifetime.program
  rw [OracleProgram.run_bind,ObservationReplay.run_bind]
  exact List.sublist_append_left _ _

def Origin (source : Slice Source) (models : NativePrefixCodec.Vector Model)
    (sources : StoredSourceVectorReadCost.Sources) (index : Fin sources.val.length)
    (ctx : NativeGoldBatchPcsProgram.Context) (expectedRoot : NativeRootMessage.Digest) : Prop :=
  ∃ (original : Fin models.val.length) (word : Usize) (entry : Source),
    (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧ original.val ≤ index.val ∧
    word.val = original.val ∧ registry_get source word = .ok (some (entry.parameters,entry.commitment.root)) ∧
    decode entry = some (models.val.get original) ∧
    decodeParameters entry.parameters = some ctx.parameters ∧ root entry.commitment.root = expectedRoot

theorem extraction_original (source : Slice Source) (models : NativePrefixCodec.Vector Model)
    (sourceDecoded : registry source = some models) (parent : Transcript) (world : World)
    (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.1 = some initialized)
    (sources : StoredSourceVectorReadCost.Sources)
    (storedDecoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (log : List Observation)
    (included : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.2.Sublist log)
    (input : Input) (dummy : Vector InputIndexedOracle.Byte 64) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run log input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index) (truthful : ObservationReplay.Agrees world log)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get log) :
    Origin source models sources index ctx output.1.data.source.2.get := by
  obtain ⟨original,selected,before,parameters,rootEq⟩ := StoredGoldRegistryAssociation.extraction_decoded_original
    models parent world initialized executed sources storedDecoded index log included input dummy ctx radius output accepted key truthful safe
  obtain ⟨word,entry,wordValue,read,entryDecoded⟩ := registry_slot source models sourceDecoded original
  have fields := HasteBootsExtractedRegistryDecode.decode_fields entry (models.val.get original) entryDecoded
  refine ⟨original,word,entry,selected,before,wordValue,read,entryDecoded,?_,fields.2.symm.trans rootEq⟩
  rw [parameters]
  exact fields.1

theorem extraction_bad_or_original {S A : Type} (prior : Program (Setup S))
    (step : State S → OracleMachine.Command (State S) A) (fuel : ℕ) (world : World)
    (setup : Setup S) (models : NativePrefixCodec.Vector Model) (initialized : NativeSourceRegistry.Initialized)
    (started : (run (prelude prior) world).run.1 = (setup,some (models,initialized)))
    (sources : StoredSourceVectorReadCost.Sources)
    (storedDecoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (input : Input) (dummy : Vector InputIndexedOracle.Byte 64)
    (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run (history prior step fuel world) input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index) :
    NativeRootFamilyLifetime.Bad dummy.get (history prior step fuel world) ∨
      Origin setup.source models sources index ctx output.1.data.source.2.get := by
  classical
  by_cases bad : NativeRootFamilyLifetime.Bad dummy.get (history prior step fuel world)
  · exact Or.inl bad
  · obtain ⟨decoded,startedRegistry,trace⟩ := prelude_origin prior world setup models initialized started
    exact Or.inr (extraction_original setup.source models decoded setup.parent world initialized startedRegistry sources storedDecoded index
      (history prior step fuel world) (trace.trans (prelude_included prior step fuel world)) input dummy ctx radius output accepted key
      ((OracleProgram.run_replay _).truthful world) bad)

def Misassociation {S A : Type} (prior : Program (Setup S))
    (step : State S → OracleMachine.Command (State S) A) (fuel : ℕ) (dummy : Vector InputIndexedOracle.Byte 64) (world : World) : Prop :=
  ∃ (setup : Setup S) (models : NativePrefixCodec.Vector Model) (initialized : NativeSourceRegistry.Initialized)
    (sources : StoredSourceVectorReadCost.Sources) (index : Fin sources.val.length)
    (input : Input) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ), ∃ output,
    (run (prelude prior) world).run.1 = (setup,some (models,initialized)) ∧
    (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources ∧
    (ObservedGoldFieldExtraction.run (history prior step fuel world) input dummy ctx radius).value = some output ∧
    output.1.data.source = sources.val.get index ∧
    ¬Origin setup.source models sources index ctx output.1.data.source.2.get

theorem misassociation_bad {S A : Type} (prior : Program (Setup S))
    (step : State S → OracleMachine.Command (State S) A) (fuel : ℕ) (dummy : Vector InputIndexedOracle.Byte 64) (world : World)
    (failed : Misassociation prior step fuel dummy world) :
    NativeRootFamilyLifetime.Bad dummy.get (history prior step fuel world) := by
  obtain ⟨setup,models,initialized,sources,index,input,ctx,radius,output,started,stored,accepted,key,missing⟩ := failed
  rcases extraction_bad_or_original prior step fuel world setup models initialized started sources stored index input dummy ctx radius
    output accepted key with bad | original
  · exact bad
  · exact False.elim (missing original)

theorem lifetime_misassociation_le_charge {S A : Type} (prior : Program (Setup S))
    (step : State S → OracleMachine.Command (State S) A) (dummy : Vector InputIndexedOracle.Byte 64) :
    InputIndexedOracle.law {world | ∃ fuel, Misassociation prior step fuel dummy world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy.get (prelude prior) step fuel := by
  apply le_trans (MeasureTheory.measure_mono ?_)
    (NativeRootFamilyLifetime.lifetime_bad_le_charge dummy.get (prelude prior) step)
  rintro world ⟨fuel,failed⟩
  exact ⟨fuel,misassociation_bad prior step fuel dummy world failed⟩

theorem extraction_in_program_bad_or_original {A : Type} (program : Program A) (world : World)
    (source : Slice Source) (models : NativePrefixCodec.Vector Model) (sourceDecoded : registry source = some models)
    (parent : Transcript) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.1 = some initialized)
    (sources : StoredSourceVectorReadCost.Sources)
    (storedDecoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length)
    (included : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.2.Sublist
      (run program world).run.2)
    (input : Input) (dummy : Vector InputIndexedOracle.Byte 64)
    (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run (run program world).run.2 input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index) :
    NativeRootFamilyLifetime.Bad dummy.get (run program world).run.2 ∨
      Origin source models sources index ctx output.1.data.source.2.get := by
  classical
  by_cases bad : NativeRootFamilyLifetime.Bad dummy.get (run program world).run.2
  · exact Or.inl bad
  · exact Or.inr (extraction_original source models sourceDecoded parent world initialized executed sources storedDecoded
      index (run program world).run.2 included input dummy ctx radius output accepted key
      ((OracleProgram.run_replay program).truthful world) bad)

/-- One complete shared history covers every matching initializer/field witness. -/
def TraceMisassociation {A : Type} (program : Program A) (dummy : Vector InputIndexedOracle.Byte 64) (world : World) : Prop :=
  ∃ (source : Slice Source) (models : NativePrefixCodec.Vector Model) (parent : Transcript)
    (initialized : NativeSourceRegistry.Initialized) (sources : StoredSourceVectorReadCost.Sources)
    (index : Fin sources.val.length) (input : Input) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ), ∃ output,
    registry source = some models ∧
    (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.1 = some initialized ∧
    (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.2.Sublist (run program world).run.2 ∧
    (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources ∧
    (ObservedGoldFieldExtraction.run (run program world).run.2 input dummy ctx radius).value = some output ∧
    output.1.data.source = sources.val.get index ∧
    ¬Origin source models sources index ctx output.1.data.source.2.get

theorem trace_misassociation_bad {A : Type} (program : Program A) (dummy : Vector InputIndexedOracle.Byte 64)
    (world : World) (failed : TraceMisassociation program dummy world) :
    NativeRootFamilyLifetime.Bad dummy.get (run program world).run.2 := by
  obtain ⟨source,models,parent,initialized,sources,index,input,ctx,radius,output,
    decoded,started,included,stored,accepted,key,missing⟩ := failed
  rcases extraction_in_program_bad_or_original program world source models decoded parent initialized started sources stored index
    included input dummy ctx radius output accepted key with bad | original
  · exact bad
  · exact False.elim (missing original)

theorem lifetime_trace_misassociation_le_charge {S A : Type} (initial : Program S)
    (step : S → OracleMachine.Command S A) (dummy : Vector InputIndexedOracle.Byte 64) :
    InputIndexedOracle.law {world | ∃ fuel,
      TraceMisassociation (NativeRootFamilyLifetime.program initial step fuel) dummy world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy.get initial step fuel := by
  apply le_trans (MeasureTheory.measure_mono ?_)
    (NativeRootFamilyLifetime.lifetime_bad_le_charge dummy.get initial step)
  rintro world ⟨fuel,failed⟩
  exact ⟨fuel,trace_misassociation_bad (NativeRootFamilyLifetime.program initial step fuel) dummy world failed⟩

end HasteBootsExtractedRegistryAssociation
