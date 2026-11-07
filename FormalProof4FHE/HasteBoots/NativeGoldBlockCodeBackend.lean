module
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeProgram
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext
@[expose] public section

/-! Constructor/cached-table receipts supply the earlier code/encoding semantic
interface. The table record below observes actual program outcomes; it does not
implement initialization. Root conversion erases a proved canonical bound,
without adding a native gate or normalization. Rust/ArcSwap, optimized kernels
and physical/source refinement remain mandatory separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBlockCodeBackend
open NativeGoldBlockCodeProgram (Request Config Completed rawRoot)
open ConcreteNTTGoldCacheRCU (Machine)
open ConcreteNTTGoldTable (Table newTable)
open ConcreteNTTCacheLookup (lookup)

def canonicalRoot (logSize : ℕ) (table : Table) (built : newTable logSize = .created table) : NativeGoldSolinas.Word :=
  ⟨table.root.val,ConcreteNTTGoldTable.root_canonical logSize table built⟩

theorem canonicalRoot_raw (logSize : ℕ) (table : Table) (built : newTable logSize = .created table) :
    NativeGoldSolinas.raw (canonicalRoot logSize table built) = rawRoot table.root := by
  apply Fin.ext
  rfl

def observations (machine : Machine) (reachable : ConcreteNTTGoldCacheRCU.Reachable machine) : NativeGoldBlockCode.Tables where
  generate logSize := match newTable logSize with | .created _ => true | _ => false
  initTable logSize := (lookup machine.current.tables logSize).isSome
  load logSize :=
    match found : lookup machine.current.tables logSize with
    | none => none
    | some table => some (canonicalRoot logSize table (ConcreteNTTGoldCacheRCU.retained_table_origin machine reachable logSize table found))

theorem observed_generated (machine : Machine) (reachable : ConcreteNTTGoldCacheRCU.Reachable machine)
    (logSize : ℕ) (table : Table) (built : newTable logSize = .created table) :
    (observations machine reachable).generate logSize = true := by
  simp only [observations,built]

theorem observed_initialized (machine : Machine) (reachable : ConcreteNTTGoldCacheRCU.Reachable machine)
    (logSize : ℕ) (table : Table) (found : lookup machine.current.tables logSize = some table) :
    (observations machine reachable).initTable logSize = true := by
  simp only [observations,found,Option.isSome_some]

theorem observed_loaded (machine : Machine) (reachable : ConcreteNTTGoldCacheRCU.Reachable machine)
    (logSize : ℕ) (table : Table) (found : lookup machine.current.tables logSize = some table)
    (built : newTable logSize = .created table) :
    (observations machine reachable).load logSize = some (canonicalRoot logSize table built) := by
  simp only [observations]
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i loaded cached
    have same : loaded = table := Option.some.inj (cached.symm.trans found)
    subst loaded
    rfl

theorem layout_build (request : Request) (layout : NativeGoldBlockCodeLayout.Layout)
    (ready : NativeGoldBlockCodeProgram.LayoutReady request layout) (machine : Machine)
    (reachable : ConcreteNTTGoldCacheRCU.Reachable machine) (table : Table)
    (found : lookup machine.current.tables (NativeGoldBlockCodeLayout.logSize layout) = some table) :
    NativeGoldBlockCode.build (observations machine reachable) request.message request.block request.blowup =
      .ok (NativeGoldBlockCodeLayout.store layout (rawRoot table.root)) := by
  have built := ConcreteNTTGoldCacheRCU.retained_table_origin machine reachable _ table found
  have result := NativeGoldBlockCodeLayout.build_from_preflight request.message request.block request.blowup layout ready
    (observations machine reachable) (canonicalRoot _ table built)
    (observed_generated machine reachable _ table built) (observed_initialized machine reachable _ table found)
    (observed_loaded machine reachable _ table found built)
  simpa only [canonicalRoot_raw] using result

theorem completed_build (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    NativeGoldBlockCode.build (observations config.cache (NativeGoldBlockCodeProgram.reachable_good request config reachable).1)
      request.message request.block request.blowup = .ok result.code := by
  have origin := NativeGoldBlockCodeProgram.completed_origin request config reachable result finished
  rw [origin.2.2.2.2]
  exact layout_build request result.layout origin.2.1 config.cache origin.1 result.loaded origin.2.2.2.1

theorem completed_log (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    NativeGoldBlockCode.logSize result.code = NativeGoldBlockCodeLayout.logSize result.layout := by
  have origin := NativeGoldBlockCodeProgram.completed_origin request config reachable result finished
  rw [origin.2.2.2.2]
  rfl

theorem completed_primitive (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    IsPrimitiveRoot (NativeFieldRepresentation.goldValue result.code.domainRoot) (2^(NativeGoldBlockCode.logSize result.code+1)) := by
  have origin := NativeGoldBlockCodeProgram.completed_origin request config reachable result finished
  rw [origin.2.2.2.2]
  exact ConcreteNTTGoldTable.root_primitive _ result.loaded origin.2.2.1

def planRoot (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) : NativeGoldSolinas.Word :=
  canonicalRoot (NativeGoldBlockCodeLayout.logSize result.layout) result.loaded
    (NativeGoldBlockCodeProgram.completed_origin request config reachable result finished).2.2.1

theorem planRoot_value (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    (planRoot request config reachable result finished).val = result.loaded.root.val := rfl

theorem completed_loaded (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    (observations config.cache (NativeGoldBlockCodeProgram.reachable_good request config reachable).1).load
      (NativeGoldBlockCode.logSize result.code) = some (planRoot request config reachable result finished) := by
  have origin := NativeGoldBlockCodeProgram.completed_origin request config reachable result finished
  rw [completed_log request config reachable result finished]
  exact observed_loaded config.cache _ _ result.loaded origin.2.2.2.1 origin.2.2.1

theorem completed_encoding_check (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    NativeGoldRowEncoding.check (NativeGoldBlockCode.encoding result.code (planRoot request config reachable result finished)) = true :=
  NativeGoldBlockCodeMeaning.constructor_encoding_check _ request.message request.block request.blowup result.code
    (completed_build request config reachable result finished) _ (completed_loaded request config reachable result finished)
    (completed_primitive request config reachable result finished)

theorem later_table_same (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (machine : Machine)
    (later : ConcreteNTTGoldCacheRCU.Reachable machine) (table : Table)
    (found : lookup machine.current.tables (NativeGoldBlockCode.logSize result.code) = some table) : table = result.loaded := by
  have origin := NativeGoldBlockCodeProgram.completed_origin request config reachable result finished
  have built := ConcreteNTTGoldCacheRCU.retained_table_origin machine later _ table found
  rw [completed_log request config reachable result finished] at built
  exact ConcreteNTTGoldTable.Outcome.created.inj (built.symm.trans origin.2.2.1)

theorem later_encoding_check (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (machine : Machine)
    (later : ConcreteNTTGoldCacheRCU.Reachable machine) (table : Table)
    (found : lookup machine.current.tables (NativeGoldBlockCode.logSize result.code) = some table) :
    NativeGoldRowEncoding.check (NativeGoldBlockCode.encoding result.code (canonicalRoot _ table
      (ConcreteNTTGoldCacheRCU.retained_table_origin machine later _ table found))) = true := by
  have same := later_table_same request config reachable result finished machine later table found
  have rootEq : canonicalRoot _ table (ConcreteNTTGoldCacheRCU.retained_table_origin machine later _ table found) =
      planRoot request config reachable result finished := by
    apply Fin.ext
    rw [planRoot_value]
    exact congrArg (fun value : Table => value.root.val) same
  rw [rootEq]
  exact completed_encoding_check request config reachable result finished

theorem completed_responses_complete (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (width : ℕ) (input : List NativeFieldRepresentation.GoldWord)
    (size : input.length = width*result.code.messageLength.val) :
    ∃ output, NativeGoldRowEncoding.encodeResponses (NativeGoldBlockCode.encoding result.code
      (planRoot request config reachable result finished)) width input = some output :=
  NativeGoldRowEncoding.encodeResponses_complete _ width input (completed_encoding_check request config reachable result finished) size

theorem completed_code_bytes (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    NativeGoldBlockCode.codec.encode result.code =
      NativeUsizeMessage.encode result.layout.messageLength ++
        (NativeUsizeMessage.encode result.layout.blockWidth ++
          (NativeUsizeMessage.encode result.layout.messageBlocks ++
            (NativeUsizeMessage.encode result.layout.blocks ++
              (NativeByteCodec.bytes.encode NativeBrakedownContext.modulus ++
                NativeFieldWire.gold (rawRoot result.loaded.root))))) := by
  have origin := NativeGoldBlockCodeProgram.completed_origin request config reachable result finished
  rw [origin.2.2.2.2,NativeGoldBlockCode.serialize_fields]
  rfl

theorem completed_codeShape (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result)
    (parameters : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) (same : parameters.code = result.code)
    (messageMatches : request.message.val = 2^(parameters.numVariables.val-parameters.leftVariables.val)) :
    NativeBrakedownParameters.codeShape NativeGoldBlockCode.description parameters = true := by
  apply NativeGoldBlockCodeMeaning.constructor_codeShape _ request.message request.block request.blowup parameters
  · rw [same]
    exact completed_build request config reachable result finished
  · exact messageMatches

noncomputable section

theorem completed_response_lanes (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (width : ℕ)
    (input output : List NativeFieldRepresentation.GoldWord)
    (success : NativeGoldRowEncoding.encodeResponses (NativeGoldBlockCode.encoding result.code
      (planRoot request config reachable result finished)) width input = some output) :
    ∀ lane < width,
      NativeGoldResponseMeaning.laneWord (NativeGoldBlockCode.encoding result.code
        (planRoot request config reachable result finished)) output lane = BlockEncoder.encode
          (NTTButterfly.domain (NativeGoldBlockCode.logSize result.code) (NativeFieldRepresentation.goldValue result.code.domainRoot)
            (completed_primitive request config reachable result finished))
          (NativeGoldRowMeaning.coefficients (NativeGoldBlockCode.encoding result.code
            (planRoot request config reachable result finished)) result.code.messageBlocks.val
            ((input.drop (lane*result.code.messageLength.val)).take result.code.messageLength.val)) ∧
      NativeGoldResponseMeaning.laneWord (NativeGoldBlockCode.encoding result.code
        (planRoot request config reachable result finished)) output lane ∈ BlockCode.code
          (NTTButterfly.domain (NativeGoldBlockCode.logSize result.code) (NativeFieldRepresentation.goldValue result.code.domainRoot)
            (completed_primitive request config reachable result finished)) result.code.messageBlocks.val result.code.blockWidth.val :=
  NativeGoldBlockCodeMeaning.response_lanes _ request.message request.block request.blowup result.code
    (completed_build request config reachable result finished) _ width input output success
    (completed_primitive request config reachable result finished)

end
end FormalProof4FHE.HasteBoots.NativeGoldBlockCodeBackend
