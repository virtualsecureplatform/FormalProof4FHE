module

public import FormalProof4FHE.HasteBoots.NativeTupleLookupConfig
public import FormalProof4FHE.HasteBoots.UsizeVectorCost
import all Init.Data.String.Defs

@[expose] public section

/-!
# Exact native tuple-config and shared-request wire records

Config serializes logical_len, nested public table and repetitions, without
an independent columns field. Request then appends its ordered source slots.
Every native Vec retains its usize header/domain and every Goldilocks word
its original raw u64 spelling. Structural prefix readers do not establish
strict adversarial proof deserialization or Rust/serde refinement.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupRequestWire

open NativePrefixCodec (Codec product vector transport usize)
open NativeUsizeMessage (Usize)
open NativeFieldRepresentation (GoldWord)
open NativeSharedLookupValues (Policy)
open InputIndexedOracle (Input)

abbrev Row := NativePrefixCodec.Vector GoldWord
abbrev Table := NativePrefixCodec.Vector Row

structure Config where
  logicalLength : Usize
  table : Table
  repetitions : Usize
  deriving DecidableEq

structure Request where
  config : Config
  sourceSlots : NativePrefixCodec.Vector Usize
  deriving DecidableEq

def configEquiv : (Usize × Table × Usize) ≃ Config where
  toFun := fun value => ⟨value.1,value.2.1,value.2.2⟩
  invFun := fun value => ⟨value.logicalLength,value.table,value.repetitions⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def requestEquiv : (Config × NativePrefixCodec.Vector Usize) ≃ Request where
  toFun := fun value => ⟨value.1,value.2⟩
  invFun := fun value => ⟨value.config,value.sourceSlots⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def rowCodec : Codec Row where
  encode := (vector usize).encode
  read := fun bytes => (UsizeVectorCost.read bytes).value
  read_encode := by
    intro row suffix
    rw [UsizeVectorCost.read_value]
    exact (vector usize).read_encode row suffix

theorem rowCodec_read_eq_reference (bytes : Input) :
    rowCodec.read bytes = (vector usize).read bytes := UsizeVectorCost.read_value bytes

def tableCodec : Codec Table := vector rowCodec
def configCodec : Codec Config := transport (product usize (product tableCodec usize)) configEquiv
def requestCodec : Codec Request := transport (product configCodec (vector usize)) requestEquiv
def requestsCodec : Codec (NativePrefixCodec.Vector Request) := vector requestCodec

def Table.values (table : Table) : List (List GoldWord) := table.val.map Subtype.val

def Request.toModel (request : Request) : NativeSharedLookupStatement.Request :=
  ⟨NativeTupleLookupConfig.columns request.config.table.values,request.config.table.values,request.config.repetitions.val,
    ⟨request.sourceSlots.val.map Fin.val,request.config.logicalLength⟩⟩

def normalizeRow (policy : Policy) (row : Row) : Row :=
  ⟨NativeTupleLookupConfig.normalizeRow policy row.val,by rw [NativeTupleLookupConfig.normalizeRow_length]; exact row.property⟩

def normalizeConfig (policy : Policy) (config : Config) : Config :=
  {config with table := ⟨config.table.val.map (normalizeRow policy),by rw [List.length_map]; exact config.table.property⟩}

def normalizeRequest (policy : Policy) (request : Request) : Request := {request with config := normalizeConfig policy request.config}

theorem row_encode (row : Row) : rowCodec.encode row = NativeFieldWire.goldColumn row.val row.property := rfl

theorem table_encode (table : Table) : tableCodec.encode table =
    NativeUsizeMessage.encode ⟨table.val.length,table.property⟩ ++ table.val.flatMap (fun row => NativeFieldWire.goldColumn row.val row.property) := rfl

theorem config_encode (config : Config) : configCodec.encode config =
    NativeUsizeMessage.encode config.logicalLength ++ tableCodec.encode config.table ++ NativeUsizeMessage.encode config.repetitions := by
  simp only [configCodec,NativePrefixCodec.transport,NativePrefixCodec.product,configEquiv]
  exact (List.append_assoc _ _ _).symm

theorem request_encode (request : Request) : requestCodec.encode request = configCodec.encode request.config ++
    (NativeUsizeMessage.encode ⟨request.sourceSlots.val.length,request.sourceSlots.property⟩ ++
      request.sourceSlots.val.flatMap NativeUsizeMessage.encode) := rfl

theorem config_prefix (config : Config) (suffix : Input) :
    configCodec.read (configCodec.encode config ++ suffix) = some (config,suffix) := configCodec.read_encode config suffix

theorem request_prefix (request : Request) (suffix : Input) :
    requestCodec.read (requestCodec.encode request ++ suffix) = some (request,suffix) := requestCodec.read_encode request suffix

theorem requests_prefix (requests : NativePrefixCodec.Vector Request) (suffix : Input) :
    requestsCodec.read (requestsCodec.encode requests ++ suffix) = some (requests,suffix) := requestsCodec.read_encode requests suffix

theorem requests_injective : Function.Injective requestsCodec.encode := requestsCodec.encode_injective

theorem normalize_table_values (policy : Policy) (config : Config) :
    (normalizeConfig policy config).table.values = NativeTupleLookupConfig.normalizeTable policy config.table.values := by
  simp only [normalizeConfig,Table.values,normalizeRow,NativeTupleLookupConfig.normalizeTable,List.map_map,Function.comp_def]

/-- Rebuilding the native semantic request produces exactly the typed
normalized wire object; its arity is always derived rather than serialized. -/
theorem rebuild_model (policy : Policy) (request : Request) :
    NativeTupleLookupConfig.rebuild policy request.toModel =
      if NativeTupleLookupConfig.valid request.config.logicalLength request.config.repetitions.val request.config.table.values then
        some (normalizeRequest policy request).toModel else none := by
  simp only [NativeTupleLookupConfig.rebuild,Request.toModel,NativeTupleLookupConfig.valid_normalize]
  by_cases valid : NativeTupleLookupConfig.valid request.config.logicalLength request.config.repetitions.val request.config.table.values = true
  · simp only [valid,ite_true]
    congr 1
    simp only [normalizeRequest,normalize_table_values]
    rfl
  · simp only [valid,Bool.false_eq_true,ite_false]

def requestsLabel : Input := NativeTranscript.utf8 "canonical shared-query extension lookups v1"

def bindRequests (parent : NativeTranscript.Transcript) (requests : NativePrefixCodec.Vector Request) : NativeTranscript.Transcript :=
  NativeTranscript.appendBytes parent requestsLabel (requestsCodec.encode requests)

theorem bindRequests_input (parent : NativeTranscript.Transcript) (requests : NativePrefixCodec.Vector Request) :
    (bindRequests parent requests).input = parent.input ++ TranscriptFrame.encode ⟨1,requestsLabel,requestsCodec.encode requests⟩ := rfl

theorem bindRequests_injective (parent : NativeTranscript.Transcript) (left right : NativePrefixCodec.Vector Request)
    (leftFits : (requestsCodec.encode left).length < TranscriptFrame.lengthLimit)
    (rightFits : (requestsCodec.encode right).length < TranscriptFrame.lengthLimit)
    (same : (bindRequests parent left).input = (bindRequests parent right).input) : left = right := by
  rw [bindRequests_input,bindRequests_input] at same
  have encoded := List.append_cancel_left same
  have labelFits : requestsLabel.length < TranscriptFrame.lengthLimit := by decide +kernel
  have frames := TranscriptFrame.encodeMany_injective
    [⟨1,requestsLabel,requestsCodec.encode left⟩] [⟨1,requestsLabel,requestsCodec.encode right⟩]
    (by intro frame member; obtain rfl := List.mem_singleton.mp member; exact ⟨labelFits,leftFits⟩)
    (by intro frame member; obtain rfl := List.mem_singleton.mp member; exact ⟨labelFits,rightFits⟩)
    (by simpa only [TranscriptFrame.encodeMany,List.append_nil] using encoded)
  exact requests_injective (congrArg TranscriptFrame.Frame.message (List.cons.inj frames).1)

end FormalProof4FHE.HasteBoots.NativeLookupRequestWire
