module
public import FormalProof4FHE.HasteBoots.LookupRequestRebuild
@[expose] public section

/-! Original validated public-table complexity is paid by its actual wire
payload. Every raw usize word occupies at least one byte; bincode headers and
word spellings remain variable length. No fixed eight-byte word assumption
or attacker-declared count bound is introduced. -/
namespace FormalProof4FHE.HasteBoots.LookupRequestPayloadSize
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request Row Table)
open NativeFieldRepresentation (GoldWord)

theorem word_positive (value : NativeUsizeMessage.Usize) : 0 < (NativeUsizeMessage.encode value).length := by
  unfold NativeUsizeMessage.encode
  split
  · simp
  · split
    · simp [TranscriptFrame.littleEndian_length]
    · split <;> simp [TranscriptFrame.littleEndian_length]

theorem words_length (values : List GoldWord) : values.length ≤ (NativeIntegerPrefix.words values).length := by
  induction values with
  | nil => exact le_rfl
  | cons head tail ih =>
    have first := word_positive head
    simp only [NativeIntegerPrefix.words,List.flatMap_cons,List.length_cons,List.length_append] at ih ⊢
    omega

theorem row_length (row : Row) : row.val.length ≤ (NativeLookupRequestWire.rowCodec.encode row).length := by
  rw [NativeLookupRequestWire.row_encode,NativeFieldWire.goldColumn,NativeIntegerPrefix.encodeVector,List.length_append]
  exact (words_length row.val).trans (Nat.le_add_left _ _)

theorem rows_length (rows : List Row) :
    (rows.map (fun row => row.val.length)).sum ≤ (rows.flatMap NativeLookupRequestWire.rowCodec.encode).length := by
  induction rows with
  | nil => exact le_rfl
  | cons head tail ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
    exact Nat.add_le_add (row_length head) ih

theorem table_cells (table : Table) :
    (table.val.map (fun row => row.val.length)).sum ≤ (NativeLookupRequestWire.tableCodec.encode table).length := by
  rw [NativeLookupRequestWire.table_encode,List.length_append]
  exact (rows_length table.val).trans (Nat.le_add_left _ _)

theorem rectangular_sum (rows : List Row) (width : ℕ) (rectangular : ∀ row ∈ rows, row.val.length = width) :
    (rows.map (fun row => row.val.length)).sum = rows.length*width := by
  induction rows with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [rectangular head List.mem_cons_self,ih (fun row member => rectangular row (List.mem_cons_of_mem _ member))]
    rw [Nat.add_mul,one_mul]
    omega

def complexity (request : Request) : ℕ := request.toModel.table.length*(request.toModel.columns-1)

theorem complexity_le_payload (request : Request)
    (spec : NativeTupleLookupConfig.Spec request.config.logicalLength request.config.repetitions.val request.config.table.values) :
    complexity request ≤ (NativeLookupRequestWire.requestCodec.encode request).length := by
  have rectangular : ∀ row ∈ request.config.table.val, row.val.length = NativeTupleLookupConfig.columns request.config.table.values := by
    intro row member
    exact spec.rectangular row.val (List.mem_map.mpr ⟨row,member,rfl⟩)
  have cells := table_cells request.config.table
  rw [rectangular_sum _ _ rectangular] at cells
  have smaller := Nat.mul_le_mul_left request.config.table.val.length
    (Nat.sub_le (NativeTupleLookupConfig.columns request.config.table.values) 1)
  change request.config.table.values.length*(NativeTupleLookupConfig.columns request.config.table.values-1) ≤ _
  have length : request.config.table.values.length = request.config.table.val.length := List.length_map _
  rw [length]
  rw [NativeLookupRequestWire.request_encode,NativeLookupRequestWire.config_encode]
  simp only [List.length_append]
  omega

theorem list_complexities (requests : List Request)
    (valid : ∀ request ∈ requests, NativeTupleLookupConfig.Spec request.config.logicalLength request.config.repetitions.val request.config.table.values) :
    (requests.map complexity).sum ≤ (requests.flatMap NativeLookupRequestWire.requestCodec.encode).length := by
  induction requests with
  | nil => exact le_rfl
  | cons request rest ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
    exact Nat.add_le_add (complexity_le_payload request (valid request List.mem_cons_self))
      (ih (fun entry member => valid entry (List.mem_cons_of_mem _ member)))

theorem requests_complexities (requests : Vector Request)
    (valid : ∀ request ∈ requests.val, NativeTupleLookupConfig.Spec request.config.logicalLength request.config.repetitions.val request.config.table.values) :
    (requests.val.map complexity).sum ≤ (NativeLookupRequestWire.requestsCodec.encode requests).length := by
  change _ ≤ (NativeUsizeMessage.encode ⟨requests.val.length,requests.property⟩ ++
    requests.val.flatMap NativeLookupRequestWire.requestCodec.encode).length
  rw [List.length_append]
  exact (list_complexities requests.val valid).trans (Nat.le_add_left _ _)

end FormalProof4FHE.HasteBoots.LookupRequestPayloadSize
