module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsOpening
@[expose] public section

/-! Native non-hiding batch opening payload, shape gates and the shared response
frame. The response-group count is computed from trusted checked queries by
the caller. Constructed-message prefix readers do not establish strict Rust
proof-byte decoder equivalence, resource behavior or application security. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchOpening
open NativeLookupRequestWire (Row rowCodec)
open NativeGoldColumnAuthentication (Column columnCodec)
open NativeBrakedownParameters (Geometry)
open NativePrefixCodec (Codec Vector product vector transport)

structure Opening where
  test : Row
  evaluations : Vector Row
  columns : Vector Column

def openingEquiv : (Row × Vector Row × Vector Column) ≃ Opening where
  toFun := fun data => ⟨data.1,data.2.1,data.2.2⟩
  invFun := fun opening => (opening.test,opening.evaluations,opening.columns)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def codec : Codec Opening := transport (product rowCodec (product (vector rowCodec) (vector columnCodec))) openingEquiv

/-- The group count comes from checked caller queries, never from the proof. -/
def check (geometry : Geometry) (queries : NativeUsizeMessage.Usize) (groups : ℕ) (opening : Opening) : Bool :=
  decide (opening.test.val.length = geometry.responseWords) &&
    decide (opening.evaluations.val.length = groups) &&
    opening.evaluations.val.all (fun evaluation => decide (evaluation.val.length = geometry.responseWords)) &&
    decide (opening.columns.val ≠ []) && decide (opening.columns.val.length ≤ min queries.val geometry.blocks) &&
    opening.columns.val.all (fun column => decide (column.values.val.length = geometry.columnWords) &&
      decide (column.path.val.length = geometry.height+1))

structure Spec (geometry : Geometry) (queries : NativeUsizeMessage.Usize) (groups : ℕ) (opening : Opening) : Prop where
  test : opening.test.val.length = geometry.responseWords
  groups : opening.evaluations.val.length = groups
  evaluations : ∀ evaluation ∈ opening.evaluations.val, evaluation.val.length = geometry.responseWords
  nonempty : opening.columns.val ≠ []
  count : opening.columns.val.length ≤ min queries.val geometry.blocks
  columns : ∀ column ∈ opening.columns.val, column.values.val.length = geometry.columnWords ∧ column.path.val.length = geometry.height+1

theorem check_iff (geometry : Geometry) (queries : NativeUsizeMessage.Usize) (groups : ℕ) (opening : Opening) :
    check geometry queries groups opening = true ↔ Spec geometry queries groups opening := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc]
  constructor
  · rintro ⟨test,groups,evaluations,nonempty,count,columns⟩
    exact ⟨test,groups,evaluations,nonempty,count,columns⟩
  · intro spec
    exact ⟨spec.test,spec.groups,spec.evaluations,spec.nonempty,spec.count,spec.columns⟩

theorem encode (opening : Opening) : codec.encode opening = rowCodec.encode opening.test ++
    ((vector rowCodec).encode opening.evaluations ++ (vector columnCodec).encode opening.columns) := rfl

theorem read_prefix (opening : Opening) (suffix : InputIndexedOracle.Input) :
    codec.read (codec.encode opening ++ suffix) = some (opening,suffix) := codec.read_encode _ _

/-- The native response message shares the test and every first-occurrence response in one frame. -/
def bindResponses (parent : NativeTranscript.Transcript) (opening : Opening) : NativeTranscript.Transcript :=
  NativeTranscript.appendBytes parent (NativeTranscript.utf8 "mw batch linear responses")
    (rowCodec.encode opening.test ++ (vector rowCodec).encode opening.evaluations)

theorem bindResponses_input (parent : NativeTranscript.Transcript) (opening : Opening) :
    (bindResponses parent opening).input = parent.input ++ TranscriptFrame.encode
      ⟨1,NativeTranscript.utf8 "mw batch linear responses",rowCodec.encode opening.test ++ (vector rowCodec).encode opening.evaluations⟩ := rfl
end FormalProof4FHE.HasteBoots.NativeGoldBatchOpening
