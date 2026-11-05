module

public import FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
public import FormalProof4FHE.HasteBoots.NativeBrakedownParameters

@[expose] public section

/-! Original non-hiding Goldilocks single-opening fields and native outer
shape gates. Columns keep raw words and complete leaf-first paths. Constructed
wire prefix readers are not a strict adversarial Rust decoder refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsOpening

open NativeLookupRequestWire (Row rowCodec)
open NativeGoldColumnAuthentication (Column columnCodec)
open NativeBrakedownParameters (Geometry)
open NativePrefixCodec (Codec product vector transport)

structure Opening where
  test : Row
  evaluation : Row
  columns : NativePrefixCodec.Vector Column

def openingEquiv : (Row × Row × NativePrefixCodec.Vector Column) ≃ Opening where
  toFun := fun data => ⟨data.1,data.2.1,data.2.2⟩
  invFun := fun opening => (opening.test,opening.evaluation,opening.columns)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def codec : Codec Opening := transport (product rowCodec (product rowCodec (vector columnCodec))) openingEquiv

def check (geometry : Geometry) (queries : NativeUsizeMessage.Usize) (opening : Opening) : Bool :=
  decide (opening.test.val.length = geometry.responseWords) &&
    decide (opening.evaluation.val.length = geometry.responseWords) &&
    decide (opening.columns.val ≠ []) && decide (opening.columns.val.length ≤ min queries.val geometry.blocks) &&
    opening.columns.val.all (fun column => decide (column.values.val.length = geometry.columnWords) &&
      decide (column.path.val.length = geometry.height+1))

structure Spec (geometry : Geometry) (queries : NativeUsizeMessage.Usize) (opening : Opening) : Prop where
  test : opening.test.val.length = geometry.responseWords
  evaluation : opening.evaluation.val.length = geometry.responseWords
  nonempty : opening.columns.val ≠ []
  count : opening.columns.val.length ≤ min queries.val geometry.blocks
  columns : ∀ column ∈ opening.columns.val, column.values.val.length = geometry.columnWords ∧ column.path.val.length = geometry.height+1

theorem check_iff (geometry : Geometry) (queries : NativeUsizeMessage.Usize) (opening : Opening) :
    check geometry queries opening = true ↔ Spec geometry queries opening := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc]
  constructor
  · rintro ⟨test,evaluation,nonempty,count,columns⟩
    exact ⟨test,evaluation,nonempty,count,columns⟩
  · intro spec
    exact ⟨spec.test,spec.evaluation,spec.nonempty,spec.count,spec.columns⟩

theorem encode (opening : Opening) : codec.encode opening = rowCodec.encode opening.test ++
    (rowCodec.encode opening.evaluation ++ (vector columnCodec).encode opening.columns) := rfl

theorem read_prefix (opening : Opening) (suffix : InputIndexedOracle.Input) :
    codec.read (codec.encode opening ++ suffix) = some (opening,suffix) := codec.read_encode _ _

end FormalProof4FHE.HasteBoots.NativeGoldPcsOpening
