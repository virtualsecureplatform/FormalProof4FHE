namespace HasteBootsRawVecOption
open FormalProof4FHE.HasteBoots
open NativeVariantValues

def noneValue : Value := ⟨10, 0, .scalar .unit⟩
def someValue (payload : NativeRecordValues.Value) : Value := ⟨10, 1, payload⟩

theorem none_discriminant : discriminant schema noneValue = some 0 := by decide

theorem some_discriminant (payload : NativeRecordValues.Value) :
    discriminant schema (someValue payload) = some 1 := rfl

theorem none_pack : pack schema 0 (.scalar .unit) = some noneValue := by decide

theorem some_projection_provenance (payload field : NativeRecordValues.Value)
    (path : NativeRecordValues.Path)
    (read : project schema (someValue payload) 1 path = some field)
    (pointer : NativeSliceLLBC.Value) (member : pointer ∈ NativeRecordValues.leaves field) :
    pointer ∈ NativeRecordValues.leaves payload :=
  project_leaves schema (someValue payload) 1 path field read pointer member

theorem some_move_discriminant (payload field : NativeRecordValues.Value)
    (path : NativeRecordValues.Path) (changed : Value)
    (moved : take schema (someValue payload) 1 path = some (field, changed)) :
    discriminant schema changed = some 1 := by
  rw [take_discriminant schema (someValue payload) 1 path field changed moved]
  rfl

end HasteBootsRawVecOption
