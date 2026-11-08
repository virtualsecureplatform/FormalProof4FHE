import Aeneas.Std

/-! Explicit word64 slice values and checked indexing/update. This does not
supply Rust references, heap access, alias permissions or physical-work costs. -/
namespace HasteBootsSlice64Runtime
open Aeneas Aeneas.Std Result

def Slice (T : Type) := { values : List T // values.length < 2 ^ 64 }

def len {T : Type} (slice : Slice T) : U64 :=
  ⟨BitVec.ofFin ⟨slice.val.length, slice.property⟩⟩

def index {T : Type} (slice : Slice T) (offset : U64) : Result T :=
  match slice.val[offset.val]? with
  | none => .fail .arrayOutOfBounds
  | some value => .ok value

def set {T : Type} (slice : Slice T) (offset : U64) (value : T) : Slice T :=
  ⟨slice.val.set offset.val value, by simpa only [List.length_set] using slice.property⟩

def index_mut {T : Type} (slice : Slice T) (offset : U64) : Result (T × (T → Slice T)) := do
  let value ← index slice offset
  ok (value, set slice offset)

def update {T : Type} (slice : Slice T) (offset : U64) (value : T) : Result (Slice T) :=
  match slice.val[offset.val]? with
  | none => .fail .arrayOutOfBounds
  | some _ => .ok (set slice offset value)

theorem len_value {T : Type} (slice : Slice T) : (len slice).val = slice.val.length := rfl

theorem index_found {T : Type} (slice : Slice T) (offset : U64) (value : T)
    (found : slice.val[offset.val]? = some value) : index slice offset = ok value := by
  simp only [index, found]

theorem index_missing {T : Type} (slice : Slice T) (offset : U64)
    (missing : slice.val[offset.val]? = none) : index slice offset = fail .arrayOutOfBounds := by
  simp only [index, missing]

theorem set_values {T : Type} (slice : Slice T) (offset : U64) (value : T) :
    (set slice offset value).val = slice.val.set offset.val value := rfl

theorem set_length {T : Type} (slice : Slice T) (offset : U64) (value : T) :
    (set slice offset value).val.length = slice.val.length := by
  exact List.length_set

theorem update_found {T : Type} (slice : Slice T) (offset : U64) (previous value : T)
    (found : slice.val[offset.val]? = some previous) : update slice offset value = ok (set slice offset value) := by
  simp only [update, found]

theorem update_missing {T : Type} (slice : Slice T) (offset : U64) (value : T)
    (missing : slice.val[offset.val]? = none) : update slice offset value = fail .arrayOutOfBounds := by
  simp only [update, missing]

theorem index_mut_found {T : Type} (slice : Slice T) (offset : U64) (value : T)
    (found : slice.val[offset.val]? = some value) : index_mut slice offset = ok (value, set slice offset) := by
  simp only [index_mut, index_found slice offset value found, bind_tc_ok]

end HasteBootsSlice64Runtime
