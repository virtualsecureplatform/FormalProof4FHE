module
public import FormalProof4FHE.HasteBoots.NativeRecordValues
@[expose] public section

/-! Logical payload enums for the RawVec cleanup frontier. Variant indices and
signed source discriminants are separate. No physical enum decoding or Rust ABI
correspondence is asserted here; in particular a niche need not store the source
discriminant. Payloads retain complete pointer values and explicit move holes. -/
namespace FormalProof4FHE.HasteBoots.NativeVariantValues
open NativeRecordValues

structure Branch where
  discriminant : Int
  fields : Ty
  deriving DecidableEq

structure Schema where
  tag : Nat
  branches : List Branch
  deriving DecidableEq

structure Value where
  tag : Nat
  variant : Nat
  payload : NativeRecordValues.Value
  deriving DecidableEq

def branch (schema : Schema) (value : Value) : Option Branch :=
  if value.tag = schema.tag then schema.branches[value.variant]? else none

/-- Discriminants survive moves from the payload. -/
def discriminant (schema : Schema) (value : Value) : Option Int :=
  (branch schema value).map Branch.discriminant

def pack (schema : Schema) (variant : Nat) (payload : NativeRecordValues.Value) : Option Value := do
  let selected ← schema.branches[variant]?
  if fits selected.fields payload then some ⟨schema.tag, variant, payload⟩ else none

/-- The active variant must match the projection's source variant. -/
def project (schema : Schema) (value : Value) (variant : Nat) (path : Path) : Option NativeRecordValues.Value := do
  let selected ← branch schema value
  if value.variant ≠ variant then none else do
    let type ← typeAt selected.fields path
    let field ← get value.payload path
    if fits type field then some field else none

def take (schema : Schema) (value : Value) (variant : Nat) (path : Path) :
    Option (NativeRecordValues.Value × Value) := do
  let field ← project schema value variant path
  let payload ← replace value.payload path .uninit
  pure (field, {value with payload})

theorem branch_same_payload (schema : Schema) (value : Value) (payload : NativeRecordValues.Value) :
    branch schema {value with payload} = branch schema value := rfl

theorem discriminant_same_payload (schema : Schema) (value : Value) (payload : NativeRecordValues.Value) :
    discriminant schema {value with payload} = discriminant schema value := rfl

theorem pack_spec (schema : Schema) (variant : Nat) (payload : NativeRecordValues.Value) (value : Value)
    (packed : pack schema variant payload = some value) :
    ∃ selected, schema.branches[variant]? = some selected ∧ fits selected.fields payload = true ∧
      value = ⟨schema.tag, variant, payload⟩ := by
  simp only [pack, Option.bind_eq_bind', Option.bind_eq_some_iff] at packed
  obtain ⟨selected, found, packed⟩ := packed
  split at packed
  next valid => exact ⟨selected, found, valid, Option.some.inj packed.symm⟩
  next => cases packed

theorem pack_discriminant (schema : Schema) (variant : Nat) (payload : NativeRecordValues.Value) (value : Value)
    (packed : pack schema variant payload = some value) :
    ∃ selected, schema.branches[variant]? = some selected ∧
      discriminant schema value = some selected.discriminant := by
  obtain ⟨selected, found, _, same⟩ := pack_spec schema variant payload value packed
  subst value
  exact ⟨selected, found, by simp [discriminant, branch, found]⟩

theorem project_spec (schema : Schema) (value : Value) (variant : Nat) (path : Path)
    (field : NativeRecordValues.Value) (read : project schema value variant path = some field) :
    ∃ selected type, branch schema value = some selected ∧ value.variant = variant ∧
      typeAt selected.fields path = some type ∧ get value.payload path = some field ∧ fits type field = true := by
  simp only [project, Option.bind_eq_bind', Option.bind_eq_some_iff] at read
  obtain ⟨selected, found, read⟩ := read
  split at read
  next => cases read
  next same =>
    simp only [Option.bind_eq_some_iff] at read
    obtain ⟨type, typed, middle, got, read⟩ := read
    split at read
    next valid => cases read; exact ⟨selected, type, found, by simpa using same, typed, got, valid⟩
    next => cases read

theorem project_complete (schema : Schema) (value : Value) (variant : Nat) (path : Path)
    (field : NativeRecordValues.Value) (read : project schema value variant path = some field) :
    complete field = true := by
  obtain ⟨_, _, _, _, _, got, _⟩ := project_spec schema value variant path field read
  exact get_complete value.payload field path got

theorem project_leaves (schema : Schema) (value : Value) (variant : Nat) (path : Path)
    (field : NativeRecordValues.Value) (read : project schema value variant path = some field)
    (leaf : NativeSliceLLBC.Value) (member : leaf ∈ leaves field) : leaf ∈ leaves value.payload := by
  obtain ⟨_, _, _, _, _, got, _⟩ := project_spec schema value variant path field read
  exact get_leaves value.payload field path got leaf member

theorem take_spec (schema : Schema) (value : Value) (variant : Nat) (path : Path)
    (field : NativeRecordValues.Value) (changed : Value)
    (moved : take schema value variant path = some (field, changed)) :
    project schema value variant path = some field ∧
      replace value.payload path .uninit = some changed.payload ∧
      changed.tag = value.tag ∧ changed.variant = value.variant := by
  simp only [take, Option.bind_eq_bind', Option.bind_eq_some_iff, pure, Option.some.injEq] at moved
  obtain ⟨first, read, payload, written, same⟩ := moved
  cases same
  exact ⟨read, written, rfl, rfl⟩

theorem take_consumes (schema : Schema) (value : Value) (variant : Nat) (path : Path)
    (field : NativeRecordValues.Value) (changed : Value)
    (moved : take schema value variant path = some (field, changed)) : get changed.payload path = none :=
  get_replace value.payload .uninit changed.payload path (take_spec schema value variant path field changed moved).2.1

theorem take_discriminant (schema : Schema) (value : Value) (variant : Nat) (path : Path)
    (field : NativeRecordValues.Value) (changed : Value)
    (moved : take schema value variant path = some (field, changed)) :
    discriminant schema changed = discriminant schema value := by
  obtain ⟨_, _, tag, index⟩ := take_spec schema value variant path field changed moved
  simp only [discriminant, branch, tag, index]

/-- Binary enum representation used by the aggregate interpreter. -/
def binaryType (tag : Nat) (left right : Ty) : Ty := .record tag (.choice left right)

def binaryValue (tag : Nat) (side : Bool) (payload : NativeRecordValues.Value) : NativeRecordValues.Value :=
  .record tag (.choice side payload)

theorem binary_fits (tag : Nat) (left right : Ty) (side : Bool) (payload : NativeRecordValues.Value) :
    fits (binaryType tag left right) (binaryValue tag side payload) =
      fits (if side then right else left) payload := by
  cases side <;> simp [binaryType, binaryValue, fits, complete, compatible]

theorem binary_get (tag : Nat) (side : Bool) (payload : NativeRecordValues.Value) (path : Path) :
    get (binaryValue tag side payload) ([.unwrap tag, .active side] ++ path) = get payload path := by
  simp [binaryValue, NativeRecordValues.get]

theorem binary_replace (tag : Nat) (side : Bool) (payload replacement : NativeRecordValues.Value) (path : Path) :
    replace (binaryValue tag side payload) ([.unwrap tag, .active side] ++ path) replacement =
      (replace payload path replacement).map (binaryValue tag side) := by
  simp only [binaryValue, replace, List.cons_append, List.nil_append, ite_true, Option.map_map]
  rfl

theorem binary_side (tag : Nat) (side : Bool) (payload : NativeRecordValues.Value) :
    sideAt (binaryValue tag side payload) [] tag = some side := by
  simp [binaryValue, sideAt]

end FormalProof4FHE.HasteBoots.NativeVariantValues
