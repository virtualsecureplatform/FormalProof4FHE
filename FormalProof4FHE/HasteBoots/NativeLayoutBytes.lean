module
public import FormalProof4FHE.HasteBoots.NativeRecordValues
@[expose] public section

/-! The retained x86_64 Layout object has alignment at byte 0 and size at byte
8. This byte bridge does not prove Rust ABI/compiler/lifetime correspondence. -/
namespace FormalProof4FHE.HasteBoots.NativeLayoutBytes
open NativeWord64Memory (Word)
open NativeByteMemory (Byte)
open NativeReferenceMachine (State)

structure Words where
  size : Word
  alignment : Word
  deriving DecidableEq

def Words.Valid (value : Words) : Prop :=
  value.alignment.val ∈ (List.range 64).map (fun exponent => 2 ^ exponent)

instance (value : Words) : Decidable value.Valid := by
  unfold Words.Valid
  infer_instance

def Words.value (value : Words) (layoutTag alignmentTag enumTag : Nat) : NativeRecordValues.Value :=
  .record layoutTag (.pair (.scalar (.usize value.size))
    (.pair (.record alignmentTag (.pair (.enumeration enumTag value.alignment) (.scalar .unit))) (.scalar .unit)))

/-- Physical field order is alignment, then size. -/
def encode (value : Words) : List Byte :=
  NativeWord64Memory.encode value.alignment ++ NativeWord64Memory.encode value.size

def decode (bytes : List Byte) : Option Words := do
  if bytes.length = 16 then
    let alignment ← NativeWord64Memory.decode (bytes.take 8)
    let size ← NativeWord64Memory.decode (bytes.drop 8)
    let value := Words.mk size alignment
    if value.Valid then some value else none
  else none

inductive Result where
  | value (words : Words) (world : State)
  | invalid (world : State)
  deriving DecidableEq

def Result.world : Result → State
  | .value _ world | .invalid world => world

/-- The actual shared read records bytes and prepares its scratch pointer.
Malformed initialized bytes retain that executed read prefix on failure. -/
def read (world : State) (reference : Nat) : Result :=
  match NativeReferenceMachine.execute world (.access reference 0 (.read 16 8)) with
  | none => .invalid world
  | some next => match next.outputs[0]? with
    | none => .invalid next
    | some bytes => match decode bytes with
      | none => .invalid next
      | some words => .value words next

theorem encode_length (value : Words) : (encode value).length = 16 := by
  simp [encode, NativeWord64Memory.encode_length]

theorem decode_encode (value : Words) (valid : value.Valid) : decode (encode value) = some value := by
  simp [decode, encode, NativeWord64Memory.encode_length, NativeWord64Memory.decode_encode, valid]

theorem decode_valid (bytes : List Byte) (value : Words) (decoded : decode bytes = some value) : value.Valid := by
  simp only [decode, Option.bind_eq_bind'] at decoded
  split at decoded
  · simp only [Option.bind_eq_some_iff] at decoded
    obtain ⟨alignment, _, size, _, actual⟩ := decoded
    split at actual
    next valid => cases actual; exact valid
    next => cases actual
  · cases decoded

theorem decode_fields (bytes : List Byte) (value : Words) (decoded : decode bytes = some value) :
    bytes.length = 16 ∧ NativeWord64Memory.decode (bytes.take 8) = some value.alignment ∧
      NativeWord64Memory.decode (bytes.drop 8) = some value.size := by
  simp only [decode, Option.bind_eq_bind'] at decoded
  split at decoded
  next length =>
    simp only [Option.bind_eq_some_iff] at decoded
    obtain ⟨alignment, first, size, second, actual⟩ := decoded
    split at actual
    next => cases actual; exact ⟨length, first, second⟩
    next => cases actual
  next => cases decoded

theorem encode_decode (bytes : List Byte) (value : Words) (decoded : decode bytes = some value) : encode value = bytes := by
  obtain ⟨_, first, second⟩ := decode_fields bytes value decoded
  have alignment := NativeWord64Memory.encode_decode _ _ first
  have size := NativeWord64Memory.encode_decode _ _ second
  simp only [encode, alignment, size]
  exact List.take_append_drop 8 bytes

theorem decode_wrong_length (bytes : List Byte) (wrong : bytes.length ≠ 16) : decode bytes = none := by
  simp only [decode, Option.bind_eq_bind', wrong, ite_false]

theorem size_field (value : Words) (layoutTag alignmentTag enumTag : Nat) :
    NativeRecordValues.get (value.value layoutTag alignmentTag enumTag) [.unwrap layoutTag,.left] =
      some (.scalar (.usize value.size)) := by
  simp [Words.value, NativeRecordValues.get, NativeRecordValues.complete]

theorem alignment_field (value : Words) (layoutTag alignmentTag enumTag : Nat) :
    NativeRecordValues.get (value.value layoutTag alignmentTag enumTag)
      [.unwrap layoutTag,.right,.left,.unwrap alignmentTag,.left] = some (.enumeration enumTag value.alignment) := by
  simp [Words.value, NativeRecordValues.get, NativeRecordValues.complete]

theorem read_projects (world : State) (reference : Nat) :
    NativeReferenceMachine.Runs world (read world reference).world := by
  cases actual : NativeReferenceMachine.execute world (.access reference 0 (.read 16 8)) with
  | none => simp only [read, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeReferenceMachine.Runs.step (.refl world) _ actual
    cases found : next.outputs[0]? with
    | none => simpa only [read, actual, found, Result.world] using first
    | some bytes =>
      cases decoded : decode bytes <;> simpa only [read, actual, found, decoded, Result.world] using first

theorem read_success (world next : State) (reference : Nat) (value : Words)
    (loaded : read world reference = .value value next) :
    NativeReferenceMachine.execute world (.access reference 0 (.read 16 8)) = some next ∧
      ∃ bytes, next.outputs[0]? = some bytes ∧ decode bytes = some value := by
  cases actual : NativeReferenceMachine.execute world (.access reference 0 (.read 16 8)) with
  | none => simp only [read, actual] at loaded; cases loaded
  | some changed =>
    cases found : changed.outputs[0]? with
    | none => simp only [read, actual, found] at loaded; cases loaded
    | some bytes =>
      cases decoded : decode bytes with
      | none => simp only [read, actual, found, decoded] at loaded; cases loaded
      | some words =>
        simp only [read, actual, found, decoded] at loaded
        cases loaded
        exact ⟨rfl, bytes, found, decoded⟩

theorem read_reachable (world : State) (reference : Nat) (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (read world reference).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (read_projects world reference)


theorem read_effect (world next : State) (reference : Nat) (value : Words)
    (loaded : read world reference = .value value next) :
    ∃ lease pointer bytes,
      (∃ selected, world.references[reference]? = some selected ∧
        NativeByteBorrow.lookup world.leases selected.tag = some lease ∧
        NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger world) selected.tag .shared pointer ⟨16,8⟩ = true) ∧
      NativeByteRange.loadRange world.pointers.heap.memory pointer ⟨16,8⟩ = some bytes ∧
      encode value = bytes ∧ next.outputs = bytes :: world.outputs ∧
      next.pointers.heap = world.pointers.heap ∧ next.pointers.registers = pointer :: world.pointers.registers ∧
      next.pointers.history = world.pointers.history ∧ next.nextTag = world.nextTag ∧
      next.leases = world.leases ∧ next.references = world.references ∧ next.births = world.births := by
  obtain ⟨actual, observed, headEq, decoded⟩ := read_success world next reference value loaded
  have accessed : NativeReferenceMachine.access world reference 0 (.read 16 8) = some next := actual
  obtain ⟨selected, lease, pointer, prepared, chosen, found, _, _, shifted, allowed, preparedEq, performed⟩ :=
    NativeReferenceMachine.access_success world next reference 0 (.read 16 8) accessed
  have fields := NativeByteRange.pointerAt_fields lease.pointer 0 pointer shifted
  have preparedState := (NativeReferenceMachine.prepare_success world lease.pointer pointer.address prepared preparedEq).2
  have pointerEq : NativePointerStorage.Pointer.mk pointer.address lease.pointer.provenance = pointer := by
    rw [← fields.2]
  simp only [NativeReferenceMachine.perform, Option.map_eq_some_iff] at performed
  obtain ⟨bytes, bytesEq, same⟩ := performed
  cases same
  rw [preparedState] at bytesEq
  change NativeByteRange.loadRange world.pointers.heap.memory pointer ⟨16,8⟩ = some bytes at bytesEq
  have observedEq : observed = bytes := by
    simpa only [List.getElem?_cons_zero, Option.some.injEq] using headEq.symm
  subst observed
  refine ⟨lease,pointer,bytes,⟨selected,chosen,found,allowed⟩,bytesEq,encode_decode bytes value decoded,rfl,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [preparedState]; rfl
  · rw [preparedState, pointerEq]; rfl
  · rw [preparedState]; rfl

theorem read_failure_prefix (world next : State) (reference : Nat)
    (failed : read world reference = .invalid next) :
    next = world ∨ NativeReferenceMachine.execute world (.access reference 0 (.read 16 8)) = some next := by
  cases actual : NativeReferenceMachine.execute world (.access reference 0 (.read 16 8)) with
  | none => simp only [read, actual] at failed; cases failed; exact Or.inl rfl
  | some changed =>
    cases found : changed.outputs[0]? with
    | none => simp only [read, actual, found] at failed; cases failed; exact Or.inr rfl
    | some bytes =>
      cases decoded : decode bytes with
      | none => simp only [read, actual, found, decoded] at failed; cases failed; exact Or.inr rfl
      | some words => simp only [read, actual, found, decoded] at failed; cases failed

end FormalProof4FHE.HasteBoots.NativeLayoutBytes
