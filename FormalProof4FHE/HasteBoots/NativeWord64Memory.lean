module
public import FormalProof4FHE.HasteBoots.NativeByteRangeWrite
public import FormalProof4FHE.HasteBoots.TranscriptFrame
@[expose] public section

/-! Fixed-width little-endian u64 values over the concrete byte heap. This
supplies neither arbitrary typed/pointer validity nor a Rust layout theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeWord64Memory
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte State)

abbrev Word := Fin (2 ^ 64)

def encode (word : Word) : List Byte := TranscriptFrame.littleEndian 8 word.val

def decode (bytes : List Byte) : Option Word :=
  if length : bytes.length = 8 then
    some ⟨TranscriptFrame.fromLittleEndian bytes, by
      have fits := TranscriptFrame.fromLittleEndian_lt bytes
      rw [length] at fits
      exact fits⟩
  else none

def load (state : State) (pointer : Pointer) : Option Word :=
  (NativeByteRange.loadRange state pointer ⟨8, 8⟩).bind decode

def store (state : State) (pointer : Pointer) (word : Word) : Option State :=
  NativeByteRangeWrite.storeRange state pointer 8 (encode word)

def rawWrite (state : NativeByteBorrow.State) (pointer : Pointer) (word : Word) : Option NativeByteBorrow.State :=
  NativeByteRangeWrite.rawWrite state pointer 8 (encode word)

/-- Check the complete byte extent before converting an element offset to
an address. Metadata remains an element count; the byte stride is eight. -/
def element {mutable : Bool} (pointer : NativeRawPointer.RawPtr (List Word) mutable) (index : Nat) :
    Option (NativeRawPointer.RawPtr Word mutable) :=
  match pointer.metadata with
  | .slice length =>
    if index < length.val ∧ NativeByteRange.Geometry pointer.storage ⟨8 * length.val, 8⟩ then
      (NativeByteRange.pointerAt pointer.storage (8 * index)).map (fun reference => ⟨reference, .thin⟩)
    else none
  | .thin | .vtable _ => none

def borrowSlice {mutable : Bool} (state : NativeByteBorrow.State) (parent : Option Nat) (mode : NativeByteBorrow.Mode)
    (pointer : NativeRawPointer.RawPtr (List Word) mutable) : Option (Nat × NativeByteBorrow.State) :=
  match pointer.metadata with
  | .slice length => NativeByteBorrow.borrow state parent mode pointer.storage ⟨8 * length.val, 8⟩
  | .thin | .vtable _ => none

theorem encode_length (word : Word) : (encode word).length = 8 := TranscriptFrame.littleEndian_length 8 word.val

theorem decode_encode (word : Word) : decode (encode word) = some word := by
  unfold decode
  rw [dite_eq_left (encode_length word)]
  have value := TranscriptFrame.fromLittleEndian_littleEndian 8 word.val word.isLt
  apply congrArg some
  apply Fin.ext
  exact value

theorem encode_decode (bytes : List Byte) (word : Word) (decoded : decode bytes = some word) : encode word = bytes := by
  unfold decode at decoded
  split at decoded
  next length =>
    cases decoded
    unfold encode
    rw [← length]
    exact TranscriptFrame.littleEndian_fromLittleEndian bytes
  next => cases decoded

theorem decode_wrong_length (bytes : List Byte) (wrong : bytes.length ≠ 8) : decode bytes = none := by
  exact dite_eq_right wrong

theorem store_then_load (state next : State) (pointer : Pointer) (word : Word)
    (stored : store state pointer word = some next) : load next pointer = some word := by
  have loaded := NativeByteRangeWrite.storeRange_then_load state pointer 8 (encode word) next stored
  rw [encode_length] at loaded
  simp only [load, loaded, Option.bind, decode_encode]

theorem store_wellFormed (state next : State) (valid : NativeByteMemory.WellFormed state) (pointer : Pointer) (word : Word)
    (stored : store state pointer word = some next) : NativeByteMemory.WellFormed next :=
  NativeByteRangeWrite.storeRange_wellFormed state valid pointer 8 (encode word) next stored

theorem store_defined_iff (state : State) (valid : NativeByteMemory.WellFormed state) (pointer : Pointer) (word : Word) :
    (∃ next, store state pointer word = some next) ↔ NativeByteRange.checkRange state pointer ⟨8, 8⟩ = true := by
  simpa only [store, encode_length] using NativeByteRangeWrite.storeRange_defined_iff state valid pointer 8 (encode word)

theorem rawWrite_wellFormed (state next : NativeByteBorrow.State) (valid : NativeByteBorrow.WellFormed state)
    (pointer : Pointer) (word : Word) (stored : rawWrite state pointer word = some next) : NativeByteBorrow.WellFormed next :=
  NativeByteRangeWrite.rawWrite_wellFormed state next valid pointer 8 (encode word) stored

theorem element_fields {mutable : Bool} (pointer : NativeRawPointer.RawPtr (List Word) mutable) (index : Nat)
    (result : NativeRawPointer.RawPtr Word mutable) (executed : element pointer index = some result) :
    ∃ length, pointer.metadata = .slice length ∧ index < length.val ∧
      NativeByteRange.Geometry pointer.storage ⟨8 * length.val, 8⟩ ∧
      result.storage.address.val = pointer.storage.address.val + 8 * index ∧
      result.storage.provenance = pointer.storage.provenance ∧ result.metadata = .thin := by
  unfold element at executed
  cases metadata : pointer.metadata with
  | thin => simp only [metadata] at executed; cases executed
  | vtable table => simp only [metadata] at executed; cases executed
  | slice length =>
    simp only [metadata] at executed
    split at executed
    next valid =>
      cases advanced : NativeByteRange.pointerAt pointer.storage (8 * index) with
      | none => simp only [advanced, Option.map_none] at executed; cases executed
      | some reference =>
        simp only [advanced, Option.map_some] at executed
        cases executed
        have fields := NativeByteRange.pointerAt_fields pointer.storage (8 * index) reference advanced
        exact ⟨length, rfl, valid.1, valid.2, fields.1, fields.2, rfl⟩
    next => cases executed

theorem element_exists {mutable : Bool} (pointer : NativeRawPointer.RawPtr (List Word) mutable)
    (length : NativePointerStorage.Address) (metadata : pointer.metadata = .slice length)
    (index : Nat) (inside : index < length.val)
    (geometry : NativeByteRange.Geometry pointer.storage ⟨8 * length.val, 8⟩) :
    ∃ result, element pointer index = some result := by
  have fits : pointer.storage.address.val + 8 * index < 2 ^ 64 := by
    have upper : pointer.storage.address.val + 8 * length.val < 2 ^ 64 := geometry.2.2.2
    omega
  let reference : Pointer := ⟨⟨pointer.storage.address.val + 8 * index, fits⟩, pointer.storage.provenance⟩
  have advanced : NativeByteRange.pointerAt pointer.storage (8 * index) = some reference := dite_eq_left fits
  exact ⟨⟨reference, .thin⟩, by simp only [element, metadata, ite_eq_left (And.intro inside geometry), advanced, Option.map_some]⟩

theorem element_geometry {mutable : Bool} (pointer : NativeRawPointer.RawPtr (List Word) mutable) (index : Nat)
    (result : NativeRawPointer.RawPtr Word mutable) (executed : element pointer index = some result) :
    NativeByteRange.Geometry result.storage ⟨8, 8⟩ := by
  obtain ⟨length, _, inside, geometry, address, _, _⟩ := element_fields pointer index result executed
  refine ⟨by decide, ?_, ?_, ?_⟩
  · have nonzero := geometry.2.1
    omega
  · rw [address]
    simp only [Nat.add_mod, geometry.2.2.1, Nat.mul_mod_right, Nat.add_zero]
  · change result.storage.address.val + 8 < 2 ^ 64
    have upper : pointer.storage.address.val + 8 * length.val < 2 ^ 64 := geometry.2.2.2
    omega

theorem borrowSlice_exact {mutable : Bool} (state : NativeByteBorrow.State) (parent : Option Nat)
    (mode : NativeByteBorrow.Mode) (pointer : NativeRawPointer.RawPtr (List Word) mutable)
    (length : NativePointerStorage.Address) (metadata : pointer.metadata = .slice length) :
    borrowSlice state parent mode pointer = NativeByteBorrow.borrow state parent mode pointer.storage ⟨8 * length.val, 8⟩ := by
  simp only [borrowSlice, metadata]

theorem borrowed_byte_extent {mutable : Bool} (state : NativeByteBorrow.State) (parent : Option Nat)
    (mode : NativeByteBorrow.Mode) (pointer : NativeRawPointer.RawPtr (List Word) mutable)
    (length : NativePointerStorage.Address) (metadata : pointer.metadata = .slice length)
    (tag : Nat) (next : NativeByteBorrow.State) (issued : borrowSlice state parent mode pointer = some (tag, next)) :
    NativeByteRange.Geometry pointer.storage ⟨8 * length.val, 8⟩ ∧
      ∃ bytes, NativeByteRange.loadRange state.memory pointer.storage ⟨8 * length.val, 8⟩ = some bytes ∧
        bytes.length = 8 * length.val := by
  rw [borrowSlice_exact state parent mode pointer length metadata] at issued
  obtain ⟨_, _, _, _, _, bytes, loaded⟩ := NativeByteBorrow.borrow_success state parent mode pointer.storage ⟨8 * length.val, 8⟩ tag next issued
  exact ⟨NativeByteBorrow.borrow_geometry state parent mode pointer.storage ⟨8 * length.val, 8⟩ tag next issued,
    bytes, loaded, NativeByteRange.loadRange_length state.memory pointer.storage ⟨8 * length.val, 8⟩ bytes loaded⟩

theorem store_frame (state next : State) (pointer : Pointer) (word : Word)
    (stored : store state pointer word = some next) (reference : Pointer)
    (separate : reference.provenance ≠ pointer.provenance ∨ reference.address.val < pointer.address.val ∨
      pointer.address.val + 8 ≤ reference.address.val) :
    NativeByteMemory.loadByte next reference = NativeByteMemory.loadByte state reference := by
  apply NativeByteRangeWrite.storeRange_frame state pointer 8 (encode word) next stored reference
  simpa only [encode_length] using separate

theorem store_after_deallocation (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (layout : NativeByteMemory.Layout) (next : State)
    (released : NativeByteMemory.deallocate state pointer layout = some next) (reference : Pointer)
    (sameOrigin : reference.provenance = pointer.provenance) (word : Word) : store next reference word = none :=
  NativeByteRangeWrite.storeRange_after_deallocation state valid pointer layout next released reference sameOrigin 8 (encode word)
    (by rw [encode_length]; decide)

theorem load_iff_bytes (state : State) (pointer : Pointer) (word : Word) :
    load state pointer = some word ↔ NativeByteRange.loadRange state pointer ⟨8, 8⟩ = some (encode word) := by
  constructor
  · intro loaded
    unfold load at loaded
    cases bytesRead : NativeByteRange.loadRange state pointer ⟨8, 8⟩ with
    | none => simp only [bytesRead, Option.bind] at loaded; cases loaded
    | some bytes =>
      simp only [bytesRead, Option.bind] at loaded
      rw [encode_decode bytes word loaded]
  · intro bytesRead
    simp only [load, bytesRead, Option.bind, decode_encode]

end FormalProof4FHE.HasteBoots.NativeWord64Memory
