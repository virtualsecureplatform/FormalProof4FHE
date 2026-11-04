module

public import FormalProof4FHE.HasteBoots.NativeIntegerPrefix

@[expose] public section

/-!
# Compositional native transcript encoding with prefix left inverses

These readers prove self-delimitation of constructed wire messages, including
trailing bytes. They are structural readers, not an equivalence theorem for
the native adversarial proof-byte deserializer or its resource/error behavior.
-/

namespace FormalProof4FHE.HasteBoots.NativePrefixCodec

open InputIndexedOracle (Input)
open NativeUsizeMessage (Usize)

structure Codec (A : Type) where
  encode : A → Input
  read : Input → Option (A × Input)
  read_encode : ∀ value suffix, read (encode value ++ suffix) = some (value, suffix)

theorem Codec.prefix_injective {A : Type} (codec : Codec A) (left right : A) (first last : Input)
    (same : codec.encode left ++ first = codec.encode right ++ last) : left = right ∧ first = last := by
  have parsed := congrArg codec.read same
  rw [codec.read_encode, codec.read_encode] at parsed
  exact Prod.mk.inj (Option.some.inj parsed)

theorem Codec.encode_injective {A : Type} (codec : Codec A) : Function.Injective codec.encode := by
  intro left right same
  exact (codec.prefix_injective left right [] [] (by simpa only [List.append_nil] using same)).1

def usize : Codec Usize where
  encode := NativeUsizeMessage.encode
  read := fun bytes => (NativeIntegerPrefix.read bytes).bind (fun pair =>
    if fits : pair.1 < 2 ^ 64 then some (⟨pair.1, fits⟩, pair.2) else none)
  read_encode := by
    intro value suffix
    rw [NativeIntegerPrefix.read_encode, Option.bind_some, dite_eq_left value.isLt]

def product {A B : Type} (first : Codec A) (second : Codec B) : Codec (A × B) where
  encode := fun pair => first.encode pair.1 ++ second.encode pair.2
  read := fun bytes => (first.read bytes).bind (fun left =>
    (second.read left.2).map (fun right => ((left.1, right.1), right.2)))
  read_encode := by
    intro pair suffix
    rw [List.append_assoc, first.read_encode, Option.bind_some, second.read_encode]
    rfl

def transport {A B : Type} (codec : Codec A) (equiv : A ≃ B) : Codec B where
  encode := fun value => codec.encode (equiv.symm value)
  read := fun bytes => (codec.read bytes).map (fun pair => (equiv pair.1, pair.2))
  read_encode := by
    intro value suffix
    rw [codec.read_encode, Option.map_some, equiv.apply_symm_apply]

def readCount {A : Type} (codec : Codec A) : ℕ → Input → Option (List A × Input)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => (codec.read bytes).bind (fun entry =>
      (readCount codec count entry.2).map (fun rest => (entry.1 :: rest.1, rest.2)))

theorem readCount_encode {A : Type} (codec : Codec A) (values : List A) (suffix : Input) :
    readCount codec values.length (values.flatMap codec.encode ++ suffix) = some (values, suffix) := by
  induction values with
  | nil => rfl
  | cons value tail ih =>
    simp only [List.length_cons, readCount, List.flatMap_cons, List.append_assoc]
    rw [codec.read_encode, Option.bind_some, ih]
    rfl

/-- The native target is 64-bit: vector lengths retain their usize bound. -/
abbrev Vector (A : Type) := { values : List A // values.length < 2 ^ 64 }

def vector {A : Type} (codec : Codec A) : Codec (Vector A) where
  encode := fun values => usize.encode ⟨values.val.length, values.property⟩ ++
    values.val.flatMap codec.encode
  read := fun bytes => (usize.read bytes).bind (fun count =>
    (readCount codec count.1.val count.2).bind (fun result =>
      if fits : result.1.length < 2 ^ 64 then some (⟨result.1, fits⟩, result.2) else none))
  read_encode := by
    intro values suffix
    rw [List.append_assoc, usize.read_encode, Option.bind_some, readCount_encode,
      Option.bind_some, dite_eq_left values.property]

def fixed {A : Type} (codec : Codec A) (count : ℕ) (fits : count < 2 ^ 64) : Codec (Fin count → A) where
  encode := fun value => (vector codec).encode ⟨List.ofFn value, by simpa only [List.length_ofFn] using fits⟩
  read := fun bytes => ((vector codec).read bytes).bind (fun result =>
    if length : result.1.val.length = count then
      some ((fun index => result.1.val[index.val]'(by rw [length]; exact index.isLt)), result.2)
    else none)
  read_encode := by
    intro value suffix
    rw [(vector codec).read_encode, Option.bind_some]
    simp only [List.length_ofFn, dite_true, List.getElem_ofFn]

end FormalProof4FHE.HasteBoots.NativePrefixCodec
