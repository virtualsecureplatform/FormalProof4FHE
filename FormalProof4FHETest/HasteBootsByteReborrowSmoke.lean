module
import all FormalProof4FHE.HasteBoots.NativeByteReborrow

namespace HasteBootsByteReborrowSmoke
open FormalProof4FHE.HasteBoots
open NativeByteBorrow
open NativePointerStorage (Pointer)

private def prepared (mode : Mode) : Option (Pointer × Nat × State) := do
  let (pointer, state) ← allocate empty ⟨64, by decide⟩ ⟨4, 1⟩
  let state ← rawWrite state pointer 10
  let p ← NativeByteRange.pointerAt pointer 1
  let state ← rawWrite state p 20
  let p ← NativeByteRange.pointerAt pointer 2
  let state ← rawWrite state p 30
  let p ← NativeByteRange.pointerAt pointer 3
  let state ← rawWrite state p 40
  let (parent, state) ← borrow state none mode pointer ⟨4, 1⟩
  pure (pointer, parent, state)

example : (do
    let (_, parent, state) ← prepared .exclusive
    let (old, _) ← NativeByteReborrow.replaceAt state parent 2 99
    pure old) = some (some 30) := by decide
example : (do
    let (p, parent, state) ← prepared .exclusive
    let (_, state) ← NativeByteReborrow.replaceAt state parent 2 99
    NativeByteRange.loadRange state.memory p ⟨4, 1⟩) = some [10, 20, 99, 40] := by decide
example : (do
    let (_, parent, state) ← prepared .exclusive
    let (_, state) ← NativeByteReborrow.replaceAt state parent 2 99
    read state parent 0 4) = some [10, 20, 99, 40] := by decide
example : (do
    let (_, parent, state) ← prepared .exclusive
    let (_, next) ← NativeByteReborrow.replaceAt state parent 2 99
    pure (next.leases == state.leases, next.nextTag)) = some (true, 2) := by decide
example : (do
    let (_, parent, state) ← prepared .exclusive
    let (_, next) ← NativeByteReborrow.replaceAt state parent 2 99
    read next state.nextTag 0 1) = none := by decide
example : (do
    let (_, parent, state) ← prepared .exclusive
    let (_, next) ← NativeByteReborrow.replaceAt state parent 2 99
    let (_, finalState) ← NativeByteReborrow.replaceAt next parent 2 88
    pure (finalState.nextTag, lookup finalState.leases 1, lookup finalState.leases 2)) = some (3, none, none) := by decide
example : (do
    let (_, parent, state) ← prepared .exclusive
    let (old, next) ← NativeByteReborrow.replaceAt state parent 4 99
    pure (old, next == state)) = some (none, true) := by decide
example : (do
    let (_, parent, state) ← prepared .shared
    NativeByteReborrow.replaceAt state parent 0 99) = none := by decide
example : (do
    let (_, _, state) ← prepared .exclusive
    NativeByteReborrow.replaceAt state 999 0 99) = none := by decide
example : (do
    let (p, parent, state) ← prepared .exclusive
    let (_, state) ← borrow state (some parent) .exclusive p ⟨2, 1⟩
    let (old, next) ← NativeByteReborrow.replaceAt state parent 3 99
    let bytes ← NativeByteRange.loadRange next.memory p ⟨4, 1⟩
    pure (old, bytes, next.leases == state.leases)) = some (some 40, [10, 20, 30, 99], true) := by decide
example : (do
    let (p, parent, state) ← prepared .exclusive
    let (_, state) ← borrow state (some parent) .exclusive p ⟨2, 1⟩
    NativeByteReborrow.replaceAt state parent 0 99) = none := by decide
example : (do
    let (p, parent, state) ← prepared .exclusive
    let (child, state) ← borrow state (some parent) .exclusive p ⟨2, 1⟩
    let (old, next) ← NativeByteReborrow.replaceAt state child 1 99
    let bytes ← NativeByteRange.loadRange next.memory p ⟨4, 1⟩
    pure (old, bytes, next.leases == state.leases)) = some (some 20, [10, 99, 30, 40], true) := by decide

end HasteBootsByteReborrowSmoke
