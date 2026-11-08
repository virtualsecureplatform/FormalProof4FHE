module
import all FormalProof4FHE.HasteBoots.NativeByteBorrow

namespace HasteBootsByteBorrowSmoke
open FormalProof4FHE.HasteBoots
open NativeByteBorrow
open NativePointerStorage (Pointer Address)

private def base : Address := ⟨64, by decide⟩
private def prepared : Option (Pointer × State) := do
  let (p, state) ← allocate empty base ⟨4, 1⟩
  let state ← rawWrite state p 10
  let q ← NativeByteRange.pointerAt p 1
  let state ← rawWrite state q 20
  let q ← NativeByteRange.pointerAt p 2
  let state ← rawWrite state q 30
  let q ← NativeByteRange.pointerAt p 3
  let state ← rawWrite state q 40
  pure (p, state)

private def exclusive : Option (Pointer × Nat × State) := do
  let (p, state) ← prepared
  let (tag, state) ← borrow state none .exclusive p ⟨4, 1⟩
  pure (p, tag, state)

private def shared : Option (Pointer × Nat × State) := do
  let (p, state) ← prepared
  let (tag, state) ← borrow state none .shared p ⟨4, 1⟩
  pure (p, tag, state)

example : (do
    let (p, state) ← prepared; rawRead state p ⟨4, 1⟩) = some [10, 20, 30, 40] := by decide
example : (do
    let (p, _, state) ← shared; rawRead state p ⟨4, 1⟩) = some [10, 20, 30, 40] := by decide
example : (do
    let (p, _, state) ← shared; let (tag, _) ← borrow state none .shared p ⟨4, 1⟩; pure tag) = some 1 := by decide
example : (do
    let (p, _, state) ← shared; borrow state none .exclusive p ⟨4, 1⟩) = none := by decide
example : (do
    let (_, tag, state) ← shared; write state tag 0 77) = none := by decide
example : (do
    let (p, _, state) ← shared; rawWrite state p 77) = none := by decide
example : (do
    let (p, _, state) ← shared; deallocate state p ⟨4, 1⟩) = none := by decide
example : (do
    let (p, _, state) ← exclusive; rawRead state p ⟨4, 1⟩) = none := by decide
example : (do
    let (p, _, state) ← exclusive; rawWrite state p 77) = none := by decide
example : (do
    let (p, _, state) ← exclusive; deallocate state p ⟨4, 1⟩) = none := by decide
example : (do
    let (_, tag, state) ← exclusive; read state tag 0 4) = some [10, 20, 30, 40] := by decide
example : (do
    let (_, tag, state) ← exclusive; let state ← write state tag 1 77; read state tag 0 4) = some [10, 77, 30, 40] := by decide
example : (do
    let (_, tag, state) ← exclusive; write state tag 4 77) = none := by decide
example : (do
    let (p, tag, state) ← exclusive; let state ← endBorrow state tag; let state ← rawWrite state p 77;
    rawRead state p ⟨1, 1⟩) = some [77] := by decide
example : (do
    let (_, tag, state) ← exclusive; let state ← endBorrow state tag; read state tag 0 1) = none := by decide
example : (do
    let (_, tag, state) ← exclusive; let state ← endBorrow state tag; write state tag 0 77) = none := by decide

private def child : Option (Pointer × Nat × Nat × State) := do
  let (p, parent, state) ← exclusive
  let (child, state) ← borrow state (some parent) .exclusive p ⟨2, 1⟩
  pure (p, parent, child, state)

example : (do
    let (_, parent, _, state) ← child; endBorrow state parent) = none := by decide
example : (do
    let (_, parent, _, state) ← child; read state parent 0 4) = none := by decide
example : (do
    let (_, parent, _, state) ← child; write state parent 0 77) = none := by decide
example : (do
    let (_, parent, child, state) ← child; let state ← write state parent 3 77;
    read state child 0 2) = some [10, 20] := by decide
example : (do
    let (_, _, child, state) ← child; let state ← write state child 1 88;
    read state child 0 2) = some [10, 88] := by decide
example : (do
    let (_, parent, child, state) ← child; let state ← write state child 1 88;
    let state ← endBorrow state child; read state parent 0 4) = some [10, 88, 30, 40] := by decide
example : (do
    let (p, parent, _, state) ← child; let q ← NativeByteRange.pointerAt p 2;
    let (sibling, _) ← borrow state (some parent) .exclusive q ⟨2, 1⟩; pure sibling) = some 2 := by decide
example : (do
    let (p, parent, _, state) ← child; let q ← NativeByteRange.pointerAt p 1;
    borrow state (some parent) .exclusive q ⟨2, 1⟩) = none := by decide
example : (do
    let (p, _, child, state) ← child; let (grandchild, state) ← borrow state (some child) .exclusive p ⟨1, 1⟩;
    let state ← write state grandchild 0 99; read state grandchild 0 1) = some [99] := by decide
example : (do
    let (p, _, child, state) ← child; let (_, state) ← borrow state (some child) .exclusive p ⟨1, 1⟩;
    endBorrow state child) = none := by decide
example : (do
    let (p, parent, state) ← shared; borrow state (some parent) .exclusive p ⟨1, 1⟩) = none := by decide
example : (do
    let (p, parent, state) ← exclusive; let (_, state) ← borrow state (some parent) .shared p ⟨2, 1⟩;
    read state parent 0 4) = some [10, 20, 30, 40] := by decide
example : (do
    let (p, parent, state) ← exclusive; let (_, state) ← borrow state (some parent) .shared p ⟨2, 1⟩;
    write state parent 0 99) = none := by decide
example : (do
    let (p, parent, state) ← exclusive; let state ← endBorrow state parent;
    let (fresh, state) ← borrow state none .exclusive p ⟨4, 1⟩;
    pure (fresh, read state parent 0 4)) = some (1, none) := by decide
example : read empty 42 0 0 = none := by decide
example : write empty 42 0 77 = none := by decide
example : borrow empty (some 42) .shared ⟨base, none⟩ ⟨0, 1⟩ = none := by decide
example : borrow empty none .exclusive ⟨0, none⟩ ⟨0, 1⟩ = none := by decide
example : (do
    let (tag, state) ← borrow empty none .exclusive ⟨base, none⟩ ⟨0, 1⟩;
    read state tag 0 0) = some [] := by decide
example : (do
    let (_, state) ← borrow empty none .exclusive ⟨base, none⟩ ⟨0, 1⟩;
    let (p, state) ← allocate state base ⟨1, 1⟩;
    let state ← rawWrite state p 77; let state ← deallocate state p ⟨1, 1⟩;
    pure state.memory.blocks.length) = some 0 := by decide

end HasteBootsByteBorrowSmoke
