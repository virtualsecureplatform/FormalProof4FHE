module
import all FormalProof4FHE.HasteBoots.NativeByteRangeUpdate

namespace HasteBootsByteRangeUpdateSmoke
open FormalProof4FHE.HasteBoots
open NativeByteBorrow
open NativePointerStorage (Pointer Address)

private def prepared : Option (Pointer × Nat × Nat × State) := do
  let (p, state) ← allocate empty ⟨64, by decide⟩ ⟨4, 1⟩
  let state ← rawWrite state p 10
  let q ← NativeByteRange.pointerAt p 1
  let state ← rawWrite state q 20
  let q ← NativeByteRange.pointerAt p 2
  let state ← rawWrite state q 30
  let q ← NativeByteRange.pointerAt p 3
  let state ← rawWrite state q 40
  let (parent, state) ← borrow state none .exclusive p ⟨4, 1⟩
  let (child, state) ← borrow state (some parent) .exclusive p ⟨2, 1⟩
  pure (p, parent, child, state)

-- Whole-range ghost observation does not require a parent read permission.
example : (do
    let (p, _, _, state) ← prepared;
    NativeByteRange.loadRange state.memory p ⟨4, 1⟩) = some [10, 20, 30, 40] := by decide
example : (do
    let (_, parent, _, state) ← prepared; read state parent 0 4) = none := by decide
example : (do
    let (p, parent, _, state) ← prepared; let state ← write state parent 3 99;
    NativeByteRange.loadRange state.memory p ⟨4, 1⟩) = some [10, 20, 30, 99] := by decide
example : (do
    let (p, _, child, state) ← prepared; let state ← write state child 1 77;
    NativeByteRange.loadRange state.memory p ⟨4, 1⟩) = some [10, 77, 30, 40] := by decide
example : (do
    let (_, parent, _, state) ← prepared; write state parent 1 77) = none := by decide
example : (do
    let (_, _, child, state) ← prepared; write state child 2 77) = none := by decide
example : (do
    let (p, parent, _, state) ← prepared; let q ← NativeByteRange.pointerAt p 2;
    let state ← write state parent 3 99;
    NativeByteRange.loadRange state.memory q ⟨2, 1⟩) = some [30, 99] := by decide
example : (do
    let (p, parent, _, state) ← prepared;
    let (_, state) ← allocate state ⟨128, by decide⟩ ⟨3, 1⟩;
    let state ← write state parent 3 99;
    NativeByteRange.loadRange state.memory p ⟨4, 1⟩) = some [10, 20, 30, 99] := by decide
example : (do
    let (_, parent, _, state) ← prepared;
    let (other, state) ← allocate state ⟨128, by decide⟩ ⟨1, 1⟩;
    let state ← rawWrite state other 88; let state ← write state parent 3 99;
    NativeByteRange.loadRange state.memory other ⟨1, 1⟩) = some [88] := by decide

end HasteBootsByteRangeUpdateSmoke
