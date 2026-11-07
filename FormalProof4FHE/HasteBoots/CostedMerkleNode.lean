module
public import FormalProof4FHE.HasteBoots.FixedByteReadCost
public import FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
@[expose] public section

/-! Strict node decoding into two stored 64-byte digests. Raw fixed-size byte
arrays have no alternate canonical spelling: successful complete reading is
proved to reconstruct the original hash input. Charges count prefix/array
operations and construction, not physical/compiler/backend execution. -/
namespace FormalProof4FHE.HasteBoots.CostedMerkleNode
open InputIndexedOracle (Input Byte)
open NativeRootMessage (Digest)
open NativeGoldColumnAuthentication (nodeInput)
open SolverOperationCost (Run)

abbrev Stored := Vector Byte 64 × Vector Byte 64

def view (node : Stored) : Digest × Digest := (node.1.get,node.2.get)

def read (input : Input) : Run (Option Stored) :=
  let first := FixedByteReadCost.read 64 input
  match first.value with
  | none => ⟨none,first.cost+3⟩
  | some (left,tail) =>
    let second := FixedByteReadCost.read 64 tail
    match second.value with
    | none => ⟨none,first.cost+second.cost+5⟩
    | some (right,rest) =>
      ⟨if rest = [] then some (left,right) else none,first.cost+second.cost+7⟩

theorem read_cost (input : Input) : (read input).cost ≤ 911 := by
  have first := FixedByteReadCost.read_cost 64 input
  simp only [read]
  split
  · dsimp only; omega
  · rename_i left tail parsed
    have second := FixedByteReadCost.read_cost 64 tail
    split <;> dsimp only <;> omega

theorem read_sound (input : Input) (node : Stored) (found : (read input).value = some node) :
    nodeInput (view node).1 (view node).2 = input := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i left tail first
    split at found
    · contradiction
    · rename_i right rest second
      split at found
      · rename_i ended
        have same := Option.some.inj found
        subst node
        have leftParts := FixedByteReadCost.read_some 64 input left tail first
        have rightParts := FixedByteReadCost.read_some 64 tail right rest second
        simp only [view,nodeInput,FixedByteReadCost.ofFn_get]
        rw [leftParts,rightParts,ended,List.append_nil]
      · contradiction

theorem read_as_native (input : Input) :
    (read input).value.map view =
      ((NativePrefixCodec.product NativeByteCodec.digest NativeByteCodec.digest).read input).bind
        (fun parsed => if parsed.2 = [] then some parsed.1 else none) := by
  simp only [read,NativePrefixCodec.product,NativeByteCodec.digest,← FixedByteReadCost.read_value]
  cases first : (FixedByteReadCost.read 64 input).value with
  | none => rfl
  | some pair =>
    rcases pair with ⟨left,tail⟩
    simp only [Option.map_some,Option.bind_some]
    cases second : (FixedByteReadCost.read 64 tail).value with
    | none => rfl
    | some pair =>
      rcases pair with ⟨right,rest⟩
      by_cases ended : rest = [] <;> simp [ended,view]

def decode (input : Input) : Run (Option (Digest × Digest)) :=
  let result := read input
  ⟨result.value.map view,result.cost+3⟩

theorem decode_value (input : Input) :
    (decode input).value =
      (((NativePrefixCodec.product NativeByteCodec.digest NativeByteCodec.digest).read input).bind
        (fun parsed => if parsed.2 = [] then some parsed.1 else none)).bind
          (fun pair => if nodeInput pair.1 pair.2 = input then some pair else none) := by
  rw [← read_as_native]
  simp only [decode]
  cases parsed : (read input).value with
  | none => rfl
  | some node =>
    have canonical := read_sound input node parsed
    simp only [Option.map_some,Option.bind_some,canonical,ite_true]

theorem decode_cost (input : Input) : (decode input).cost ≤ 914 := by
  have bound := read_cost input
  simp only [decode]
  omega
end FormalProof4FHE.HasteBoots.CostedMerkleNode
