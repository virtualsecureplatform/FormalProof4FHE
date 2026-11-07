module
public import FormalProof4FHE.HasteBoots.BytePrefixCost
public import FormalProof4FHE.HasteBoots.NativeByteCodec
@[expose] public section

/-! Exact-width byte reads into stored vectors. Prefix extraction, list-to-array
loads/stores and result construction are charged. Truncated reads stop at the
supplied input length. Physical/compiler refinement is separate. -/
namespace FormalProof4FHE.HasteBoots.FixedByteReadCost
open InputIndexedOracle (Input Byte)
open SolverOperationCost (Run)

theorem takeExact_parts (count : ℕ) (input first rest : Input)
    (found : (BytePrefixCost.takeExact count input).value = some (first,rest)) :
    first.length = count ∧ input = first++rest := by
  rw [BytePrefixCost.takeExact_value] at found
  split at found
  · rename_i enough
    have pair := Option.some.inj found
    cases pair
    exact ⟨by rw [List.length_take,Nat.min_eq_left enough],(List.take_append_drop count input).symm⟩
  · contradiction

def read (count : ℕ) (input : Input) : Run (Option (Vector Byte count × Input)) :=
  let prefixRead := BytePrefixCost.takeExact count input
  match found : prefixRead.value with
  | none => ⟨none,prefixRead.cost+2⟩
  | some (first,rest) =>
    have size : first.toArray.size = count := by
      rw [List.size_toArray]
      exact (takeExact_parts count input first rest found).1
    ⟨some (⟨first.toArray,size⟩,rest),prefixRead.cost+2*count+3⟩

theorem read_cost (count : ℕ) (input : Input) :
    (read count input).cost ≤ 7*min count input.length+4 := by
  have prefixCost := BytePrefixCost.takeExact_cost count input
  simp only [read]
  split
  · dsimp only; omega
  · rename_i first rest found
    have parts := takeExact_parts count input first rest found
    have enough : count ≤ input.length := by rw [parts.2,List.length_append,parts.1]; omega
    dsimp only
    omega

theorem read_some (count : ℕ) (input : Input) (value : Vector Byte count) (rest : Input)
    (found : (read count input).value = some (value,rest)) :
    input = value.toList++rest := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i first tail parsed
    have parts := takeExact_parts count input first tail parsed
    have same := Option.some.inj found
    cases same
    simpa only [Vector.toList,List.toList_toArray] using parts.2

theorem ofFn_get {count : ℕ} (value : Vector Byte count) :
    List.ofFn value.get = value.toList := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp only [List.getElem_ofFn,Vector.getElem_toList]
    rfl

theorem read_value (count : ℕ) (input : Input) :
    (read count input).value.map (fun pair => (pair.1.get,pair.2)) =
      (NativeByteCodec.fixed count).read input := by
  simp only [read]
  split
  · rename_i parsed
    have short : (input.take count).length ≠ count := by
      intro size
      have enough : count ≤ input.length := calc
        count = (input.take count).length := size.symm
        _ = min count input.length := List.length_take
        _ ≤ input.length := Nat.min_le_right _ _
      have full := BytePrefixCost.takeExact_value count input
      rw [parsed,ite_eq_left enough] at full
      contradiction
    simp only [Option.map_none,NativeByteCodec.fixed,dite_eq_right short]
  · rename_i first rest parsed
    have parts := takeExact_parts count input first rest parsed
    have before : input.take count = first := by rw [parts.2,← parts.1,List.take_left]
    have after : input.drop count = rest := by rw [parts.2,← parts.1,List.drop_left]
    simp only [Option.map_some,NativeByteCodec.fixed,before,parts.1,dite_true,after]
    congr 1
end FormalProof4FHE.HasteBoots.FixedByteReadCost
