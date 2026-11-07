module
public import FormalProof4FHE.HasteBoots.StoredDigestVectorReadCost
public import FormalProof4FHE.HasteBoots.StoredDigestView
public import FormalProof4FHE.HasteBoots.RowEncodingCost
public import FormalProof4FHE.HasteBoots.NativeExactCodec
@[expose] public section

/-! Strict native digest-vector decoding with charged canonical serialization
and exact input comparison. Order, duplicates and every raw digest byte are
preserved. No digest/serializer callback executes. Charges are abstract
byte/list/access operations; physical/compiler/native refinement is separate. -/
namespace FormalProof4FHE.HasteBoots.StoredDigestVectorCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
open StoredDigestVectorReadCost (Root Roots view)

def body : List Root → Run Input
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := StoredDigestView.fromVector head
    let rest := body tail
    let joined := RowEncodingCost.append first.value.val rest.value
    ⟨joined.value,first.cost+rest.cost+joined.cost+5⟩

theorem body_value (roots : List Root) : (body roots).value = roots.flatMap (fun root => root.toList) := by
  induction roots with
  | nil => rfl
  | cons head tail ih => simp only [body,StoredDigestView.fromVector,RowEncodingCost.append_value,List.flatMap_cons,ih]

theorem body_cost (roots : List Root) : (body roots).cost = 327*roots.length+1 := by
  induction roots with
  | nil => rfl
  | cons head tail ih =>
    simp only [body,StoredDigestView.fromVector,RowEncodingCost.append_cost,Vector.length_toList,ih,List.length_cons]
    omega

def encode (roots : Roots) : Run Input :=
  let count := RowEncodingCost.length roots.val
  let header := IntegerEncodingCost.encode ⟨count.value,by rw [RowEncodingCost.length_value]; exact roots.property⟩
  let bytes := body roots.val
  let joined := RowEncodingCost.append header.value bytes.value
  ⟨joined.value,count.cost+header.cost+bytes.cost+joined.cost+4⟩

theorem encode_value (roots : Roots) :
    (encode roots).value = (NativePrefixCodec.vector NativeByteCodec.digest).encode (view roots) := by
  simp only [encode,RowEncodingCost.append_value,RowEncodingCost.length_value,
    IntegerEncodingCost.encode_value,body_value,NativePrefixCodec.vector,view,List.length_map,
    NativePrefixCodec.usize,List.flatMap_map,NativeByteCodec.digest,
    NativeByteCodec.fixed,FixedByteReadCost.ofFn_get]

theorem encode_cost (roots : Roots) : (encode roots).cost ≤ 330*roots.val.length+93 := by
  have header := IntegerEncodingCost.encode_cost
    (⟨(RowEncodingCost.length roots.val).value,by rw [RowEncodingCost.length_value]; exact roots.property⟩ : NativeUsizeMessage.Usize)
  have headerSize := IntegerEncodingCost.encode_length
    (⟨(RowEncodingCost.length roots.val).value,by rw [RowEncodingCost.length_value]; exact roots.property⟩ : NativeUsizeMessage.Usize)
  simp only [encode,RowEncodingCost.length_cost,body_cost,RowEncodingCost.append_cost]
  omega

def parse (input : Input) : Run (Option Roots) :=
  let result := StoredDigestVectorReadCost.read input
  match result.value with
  | none => ⟨none,result.cost+2⟩
  | some (roots,rest) => ⟨if rest = [] then some roots else none,result.cost+3⟩

theorem parse_cost (input : Input) : (parse input).cost ≤ 457*(input.length/64+1)+113 := by
  have bound := StoredDigestVectorReadCost.read_cost input
  simp only [parse]
  split <;> dsimp only <;> omega

theorem parse_size (input : Input) (roots : Roots) (found : (parse input).value = some roots) :
    roots.val.length ≤ input.length/64 := by
  simp only [parse] at found
  split at found
  · contradiction
  · rename_i values rest parsed
    have size := StoredDigestVectorReadCost.read_size input values rest parsed
    split at found
    · have same := Option.some.inj found
      subst roots
      omega
    · contradiction

def decode (input : Input) : Run (Option Roots) :=
  let parsed := parse input
  match parsed.value with
  | none => ⟨none,parsed.cost+2⟩
  | some roots =>
    let canonical := encode roots
    let compared := BytePrefixMatchCost.equal canonical.value input
    ⟨if compared.value then some roots else none,parsed.cost+canonical.cost+compared.cost+5⟩

theorem decode_value (input : Input) :
    (decode input).value.map view = NativeExactCodec.read (NativePrefixCodec.vector NativeByteCodec.digest) input := by
  simp only [NativeExactCodec.read,← StoredDigestVectorReadCost.read_value]
  cases parsed : (StoredDigestVectorReadCost.read input).value with
  | none => simp only [decode,parse,parsed,Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨roots,rest⟩
    by_cases ended : rest = [] <;>
      by_cases same : (NativePrefixCodec.vector NativeByteCodec.digest).encode (view roots) = input <;>
        simp [decode,parse,parsed,ended,same,encode_value,BytePrefixMatchCost.equal_value]

theorem decode_cost (input : Input) :
    (decode input).cost ≤ 787*(input.length/64+1)+6*input.length+1 := by
  have parsed := parse_cost input
  simp only [decode]
  split
  · dsimp only; omega
  · rename_i roots found
    have size := parse_size input roots found
    have encoded := encode_cost roots
    have compared := BytePrefixMatchCost.equal_cost (encode roots).value input
    have length := Nat.min_le_right (encode roots).value.length input.length
    dsimp only
    omega

theorem decode_size (input : Input) (roots : Roots) (found : (decode input).value = some roots) :
    roots.val.length ≤ input.length/64 := by
  simp only [decode] at found
  split at found
  · contradiction
  · rename_i values parsed
    split at found
    · have same := Option.some.inj found
      subst roots
      exact parse_size input values parsed
    · contradiction

theorem decode_sound (input : Input) (roots : Roots) (found : (decode input).value = some roots) :
    (NativePrefixCodec.vector NativeByteCodec.digest).encode (view roots) = input := by
  have native := decode_value input
  rw [found,Option.map_some] at native
  exact NativeExactCodec.read_sound _ _ _ native.symm

theorem view_injective : Function.Injective view := by
  intro left right same
  apply Subtype.ext
  have data := congrArg Subtype.val same
  have injective : Function.Injective (fun root : Root => root.get) := by
    intro first last equal
    apply Vector.ext
    intro i hi
    exact congrFun equal ⟨i,hi⟩
  exact (List.map_injective_iff.mpr injective) data

theorem decode_encode (roots : Roots) : (decode (encode roots).value).value = some roots := by
  have accepted : NativeExactCodec.read (NativePrefixCodec.vector NativeByteCodec.digest) (encode roots).value =
      some (view roots) := by
    rw [encode_value]
    exact NativeExactCodec.read_encode _ _
  have native := (decode_value (encode roots).value).trans accepted
  cases parsed : (decode (encode roots).value).value with
  | none => rw [parsed,Option.map_none] at native; cases native
  | some values =>
    rw [parsed,Option.map_some] at native
    exact congrArg some (view_injective (Option.some.inj native))
end FormalProof4FHE.HasteBoots.StoredDigestVectorCost
