module
public import FormalProof4FHE.HasteBoots.StoredSourceVectorReadCost
public import FormalProof4FHE.HasteBoots.StoredDigestView
public import FormalProof4FHE.HasteBoots.RowEncodingCost
public import FormalProof4FHE.HasteBoots.NativeExactCodec
@[expose] public section

/-! Strict native context/root source-vector decoding with charged canonical serialization
and exact input comparison. Order, duplicates and every raw context/root byte are
preserved. No context/root/serializer callback executes. Charges are abstract
byte/list/access operations; physical/compiler/native refinement is separate. -/
namespace FormalProof4FHE.HasteBoots.StoredSourceVectorCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source Sources sourceView view)

def sourceBytes (source : Source) : Run Input :=
  let context := StoredDigestView.fromVector source.1
  let root := StoredDigestView.fromVector source.2
  let joined := RowEncodingCost.append context.value.val root.value.val
  ⟨joined.value,context.cost+root.cost+joined.cost+4⟩

theorem sourceBytes_value (source : Source) :
    (sourceBytes source).value = source.1.toList++source.2.toList := by
  simp only [sourceBytes,StoredDigestView.fromVector,RowEncodingCost.append_value]

theorem sourceBytes_cost (source : Source) : (sourceBytes source).cost = 455 := by
  simp only [sourceBytes,StoredDigestView.fromVector,RowEncodingCost.append_cost,Vector.length_toList]

theorem sourceBytes_size (source : Source) : (sourceBytes source).value.length = 128 := by
  simp only [sourceBytes_value,List.length_append,Vector.length_toList]

def body : List Source → Run Input
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := sourceBytes head
    let rest := body tail
    let joined := RowEncodingCost.append first.value rest.value
    ⟨joined.value,first.cost+rest.cost+joined.cost+5⟩

theorem body_value (roots : List Source) : (body roots).value = roots.flatMap (fun source => source.1.toList++source.2.toList) := by
  induction roots with
  | nil => rfl
  | cons head tail ih => simp only [body,sourceBytes_value,RowEncodingCost.append_value,List.flatMap_cons,ih]

theorem body_cost (roots : List Source) : (body roots).cost = 845*roots.length+1 := by
  induction roots with
  | nil => rfl
  | cons head tail ih =>
    simp only [body,sourceBytes_cost,RowEncodingCost.append_cost,sourceBytes_size,ih,List.length_cons]
    omega

def encode (roots : Sources) : Run Input :=
  let count := RowEncodingCost.length roots.val
  let header := IntegerEncodingCost.encode ⟨count.value,by rw [RowEncodingCost.length_value]; exact roots.property⟩
  let bytes := body roots.val
  let joined := RowEncodingCost.append header.value bytes.value
  ⟨joined.value,count.cost+header.cost+bytes.cost+joined.cost+4⟩

theorem encode_value (roots : Sources) :
    (encode roots).value = NativeCanonicalLookupWire.sourcesCodec.encode (view roots) := by
  simp only [encode,RowEncodingCost.append_value,RowEncodingCost.length_value,
    IntegerEncodingCost.encode_value,body_value,NativeCanonicalLookupWire.sourcesCodec,
    NativePrefixCodec.vector,view,List.length_map,NativePrefixCodec.usize,List.flatMap_map,
    NativePrefixCodec.product,NativeByteCodec.digest,NativeByteCodec.fixed,sourceView,
    FixedByteReadCost.ofFn_get]

theorem encode_cost (roots : Sources) : (encode roots).cost ≤ 848*roots.val.length+93 := by
  have header := IntegerEncodingCost.encode_cost
    (⟨(RowEncodingCost.length roots.val).value,by rw [RowEncodingCost.length_value]; exact roots.property⟩ : NativeUsizeMessage.Usize)
  have headerSize := IntegerEncodingCost.encode_length
    (⟨(RowEncodingCost.length roots.val).value,by rw [RowEncodingCost.length_value]; exact roots.property⟩ : NativeUsizeMessage.Usize)
  simp only [encode,RowEncodingCost.length_cost,body_cost,RowEncodingCost.append_cost]
  omega

def parse (input : Input) : Run (Option Sources) :=
  let result := StoredSourceVectorReadCost.read input
  match result.value with
  | none => ⟨none,result.cost+2⟩
  | some (roots,rest) => ⟨if rest = [] then some roots else none,result.cost+3⟩

theorem parse_cost (input : Input) : (parse input).cost ≤ 916*(input.length/128+1)+113 := by
  have bound := StoredSourceVectorReadCost.read_cost input
  simp only [parse]
  split <;> dsimp only <;> omega

theorem parse_size (input : Input) (roots : Sources) (found : (parse input).value = some roots) :
    roots.val.length ≤ input.length/128 := by
  simp only [parse] at found
  split at found
  · contradiction
  · rename_i values rest parsed
    have size := StoredSourceVectorReadCost.read_size input values rest parsed
    split at found
    · have same := Option.some.inj found
      subst roots
      omega
    · contradiction

def decode (input : Input) : Run (Option Sources) :=
  let parsed := parse input
  match parsed.value with
  | none => ⟨none,parsed.cost+2⟩
  | some roots =>
    let canonical := encode roots
    let compared := BytePrefixMatchCost.equal canonical.value input
    ⟨if compared.value then some roots else none,parsed.cost+canonical.cost+compared.cost+5⟩

theorem decode_value (input : Input) :
    (decode input).value.map view = NativeExactCodec.read NativeCanonicalLookupWire.sourcesCodec input := by
  simp only [NativeExactCodec.read,← StoredSourceVectorReadCost.read_value]
  cases parsed : (StoredSourceVectorReadCost.read input).value with
  | none => simp only [decode,parse,parsed,Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨roots,rest⟩
    by_cases ended : rest = [] <;>
      by_cases same : NativeCanonicalLookupWire.sourcesCodec.encode (view roots) = input <;>
        simp [decode,parse,parsed,ended,same,encode_value,BytePrefixMatchCost.equal_value]

theorem decode_cost (input : Input) :
    (decode input).cost ≤ 1764*(input.length/128+1)+6*input.length+1 := by
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

theorem decode_size (input : Input) (roots : Sources) (found : (decode input).value = some roots) :
    roots.val.length ≤ input.length/128 := by
  simp only [decode] at found
  split at found
  · contradiction
  · rename_i values parsed
    split at found
    · have same := Option.some.inj found
      subst roots
      exact parse_size input values parsed
    · contradiction

theorem decode_sound (input : Input) (roots : Sources) (found : (decode input).value = some roots) :
    NativeCanonicalLookupWire.sourcesCodec.encode (view roots) = input := by
  have native := decode_value input
  rw [found,Option.map_some] at native
  exact NativeExactCodec.read_sound _ _ _ native.symm

theorem view_injective : Function.Injective view := by
  intro left right same
  apply Subtype.ext
  have data := congrArg Subtype.val same
  have injective : Function.Injective sourceView := by
    intro first last equal
    apply Prod.ext
    · apply Vector.ext
      intro i hi
      exact congrFun (congrArg Prod.fst equal) ⟨i,hi⟩
    · apply Vector.ext
      intro i hi
      exact congrFun (congrArg Prod.snd equal) ⟨i,hi⟩
  exact (List.map_injective_iff.mpr injective) data

theorem decode_encode (roots : Sources) : (decode (encode roots).value).value = some roots := by
  have accepted : NativeExactCodec.read NativeCanonicalLookupWire.sourcesCodec (encode roots).value =
      some (view roots) := by
    rw [encode_value]
    exact NativeExactCodec.read_encode _ _
  have native := (decode_value (encode roots).value).trans accepted
  cases parsed : (decode (encode roots).value).value with
  | none => rw [parsed,Option.map_none] at native; cases native
  | some values =>
    rw [parsed,Option.map_some] at native
    exact congrArg some (view_injective (Option.some.inj native))
end FormalProof4FHE.HasteBoots.StoredSourceVectorCost
