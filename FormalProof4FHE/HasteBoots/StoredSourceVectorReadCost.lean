module
public import FormalProof4FHE.HasteBoots.FixedByteReadCost
public import FormalProof4FHE.HasteBoots.IntegerPrefixProgress
public import FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire
@[expose] public section

/-! Measured prefix decoding of native vectors of fixed 128-byte context/root pairs.
Stored vectors replace functional context/root callbacks. Every successful body step
consumes 128 supplied bytes; forged counts stop at the first truncated pair.
Canonical complete decoding and physical/native refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.StoredSourceVectorReadCost
open InputIndexedOracle (Input Byte)
open NativeRootMessage (Digest)
open SolverOperationCost (Run)
abbrev Source := Vector Byte 64 × Vector Byte 64
abbrev Sources := NativePrefixCodec.Vector Source

def sourceView (source : Source) : NativeCanonicalLookupWire.Source := (source.1.get,source.2.get)
def sourceCodec := NativePrefixCodec.product NativeByteCodec.digest NativeByteCodec.digest

def readSource (input : Input) : Run (Option (Source × Input)) :=
  let first := FixedByteReadCost.read 64 input
  match first.value with
  | none => ⟨none,first.cost+3⟩
  | some (context,tail) =>
    let second := FixedByteReadCost.read 64 tail
    match second.value with
    | none => ⟨none,first.cost+second.cost+5⟩
    | some (root,rest) => ⟨some ((context,root),rest),first.cost+second.cost+7⟩

theorem readSource_value (input : Input) :
    (readSource input).value.map (fun pair => (sourceView pair.1,pair.2)) = sourceCodec.read input := by
  simp only [sourceCodec,NativePrefixCodec.product,NativeByteCodec.digest,← FixedByteReadCost.read_value]
  cases first : (FixedByteReadCost.read 64 input).value with
  | none => simp only [readSource,first,Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨context,tail⟩
    simp only [readSource,first,Option.map_some,Option.bind_some]
    cases second : (FixedByteReadCost.read 64 tail).value <;> rfl

theorem readSource_cost (input : Input) : (readSource input).cost ≤ 911 := by
  have first := FixedByteReadCost.read_cost 64 input
  have width := Nat.min_le_left 64 input.length
  simp only [readSource]
  split
  · dsimp only; omega
  · rename_i context tail parsed
    have second := FixedByteReadCost.read_cost 64 tail
    have size := Nat.min_le_left 64 tail.length
    split <;> dsimp only <;> omega

theorem readSource_remaining (input : Input) (source : Source) (rest : Input)
    (found : (readSource input).value = some (source,rest)) : rest.length+128 = input.length := by
  simp only [readSource] at found
  split at found
  · contradiction
  · rename_i context tail first
    split at found
    · contradiction
    · rename_i root last second
      have left := congrArg List.length (FixedByteReadCost.read_some 64 input context tail first)
      have right := congrArg List.length (FixedByteReadCost.read_some 64 tail root last second)
      simp only [List.length_append,Vector.length_toList] at left right
      have same := Option.some.inj found
      cases same
      omega

def view (roots : Sources) : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨roots.val.map sourceView,by simpa only [List.length_map] using roots.property⟩

def readCount : ℕ → Input → Run (Option (List Source × Input))
  | 0,bytes => ⟨some ([],bytes),1⟩
  | count+1,bytes =>
    let first := readSource bytes
    match first.value with
    | none => ⟨none,first.cost+3⟩
    | some (value,rest) =>
      let tail := readCount count rest
      ⟨tail.value.map (fun pair => (value::pair.1,pair.2)),first.cost+tail.cost+5⟩

theorem readCount_value (count : ℕ) (bytes : Input) :
    (readCount count bytes).value.map (fun pair => (pair.1.map sourceView,pair.2)) =
      NativePrefixCodec.readCount sourceCodec count bytes := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
    simp only [NativePrefixCodec.readCount,← readSource_value]
    cases first : (readSource bytes).value with
    | none => simp only [readCount,first,Option.map_none,Option.bind_none]
    | some pair =>
      rcases pair with ⟨value,rest⟩
      simp only [readCount,first,Option.map_some,Option.bind_some]
      rw [← ih rest]
      cases last : (readCount count rest).value <;> rfl

/-- Pure length proof, independent of arithmetic resource bounds. -/
theorem readCount_length (count : ℕ) (bytes : Input) (values : List Source) (rest : Input)
    (found : (readCount count bytes).value = some (values,rest)) : values.length = count := by
  induction count generalizing bytes values rest with
  | zero => have same := Option.some.inj found; cases same; rfl
  | succ count ih =>
    cases first : (readSource bytes).value with
    | none => simp only [readCount,first] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,first] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have length := ih tail remaining last continued
      cases same
      simp only [List.length_cons,length]

theorem readCount_remaining (count : ℕ) (bytes : Input) (values : List Source) (rest : Input)
    (found : (readCount count bytes).value = some (values,rest)) :
    rest.length+128*values.length = bytes.length := by
  induction count generalizing bytes values rest with
  | zero => have same := Option.some.inj found; cases same; simp
  | succ count ih =>
    cases first : (readSource bytes).value with
    | none => simp only [readCount,first] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,first] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have length := ih tail remaining last continued
      have parts := readSource_remaining bytes value tail first
      cases same
      simp only [List.length_cons]
      omega

theorem readCount_cost (count : ℕ) (bytes : Input) :
    (readCount count bytes).cost ≤ 916*(min count (bytes.length/128)+1) := by
  induction count generalizing bytes with
  | zero => simp [readCount]
  | succ count ih =>
    have first := readSource_cost bytes
    cases parsed : (readSource bytes).value with
    | none => simp only [readCount,parsed]; omega
    | some pair =>
      rcases pair with ⟨value,rest⟩
      have parts := readSource_remaining bytes value rest parsed
      have tail := ih rest
      simp only [readCount,parsed]
      omega

def read (bytes : Input) : Run (Option (Sources × Input)) :=
  let header := IntegerPrefixCost.readUsize bytes
  match header.value with
  | none => ⟨none,header.cost+3⟩
  | some (count,tail) =>
    let body := readCount count.val tail
    match decoded : body.value with
    | none => ⟨none,header.cost+body.cost+5⟩
    | some (values,rest) =>
      have fits : values.length < 2^64 := by
        rw [readCount_length count.val tail values rest decoded]
        exact count.isLt
      ⟨some (⟨values,fits⟩,rest),header.cost+body.cost+6⟩

theorem read_value (bytes : Input) :
    (read bytes).value.map (fun pair => (view pair.1,pair.2)) =
      NativeCanonicalLookupWire.sourcesCodec.read bytes := by
  change _ = (IntegerPrefixCost.readUsize bytes).value.bind (fun count =>
    (NativePrefixCodec.readCount sourceCodec count.1.val count.2).bind (fun result =>
      if fits : result.1.length < 2^64 then some ((⟨result.1,fits⟩ : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source),result.2) else none))
  simp only [read,← readCount_value]
  split
  · rename_i parsed
    simp only [parsed,Option.map_none,Option.bind_none]
  · rename_i count tail parsed
    simp only [parsed,Option.bind_some]
    split
    · rename_i decoded
      simp only [decoded,Option.map_none,Option.bind_none]
    · rename_i values rest decoded
      have fits : (values.map sourceView).length < 2^64 := by
        rw [List.length_map,readCount_length count.val tail values rest decoded]
        exact count.isLt
      simp only [decoded,Option.map_some,Option.bind_some,dite_eq_left fits,view]

theorem read_cost (bytes : Input) : (read bytes).cost ≤ 916*(bytes.length/128+1)+110 := by
  have header := IntegerPrefixCost.readUsize_cost bytes
  cases parsed : (IntegerPrefixCost.readUsize bytes).value with
  | none => simp only [read,parsed]; omega
  | some pair =>
    rcases pair with ⟨count,tail⟩
    have progress := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
    have body := readCount_cost count.val tail
    have size := Nat.min_le_right count.val (tail.length/128)
    simp only [read,parsed]
    split <;> dsimp only <;> omega

theorem read_size (bytes : Input) (roots : Sources) (rest : Input)
    (found : (read bytes).value = some (roots,rest)) : 128*roots.val.length+rest.length < bytes.length := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i count tail parsed
    split at found
    · contradiction
    · rename_i values last decoded
      have same := Option.some.inj found
      have body := readCount_remaining count.val tail values last decoded
      have progress := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
      cases same
      dsimp only
      omega
end FormalProof4FHE.HasteBoots.StoredSourceVectorReadCost
