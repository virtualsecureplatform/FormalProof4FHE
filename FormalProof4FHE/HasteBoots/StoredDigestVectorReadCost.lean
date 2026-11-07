module
public import FormalProof4FHE.HasteBoots.FixedByteReadCost
public import FormalProof4FHE.HasteBoots.IntegerPrefixProgress
@[expose] public section

/-! Measured prefix decoding of native vectors of fixed 64-byte digests.
Stored vectors replace functional digest callbacks. Every successful body step
consumes 64 supplied bytes; forged counts stop at the first truncated digest.
Canonical complete decoding and physical/native refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.StoredDigestVectorReadCost
open InputIndexedOracle (Input Byte)
open NativeRootMessage (Digest)
open SolverOperationCost (Run)
abbrev Root := Vector Byte 64
abbrev Roots := NativePrefixCodec.Vector Root

def view (roots : Roots) : NativePrefixCodec.Vector Digest :=
  ⟨roots.val.map Vector.get,by simpa only [List.length_map] using roots.property⟩

def readCount : ℕ → Input → Run (Option (List Root × Input))
  | 0,bytes => ⟨some ([],bytes),1⟩
  | count+1,bytes =>
    let first := FixedByteReadCost.read 64 bytes
    match first.value with
    | none => ⟨none,first.cost+3⟩
    | some (value,rest) =>
      let tail := readCount count rest
      ⟨tail.value.map (fun pair => (value::pair.1,pair.2)),first.cost+tail.cost+5⟩

theorem readCount_value (count : ℕ) (bytes : Input) :
    (readCount count bytes).value.map (fun pair => (pair.1.map Vector.get,pair.2)) =
      NativePrefixCodec.readCount NativeByteCodec.digest count bytes := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
    simp only [NativePrefixCodec.readCount,NativeByteCodec.digest,← FixedByteReadCost.read_value]
    cases first : (FixedByteReadCost.read 64 bytes).value with
    | none => simp only [readCount,first,Option.map_none,Option.bind_none]
    | some pair =>
      rcases pair with ⟨value,rest⟩
      simp only [readCount,first,Option.map_some,Option.bind_some]
      have tailValue := ih rest
      simp only [NativeByteCodec.digest] at tailValue
      rw [← tailValue]
      cases last : (readCount count rest).value <;> rfl

/-- Pure length proof, independent of arithmetic resource bounds. -/
theorem readCount_length (count : ℕ) (bytes : Input) (values : List Root) (rest : Input)
    (found : (readCount count bytes).value = some (values,rest)) : values.length = count := by
  induction count generalizing bytes values rest with
  | zero => have same := Option.some.inj found; cases same; rfl
  | succ count ih =>
    cases first : (FixedByteReadCost.read 64 bytes).value with
    | none => simp only [readCount,first] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,first] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have length := ih tail remaining last continued
      cases same
      simp only [List.length_cons,length]

theorem readCount_remaining (count : ℕ) (bytes : Input) (values : List Root) (rest : Input)
    (found : (readCount count bytes).value = some (values,rest)) :
    rest.length+64*values.length = bytes.length := by
  induction count generalizing bytes values rest with
  | zero => have same := Option.some.inj found; cases same; simp
  | succ count ih =>
    cases first : (FixedByteReadCost.read 64 bytes).value with
    | none => simp only [readCount,first] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,first] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have length := ih tail remaining last continued
      have parts := congrArg List.length (FixedByteReadCost.read_some 64 bytes value tail first)
      simp only [List.length_append,Vector.length_toList] at parts
      cases same
      simp only [List.length_cons]
      omega

theorem readCount_cost (count : ℕ) (bytes : Input) :
    (readCount count bytes).cost ≤ 457*(min count (bytes.length/64)+1) := by
  induction count generalizing bytes with
  | zero => simp [readCount]
  | succ count ih =>
    have first := FixedByteReadCost.read_cost 64 bytes
    have width := Nat.min_le_left 64 bytes.length
    cases parsed : (FixedByteReadCost.read 64 bytes).value with
    | none => simp only [readCount,parsed]; omega
    | some pair =>
      rcases pair with ⟨value,rest⟩
      have parts := congrArg List.length (FixedByteReadCost.read_some 64 bytes value rest parsed)
      simp only [List.length_append,Vector.length_toList] at parts
      have tail := ih rest
      simp only [readCount,parsed]
      omega

def read (bytes : Input) : Run (Option (Roots × Input)) :=
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
      (NativePrefixCodec.vector NativeByteCodec.digest).read bytes := by
  change _ = (IntegerPrefixCost.readUsize bytes).value.bind (fun count =>
    (NativePrefixCodec.readCount NativeByteCodec.digest count.1.val count.2).bind (fun result =>
      if fits : result.1.length < 2^64 then some ((⟨result.1,fits⟩ : NativePrefixCodec.Vector Digest),result.2) else none))
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
      have fits : (values.map Vector.get).length < 2^64 := by
        rw [List.length_map,readCount_length count.val tail values rest decoded]
        exact count.isLt
      simp only [decoded,Option.map_some,Option.bind_some,dite_eq_left fits,view]

theorem read_cost (bytes : Input) : (read bytes).cost ≤ 457*(bytes.length/64+1)+110 := by
  have header := IntegerPrefixCost.readUsize_cost bytes
  cases parsed : (IntegerPrefixCost.readUsize bytes).value with
  | none => simp only [read,parsed]; omega
  | some pair =>
    rcases pair with ⟨count,tail⟩
    have progress := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
    have body := readCount_cost count.val tail
    have size := Nat.min_le_right count.val (tail.length/64)
    simp only [read,parsed]
    split <;> dsimp only <;> omega

theorem read_size (bytes : Input) (roots : Roots) (rest : Input)
    (found : (read bytes).value = some (roots,rest)) : 64*roots.val.length+rest.length < bytes.length := by
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
end FormalProof4FHE.HasteBoots.StoredDigestVectorReadCost
