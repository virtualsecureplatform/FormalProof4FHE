module
public import FormalProof4FHE.HasteBoots.NativeByteCodec
@[expose] public section

/-! Canonical reencoding does not enlarge successfully decoded structural
prefixes. Left-inverse codecs alone do not imply this property; the base
readers and every composition operation are checked separately. -/
namespace FormalProof4FHE.HasteBoots.PrefixCodecReadSize
open NativePrefixCodec (Codec)
open NativeUsizeMessage (Usize)
open InputIndexedOracle (Input)

def Nonexpanding {A : Type} (codec : Codec A) : Prop :=
  ∀ input value rest, codec.read input = some (value,rest) →
    (codec.encode value).length + rest.length ≤ input.length

theorem encode_le_three (value : Usize) (fits : value.val < 2^16) :
    (NativeUsizeMessage.encode value).length ≤ 3 := by
  unfold NativeUsizeMessage.encode
  split_ifs <;> simp only [List.length_cons,List.length_nil,TranscriptFrame.littleEndian_length] <;> omega

theorem encode_le_five (value : Usize) (fits : value.val < 2^32) :
    (NativeUsizeMessage.encode value).length ≤ 5 := by
  unfold NativeUsizeMessage.encode
  split_ifs <;> simp only [List.length_cons,List.length_nil,TranscriptFrame.littleEndian_length] <;> omega

theorem wide (width : ℕ) (input : Input) (value : ℕ) (rest : Input)
    (found : (BytePrefixCost.readWide width input).value = some (value,rest)) :
    value < 256^width ∧ rest.length + width = input.length := by
  rw [BytePrefixCost.readWide_value] at found
  split at found
  next enough =>
    have pair := Prod.mk.inj (Option.some.inj found)
    have bound := TranscriptFrame.fromLittleEndian_lt (input.take width)
    rw [List.length_take,Nat.min_eq_left enough] at bound
    refine ⟨by rw [← pair.1]; exact bound,?_⟩
    rw [← pair.2,List.length_drop]
    omega
  next => contradiction

theorem integer (input : Input) (value : Usize) (rest : Input)
    (found : (IntegerPrefixCost.read input).value = some (value.val,rest)) :
    (NativeUsizeMessage.encode value).length + rest.length ≤ input.length := by
  cases input with
  | nil => contradiction
  | cons tag tail =>
    simp only [IntegerPrefixCost.read] at found
    split at found
    next small =>
      have pair := Prod.mk.inj (Option.some.inj found)
      have fits : value.val < 251 := by rw [← pair.1]; exact small
      simp only [NativeUsizeMessage.encode,fits,↓reduceDIte,List.length_cons,List.length_nil]
      have size := congrArg List.length pair.2
      omega
    next =>
      split at found
      next =>
        have decoded := wide 2 tail value.val rest found
        have fits : value.val < 2^16 := by norm_num at decoded; omega
        have encoded := encode_le_three value fits
        simp only [List.length_cons]
        omega
      next =>
        split at found
        next =>
          have decoded := wide 4 tail value.val rest found
          have fits : value.val < 2^32 := by norm_num at decoded; omega
          have encoded := encode_le_five value fits
          simp only [List.length_cons]
          omega
        next =>
          split at found
          next =>
            have decoded := (wide 8 tail value.val rest found).2
            have encoded := NativeUsizeMessage.encode_length value
            simp only [List.length_cons]
            omega
          next => contradiction

theorem usize : Nonexpanding NativePrefixCodec.usize := by
  intro input value rest found
  rw [NativePrefixCodec.usize_read_eq_reference,← IntegerPrefixCost.read_value] at found
  obtain ⟨⟨raw,tail⟩,parsed,converted⟩ := Option.bind_eq_some_iff.mp found
  split at converted
  next fits =>
    have pair := Option.some.inj converted
    have same := congrArg (fun pair => (pair.1.val,pair.2)) pair
    simp only [Prod.mk.injEq] at same
    have decoded : (IntegerPrefixCost.read input).value = some (value.val,rest) := by
      simpa only [same.1,same.2] using parsed
    exact integer input value rest decoded
  next => contradiction

theorem product {A B : Type} (first : Codec A) (second : Codec B)
    (left : Nonexpanding first) (right : Nonexpanding second) :
    Nonexpanding (NativePrefixCodec.product first second) := by
  intro input value rest found
  obtain ⟨⟨a,tail⟩,firstRead,later⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨⟨b,suffix⟩,secondRead,same⟩ := Option.map_eq_some_iff.mp later
  cases same
  have earlier := left input a tail firstRead
  have after := right tail b suffix secondRead
  change (first.encode a ++ second.encode b).length + suffix.length ≤ input.length
  rw [List.length_append]
  omega

theorem transport {A B : Type} (codec : Codec A) (equiv : A ≃ B) (size : Nonexpanding codec) :
    Nonexpanding (NativePrefixCodec.transport codec equiv) := by
  intro input value rest found
  obtain ⟨⟨a,tail⟩,parsed,same⟩ := Option.map_eq_some_iff.mp found
  cases same
  simpa only [NativePrefixCodec.transport,equiv.symm_apply_apply] using size input a tail parsed

theorem readCount {A : Type} (codec : Codec A) (size : Nonexpanding codec)
    (count : ℕ) (input : Input) (values : List A) (rest : Input)
    (found : NativePrefixCodec.readCount codec count input = some (values,rest)) :
    values.length = count ∧ (values.flatMap codec.encode).length + rest.length ≤ input.length := by
  induction count generalizing input values rest with
  | zero =>
    have same := Option.some.inj found
    cases same
    exact ⟨rfl,by simp⟩
  | succ count ih =>
    obtain ⟨⟨a,tail⟩,firstRead,later⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨⟨remaining,suffix⟩,secondRead,same⟩ := Option.map_eq_some_iff.mp later
    cases same
    obtain ⟨length,bound⟩ := ih tail remaining suffix secondRead
    have first := size input a tail firstRead
    constructor
    · simp only [List.length_cons,length]
    · simp only [List.flatMap_cons,List.length_append]
      omega

theorem vector {A : Type} (codec : Codec A) (size : Nonexpanding codec) :
    Nonexpanding (NativePrefixCodec.vector codec) := by
  intro input value rest found
  obtain ⟨⟨count,tail⟩,header,later⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨⟨entries,suffix⟩,body,returned⟩ := Option.bind_eq_some_iff.mp later
  split at returned
  next fits =>
    have same := Option.some.inj returned
    cases same
    obtain ⟨length,bound⟩ := readCount codec size count.val tail entries suffix body
    have head := usize input count tail header
    have sameCount : (⟨entries.length,fits⟩ : Usize) = count := Fin.ext length
    change (NativePrefixCodec.usize.encode ⟨entries.length,fits⟩ ++ entries.flatMap codec.encode).length + suffix.length ≤ _
    rw [sameCount,List.length_append]
    omega
  next => contradiction

theorem fixed {A : Type} (codec : Codec A) (size : Nonexpanding codec) (count : ℕ) (fits : count < 2^64) :
    Nonexpanding (NativePrefixCodec.fixed codec count fits) := by
  intro input value rest found
  obtain ⟨⟨entries,tail⟩,parsed,returned⟩ := Option.bind_eq_some_iff.mp found
  split at returned
  next length =>
    have same := Option.some.inj returned
    cases same
    subst count
    have bound := vector codec size input entries tail parsed
    simpa only [NativePrefixCodec.fixed,List.ofFn_getElem] using bound
  next => contradiction

theorem bytes_fixed (count : ℕ) : Nonexpanding (NativeByteCodec.fixed count) := by
  intro input value rest found
  change (if length : (input.take count).length = count then some (_,input.drop count) else none) = some (value,rest) at found
  split at found
  next enough =>
    have same := Prod.mk.inj (Option.some.inj found)
    have remaining := congrArg List.length same.2
    change (List.ofFn value).length + rest.length ≤ input.length
    rw [List.length_ofFn]
    have available : count ≤ input.length := by rw [List.length_take] at enough; omega
    rw [List.length_drop] at remaining
    omega
  next => contradiction

end FormalProof4FHE.HasteBoots.PrefixCodecReadSize
