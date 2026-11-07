module
public import FormalProof4FHE.HasteBoots.ConfigWireCost
public import FormalProof4FHE.HasteBoots.StoredSourceVectorCost
public import FormalProof4FHE.HasteBoots.NativeRootInputView
@[expose] public section

/-! Measured original canonical lookup bindings with stored helper/source bytes.
The complete raw configuration, serialized extension degree 3, helper digest and
ordered source vector are decoded. Canonicality is checked by charged complete
re-encoding. This does not assert trusted configuration/ownership or native
physical refinement, and does not reinterpret lookup widths as degree fields. -/
namespace FormalProof4FHE.HasteBoots.StoredCanonicalBindingCost
open InputIndexedOracle (Input Byte)
open SolverOperationCost (Run)
structure Stored where
  config : NativeLookupRequestWire.Config
  helper : Vector Byte 64
  sources : StoredSourceVectorReadCost.Sources

def view (binding : Stored) : NativeCanonicalLookupWire.Binding :=
  ⟨binding.config,binding.helper.get,StoredSourceVectorReadCost.view binding.sources⟩

def read (input : Input) : Run (Option (Stored × Input)) :=
  let config := ConfigWireCost.read input
  match config.value with
  | none => ⟨none,config.cost+3⟩
  | some (cfg,afterConfig) =>
    let degree := IntegerPrefixCost.readUsize afterConfig
    match degree.value with
    | none => ⟨none,config.cost+degree.cost+5⟩
    | some (extension,afterDegree) =>
      if extension.val = 3 then
        let helper := FixedByteReadCost.read 64 afterDegree
        match helper.value with
        | none => ⟨none,config.cost+degree.cost+helper.cost+8⟩
        | some (root,afterHelper) =>
          let sources := StoredSourceVectorReadCost.read afterHelper
          match sources.value with
          | none => ⟨none,config.cost+degree.cost+helper.cost+sources.cost+10⟩
          | some (values,rest) =>
            ⟨some (⟨cfg,root,values⟩,rest),config.cost+degree.cost+helper.cost+sources.cost+12⟩
      else ⟨none,config.cost+degree.cost+6⟩

theorem read_value (input : Input) :
    (read input).value.map (fun pair => (view pair.1,pair.2)) = NativeRootInputView.readBinding input := by
  simp only [NativeRootInputView.readBinding,Option.bind_eq_bind,← ConfigWireCost.read_value,NativePrefixCodec.usize,
    NativeByteCodec.digest,← FixedByteReadCost.read_value,← StoredSourceVectorReadCost.read_value]
  cases config : (ConfigWireCost.read input).value with
  | none => simp only [read,config,Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨cfg,afterConfig⟩
    simp only [read,config,Option.bind_some]
    cases degree : (IntegerPrefixCost.readUsize afterConfig).value with
    | none => rfl
    | some pair =>
      rcases pair with ⟨extension,afterDegree⟩
      simp only [Option.bind_some]
      by_cases valid : extension.val = 3
      · simp only [valid,ite_true]
        cases helper : (FixedByteReadCost.read 64 afterDegree).value with
        | none => rfl
        | some pair =>
          rcases pair with ⟨root,afterHelper⟩
          simp only [Option.map_some,Option.bind_some]
          cases sources : (StoredSourceVectorReadCost.read afterHelper).value <;> rfl
      · simp only [valid,ite_false,Option.map_none]

theorem read_cost (input : Input) :
    (read input).cost ≤ 113*(input.length+1)+916*(input.length/128+1)+700 := by
  have config := ConfigWireCost.read_cost input
  simp only [read]
  split
  · dsimp only; omega
  · rename_i cfg afterConfig decoded
    have first := ConfigWireCost.read_remaining input cfg afterConfig decoded
    have degree := IntegerPrefixCost.readUsize_cost afterConfig
    split
    · dsimp only; omega
    · rename_i extension afterDegree parsed
      have second := IntegerPrefixCost.readUsize_remaining afterConfig extension afterDegree parsed
      split
      · have helper := FixedByteReadCost.read_cost 64 afterDegree
        have width := Nat.min_le_left 64 afterDegree.length
        split
        · dsimp only; omega
        · rename_i root afterHelper found
          have parts := congrArg List.length (FixedByteReadCost.read_some 64 afterDegree root afterHelper found)
          simp only [List.length_append,Vector.length_toList] at parts
          have sources := StoredSourceVectorReadCost.read_cost afterHelper
          split <;> dsimp only <;> omega
      · dsimp only; omega

theorem read_remaining (input : Input) (binding : Stored) (rest : Input)
    (found : (read input).value = some (binding,rest)) :
    TableWireCost.cells binding.config.table.val+128*binding.sources.val.length+rest.length+69 ≤ input.length := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i cfg afterConfig decoded
    split at found
    · contradiction
    · rename_i extension afterDegree parsed
      split at found
      · split at found
        · contradiction
        · rename_i root afterHelper helper
          split at found
          · contradiction
          · rename_i values last sources
            have first := ConfigWireCost.read_remaining input cfg afterConfig decoded
            have second := IntegerPrefixCost.readUsize_remaining afterConfig extension afterDegree parsed
            have third := congrArg List.length (FixedByteReadCost.read_some 64 afterDegree root afterHelper helper)
            simp only [List.length_append,Vector.length_toList] at third
            have lastSize := StoredSourceVectorReadCost.read_size afterHelper values last sources
            have same := Option.some.inj found
            cases same
            dsimp only
            omega
      · contradiction

def encode (binding : Stored) : Run Input :=
  let config := ConfigWireCost.encode binding.config
  let degree := IntegerEncodingCost.encode (⟨3,by decide⟩ : NativeUsizeMessage.Usize)
  let helper := StoredDigestView.fromVector binding.helper
  let sources := StoredSourceVectorCost.encode binding.sources
  let tail := RowEncodingCost.append helper.value.val sources.value
  let afterDegree := RowEncodingCost.append degree.value tail.value
  let complete := RowEncodingCost.append config.value afterDegree.value
  ⟨complete.value,config.cost+degree.cost+helper.cost+sources.cost+tail.cost+afterDegree.cost+complete.cost+7⟩

theorem encode_value (binding : Stored) :
    (encode binding).value = NativeCanonicalLookupWire.payload (view binding) := by
  simp only [encode,RowEncodingCost.append_value,ConfigWireCost.encode_value,
    IntegerEncodingCost.encode_value,StoredDigestView.fromVector,StoredSourceVectorCost.encode_value,
    NativeCanonicalLookupWire.payload,view,NativeByteCodec.digest_encode,FixedByteReadCost.ofFn_get,List.append_assoc]

theorem encode_cost (binding : Stored) :
    (encode binding).cost ≤ 183*TableWireCost.cells binding.config.table.val+848*binding.sources.val.length+1063 := by
  have config := ConfigWireCost.encode_cost binding.config
  have configSize := ConfigWireCost.encode_size binding.config
  have degree := IntegerEncodingCost.encode_cost (⟨3,by decide⟩ : NativeUsizeMessage.Usize)
  have degreeSize := IntegerEncodingCost.encode_length (⟨3,by decide⟩ : NativeUsizeMessage.Usize)
  have sources := StoredSourceVectorCost.encode_cost binding.sources
  simp only [encode,StoredDigestView.fromVector,RowEncodingCost.append_cost,Vector.length_toList]
  omega

def parse (input : Input) : Run (Option Stored) :=
  let result := read input
  match result.value with
  | none => ⟨none,result.cost+2⟩
  | some (binding,rest) => ⟨if rest = [] then some binding else none,result.cost+3⟩

theorem parse_cost (input : Input) :
    (parse input).cost ≤ 113*(input.length+1)+916*(input.length/128+1)+703 := by
  have parsed := read_cost input
  simp only [parse]
  split <;> dsimp only <;> omega

theorem parse_size (input : Input) (binding : Stored) (found : (parse input).value = some binding) :
    TableWireCost.cells binding.config.table.val ≤ input.length ∧ binding.sources.val.length ≤ input.length/128 := by
  simp only [parse] at found
  split at found
  · contradiction
  · rename_i values rest parsed
    have size := read_remaining input values rest parsed
    split at found
    · have same := Option.some.inj found
      subst binding
      constructor <;> omega
    · contradiction

def decode (input : Input) : Run (Option Stored) :=
  let parsed := parse input
  match parsed.value with
  | none => ⟨none,parsed.cost+2⟩
  | some binding =>
    let canonical := encode binding
    let compared := BytePrefixMatchCost.equal canonical.value input
    ⟨if compared.value then some binding else none,parsed.cost+canonical.cost+compared.cost+5⟩

theorem decode_value (input : Input) :
    (decode input).value.map view = NativeExactCodec.read NativeRootInputView.bindingCodec input := by
  simp only [NativeExactCodec.read,NativeRootInputView.bindingCodec,← read_value]
  cases parsed : (read input).value with
  | none => simp only [decode,parse,parsed,Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨binding,rest⟩
    by_cases ended : rest = [] <;> by_cases same : NativeCanonicalLookupWire.payload (view binding) = input <;>
      simp [decode,parse,parsed,ended,same,encode_value,BytePrefixMatchCost.equal_value]

theorem decode_cost (input : Input) :
    (decode input).cost ≤ 302*input.length+1764*(input.length/128+1)+1100 := by
  have parsed := parse_cost input
  simp only [decode]
  split
  · dsimp only; omega
  · rename_i binding found
    have size := parse_size input binding found
    have encoded := encode_cost binding
    have compared := BytePrefixMatchCost.equal_cost (encode binding).value input
    have matched := Nat.min_le_right (encode binding).value.length input.length
    dsimp only
    omega

theorem decode_sound (input : Input) (binding : Stored) (found : (decode input).value = some binding) :
    NativeCanonicalLookupWire.payload (view binding) = input := by
  have native := decode_value input
  rw [found,Option.map_some] at native
  exact NativeExactCodec.read_sound _ _ _ native.symm

theorem view_injective : Function.Injective view := by
  intro first last same
  have config : first.config = last.config := congrArg NativeCanonicalLookupWire.Binding.config same
  have helper : first.helper = last.helper := by
    apply Vector.ext
    intro i hi
    exact congrFun (congrArg NativeCanonicalLookupWire.Binding.helper same) ⟨i,hi⟩
  have sources : first.sources = last.sources :=
    StoredSourceVectorCost.view_injective (congrArg NativeCanonicalLookupWire.Binding.sources same)
  cases first
  cases last
  cases config
  cases helper
  cases sources
  rfl

theorem decode_encode (binding : Stored) : (decode (encode binding).value).value = some binding := by
  have accepted : NativeExactCodec.read NativeRootInputView.bindingCodec (encode binding).value = some (view binding) := by
    rw [encode_value]
    exact NativeExactCodec.read_encode NativeRootInputView.bindingCodec (view binding)
  have native := (decode_value (encode binding).value).trans accepted
  cases parsed : (decode (encode binding).value).value with
  | none => rw [parsed,Option.map_none] at native; cases native
  | some values => rw [parsed,Option.map_some] at native; exact congrArg some (view_injective (Option.some.inj native))
end FormalProof4FHE.HasteBoots.StoredCanonicalBindingCost
