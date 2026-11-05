module

public import FormalProof4FHE.HasteBoots.NativeGoldNttMeaning
public import FormalProof4FHE.HasteBoots.NativeGoldRowEncoding
public import FormalProof4FHE.HasteBoots.NTTBlockEncoder

@[expose] public section

/-! Computed canonical scalar block-RS rows equal the actual polynomial code.
The original raw input fixes every coefficient; no encoded-response or
encoder-correctness certificate is a protocol input. Native root discovery,
cache/serialized-code linkage and SIMD/instruction refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldRowMeaning

open NativeFields NativeFieldRepresentation
open NativeGoldRowEncoding (Code)

noncomputable section

def coefficients (code : Code) (m : ℕ) (input : List GoldWord) : Fin m → Fin code.blockWidth → Goldilocks :=
  fun block lane => goldValue (input[block.val*code.blockWidth+lane.val]?.getD 0)

def word (code : Code) (result : List GoldWord) : Fin (2^code.logSize) → Fin code.blockWidth → Goldilocks :=
  fun symbol lane => goldValue (result[(finProdFinEquiv (symbol,lane)).val]?.getD 0)

/-- The checked retained root is the actual plan root used by the encoder. -/
theorem root_value (code : Code) (valid : NativeGoldRowEncoding.check code = true) :
    goldValue code.domainRoot = NativeGoldSolinas.value code.planRoot := by
  have same := (NativeGoldRowEncoding.check_iff code).mp valid |>.2.2.2.2.2.2
  rw [← goldCanonical_cast,same]
  rfl

/-- Every missing coefficient block is genuinely zero padding, including
unused coordinates of the partial final input block. -/
theorem coordinate_padded (code : Code) (m : ℕ) (input : List GoldWord)
    (padding : input.length ≤ m*code.blockWidth) (lane : Fin code.blockWidth) :
    (fun index : Fin (2^code.logSize) => goldValue ((NativeGoldRowEncoding.coordinate code input lane.val)[index.val]?.getD 0)) =
      NTTBlockEncoder.padded (fun index => coefficients code m input index lane) := by
  funext index
  simp only [NativeGoldRowEncoding.coordinate,List.getElem?_ofFn,dite_eq_left index.isLt,Option.getD_some,
    NTTBlockEncoder.padded]
  split
  · rfl
  · rename_i outside
    have blockBound := Nat.mul_le_mul_right code.blockWidth (Nat.le_of_not_gt outside)
    have absent : input.length ≤ index.val*code.blockWidth+lane.val := by omega
    rw [List.getElem?_eq_none absent,Option.getD_none]
    rfl

/-- All computed non-shortcut outputs are the semantic polynomial encoder. -/
theorem payload_value (code : Code) (m : ℕ) (input : List GoldWord)
    (enough : m ≤ 2^code.logSize) (padding : input.length ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (NativeGoldSolinas.value code.planRoot) (2^(code.logSize+1))) :
    word code (NativeGoldRowEncoding.payload code input) =
      BlockEncoder.encode (NTTButterfly.domain code.logSize (NativeGoldSolinas.value code.planRoot) primitive)
        (coefficients code m input) := by
  funext symbol lane
  have address : (finProdFinEquiv (symbol,lane)).val = symbol.val*code.blockWidth+lane.val := by
    change lane.val+code.blockWidth*symbol.val = symbol.val*code.blockWidth+lane.val
    ac_rfl
  have present : (finProdFinEquiv (symbol,lane)).val < (NativeGoldRowEncoding.payload code input).length := by
    rw [NativeGoldRowEncoding.payload_length]
    exact (finProdFinEquiv (symbol,lane)).isLt
  have present' : symbol.val*code.blockWidth+lane.val < (NativeGoldRowEncoding.payload code input).length := by
    rw [← address]
    exact present
  rw [word,address,List.getElem?_eq_getElem present',Option.getD_some,NativeGoldRowEncoding.payload_get]
  let data := NativeGoldRowEncoding.coordinate code input lane.val
  have size : data.length = 2^code.logSize := NativeGoldRowEncoding.coordinate_length _ _ _
  have encoded := NativeGoldNttMeaning.forwardData_evaluation code.logSize code.planRoot data size primitive
  have projected := congrArg (fun values : List Goldilocks => values[symbol.val]?.getD 0) encoded
  have outputBound : symbol.val < (NativeGoldNtt.forwardData code.logSize code.planRoot data).length := by
    rw [NativeGoldNtt.forwardData_length _ _ _ size]
    exact symbol.isLt
  simp only [List.getElem?_map,List.getElem?_ofFn,dite_eq_left symbol.isLt,List.getElem?_eq_getElem outputBound,
    Option.map_some,Option.getD_some] at projected
  rw [projected]
  change NTTButterfly.evaluate (fun index => goldValue (data[index.val]?.getD 0))
    (NTTButterfly.nodes code.logSize (NativeGoldSolinas.value code.planRoot) symbol) = _
  rw [coordinate_padded code m input padding lane,NTTBlockEncoder.evaluate_padded enough]
  rfl

theorem rawZero_get (input : List GoldWord) (index : ℕ) (zero : NativeGoldRowEncoding.rawZero input = true) :
    input[index]?.getD 0 = 0 := by
  cases found : input[index]? with
  | none => rfl
  | some value =>
    simp only [Option.getD_some]
    have same := of_decide_eq_true (List.all_eq_true.mp zero value (List.mem_of_getElem? found))
    exact Fin.ext same

/-- The shortcut computes exactly the same codeword as the scalar transform,
even though its raw predicate intentionally excludes lazy zero spellings. -/
theorem encodeRow_value (code : Code) (m : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.encodeRow code input = some result)
    (enough : m ≤ 2^code.logSize) (padding : input.length ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (NativeGoldSolinas.value code.planRoot) (2^(code.logSize+1))) :
    word code result = BlockEncoder.encode
      (NTTButterfly.domain code.logSize (NativeGoldSolinas.value code.planRoot) primitive) (coefficients code m input) := by
  unfold NativeGoldRowEncoding.encodeRow at success
  split at success
  · split at success
    · rename_i zero
      have same := Option.some.inj success
      subst result
      funext symbol lane
      have present : (finProdFinEquiv (symbol,lane)).val <
          (List.replicate (2^code.logSize*code.blockWidth) (0 : GoldWord)).length := by
        rw [List.length_replicate]
        exact (finProdFinEquiv (symbol,lane)).isLt
      rw [word,List.getElem?_eq_getElem present,Option.getD_some,List.getElem_replicate]
      simp [coefficients,BlockEncoder.encode,rawZero_get input _ zero,goldValue]
    · have same := Option.some.inj success
      subst result
      exact payload_value code m input enough padding primitive
  · contradiction

/-- Native scalar row encoding lands in the same whole-symbol distance code
used by the opening security proof, with actual input coefficients. -/
theorem encodeRow_mem_code (code : Code) (m : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.encodeRow code input = some result)
    (enough : m ≤ 2^code.logSize) (padding : input.length ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (NativeGoldSolinas.value code.planRoot) (2^(code.logSize+1))) :
    word code result ∈ BlockCode.code
      (NTTButterfly.domain code.logSize (NativeGoldSolinas.value code.planRoot) primitive) m code.blockWidth := by
  have valid := (NativeGoldRowEncoding.encodeRow_shape code input result success).1
  have : NeZero code.blockWidth := ⟨(NativeGoldRowEncoding.check_iff code).mp valid |>.2.2.2.1⟩
  rw [encodeRow_value code m input result success enough padding primitive]
  exact BlockEncoder.encode_mem_code _ _

/-- Membership uses the original retained code root because its equality with
the actual plan root was checked by the successful encoder itself. -/
theorem encodeRow_mem_retained_code (code : Code) (m : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.encodeRow code input = some result)
    (enough : m ≤ 2^code.logSize) (padding : input.length ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (goldValue code.domainRoot) (2^(code.logSize+1))) :
    word code result ∈ BlockCode.code (NTTButterfly.domain code.logSize (goldValue code.domainRoot) primitive) m code.blockWidth := by
  have same := root_value code (NativeGoldRowEncoding.encodeRow_shape code input result success).1
  have planPrimitive : IsPrimitiveRoot (NativeGoldSolinas.value code.planRoot) (2^(code.logSize+1)) := by
    rw [← same]
    exact primitive
  have coded := encodeRow_mem_code code m input result success enough padding planPrimitive
  simpa only [← same] using coded

end
end FormalProof4FHE.HasteBoots.NativeGoldRowMeaning
