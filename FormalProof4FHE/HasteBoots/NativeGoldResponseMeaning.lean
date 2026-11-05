module

public import FormalProof4FHE.HasteBoots.NativeGoldRowMeaning

@[expose] public section

/-! Every response lane is the computed codeword of its own original raw
message chunk. Encoded parts are extracted from the actual successful run;
they are not a certificate accepted as a verifier input. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldResponseMeaning

open NativeFields NativeFieldRepresentation
open NativeGoldRowEncoding (Code)

/-- Successful recursive encoding retains every ordered chunk without zip
truncation. The witness parts are precisely the computed row outputs. -/
theorem rows_parts (code : Code) (width : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.rows code width input = some result) :
    ∃ parts : List (List GoldWord), result = parts.flatten ∧ parts.length = width ∧
      ∀ lane < width, NativeGoldRowEncoding.encodeRow code ((input.drop (lane*code.messageLength)).take code.messageLength) = parts[lane]? := by
  induction width generalizing input result with
  | zero =>
    have same := Option.some.inj success
    subst result
    exact ⟨[],rfl,rfl,by intro lane bound; omega⟩
  | succ width ih =>
    obtain ⟨first,read,remaining⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨rest,tailRead,same⟩ := Option.map_eq_some_iff.mp remaining
    subst result
    obtain ⟨parts,restEq,size,claims⟩ := ih _ rest tailRead
    refine ⟨first::parts,?_,by rw [List.length_cons,size],?_⟩
    · simp only [List.flatten_cons,restEq]
    · intro lane bound
      cases lane with
      | zero => simpa only [Nat.zero_mul,List.drop_zero,List.getElem?_cons_zero] using read
      | succ lane =>
        have claim := claims lane (by omega)
        have offsets : code.messageLength+lane*code.messageLength = (lane+1)*code.messageLength := by ring
        simpa only [List.getElem?_cons_succ,List.drop_drop,offsets] using claim

/-- Whole-response input shape and all lane-specific encodings follow from
the real checked API result. No input or output vector is silently truncated. -/
theorem encodeResponses_parts (code : Code) (width : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.encodeResponses code width input = some result) :
    input.length = width*code.messageLength ∧
    ∃ parts : List (List GoldWord), result = parts.flatten ∧ parts.length = width ∧
      ∀ lane < width, NativeGoldRowEncoding.encodeRow code ((input.drop (lane*code.messageLength)).take code.messageLength) = parts[lane]? := by
  unfold NativeGoldRowEncoding.encodeResponses at success
  split at success
  · rename_i size
    exact ⟨size,rows_parts code width input result success⟩
  · contradiction

/-- Uniform row concatenation preserves the exact native lane-major address. -/
theorem flatten_get (parts : List (List GoldWord)) (stride : ℕ)
    (sized : ∀ lane < parts.length, (parts[lane]?.getD []).length = stride)
    (lane offset : ℕ) (laneBound : lane < parts.length) (offsetBound : offset < stride) :
    parts.flatten[lane*stride+offset]? = (parts[lane]?.getD [])[offset]? := by
  induction parts generalizing lane with
  | nil => simp only [List.length_nil] at laneBound; omega
  | cons first tail ih =>
    have firstSize := sized 0 (by simp)
    simp only [List.getElem?_cons_zero,Option.getD_some] at firstSize
    have tailSize (index : ℕ) (bound : index < tail.length) : (tail[index]?.getD []).length = stride := by
      have next := sized (index+1) (by simp only [List.length_cons]; omega)
      simpa only [List.getElem?_cons_succ] using next
    cases lane with
    | zero =>
      simp only [List.flatten_cons,Nat.zero_mul,zero_add,List.getElem?_cons_zero,Option.getD_some]
      exact List.getElem?_append_left (by rw [firstSize]; exact offsetBound)
    | succ lane =>
      rw [List.flatten_cons,List.getElem?_append_right (by rw [firstSize,Nat.succ_mul]; omega),
        List.getElem?_cons_succ,firstSize,Nat.succ_mul]
      have index : (lane*stride+stride+offset)-stride = lane*stride+offset := by omega
      rw [index]
      exact ih tailSize lane (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using laneBound)

noncomputable section

/-- Every computed lane is coded, and its coefficient table is fixed by that
lane's original response chunk, including lazy representations and padding. -/
theorem encodeResponses_coded (code : Code) (m width : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.encodeResponses code width input = some result)
    (enough : m ≤ 2^code.logSize) (padding : code.messageLength ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (NativeGoldSolinas.value code.planRoot) (2^(code.logSize+1))) :
    ∃ parts : List (List GoldWord), result = parts.flatten ∧ parts.length = width ∧
      ∀ lane < width, ∃ row : List GoldWord, parts[lane]? = some row ∧
        NativeGoldRowMeaning.word code row = BlockEncoder.encode
          (NTTButterfly.domain code.logSize (NativeGoldSolinas.value code.planRoot) primitive)
          (NativeGoldRowMeaning.coefficients code m ((input.drop (lane*code.messageLength)).take code.messageLength)) ∧
        NativeGoldRowMeaning.word code row ∈ BlockCode.code
          (NTTButterfly.domain code.logSize (NativeGoldSolinas.value code.planRoot) primitive) m code.blockWidth := by
  obtain ⟨_,parts,eq,size,claims⟩ := encodeResponses_parts code width input result success
  refine ⟨parts,eq,size,?_⟩
  intro lane bound
  have present : lane < parts.length := by rw [size]; exact bound
  let row := parts[lane]'present
  have stored : parts[lane]? = some row := List.getElem?_eq_getElem present
  have read : NativeGoldRowEncoding.encodeRow code ((input.drop (lane*code.messageLength)).take code.messageLength) = some row :=
    (claims lane bound).trans stored
  have rowSize := (NativeGoldRowEncoding.encodeRow_shape code _ row read).2.1
  have padded : ((input.drop (lane*code.messageLength)).take code.messageLength).length ≤ m*code.blockWidth := by
    rw [rowSize]
    exact padding
  exact ⟨row,stored,NativeGoldRowMeaning.encodeRow_value code m _ row read enough padded primitive,
    NativeGoldRowMeaning.encodeRow_mem_code code m _ row read enough padded primitive⟩

/-- Direct field interpretation of the returned flat encoded response. -/
def laneWord (code : Code) (result : List GoldWord) (lane : ℕ) : Fin (2^code.logSize) → Fin code.blockWidth → Goldilocks :=
  fun symbol coordinate => goldValue (result[lane*(2^code.logSize*code.blockWidth)+(finProdFinEquiv (symbol,coordinate)).val]?.getD 0)

/-- The actual returned flat vector has the required codeword in every lane,
with coefficients from the original response and no existential certificate
remaining in the verifier interface. -/
theorem encodeResponses_lanes (code : Code) (m width : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.encodeResponses code width input = some result)
    (enough : m ≤ 2^code.logSize) (padding : code.messageLength ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (NativeGoldSolinas.value code.planRoot) (2^(code.logSize+1))) :
    ∀ lane < width,
      laneWord code result lane = BlockEncoder.encode
        (NTTButterfly.domain code.logSize (NativeGoldSolinas.value code.planRoot) primitive)
        (NativeGoldRowMeaning.coefficients code m ((input.drop (lane*code.messageLength)).take code.messageLength)) ∧
      laneWord code result lane ∈ BlockCode.code
        (NTTButterfly.domain code.logSize (NativeGoldSolinas.value code.planRoot) primitive) m code.blockWidth := by
  obtain ⟨_,parts,eq,size,claims⟩ := encodeResponses_parts code width input result success
  have rows (lane : ℕ) (bound : lane < parts.length) :
      ∃ row : List GoldWord, parts[lane]? = some row ∧
        NativeGoldRowEncoding.encodeRow code ((input.drop (lane*code.messageLength)).take code.messageLength) = some row := by
    have read : parts[lane]? = some (parts[lane]'bound) := List.getElem?_eq_getElem bound
    exact ⟨_,read,(claims lane (by rw [← size]; exact bound)).trans read⟩
  have sized (lane : ℕ) (bound : lane < parts.length) :
      (parts[lane]?.getD []).length = 2^code.logSize*code.blockWidth := by
    obtain ⟨row,stored,read⟩ := rows lane bound
    rw [stored,Option.getD_some]
    exact (NativeGoldRowEncoding.encodeRow_shape _ _ _ read).2.2.1
  intro lane bound
  have inside : lane < parts.length := by rw [size]; exact bound
  obtain ⟨row,stored,read⟩ := rows lane inside
  have same : laneWord code result lane = NativeGoldRowMeaning.word code row := by
    funext symbol coordinate
    rw [laneWord,eq,flatten_get parts _ sized lane _ inside (finProdFinEquiv (symbol,coordinate)).isLt,stored,Option.getD_some]
    rfl
  have rowSize := (NativeGoldRowEncoding.encodeRow_shape _ _ _ read).2.1
  have padded : ((input.drop (lane*code.messageLength)).take code.messageLength).length ≤ m*code.blockWidth := by
    rw [rowSize]
    exact padding
  rw [same]
  exact ⟨NativeGoldRowMeaning.encodeRow_value code m _ row read enough padded primitive,
    NativeGoldRowMeaning.encodeRow_mem_code code m _ row read enough padded primitive⟩

/-- The original retained code root determines every lane's semantic domain.
The successful row checks derive the plan-root equality; it is not a supplied
cache-consistency certificate. -/
theorem encodeResponses_retained_lanes (code : Code) (m width : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.encodeResponses code width input = some result)
    (enough : m ≤ 2^code.logSize) (padding : code.messageLength ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (goldValue code.domainRoot) (2^(code.logSize+1))) :
    ∀ lane < width,
      laneWord code result lane = BlockEncoder.encode
        (NTTButterfly.domain code.logSize (goldValue code.domainRoot) primitive)
        (NativeGoldRowMeaning.coefficients code m ((input.drop (lane*code.messageLength)).take code.messageLength)) ∧
      laneWord code result lane ∈ BlockCode.code
        (NTTButterfly.domain code.logSize (goldValue code.domainRoot) primitive) m code.blockWidth := by
  obtain ⟨_,parts,_,size,claims⟩ := encodeResponses_parts code width input result success
  intro lane bound
  have present : lane < parts.length := by rw [size]; exact bound
  have read : NativeGoldRowEncoding.encodeRow code ((input.drop (lane*code.messageLength)).take code.messageLength) =
      some (parts[lane]'present) := (claims lane bound).trans (List.getElem?_eq_getElem present)
  have same := NativeGoldRowMeaning.root_value code (NativeGoldRowEncoding.encodeRow_shape code _ _ read).1
  have planPrimitive : IsPrimitiveRoot (NativeGoldSolinas.value code.planRoot) (2^(code.logSize+1)) := by
    rw [← same]
    exact primitive
  have properties := encodeResponses_lanes code m width input result success enough padding planPrimitive lane bound
  simpa only [← same] using properties

end
end FormalProof4FHE.HasteBoots.NativeGoldResponseMeaning
