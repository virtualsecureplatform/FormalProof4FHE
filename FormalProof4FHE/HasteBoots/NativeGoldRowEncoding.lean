module

public import FormalProof4FHE.HasteBoots.NativeGoldNtt

@[expose] public section

/-! Raw BlockReedSolomonCode::encode_row and per-lane PCS encode_responses.
The trusted plan root is checked against the retained code root before the
raw-zero shortcut. Gathered coordinates are transformed by the actual scalar
buffer algorithm, then interleaved by symbol. No encoded response is supplied
by the prover. These checked wrappers expose existing successful native
constructor/slice preconditions; code construction, native plan discovery,
SIMD and instruction refinement are still separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldRowEncoding

open NativeFieldRepresentation NativeFields

structure Code where
  messageLength : ℕ
  blockWidth : ℕ
  logSize : ℕ
  domainRoot : GoldWord
  planRoot : NativeGoldSolinas.Word

def check (code : Code) : Bool :=
  if 5 ≤ code.logSize ∧ code.logSize ≤ 31 then
    decide (code.messageLength ≠ 0 ∧ code.blockWidth ≠ 0 ∧
      2^code.logSize*code.blockWidth < 2^64 ∧ code.messageLength ≤ 2^code.logSize*code.blockWidth ∧
      goldCanonical code.domainRoot = code.planRoot.val)
  else false

def rawZero (input : List GoldWord) : Bool := input.all (fun word => decide (word.val = 0))

/-- Coordinate j of consecutive message blocks, including a partial last block. -/
def coordinate (code : Code) (input : List GoldWord) (lane : ℕ) : List GoldWord :=
  List.ofFn (fun block : Fin (2^code.logSize) => input[block.val*code.blockWidth+lane]?.getD 0)

def transformed (code : Code) (input : List GoldWord) : List (List GoldWord) :=
  (List.range code.blockWidth).map (fun lane =>
    NativeGoldNtt.forwardData code.logSize code.planRoot (coordinate code input lane))

/-- Copy lane j's transform to symbol*b+j; all final words are original
canonical backend outputs. The native mutable copy-loop refinement is open. -/
def payload (code : Code) (input : List GoldWord) : List GoldWord :=
  let lanes := transformed code input
  List.ofFn (fun address : Fin (2^code.logSize*code.blockWidth) =>
    let indices := finProdFinEquiv.symm address
    ((lanes[indices.2.val]?.getD [])[indices.1.val]?.getD 0))

def encodeRow (code : Code) (input : List GoldWord) : Option (List GoldWord) :=
  if check code && decide (input.length = code.messageLength) then
    if rawZero input then some (List.replicate (2^code.logSize*code.blockWidth) 0)
    else some (payload code input)
  else none

/-- Each output lane is encoded from its own exact-length response chunk. -/
def rows (code : Code) : ℕ → List GoldWord → Option (List GoldWord)
  | 0,_ => some []
  | width+1,input =>
    (encodeRow code (input.take code.messageLength)).bind (fun first =>
      (rows code width (input.drop code.messageLength)).map (fun rest => first ++ rest))

def encodeResponses (code : Code) (width : ℕ) (input : List GoldWord) : Option (List GoldWord) :=
  if input.length = width*code.messageLength then rows code width input else none

theorem check_iff (code : Code) : check code = true ↔
    5 ≤ code.logSize ∧ code.logSize ≤ 31 ∧ code.messageLength ≠ 0 ∧ code.blockWidth ≠ 0 ∧
    2^code.logSize*code.blockWidth < 2^64 ∧ code.messageLength ≤ 2^code.logSize*code.blockWidth ∧
    goldCanonical code.domainRoot = code.planRoot.val := by
  simp only [check]
  split <;> simp_all

/-- Native is_canonical && field-zero agrees with the literal raw-zero test. -/
theorem raw_zero_iff (word : GoldWord) : word.val = 0 ↔ word.val < goldilocksModulus ∧ goldCanonical word = 0 := by
  have positive : 0 < goldilocksModulus := by decide
  unfold goldCanonical
  split <;> omega

theorem coordinate_length (code : Code) (input : List GoldWord) (lane : ℕ) :
    (coordinate code input lane).length = 2^code.logSize := List.length_ofFn

theorem payload_length (code : Code) (input : List GoldWord) :
    (payload code input).length = 2^code.logSize*code.blockWidth := List.length_ofFn

/-- The final symbol-major payload contains exactly each native coordinate
transform output, without a projection or normalization at scatter time. -/
theorem payload_get (code : Code) (input : List GoldWord) (symbol : Fin (2^code.logSize))
    (lane : Fin code.blockWidth) :
    (payload code input)[symbol.val*code.blockWidth+lane.val]'(by
      rw [payload_length]; have := symbol.isLt; have := lane.isLt; nlinarith) =
      (NativeGoldNtt.forwardData code.logSize code.planRoot (coordinate code input lane.val))[symbol.val]'(by
        rw [NativeGoldNtt.forwardData_length _ _ _ (coordinate_length _ _ _)]; exact symbol.isLt) := by
  have address : (⟨symbol.val*code.blockWidth+lane.val,by
      have := symbol.isLt; have := lane.isLt; nlinarith⟩ : Fin (2^code.logSize*code.blockWidth)) =
      finProdFinEquiv (symbol,lane) := by
    apply Fin.ext
    change symbol.val*code.blockWidth+lane.val = lane.val+code.blockWidth*symbol.val
    ac_rfl
  simp only [payload,List.getElem_ofFn,address,Equiv.symm_apply_apply,transformed,List.getElem?_map,
    List.getElem?_range,lane.isLt,Option.map_some,Option.getD_some]
  rw [List.getElem?_eq_getElem (by rw [NativeGoldNtt.forwardData_length _ _ _ (coordinate_length _ _ _)]; exact symbol.isLt)]
  rfl

/-- Every transform getter is in bounds on the actual copied symbol and lane. -/
theorem transformed_shape (code : Code) (input : List GoldWord) :
    (transformed code input).length = code.blockWidth ∧
      ∀ lane ∈ transformed code input, lane.length = 2^code.logSize ∧ ∀ word ∈ lane, word.val < goldilocksModulus := by
  refine ⟨by simp only [transformed,List.length_map,List.length_range],?_⟩
  intro lane member
  obtain ⟨index,_,same⟩ := List.mem_map.mp member
  subst lane
  exact ⟨NativeGoldNtt.forwardData_length _ _ _ (coordinate_length _ _ _),NativeGoldNtt.forwardData_canonical _ _ _⟩

private theorem canonical_get (values : List GoldWord) (index : ℕ)
    (valid : ∀ word ∈ values, word.val < goldilocksModulus) : (values[index]?.getD 0).val < goldilocksModulus := by
  cases found : values[index]? with
  | none => simp only [Option.getD_none,Fin.val_zero]; decide
  | some word =>
    simp only [Option.getD_some]
    exact valid word (List.mem_of_getElem? found)

theorem payload_canonical (code : Code) (input : List GoldWord) :
    ∀ word ∈ payload code input, word.val < goldilocksModulus := by
  intro word member
  obtain ⟨address,same⟩ := List.mem_ofFn.mp member
  subst word
  dsimp only
  apply canonical_get
  cases found : (transformed code input)[(finProdFinEquiv.symm address).2.val]? with
  | none => simp only [Option.getD_none]; simp
  | some lane =>
    simp only [Option.getD_some]
    exact (transformed_shape code input).2 lane (List.mem_of_getElem? found) |>.2

theorem encodeRow_shape (code : Code) (input result : List GoldWord) (success : encodeRow code input = some result) :
    check code = true ∧ input.length = code.messageLength ∧ result.length = 2^code.logSize*code.blockWidth ∧
      ∀ word ∈ result, word.val < goldilocksModulus := by
  unfold encodeRow at success
  split at success
  · rename_i guards
    have facts := Bool.and_eq_true_iff.mp guards
    refine ⟨facts.1,of_decide_eq_true facts.2,?_⟩
    split at success
    · have same := Option.some.inj success
      subst result
      refine ⟨List.length_replicate,?_⟩
      intro word member
      have same := List.mem_replicate.mp member |>.2
      subst word
      exact (by decide : (0 : GoldWord).val < goldilocksModulus)
    · have same := Option.some.inj success
      subst result
      exact ⟨payload_length _ _,payload_canonical _ _⟩
  · contradiction

theorem encodeRow_complete (code : Code) (input : List GoldWord) (valid : check code = true)
    (size : input.length = code.messageLength) : ∃ result, encodeRow code input = some result := by
  simp only [encodeRow,valid,size,decide_true,Bool.true_and,ite_true]
  split <;> exact ⟨_,rfl⟩

/-- Successful native preconditions encode every response lane; no zip
truncation or caller-supplied encoded vector is used. -/
theorem encodeResponses_complete (code : Code) (width : ℕ) (input : List GoldWord) (valid : check code = true)
    (size : input.length = width*code.messageLength) : ∃ result, encodeResponses code width input = some result := by
  have complete (width : ℕ) (input : List GoldWord) (size : input.length = width*code.messageLength) :
      ∃ result, rows code width input = some result := by
    induction width generalizing input with
    | zero => exact ⟨[],rfl⟩
    | succ width ih =>
      have firstSize : (input.take code.messageLength).length = code.messageLength := by
        rw [List.length_take,size,Nat.succ_mul,Nat.min_eq_left (by omega)]
      have tailSize : (input.drop code.messageLength).length = width*code.messageLength := by
        rw [List.length_drop,size,Nat.succ_mul]; omega
      obtain ⟨first,read⟩ := encodeRow_complete code _ valid firstSize
      obtain ⟨rest,tailRead⟩ := ih _ tailSize
      exact ⟨first++rest,by simp only [rows,read,Option.bind_some,tailRead,Option.map_some]⟩
  obtain ⟨result,read⟩ := complete width input size
  exact ⟨result,by simp only [encodeResponses,ite_eq_left size,read]⟩

theorem encodeResponses_shape (code : Code) (width : ℕ) (input result : List GoldWord)
    (success : encodeResponses code width input = some result) :
    input.length = width*code.messageLength ∧ result.length = width*(2^code.logSize*code.blockWidth) ∧
      ∀ word ∈ result, word.val < goldilocksModulus := by
  unfold encodeResponses at success
  split at success
  · rename_i size
    refine ⟨size,?_⟩
    induction width generalizing input result with
    | zero => have same := Option.some.inj success; subst result; exact ⟨by simp,by simp⟩
    | succ width ih =>
      obtain ⟨first,read,remaining⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨rest,tailRead,same⟩ := Option.map_eq_some_iff.mp remaining
      subst result
      have firstSpec := encodeRow_shape _ _ _ read
      have tailSize : (input.drop code.messageLength).length = width*code.messageLength := by
        rw [List.length_drop,size,Nat.succ_mul]; omega
      have previous := ih _ rest tailSize tailRead
      refine ⟨?_,?_⟩
      · rw [List.length_append,firstSpec.2.2.1,previous.1,Nat.succ_mul]; omega
      · intro word member
        rcases List.mem_append.mp member with member | member
        · exact firstSpec.2.2.2 word member
        · exact previous.2 word member
  · contradiction

end FormalProof4FHE.HasteBoots.NativeGoldRowEncoding
