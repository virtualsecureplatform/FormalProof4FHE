module

public import FormalProof4FHE.HasteBoots.NativeGoldBlockCode
public import FormalProof4FHE.HasteBoots.NativeGoldResponseMeaning
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-! Constructor-derived coefficient counts for the actual retained block code.
Primitive root generation is still a backend obligation; encoder correctness
and padding/dimension certificates are not supplied by the caller. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning

open NativeGoldBlockCode
open NativeUsizeMessage (Usize)
open NativeFieldRepresentation (GoldWord goldValue)

theorem ceil_cover (message block : ℕ) (positive : 0 < block) :
    message ≤ ceilBlocks message block*block := by
  have decomposition := Nat.mod_add_div message block
  have remainder := Nat.mod_lt message positive
  unfold ceilBlocks
  split <;> simp only [Nat.add_zero,Nat.add_mul,Nat.one_mul] <;> nlinarith

theorem ceil_minimal (message block count : ℕ) (positive : 0 < block)
    (covers : message ≤ count*block) : ceilBlocks message block ≤ count := by
  have decomposition := Nat.mod_add_div message block
  unfold ceilBlocks
  split
  · simp only [Nat.add_zero]
    nlinarith
  · rename_i nonzero
    have remainderPositive := Nat.pos_of_ne_zero nonzero
    nlinarith

theorem ceil_positive (message block : ℕ) (messagePositive : 0 < message) (blockPositive : 0 < block) :
    0 < ceilBlocks message block := by
  have covers := ceil_cover message block blockPositive
  by_contra rejected
  have zero : ceilBlocks message block = 0 := by omega
  rw [zero,Nat.zero_mul] at covers
  omega

theorem next_cover (count : ℕ) (positive : 0 < count) : count ≤ 2^(nextLog count) :=
  NativeBrakedownParameters.leaves_cover count positive

theorem next_minimal (count exponent : ℕ) (covers : count ≤ 2^exponent) : nextLog count ≤ exponent :=
  NativeBrakedownParameters.height_minimal count exponent covers

theorem padded_cover (message block : ℕ) (messagePositive : 0 < message) (blockPositive : 0 < block) :
    message ≤ paddedBlocks message block*block := by
  exact (ceil_cover message block blockPositive).trans
    (Nat.mul_le_mul_right block (next_cover _ (ceil_positive message block messagePositive blockPositive)))

theorem padded_minimal (message block exponent : ℕ) (blockPositive : 0 < block)
    (covers : message ≤ 2^exponent*block) : nextLog (ceilBlocks message block) ≤ exponent :=
  next_minimal _ exponent (ceil_minimal message block _ blockPositive covers)

theorem domain_power (message block blowup : ℕ) (power : blowup = 2^(nextLog blowup)) :
    domainBlocks message block blowup = 2^(max (nextLog (ceilBlocks message block)+nextLog blowup) 5) := by
  unfold domainBlocks paddedBlocks
  conv_lhs => rw [power,← pow_add]
  have fixed : (32 : ℕ) = 2^5 := by decide
  rw [fixed]
  by_cases order : nextLog (ceilBlocks message block)+nextLog blowup ≤ 5
  · rw [max_eq_right order,max_eq_right (Nat.pow_le_pow_right (by decide) order)]
  · have order' : 5 ≤ nextLog (ceilBlocks message block)+nextLog blowup := by omega
    rw [max_eq_left order',max_eq_left (Nat.pow_le_pow_right (by decide) order')]

theorem constructor_log (tables : Tables) (message block blowup : Usize) (code : Stored)
    (success : build tables message block blowup = .ok code) :
    logSize code = max (nextLog (ceilBlocks message.val block.val)+nextLog blowup.val) 5 ∧
      code.blocks.val = 2^(logSize code) := by
  have spec := build_spec tables message block blowup code success
  have power := domain_power message.val block.val blowup.val spec.dimensions.2.2.2
  have count := spec.count.trans power
  have exponent : logSize code = max (nextLog (ceilBlocks message.val block.val)+nextLog blowup.val) 5 := by
    simp only [logSize,count,Nat.size_pow,Nat.add_sub_cancel_right]
  exact ⟨exponent,by rw [exponent]; exact count⟩

/-- Exact native padded coefficient count, strict expansion, and complete
message coverage are consequences of constructor success. -/
theorem constructor_dimensions (tables : Tables) (message block blowup : Usize) (code : Stored)
    (success : build tables message block blowup = .ok code) :
    0 < code.messageBlocks.val ∧ code.messageBlocks.val < 2^(logSize code) ∧
      code.messageLength.val ≤ code.messageBlocks.val*code.blockWidth.val ∧
      5 ≤ logSize code ∧ 2^(logSize code)*code.blockWidth.val < 2^64 := by
  have spec := build_spec tables message block blowup code success
  have logs := constructor_log tables message block blowup code success
  have paddedPositive : 0 < paddedBlocks message.val block.val := by unfold paddedBlocks; positivity
  have expanded : paddedBlocks message.val block.val < domainBlocks message.val block.val blowup.val := by
    have bigger : paddedBlocks message.val block.val*blowup.val ≤ domainBlocks message.val block.val blowup.val := le_max_left _ _
    have factor := spec.dimensions.2.2.1
    nlinarith
  refine ⟨by rw [spec.padded]; exact paddedPositive,?_,?_,?_,?_⟩
  · rw [← logs.2,spec.padded,spec.count]; exact expanded
  · rw [spec.messageEq,spec.blockEq,spec.padded]
    exact padded_cover _ _ (Nat.pos_of_ne_zero spec.dimensions.1) (Nat.pos_of_ne_zero spec.dimensions.2.1)
  · rw [logs.1]; exact le_max_right _ _
  · rw [← logs.2,spec.count,spec.blockEq]; exact spec.strideFits

/-- Parameter initialization reads the same constructed code. Its code-shape
gate follows from native message-length matching, without an assumed code
geometry or an independently chosen coefficient count. -/
theorem constructor_codeShape (tables : Tables) (message block blowup : Usize)
    (parameters : NativeBrakedownContext.Parameters Stored)
    (constructed : build tables message block blowup = .ok parameters.code)
    (messageMatches : message.val = 2^(parameters.numVariables.val-parameters.leftVariables.val)) :
    NativeBrakedownParameters.codeShape description parameters = true := by
  have spec := build_spec tables message block blowup parameters.code constructed
  have dimensions := constructor_dimensions tables message block blowup parameters.code constructed
  have count := (constructor_log tables message block blowup parameters.code constructed).2
  have messageLength : parameters.code.messageLength.val = 2^(parameters.numVariables.val-parameters.leftVariables.val) := by
    rw [spec.messageEq]; exact messageMatches
  have padding : parameters.code.messageLength.val ≤ parameters.code.blocks.val*parameters.code.blockWidth.val := by
    exact dimensions.2.2.1.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt (dimensions.2.1.trans_eq count.symm)))
  have blockPositive : parameters.code.blockWidth.val ≠ 0 := by rw [spec.blockEq]; exact spec.dimensions.2.1
  have blocksPositive : parameters.code.blocks.val ≠ 0 := by rw [count]; positivity
  unfold NativeBrakedownParameters.codeShape
  dsimp only [description]
  apply decide_eq_true
  exact ⟨messageLength,by rw [count]; exact dimensions.2.2.2.2,by rw [← messageLength]; exact padding,blocksPositive,blockPositive⟩

noncomputable section

/-- Goldilocks cannot have a primitive root for a larger native domain.
This derives the scalar wrapper's upper size bound from the retained root. -/
theorem primitive_log_upper (log : ℕ) (root : NativeFields.Goldilocks)
    (primitive : IsPrimitiveRoot root (2^(log+1))) : log ≤ 31 := by
  have nonzero := primitive.ne_zero (by positivity : 2^(log+1) ≠ 0)
  have divides := primitive.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one nonzero)
  by_contra tooLarge
  have lower : 33 ≤ log+1 := by omega
  have impossible := (Nat.pow_dvd_pow 2 lower).trans divides
  exact (by decide +kernel : ¬ (2^33 : ℕ) ∣ NativeFields.goldilocksModulus-1) impossible

/-- Loading the same constructor cache derives root agreement and every
checked encoding precondition. No plan-consistency certificate is supplied. -/
theorem constructor_encoding_check (tables : Tables) (message block blowup : Usize) (code : Stored)
    (constructed : build tables message block blowup = .ok code)
    (planRoot : NativeGoldSolinas.Word) (loaded : tables.load (logSize code) = some planRoot)
    (primitive : IsPrimitiveRoot (goldValue code.domainRoot) (2^(logSize code+1))) :
    NativeGoldRowEncoding.check (encoding code planRoot) = true := by
  have spec := build_spec tables message block blowup code constructed
  have dimensions := constructor_dimensions tables message block blowup code constructed
  obtain ⟨root,rootRead,rootEq⟩ := spec.loaded
  have same := Option.some.inj (rootRead.symm.trans loaded)
  subst root
  have canonical : NativeFieldRepresentation.goldCanonical code.domainRoot = planRoot.val := by
    rw [rootEq]
    exact ite_eq_right (by have bound := planRoot.isLt; change ¬ NativeFields.goldilocksModulus ≤ planRoot.val; omega)
  apply (NativeGoldRowEncoding.check_iff _).mpr
  refine ⟨dimensions.2.2.2.1,primitive_log_upper _ _ primitive,?_,?_,dimensions.2.2.2.2,?_,canonical⟩
  · change code.messageLength.val ≠ 0
    rw [spec.messageEq]; exact spec.dimensions.1
  · change code.blockWidth.val ≠ 0
    rw [spec.blockEq]; exact spec.dimensions.2.1
  · exact dimensions.2.2.1.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt dimensions.2.1))

/-- Every exact-size response has a computed encoding for a constructed code
with its own primitive root and successfully loaded retained cache. -/
theorem constructor_responses_complete (tables : Tables) (message block blowup : Usize) (code : Stored)
    (constructed : build tables message block blowup = .ok code)
    (planRoot : NativeGoldSolinas.Word) (loaded : tables.load (logSize code) = some planRoot)
    (primitive : IsPrimitiveRoot (goldValue code.domainRoot) (2^(logSize code+1)))
    (width : ℕ) (input : List GoldWord) (size : input.length = width*code.messageLength.val) :
    ∃ result, NativeGoldRowEncoding.encodeResponses (encoding code planRoot) width input = some result :=
  NativeGoldRowEncoding.encodeResponses_complete _ width input
    (constructor_encoding_check tables message block blowup code constructed planRoot loaded primitive) size

/-- A successfully constructed code fixes every lane's degree bound and
padding. Only primitive-root correctness of the actual retained backend root
remains a mathematical backend premise. -/
theorem response_lanes (tables : Tables) (message block blowup : Usize) (code : Stored)
    (constructed : build tables message block blowup = .ok code)
    (planRoot : NativeGoldSolinas.Word) (width : ℕ) (input result : List GoldWord)
    (success : NativeGoldRowEncoding.encodeResponses (encoding code planRoot) width input = some result)
    (primitive : IsPrimitiveRoot (goldValue code.domainRoot) (2^(logSize code+1))) :
    ∀ lane < width,
      NativeGoldResponseMeaning.laneWord (encoding code planRoot) result lane = BlockEncoder.encode
        (NTTButterfly.domain (logSize code) (goldValue code.domainRoot) primitive)
        (NativeGoldRowMeaning.coefficients (encoding code planRoot) code.messageBlocks.val
          ((input.drop (lane*code.messageLength.val)).take code.messageLength.val)) ∧
      NativeGoldResponseMeaning.laneWord (encoding code planRoot) result lane ∈ BlockCode.code
        (NTTButterfly.domain (logSize code) (goldValue code.domainRoot) primitive) code.messageBlocks.val code.blockWidth.val := by
  have dimensions := constructor_dimensions tables message block blowup code constructed
  exact NativeGoldResponseMeaning.encodeResponses_retained_lanes (encoding code planRoot) code.messageBlocks.val width input result success
    (Nat.le_of_lt dimensions.2.1) dimensions.2.2.1 primitive

end
end FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
