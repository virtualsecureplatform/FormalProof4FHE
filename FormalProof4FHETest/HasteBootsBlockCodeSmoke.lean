module

import all FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
import all FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext
import all FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding
import all FormalProof4FHE.HasteBoots.NTTRootCheck
import all Init.Data.String.Defs
import all Batteries.Data.Except

/-! Complete native retained-code and context bytes from the pinned HasteBoots
constructor. Table responses are fixture backend observations; root discovery
and mutable-cache refinement are not proved by these tests. -/
open FormalProof4FHE.HasteBoots
namespace NativeGoldBlockCodeSmoke
open NativeGoldBlockCode
private noncomputable def usize (n : ℕ) : NativeUsizeMessage.Usize := ⟨n%(2^64),Nat.mod_lt _ (by decide)⟩
private noncomputable def canonical (n : ℕ) : NativeGoldSolinas.Word := ⟨n%NativeFields.goldilocksModulus,Nat.mod_lt _ (by decide)⟩
private noncomputable def bytes (values : List ℕ) : InputIndexedOracle.Input := values.map (fun n => ⟨n%256,Nat.mod_lt _ (by decide)⟩)
private noncomputable def tables : Tables where
  generate log := decide (log=5 ∨ log=6 ∨ log=8 ∨ log=9)
  initTable _ := true
  load log := match log with
    | 5 => some (canonical 549755813888)
    | 6 => some (canonical 17870292113338400769)
    | 8 => some (canonical 1803076106186727246)
    | 9 => some (canonical 11353340290879379826)
    | _ => none
private noncomputable def stored (message block padded count root : ℕ) : Stored :=
  ⟨usize message,usize block,usize padded,usize count,NativeBrakedownContext.modulus,usize root⟩
private noncomputable def code2 := stored 2 2 1 32 549755813888
example : build tables (usize 2) (usize 2) (usize 2) = .ok code2 := by decide +kernel
example : codec.encode code2 = bytes [2, 2, 1, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0] := by decide +kernel
private noncomputable def code8 := stored 8 3 4 32 549755813888
example : build tables (usize 8) (usize 3) (usize 2) = .ok code8 := by decide +kernel
example : codec.encode code8 = bytes [8, 3, 4, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0] := by decide +kernel
private noncomputable def code17 := stored 17 2 16 64 17870292113338400769
example : build tables (usize 17) (usize 2) (usize 4) = .ok code17 := by decide +kernel
example : codec.encode code17 = bytes [17, 2, 16, 64, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 1, 0, 0, 8, 255, 7, 0, 248] := by decide +kernel
private noncomputable def code128 := stored 128 1 128 256 1803076106186727246
example : build tables (usize 128) (usize 1) (usize 2) = .ok code128 := by decide +kernel
example : codec.encode code128 = bytes [128, 1, 128, 251, 0, 1, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 78, 31, 65, 92, 42, 208, 5, 25] := by decide +kernel
private noncomputable def code129 := stored 129 3 64 512 11353340290879379826
example : build tables (usize 129) (usize 3) (usize 8) = .ok code129 := by decide +kernel
example : codec.encode code129 = bytes [129, 3, 64, 251, 0, 2, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 114, 217, 254, 139, 215, 42, 143, 157] := by decide +kernel
private noncomputable def code1 := stored 1 17 1 32 549755813888
example : build tables (usize 1) (usize 17) (usize 2) = .ok code1 := by decide +kernel
example : codec.encode code1 = bytes [1, 17, 1, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0] := by decide +kernel
example : codec.read (codec.encode code17 ++ bytes [88,99]) = some (code17,bytes [88,99]) := codec.read_encode _ _
private noncomputable def parameters : NativeBrakedownContext.Parameters Stored := ⟨usize 2,usize 3,usize 1,usize 1,code2⟩
example : NativeBrakedownContext.input description.row parameters = some (bytes [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 47, 118, 50, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 2, 3, 1, 1, 2, 32, 26, 98, 108, 111, 99, 107, 45, 114, 115, 47, 110, 101, 103, 97, 99, 121, 99, 108, 105, 99, 45, 110, 116, 116, 47, 118, 49, 2, 2, 1, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0]) := by decide +kernel
example : build tables (usize 0) (usize 1) (usize 2) = .error .dimensions := by decide +kernel
example : build tables (usize 1) (usize 0) (usize 2) = .error .dimensions := by decide +kernel
example : build tables (usize 1) (usize 1) (usize 0) = .error .dimensions := by decide +kernel
example : build tables (usize 1) (usize 1) (usize 1) = .error .dimensions := by decide +kernel
example : build tables (usize 1) (usize 1) (usize 3) = .error .dimensions := by decide +kernel
example : build tables (usize 18446744073709551615) (usize 1) (usize 2) = .error .messageOverflow := by decide +kernel
example : build tables (usize 9223372036854775808) (usize 1) (usize 2) = .error .domainOverflow := by decide +kernel
example : build tables (usize 1) (usize 18446744073709551615) (usize 2) = .error .codewordOverflow := by decide +kernel
example : build tables (usize 2147483648) (usize 1) (usize 2) = .error .generation := by decide +kernel
example : build {tables with initTable := fun _ => false} (usize 2) (usize 2) (usize 2) = .error .initialization := by decide +kernel
example : build {tables with load := fun _ => none} (usize 2) (usize 2) (usize 2) = .error .loading := by decide +kernel
example : NativeBrakedownParameters.codeShape description parameters = true :=
  NativeGoldBlockCodeMeaning.constructor_codeShape tables (usize 2) (usize 2) (usize 2) parameters (by decide +kernel) (by decide +kernel)
private theorem primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue code2.domainRoot) (2^(logSize code2+1)) := by
  apply NTTRootCheck.primitive_of_half_power 5 _ NativeFields.goldilocks_odd
  decide +kernel
example (plan : NativeGoldSolinas.Word) (input result : List NativeFieldRepresentation.GoldWord)
    (success : NativeGoldRowEncoding.encodeResponses (encoding code2 plan) 3 input = some result) :
    ∀ lane < 3, NativeGoldResponseMeaning.laneWord (encoding code2 plan) result lane ∈
      BlockCode.code (NTTButterfly.domain (logSize code2) (NativeFieldRepresentation.goldValue code2.domainRoot) primitive)
        code2.messageBlocks.val code2.blockWidth.val := by
  intro lane bound
  exact (NativeGoldBlockCodeMeaning.response_lanes tables (usize 2) (usize 2) (usize 2) code2 (by decide +kernel)
    plan 3 input result success primitive lane bound).2
end NativeGoldBlockCodeSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCode.serialize_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCode.serialize_fields

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCode.serialize_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCode.serialize_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCode.serialize_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCode.serialize_injective

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCode.build_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCode.build_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.metadata_computed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.metadata_computed

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.input_computed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.input_computed

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.contextFields_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.contextFields_injective

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.input_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.input_injective

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.metadata_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext.metadata_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.ceil_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.ceil_cover

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.ceil_minimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.ceil_minimal

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.ceil_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.ceil_positive

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.next_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.next_cover

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.next_minimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.next_minimal

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.padded_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.padded_cover

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.padded_minimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.padded_minimal

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.domain_power' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.domain_power

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_log

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_dimensions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_dimensions

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_codeShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_codeShape

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.primitive_log_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.primitive_log_upper

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_encoding_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_encoding_check

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_responses_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.constructor_responses_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.response_lanes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning.response_lanes

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.run_protocol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.run_protocol

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.observations

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.encoded_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.encoded_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.columns_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.columns_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.encoded_coded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding.encoded_coded
