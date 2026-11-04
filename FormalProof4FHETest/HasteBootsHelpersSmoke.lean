module

import all FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers

open FormalProof4FHE.HasteBoots

namespace NativeHelperHandoffSmoke
open NativeSharedLookupHelpers
private noncomputable def word (n : ℕ) : NativeFieldRepresentation.GoldWord := ⟨n % (2^64),Nat.mod_lt _ (by decide)⟩
private noncomputable def usize (n : ℕ) : NativeUsizeMessage.Usize := word n
private noncomputable def root (n : ℕ) : NativeRootMessage.Digest := fun _ => ⟨n % 256,Nat.mod_lt _ (by decide)⟩
private noncomputable def proof : NativeSharedLookupProofData.Proof ℕ Unit :=
  ⟨⟨⟨[],by decide⟩,by decide⟩,⟨[root 7,root 11,root 7],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩,
    ⟨[![word (2^64-1),word 2,word 3],![word 5,word 7,word 11],![word 13,word 17,word 19]],by decide⟩,
    (),⟨[31,37,41],by decide⟩⟩
private noncomputable def packed := build (usize 4) [] proof
private noncomputable def summary (result : Option (Plan ℕ)) := result.map (fun plan =>
  plan.calls.map (fun call => ((call.root ⟨0,by decide⟩).val,call.values.val.map Fin.val,call.opening)))
example : summary packed = some [(7,[2^64-1,2,3,0],31),(11,[5,7,11,0],37),(7,[13,17,19,0],41)] := by decide +kernel
example : packed.map (fun plan => plan.values.val.map (fun row => row.val.map Fin.val)) =
    some [[2^64-1,2,3,0],[5,7,11,0],[13,17,19,0]] := by decide +kernel
example : packed.map (fun plan => NativeGoldPcsWire.queryCodec.encode plan.query) = some [0] := by decide +kernel
example : (build (usize 2) [] proof).isNone = true := by decide +kernel
example : (build (usize 0) [] proof).isNone = true := by decide +kernel
-- The low-level zip retains native truncation; the completed-run theorem
-- discharges the upstream equal-length gates rather than altering this zip.
private noncomputable def short : NativeSharedLookupProofData.Proof ℕ Unit := {proof with helperOpenings := ⟨[31,37],by decide⟩}
example : summary (build (usize 4) [] short) = some [(7,[2^64-1,2,3,0],31),(11,[5,7,11,0],37)] := by decide +kernel
private noncomputable def oneRoot : NativeSharedLookupProofData.Proof ℕ Unit := {proof with roots := ⟨[root 7],by decide⟩}
example : (build (usize 4) [] oneRoot).map (fun plan => (plan.calls.length,plan.values.val.length)) = some (1,3) := by decide +kernel
example : (NativeGoldPcsWire.queryCodec.encode <$> NativeGoldPcsWire.coefficientsQuery 4 []) = some [0] := by decide +kernel
end NativeHelperHandoffSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.vector_raw' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.vector_raw

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.values_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.values_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.calls_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.calls_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.calls_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.calls_get

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.build_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.build_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.build_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.build_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.query_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.query_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.packet_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.packet_at

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.no_truncation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.no_truncation

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.preflight_helper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.preflight_helper

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.completed_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.completed_geometry

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.run_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.run_protocol

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.completed_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.completed_handoff
