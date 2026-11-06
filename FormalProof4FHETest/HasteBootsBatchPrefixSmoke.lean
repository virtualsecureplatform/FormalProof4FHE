module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchColumns
import all FormalProof4FHETest.HasteBootsSourceGroupsSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (run)
open HasteBootsSourceGroupsSmoke (bytes queries values batchParameters nativeRoot nativePrefix nativeContextInput nativeContextDigest)
namespace HasteBootsBatchPrefixSmoke
noncomputable section
def nativeOpeningPart0 : Input := bytes [2,253,239,202,53,26,69,225,188,203,253,106,41,104,11,112,22,208,208,2,2,1,3,2,0,2,1,4,0,2,1,3,6,20,255,168,80,102,27,112,88,108,125,246,202,234,40,154,152,79,88,207,135,150,252,159,154,170,52,38,147,89,98,169,94,227,91,216,105,118,25,119,227,173,118,9,78,32,23,46,120,143,209,170,225,148,254,81,182,159,129,57,92,195,2,105,255,20,255,168,80,102,27,112,88,108,125,246,202,234,40,154]
def nativeOpeningPart1 : Input := bytes [152,79,88,207,135,150,252,159,154,170,52,38,147,89,98,169,94,227,91,216,105,118,25,119,227,173,118,9,78,32,23,46,120,143,209,170,225,148,254,81,182,159,129,57,92,195,2,105,255,18,2,179,17,23,9,92,168,113,65,75,87,182,228,31,157,14,48,43,35,104,13,32,250,121,222,243,21,46,145,0,196,159,61,168,110,32,171,2,237,242,12,164,105,4,187,96,184,174,92,185,99,119,229,156,89,201,1,200,201,35,197,174]
def nativeOpeningPart2 : Input := bytes [81,32,250,204,168,48,135,160,106,54,109,216,14,241,102,10,90,28,46,232,183,3,84,12,254,219,190,99,229,237,24,37,59,139,120,212,51,202,64,26,83,62,71,224,84,139,70,97,38,128,26,27,21,53,156,27,6,123,250,35,46,234,86,243,140,19,94,19,83,145,137,153,192,196,83,22,61,209,206,109,190,161,101,252,125,47,208,105,176,58,23,127,46,244,120,231,193,142,6,211,22,69,247,51,33,101,168,206,227,92,19,85]
def nativeOpeningPart3 : Input := bytes [228,218,2,41,148,87,156,50,99,226,244,82,106,70,57,207,115,25,183,134,211,74,34,162,162,121,252,100,12,88,51,136,237,45,17,102,194,243,39,149,128,170,146,132,54,16,67,202,205,134,41,130,14,240,159,183,44,125,255,53,176,60,125,154,16,126,159,165,136,124,207,100,151,225,227,226,186,244,19,129,156]
def nativeOpening : Input := List.flatten [nativeOpeningPart0,nativeOpeningPart1,nativeOpeningPart2,nativeOpeningPart3]
def start0Part0 : Input := bytes [0,8,0,0,0,0,0,0,0,112,114,111,116,111,99,111,108,29,0,0,0,0,0,0,0,72,97,115,116,101,66,111,111,116,115,32,102,114,97,109,101,100,32,83,72,65,75,69,50,53,54,32,118,49,0,11,0,0,0,0,0,0,0,97,112,112,108,105,99,97,116,105,111,110,35,0,0,0,0,0,0,0,72,97,115,116,101,66,111,111,116,115,32,116,121,112,101,100,32,99,108,97,115,115,105,99,97,108,32,112,114,105]
def start0Part1 : Input := bytes [109,101,32,118,49,0,15,0,0,0,0,0,0,0,116,114,117,115,116,101,100,32,112,114,111,102,105,108,101,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,17,0,0,0,0,0,0,0,116,121]
def start0Part2 : Input := bytes [112,101,100,32,112,114,105,109,101,32,102,105,101,108,100,16,0,0,0,0,0,0,0,1,0,0,0,255,255,255,255,0,0,0,0,0,0,0,0,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,23,0,0,0,0,0,0,0,97,116,111,109,105,99,32,78,84,84,32,114,111,119,32,112,104,97,115,101,32,118,50,1,28,0,0,0]
def start0Part3 : Input := bytes [0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,27,0,0,0,0,0,0,0,97,116,111,109,105,99,32,106,111,105,110,116,32,112,114,111,106,101,99,116,105,111,110,115,32,118,51,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,26,0,0,0,0,0,0,0]
def start0Part4 : Input := bytes [97,116,111,109,105,99,32,112,97,99,107,101,100,32,122,101,114,111,99,104,101,99,107,32,118,52,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,27,0,0,0,0,0,0,0,97,116,111,109,105,99,32,66,114,97,107,101,100,111,119,110,32,99,111,108,117,109,110,115,32,118,53,1,22,0,0,0,0,0,0,0,109,119,32,98,97]
def start0Part5 : Input := bytes [116,99,104,101,100,32,114,111,119,45,99,111,100,101,32,118,49,198,0,0,0,0,0,0,0,215,128,227,180,182,92,110,247,243,98,252,99,110,173,56,166,213,97,87,21,39,25,189,12,37,154,74,86,139,106,153,34,56,167,152,87,55,65,245,153,16,101,7,158,173,37,22,201,109,38,36,240,113,210,96,96,210,7,228,46,159,176,73,75,236,255,121,148,40,92,99,241,64,131,187,250,61,215,77,252,205,24,186,73,136,206,154]
def start0Part6 : Input := bytes [126,126,206,87,101,210,171,159,114,65,145,231,96,151,110,42,225,28,79,6,117,197,155,189,109,217,11,238,118,214,241,171,107,34,128,73,40,11,4,235,250,4,2,1,1,0,1,1,1,1,1,1,1,1,0,2,1,1,0,1,1,1,1,1,2,1,1,3,2,1,1,1,1,1,0,1,1,0,1,1,1,2,1,1,253,1,0,0,0,255,255,255,255,1,1,1,1,1,1,1,1,0,4,1,1,1,11,1,2,1,1,1]
def start0Part7 : Input := bytes [18,0,0,0,0,0,0,0,116,121,112,101,100,32,114,101,113,117,101,115,116,32,107,105,110,100,6,0,0,0,0,0,0,0,118,101,99,116,111,114,1,20,0,0,0,0,0,0,0,102,105,101,108,100,32,99,104,97,108,108,101,110,103,101,32,107,105,110,100,12,0,0,0,0,0,0,0,112,114,105,109,101,32,118,101,99,116,111,114,4,27,0,0,0,0,0,0,0,109,119,32,98,97,116,99,104,32,114,97,110,100,111]
def start0Part8 : Input := bytes [109,32,108,105,110,101,97,114,32,116,101,115,116,24,0,0,0,0,0,0,0,1,0,0,0,255,255,255,255,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0]
def start0 : Input := List.flatten [start0Part0,start0Part1,start0Part2,start0Part3,start0Part4,start0Part5,start0Part6,start0Part7,start0Part8]
def stream0Part0 : Input := bytes [80,100,99,222,78,185,204,182,239,202,53,26,69,225,188,203]
def stream0 : Input := List.flatten [stream0Part0]
def start1Part0 : Input := bytes [72,97,115,116,101,66,111,111,116,115,32,99,111,110,115,117,109,101,100,32,102,105,101,108,100,32,98,121,116,101,115,32,118,49,80,100,99,222,78,185,204,182,239,202,53,26,69,225,188,203]
def start1 : Input := List.flatten [start1Part0]
def stream1Part0 : Input := bytes [127,47,247,170,202,4,217,102,81,197,178,114,33,94,153,226,198,71,126,45,249,45,142,223,132,173,46,8,80,141,109,233,25,194,75,251,158,248,173,31,46,42,97,109,32,137,250,9,39,139,141,0,58,208,240,178,147,205,4,133,86,235,223,225]
def stream1 : Input := List.flatten [stream1Part0]
def start2Part0 : Input := bytes [0,8,0,0,0,0,0,0,0,112,114,111,116,111,99,111,108,29,0,0,0,0,0,0,0,72,97,115,116,101,66,111,111,116,115,32,102,114,97,109,101,100,32,83,72,65,75,69,50,53,54,32,118,49,0,11,0,0,0,0,0,0,0,97,112,112,108,105,99,97,116,105,111,110,35,0,0,0,0,0,0,0,72,97,115,116,101,66,111,111,116,115,32,116,121,112,101,100,32,99,108,97,115,115,105,99,97,108,32,112,114,105]
def start2Part1 : Input := bytes [109,101,32,118,49,0,15,0,0,0,0,0,0,0,116,114,117,115,116,101,100,32,112,114,111,102,105,108,101,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,17,0,0,0,0,0,0,0,116,121]
def start2Part2 : Input := bytes [112,101,100,32,112,114,105,109,101,32,102,105,101,108,100,16,0,0,0,0,0,0,0,1,0,0,0,255,255,255,255,0,0,0,0,0,0,0,0,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,23,0,0,0,0,0,0,0,97,116,111,109,105,99,32,78,84,84,32,114,111,119,32,112,104,97,115,101,32,118,50,1,28,0,0,0]
def start2Part3 : Input := bytes [0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,27,0,0,0,0,0,0,0,97,116,111,109,105,99,32,106,111,105,110,116,32,112,114,111,106,101,99,116,105,111,110,115,32,118,51,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,26,0,0,0,0,0,0,0]
def start2Part4 : Input := bytes [97,116,111,109,105,99,32,112,97,99,107,101,100,32,122,101,114,111,99,104,101,99,107,32,118,52,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,27,0,0,0,0,0,0,0,97,116,111,109,105,99,32,66,114,97,107,101,100,111,119,110,32,99,111,108,117,109,110,115,32,118,53,1,22,0,0,0,0,0,0,0,109,119,32,98,97]
def start2Part5 : Input := bytes [116,99,104,101,100,32,114,111,119,45,99,111,100,101,32,118,49,198,0,0,0,0,0,0,0,215,128,227,180,182,92,110,247,243,98,252,99,110,173,56,166,213,97,87,21,39,25,189,12,37,154,74,86,139,106,153,34,56,167,152,87,55,65,245,153,16,101,7,158,173,37,22,201,109,38,36,240,113,210,96,96,210,7,228,46,159,176,73,75,236,255,121,148,40,92,99,241,64,131,187,250,61,215,77,252,205,24,186,73,136,206,154]
def start2Part6 : Input := bytes [126,126,206,87,101,210,171,159,114,65,145,231,96,151,110,42,225,28,79,6,117,197,155,189,109,217,11,238,118,214,241,171,107,34,128,73,40,11,4,235,250,4,2,1,1,0,1,1,1,1,1,1,1,1,0,2,1,1,0,1,1,1,1,1,2,1,1,3,2,1,1,1,1,1,0,1,1,0,1,1,1,2,1,1,253,1,0,0,0,255,255,255,255,1,1,1,1,1,1,1,1,0,4,1,1,1,11,1,2,1,1,1]
def start2Part7 : Input := bytes [18,0,0,0,0,0,0,0,116,121,112,101,100,32,114,101,113,117,101,115,116,32,107,105,110,100,6,0,0,0,0,0,0,0,118,101,99,116,111,114,1,20,0,0,0,0,0,0,0,102,105,101,108,100,32,99,104,97,108,108,101,110,103,101,32,107,105,110,100,12,0,0,0,0,0,0,0,112,114,105,109,101,32,118,101,99,116,111,114,4,27,0,0,0,0,0,0,0,109,119,32,98,97,116,99,104,32,114,97,110,100,111]
def start2Part8 : Input := bytes [109,32,108,105,110,101,97,114,32,116,101,115,116,24,0,0,0,0,0,0,0,1,0,0,0,255,255,255,255,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,5,27,0,0,0,0,0,0,0,109,119,32,98,97,116,99,104,32,114,97,110,100,111,109,32,108,105,110,101,97,114,32,116,101,115,116,80,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,127,47,247,170,202,4,217]
def start2Part9 : Input := bytes [102,81,197,178,114,33,94,153,226,198,71,126,45,249,45,142,223,132,173,46,8,80,141,109,233,25,194,75,251,158,248,173,31,46,42,97,109,32,137,250,9,39,139,141,0,58,208,240,178,147,205,4,133,86,235,223,225,1,25,0,0,0,0,0,0,0,109,119,32,98,97,116,99,104,32,108,105,110,101,97,114,32,114,101,115,112,111,110,115,101,115,26,0,0,0,0,0,0,0,2,253,239,202,53,26,69,225,188,203,253,106,41]
def start2Part10 : Input := bytes [104,11,112,22,208,208,2,2,1,3,2,0,2,1,12,0,0,0,0,0,0,0,105,110,100,101,120,32,100,111,109,97,105,110,8,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,2,25,0,0,0,0,0,0,0,109,119,32,97,116,111,109,105,99,32,99,111,108,117,109,110,32,98,108,111,99,107,32,118,53,8,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]
def start2 : Input := List.flatten [start2Part0,start2Part1,start2Part2,start2Part3,start2Part4,start2Part5,start2Part6,start2Part7,start2Part8,start2Part9,start2Part10]
def stream2Part0 : Input := bytes [220,10,192,192,186,116,50,236]
def stream2 : Input := List.flatten [stream2Part0]

def parent := NativePcsClaimSmoke.parent
def world : World
  | .inl (input,offset) => if input = start0 then stream0[offset]?.getD 255 else
      if input = start1 then stream1[offset]?.getD 255 else if input = start2 then stream2[offset]?.getD 255 else 255
  | .inr pair => HasteBootsSourceGroupsSmoke.batchWorld (.inr pair)
def opening := (NativeGoldBatchOpening.codec.read nativeOpening).map Prod.fst
def prefixRun (fuel : ℕ) := opening.map (fun proof =>
  (run (NativeGoldBatchColumns.protocol NativeGoldBlockCode.description batchParameters parent nativeRoot queries values proof fuel) world).run)
def tag : NativeGoldBatchColumns.Outcome → ℕ
  | .columns _ _ _ _ _ => 1
  | .suspended _ _ _ => 2
  | .rejected _ _ => 3
  | .atomicUnavailable _ => 4

def expected : List Observation := [.hash nativeContextInput nativeContextDigest,
  .start start0,.output start0 0 (stream0.take 8),.output start0 8 (stream0.drop 8),
  .start start1,.output start1 0 stream1,.start start2,.output start2 0 stream2]
example : opening.isSome = true := by decide +kernel
example : (NativeGoldBatchOpening.codec.read nativeOpening).map (fun packet => packet.2.length) = some 0 := by decide +kernel
example : opening.map NativeGoldBatchOpening.codec.encode = some nativeOpening := by decide +kernel
example : (prefixRun 2).map (fun result => tag result.1) = some 1 := by decide +kernel
example : (prefixRun 2).map Prod.snd = some expected := by decide +kernel
example : (prefixRun 2).map (fun result => match result.1 with
  | .columns geometry binding _ weights sample => (geometry.rows,binding.queries.val.length,weights.map (List.map Fin.val),sample.draws,sample.indices)
  | _ => (0,0,[],[],[])) = some (2,4,[[0,1],[1,0]],[28],[28]) := by decide +kernel
example : (prefixRun 1).map (fun result => tag result.1) = some 2 := by decide +kernel
example : (prefixRun 1).map Prod.snd = some (expected.take 3) := by decide +kernel
example : (prefixRun 0).map (fun result => tag result.1) = some 2 := by decide +kernel
-- Native bind_many runs before proof-shape rejection and retains its mutated parent.
def malformed := opening.map (fun proof => {proof with evaluations := ⟨[],by decide⟩})
def malformedRun := malformed.map (fun proof =>
  (run (NativeGoldBatchPrelude.protocol NativeGoldBlockCode.description batchParameters parent nativeRoot queries values proof 2) world).run)
example : malformedRun.map (fun result => match result.1 with
  | .rejected .proofShape bound => decide (bound.input = nativePrefix)
  | _ => false) = some true := by decide +kernel
example : malformedRun.map Prod.snd = some [Observation.hash nativeContextInput nativeContextDigest] := by decide +kernel
-- Invalid binding dimensions stop before context hashing, even with a malformed proof.
def invalidBinding := malformed.map (fun proof =>
  (run (NativeGoldBatchPrelude.protocol NativeGoldBlockCode.description batchParameters parent nativeRoot queries ⟨[],by decide⟩ proof 2) world).run)
example : invalidBinding.map (fun result => match result.1 with | .rejected .binding _ => true | _ => false) = some true := by decide +kernel
example : invalidBinding.map Prod.snd = some [] := by decide +kernel
end
end HasteBootsBatchPrefixSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchOpening.check_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchOpening.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchOpening.encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchOpening.encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchOpening.read_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchOpening.read_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchOpening.bindResponses_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchOpening.bindResponses_input

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.run_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.run_protocol

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.sampling_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.sampling_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.sampling_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.sampling_log

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.finished_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.finished_values

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.proofShape_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude.proofShape_rejected

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.collect_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.collect_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.structured_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.structured_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.structured_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.structured_group

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.run_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.run_protocol

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.run_afterField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.run_afterField

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.suspended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.suspended

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.columns_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.columns_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.columns_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.columns_log

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.columns_draws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchColumns.columns_draws
