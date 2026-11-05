module
import all Mathlib.Data.List.Sort
import all FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability
import all FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks
import all FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape
import all FormalProof4FHE.HasteBoots.NativeIndexRequest
import all FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers

import all FormalProof4FHE.HasteBoots.NativeCheckpointProgram
import all FormalProof4FHE.HasteBoots.NativeGoldPcsExecutionAgrees
import all FormalProof4FHE.HasteBoots.HashWorkerPool
import all FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness
import all Init.Data.String.Defs
import all FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude
import all FormalProof4FHE.HasteBoots.NativeGoldPcsColumns
import all FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding
import all FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers
import all FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.OracleProgram
import all Batteries.Data.Except

open FormalProof4FHE.HasteBoots

/-! Native schedule-5 single-open fixtures at dff353006322693cab3dc6b654f82151f658f294.
The native verifier accepts CANONICAL and rejects ZERO_BAD only at its final
claim comparison. This single-worker harness checks the same raw observations;
it is a regression fixture, not the production interleaved pool or a refinement proof. -/
namespace NativePcsClaimSmoke
private noncomputable def byte (n : ℕ) : InputIndexedOracle.Byte := ⟨n % 256,Nat.mod_lt _ (by decide)⟩
private noncomputable def usize (n : ℕ) : NativeUsizeMessage.Usize := ⟨n % (2^64),Nat.mod_lt _ (by decide)⟩
private noncomputable def row (values : List ℕ) (fits : values.length < 2^64) : NativeLookupRequestWire.Row :=
  ⟨values.map usize,by rw [List.length_map]; exact fits⟩
private noncomputable def initial := NativeTranscript.appendBytes (NativeTranscript.new (NativeTranscript.utf8 "HasteBoots typed classical prime v1") (fun _ => 0))
  (NativeTranscript.utf8 "typed prime field") (TranscriptFrame.littleEndian 16 NativeFields.goldilocksModulus)
private noncomputable def parent := (["atomic NTT row phase v2","atomic joint projections v3","atomic packed zerocheck v4","atomic Brakedown columns v5"] : List String).foldl
  (fun state schedule => NativeTranscript.appendBytes state (NativeTranscript.utf8 "classical challenge schedule") (NativeTranscript.utf8 schedule)) initial
private noncomputable def blockPlanRoot : NativeGoldSolinas.Word := ⟨549755813888,by decide⟩
private noncomputable def blockTables : NativeGoldBlockCode.Tables :=
  ⟨fun log => decide (log=5),fun _ => true,fun log => if log=5 then some blockPlanRoot else none⟩
private noncomputable def retainedCode : NativeGoldBlockCode.Stored :=
  ⟨usize 2,usize 2,usize 1,usize 32,NativeBrakedownContext.modulus,usize 549755813888⟩
private noncomputable def retainedParameters : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored :=
  ⟨usize 2,usize 3,usize 1,usize 1,retainedCode⟩

-- Test interpretation of the actual production program. The canonical shared
-- cache is covered by the support theorems; this interpreter compares every
-- issued hash against the unchanged native fixture world.
private noncomputable def executionHandler (actual : InputIndexedOracle.World) :
    QueryImpl (CheckpointExecution.Spec unifSpec Unit InputIndexedOracle.Input NativeRootMessage.Digest)
      NativeTranscript.Execution := fun request => match request with
  | .inl size => pure ⟨0,by omega⟩
  | .inr (.inl input) => ObservationReplay.hash actual input
  | .inr (.inr _) => pure ()
private noncomputable def chooseWorker (cancel : Bool) (work : NativeGoldPcsWorkers.Prepared)
    (_ : HashWorkerPool.Workers InputIndexedOracle.Input NativeRootMessage.Digest work.jobs.length) (_ : Unit) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit InputIndexedOracle.Input NativeRootMessage.Digest)
      (Option (Fin work.jobs.length) × Unit) :=
  pure (if cancel then none else if positive : 0 < work.jobs.length then some ⟨0,positive⟩ else none,())
private noncomputable def executionTag : NativeGoldPcsExecution.Outcome Unit → Nat
  | .prefix _ _ => 0
  | .completed _ _ completion => match completion.status with
    | .accepted _ => 1
    | .columns => 2
    | .claim .claim => 3
    | .suspended => 4
    | .claim .finish => 5

namespace Canonical
private noncomputable def nativeRootPart0 : List ℕ := [222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201]
private noncomputable def nativeRoot : InputIndexedOracle.Input := (nativeRootPart0).map byte
private noncomputable def nativeQueryPart0 : List ℕ := [2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255]
private noncomputable def nativeQueryPart1 : List ℕ := [255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7]
private noncomputable def nativeQuery : InputIndexedOracle.Input := (nativeQueryPart0 ++ nativeQueryPart1).map byte
private noncomputable def nativeOpeningPart0 : List ℕ := [6, 253, 156, 80, 32, 65, 156, 75, 240, 203, 253, 175, 247, 224, 160, 245, 96, 83, 171, 253, 11, 184, 151, 155, 95, 8, 132, 142, 253, 37, 54, 72, 137, 0, 40, 45, 69, 253, 17, 117, 27, 111, 63, 243, 169, 101, 253, 96, 55, 51, 183, 141, 153, 233, 166, 6, 253, 175, 0, 0, 0, 255, 255, 255, 255, 253, 181, 0, 0, 0, 255, 255, 255, 255, 253, 122, 0, 0, 0, 255, 255, 255, 255, 253, 128, 0, 0, 0, 255, 255, 255, 255, 253, 33, 0, 0, 0, 255, 255, 255, 255, 253, 39, 0, 0, 0, 255, 255, 255, 255, 1, 12, 0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11, 6, 173, 84, 12]
private noncomputable def nativeOpeningPart1 : List ℕ := [187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2, 173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2, 76, 217, 186]
private noncomputable def nativeOpeningPart2 : List ℕ := [226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179, 177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42, 134, 66, 93]
private noncomputable def nativeOpeningPart3 : List ℕ := [124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84, 28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166]
private noncomputable def nativeOpening : InputIndexedOracle.Input := (nativeOpeningPart0 ++ nativeOpeningPart1 ++ nativeOpeningPart2 ++ nativeOpeningPart3).map byte
private noncomputable def start0Part0 : List ℕ := [0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114]
private noncomputable def start0Part1 : List ℕ := [117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0]
private noncomputable def start0Part2 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 23, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 78, 84, 84, 32, 114, 111, 119, 32, 112, 104, 97, 115, 101, 32, 118, 50, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 106]
private noncomputable def start0Part3 : List ℕ := [111, 105, 110, 116, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 32, 118, 51, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 26, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 112, 97, 99, 107, 101, 100, 32, 122, 101, 114, 111, 99, 104, 101, 99, 107, 32, 118, 52, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27]
private noncomputable def start0Part4 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 66, 114, 97, 107, 101, 100, 111, 119, 110, 32, 99, 111, 108, 117, 109, 110, 115, 32, 118, 53, 1, 24, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 98, 114, 97, 107, 101, 100, 111, 119, 110, 32, 114, 111, 119, 45, 99, 111, 100, 101, 32, 118, 50, 64, 0, 0, 0, 0, 0, 0, 0, 168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25]
private noncomputable def start0Part5 : List ℕ := [39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145, 1, 23, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 32, 97, 110, 100, 32, 113, 117, 101, 114, 121, 5, 1, 0, 0, 0, 0, 0, 0, 222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201, 2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253]
private noncomputable def start0Part6 : List ℕ := [222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255]
private noncomputable def start0Part7 : List ℕ := [255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7, 3, 251, 200, 4, 251, 7, 3, 218, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0]
private noncomputable def start0Part8 : List ℕ := [0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0]
private noncomputable def start0 : InputIndexedOracle.Input := (start0Part0 ++ start0Part1 ++ start0Part2 ++ start0Part3 ++ start0Part4 ++ start0Part5 ++ start0Part6 ++ start0Part7 ++ start0Part8).map byte
private noncomputable def start1Part0 : List ℕ := [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 99, 111, 110, 115, 117, 109, 101, 100, 32, 102, 105, 101, 108, 100, 32, 98, 121, 116, 101, 115, 32, 118, 49, 72, 174, 236, 126, 59, 197, 218, 75, 200, 66, 60, 6, 104, 141, 92, 93, 40, 137, 220, 139, 230, 194, 37, 37, 47, 219, 73, 20, 207, 123, 253, 49, 155, 203, 155, 89, 184, 160, 104, 127, 131, 165, 95, 230, 208, 166, 34, 80, 249, 59, 115, 8, 55, 16, 161, 3, 132, 182, 200, 188, 187, 52, 166, 230, 30, 11, 112, 211, 106, 25, 22, 27, 140, 188, 242, 241, 202, 9, 36, 47, 177, 16, 56, 4, 30, 14, 107, 45, 46, 74, 113, 67, 253, 14]
private noncomputable def start1Part1 : List ℕ := [133, 60, 97, 169, 195, 27, 105, 220, 47, 177, 140, 183, 18, 0, 81, 52, 192, 35, 143, 240, 247, 57, 58, 80, 213, 25, 169, 35, 169, 50, 121, 194, 221, 139, 120, 17, 161, 174, 94, 130, 223, 59, 29, 111, 235, 84, 233, 245, 7, 127]
private noncomputable def start1 : InputIndexedOracle.Input := (start1Part0 ++ start1Part1).map byte
private noncomputable def start2Part0 : List ℕ := [0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114]
private noncomputable def start2Part1 : List ℕ := [117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0]
private noncomputable def start2Part2 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 23, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 78, 84, 84, 32, 114, 111, 119, 32, 112, 104, 97, 115, 101, 32, 118, 50, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 106]
private noncomputable def start2Part3 : List ℕ := [111, 105, 110, 116, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 32, 118, 51, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 26, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 112, 97, 99, 107, 101, 100, 32, 122, 101, 114, 111, 99, 104, 101, 99, 107, 32, 118, 52, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27]
private noncomputable def start2Part4 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 66, 114, 97, 107, 101, 100, 111, 119, 110, 32, 99, 111, 108, 117, 109, 110, 115, 32, 118, 53, 1, 24, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 98, 114, 97, 107, 101, 100, 111, 119, 110, 32, 114, 111, 119, 45, 99, 111, 100, 101, 32, 118, 50, 64, 0, 0, 0, 0, 0, 0, 0, 168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25]
private noncomputable def start2Part5 : List ℕ := [39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145, 1, 23, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 32, 97, 110, 100, 32, 113, 117, 101, 114, 121, 5, 1, 0, 0, 0, 0, 0, 0, 222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201, 2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253]
private noncomputable def start2Part6 : List ℕ := [222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255]
private noncomputable def start2Part7 : List ℕ := [255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7, 3, 251, 200, 4, 251, 7, 3, 218, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0]
private noncomputable def start2Part8 : List ℕ := [0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 5, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 80, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private noncomputable def start2Part9 : List ℕ := [0, 0, 0, 0, 0, 0, 237, 145, 6, 216, 74, 225, 211, 101, 9, 35, 93, 244, 195, 247, 90, 123, 137, 39, 145, 128, 172, 30, 85, 101, 199, 74, 1, 193, 3, 186, 98, 173, 89, 120, 182, 220, 140, 243, 105, 109, 202, 134, 82, 91, 135, 29, 64, 82, 192, 253, 251, 214, 118, 134, 168, 242, 249, 220, 36, 155, 220, 159, 57, 83, 1, 19, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 108, 105, 110, 101, 97, 114, 32, 114, 101, 115, 112, 111, 110, 115, 101, 115, 110, 0, 0, 0, 0, 0, 0, 0, 6, 253, 156, 80, 32, 65, 156, 75, 240, 203, 253, 175, 247, 224, 160, 245, 96, 83, 171, 253, 11, 184]
private noncomputable def start2Part10 : List ℕ := [151, 155, 95, 8, 132, 142, 253, 37, 54, 72, 137, 0, 40, 45, 69, 253, 17, 117, 27, 111, 63, 243, 169, 101, 253, 96, 55, 51, 183, 141, 153, 233, 166, 6, 253, 175, 0, 0, 0, 255, 255, 255, 255, 253, 181, 0, 0, 0, 255, 255, 255, 255, 253, 122, 0, 0, 0, 255, 255, 255, 255, 253, 128, 0, 0, 0, 255, 255, 255, 255, 253, 33, 0, 0, 0, 255, 255, 255, 255, 253, 39, 0, 0, 0, 255, 255, 255, 255, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0]
private noncomputable def start2Part11 : List ℕ := [0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]
private noncomputable def start2 : InputIndexedOracle.Input := (start2Part0 ++ start2Part1 ++ start2Part2 ++ start2Part3 ++ start2Part4 ++ start2Part5 ++ start2Part6 ++ start2Part7 ++ start2Part8 ++ start2Part9 ++ start2Part10 ++ start2Part11).map byte
private noncomputable def stream0Part0 : List ℕ := [72, 174, 236, 126, 59, 197, 218, 75, 200, 66, 60, 6, 104, 141, 92, 93, 40, 137, 220, 139, 230, 194, 37, 37, 47, 219, 73, 20, 207, 123, 253, 49, 155, 203, 155, 89, 184, 160, 104, 127, 131, 165, 95, 230, 208, 166, 34, 80, 249, 59, 115, 8, 55, 16, 161, 3, 132, 182, 200, 188, 187, 52, 166, 230, 30, 11, 112, 211, 106, 25, 22, 27, 140, 188, 242, 241, 202, 9, 36, 47, 177, 16, 56, 4, 30, 14, 107, 45, 46, 74, 113, 67, 253, 14, 133, 60, 97, 169, 195, 27, 105, 220, 47, 177, 140, 183, 18, 0, 81, 52, 192, 35, 143, 240, 247, 57, 58, 80, 213, 25, 169, 35, 169, 50, 121, 194, 221, 139]
private noncomputable def stream0Part1 : List ℕ := [120, 17, 161, 174, 94, 130, 223, 59, 29, 111, 235, 84, 233, 245, 7, 127]
private noncomputable def stream0 : InputIndexedOracle.Input := (stream0Part0 ++ stream0Part1).map byte
private noncomputable def stream1Part0 : List ℕ := [237, 145, 6, 216, 74, 225, 211, 101, 9, 35, 93, 244, 195, 247, 90, 123, 137, 39, 145, 128, 172, 30, 85, 101, 199, 74, 1, 193, 3, 186, 98, 173, 89, 120, 182, 220, 140, 243, 105, 109, 202, 134, 82, 91, 135, 29, 64, 82, 192, 253, 251, 214, 118, 134, 168, 242, 249, 220, 36, 155, 220, 159, 57, 83]
private noncomputable def stream1 : InputIndexedOracle.Input := (stream1Part0).map byte
private noncomputable def stream2Part0 : List ℕ := [127, 17, 231, 56, 82, 199, 13, 194]
private noncomputable def stream2 : InputIndexedOracle.Input := (stream2Part0).map byte
private noncomputable def hashInput0Part0 : List ℕ := [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 47, 118, 50, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 2, 3, 1, 1, 2, 32, 26, 98, 108, 111, 99, 107, 45, 114, 115, 47, 110, 101, 103, 97, 99, 121, 99, 108, 105, 99, 45, 110, 116, 116, 47, 118, 49, 2, 2, 1, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0]
private noncomputable def hashInput0 : InputIndexedOracle.Input := (hashInput0Part0).map byte
private noncomputable def hashOutput0Part0 : List ℕ := [168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25, 39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145]
private noncomputable def hashOutput0 : InputIndexedOracle.Input := (hashOutput0Part0).map byte
private noncomputable def hashInput1Part0 : List ℕ := [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 99, 111, 108, 117, 109, 110, 47, 118, 49, 12, 0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11]
private noncomputable def hashInput1 : InputIndexedOracle.Input := (hashInput1Part0).map byte
private noncomputable def hashOutput1Part0 : List ℕ := [173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2]
private noncomputable def hashOutput1 : InputIndexedOracle.Input := (hashOutput1Part0).map byte
private noncomputable def hashInput2Part0 : List ℕ := [173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2, 173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2]
private noncomputable def hashInput2 : InputIndexedOracle.Input := (hashInput2Part0).map byte
private noncomputable def hashOutput2Part0 : List ℕ := [76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179]
private noncomputable def hashOutput2 : InputIndexedOracle.Input := (hashOutput2Part0).map byte
private noncomputable def hashInput3Part0 : List ℕ := [76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179, 76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179]
private noncomputable def hashInput3 : InputIndexedOracle.Input := (hashInput3Part0).map byte
private noncomputable def hashOutput3Part0 : List ℕ := [177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42]
private noncomputable def hashOutput3 : InputIndexedOracle.Input := (hashOutput3Part0).map byte
private noncomputable def hashInput4Part0 : List ℕ := [177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42, 177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42]
private noncomputable def hashInput4 : InputIndexedOracle.Input := (hashInput4Part0).map byte
private noncomputable def hashOutput4Part0 : List ℕ := [134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84]
private noncomputable def hashOutput4 : InputIndexedOracle.Input := (hashOutput4Part0).map byte
private noncomputable def hashInput5Part0 : List ℕ := [134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84, 134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84]
private noncomputable def hashInput5 : InputIndexedOracle.Input := (hashInput5Part0).map byte
private noncomputable def hashOutput5Part0 : List ℕ := [28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166]
private noncomputable def hashOutput5 : InputIndexedOracle.Input := (hashOutput5Part0).map byte
private noncomputable def hashInput6Part0 : List ℕ := [28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166, 28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166]
private noncomputable def hashInput6 : InputIndexedOracle.Input := (hashInput6Part0).map byte
private noncomputable def hashOutput6Part0 : List ℕ := [222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201]
private noncomputable def hashOutput6 : InputIndexedOracle.Input := (hashOutput6Part0).map byte
private noncomputable def hashPairs : List (InputIndexedOracle.Input × InputIndexedOracle.Input) := [(hashInput0,hashOutput0),(hashInput1,hashOutput1),(hashInput2,hashOutput2),(hashInput3,hashOutput3),(hashInput4,hashOutput4),(hashInput5,hashOutput5),(hashInput6,hashOutput6)]
private noncomputable def world : InputIndexedOracle.World
  | .inr (input,index) => match hashPairs.find? (fun pair => pair.1=input) with
    | none => byte 255
    | some pair => pair.2[index.val]?.getD (byte 255)
  | .inl (input,offset) => match ([(start0,stream0),(start1,stream1),(start2,stream2)] :
      List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1=input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def root : NativeRootMessage.Digest := fun index => nativeRoot[index.val]?.getD (byte 255)
private noncomputable def query := (NativeGoldPcsWire.queryCodec.read nativeQuery).map Prod.fst
private noncomputable def opening := (NativeGoldPcsOpening.codec.read nativeOpening).map Prod.fst
private noncomputable def claimed := row [1224, 775, 218] (by decide)
-- Decode the original native bytes and run the actual prefix and raw worker.
private noncomputable def handoff : OracleProgram.Program Nat :=
  match query,opening with
  | some q,some proof => OracleProgram.bind
    (NativeGoldPcsWorkers.protocol blockTables retainedParameters parent root q claimed proof 18)
    (fun result => match result with
      | .prepared work => match work.jobs with
        | [job] => OracleProgram.bind
          (NativeHashOracleBridge.compile (NativeGoldColumnWorker.worker work.geometry work.width work.random
            work.structured work.test work.evaluation work.root job.index job.column))
          (fun passed => .pure (match NativeGoldPcsAcceptance.finish retainedParameters q proof claimed work
              (⟨fun _ => pure passed,()⟩ : HashWorkerPool.Outcome InputIndexedOracle.Input NativeRootMessage.Digest Unit work.jobs.length) with
            | .accepted _ => 1
            | .columns => 2
            | .claim .claim => 3
            | _ => 0))
        | _ => .pure 0
      | _ => .pure 0)
  | _,_ => .pure 0
private noncomputable def result : Nat × List NativeTranscript.Observation := (OracleProgram.run handoff world).run
example : result.1 = 1 := by decide +kernel
private noncomputable def expected : List NativeTranscript.Observation :=
  [.hash hashInput0 hashOutput0,.start start0] ++
  (List.range 18).map (fun index => .output start0 (index*8) ((stream0.drop (index*8)).take 8)) ++
  [.start start1,.output start1 0 stream1,.start start2,.output start2 0 stream2] ++
  [.hash hashInput1 hashOutput1,.hash hashInput2 hashOutput2,.hash hashInput3 hashOutput3,.hash hashInput4 hashOutput4,.hash hashInput5 hashOutput5,.hash hashInput6 hashOutput6]
example : result.2 = expected := by decide +kernel

-- Full production prefix/pool/claim program, including computed residuals.
private noncomputable def fullRun (fuel : ℕ) (cancel : Bool) :
    NativeGoldPcsExecution.Outcome Unit × List NativeTranscript.Observation :=
  match query,opening with
  | some q,some proof =>
    (simulateQ (executionHandler world) (NativeGoldPcsExecution.program
      ⟨blockTables,retainedParameters,parent,root,q,claimed,proof,18⟩
      (InputIndexedOracle.shake world) (chooseWorker cancel) fuel ())).run
  | _,_ => (.prefix .pairingUnavailable [],[])
example : executionTag (fullRun 6 false).1 = 1 := by decide +kernel
example : (fullRun 6 false).2 = hashPairs.map (fun pair => .hash pair.1 pair.2) := by decide +kernel
example : (match (fullRun 6 false).1 with
  | .completed _ observations _ => some observations | _ => none) = some (expected.take 24) := by decide +kernel
example : executionTag (fullRun 5 false).1 = 4 := by decide +kernel
example : (fullRun 5 false).2 = (hashPairs.take 6).map (fun pair => .hash pair.1 pair.2) := by decide +kernel
example : executionTag (fullRun 6 true).1 = 4 := by decide +kernel
example : (fullRun 6 true).2 = [.hash hashInput0 hashOutput0] := by decide +kernel
end Canonical

namespace ZeroBad
private noncomputable def nativeRootPart0 : List ℕ := [128, 159, 78, 167, 37, 0, 249, 58, 247, 55, 197, 246, 10, 140, 8, 180, 126, 62, 5, 162, 183, 44, 246, 37, 85, 88, 167, 253, 25, 75, 171, 196, 213, 7, 207, 63, 66, 20, 82, 21, 155, 235, 74, 33, 161, 244, 239, 93, 179, 186, 128, 172, 179, 27, 97, 119, 1, 61, 105, 252, 214, 80, 207, 233]
private noncomputable def nativeRoot : InputIndexedOracle.Input := (nativeRootPart0).map byte
private noncomputable def nativeQueryPart0 : List ℕ := [2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255]
private noncomputable def nativeQueryPart1 : List ℕ := [255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7]
private noncomputable def nativeQuery : InputIndexedOracle.Input := (nativeQueryPart0 ++ nativeQueryPart1).map byte
private noncomputable def nativeOpeningPart0 : List ℕ := [6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 179, 61, 181, 43, 182, 65, 237, 45, 72, 195, 104, 253, 223, 147, 94, 26, 91, 132, 97, 214, 65, 94, 155, 194, 37, 121, 53, 147, 107, 168, 241, 154, 252, 174, 235, 201, 41, 169, 180, 117, 244, 61, 100, 119, 242, 203, 187, 74, 219, 173, 130, 30, 118, 88, 163, 182, 245, 41, 154, 151, 85, 251, 140, 233, 179, 61, 181, 43, 182, 65, 237, 45, 72, 195, 104, 253, 223, 147, 94, 26, 91, 132, 97, 214, 65, 94, 155, 194, 37, 121, 53, 147, 107, 168, 241, 154, 252, 174, 235]
private noncomputable def nativeOpeningPart1 : List ℕ := [201, 41, 169, 180, 117, 244, 61, 100, 119, 242, 203, 187, 74, 219, 173, 130, 30, 118, 88, 163, 182, 245, 41, 154, 151, 85, 251, 140, 233, 12, 207, 191, 125, 34, 189, 58, 109, 187, 4, 46, 47, 29, 131, 25, 54, 56, 76, 173, 42, 208, 149, 2, 37, 139, 199, 86, 225, 154, 251, 174, 31, 243, 82, 146, 120, 205, 135, 234, 206, 15, 254, 158, 146, 130, 92, 208, 68, 79, 47, 119, 68, 42, 34, 227, 149, 255, 69, 181, 193, 176, 192, 195, 82, 150, 185, 152, 250, 129, 108, 45, 84, 35, 203, 167, 233, 93, 4, 27, 242, 94, 153, 247, 70, 12, 141, 66, 135, 198, 239, 17, 33, 19, 68, 37, 79, 139, 55, 71]
private noncomputable def nativeOpeningPart2 : List ℕ := [182, 135, 229, 79, 217, 5, 192, 80, 178, 76, 180, 90, 162, 135, 57, 109, 63, 235, 196, 117, 37, 69, 122, 12, 78, 218, 148, 132, 197, 31, 139, 15, 167, 140, 100, 3, 107, 39, 244, 237, 190, 49, 157, 105, 102, 173, 176, 23, 157, 41, 236, 122, 230, 176, 120, 213, 59, 239, 62, 143, 8, 179, 96, 241, 219, 161, 243, 80, 189, 9, 95, 32, 103, 210, 127, 229, 24, 56, 36, 9, 239, 238, 10, 141, 185, 195, 79, 97, 203, 123, 68, 43, 213, 220, 143, 168, 252, 21, 76, 13, 212, 18, 28, 43, 112, 109, 152, 161, 59, 223, 149, 43, 99, 19, 191, 251, 110, 76, 10, 135, 196, 142, 174, 68, 211, 223, 83, 49]
private noncomputable def nativeOpeningPart3 : List ℕ := [31, 224, 15, 177, 28, 175, 199, 67, 5, 28, 132, 61, 144, 224, 105, 238, 57, 90, 28, 65, 255, 165, 129, 75, 157, 149, 163, 107, 158]
private noncomputable def nativeOpening : InputIndexedOracle.Input := (nativeOpeningPart0 ++ nativeOpeningPart1 ++ nativeOpeningPart2 ++ nativeOpeningPart3).map byte
private noncomputable def start0Part0 : List ℕ := [0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114]
private noncomputable def start0Part1 : List ℕ := [117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0]
private noncomputable def start0Part2 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 23, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 78, 84, 84, 32, 114, 111, 119, 32, 112, 104, 97, 115, 101, 32, 118, 50, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 106]
private noncomputable def start0Part3 : List ℕ := [111, 105, 110, 116, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 32, 118, 51, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 26, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 112, 97, 99, 107, 101, 100, 32, 122, 101, 114, 111, 99, 104, 101, 99, 107, 32, 118, 52, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27]
private noncomputable def start0Part4 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 66, 114, 97, 107, 101, 100, 111, 119, 110, 32, 99, 111, 108, 117, 109, 110, 115, 32, 118, 53, 1, 24, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 98, 114, 97, 107, 101, 100, 111, 119, 110, 32, 114, 111, 119, 45, 99, 111, 100, 101, 32, 118, 50, 64, 0, 0, 0, 0, 0, 0, 0, 168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25]
private noncomputable def start0Part5 : List ℕ := [39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145, 1, 23, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 32, 97, 110, 100, 32, 113, 117, 101, 114, 121, 1, 1, 0, 0, 0, 0, 0, 0, 128, 159, 78, 167, 37, 0, 249, 58, 247, 55, 197, 246, 10, 140, 8, 180, 126, 62, 5, 162, 183, 44, 246, 37, 85, 88, 167, 253, 25, 75, 171, 196, 213, 7, 207, 63, 66, 20, 82, 21, 155, 235, 74, 33, 161, 244, 239, 93, 179, 186, 128, 172, 179, 27, 97, 119, 1, 61, 105, 252, 214, 80, 207, 233, 2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253]
private noncomputable def start0Part6 : List ℕ := [222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255]
private noncomputable def start0Part7 : List ℕ := [255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7, 3, 1, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0]
private noncomputable def start0Part8 : List ℕ := [0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0]
private noncomputable def start0 : InputIndexedOracle.Input := (start0Part0 ++ start0Part1 ++ start0Part2 ++ start0Part3 ++ start0Part4 ++ start0Part5 ++ start0Part6 ++ start0Part7 ++ start0Part8).map byte
private noncomputable def start1Part0 : List ℕ := [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 99, 111, 110, 115, 117, 109, 101, 100, 32, 102, 105, 101, 108, 100, 32, 98, 121, 116, 101, 115, 32, 118, 49, 241, 111, 147, 79, 61, 255, 121, 79, 59, 108, 9, 250, 242, 130, 20, 157, 140, 237, 230, 136, 61, 227, 152, 10, 167, 117, 38, 30, 226, 84, 150, 106, 164, 153, 199, 238, 75, 200, 238, 1, 218, 31, 141, 227, 151, 71, 61, 233, 23, 218, 99, 4, 67, 21, 96, 150, 185, 232, 19, 196, 51, 42, 33, 64, 63, 97, 74, 39, 239, 126, 72, 119, 178, 104, 13, 94, 152, 135, 253, 241, 33, 214, 6, 169, 209, 135, 224, 154, 17, 62, 176, 232, 164, 162]
private noncomputable def start1Part1 : List ℕ := [60, 251, 233, 223, 27, 165, 145, 138, 167, 42, 167, 232, 161, 188, 176, 148, 13, 107, 112, 7, 93, 223, 125, 156, 9, 230, 141, 71, 193, 11, 94, 42, 200, 201, 64, 221, 227, 123, 34, 32, 208, 92, 222, 145, 144, 142, 204, 188, 98, 221]
private noncomputable def start1 : InputIndexedOracle.Input := (start1Part0 ++ start1Part1).map byte
private noncomputable def start2Part0 : List ℕ := [0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114]
private noncomputable def start2Part1 : List ℕ := [117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0]
private noncomputable def start2Part2 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 23, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 78, 84, 84, 32, 114, 111, 119, 32, 112, 104, 97, 115, 101, 32, 118, 50, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 106]
private noncomputable def start2Part3 : List ℕ := [111, 105, 110, 116, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 32, 118, 51, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 26, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 112, 97, 99, 107, 101, 100, 32, 122, 101, 114, 111, 99, 104, 101, 99, 107, 32, 118, 52, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27]
private noncomputable def start2Part4 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 66, 114, 97, 107, 101, 100, 111, 119, 110, 32, 99, 111, 108, 117, 109, 110, 115, 32, 118, 53, 1, 24, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 98, 114, 97, 107, 101, 100, 111, 119, 110, 32, 114, 111, 119, 45, 99, 111, 100, 101, 32, 118, 50, 64, 0, 0, 0, 0, 0, 0, 0, 168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25]
private noncomputable def start2Part5 : List ℕ := [39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145, 1, 23, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 32, 97, 110, 100, 32, 113, 117, 101, 114, 121, 1, 1, 0, 0, 0, 0, 0, 0, 128, 159, 78, 167, 37, 0, 249, 58, 247, 55, 197, 246, 10, 140, 8, 180, 126, 62, 5, 162, 183, 44, 246, 37, 85, 88, 167, 253, 25, 75, 171, 196, 213, 7, 207, 63, 66, 20, 82, 21, 155, 235, 74, 33, 161, 244, 239, 93, 179, 186, 128, 172, 179, 27, 97, 119, 1, 61, 105, 252, 214, 80, 207, 233, 2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253]
private noncomputable def start2Part6 : List ℕ := [222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255]
private noncomputable def start2Part7 : List ℕ := [255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7, 3, 1, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0]
private noncomputable def start2Part8 : List ℕ := [0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 5, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 80, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private noncomputable def start2Part9 : List ℕ := [0, 0, 227, 138, 134, 109, 42, 81, 137, 86, 200, 244, 226, 164, 7, 194, 6, 180, 182, 148, 79, 155, 130, 141, 54, 71, 92, 90, 24, 200, 70, 175, 244, 32, 104, 35, 73, 37, 147, 173, 239, 228, 117, 201, 125, 24, 208, 255, 97, 29, 5, 215, 125, 195, 139, 75, 134, 13, 230, 57, 195, 151, 69, 103, 51, 162, 1, 19, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 108, 105, 110, 101, 97, 114, 32, 114, 101, 115, 112, 111, 110, 115, 101, 115, 14, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100]
private noncomputable def start2Part10 : List ℕ := [101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]
private noncomputable def start2 : InputIndexedOracle.Input := (start2Part0 ++ start2Part1 ++ start2Part2 ++ start2Part3 ++ start2Part4 ++ start2Part5 ++ start2Part6 ++ start2Part7 ++ start2Part8 ++ start2Part9 ++ start2Part10).map byte
private noncomputable def stream0Part0 : List ℕ := [241, 111, 147, 79, 61, 255, 121, 79, 59, 108, 9, 250, 242, 130, 20, 157, 140, 237, 230, 136, 61, 227, 152, 10, 167, 117, 38, 30, 226, 84, 150, 106, 164, 153, 199, 238, 75, 200, 238, 1, 218, 31, 141, 227, 151, 71, 61, 233, 23, 218, 99, 4, 67, 21, 96, 150, 185, 232, 19, 196, 51, 42, 33, 64, 63, 97, 74, 39, 239, 126, 72, 119, 178, 104, 13, 94, 152, 135, 253, 241, 33, 214, 6, 169, 209, 135, 224, 154, 17, 62, 176, 232, 164, 162, 60, 251, 233, 223, 27, 165, 145, 138, 167, 42, 167, 232, 161, 188, 176, 148, 13, 107, 112, 7, 93, 223, 125, 156, 9, 230, 141, 71, 193, 11, 94, 42, 200, 201]
private noncomputable def stream0Part1 : List ℕ := [64, 221, 227, 123, 34, 32, 208, 92, 222, 145, 144, 142, 204, 188, 98, 221]
private noncomputable def stream0 : InputIndexedOracle.Input := (stream0Part0 ++ stream0Part1).map byte
private noncomputable def stream1Part0 : List ℕ := [227, 138, 134, 109, 42, 81, 137, 86, 200, 244, 226, 164, 7, 194, 6, 180, 182, 148, 79, 155, 130, 141, 54, 71, 92, 90, 24, 200, 70, 175, 244, 32, 104, 35, 73, 37, 147, 173, 239, 228, 117, 201, 125, 24, 208, 255, 97, 29, 5, 215, 125, 195, 139, 75, 134, 13, 230, 57, 195, 151, 69, 103, 51, 162]
private noncomputable def stream1 : InputIndexedOracle.Input := (stream1Part0).map byte
private noncomputable def stream2Part0 : List ℕ := [196, 170, 80, 141, 175, 155, 118, 108]
private noncomputable def stream2 : InputIndexedOracle.Input := (stream2Part0).map byte
private noncomputable def hashInput0Part0 : List ℕ := [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 47, 118, 50, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 2, 3, 1, 1, 2, 32, 26, 98, 108, 111, 99, 107, 45, 114, 115, 47, 110, 101, 103, 97, 99, 121, 99, 108, 105, 99, 45, 110, 116, 116, 47, 118, 49, 2, 2, 1, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0]
private noncomputable def hashInput0 : InputIndexedOracle.Input := (hashInput0Part0).map byte
private noncomputable def hashOutput0Part0 : List ℕ := [168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25, 39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145]
private noncomputable def hashOutput0 : InputIndexedOracle.Input := (hashOutput0Part0).map byte
private noncomputable def hashInput1Part0 : List ℕ := [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 99, 111, 108, 117, 109, 110, 47, 118, 49, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private noncomputable def hashInput1 : InputIndexedOracle.Input := (hashInput1Part0).map byte
private noncomputable def hashOutput1Part0 : List ℕ := [179, 61, 181, 43, 182, 65, 237, 45, 72, 195, 104, 253, 223, 147, 94, 26, 91, 132, 97, 214, 65, 94, 155, 194, 37, 121, 53, 147, 107, 168, 241, 154, 252, 174, 235, 201, 41, 169, 180, 117, 244, 61, 100, 119, 242, 203, 187, 74, 219, 173, 130, 30, 118, 88, 163, 182, 245, 41, 154, 151, 85, 251, 140, 233]
private noncomputable def hashOutput1 : InputIndexedOracle.Input := (hashOutput1Part0).map byte
private noncomputable def hashInput2Part0 : List ℕ := [179, 61, 181, 43, 182, 65, 237, 45, 72, 195, 104, 253, 223, 147, 94, 26, 91, 132, 97, 214, 65, 94, 155, 194, 37, 121, 53, 147, 107, 168, 241, 154, 252, 174, 235, 201, 41, 169, 180, 117, 244, 61, 100, 119, 242, 203, 187, 74, 219, 173, 130, 30, 118, 88, 163, 182, 245, 41, 154, 151, 85, 251, 140, 233, 179, 61, 181, 43, 182, 65, 237, 45, 72, 195, 104, 253, 223, 147, 94, 26, 91, 132, 97, 214, 65, 94, 155, 194, 37, 121, 53, 147, 107, 168, 241, 154, 252, 174, 235, 201, 41, 169, 180, 117, 244, 61, 100, 119, 242, 203, 187, 74, 219, 173, 130, 30, 118, 88, 163, 182, 245, 41, 154, 151, 85, 251, 140, 233]
private noncomputable def hashInput2 : InputIndexedOracle.Input := (hashInput2Part0).map byte
private noncomputable def hashOutput2Part0 : List ℕ := [12, 207, 191, 125, 34, 189, 58, 109, 187, 4, 46, 47, 29, 131, 25, 54, 56, 76, 173, 42, 208, 149, 2, 37, 139, 199, 86, 225, 154, 251, 174, 31, 243, 82, 146, 120, 205, 135, 234, 206, 15, 254, 158, 146, 130, 92, 208, 68, 79, 47, 119, 68, 42, 34, 227, 149, 255, 69, 181, 193, 176, 192, 195, 82]
private noncomputable def hashOutput2 : InputIndexedOracle.Input := (hashOutput2Part0).map byte
private noncomputable def hashInput3Part0 : List ℕ := [12, 207, 191, 125, 34, 189, 58, 109, 187, 4, 46, 47, 29, 131, 25, 54, 56, 76, 173, 42, 208, 149, 2, 37, 139, 199, 86, 225, 154, 251, 174, 31, 243, 82, 146, 120, 205, 135, 234, 206, 15, 254, 158, 146, 130, 92, 208, 68, 79, 47, 119, 68, 42, 34, 227, 149, 255, 69, 181, 193, 176, 192, 195, 82, 12, 207, 191, 125, 34, 189, 58, 109, 187, 4, 46, 47, 29, 131, 25, 54, 56, 76, 173, 42, 208, 149, 2, 37, 139, 199, 86, 225, 154, 251, 174, 31, 243, 82, 146, 120, 205, 135, 234, 206, 15, 254, 158, 146, 130, 92, 208, 68, 79, 47, 119, 68, 42, 34, 227, 149, 255, 69, 181, 193, 176, 192, 195, 82]
private noncomputable def hashInput3 : InputIndexedOracle.Input := (hashInput3Part0).map byte
private noncomputable def hashOutput3Part0 : List ℕ := [150, 185, 152, 250, 129, 108, 45, 84, 35, 203, 167, 233, 93, 4, 27, 242, 94, 153, 247, 70, 12, 141, 66, 135, 198, 239, 17, 33, 19, 68, 37, 79, 139, 55, 71, 182, 135, 229, 79, 217, 5, 192, 80, 178, 76, 180, 90, 162, 135, 57, 109, 63, 235, 196, 117, 37, 69, 122, 12, 78, 218, 148, 132, 197]
private noncomputable def hashOutput3 : InputIndexedOracle.Input := (hashOutput3Part0).map byte
private noncomputable def hashInput4Part0 : List ℕ := [150, 185, 152, 250, 129, 108, 45, 84, 35, 203, 167, 233, 93, 4, 27, 242, 94, 153, 247, 70, 12, 141, 66, 135, 198, 239, 17, 33, 19, 68, 37, 79, 139, 55, 71, 182, 135, 229, 79, 217, 5, 192, 80, 178, 76, 180, 90, 162, 135, 57, 109, 63, 235, 196, 117, 37, 69, 122, 12, 78, 218, 148, 132, 197, 150, 185, 152, 250, 129, 108, 45, 84, 35, 203, 167, 233, 93, 4, 27, 242, 94, 153, 247, 70, 12, 141, 66, 135, 198, 239, 17, 33, 19, 68, 37, 79, 139, 55, 71, 182, 135, 229, 79, 217, 5, 192, 80, 178, 76, 180, 90, 162, 135, 57, 109, 63, 235, 196, 117, 37, 69, 122, 12, 78, 218, 148, 132, 197]
private noncomputable def hashInput4 : InputIndexedOracle.Input := (hashInput4Part0).map byte
private noncomputable def hashOutput4Part0 : List ℕ := [31, 139, 15, 167, 140, 100, 3, 107, 39, 244, 237, 190, 49, 157, 105, 102, 173, 176, 23, 157, 41, 236, 122, 230, 176, 120, 213, 59, 239, 62, 143, 8, 179, 96, 241, 219, 161, 243, 80, 189, 9, 95, 32, 103, 210, 127, 229, 24, 56, 36, 9, 239, 238, 10, 141, 185, 195, 79, 97, 203, 123, 68, 43, 213]
private noncomputable def hashOutput4 : InputIndexedOracle.Input := (hashOutput4Part0).map byte
private noncomputable def hashInput5Part0 : List ℕ := [31, 139, 15, 167, 140, 100, 3, 107, 39, 244, 237, 190, 49, 157, 105, 102, 173, 176, 23, 157, 41, 236, 122, 230, 176, 120, 213, 59, 239, 62, 143, 8, 179, 96, 241, 219, 161, 243, 80, 189, 9, 95, 32, 103, 210, 127, 229, 24, 56, 36, 9, 239, 238, 10, 141, 185, 195, 79, 97, 203, 123, 68, 43, 213, 31, 139, 15, 167, 140, 100, 3, 107, 39, 244, 237, 190, 49, 157, 105, 102, 173, 176, 23, 157, 41, 236, 122, 230, 176, 120, 213, 59, 239, 62, 143, 8, 179, 96, 241, 219, 161, 243, 80, 189, 9, 95, 32, 103, 210, 127, 229, 24, 56, 36, 9, 239, 238, 10, 141, 185, 195, 79, 97, 203, 123, 68, 43, 213]
private noncomputable def hashInput5 : InputIndexedOracle.Input := (hashInput5Part0).map byte
private noncomputable def hashOutput5Part0 : List ℕ := [220, 143, 168, 252, 21, 76, 13, 212, 18, 28, 43, 112, 109, 152, 161, 59, 223, 149, 43, 99, 19, 191, 251, 110, 76, 10, 135, 196, 142, 174, 68, 211, 223, 83, 49, 31, 224, 15, 177, 28, 175, 199, 67, 5, 28, 132, 61, 144, 224, 105, 238, 57, 90, 28, 65, 255, 165, 129, 75, 157, 149, 163, 107, 158]
private noncomputable def hashOutput5 : InputIndexedOracle.Input := (hashOutput5Part0).map byte
private noncomputable def hashInput6Part0 : List ℕ := [220, 143, 168, 252, 21, 76, 13, 212, 18, 28, 43, 112, 109, 152, 161, 59, 223, 149, 43, 99, 19, 191, 251, 110, 76, 10, 135, 196, 142, 174, 68, 211, 223, 83, 49, 31, 224, 15, 177, 28, 175, 199, 67, 5, 28, 132, 61, 144, 224, 105, 238, 57, 90, 28, 65, 255, 165, 129, 75, 157, 149, 163, 107, 158, 220, 143, 168, 252, 21, 76, 13, 212, 18, 28, 43, 112, 109, 152, 161, 59, 223, 149, 43, 99, 19, 191, 251, 110, 76, 10, 135, 196, 142, 174, 68, 211, 223, 83, 49, 31, 224, 15, 177, 28, 175, 199, 67, 5, 28, 132, 61, 144, 224, 105, 238, 57, 90, 28, 65, 255, 165, 129, 75, 157, 149, 163, 107, 158]
private noncomputable def hashInput6 : InputIndexedOracle.Input := (hashInput6Part0).map byte
private noncomputable def hashOutput6Part0 : List ℕ := [128, 159, 78, 167, 37, 0, 249, 58, 247, 55, 197, 246, 10, 140, 8, 180, 126, 62, 5, 162, 183, 44, 246, 37, 85, 88, 167, 253, 25, 75, 171, 196, 213, 7, 207, 63, 66, 20, 82, 21, 155, 235, 74, 33, 161, 244, 239, 93, 179, 186, 128, 172, 179, 27, 97, 119, 1, 61, 105, 252, 214, 80, 207, 233]
private noncomputable def hashOutput6 : InputIndexedOracle.Input := (hashOutput6Part0).map byte
private noncomputable def hashPairs : List (InputIndexedOracle.Input × InputIndexedOracle.Input) := [(hashInput0,hashOutput0),(hashInput1,hashOutput1),(hashInput2,hashOutput2),(hashInput3,hashOutput3),(hashInput4,hashOutput4),(hashInput5,hashOutput5),(hashInput6,hashOutput6)]
private noncomputable def world : InputIndexedOracle.World
  | .inr (input,index) => match hashPairs.find? (fun pair => pair.1=input) with
    | none => byte 255
    | some pair => pair.2[index.val]?.getD (byte 255)
  | .inl (input,offset) => match ([(start0,stream0),(start1,stream1),(start2,stream2)] :
      List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1=input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def root : NativeRootMessage.Digest := fun index => nativeRoot[index.val]?.getD (byte 255)
private noncomputable def query := (NativeGoldPcsWire.queryCodec.read nativeQuery).map Prod.fst
private noncomputable def opening := (NativeGoldPcsOpening.codec.read nativeOpening).map Prod.fst
private noncomputable def claimed := row [1, 0, 0] (by decide)
-- Decode the original native bytes and run the actual prefix and raw worker.
private noncomputable def handoff : OracleProgram.Program Nat :=
  match query,opening with
  | some q,some proof => OracleProgram.bind
    (NativeGoldPcsWorkers.protocol blockTables retainedParameters parent root q claimed proof 18)
    (fun result => match result with
      | .prepared work => match work.jobs with
        | [job] => OracleProgram.bind
          (NativeHashOracleBridge.compile (NativeGoldColumnWorker.worker work.geometry work.width work.random
            work.structured work.test work.evaluation work.root job.index job.column))
          (fun passed => .pure (match NativeGoldPcsAcceptance.finish retainedParameters q proof claimed work
              (⟨fun _ => pure passed,()⟩ : HashWorkerPool.Outcome InputIndexedOracle.Input NativeRootMessage.Digest Unit work.jobs.length) with
            | .accepted _ => 1
            | .columns => 2
            | .claim .claim => 3
            | _ => 0))
        | _ => .pure 0
      | _ => .pure 0)
  | _,_ => .pure 0
private noncomputable def result : Nat × List NativeTranscript.Observation := (OracleProgram.run handoff world).run
example : result.1 = 3 := by decide +kernel
private noncomputable def expected : List NativeTranscript.Observation :=
  [.hash hashInput0 hashOutput0,.start start0] ++
  (List.range 18).map (fun index => .output start0 (index*8) ((stream0.drop (index*8)).take 8)) ++
  [.start start1,.output start1 0 stream1,.start start2,.output start2 0 stream2] ++
  [.hash hashInput1 hashOutput1,.hash hashInput2 hashOutput2,.hash hashInput3 hashOutput3,.hash hashInput4 hashOutput4,.hash hashInput5 hashOutput5,.hash hashInput6 hashOutput6]
example : result.2 = expected := by decide +kernel

-- Full production prefix/pool/claim program, including computed residuals.
private noncomputable def fullRun (fuel : ℕ) (cancel : Bool) :
    NativeGoldPcsExecution.Outcome Unit × List NativeTranscript.Observation :=
  match query,opening with
  | some q,some proof =>
    (simulateQ (executionHandler world) (NativeGoldPcsExecution.program
      ⟨blockTables,retainedParameters,parent,root,q,claimed,proof,18⟩
      (InputIndexedOracle.shake world) (chooseWorker cancel) fuel ())).run
  | _,_ => (.prefix .pairingUnavailable [],[])
example : executionTag (fullRun 6 false).1 = 3 := by decide +kernel
example : (fullRun 6 false).2 = hashPairs.map (fun pair => .hash pair.1 pair.2) := by decide +kernel
example : (match (fullRun 6 false).1 with
  | .completed _ observations _ => some observations | _ => none) = some (expected.take 24) := by decide +kernel
example : executionTag (fullRun 5 false).1 = 4 := by decide +kernel
example : (fullRun 5 false).2 = (hashPairs.take 6).map (fun pair => .hash pair.1 pair.2) := by decide +kernel
example : executionTag (fullRun 6 true).1 = 4 := by decide +kernel
example : (fullRun 6 true).2 = [.hash hashInput0 hashOutput0] := by decide +kernel
end ZeroBad

end NativePcsClaimSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsClaim.equal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsClaim.equal_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsClaim.accepted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsClaim.accepted_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsClaim.accepted_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsClaim.accepted_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete.loop_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete.loop_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete.evaluate_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete.evaluate_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete.finish_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete.finish_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete.prepared_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete.prepared_finish

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.failed_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.failed_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.anyRejected_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.anyRejected_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.accepted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.accepted_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.program_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.program_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.accepted_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance.accepted_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness.prepared_no_finish_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness.prepared_no_finish_error

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness.accepted_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness.accepted_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness.accepted_workers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness.accepted_workers
