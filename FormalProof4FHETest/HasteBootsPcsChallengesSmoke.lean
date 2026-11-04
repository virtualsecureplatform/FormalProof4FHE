module

import all Mathlib.Data.List.Sort

import all FormalProof4FHE.HasteBoots.NativePrimeRequest
import all FormalProof4FHE.HasteBoots.NativeIndexRequest
import all FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw
import all FormalProof4FHE.HasteBoots.NativeGoldPcsWire
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.OracleProgram

open FormalProof4FHE.HasteBoots
/-! Goldilocks native fixtures at dff353006322693cab3dc6b654f82151f658f294.
Recorded SHAKE bytes instantiate ideal worlds. The combined case retains native
linear-response framing between base-field and atomic-column requests. These
are differential computations, not a checked Rust/SHAKE implementation proof. -/

namespace NativePcsChallengeSmoke
open OracleProgram (Program bind run)
private noncomputable def byte (n : ℕ) : InputIndexedOracle.Byte := ⟨n % 256,Nat.mod_lt _ (by decide)⟩
private noncomputable def usize (n : ℕ) : NativeUsizeMessage.Usize := ⟨n % (2^64),Nat.mod_lt _ (by decide)⟩
private noncomputable def parent := NativeTranscript.appendBytes (NativeTranscript.new (NativeTranscript.utf8 "HasteBoots typed classical prime v1") (fun _ => 0)) (NativeTranscript.utf8 "typed prime field") (TranscriptFrame.littleEndian 16 NativeFields.goldilocksModulus)
private noncomputable def primeLabel := NativeTranscript.utf8 "mw random linear test"
private noncomputable def columnLabel := NativeTranscript.utf8 "mw atomic column block v5"
private noncomputable def afterLabel := NativeTranscript.utf8 "after PCS challenge fixture"
private noncomputable def combinedStart0 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def combinedStream0 : InputIndexedOracle.Input := ([128, 30, 54, 82, 140, 45, 158, 73, 87, 198, 14, 145, 5, 56, 38, 241, 198, 101, 132, 71, 8, 142, 242, 116, 122, 7, 68, 200, 36, 150, 131, 228] : List ℕ).map byte
private noncomputable def combinedStart1 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 99, 111, 110, 115, 117, 109, 101, 100, 32, 102, 105, 101, 108, 100, 32, 98, 121, 116, 101, 115, 32, 118, 49, 128, 30, 54, 82, 140, 45, 158, 73, 87, 198, 14, 145, 5, 56, 38, 241, 198, 101, 132, 71, 8, 142, 242, 116, 122, 7, 68, 200, 36, 150, 131, 228] : List ℕ).map byte
private noncomputable def combinedStream1 : InputIndexedOracle.Input := ([171, 167, 109, 234, 231, 63, 201, 238, 139, 24, 24, 221, 22, 255, 26, 49, 236, 253, 83, 113, 100, 207, 56, 59, 91, 196, 152, 31, 97, 10, 8, 33, 222, 139, 19, 77, 79, 241, 226, 90, 142, 19, 114, 12, 216, 220, 240, 134, 40, 116, 194, 252, 27, 122, 190, 148, 167, 212, 235, 10, 251, 217, 48, 149] : List ℕ).map byte
private noncomputable def combinedStart2 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 5, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 80, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 171, 167, 109, 234, 231, 63, 201, 238, 139, 24, 24, 221, 22, 255, 26, 49, 236, 253, 83, 113, 100, 207, 56, 59, 91, 196, 152, 31, 97, 10, 8, 33, 222, 139, 19, 77, 79, 241, 226, 90, 142, 19, 114, 12, 216, 220, 240, 134, 40, 116, 194, 252, 27, 122, 190, 148, 167, 212, 235, 10, 251, 217, 48, 149, 1, 19, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 108, 105, 110, 101, 97, 114, 32, 114, 101, 115, 112, 111, 110, 115, 101, 115, 24, 0, 0, 0, 0, 0, 0, 0, 4, 251, 251, 0, 253, 255, 255, 255, 255, 255, 255, 255, 255, 252, 0, 0, 1, 0, 0, 4, 5, 7, 11, 13, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 136, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def combinedStream2 : InputIndexedOracle.Input := ([251, 121, 4, 134, 46, 168, 29, 148, 139, 215, 154, 91, 91, 236, 223, 182, 164, 83, 208, 126, 85, 77, 208, 50, 228, 143, 29, 98, 82, 233, 4, 76, 179, 44, 105, 15, 69, 189, 167, 147, 94, 212, 51, 94, 136, 85, 62, 36, 167, 182, 140, 16, 146, 244, 8, 95, 167, 50, 235, 143, 77, 147, 139, 103, 197, 211, 179, 215, 74, 113, 191, 169, 159, 3, 68, 57, 129, 100, 122, 47, 181, 246, 161, 53, 237, 215, 97, 48, 137, 203, 141, 21, 241, 253, 90, 61, 185, 192, 190, 105, 114, 251, 2, 160, 38, 226, 13, 247, 172, 36, 143, 99, 64, 131, 220, 112, 124, 122, 109, 43, 134, 41, 6, 167, 6, 52, 208, 139, 20, 206, 170, 196, 152, 41, 182, 241] : List ℕ).map byte
private noncomputable def combinedStart3 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 5, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 80, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 171, 167, 109, 234, 231, 63, 201, 238, 139, 24, 24, 221, 22, 255, 26, 49, 236, 253, 83, 113, 100, 207, 56, 59, 91, 196, 152, 31, 97, 10, 8, 33, 222, 139, 19, 77, 79, 241, 226, 90, 142, 19, 114, 12, 216, 220, 240, 134, 40, 116, 194, 252, 27, 122, 190, 148, 167, 212, 235, 10, 251, 217, 48, 149, 1, 19, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 108, 105, 110, 101, 97, 114, 32, 114, 101, 115, 112, 111, 110, 115, 101, 115, 24, 0, 0, 0, 0, 0, 0, 0, 4, 251, 251, 0, 253, 255, 255, 255, 255, 255, 255, 255, 255, 252, 0, 0, 1, 0, 0, 4, 5, 7, 11, 13, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 136, 0, 0, 0, 0, 0, 0, 0, 3, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 136, 0, 0, 0, 0, 0, 0, 0, 251, 121, 4, 134, 46, 168, 29, 148, 139, 215, 154, 91, 91, 236, 223, 182, 164, 83, 208, 126, 85, 77, 208, 50, 228, 143, 29, 98, 82, 233, 4, 76, 179, 44, 105, 15, 69, 189, 167, 147, 94, 212, 51, 94, 136, 85, 62, 36, 167, 182, 140, 16, 146, 244, 8, 95, 167, 50, 235, 143, 77, 147, 139, 103, 197, 211, 179, 215, 74, 113, 191, 169, 159, 3, 68, 57, 129, 100, 122, 47, 181, 246, 161, 53, 237, 215, 97, 48, 137, 203, 141, 21, 241, 253, 90, 61, 185, 192, 190, 105, 114, 251, 2, 160, 38, 226, 13, 247, 172, 36, 143, 99, 64, 131, 220, 112, 124, 122, 109, 43, 134, 41, 6, 167, 6, 52, 208, 139, 20, 206, 170, 196, 152, 41, 182, 241, 2, 27, 0, 0, 0, 0, 0, 0, 0, 97, 102, 116, 101, 114, 32, 80, 67, 83, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 102, 105, 120, 116, 117, 114, 101, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def combinedStream3 : InputIndexedOracle.Input := ([251, 19, 222, 187] : List ℕ).map byte
private noncomputable def combinedWorld : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (input,offset) => match ([(combinedStart0,combinedStream0),(combinedStart1,combinedStream1),(combinedStart2,combinedStream2),(combinedStart3,combinedStream3)] : List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1 = input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def combinedEvents : List NativeTranscript.Observation := [.start combinedStart0,.output combinedStart0 0 ((combinedStream0.drop 0).take 8),.output combinedStart0 8 ((combinedStream0.drop 8).take 8),.output combinedStart0 16 ((combinedStream0.drop 16).take 8),.output combinedStart0 24 ((combinedStream0.drop 24).take 8),.start combinedStart1,.output combinedStart1 0 ((combinedStream1.drop 0).take 64),.start combinedStart2,.output combinedStart2 0 ((combinedStream2.drop 0).take 136),.start combinedStart3,.output combinedStart3 0 ((combinedStream3.drop 0).take 4)]
private noncomputable def scalarStart0 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 115, 99, 97, 108, 97, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 19, 0, 0, 0, 0, 0, 0, 0, 98, 97, 115, 101, 32, 115, 99, 97, 108, 97, 114, 32, 102, 105, 120, 116, 117, 114, 101, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def scalarStream0 : InputIndexedOracle.Input := ([43, 46, 209, 53, 95, 36, 135, 71] : List ℕ).map byte
private noncomputable def scalarStart1 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 99, 111, 110, 115, 117, 109, 101, 100, 32, 102, 105, 101, 108, 100, 32, 98, 121, 116, 101, 115, 32, 118, 49, 43, 46, 209, 53, 95, 36, 135, 71] : List ℕ).map byte
private noncomputable def scalarStream1 : InputIndexedOracle.Input := ([3, 177, 226, 234, 245, 252, 4, 19, 104, 251, 81, 5, 135, 74, 20, 192, 85, 159, 177, 170, 153, 138, 75, 32, 172, 91, 133, 25, 254, 223, 200, 147, 156, 65, 135, 213, 22, 172, 32, 39, 139, 146, 8, 57, 54, 232, 160, 65, 71, 72, 190, 89, 149, 201, 95, 237, 132, 159, 42, 106, 63, 8, 50, 167] : List ℕ).map byte
private noncomputable def scalarStart2 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 115, 99, 97, 108, 97, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 19, 0, 0, 0, 0, 0, 0, 0, 98, 97, 115, 101, 32, 115, 99, 97, 108, 97, 114, 32, 102, 105, 120, 116, 117, 114, 101, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 19, 0, 0, 0, 0, 0, 0, 0, 98, 97, 115, 101, 32, 115, 99, 97, 108, 97, 114, 32, 102, 105, 120, 116, 117, 114, 101, 80, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 177, 226, 234, 245, 252, 4, 19, 104, 251, 81, 5, 135, 74, 20, 192, 85, 159, 177, 170, 153, 138, 75, 32, 172, 91, 133, 25, 254, 223, 200, 147, 156, 65, 135, 213, 22, 172, 32, 39, 139, 146, 8, 57, 54, 232, 160, 65, 71, 72, 190, 89, 149, 201, 95, 237, 132, 159, 42, 106, 63, 8, 50, 167, 2, 27, 0, 0, 0, 0, 0, 0, 0, 97, 102, 116, 101, 114, 32, 80, 67, 83, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 102, 105, 120, 116, 117, 114, 101, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def scalarStream2 : InputIndexedOracle.Input := ([66, 232, 248, 87] : List ℕ).map byte
private noncomputable def scalarWorld : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (input,offset) => match ([(scalarStart0,scalarStream0),(scalarStart1,scalarStream1),(scalarStart2,scalarStream2)] : List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1 = input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def scalarEvents : List NativeTranscript.Observation := [.start scalarStart0,.output scalarStart0 0 ((scalarStream0.drop 0).take 8),.start scalarStart1,.output scalarStart1 0 ((scalarStream1.drop 0).take 64),.start scalarStart2,.output scalarStart2 0 ((scalarStream2.drop 0).take 4)]
private noncomputable def emptyStart0 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def emptyStream0 : InputIndexedOracle.Input := ([] : List ℕ).map byte
private noncomputable def emptyStart1 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 99, 111, 110, 115, 117, 109, 101, 100, 32, 102, 105, 101, 108, 100, 32, 98, 121, 116, 101, 115, 32, 118, 49] : List ℕ).map byte
private noncomputable def emptyStream1 : InputIndexedOracle.Input := ([183, 182, 52, 111, 170, 211, 33, 223, 7, 70, 151, 196, 155, 55, 129, 27, 216, 220, 105, 85, 91, 166, 126, 23, 56, 70, 210, 51, 28, 126, 173, 234, 236, 55, 125, 125, 75, 115, 235, 234, 232, 239, 32, 17, 220, 139, 73, 173, 242, 235, 88, 190, 76, 47, 120, 99, 56, 56, 95, 131, 6, 248, 148, 233] : List ℕ).map byte
private noncomputable def emptyStart2 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 183, 182, 52, 111, 170, 211, 33, 223, 7, 70, 151, 196, 155, 55, 129, 27, 216, 220, 105, 85, 91, 166, 126, 23, 56, 70, 210, 51, 28, 126, 173, 234, 236, 55, 125, 125, 75, 115, 235, 234, 232, 239, 32, 17, 220, 139, 73, 173, 242, 235, 88, 190, 76, 47, 120, 99, 56, 56, 95, 131, 6, 248, 148, 233, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def emptyStream2 : InputIndexedOracle.Input := ([] : List ℕ).map byte
private noncomputable def emptyStart3 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 183, 182, 52, 111, 170, 211, 33, 223, 7, 70, 151, 196, 155, 55, 129, 27, 216, 220, 105, 85, 91, 166, 126, 23, 56, 70, 210, 51, 28, 126, 173, 234, 236, 55, 125, 125, 75, 115, 235, 234, 232, 239, 32, 17, 220, 139, 73, 173, 242, 235, 88, 190, 76, 47, 120, 99, 56, 56, 95, 131, 6, 248, 148, 233, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 0, 0, 0, 0, 0, 0, 0, 0, 2, 27, 0, 0, 0, 0, 0, 0, 0, 97, 102, 116, 101, 114, 32, 80, 67, 83, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 102, 105, 120, 116, 117, 114, 101, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def emptyStream3 : InputIndexedOracle.Input := ([168, 102, 28, 220] : List ℕ).map byte
private noncomputable def emptyWorld : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (input,offset) => match ([(emptyStart0,emptyStream0),(emptyStart1,emptyStream1),(emptyStart2,emptyStream2),(emptyStart3,emptyStream3)] : List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1 = input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def emptyEvents : List NativeTranscript.Observation := [.start emptyStart0,.start emptyStart1,.output emptyStart1 0 ((emptyStream1.drop 0).take 64),.start emptyStart2,.output emptyStart2 0 ((emptyStream2.drop 0).take 0),.start emptyStart3,.output emptyStart3 0 ((emptyStream3.drop 0).take 4)]
private noncomputable def oneStart0 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def oneStream0 : InputIndexedOracle.Input := ([150, 195, 202, 73, 14, 86, 219, 243, 184, 4, 134, 156, 83, 155, 202, 0, 7, 66, 39, 51, 232, 245, 138, 37, 246, 249, 63, 133, 11, 243, 47, 9] : List ℕ).map byte
private noncomputable def oneStart1 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 3, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 32, 0, 0, 0, 0, 0, 0, 0, 150, 195, 202, 73, 14, 86, 219, 243, 184, 4, 134, 156, 83, 155, 202, 0, 7, 66, 39, 51, 232, 245, 138, 37, 246, 249, 63, 133, 11, 243, 47, 9, 2, 27, 0, 0, 0, 0, 0, 0, 0, 97, 102, 116, 101, 114, 32, 80, 67, 83, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 102, 105, 120, 116, 117, 114, 101, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def oneStream1 : InputIndexedOracle.Input := ([30, 87, 19, 146] : List ℕ).map byte
private noncomputable def oneWorld : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (input,offset) => match ([(oneStart0,oneStream0),(oneStart1,oneStream1)] : List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1 = input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def oneEvents : List NativeTranscript.Observation := [.start oneStart0,.output oneStart0 0 ((oneStream0.drop 0).take 32),.start oneStart1,.output oneStart1 0 ((oneStream1.drop 0).take 4)]
private noncomputable def invalidStart0 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 2, 27, 0, 0, 0, 0, 0, 0, 0, 97, 102, 116, 101, 114, 32, 80, 67, 83, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 102, 105, 120, 116, 117, 114, 101, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def invalidStream0 : InputIndexedOracle.Input := ([20, 130, 186, 27] : List ℕ).map byte
private noncomputable def invalidWorld : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (input,offset) => match ([(invalidStart0,invalidStream0)] : List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1 = input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def invalidEvents : List NativeTranscript.Observation := [.start invalidStart0,.output invalidStart0 0 ((invalidStream0.drop 0).take 4)]
private noncomputable def unchangedStart0 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 2, 27, 0, 0, 0, 0, 0, 0, 0, 97, 102, 116, 101, 114, 32, 80, 67, 83, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 102, 105, 120, 116, 117, 114, 101, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def unchangedStream0 : InputIndexedOracle.Input := ([20, 130, 186, 27] : List ℕ).map byte
private noncomputable def unchangedWorld : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (input,offset) => match ([(unchangedStart0,unchangedStream0)] : List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1 = input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def unchangedEvents : List NativeTranscript.Observation := [.start unchangedStart0,.output unchangedStart0 0 ((unchangedStream0.drop 0).take 4)]
private noncomputable def nativeResponses : InputIndexedOracle.Input := ([4, 251, 251, 0, 253, 255, 255, 255, 255, 255, 255, 255, 255, 252, 0, 0, 1, 0, 0, 4, 5, 7, 11, 13] : List ℕ).map byte
private noncomputable def test : NativeLookupRequestWire.Row := ⟨[usize 251,usize (2^64-1),usize 65536,usize 0],by decide⟩
private noncomputable def evaluation : NativeLookupRequestWire.Row := ⟨[usize 5,usize 7,usize 11,usize 13],by decide⟩
private noncomputable def combined : Program (Option (List ℕ × List ℕ × List ℕ × InputIndexedOracle.Input)) :=
  bind (NativePrimeRequest.request NativeFields.goldilocksModulus 8 parent .vector primeLabel (usize 4)) (fun phase =>
    match phase with
    | .suspended _ => .pure none
    | .finished state next => bind (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses next test evaluation) columnLabel (usize 32) (usize 17)) (fun received =>
      match received with
      | none => .pure none
      | some result => bind (NativeTranscriptProgram.challengeBytes result.transcript afterLabel 4) (fun output =>
        .pure (some (state.values,result.draws,result.indices,output.1)))))
private noncomputable def combinedResult := (run combined combinedWorld).run
example : combinedResult.1 = some ([5304727491786972800, 17376637808815294039, 8426954018974361030, 16466169747319555962],[27, 11, 4, 4, 19, 30, 7, 7, 5, 31, 21, 9, 25, 6, 0, 6, 20],[0, 4, 5, 6, 7, 9, 11, 19, 20, 21, 25, 27, 30, 31],combinedStream3) := by decide +kernel
example : combinedResult.2 = combinedEvents := by decide +kernel
example : NativeGoldPcsWire.responses test evaluation = nativeResponses := by decide +kernel
example : NativeGoldPcsWire.responseCodec.read (nativeResponses ++ [byte 88]) = some ((test,evaluation),[byte 88]) := by decide +kernel
private noncomputable def scalar : Program (Option (List ℕ × InputIndexedOracle.Input)) :=
  bind (NativePrimeRequest.request NativeFields.goldilocksModulus 2 parent .scalar (NativeTranscript.utf8 "base scalar fixture") (usize 1)) (fun phase =>
    match phase with
    | .suspended _ => .pure none
    | .finished state next => bind (NativeTranscriptProgram.challengeBytes next afterLabel 4) (fun output => .pure (some (state.values,output.1))))
private noncomputable def scalarResult := (run scalar scalarWorld).run
example : scalarResult.1 = some ([5154128289892216363],scalarStream2) := by decide +kernel
example : scalarResult.2 = scalarEvents := by decide +kernel
private noncomputable def emptyRequest : Program (Option (List ℕ × List ℕ × InputIndexedOracle.Input)) :=
  bind (NativePrimeRequest.request NativeFields.goldilocksModulus 0 parent .vector primeLabel (usize 0)) (fun phase =>
    match phase with
    | .suspended _ => .pure none
    | .finished state next => bind (NativeIndexRequest.request next columnLabel (usize 1) (usize 0)) (fun received =>
      match received with
      | none => .pure none
      | some result => bind (NativeTranscriptProgram.challengeBytes result.transcript afterLabel 4) (fun output => .pure (some (state.values,result.draws,output.1)))))
private noncomputable def emptyResult := (run emptyRequest emptyWorld).run
example : emptyResult.1 = some ([],[],emptyStream3) := by decide +kernel
example : emptyResult.2 = emptyEvents := by decide +kernel
private noncomputable def one : Program (Option (List ℕ × List ℕ × InputIndexedOracle.Input)) :=
  bind (NativeIndexRequest.request parent columnLabel (usize 1) (usize 4)) (fun received =>
    match received with
    | none => .pure none
    | some result => bind (NativeTranscriptProgram.challengeBytes result.transcript afterLabel 4) (fun output => .pure (some (result.draws,result.indices,output.1))))
example : (run one oneWorld).run.1 = some ([0,0,0,0],[0],oneStream1) := by decide +kernel
example : (run one oneWorld).run.2 = oneEvents := by decide +kernel
private noncomputable def invalidRequests := bind (NativeIndexRequest.request parent columnLabel (usize 0) (usize 17)) (fun _ =>
  bind (NativeIndexRequest.request parent columnLabel (usize 3) (usize 17)) (fun _ =>
    bind (NativeIndexRequest.request parent columnLabel (usize 32) (usize (2^64-1))) (fun _ => NativeTranscriptProgram.challengeBytes parent afterLabel 4)))
example : (run invalidRequests invalidWorld).run.2 = invalidEvents := by decide +kernel
example : invalidEvents = unchangedEvents := by decide +kernel
example : (NativePrimeRequest.prepare parent .scalar).input ≠ (NativePrimeRequest.prepare parent .vector).input := by decide +kernel
example : (NativePrimeRequest.prepare parent .vector).input ≠ (NativeExtensionRequest.prepare (TypedFieldRequest.prepare parent .vector) 1 0).input := by decide +kernel
-- Scripted ideal bytes exercise canonical rejection; no SHAKE preimage is claimed.
private noncomputable def rejectionPhase := NativePrimeRequest.phase NativeFields.goldilocksModulus parent .vector primeLabel (usize 1)
private noncomputable def rejectionWorld : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (input,offset) => if input = rejectionPhase.pending.input then
      if offset < 8 then byte 255 else if offset = 8 then byte 7 else byte 0
    else byte 0
private noncomputable def first := (run (NativePrimeRequest.request NativeFields.goldilocksModulus 1 parent .vector primeLabel (usize 1)) rejectionWorld).run
private noncomputable def resumed := (run (NativeFieldVector.resume NativeFields.goldilocksModulus 1 first.1) rejectionWorld).run
example : (match first.1 with | .suspended state => some (state.remaining,state.values,state.phase.consumed.length) | _ => none) = some (1,[],8) := by decide +kernel
example : first.2.length = 2 := by decide +kernel
example : (match resumed.1 with | .finished state _ => some (state.remaining,state.values,state.phase.consumed.map Fin.val) | _ => none) = some (0,[7],List.replicate 8 255 ++ [7,0,0,0,0,0,0,0]) := by decide +kernel
example : (first.2 ++ resumed.2).filterMap (fun event => match event with | .output _ offset bytes => if bytes.length = 8 then some offset else none | _ => none) = [0,8] := by decide +kernel
example : ((first.2 ++ resumed.2).filterMap (fun event => match event with | .start input => some input | _ => none)).length = 2 := by decide +kernel
example : NativeIndexRequest.check (usize (2^63)) (usize 3) = true := by decide +kernel
example : NativeIndexRequest.check (usize 32) (usize (2^61)) = false := by decide +kernel
private noncomputable def allOnes : InputIndexedOracle.World := fun _ => byte 255
example : (run (NativeIndexRequest.request parent columnLabel (usize (2^63)) (usize 3)) allOnes).run.1.map (fun result => (result.draws,result.indices)) = some ([2^63-1,2^63-1,2^63-1],[2^63-1]) := by decide +kernel
private noncomputable def block : Fin 16 → InputIndexedOracle.Byte := fun index => if index.val % 8 = 0 then byte (index.val / 8) else byte 255
example : NativeIndexRequest.ordered 8 2 (List.ofFn block) = [0,1] := by decide +kernel
example : (List.ofFn (NativeIndexRequest.typedDraws 3 2 block)).map Fin.val = [0,1] := by decide +kernel
end NativePcsChallengeSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.prepare_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.prepare_input

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.request_eq_collector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.request_eq_collector

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.run_beginRequest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.run_beginRequest

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.drive_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.drive_request

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.request_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.request_count

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.request_values_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.request_values_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.finished_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.finished_length

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.request_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.request_add

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.request_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.request_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.goldWord_exact' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.goldWord_exact

/-- info: 'FormalProof4FHE.HasteBoots.NativePrimeRequest.finished_gold_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrimeRequest.finished_gold_exact

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.distinct_eq_mergeSort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.distinct_eq_mergeSort

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.checked_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.checked_bits

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.prepare_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.prepare_input

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.ordered_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.ordered_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.word_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.word_lt

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.ordered_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.ordered_bounded

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.mem_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.mem_distinct

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.distinct_nodup' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.distinct_nodup

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.distinct_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.distinct_sorted

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.misses_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.misses_distinct

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.invalid_request' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.invalid_request

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.accepted_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.accepted_check

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.run_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.run_request

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.accepted_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.accepted_shape

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.word_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.word_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.ordered_get' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.ordered_get

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.slice_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.slice_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.slice_ofFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.slice_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.NativeIndexRequest.ordered_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeIndexRequest.ordered_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw.blocks_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw.blocks_apply

/-- info: 'FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw.splitBlock_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw.splitBlock_snd

/-- info: 'FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw.uniform_draws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw.uniform_draws

/-- info: 'FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw.agreement_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw.agreement_probability

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.responses_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.responses_encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.responses_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.responses_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.bindResponses_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.bindResponses_input
