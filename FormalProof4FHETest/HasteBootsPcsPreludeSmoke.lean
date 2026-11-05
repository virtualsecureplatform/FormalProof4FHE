module

import all Mathlib.Data.List.Sort
import all Batteries.Data.Except
import all FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding
import all FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers
import all FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability
import all FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks

import all FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude
import all FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape
import all FormalProof4FHE.HasteBoots.NativeGoldPcsColumns
import all FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic
import all FormalProof4FHE.HasteBoots.NativeIndexRequest
import all FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.OracleProgram

open FormalProof4FHE.HasteBoots
/-! Native fixtures at dff353006322693cab3dc6b654f82151f658f294. The fixture
passes the full native schedule-5 single-opening verifier. Lean compares the
checked parameter/binding/random-test prefix and the next atomic reader input;
the column prefix now computes structured weights and the actual atomic draw.
The raw suffix reproduces the exact native claimed words. A retained block-code specialization now continues through computed response
encoding. Column authentication/checking is not yet composed into that entry point. -/

namespace NativePcsPreludeSmoke
private noncomputable def byte (n : ℕ) : InputIndexedOracle.Byte := ⟨n % 256,Nat.mod_lt _ (by decide)⟩
private noncomputable def usize (n : ℕ) : NativeUsizeMessage.Usize := ⟨n % (2^64),Nat.mod_lt _ (by decide)⟩
private noncomputable def row (values : List ℕ) (fits : values.length < 2^64) : NativeLookupRequestWire.Row := ⟨values.map usize,by rw [List.length_map]; exact fits⟩
private noncomputable def digestOf (bytes : InputIndexedOracle.Input) : NativeRootMessage.Digest := fun index => bytes[index.val]?.getD (byte 255)
private noncomputable def nativeCode : InputIndexedOracle.Input := ([2, 2, 1, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0] : List ℕ).map byte
private noncomputable def nativeRoot : InputIndexedOracle.Input := ([222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201] : List ℕ).map byte
private noncomputable def nativeQuery : InputIndexedOracle.Input := ([2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7] : List ℕ).map byte
private noncomputable def nativeOpeningBytes : InputIndexedOracle.Input := ([6, 253, 14, 51, 105, 51, 92, 44, 251, 147, 253, 207, 231, 113, 94, 138, 243, 76, 255, 253, 150, 217, 11, 247, 61, 32, 251, 231, 253, 199, 191, 217, 7, 173, 169, 95, 162, 253, 206, 194, 126, 59, 84, 153, 156, 47, 253, 150, 132, 6, 186, 179, 195, 95, 113, 6, 253, 175, 0, 0, 0, 255, 255, 255, 255, 253, 181, 0, 0, 0, 255, 255, 255, 255, 253, 122, 0, 0, 0, 255, 255, 255, 255, 253, 128, 0, 0, 0, 255, 255, 255, 255, 253, 33, 0, 0, 0, 255, 255, 255, 255, 253, 39, 0, 0, 0, 255, 255, 255, 255, 1, 12, 0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11, 6, 173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2, 173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2, 76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179, 177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42, 134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84, 28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166] : List ℕ).map byte
private noncomputable def nativeStart0 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 23, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 78, 84, 84, 32, 114, 111, 119, 32, 112, 104, 97, 115, 101, 32, 118, 50, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 106, 111, 105, 110, 116, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 32, 118, 51, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 26, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 112, 97, 99, 107, 101, 100, 32, 122, 101, 114, 111, 99, 104, 101, 99, 107, 32, 118, 52, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 66, 114, 97, 107, 101, 100, 111, 119, 110, 32, 99, 111, 108, 117, 109, 110, 115, 32, 118, 53, 1, 24, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 98, 114, 97, 107, 101, 100, 111, 119, 110, 32, 114, 111, 119, 45, 99, 111, 100, 101, 32, 118, 50, 64, 0, 0, 0, 0, 0, 0, 0, 168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25, 39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145, 1, 23, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 32, 97, 110, 100, 32, 113, 117, 101, 114, 121, 25, 1, 0, 0, 0, 0, 0, 0, 222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201, 2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7, 3, 253, 201, 4, 0, 0, 255, 255, 255, 255, 253, 8, 3, 0, 0, 255, 255, 255, 255, 253, 219, 0, 0, 0, 255, 255, 255, 255, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def nativeStart1 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 99, 111, 110, 115, 117, 109, 101, 100, 32, 102, 105, 101, 108, 100, 32, 98, 121, 116, 101, 115, 32, 118, 49, 244, 141, 75, 248, 195, 196, 254, 124, 115, 239, 75, 153, 229, 32, 47, 203, 132, 44, 112, 108, 43, 64, 194, 136, 198, 137, 128, 76, 97, 253, 214, 133, 73, 156, 205, 168, 231, 226, 29, 87, 212, 248, 128, 62, 17, 155, 168, 142, 197, 225, 5, 81, 110, 225, 158, 234, 94, 174, 249, 203, 193, 164, 12, 236, 5, 31, 162, 110, 169, 107, 3, 161, 230, 192, 154, 165, 129, 114, 34, 251, 117, 186, 127, 101, 183, 218, 17, 234, 138, 38, 102, 193, 37, 45, 216, 108, 198, 173, 251, 191, 69, 62, 248, 63, 253, 153, 162, 26, 155, 7, 98, 213, 209, 79, 212, 247, 149, 117, 56, 8, 110, 3, 183, 255, 140, 110, 110, 146, 233, 240, 231, 241, 164, 203, 243, 222, 15, 191, 175, 123, 14, 60, 86, 209] : List ℕ).map byte
private noncomputable def nativeStart2 : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 23, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 78, 84, 84, 32, 114, 111, 119, 32, 112, 104, 97, 115, 101, 32, 118, 50, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 106, 111, 105, 110, 116, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 32, 118, 51, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 26, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 112, 97, 99, 107, 101, 100, 32, 122, 101, 114, 111, 99, 104, 101, 99, 107, 32, 118, 52, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 66, 114, 97, 107, 101, 100, 111, 119, 110, 32, 99, 111, 108, 117, 109, 110, 115, 32, 118, 53, 1, 24, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 98, 114, 97, 107, 101, 100, 111, 119, 110, 32, 114, 111, 119, 45, 99, 111, 100, 101, 32, 118, 50, 64, 0, 0, 0, 0, 0, 0, 0, 168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25, 39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145, 1, 23, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 32, 97, 110, 100, 32, 113, 117, 101, 114, 121, 25, 1, 0, 0, 0, 0, 0, 0, 222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201, 2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7, 3, 253, 201, 4, 0, 0, 255, 255, 255, 255, 253, 8, 3, 0, 0, 255, 255, 255, 255, 253, 219, 0, 0, 0, 255, 255, 255, 255, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 5, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 80, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 125, 50, 231, 144, 114, 248, 153, 230, 232, 125, 70, 152, 157, 137, 210, 201, 204, 114, 197, 161, 100, 10, 58, 191, 223, 199, 219, 223, 105, 244, 252, 197, 75, 141, 165, 176, 135, 78, 178, 192, 143, 20, 181, 121, 154, 78, 17, 243, 134, 190, 195, 162, 176, 214, 203, 141, 102, 83, 70, 225, 234, 121, 23, 1, 19, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 108, 105, 110, 101, 97, 114, 32, 114, 101, 115, 112, 111, 110, 115, 101, 115, 110, 0, 0, 0, 0, 0, 0, 0, 6, 253, 14, 51, 105, 51, 92, 44, 251, 147, 253, 207, 231, 113, 94, 138, 243, 76, 255, 253, 150, 217, 11, 247, 61, 32, 251, 231, 253, 199, 191, 217, 7, 173, 169, 95, 162, 253, 206, 194, 126, 59, 84, 153, 156, 47, 253, 150, 132, 6, 186, 179, 195, 95, 113, 6, 253, 175, 0, 0, 0, 255, 255, 255, 255, 253, 181, 0, 0, 0, 255, 255, 255, 255, 253, 122, 0, 0, 0, 255, 255, 255, 255, 253, 128, 0, 0, 0, 255, 255, 255, 255, 253, 33, 0, 0, 0, 255, 255, 255, 255, 253, 39, 0, 0, 0, 255, 255, 255, 255, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def nativeHashInput0 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 47, 118, 50, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 2, 3, 1, 1, 2, 32, 26, 98, 108, 111, 99, 107, 45, 114, 115, 47, 110, 101, 103, 97, 99, 121, 99, 108, 105, 99, 45, 110, 116, 116, 47, 118, 49, 2, 2, 1, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0] : List ℕ).map byte
private noncomputable def nativeHashOutput0 : InputIndexedOracle.Input := ([168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25, 39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145] : List ℕ).map byte
private noncomputable def nativeStream0 : InputIndexedOracle.Input := ([244, 141, 75, 248, 195, 196, 254, 124, 115, 239, 75, 153, 229, 32, 47, 203, 132, 44, 112, 108, 43, 64, 194, 136, 198, 137, 128, 76, 97, 253, 214, 133, 73, 156, 205, 168, 231, 226, 29, 87, 212, 248, 128, 62, 17, 155, 168, 142, 197, 225, 5, 81, 110, 225, 158, 234, 94, 174, 249, 203, 193, 164, 12, 236, 5, 31, 162, 110, 169, 107, 3, 161, 230, 192, 154, 165, 129, 114, 34, 251, 117, 186, 127, 101, 183, 218, 17, 234, 138, 38, 102, 193, 37, 45, 216, 108, 198, 173, 251, 191, 69, 62, 248, 63, 253, 153, 162, 26, 155, 7, 98, 213, 209, 79, 212, 247, 149, 117, 56, 8, 110, 3, 183, 255, 140, 110, 110, 146, 233, 240, 231, 241, 164, 203, 243, 222, 15, 191, 175, 123, 14, 60, 86, 209] : List ℕ).map byte
private noncomputable def nativeStream1 : InputIndexedOracle.Input := ([229, 125, 50, 231, 144, 114, 248, 153, 230, 232, 125, 70, 152, 157, 137, 210, 201, 204, 114, 197, 161, 100, 10, 58, 191, 223, 199, 219, 223, 105, 244, 252, 197, 75, 141, 165, 176, 135, 78, 178, 192, 143, 20, 181, 121, 154, 78, 17, 243, 134, 190, 195, 162, 176, 214, 203, 141, 102, 83, 70, 225, 234, 121, 23] : List ℕ).map byte
private noncomputable def nativePath0_0 : InputIndexedOracle.Input := ([173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2] : List ℕ).map byte
private noncomputable def nativePath0_1 : InputIndexedOracle.Input := ([173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2] : List ℕ).map byte
private noncomputable def nativePath0_2 : InputIndexedOracle.Input := ([76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179] : List ℕ).map byte
private noncomputable def nativePath0_3 : InputIndexedOracle.Input := ([177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42] : List ℕ).map byte
private noncomputable def nativePath0_4 : InputIndexedOracle.Input := ([134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84] : List ℕ).map byte
private noncomputable def nativePath0_5 : InputIndexedOracle.Input := ([28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166] : List ℕ).map byte
private noncomputable def opening : NativeGoldPcsOpening.Opening := ⟨row [10663165317240926990, 18396346353517193167, 16715989892425570710, 11700256917557985223, 3430785603203941070, 8169463425760920726] (by decide),row [18446744069414584495, 18446744069414584501, 18446744069414584442, 18446744069414584448, 18446744069414584353, 18446744069414584359] (by decide),⟨[⟨row [0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11] (by decide),⟨[digestOf nativePath0_0,digestOf nativePath0_1,digestOf nativePath0_2,digestOf nativePath0_3,digestOf nativePath0_4,digestOf nativePath0_5],by decide⟩⟩],by decide⟩⟩
private noncomputable def claimed := row [18446744069414585545, 18446744069414585096, 18446744069414584539] (by decide)
private noncomputable def nativeStream2 : InputIndexedOracle.Input := ([187, 3, 162, 26, 70, 229, 227, 156] : List ℕ).map byte
private noncomputable def nativeAfterColumns : InputIndexedOracle.Input := ([0, 8, 0, 0, 0, 0, 0, 0, 0, 112, 114, 111, 116, 111, 99, 111, 108, 29, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 102, 114, 97, 109, 101, 100, 32, 83, 72, 65, 75, 69, 50, 53, 54, 32, 118, 49, 0, 11, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 35, 0, 0, 0, 0, 0, 0, 0, 72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 32, 116, 121, 112, 101, 100, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 112, 114, 105, 109, 101, 32, 118, 49, 0, 15, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 115, 116, 101, 100, 32, 112, 114, 111, 102, 105, 108, 101, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 112, 114, 105, 109, 101, 32, 102, 105, 101, 108, 100, 16, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 23, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 78, 84, 84, 32, 114, 111, 119, 32, 112, 104, 97, 115, 101, 32, 118, 50, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 106, 111, 105, 110, 116, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 32, 118, 51, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 26, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 112, 97, 99, 107, 101, 100, 32, 122, 101, 114, 111, 99, 104, 101, 99, 107, 32, 118, 52, 1, 28, 0, 0, 0, 0, 0, 0, 0, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 115, 99, 104, 101, 100, 117, 108, 101, 27, 0, 0, 0, 0, 0, 0, 0, 97, 116, 111, 109, 105, 99, 32, 66, 114, 97, 107, 101, 100, 111, 119, 110, 32, 99, 111, 108, 117, 109, 110, 115, 32, 118, 53, 1, 24, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 98, 114, 97, 107, 101, 100, 111, 119, 110, 32, 114, 111, 119, 45, 99, 111, 100, 101, 32, 118, 50, 64, 0, 0, 0, 0, 0, 0, 0, 168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25, 39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145, 1, 23, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 32, 97, 110, 100, 32, 113, 117, 101, 114, 121, 25, 1, 0, 0, 0, 0, 0, 0, 222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201, 2, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 9, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 180, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 253, 166, 255, 255, 255, 254, 255, 255, 255, 253, 244, 255, 255, 255, 254, 255, 255, 255, 253, 246, 255, 255, 255, 254, 255, 255, 255, 253, 251, 255, 255, 255, 254, 255, 255, 255, 3, 9, 7, 91, 77, 11, 7, 91, 13, 11, 7, 3, 253, 201, 4, 0, 0, 255, 255, 255, 255, 253, 8, 3, 0, 0, 255, 255, 255, 255, 253, 219, 0, 0, 0, 255, 255, 255, 255, 1, 18, 0, 0, 0, 0, 0, 0, 0, 116, 121, 112, 101, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 107, 105, 110, 100, 6, 0, 0, 0, 0, 0, 0, 0, 118, 101, 99, 116, 111, 114, 1, 20, 0, 0, 0, 0, 0, 0, 0, 102, 105, 101, 108, 100, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 107, 105, 110, 100, 12, 0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 109, 101, 32, 118, 101, 99, 116, 111, 114, 4, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 5, 21, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 114, 97, 110, 100, 111, 109, 32, 108, 105, 110, 101, 97, 114, 32, 116, 101, 115, 116, 80, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 125, 50, 231, 144, 114, 248, 153, 230, 232, 125, 70, 152, 157, 137, 210, 201, 204, 114, 197, 161, 100, 10, 58, 191, 223, 199, 219, 223, 105, 244, 252, 197, 75, 141, 165, 176, 135, 78, 178, 192, 143, 20, 181, 121, 154, 78, 17, 243, 134, 190, 195, 162, 176, 214, 203, 141, 102, 83, 70, 225, 234, 121, 23, 1, 19, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 108, 105, 110, 101, 97, 114, 32, 114, 101, 115, 112, 111, 110, 115, 101, 115, 110, 0, 0, 0, 0, 0, 0, 0, 6, 253, 14, 51, 105, 51, 92, 44, 251, 147, 253, 207, 231, 113, 94, 138, 243, 76, 255, 253, 150, 217, 11, 247, 61, 32, 251, 231, 253, 199, 191, 217, 7, 173, 169, 95, 162, 253, 206, 194, 126, 59, 84, 153, 156, 47, 253, 150, 132, 6, 186, 179, 195, 95, 113, 6, 253, 175, 0, 0, 0, 255, 255, 255, 255, 253, 181, 0, 0, 0, 255, 255, 255, 255, 253, 122, 0, 0, 0, 255, 255, 255, 255, 253, 128, 0, 0, 0, 255, 255, 255, 255, 253, 33, 0, 0, 0, 255, 255, 255, 255, 253, 39, 0, 0, 0, 255, 255, 255, 255, 1, 12, 0, 0, 0, 0, 0, 0, 0, 105, 110, 100, 101, 120, 32, 100, 111, 109, 97, 105, 110, 8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 3, 25, 0, 0, 0, 0, 0, 0, 0, 109, 119, 32, 97, 116, 111, 109, 105, 99, 32, 99, 111, 108, 117, 109, 110, 32, 98, 108, 111, 99, 107, 32, 118, 53, 8, 0, 0, 0, 0, 0, 0, 0, 187, 3, 162, 26, 70, 229, 227, 156, 2, 30, 0, 0, 0, 0, 0, 0, 0, 97, 102, 116, 101, 114, 32, 80, 67, 83, 32, 118, 101, 114, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 102, 105, 120, 116, 117, 114, 101, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] : List ℕ).map byte
private noncomputable def description : NativeBrakedownParameters.Description Unit :=
  ⟨⟨fun _ => usize 2,fun _ => usize 32,fun _ => ⟨NativeTranscript.utf8 "block-rs/negacyclic-ntt/v1",by decide⟩,fun _ => some nativeCode⟩,fun _ => usize 2⟩
private noncomputable def parameters : NativeBrakedownContext.Parameters Unit := ⟨usize 2,usize 3,usize 1,usize 1,()⟩
private noncomputable def root := digestOf nativeRoot
private noncomputable def point : List NativeFieldWire.GoldExtension := [![usize 2,usize 3,usize 5],![usize 7,usize 11,usize 13]]
private noncomputable def query : NativeGoldPcsWire.Query := (NativeGoldPcsWire.coefficientsQuery 3 point).getD ⟨[],by decide⟩
private noncomputable def initial := NativeTranscript.appendBytes (NativeTranscript.new (NativeTranscript.utf8 "HasteBoots typed classical prime v1") (fun _ => 0))
  (NativeTranscript.utf8 "typed prime field") (TranscriptFrame.littleEndian 16 NativeFields.goldilocksModulus)
private noncomputable def parent := (["atomic NTT row phase v2","atomic joint projections v3","atomic packed zerocheck v4","atomic Brakedown columns v5"] : List String).foldl
  (fun state schedule => NativeTranscript.appendBytes state (NativeTranscript.utf8 "classical challenge schedule") (NativeTranscript.utf8 schedule)) initial
private noncomputable def world : InputIndexedOracle.World
  | .inr (input,index) => if input = nativeHashInput0 then nativeHashOutput0[index.val]?.getD (byte 255) else byte 255
  | .inl (input,offset) => match ([(nativeStart0,nativeStream0),(nativeStart1,nativeStream1),(nativeStart2,nativeStream2)] : List (InputIndexedOracle.Input × InputIndexedOracle.Input)).find? (fun pair => pair.1 = input) with
    | none => byte 255
    | some pair => pair.2[offset]?.getD (byte 255)
private noncomputable def execute (proof : NativeGoldPcsOpening.Opening) (q : NativeGoldPcsWire.Query) (value : NativeLookupRequestWire.Row) (fuel : ℕ) :=
  (OracleProgram.run (NativeGoldPcsPrelude.protocol description parameters parent root q value proof fuel) world).run
private noncomputable def completed := execute opening query claimed 18
private noncomputable def events : List NativeTranscript.Observation := [.hash nativeHashInput0 nativeHashOutput0,.start nativeStart0] ++
  (List.range 18).map (fun index => .output nativeStart0 (index*8) ((nativeStream0.drop (index*8)).take 8)) ++ [.start nativeStart1,.output nativeStart1 0 nativeStream1]
example : NativeGoldPcsArithmetic.finish parameters.numVariables.val parameters.width.val
    parameters.leftVariables.val query.models opening.evaluation.val = some claimed.val := by decide +kernel
example : NativeGoldPcsWire.queryCodec.encode query = nativeQuery := by decide +kernel
example : NativeGoldPcsOpening.codec.encode opening = nativeOpeningBytes := by decide +kernel
example : NativeGoldPcsOpening.codec.read (nativeOpeningBytes ++ [byte 88]) = some (opening,[byte 88]) := by
  rw [← show NativeGoldPcsOpening.codec.encode opening = nativeOpeningBytes from by decide +kernel]
  exact NativeGoldPcsOpening.read_prefix _ _
example : NativeBrakedownContext.input description.row parameters = some nativeHashInput0 := by decide +kernel
example : (NativeBrakedownParameters.build description parameters).map (fun geometry =>
  ([geometry.columns,geometry.blocks,geometry.blockWidth,geometry.rows,geometry.columnWords,geometry.responseWords,geometry.height,geometry.randomCount.val] : List ℕ)) =
    some [2,32,2,6,12,6,5,18] := by decide +kernel
example : (match completed.1 with | .sampling _ (.finished _ _) => true | _ => false) = true := by decide +kernel
example : (match completed.1 with | .sampling _ (.finished state _) => some state.values | _ => none) = some [9006852650750938612, 14640957084096262003, 9854509489887128708, 9644174246397643206, 6277422940221709385, 10279636647838546132, 16906197915117412805, 17009151044929302110, 11602235440486293253, 18096152153882804454, 16866502560695958133, 7843068391247455882, 4609502687908310470, 15375860440544483837, 592352637967683537, 10551492528840311662, 16065408205054275817, 15084310034826379023] := by decide +kernel
example : completed.2 = events := by decide +kernel
example : (match completed.1 with | .sampling _ (.finished _ next) => some (NativeTranscript.requestInput (NativeIndexRequest.prepare (NativeGoldPcsWire.bindResponses next opening.test opening.evaluation) (usize 32))
  (NativeTranscript.utf8 "mw atomic column block v5") 8) | _ => none) = some nativeStart2 := by decide +kernel
example : (match (execute opening query claimed 0).1 with | .sampling _ (.suspended state) => some (state.remaining,state.values,state.phase.consumed.length) | _ => none) = some (18,[],0) := by decide +kernel
example : (execute opening query claimed 0).2 = [.hash nativeHashInput0 nativeHashOutput0,.start nativeStart0] := by decide +kernel
example : (match (execute opening query claimed 17).1 with | .sampling _ (.suspended state) => some (state.remaining,state.values.length,state.phase.consumed.length) | _ => none) = some (1,17,136) := by decide +kernel
-- Response contents are bound after the random test, not before it.
private noncomputable def changedResponse : NativeGoldPcsOpening.Opening := {opening with test := row [0,0,0,0,0,0] (by decide)}
example : (execute changedResponse query claimed 18).2 = events := by decide +kernel
example : (match completed.1 with | .sampling _ (.finished _ next) => some (NativeTranscript.requestInput
    (NativeIndexRequest.prepare (NativeGoldPcsWire.bindResponses next changedResponse.test opening.evaluation) (usize 32))
    (NativeTranscript.utf8 "mw atomic column block v5") 8) | _ => none) ≠ some nativeStart2 := by decide +kernel
private noncomputable def rejectedShape (proof : NativeGoldPcsOpening.Opening) := match (execute proof query claimed 18).1 with | .rejected .proofShape => true | _ => false
private noncomputable def shortTest : NativeGoldPcsOpening.Opening := {opening with test := row [0] (by decide)}
private noncomputable def shortEvaluation : NativeGoldPcsOpening.Opening := {opening with evaluation := row [0] (by decide)}
private noncomputable def emptyColumns : NativeGoldPcsOpening.Opening := {opening with columns := ⟨[],by decide⟩}
private noncomputable def column : NativeGoldColumnAuthentication.Column := opening.columns.val[0]' (by decide)
private noncomputable def extraColumns : NativeGoldPcsOpening.Opening := {opening with columns := ⟨[column,column],by decide⟩}
private noncomputable def shortColumn : NativeGoldPcsOpening.Opening := {opening with columns := ⟨[{column with values := row [0] (by decide)}],by decide⟩}
private noncomputable def shortPath : NativeGoldPcsOpening.Opening := {opening with columns := ⟨[{column with path := ⟨[],by decide⟩}],by decide⟩}
example : [shortTest,shortEvaluation,emptyColumns,extraColumns,shortColumn,shortPath].map rejectedShape = List.replicate 6 true := by decide +kernel
example : [shortTest,shortEvaluation,emptyColumns,extraColumns,shortColumn,shortPath].map (fun proof => (execute proof query claimed 18).2.length) = List.replicate 6 0 := by decide +kernel
private noncomputable def shortQuery : NativeGoldPcsWire.Query := ⟨query.val.take 1,by decide⟩
private noncomputable def smallMatrix : NativeGoldPcsWire.Matrix := ⟨usize 2,row [0,0,0,0] (by decide)⟩
private noncomputable def wrongMatrix : NativeGoldPcsWire.Query := ⟨[(smallMatrix,(query.val[0]' (by decide)).2),query.val[1]' (by decide)],by decide⟩
example : (match (execute opening shortQuery claimed 18).1 with | .rejected .binding => true | _ => false) = true := by decide +kernel
example : (execute opening shortQuery claimed 18).2.length = 0 := by decide +kernel
example : (match (execute opening wrongMatrix claimed 18).1 with | .rejected .binding => true | _ => false) = true := by decide +kernel
example : (execute opening wrongMatrix claimed 18).2.length = 0 := by decide +kernel
example : (match (execute opening query (row [1,2] (by decide)) 18).1 with | .rejected .binding => true | _ => false) = true := by decide +kernel
example : (execute opening query (row [1,2] (by decide)) 18).2.length = 0 := by decide +kernel
private noncomputable def failedDescription : NativeBrakedownParameters.Description Unit := {description with row := {description.row with serialize := fun _ => none}}
private noncomputable def serializationFailure := (OracleProgram.run (NativeGoldPcsPrelude.protocol failedDescription parameters parent root query claimed opening 18) world).run
example : (match serializationFailure.1 with | .rejected .binding => true | _ => false) = true := by decide +kernel
example : serializationFailure.2.length = 0 := by decide +kernel
private noncomputable def changed (n width left quota : ℕ) : NativeBrakedownContext.Parameters Unit := ⟨usize n,usize width,usize left,usize quota,()⟩
example : [changed 2 0 1 1,changed 2 3 3 1,changed 64 3 1 1,changed 2 3 1 0,changed 3 3 1 1,changed 63 3 62 1,changed 1 (2^32) 0 1].map
    (fun params => (NativeBrakedownParameters.build description params).isNone) = List.replicate 7 true := by decide +kernel
example : (NativeBrakedownParameters.build description (changed (2^64-1) 3 0 1)).isNone = true := by decide +kernel
example : (NativeBrakedownParameters.build description (changed 2 3 1 (2^64-1))).isSome = true := by decide +kernel
private noncomputable def nonpower : NativeBrakedownParameters.Description Unit := {description with row := {description.row with blocks := fun _ => usize 3}}
example : (NativeBrakedownParameters.build nonpower parameters).map (fun geometry => (geometry.blocks,geometry.height)) = some (3,2) := by decide +kernel
example : NativeIndexRequest.check (usize 3) (usize 1) = false := by decide +kernel
-- The same original opening now executes through the atomic column boundary.
private noncomputable def columnsRun (proof : NativeGoldPcsOpening.Opening) (fuel : ℕ) :=
  (OracleProgram.run (NativeGoldPcsColumns.protocol description parameters parent root query claimed proof fuel) world).run
private noncomputable def columnsCompleted := columnsRun opening 18
example : (match columnsCompleted.1 with | .columns _ _ _ _ => true | _ => false) = true := by decide +kernel
example : columnsCompleted.2 = events ++ [.start nativeStart2,.output nativeStart2 0 nativeStream2] := by decide +kernel
example : (match columnsCompleted.1 with | .columns _ _ _ sample => some (sample.draws,sample.indices) | _ => none) =
  some ([27],[27]) := by decide +kernel
example : (match columnsCompleted.1 with | .columns _ state _ _ => some ((NativeGoldPcsColumns.random state).map Fin.val) | _ => none) =
  (match completed.1 with | .sampling _ (.finished state _) => some state.values | _ => none) := by decide +kernel
example : (match columnsCompleted.1 with | .columns _ _ weights _ => some (weights.map Fin.val) | _ => none) =
  some [18446744069414584320, 18446744069414584286, 18446744069414584300, 2, 35, 21, 18446744069414584318, 18446744069414584320, 18446744069414584286, 3, 2, 35, 18446744069414584316, 18446744069414584318, 18446744069414584320, 5, 3, 2] := by decide +kernel
-- No later authentication operation appends a frame to the parent transcript.
-- This compares the next reader input only; the model has not accepted PCS.
example : (match columnsCompleted.1 with
  | .columns _ _ _ sample => some (NativeTranscript.requestInput sample.transcript (NativeTranscript.utf8 "after PCS verification fixture") 4)
  | _ => none) = some nativeAfterColumns := by decide +kernel
example : (columnsRun opening 0).2 = (execute opening query claimed 0).2 := by decide +kernel
example : (match (columnsRun opening 0).1 with | .suspended _ state => some (state.remaining,state.values.length) | _ => none) =
  some (18,0) := by decide +kernel
example : (columnsRun opening 17).2 = (execute opening query claimed 17).2 := by decide +kernel
example : (match (columnsRun opening 17).1 with | .suspended _ state => some (state.remaining,state.values.length) | _ => none) =
  some (1,17) := by decide +kernel
example : (match (columnsRun shortTest 18).1 with | .rejected (.prelude .proofShape) => true | _ => false) = true := by decide +kernel
example : (columnsRun shortTest 18).2 = [] := by decide +kernel
example : (columnsRun changedResponse 18).2.take events.length = events := by decide +kernel
example : (match (columnsRun changedResponse 18).1 with | .columns _ _ _ sample => some sample.indices | _ => none) =
  some [31] := by decide +kernel
example : (columnsRun changedResponse 18).2 ≠ columnsCompleted.2 := by decide +kernel
-- Direct continuation probes distinguish defensive failures from main-entry checks.
private noncomputable def fieldGeometry : NativeBrakedownParameters.Geometry :=
  (NativeBrakedownParameters.build description parameters).getD ⟨0,0,0,0,0,0,0,0,usize 0⟩
private noncomputable def fieldState : NativeFieldVector.State := match completed.1 with
  | .sampling _ (.finished state _) => state
  | _ => NativeFieldVector.initial ⟨parent,[],[]⟩ 0
private noncomputable def fieldNext : NativeTranscript.Transcript := match completed.1 with
  | .sampling _ (.finished _ next) => next | _ => parent
private noncomputable def after (desc : NativeBrakedownParameters.Description Unit)
    (params : NativeBrakedownContext.Parameters Unit) (q : NativeGoldPcsWire.Query) (proof : NativeGoldPcsOpening.Opening) :=
  (OracleProgram.run (NativeGoldPcsColumns.afterField desc params q proof fieldGeometry (.finished fieldState fieldNext)) world).run
example : (match (after nonpower parameters query opening).1 with | .atomicUnavailable _ => true | _ => false) = true := by decide +kernel
example : (after nonpower parameters query opening).2 = [] := by decide +kernel
example : (match (after description (changed 2 3 1 (2^64-1)) query opening).1 with | .atomicUnavailable _ => true | _ => false) = true := by decide +kernel
example : (after description (changed 2 3 1 (2^64-1)) query opening).2 = [] := by decide +kernel
example : (match (after description parameters ⟨[],by decide⟩ opening).1 with | .rejected .structured => true | _ => false) = true := by decide +kernel
example : (after description parameters ⟨[],by decide⟩ opening).2 = [] := by decide +kernel
example : (match (after description parameters query extraColumns).1 with | .rejected .distinctCount => true | _ => false) = true := by decide +kernel
example : (after description parameters query extraColumns).2 = [.start nativeStart2,.output nativeStart2 0 nativeStream2] := by decide +kernel

-- The retained native code now supplies both context serialization and encoding.
private noncomputable def blockPlanRoot : NativeGoldSolinas.Word := ⟨549755813888,by decide⟩
private noncomputable def blockTables : NativeGoldBlockCode.Tables :=
  ⟨fun log => decide (log=5),fun _ => true,fun log => if log=5 then some blockPlanRoot else none⟩
private noncomputable def retainedCode : NativeGoldBlockCode.Stored :=
  ⟨usize 2,usize 2,usize 1,usize 32,NativeBrakedownContext.modulus,usize 549755813888⟩
private noncomputable def retainedParameters : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored :=
  ⟨usize 2,usize 3,usize 1,usize 1,retainedCode⟩
example : NativeGoldBlockCode.build blockTables (usize 2) (usize 2) (usize 2) = .ok retainedCode := by decide +kernel
example : NativeBrakedownContext.input NativeGoldBlockCode.description.row retainedParameters = some nativeHashInput0 := by decide +kernel
private noncomputable def encodingRun (proof : NativeGoldPcsOpening.Opening) (fuel : ℕ) :=
  (OracleProgram.run (NativeGoldPcsEncoding.protocol blockTables retainedParameters parent root query claimed proof fuel) world).run
private noncomputable def encodingCompleted := encodingRun opening 18
example : (match encodingCompleted.1 with
  | .encoded _ _ _ sample plan test evaluation => some (sample.indices,plan.val,test.length,evaluation.length)
  | _ => none) = some ([27],549755813888,192,192) := by decide +kernel
example : encodingCompleted.2 = events ++ [.start nativeStart2,.output nativeStart2 0 nativeStream2] := by decide +kernel
example : (match encodingCompleted.1 with | .encoded _ _ _ _ _ test _ => some (test.map Fin.val) | _ => none) =
  some (((List.replicate 32 [10663165317240926990,18396346353517193167]).flatten) ++
    ((List.replicate 32 [16715989892425570710,11700256917557985223]).flatten) ++
    ((List.replicate 32 [3430785603203941070,8169463425760920726]).flatten)) := by decide +kernel
example : (match encodingCompleted.1 with | .encoded _ _ _ _ _ _ evaluation => some (evaluation.map Fin.val) | _ => none) =
  some (((List.replicate 32 [174,180]).flatten) ++ ((List.replicate 32 [121,127]).flatten) ++
    ((List.replicate 32 [32,38]).flatten)) := by decide +kernel
example : (match (encodingRun opening 0).1 with | .prefix (.suspended _ _) => true | _ => false) = true := by decide +kernel
example : (encodingRun opening 0).2 = (execute opening query claimed 0).2 := by decide +kernel
example : (match (encodingRun shortTest 18).1 with | .prefix (.rejected (.prelude .proofShape)) => true | _ => false) = true := by decide +kernel
example : (encodingRun shortTest 18).2 = [] := by decide +kernel
example : (match NativeGoldPcsEncoding.continueColumns {blockTables with load := fun _ => none}
    retainedParameters opening columnsCompleted.1 with | .encodingUnavailable => true | _ => false) = true := by decide +kernel
example : (match NativeGoldPcsEncoding.continueColumns {blockTables with load := fun _ => some ⟨1,by decide⟩}
    retainedParameters opening columnsCompleted.1 with | .encodingUnavailable => true | _ => false) = true := by decide +kernel

private noncomputable def preparedRun :=
  (OracleProgram.run (NativeGoldPcsWorkers.protocol blockTables retainedParameters parent root query claimed opening 18) world).run
example : (match preparedRun.1 with
  | .prepared work => some (work.width,work.jobs.map NativeGoldColumnWorker.Job.index,work.test.length,work.evaluation.length)
  | _ => none) = some (3,[27],192,192) := by decide +kernel
example : preparedRun.2 = events ++ [.start nativeStart2,.output nativeStart2 0 nativeStream2] := by decide +kernel
example : (match preparedRun.1 with
  | .prepared work => some (work.jobs.map NativeGoldColumnWorker.Job.column)
  | _ => none) = some opening.columns.val := by decide +kernel

-- Test-only single-worker handoff for the native one-column fixture.
private noncomputable def authHashInput1 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 99, 111, 108, 117, 109, 110, 47, 118, 49, 12, 0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11] : List ℕ).map byte
private noncomputable def authHashOutput1 : InputIndexedOracle.Input := ([173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2] : List ℕ).map byte
private noncomputable def authHashInput2 : InputIndexedOracle.Input := ([173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2, 173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2] : List ℕ).map byte
private noncomputable def authHashOutput2 : InputIndexedOracle.Input := ([76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179] : List ℕ).map byte
private noncomputable def authHashInput3 : InputIndexedOracle.Input := ([76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179, 76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179] : List ℕ).map byte
private noncomputable def authHashOutput3 : InputIndexedOracle.Input := ([177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42] : List ℕ).map byte
private noncomputable def authHashInput4 : InputIndexedOracle.Input := ([177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42, 177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42] : List ℕ).map byte
private noncomputable def authHashOutput4 : InputIndexedOracle.Input := ([134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84] : List ℕ).map byte
private noncomputable def authHashInput5 : InputIndexedOracle.Input := ([134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84, 134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84] : List ℕ).map byte
private noncomputable def authHashOutput5 : InputIndexedOracle.Input := ([28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166] : List ℕ).map byte
private noncomputable def authHashInput6 : InputIndexedOracle.Input := ([28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166, 28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166] : List ℕ).map byte
private noncomputable def authHashOutput6 : InputIndexedOracle.Input := ([222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201] : List ℕ).map byte
private noncomputable def authHashPairs : List (InputIndexedOracle.Input × InputIndexedOracle.Input) := [(authHashInput1,authHashOutput1),(authHashInput2,authHashOutput2),(authHashInput3,authHashOutput3),(authHashInput4,authHashOutput4),(authHashInput5,authHashOutput5),(authHashInput6,authHashOutput6)]
private noncomputable def fullWorld : InputIndexedOracle.World
  | .inl key => world (.inl key)
  | .inr (input,index) => if input=nativeHashInput0 then nativeHashOutput0[index.val]?.getD (byte 255) else
    match authHashPairs.find? (fun pair => pair.1=input) with
    | none => byte 255
    | some pair => pair.2[index.val]?.getD (byte 255)
private noncomputable def oneWorkerHandoff := OracleProgram.bind
  (NativeGoldPcsWorkers.protocol blockTables retainedParameters parent root query claimed opening 18)
  (fun result => match result with
    | .prepared work => match work.jobs with
      | [job] => NativeHashOracleBridge.compile (NativeGoldColumnWorker.worker work.geometry work.width work.random
          work.structured work.test work.evaluation work.root job.index job.column)
      | _ => .pure false
    | _ => .pure false)
private noncomputable def authenticated := (OracleProgram.run oneWorkerHandoff fullWorld).run
example : authenticated.1 = true := by decide +kernel
example : authenticated.2 = events ++ [.start nativeStart2,.output nativeStart2 0 nativeStream2] ++
  [.hash authHashInput1 authHashOutput1,.hash authHashInput2 authHashOutput2,.hash authHashInput3 authHashOutput3,.hash authHashInput4 authHashOutput4,.hash authHashInput5 authHashOutput5,.hash authHashInput6 authHashOutput6] := by decide +kernel

example : (match preparedRun.1 with
  | .prepared work => (NativeGoldPcsRawAvailability.prepare (fun _ : Unit => 5) () work).map
      (List.map (fun entry => (entry.1.index,entry.2.position.val,entry.2.siblings.toList.length)))
  | _ => none) = some [(27,27,5)] := by decide +kernel
example : (match preparedRun.1 with
  | .prepared work => (NativeGoldPcsRawAvailability.prepare (fun _ : Unit => 5) () work).map
      (List.map (fun entry => entry.2.payload))
  | _ => none) = some (opening.columns.val.map NativeGoldColumnAuthentication.Column.values) := by decide +kernel

example : (match columnsCompleted.1 with
  | .columns geometry _ _ sample => (NativeGoldPcsDraws.typed geometry.height parameters.queries.val sample.draws).map
      (fun draw => (List.ofFn draw).map Fin.val)
  | _ => none) = some [27] := by decide +kernel

end NativePcsPreludeSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeBrakedownParameters.build_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBrakedownParameters.build_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeBrakedownParameters.build_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBrakedownParameters.build_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeBrakedownParameters.computed_sizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBrakedownParameters.computed_sizes

/-- info: 'FormalProof4FHE.HasteBoots.NativeBrakedownParameters.leaves_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBrakedownParameters.leaves_cover

/-- info: 'FormalProof4FHE.HasteBoots.NativeBrakedownParameters.height_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBrakedownParameters.height_minimal

/-- info: 'FormalProof4FHE.HasteBoots.NativeBrakedownParameters.path_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBrakedownParameters.path_shift

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsOpening.check_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsOpening.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsOpening.encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsOpening.encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsOpening.read_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsOpening.read_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.check_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.coefficients_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.coefficients_check

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.appendBound_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.appendBound_input

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.rejected

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.serialization_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.serialization_failure

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.accepted

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude.run_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude.run_protocol

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude.sampling_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude.sampling_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude.finished_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude.finished_values

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude.proofShape_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude.proofShape_rejected

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.calls_members' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.calls_members

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.calls_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.calls_checked

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.completed_binding_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers.completed_binding_checks

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.run_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.run_protocol

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.run_afterField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.run_afterField

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.suspended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.suspended

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.columns_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.columns_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.columns_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.columns_observations

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.atomic_unavailable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumns.atomic_unavailable

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape.square_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape.square_bound

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape.binding_models' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape.binding_models

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape.finished_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape.finished_structure

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape.columns_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape.columns_shape

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.bound_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsBinding.bound_check
