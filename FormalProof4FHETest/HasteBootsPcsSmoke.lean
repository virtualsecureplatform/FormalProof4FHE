module

import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.OracleProgram
import all FormalProof4FHE.HasteBoots.NativeGoldPcsWire
import all FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication

/-! Native Goldilocks fixtures from HasteBoots dff353006322693cab3dc6b654f82151f658f294.
The fixture extracts hash_column unchanged and calls the public MerkleTree checker,
coefficients_query and standard bincode serializer. SHA outputs are recorded
ideal-world answers; these tests do not prove Rust or SHA implementation correctness. -/

namespace NativePcsAuthenticationSmoke
open FormalProof4FHE.HasteBoots
open NativeGoldColumnAuthentication
local instance : DecidableEq NativeRootMessage.Digest := digestDecidableEq
private noncomputable def byte (n : ℕ) : InputIndexedOracle.Byte := ⟨n % 256,Nat.mod_lt _ (by decide)⟩
private noncomputable def word (n : ℕ) : NativeFieldRepresentation.GoldWord := ⟨n % (2^64),Nat.mod_lt _ (by decide)⟩
private noncomputable def digestOf (input : InputIndexedOracle.Input) : NativeRootMessage.Digest := fun index => input[index.val]?.getD (byte 255)
private noncomputable def nativeRoot : InputIndexedOracle.Input := ([142, 34, 250, 4, 166, 186, 7, 222, 95, 6, 108, 2, 76, 148, 237, 14, 178, 85, 179, 53, 193, 99, 98, 228, 3, 243, 240, 127, 203, 64, 123, 251, 72, 135, 134, 205, 19, 209, 115, 181, 62, 125, 73, 146, 115, 190, 64, 234, 229, 177, 29, 174, 25, 161, 137, 156, 123, 202, 139, 217, 23, 86, 23, 117] : List ℕ).map byte
private noncomputable def nativeQuery : InputIndexedOracle.Input := ([1, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2] : List ℕ).map byte
private noncomputable def nativeOpening : InputIndexedOracle.Input := ([142, 34, 250, 4, 166, 186, 7, 222, 95, 6, 108, 2, 76, 148, 237, 14, 178, 85, 179, 53, 193, 99, 98, 228, 3, 243, 240, 127, 203, 64, 123, 251, 72, 135, 134, 205, 19, 209, 115, 181, 62, 125, 73, 146, 115, 190, 64, 234, 229, 177, 29, 174, 25, 161, 137, 156, 123, 202, 139, 217, 23, 86, 23, 117, 1, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 251, 251, 0, 253, 255, 255, 255, 255, 255, 255, 255, 255, 252, 0, 0, 1, 0] : List ℕ).map byte
private noncomputable def nativeClaim : InputIndexedOracle.Input := ([251, 251, 0, 252, 0, 0, 1, 0, 1, 3, 9, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 236, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 253, 222, 255, 255, 255, 254, 255, 255, 255, 253, 252, 255, 255, 255, 254, 255, 255, 255, 253, 254, 255, 255, 255, 254, 255, 255, 255, 253, 0, 0, 0, 0, 255, 255, 255, 255, 3, 9, 2, 35, 21, 3, 2, 35, 5, 3, 2, 3, 251, 251, 0, 253, 255, 255, 255, 255, 255, 255, 255, 255, 252, 0, 0, 1, 0] : List ℕ).map byte
private noncomputable def nativeColumn0 : InputIndexedOracle.Input := ([2, 0, 251, 251, 0, 3, 78, 68, 80, 183, 82, 57, 185, 92, 73, 231, 13, 229, 125, 245, 222, 70, 10, 254, 153, 30, 220, 146, 71, 216, 30, 188, 1, 195, 166, 163, 27, 165, 68, 149, 34, 220, 102, 124, 227, 231, 107, 240, 161, 93, 207, 104, 130, 186, 129, 36, 253, 223, 105, 120, 70, 87, 186, 3, 38, 11, 186, 108, 229, 65, 24, 38, 104, 232, 13, 97, 95, 221, 91, 48, 24, 202, 168, 249, 46, 123, 122, 160, 121, 189, 44, 129, 58, 209, 110, 153, 223, 135, 28, 106, 151, 123, 61, 129, 181, 164, 79, 114, 106, 94, 9, 152, 72, 210, 106, 190, 196, 249, 165, 196, 70, 80, 104, 170, 135, 190, 94, 157, 96, 15, 38, 28, 44, 35, 152, 173, 243, 33, 1, 178, 76, 168, 233, 164, 90, 125, 2, 9, 165, 115, 242, 104, 110, 254, 83, 41, 28, 73, 139, 37, 13, 206, 85, 31, 188, 61, 114, 0, 45, 82, 142, 220, 74, 123, 136, 206, 134, 31, 206, 13, 204, 226, 109, 17, 159, 8, 107, 223, 33, 21, 222, 0, 102, 235, 51, 142, 151, 155] : List ℕ).map byte
private noncomputable def path0_0 : InputIndexedOracle.Input := ([78, 68, 80, 183, 82, 57, 185, 92, 73, 231, 13, 229, 125, 245, 222, 70, 10, 254, 153, 30, 220, 146, 71, 216, 30, 188, 1, 195, 166, 163, 27, 165, 68, 149, 34, 220, 102, 124, 227, 231, 107, 240, 161, 93, 207, 104, 130, 186, 129, 36, 253, 223, 105, 120, 70, 87, 186, 3, 38, 11, 186, 108, 229, 65] : List ℕ).map byte
private noncomputable def path0_1 : InputIndexedOracle.Input := ([24, 38, 104, 232, 13, 97, 95, 221, 91, 48, 24, 202, 168, 249, 46, 123, 122, 160, 121, 189, 44, 129, 58, 209, 110, 153, 223, 135, 28, 106, 151, 123, 61, 129, 181, 164, 79, 114, 106, 94, 9, 152, 72, 210, 106, 190, 196, 249, 165, 196, 70, 80, 104, 170, 135, 190, 94, 157, 96, 15, 38, 28, 44, 35] : List ℕ).map byte
private noncomputable def path0_2 : InputIndexedOracle.Input := ([152, 173, 243, 33, 1, 178, 76, 168, 233, 164, 90, 125, 2, 9, 165, 115, 242, 104, 110, 254, 83, 41, 28, 73, 139, 37, 13, 206, 85, 31, 188, 61, 114, 0, 45, 82, 142, 220, 74, 123, 136, 206, 134, 31, 206, 13, 204, 226, 109, 17, 159, 8, 107, 223, 33, 21, 222, 0, 102, 235, 51, 142, 151, 155] : List ℕ).map byte
private noncomputable def input0_0 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 99, 111, 108, 117, 109, 110, 47, 118, 49, 2, 0, 251, 251, 0] : List ℕ).map byte
private noncomputable def output0_0 : InputIndexedOracle.Input := ([78, 68, 80, 183, 82, 57, 185, 92, 73, 231, 13, 229, 125, 245, 222, 70, 10, 254, 153, 30, 220, 146, 71, 216, 30, 188, 1, 195, 166, 163, 27, 165, 68, 149, 34, 220, 102, 124, 227, 231, 107, 240, 161, 93, 207, 104, 130, 186, 129, 36, 253, 223, 105, 120, 70, 87, 186, 3, 38, 11, 186, 108, 229, 65] : List ℕ).map byte
private noncomputable def input0_1 : InputIndexedOracle.Input := ([78, 68, 80, 183, 82, 57, 185, 92, 73, 231, 13, 229, 125, 245, 222, 70, 10, 254, 153, 30, 220, 146, 71, 216, 30, 188, 1, 195, 166, 163, 27, 165, 68, 149, 34, 220, 102, 124, 227, 231, 107, 240, 161, 93, 207, 104, 130, 186, 129, 36, 253, 223, 105, 120, 70, 87, 186, 3, 38, 11, 186, 108, 229, 65, 24, 38, 104, 232, 13, 97, 95, 221, 91, 48, 24, 202, 168, 249, 46, 123, 122, 160, 121, 189, 44, 129, 58, 209, 110, 153, 223, 135, 28, 106, 151, 123, 61, 129, 181, 164, 79, 114, 106, 94, 9, 152, 72, 210, 106, 190, 196, 249, 165, 196, 70, 80, 104, 170, 135, 190, 94, 157, 96, 15, 38, 28, 44, 35] : List ℕ).map byte
private noncomputable def output0_1 : InputIndexedOracle.Input := ([158, 172, 63, 202, 89, 183, 63, 157, 45, 86, 99, 71, 152, 90, 174, 10, 89, 162, 181, 100, 75, 173, 119, 226, 51, 174, 145, 126, 10, 184, 102, 68, 191, 129, 126, 142, 136, 238, 170, 157, 58, 209, 18, 31, 31, 115, 31, 3, 206, 14, 26, 196, 95, 65, 251, 169, 88, 155, 243, 53, 3, 19, 186, 51] : List ℕ).map byte
private noncomputable def input0_2 : InputIndexedOracle.Input := ([158, 172, 63, 202, 89, 183, 63, 157, 45, 86, 99, 71, 152, 90, 174, 10, 89, 162, 181, 100, 75, 173, 119, 226, 51, 174, 145, 126, 10, 184, 102, 68, 191, 129, 126, 142, 136, 238, 170, 157, 58, 209, 18, 31, 31, 115, 31, 3, 206, 14, 26, 196, 95, 65, 251, 169, 88, 155, 243, 53, 3, 19, 186, 51, 152, 173, 243, 33, 1, 178, 76, 168, 233, 164, 90, 125, 2, 9, 165, 115, 242, 104, 110, 254, 83, 41, 28, 73, 139, 37, 13, 206, 85, 31, 188, 61, 114, 0, 45, 82, 142, 220, 74, 123, 136, 206, 134, 31, 206, 13, 204, 226, 109, 17, 159, 8, 107, 223, 33, 21, 222, 0, 102, 235, 51, 142, 151, 155] : List ℕ).map byte
private noncomputable def output0_2 : InputIndexedOracle.Input := ([142, 34, 250, 4, 166, 186, 7, 222, 95, 6, 108, 2, 76, 148, 237, 14, 178, 85, 179, 53, 193, 99, 98, 228, 3, 243, 240, 127, 203, 64, 123, 251, 72, 135, 134, 205, 19, 209, 115, 181, 62, 125, 73, 146, 115, 190, 64, 234, 229, 177, 29, 174, 25, 161, 137, 156, 123, 202, 139, 217, 23, 86, 23, 117] : List ℕ).map byte
private noncomputable def column0 : Column := ⟨⟨([0, 251] : List ℕ).map word,by decide⟩,⟨[digestOf path0_0,digestOf path0_1,digestOf path0_2],by decide⟩⟩
private noncomputable def events0 : List NativeTranscript.Observation := [.hash input0_0 output0_0,.hash input0_1 output0_1,.hash input0_2 output0_2]
private noncomputable def nativeColumn1 : InputIndexedOracle.Input := ([2, 1, 252, 0, 0, 1, 0, 3, 24, 38, 104, 232, 13, 97, 95, 221, 91, 48, 24, 202, 168, 249, 46, 123, 122, 160, 121, 189, 44, 129, 58, 209, 110, 153, 223, 135, 28, 106, 151, 123, 61, 129, 181, 164, 79, 114, 106, 94, 9, 152, 72, 210, 106, 190, 196, 249, 165, 196, 70, 80, 104, 170, 135, 190, 94, 157, 96, 15, 38, 28, 44, 35, 78, 68, 80, 183, 82, 57, 185, 92, 73, 231, 13, 229, 125, 245, 222, 70, 10, 254, 153, 30, 220, 146, 71, 216, 30, 188, 1, 195, 166, 163, 27, 165, 68, 149, 34, 220, 102, 124, 227, 231, 107, 240, 161, 93, 207, 104, 130, 186, 129, 36, 253, 223, 105, 120, 70, 87, 186, 3, 38, 11, 186, 108, 229, 65, 152, 173, 243, 33, 1, 178, 76, 168, 233, 164, 90, 125, 2, 9, 165, 115, 242, 104, 110, 254, 83, 41, 28, 73, 139, 37, 13, 206, 85, 31, 188, 61, 114, 0, 45, 82, 142, 220, 74, 123, 136, 206, 134, 31, 206, 13, 204, 226, 109, 17, 159, 8, 107, 223, 33, 21, 222, 0, 102, 235, 51, 142, 151, 155] : List ℕ).map byte
private noncomputable def path1_0 : InputIndexedOracle.Input := ([24, 38, 104, 232, 13, 97, 95, 221, 91, 48, 24, 202, 168, 249, 46, 123, 122, 160, 121, 189, 44, 129, 58, 209, 110, 153, 223, 135, 28, 106, 151, 123, 61, 129, 181, 164, 79, 114, 106, 94, 9, 152, 72, 210, 106, 190, 196, 249, 165, 196, 70, 80, 104, 170, 135, 190, 94, 157, 96, 15, 38, 28, 44, 35] : List ℕ).map byte
private noncomputable def path1_1 : InputIndexedOracle.Input := ([78, 68, 80, 183, 82, 57, 185, 92, 73, 231, 13, 229, 125, 245, 222, 70, 10, 254, 153, 30, 220, 146, 71, 216, 30, 188, 1, 195, 166, 163, 27, 165, 68, 149, 34, 220, 102, 124, 227, 231, 107, 240, 161, 93, 207, 104, 130, 186, 129, 36, 253, 223, 105, 120, 70, 87, 186, 3, 38, 11, 186, 108, 229, 65] : List ℕ).map byte
private noncomputable def path1_2 : InputIndexedOracle.Input := ([152, 173, 243, 33, 1, 178, 76, 168, 233, 164, 90, 125, 2, 9, 165, 115, 242, 104, 110, 254, 83, 41, 28, 73, 139, 37, 13, 206, 85, 31, 188, 61, 114, 0, 45, 82, 142, 220, 74, 123, 136, 206, 134, 31, 206, 13, 204, 226, 109, 17, 159, 8, 107, 223, 33, 21, 222, 0, 102, 235, 51, 142, 151, 155] : List ℕ).map byte
private noncomputable def input1_0 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 99, 111, 108, 117, 109, 110, 47, 118, 49, 2, 1, 252, 0, 0, 1, 0] : List ℕ).map byte
private noncomputable def output1_0 : InputIndexedOracle.Input := ([24, 38, 104, 232, 13, 97, 95, 221, 91, 48, 24, 202, 168, 249, 46, 123, 122, 160, 121, 189, 44, 129, 58, 209, 110, 153, 223, 135, 28, 106, 151, 123, 61, 129, 181, 164, 79, 114, 106, 94, 9, 152, 72, 210, 106, 190, 196, 249, 165, 196, 70, 80, 104, 170, 135, 190, 94, 157, 96, 15, 38, 28, 44, 35] : List ℕ).map byte
private noncomputable def input1_1 : InputIndexedOracle.Input := ([78, 68, 80, 183, 82, 57, 185, 92, 73, 231, 13, 229, 125, 245, 222, 70, 10, 254, 153, 30, 220, 146, 71, 216, 30, 188, 1, 195, 166, 163, 27, 165, 68, 149, 34, 220, 102, 124, 227, 231, 107, 240, 161, 93, 207, 104, 130, 186, 129, 36, 253, 223, 105, 120, 70, 87, 186, 3, 38, 11, 186, 108, 229, 65, 24, 38, 104, 232, 13, 97, 95, 221, 91, 48, 24, 202, 168, 249, 46, 123, 122, 160, 121, 189, 44, 129, 58, 209, 110, 153, 223, 135, 28, 106, 151, 123, 61, 129, 181, 164, 79, 114, 106, 94, 9, 152, 72, 210, 106, 190, 196, 249, 165, 196, 70, 80, 104, 170, 135, 190, 94, 157, 96, 15, 38, 28, 44, 35] : List ℕ).map byte
private noncomputable def output1_1 : InputIndexedOracle.Input := ([158, 172, 63, 202, 89, 183, 63, 157, 45, 86, 99, 71, 152, 90, 174, 10, 89, 162, 181, 100, 75, 173, 119, 226, 51, 174, 145, 126, 10, 184, 102, 68, 191, 129, 126, 142, 136, 238, 170, 157, 58, 209, 18, 31, 31, 115, 31, 3, 206, 14, 26, 196, 95, 65, 251, 169, 88, 155, 243, 53, 3, 19, 186, 51] : List ℕ).map byte
private noncomputable def input1_2 : InputIndexedOracle.Input := ([158, 172, 63, 202, 89, 183, 63, 157, 45, 86, 99, 71, 152, 90, 174, 10, 89, 162, 181, 100, 75, 173, 119, 226, 51, 174, 145, 126, 10, 184, 102, 68, 191, 129, 126, 142, 136, 238, 170, 157, 58, 209, 18, 31, 31, 115, 31, 3, 206, 14, 26, 196, 95, 65, 251, 169, 88, 155, 243, 53, 3, 19, 186, 51, 152, 173, 243, 33, 1, 178, 76, 168, 233, 164, 90, 125, 2, 9, 165, 115, 242, 104, 110, 254, 83, 41, 28, 73, 139, 37, 13, 206, 85, 31, 188, 61, 114, 0, 45, 82, 142, 220, 74, 123, 136, 206, 134, 31, 206, 13, 204, 226, 109, 17, 159, 8, 107, 223, 33, 21, 222, 0, 102, 235, 51, 142, 151, 155] : List ℕ).map byte
private noncomputable def output1_2 : InputIndexedOracle.Input := ([142, 34, 250, 4, 166, 186, 7, 222, 95, 6, 108, 2, 76, 148, 237, 14, 178, 85, 179, 53, 193, 99, 98, 228, 3, 243, 240, 127, 203, 64, 123, 251, 72, 135, 134, 205, 19, 209, 115, 181, 62, 125, 73, 146, 115, 190, 64, 234, 229, 177, 29, 174, 25, 161, 137, 156, 123, 202, 139, 217, 23, 86, 23, 117] : List ℕ).map byte
private noncomputable def column1 : Column := ⟨⟨([1, 65536] : List ℕ).map word,by decide⟩,⟨[digestOf path1_0,digestOf path1_1,digestOf path1_2],by decide⟩⟩
private noncomputable def events1 : List NativeTranscript.Observation := [.hash input1_0 output1_0,.hash input1_1 output1_1,.hash input1_2 output1_2]
private noncomputable def nativeColumn3 : InputIndexedOracle.Input := ([2, 3, 253, 255, 255, 255, 255, 255, 255, 255, 255, 3, 177, 47, 6, 200, 46, 36, 220, 142, 23, 98, 230, 237, 148, 187, 240, 216, 54, 134, 217, 44, 146, 178, 90, 200, 174, 3, 98, 133, 67, 96, 93, 15, 145, 130, 116, 14, 38, 227, 57, 4, 89, 77, 51, 212, 79, 235, 149, 137, 161, 229, 36, 199, 32, 170, 74, 87, 107, 99, 215, 137, 184, 227, 94, 185, 239, 17, 13, 74, 48, 148, 91, 76, 60, 25, 158, 252, 31, 192, 133, 173, 246, 173, 240, 89, 24, 202, 165, 204, 200, 143, 48, 98, 144, 170, 143, 119, 36, 133, 41, 203, 3, 82, 172, 247, 31, 53, 120, 35, 106, 16, 26, 6, 243, 131, 138, 131, 57, 134, 181, 194, 60, 157, 93, 153, 208, 160, 197, 32, 158, 172, 63, 202, 89, 183, 63, 157, 45, 86, 99, 71, 152, 90, 174, 10, 89, 162, 181, 100, 75, 173, 119, 226, 51, 174, 145, 126, 10, 184, 102, 68, 191, 129, 126, 142, 136, 238, 170, 157, 58, 209, 18, 31, 31, 115, 31, 3, 206, 14, 26, 196, 95, 65, 251, 169, 88, 155, 243, 53, 3, 19, 186, 51] : List ℕ).map byte
private noncomputable def path3_0 : InputIndexedOracle.Input := ([177, 47, 6, 200, 46, 36, 220, 142, 23, 98, 230, 237, 148, 187, 240, 216, 54, 134, 217, 44, 146, 178, 90, 200, 174, 3, 98, 133, 67, 96, 93, 15, 145, 130, 116, 14, 38, 227, 57, 4, 89, 77, 51, 212, 79, 235, 149, 137, 161, 229, 36, 199, 32, 170, 74, 87, 107, 99, 215, 137, 184, 227, 94, 185] : List ℕ).map byte
private noncomputable def path3_1 : InputIndexedOracle.Input := ([239, 17, 13, 74, 48, 148, 91, 76, 60, 25, 158, 252, 31, 192, 133, 173, 246, 173, 240, 89, 24, 202, 165, 204, 200, 143, 48, 98, 144, 170, 143, 119, 36, 133, 41, 203, 3, 82, 172, 247, 31, 53, 120, 35, 106, 16, 26, 6, 243, 131, 138, 131, 57, 134, 181, 194, 60, 157, 93, 153, 208, 160, 197, 32] : List ℕ).map byte
private noncomputable def path3_2 : InputIndexedOracle.Input := ([158, 172, 63, 202, 89, 183, 63, 157, 45, 86, 99, 71, 152, 90, 174, 10, 89, 162, 181, 100, 75, 173, 119, 226, 51, 174, 145, 126, 10, 184, 102, 68, 191, 129, 126, 142, 136, 238, 170, 157, 58, 209, 18, 31, 31, 115, 31, 3, 206, 14, 26, 196, 95, 65, 251, 169, 88, 155, 243, 53, 3, 19, 186, 51] : List ℕ).map byte
private noncomputable def input3_0 : InputIndexedOracle.Input := ([72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 99, 111, 108, 117, 109, 110, 47, 118, 49, 2, 3, 253, 255, 255, 255, 255, 255, 255, 255, 255] : List ℕ).map byte
private noncomputable def output3_0 : InputIndexedOracle.Input := ([177, 47, 6, 200, 46, 36, 220, 142, 23, 98, 230, 237, 148, 187, 240, 216, 54, 134, 217, 44, 146, 178, 90, 200, 174, 3, 98, 133, 67, 96, 93, 15, 145, 130, 116, 14, 38, 227, 57, 4, 89, 77, 51, 212, 79, 235, 149, 137, 161, 229, 36, 199, 32, 170, 74, 87, 107, 99, 215, 137, 184, 227, 94, 185] : List ℕ).map byte
private noncomputable def input3_1 : InputIndexedOracle.Input := ([239, 17, 13, 74, 48, 148, 91, 76, 60, 25, 158, 252, 31, 192, 133, 173, 246, 173, 240, 89, 24, 202, 165, 204, 200, 143, 48, 98, 144, 170, 143, 119, 36, 133, 41, 203, 3, 82, 172, 247, 31, 53, 120, 35, 106, 16, 26, 6, 243, 131, 138, 131, 57, 134, 181, 194, 60, 157, 93, 153, 208, 160, 197, 32, 177, 47, 6, 200, 46, 36, 220, 142, 23, 98, 230, 237, 148, 187, 240, 216, 54, 134, 217, 44, 146, 178, 90, 200, 174, 3, 98, 133, 67, 96, 93, 15, 145, 130, 116, 14, 38, 227, 57, 4, 89, 77, 51, 212, 79, 235, 149, 137, 161, 229, 36, 199, 32, 170, 74, 87, 107, 99, 215, 137, 184, 227, 94, 185] : List ℕ).map byte
private noncomputable def output3_1 : InputIndexedOracle.Input := ([152, 173, 243, 33, 1, 178, 76, 168, 233, 164, 90, 125, 2, 9, 165, 115, 242, 104, 110, 254, 83, 41, 28, 73, 139, 37, 13, 206, 85, 31, 188, 61, 114, 0, 45, 82, 142, 220, 74, 123, 136, 206, 134, 31, 206, 13, 204, 226, 109, 17, 159, 8, 107, 223, 33, 21, 222, 0, 102, 235, 51, 142, 151, 155] : List ℕ).map byte
private noncomputable def input3_2 : InputIndexedOracle.Input := ([158, 172, 63, 202, 89, 183, 63, 157, 45, 86, 99, 71, 152, 90, 174, 10, 89, 162, 181, 100, 75, 173, 119, 226, 51, 174, 145, 126, 10, 184, 102, 68, 191, 129, 126, 142, 136, 238, 170, 157, 58, 209, 18, 31, 31, 115, 31, 3, 206, 14, 26, 196, 95, 65, 251, 169, 88, 155, 243, 53, 3, 19, 186, 51, 152, 173, 243, 33, 1, 178, 76, 168, 233, 164, 90, 125, 2, 9, 165, 115, 242, 104, 110, 254, 83, 41, 28, 73, 139, 37, 13, 206, 85, 31, 188, 61, 114, 0, 45, 82, 142, 220, 74, 123, 136, 206, 134, 31, 206, 13, 204, 226, 109, 17, 159, 8, 107, 223, 33, 21, 222, 0, 102, 235, 51, 142, 151, 155] : List ℕ).map byte
private noncomputable def output3_2 : InputIndexedOracle.Input := ([142, 34, 250, 4, 166, 186, 7, 222, 95, 6, 108, 2, 76, 148, 237, 14, 178, 85, 179, 53, 193, 99, 98, 228, 3, 243, 240, 127, 203, 64, 123, 251, 72, 135, 134, 205, 19, 209, 115, 181, 62, 125, 73, 146, 115, 190, 64, 234, 229, 177, 29, 174, 25, 161, 137, 156, 123, 202, 139, 217, 23, 86, 23, 117] : List ℕ).map byte
private noncomputable def column3 : Column := ⟨⟨([3, 18446744073709551615] : List ℕ).map word,by decide⟩,⟨[digestOf path3_0,digestOf path3_1,digestOf path3_2],by decide⟩⟩
private noncomputable def events3 : List NativeTranscript.Observation := [.hash input3_0 output3_0,.hash input3_1 output3_1,.hash input3_2 output3_2]
private noncomputable def hashes : List (InputIndexedOracle.Input × InputIndexedOracle.Input) := [(input0_0,output0_0),(input0_1,output0_1),(input0_2,output0_2),(input1_0,output1_0),(input1_1,output1_1),(input1_2,output1_2),(input3_0,output3_0),(input3_1,output3_1),(input3_2,output3_2)]
private noncomputable def world : InputIndexedOracle.World
  | .inl _ => 0
  | .inr (input,index) => match hashes.find? (fun pair => pair.1 = input) with
    | none => 0
    | some pair => pair.2[index.val]?.getD (byte 255)
private noncomputable def root := digestOf nativeRoot
example : columnCodec.encode column0 = nativeColumn0 := by decide +kernel
example : columnCodec.read (nativeColumn0 ++ [byte 88]) = some (column0,[byte 88]) := by
  rw [← show columnCodec.encode column0 = nativeColumn0 from by decide +kernel]
  exact column_prefix _ _
example : (OracleProgram.run (verify 2 0 root column0) world).run = (true,events0) := by
  apply Prod.ext <;> decide +kernel
example : columnCodec.encode column1 = nativeColumn1 := by decide +kernel
example : columnCodec.read (nativeColumn1 ++ [byte 88]) = some (column1,[byte 88]) := by
  rw [← show columnCodec.encode column1 = nativeColumn1 from by decide +kernel]
  exact column_prefix _ _
example : (OracleProgram.run (verify 2 1 root column1) world).run = (true,events1) := by
  apply Prod.ext <;> decide +kernel
example : columnCodec.encode column3 = nativeColumn3 := by decide +kernel
example : columnCodec.read (nativeColumn3 ++ [byte 88]) = some (column3,[byte 88]) := by
  rw [← show columnCodec.encode column3 = nativeColumn3 from by decide +kernel]
  exact column_prefix _ _
example : (OracleProgram.run (verify 2 3 root column3) world).run = (true,events3) := by
  apply Prod.ext <;> decide +kernel
private noncomputable def changedValues : Column := {column1 with values := ⟨[word 7,word 8],by decide⟩}
example : (OracleProgram.run (verify 2 1 root changedValues) world).run.1 = false := by decide +kernel
example : (OracleProgram.run (verify 2 1 root changedValues) world).run.2.length = 1 := by decide +kernel
private noncomputable def changedSibling : Column := {column1 with path := ⟨[digestOf path1_0,fun _ => byte 0,digestOf path1_2],by decide⟩}
example : (OracleProgram.run (verify 2 1 root changedSibling) world).run.1 = false := by decide +kernel
example : (OracleProgram.run (verify 2 1 (fun _ => byte 0) column1) world).run.1 = false := by decide +kernel
example : (OracleProgram.run (verify 2 0 root column1) world).run.1 = false := by decide +kernel
example : (OracleProgram.run (verify 1 1 root column1) world).run = (false,[]) := by
  apply Prod.ext <;> decide +kernel
example : (OracleProgram.run (verify 2 1 root {column1 with path := ⟨[],by decide⟩}) world).run = (false,[]) := by
  apply Prod.ext <;> decide +kernel
private noncomputable def repeated := OracleProgram.bind (verify 2 1 root column1) (fun _ => verify 2 1 root column1)
example : (OracleProgram.run repeated world).run = (true,events1 ++ events1) := by
  apply Prod.ext <;> decide +kernel
example : (JointHashCache.project (events1 ++ events1)).keys.card = 3 := by decide +kernel
private noncomputable def point : List NativeGoldExtensionArithmetic.Word := [![word 2,word 3,word 5]]
private noncomputable def query : NativeGoldPcsWire.Query := (NativeGoldPcsWire.coefficientsQuery 3 point).getD ⟨[],by decide⟩
private noncomputable def values : NativeLookupRequestWire.Row := ⟨[word 251,word (2^64-1),word 65536],by decide⟩
example : NativeGoldPcsWire.queryCodec.encode query = nativeQuery := by decide +kernel
example : NativeGoldPcsWire.queryCodec.read (nativeQuery ++ [byte 88]) = some (query,[byte 88]) := by decide +kernel
example : NativeGoldPcsWire.opening root query values = nativeOpening := by decide +kernel
example : NativeGoldPcsWire.claim ⟨251,by decide⟩ ⟨65536,by decide⟩ query values = nativeClaim := by decide +kernel
example : NativeGoldPcsWire.openingCodec.read (nativeOpening ++ [byte 88]) = some ((root,query,values),[byte 88]) := by
  rw [← show NativeGoldPcsWire.opening root query values = nativeOpening from by decide +kernel]
  exact NativeGoldPcsWire.opening_prefix _ _ _ _
example : NativeGoldPcsWire.claimCodec.read (nativeClaim ++ [byte 88]) = some ((⟨251,by decide⟩,⟨65536,by decide⟩,query,values),[byte 88]) := by
  rw [← show NativeGoldPcsWire.claim ⟨251,by decide⟩ ⟨65536,by decide⟩ query values = nativeClaim from by decide +kernel]
  exact NativeGoldPcsWire.claim_prefix _ _ _ _ _
example : (NativeGoldPcsWire.coefficientsQuery 3 []).map NativeGoldPcsWire.queryCodec.encode = some [byte 0] := by decide +kernel
example : (NativeGoldCoefficientsQuery.coefficientsQuery 3 []).map (fun result => result.post.isSome) = some true := by decide +kernel
end NativePcsAuthenticationSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.compile_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.compile_pure

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.compile_hash' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.compile_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.compile_query' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.compile_query

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.compile_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.compile_bind

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.run_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.run_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.replay_of_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.replay_of_known

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.truthful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.truthful

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.cache_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.cache_known

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashOracleBridge.replay_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashOracleBridge.replay_actual

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.matrix_model' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.matrix_model

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.valid_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.valid_fits

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.fromPairs_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.fromPairs_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.fromPairs_complete' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.fromPairs_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.coefficientsQuery_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.coefficientsQuery_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.coefficientsQuery_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.coefficientsQuery_models

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.matrix_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.matrix_encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.pair_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.pair_encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.query_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.query_encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.query_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.query_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.opening_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.opening_encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.opening_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.opening_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.opening_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.opening_injective

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.claim_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.claim_encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWire.claim_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWire.claim_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.column_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.column_encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.column_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.column_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.decodePath_spec' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.decodePath_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.invalid_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.invalid_path

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.nodes_compile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.nodes_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.verifyDecoded_compile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.verifyDecoded_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.run_verifyDecoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.run_verifyDecoded

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.accepted_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.accepted_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.verify_accepted_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication.verify_accepted_replay
