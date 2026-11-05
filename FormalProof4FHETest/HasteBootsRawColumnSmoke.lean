module

import all FormalProof4FHE.HasteBoots.NativeGoldPcsWorkerSoundness
import all FormalProof4FHE.HasteBoots.NativeGoldPcsRawFailure
import all FormalProof4FHE.HasteBoots.NativeGoldRawRequests
import all FormalProof4FHE.HasteBoots.NativeGoldColumnChecks
import all FormalProof4FHE.HasteBoots.NativeGoldColumnWorker
import all FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers
import all FormalProof4FHE.HasteBoots.NativeHashOracleBridge
import all Init.Data.String.Defs

/-! Literal raw hashes and arithmetic from the pinned native full PCS verifier.
The lazy-zero alias passes the same field checks but fails raw authentication.
These are source-model/kernel comparisons, not Rust/Rayon refinement. -/
open FormalProof4FHE.HasteBoots
namespace NativeGoldColumnSmoke
private noncomputable def word (n : ℕ) : NativeFieldRepresentation.GoldWord := ⟨n%(2^64),Nat.mod_lt _ (by decide)⟩
private noncomputable def bytes (values : List ℕ) : InputIndexedOracle.Input := values.map (fun n => ⟨n%256,Nat.mod_lt _ (by decide)⟩)
private noncomputable def row (values : List ℕ) (fits : values.length < 2^64) : NativeLookupRequestWire.Row := ⟨values.map word,by rw [List.length_map]; exact fits⟩
private noncomputable def digest (values : List ℕ) : NativeRootMessage.Digest := fun index => (bytes values)[index.val]?.getD 0
private noncomputable def geometry : NativeBrakedownParameters.Geometry := ⟨2,32,2,6,64,12,6,5,word 18⟩
private noncomputable def root : NativeRootMessage.Digest := digest [222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201]
private noncomputable def column : NativeGoldColumnAuthentication.Column := ⟨row [0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11] (by decide +kernel),
  ⟨([[173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2], [173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2], [76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179], [177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42], [134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84], [28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166]] : List (List ℕ)).map digest,by decide +kernel⟩⟩
private noncomputable def random := ([9006852650750938612, 14640957084096262003, 9854509489887128708, 9644174246397643206, 6277422940221709385, 10279636647838546132, 16906197915117412805, 17009151044929302110, 11602235440486293253, 18096152153882804454, 16866502560695958133, 7843068391247455882, 4609502687908310470, 15375860440544483837, 592352637967683537, 10551492528840311662, 16065408205054275817, 15084310034826379023] : List ℕ).map word
private noncomputable def structured := ([18446744069414584320, 18446744069414584286, 18446744069414584300, 2, 35, 21, 18446744069414584318, 18446744069414584320, 18446744069414584286, 3, 2, 35, 18446744069414584316, 18446744069414584318, 18446744069414584320, 5, 3, 2] : List ℕ).map word
private noncomputable def test : List NativeFieldRepresentation.GoldWord :=
  ((List.replicate 32 ([10663165317240926990, 18396346353517193167] : List ℕ)).flatten.map word) ++ ((List.replicate 32 ([16715989892425570710, 11700256917557985223] : List ℕ)).flatten.map word) ++ ((List.replicate 32 ([3430785603203941070, 8169463425760920726] : List ℕ)).flatten.map word)
private noncomputable def evaluation : List NativeFieldRepresentation.GoldWord :=
  ((List.replicate 32 ([174, 180] : List ℕ)).flatten.map word) ++ ((List.replicate 32 ([121, 127] : List ℕ)).flatten.map word) ++ ((List.replicate 32 ([32, 38] : List ℕ)).flatten.map word)
private noncomputable def hashInput0 := bytes [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 47, 118, 50, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 2, 3, 1, 1, 2, 32, 26, 98, 108, 111, 99, 107, 45, 114, 115, 47, 110, 101, 103, 97, 99, 121, 99, 108, 105, 99, 45, 110, 116, 116, 47, 118, 49, 2, 2, 1, 32, 20, 49, 56, 52, 52, 54, 55, 52, 52, 48, 54, 57, 52, 49, 52, 53, 56, 52, 51, 50, 49, 253, 0, 0, 0, 0, 128, 0, 0, 0]
private noncomputable def hashOutput0 := bytes [168, 24, 26, 181, 23, 86, 1, 91, 75, 211, 134, 164, 239, 10, 145, 57, 198, 141, 122, 167, 100, 222, 125, 71, 160, 7, 224, 215, 227, 62, 1, 201, 190, 51, 51, 84, 116, 84, 188, 171, 139, 20, 238, 241, 201, 229, 125, 48, 206, 254, 209, 28, 25, 39, 209, 120, 172, 7, 53, 249, 138, 244, 227, 145]
private noncomputable def hashInput1 := bytes [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 99, 111, 108, 117, 109, 110, 47, 118, 49, 12, 0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11]
private noncomputable def hashOutput1 := bytes [173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2]
private noncomputable def hashInput2 := bytes [173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2, 173, 84, 12, 187, 195, 197, 34, 174, 121, 112, 70, 60, 134, 225, 99, 186, 121, 86, 141, 167, 73, 208, 34, 143, 79, 206, 162, 70, 81, 74, 145, 8, 32, 213, 38, 95, 80, 214, 90, 17, 91, 133, 108, 148, 111, 54, 9, 37, 136, 88, 170, 122, 59, 199, 32, 181, 51, 149, 247, 88, 96, 40, 160, 2]
private noncomputable def hashOutput2 := bytes [76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179]
private noncomputable def hashInput3 := bytes [76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179, 76, 217, 186, 226, 59, 186, 49, 62, 109, 245, 171, 100, 190, 9, 225, 215, 186, 94, 254, 194, 208, 76, 0, 246, 235, 199, 174, 117, 18, 56, 66, 82, 244, 152, 57, 151, 29, 228, 34, 80, 184, 209, 118, 34, 102, 223, 5, 22, 125, 253, 14, 254, 122, 18, 127, 241, 34, 224, 230, 111, 245, 200, 43, 179]
private noncomputable def hashOutput3 := bytes [177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42]
private noncomputable def hashInput4 := bytes [177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42, 177, 243, 248, 73, 103, 223, 92, 140, 108, 165, 86, 195, 214, 166, 109, 208, 121, 195, 188, 87, 181, 23, 222, 176, 41, 44, 142, 234, 62, 91, 98, 157, 247, 123, 113, 122, 152, 148, 217, 204, 23, 21, 237, 179, 162, 165, 159, 105, 190, 43, 220, 200, 167, 255, 250, 239, 150, 127, 57, 123, 213, 64, 220, 42]
private noncomputable def hashOutput4 := bytes [134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84]
private noncomputable def hashInput5 := bytes [134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84, 134, 66, 93, 124, 67, 97, 21, 157, 112, 222, 111, 251, 80, 12, 57, 163, 22, 183, 184, 88, 51, 224, 68, 24, 144, 88, 2, 145, 75, 127, 200, 251, 9, 169, 47, 41, 201, 88, 120, 179, 134, 235, 187, 75, 211, 103, 99, 233, 117, 28, 181, 163, 171, 241, 25, 52, 34, 147, 108, 101, 129, 99, 227, 84]
private noncomputable def hashOutput5 := bytes [28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166]
private noncomputable def hashInput6 := bytes [28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166, 28, 254, 215, 41, 136, 34, 8, 19, 2, 117, 43, 255, 110, 170, 74, 246, 86, 89, 22, 145, 147, 119, 181, 228, 68, 244, 152, 235, 104, 18, 123, 231, 255, 106, 1, 183, 165, 212, 247, 190, 56, 172, 107, 27, 91, 114, 223, 85, 190, 136, 27, 48, 206, 247, 44, 138, 217, 72, 245, 178, 238, 177, 93, 166]
private noncomputable def hashOutput6 := bytes [222, 45, 145, 29, 105, 30, 117, 235, 89, 81, 42, 179, 206, 224, 99, 102, 124, 123, 183, 252, 222, 171, 151, 183, 97, 141, 92, 122, 24, 0, 206, 60, 199, 203, 57, 67, 46, 150, 71, 26, 22, 161, 42, 236, 45, 230, 229, 100, 85, 209, 123, 3, 102, 39, 42, 46, 29, 11, 5, 11, 176, 232, 58, 201]
private noncomputable def hashInput7 := bytes [72, 97, 115, 116, 101, 66, 111, 111, 116, 115, 47, 109, 119, 45, 99, 111, 108, 117, 109, 110, 47, 118, 49, 12, 253, 1, 0, 0, 0, 255, 255, 255, 255, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11]
private noncomputable def hashOutput7 := bytes [24, 94, 182, 165, 101, 37, 200, 115, 161, 112, 225, 111, 24, 166, 86, 18, 176, 24, 220, 82, 14, 41, 252, 93, 97, 4, 45, 213, 206, 41, 216, 182, 67, 212, 166, 81, 94, 217, 39, 209, 152, 224, 81, 137, 11, 117, 55, 25, 243, 163, 43, 113, 5, 94, 233, 149, 131, 9, 60, 90, 194, 236, 66, 108]
private noncomputable def hashPairs : List (InputIndexedOracle.Input × InputIndexedOracle.Input) := [(hashInput0,hashOutput0),(hashInput1,hashOutput1),(hashInput2,hashOutput2),(hashInput3,hashOutput3),(hashInput4,hashOutput4),(hashInput5,hashOutput5),(hashInput6,hashOutput6),(hashInput7,hashOutput7)]
private noncomputable def world : InputIndexedOracle.World
  | .inl _ => 255
  | .inr (input,index) => match hashPairs.find? (fun pair => pair.1=input) with
    | none => 255
    | some pair => pair.2[index.val]?.getD 255
private noncomputable def execute (c : NativeGoldColumnAuthentication.Column) (t e : List NativeFieldRepresentation.GoldWord) : Bool × List NativeTranscript.Observation :=
  (OracleProgram.run (NativeHashOracleBridge.compile (NativeGoldColumnWorker.worker geometry 3 random structured t e root 27 c)) world).run
private noncomputable def events : List NativeTranscript.Observation := [.hash hashInput1 hashOutput1,.hash hashInput2 hashOutput2,.hash hashInput3 hashOutput3,.hash hashInput4 hashOutput4,.hash hashInput5 hashOutput5,.hash hashInput6 hashOutput6]
example : ((List.range 3).flatMap (fun lane => (List.range 2).map (fun component =>
    (NativeGoldColumnChecks.dot 6 2 random column.values.val lane component).val))) = [10663165317240926990, 18396346353517193167, 16715989892425570710, 11700256917557985223, 3430785603203941070, 8169463425760920726] := by decide +kernel
example : ((List.range 3).flatMap (fun lane => (List.range 2).map (fun component =>
    (NativeGoldColumnChecks.dot 6 2 structured column.values.val lane component).val))) = [18446744069414584495, 18446744069414584501, 18446744069414584442, 18446744069414584448, 18446744069414584353, 18446744069414584359] := by decide +kernel
example : NativeGoldColumnChecks.check geometry 3 random structured test evaluation column.values.val 27 = true := by decide +kernel
example : NativeGoldColumnChecks.Shape geometry 3 27 random structured test evaluation column.values.val := by
  unfold NativeGoldColumnChecks.Shape
  decide +kernel
example : execute column test evaluation = (true,events) := by decide +kernel
private noncomputable def lazyColumn : NativeGoldColumnAuthentication.Column :=
  {column with values := row [18446744069414584321,6,1,7,2,8,3,9,4,10,5,11] (by decide +kernel)}
example : lazyColumn.values.val.map NativeFieldRepresentation.goldValue = column.values.val.map NativeFieldRepresentation.goldValue := by decide +kernel
example : NativeGoldColumnChecks.check geometry 3 random structured test evaluation lazyColumn.values.val 27 = true := by decide +kernel
example : NativeGoldColumnAuthentication.leafInput column.values = hashInput1 := by decide +kernel
example : NativeGoldColumnAuthentication.leafInput lazyColumn.values = hashInput7 := by decide +kernel
example : hashInput1 ≠ hashInput7 := by decide +kernel
example : execute lazyColumn test evaluation = (false,[.hash hashInput7 hashOutput7]) := by decide +kernel
example : execute {column with path := ⟨[],by decide +kernel⟩} test evaluation = (false,[]) := by decide +kernel
example : execute column (List.replicate 192 0) evaluation = (false,events) := by decide +kernel
example : execute column test (List.replicate 192 0) = (false,events) := by decide +kernel
example : NativeGoldPcsWorkers.attach [27,28] [column] = none := by decide +kernel
example : NativeGoldPcsWorkers.attach [27] [column,column] = none := by decide +kernel
example : (NativeGoldPcsWorkers.attach [27] [column]).map (List.map NativeGoldColumnWorker.Job.index) = some [27] := by decide +kernel
private noncomputable def rawJob : NativeGoldColumnWorker.Job := ⟨27,column⟩
private noncomputable def lazyJob : NativeGoldColumnWorker.Job := ⟨27,lazyColumn⟩
private noncomputable def rawRequest := NativeGoldRawRequests.fromJob (fun _ : Unit => 5) () root rawJob
example : rawRequest.map (fun request => (request.position.val,request.payload.val.map Fin.val,request.siblings.toList.length)) =
  some (27,[0,6,1,7,2,8,3,9,4,10,5,11],5) := by decide +kernel
example : rawRequest.map (fun request => (List.ofFn request.root,List.ofFn request.leaf)) =
  some (List.ofFn root,hashOutput1) := by decide +kernel
example : (NativeGoldRawRequests.fromJob (fun _ : Unit => 5) () root {rawJob with index := 32}).isNone = true := by decide +kernel
example : (NativeGoldRawRequests.fromJob (fun _ : Unit => 6) () root rawJob).isNone = true := by decide +kernel
example : (NativeGoldRawRequests.fromJob (fun _ : Unit => 5) () root
  {rawJob with column := {column with path := ⟨[],by decide +kernel⟩}}).isNone = true := by decide +kernel
private noncomputable def rawEntries := NativeGoldRawRequests.entries (fun _ : Unit => 5) () root [rawJob,lazyJob]
example : rawEntries.map (List.map (fun entry => (entry.1.index,entry.2.position.val))) = some [(27,27),(27,27)] := by decide +kernel
example : rawEntries.map (List.map (fun entry => entry.2.payload.val.map Fin.val)) =
  some [[0,6,1,7,2,8,3,9,4,10,5,11],[18446744069414584321,6,1,7,2,8,3,9,4,10,5,11]] := by decide +kernel
example : (NativeGoldRawRequests.entries (fun _ : Unit => 5) () root [rawJob,{lazyJob with index := 32}]).isNone = true := by decide +kernel

end NativeGoldColumnSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.equal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.equal_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.addresses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.addresses

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.dot_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.dot_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.dot_layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnChecks.dot_layout

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.authentication_compile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.authentication_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.worker_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.worker_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.worker_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.worker_accepts

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.worker_raw_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.worker_raw_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.accepted_jobs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldColumnWorker.accepted_jobs

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.attach_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.attach_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.attach_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.attach_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.run_protocol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.run_protocol

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.prepared_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.prepared_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.encoded_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.encoded_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.prepared_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers.prepared_shape

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsWorkerSoundness.accepted_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsWorkerSoundness.accepted_checks

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsPaths.prepared_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsPaths.prepared_paths

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawRequests.fromJob_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawRequests.fromJob_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawRequests.decode_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawRequests.decode_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawRequests.fromJob_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawRequests.fromJob_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawRequests.entries_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawRequests.entries_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawRequests.entries_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawRequests.entries_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawRequests.replay_of_worker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawRequests.replay_of_worker

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.empty_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.empty_view

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.payload_of_no_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.payload_of_no_failure

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.values_of_no_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.values_of_no_failure

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.equations_of_no_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.equations_of_no_failure

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.failure_implies_availability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.failure_implies_availability

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.failure_le_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.failure_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.failure_from_empty_le_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldRawAvailability.failure_from_empty_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability.prepare_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability.prepare_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability.pool_replays' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability.pool_replays

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability.pool_equations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability.pool_equations

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsRawFailure.failure_implies_availability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsRawFailure.failure_implies_availability

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsRawFailure.failure_le_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsRawFailure.failure_le_charge
