module
import FormalProof4FHE.HasteBoots.LookupReceiptCandidates
import all FormalProof4FHE.HasteBoots.NativeReceiptPrefixView
import all FormalProof4FHE.HasteBoots.NativeTranscript

namespace FormalProof4FHE.HasteBoots.ReceiptCandidatesSmoke
open NativeReceiptPrefixView (key)
open NativeTranscript (Observation)
noncomputable section

/-- One positive far-offset byte reveals every consumed candidate, including
rejections and masked high bits. Starts and empty same-key reads add nothing. -/
example : ReceiptPayloadView.payloads [.start (key [3,2,255,1,0]),
    .output (key [3,2,255,1,0]) 99 [], .output (key [3,2,255,1,0]) 100 [7]] = {[3,2,255,1,0]} := by
  simp [ReceiptPayloadView.payloads,List.filterMap_cons,List.filterMap_nil,ReceiptPayloadView.candidate,ReceiptPayloadView.read_key]

example : ReceiptCoefficientCandidates.decode 3 [3,2,255,1,0] = [2,1,0] := by decide +kernel

/-- Repeated or split queries of the same raw key do not duplicate candidates. -/
example : ReceiptCoefficientCandidates.candidates 3
    [.output (key [3,2,255,1,0]) 99 [7],.output (key [3,2,255,1,0]) 0 [8]] = {[2,1,0]} := by
  simp [ReceiptCoefficientCandidates.candidates,ReceiptPayloadView.payloads,List.filterMap_nil,ReceiptPayloadView.candidate,
    ReceiptPayloadView.read_key]
  decide +kernel

/-- Hash observations name keys too, independently of the returned digest. -/
example : ReceiptPayloadView.payloads [.hash (key [3,2]) [99]] = {[3,2]} := by
  simp [ReceiptPayloadView.payloads,List.filterMap_nil,ReceiptPayloadView.candidate,ReceiptPayloadView.read_key]

/-- Distinct payloads can yield the same accepted coefficients. The cover
therefore merges equal coefficient lists without merging raw receipt keys. -/
example : ReceiptCoefficientCandidates.decode 3 [3,2] = ReceiptCoefficientCandidates.decode 3 [2] := by decide +kernel

example : ReceiptPayloadView.read [0] = none := by
  have wrong : ([0] : InputIndexedOracle.Input).take NativeReceiptPrefixView.domain.length ≠ NativeReceiptPrefixView.domain := by
    unfold NativeReceiptPrefixView.domain NativeTranscript.utf8
    decide +kernel
  simp only [ReceiptPayloadView.read,wrong,ite_false]

end
end FormalProof4FHE.HasteBoots.ReceiptCandidatesSmoke
