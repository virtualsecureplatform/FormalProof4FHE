module
import all FormalProof4FHE.HasteBoots.CallerOffsetPositionCoverage
import all FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability
import all Init.Data.String.Defs

namespace HasteBootsOffsetPositionSmoke
open FormalProof4FHE.HasteBoots
open NativeLookupChallenge (hashLabel reciprocalLabel)
noncomputable section

def identity : TranscriptFrame.Frame := ⟨5,NativeTranscript.utf8 "typed extension identity",[0]⟩
def compression : TranscriptFrame.Frame := ⟨5,hashLabel,[1]⟩
def offset : TranscriptFrame.Frame := ⟨5,reciprocalLabel,[2]⟩

/-- Different rejection counts change total receipts but preserve the
compression count that identifies the original offset job. -/
theorem retries_do_not_change_job_marker :
    LookupCompressionCount.count [identity,compression,offset,compression] = 2 ∧
    LookupCompressionCount.count [identity,compression,offset,offset,offset,compression,offset,offset] = 2 := by
  unfold LookupCompressionCount.count identity compression offset hashLabel reciprocalLabel NativeTranscript.utf8
  decide +kernel

/-- Duplicate-looking original jobs remain distinct markers. The identity
receipt is not counted as a lookup compression challenge. -/
theorem repeated_jobs_remain_distinct :
    LookupCompressionCount.count [identity] = 0 ∧
    LookupCompressionCount.count [identity,compression,offset,compression,offset,compression] = 3 := by
  unfold LookupCompressionCount.count identity compression offset hashLabel reciprocalLabel NativeTranscript.utf8
  decide +kernel

def metadataMarker : TranscriptFrame.Frame := ⟨1,hashLabel,[9]⟩

/-- An absorption with the same label cannot invent another job marker.
The input projection counts kind-5 receipts rather than label occurrences. -/
theorem metadata_is_not_a_job :
    LookupCompressionCount.fromInput (TranscriptFrame.encodeMany [identity,metadataMarker]) = 0 := by
  have valid : ∀ entry ∈ [identity,metadataMarker], TranscriptFrame.Valid entry := by
    intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · constructor
      · change (NativeTranscript.utf8 "typed extension identity").length < _
        unfold NativeTranscript.utf8
        decide +kernel
      · decide +kernel
    · constructor
      · change hashLabel.length < _
        unfold hashLabel NativeTranscript.utf8
        decide +kernel
      · decide +kernel
  unfold LookupCompressionCount.fromInput ReceiptFrameView.frames
  rw [TranscriptFrame.decodeAll_encodeMany _ valid]
  unfold LookupCompressionCount.count identity metadataMarker hashLabel NativeTranscript.utf8
  decide +kernel

end
end HasteBootsOffsetPositionSmoke
