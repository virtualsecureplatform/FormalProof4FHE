module
import FormalProof4FHE.HasteBoots.LookupDigestFixation

namespace FormalProof4FHE.HasteBoots.ReceiptFixationSmoke
open InputIndexedOracle (Input World bytes)
open NativeTranscript (Observation)
open NativeReceiptPrefixView (key)
open OracleProgram (Program run)
open ReceiptCandidateCompletion (program observations digest)
noncomputable section

def zero : World := fun _ => 0

def oldProgram : Program Unit := .read (key [1]) 99 1 (fun _ => .pure ())
def past (world : World) := run oldProgram world

theorem past_replay : ObservationReplay.Replayable past := OracleProgram.run_replay oldProgram

/-- An earlier partial far-offset read names a candidate key; completion adds
its exact full output without deleting or replacing the original observation. -/
theorem partial_completed :
    .output (key [1]) 0 (bytes zero (key [1]) 0 64) ∈ (ReceiptCandidateCompletion.extend past zero).run.2 := by
  apply ReceiptCandidateCompletion.named_output
  apply ReceiptPayloadView.observed [1] (bytes zero (key [1]) 99 1) 99 _
  · intro empty
    have length := congrArg List.length empty
    simp only [InputIndexedOracle.bytes_length,List.length_nil] at length
    contradiction
  · change _ ∈ [Observation.output (key [1]) 99 (bytes zero (key [1]) 99 1)]
    exact List.mem_singleton_self _

/-- The original far-offset read remains the first observation. -/
example : (ReceiptCandidateCompletion.extend past zero).run.2[0]? =
    some (.output (key [1]) 99 (bytes zero (key [1]) 99 1)) := by
  change (([.output (key [1]) 99 (bytes zero (key [1]) 99 1)] : List Observation) ++ _)[0]? = _
  rfl

/-- Completion preserves duplicate raw keys when passed a list directly;
the history-selected API deduplicates candidates before calling it. -/
example : (run (program [[1],[1]]) zero).run.2 =
    [.start (key [1]),.output (key [1]) 0 (bytes zero (key [1]) 0 64),
      .start (key [1]),.output (key [1]) 0 (bytes zero (key [1]) 0 64)] := by
  rw [ReceiptCandidateCompletion.run_program]
  rfl

/-- In an all-zero oracle, two distinct named receipt keys really collide.
The explicit collision alternative cannot be discarded by determinism. -/
theorem actual_collision : ReceiptDigestFixation.Collision
    [.output (key [1]) 99 [0],.output (key [2]) 7 [0]] zero := by
  refine ⟨[1],ReceiptPayloadView.observed [1] [0] 99 _ (by simp) (by simp),
    [2],ReceiptPayloadView.observed [2] [0] 7 _ (by simp) (by simp),by decide,?_⟩
  rfl

/-- Reading only the selected receipt domains leaves a distinct framed input
wholly unobserved, even though a full digest was completed at each key. -/
example : CausalStreamExposure.seen (observations [[1],[2]] zero) (TranscriptFrame.encodeMany []) = false :=
  ReceiptCandidateCompletion.unseen _ zero _ (fun raw _ => NativeTranscript.receipt_not_frame_stream raw [])

end
end FormalProof4FHE.HasteBoots.ReceiptFixationSmoke
