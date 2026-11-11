module
public import FormalProof4FHE.HasteBoots.ProgramFactorFixation
@[expose] public section

/-! Completing earlier receipt keys does not expose the actual outer scalar
stream. Its complete finite SHAKE blocks retain the exact uniform law on the
refined pre-read fiber used to fix the original lookup/EQ factors. -/
namespace FormalProof4FHE.HasteBoots.FactorFiberUniform
open InputIndexedOracle (Input World Byte law)
open OracleProgram (Program runPrefix)
open LookupFactorFixation (Sample)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

theorem input_framed (sample : Sample) :
    ∃ frames : List TranscriptFrame.Frame,
      sample.view.reader.entry.coefficients.phase.pending.input = TranscriptFrame.encodeMany frames := by
  have member := LookupSampleReceiptTargets.in_reader sample
  unfold ReceiptFrameView.frames at member
  cases decoded : TranscriptFrame.decodeAll sample.view.reader.entry.coefficients.phase.pending.input with
  | none => simp only [decoded,Option.getD_none,List.filter_nil,List.not_mem_nil] at member
  | some frames => exact ⟨frames,(TranscriptFrame.decodeAll_sound _ _ decoded).2⟩

theorem completed_unseen {A : Type} (sample : Sample) (program : Program A)
    (first : ProgramFirstStreamRead.First program sample.view.reader.world sample.view.reader.entry.coefficients.phase.pending.input) :
    CausalStreamExposure.seen
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) sample.view.reader.world).run.2
      sample.view.reader.entry.coefficients.phase.pending.input = false := by
  obtain ⟨frames,encoded⟩ := input_framed sample
  apply ReceiptCandidateCompletion.unseen_extended (runPrefix first.position program) sample.view.reader.world _ first.fresh
  intro raw _
  rw [encoded]
  exact NativeTranscript.receipt_not_frame_stream raw frames

/-- The first physical query may be a short read at a far offset. The law
is nevertheless for any finite logical block of the still-unseen scalar key. -/
theorem block_law {A : Type} (sample : Sample) (program : Program A)
    (first : ProgramFirstStreamRead.First program sample.view.reader.world sample.view.reader.entry.coefficients.phase.pending.input)
    (offset count : ℕ) :
    (law[|{other | (ReceiptCandidateCompletion.extend (runPrefix first.position program) other).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) sample.view.reader.world).run}]).map
        (fun other => InputIndexedOracle.block other sample.view.reader.entry.coefficients.phase.pending.input offset count) =
      uniformOn (Set.univ : Set (Fin count → Byte)) := by
  rw [ObservationReplay.fiber_eq_assignment (ReceiptCandidateCompletion.replay (OracleProgram.prefix_replay first.position program)) sample.view.reader.world]
  exact CachedOracleResponse.fresh_response _ _
    (CachedOracleResponse.shakeCoordinates sample.view.reader.entry.coefficients.phase.pending.input offset count)
    (CachedOracleResponse.shake_distinct _ offset count)
    (fun position => by
      simpa only [CachedOracleResponse.shakeCoordinates] using
        CausalStreamExposure.unseen_coordinates _ _ (completed_unseen sample program first) (offset+position.val))

end
end FormalProof4FHE.HasteBoots.FactorFiberUniform
