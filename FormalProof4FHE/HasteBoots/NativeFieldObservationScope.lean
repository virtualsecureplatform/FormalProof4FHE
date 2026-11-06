module
public import FormalProof4FHE.HasteBoots.NativeEarlyReceiptPrefixRisk
@[expose] public section

/-! Field collection observes only its original pending input. In particular,
collecting an arbitrary native prefix cannot expose a distinct receipt key.
This concerns actual logs and includes rejected candidates and resumed states. -/
namespace FormalProof4FHE.HasteBoots.NativeFieldObservationScope
open InputIndexedOracle (Input World bytes)
open NativeTranscript (Observation FieldPhase)
open NativeFieldVector (State execute advance)

theorem trial_log (p : ℕ) (phase : FieldPhase) (world : World) :
    (CanonicalTranscriptSampler.executePrefix p 1 phase world).2 =
      [.output phase.pending.input phase.consumed.length (bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p))] := by
  simp only [CanonicalTranscriptSampler.executePrefix,NativeTranscript.drawField,WriterT.run_mk]
  by_cases good : CanonicalTranscriptSampler.candidate p
      (bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p)) < p
  · simp only [good,ite_true]
  · simp only [good,ite_false,List.append_nil]

theorem execute_only (p fuel : ℕ) (state : State) (world : World) (entry : Observation)
    (present : entry ∈ (execute p fuel state world).2) :
    ∃ offset values, entry = .output state.phase.pending.input offset values := by
  induction fuel generalizing state with
  | zero => cases present
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simp only [execute,complete,ite_true,List.not_mem_nil] at present
    · simp only [execute,complete,ite_false,trial_log,List.mem_append,List.mem_singleton] at present
      rcases present with first | later
      · exact ⟨_,_,first⟩
      · obtain ⟨offset,values,equal⟩ := ih _ later
        have header := (NativeFieldVector.advance_header p state world).1
        exact ⟨offset,values,by simpa only [header] using equal⟩

theorem other_unseen (p fuel : ℕ) (state : State) (world : World) (input : Input)
    (apart : state.phase.pending.input ≠ input) : CausalStreamExposure.seen (execute p fuel state world).2 input = false := by
  apply List.any_eq_false.mpr
  intro entry present
  obtain ⟨offset,values,rfl⟩ := execute_only p fuel state world entry present
  simp [CausalStreamExposure.touches,apart]

theorem unseen_after_collect (p fuel : ℕ) (state : State) (world : World) (input : Input) (before : List Observation)
    (unseen : CausalStreamExposure.seen before input = false) (apart : state.phase.pending.input ≠ input) :
    CausalStreamExposure.seen (before ++ (execute p fuel state world).2) input = false := by
  simp only [CausalStreamExposure.seen,List.any_append]
  rw [show before.any (CausalStreamExposure.touches input) = false from unseen,
    show ((execute p fuel state world).2).any (CausalStreamExposure.touches input) = false from other_unseen p fuel state world input apart]
  rfl
end FormalProof4FHE.HasteBoots.NativeFieldObservationScope
