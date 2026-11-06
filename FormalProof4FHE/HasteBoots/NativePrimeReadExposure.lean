module

public import FormalProof4FHE.HasteBoots.NativePrimeRequest
@[expose] public section

/-! A completed nonempty native prime-vector request necessarily exposes its first canonical byte chunk, including when the first candidate is rejected. -/
namespace FormalProof4FHE.HasteBoots.NativePrimeReadExposure
open InputIndexedOracle (Input World bytes)
open NativeTranscript (Transcript FieldPhase Observation)
open OracleProgram (run)

theorem trial_log (p : ℕ) (phase : FieldPhase) (world : World) :
    (CanonicalTranscriptSampler.executePrefix p 1 phase world).2 =
      [.output phase.pending.input phase.consumed.length (bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p))] := by
  by_cases accepted : CanonicalTranscriptSampler.candidate p
      (bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p)) < p
  all_goals simp only [CanonicalTranscriptSampler.executePrefix,NativeTranscript.drawField,WriterT.run_mk,
    accepted,ite_true,ite_false,List.append_nil]

theorem collect_read (p fuel : ℕ) (state : NativeFieldVector.State) (world : World) (pending : state.remaining ≠ 0) :
    .output state.phase.pending.input state.phase.consumed.length
      (bytes world state.phase.pending.input state.phase.consumed.length (CanonicalByteSampler.byteCount p)) ∈
        (NativeFieldVector.execute p (fuel+1) state world).2 := by
  simp only [NativeFieldVector.execute,ite_eq_right pending]
  rw [trial_log]
  exact List.mem_append_left _ (List.mem_singleton_self _)

theorem finished_fuel (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) (positive : count ≠ 0)
    (world : World) (state : NativeFieldVector.State) (next : Transcript)
    (finished : (run (NativeFieldVector.request p fuel transcript label count) world).run.1 = .finished state next) : fuel ≠ 0 := by
  intro zero
  subst fuel
  rw [NativeFieldVector.run_request] at finished
  simp only [NativeFieldVector.driveExecute,NativeFieldVector.execute,NativeFieldVector.finishExecute,NativeFieldVector.initial,
    positive,ite_false] at finished
  contradiction

theorem finished_read (p fuel : ℕ) (transcript : Transcript) (kind : TypedFieldRequest.Kind) (label : Input)
    (count : NativeUsizeMessage.Usize) (positive : count.val ≠ 0)
    (world : World) (state : NativeFieldVector.State) (next : Transcript)
    (finished : (run (NativePrimeRequest.request p fuel transcript kind label count) world).run.1 = .finished state next) :
    .output (NativePrimeRequest.phase p transcript kind label count).pending.input 0
      (bytes world (NativePrimeRequest.phase p transcript kind label count).pending.input 0 (CanonicalByteSampler.byteCount p)) ∈
        (run (NativePrimeRequest.request p fuel transcript kind label count) world).run.2 := by
  rw [NativePrimeRequest.request_eq_collector] at finished ⊢
  have nonzero := finished_fuel p fuel (NativePrimeRequest.prepare transcript kind) label count.val positive world state next finished
  obtain ⟨fuel,rfl⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  rw [NativeFieldVector.run_request]
  apply List.mem_append_right
  apply List.mem_append_left
  exact collect_read p fuel _ world positive
end FormalProof4FHE.HasteBoots.NativePrimeReadExposure
