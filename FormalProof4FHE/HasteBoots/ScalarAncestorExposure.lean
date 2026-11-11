module
public import FormalProof4FHE.HasteBoots.ScalarChallengeInputView
public import FormalProof4FHE.HasteBoots.CausalStreamExposure
@[expose] public section

/-! Earlier native collectors may be replayed without exposing a later scalar
stream. Receipt queries are included; their domain separation is structural,
not an assumption that the adversary has not guessed a challenge input. -/
namespace FormalProof4FHE.HasteBoots.ScalarAncestorExposure
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript Observation)
open NativeFieldVector

theorem seen_append (left right : List Observation) (target : Input) :
    CausalStreamExposure.seen (left ++ right) target =
      (CausalStreamExposure.seen left target || CausalStreamExposure.seen right target) :=
  List.any_append

/-- All candidate reads, including rejections, use the original reader. -/
theorem candidate_unseen (p : ℕ) (phase : NativeTranscript.FieldPhase) (world : World)
    (target : Input) (different : phase.pending.input ≠ target) :
    CausalStreamExposure.seen (CanonicalTranscriptSampler.executePrefix p 1 phase world).2 target = false := by
  simp only [CanonicalTranscriptSampler.executePrefix, NativeTranscript.drawField, WriterT.run_mk]
  by_cases good : CanonicalTranscriptSampler.candidate p
      (InputIndexedOracle.bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p)) < p
  all_goals simp [good, CausalStreamExposure.seen, CausalStreamExposure.touches, different]

/-- Arbitrary finite candidate prefixes retain nonexposure of a different input. -/
theorem collect_unseen (p fuel : ℕ) (state : State) (world : World)
    (target : Input) (different : state.phase.pending.input ≠ target) :
    CausalStreamExposure.seen (execute p fuel state world).2 target = false := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    by_cases done : state.remaining = 0
    · simp [execute, done, CausalStreamExposure.seen]
    · have header := advance_header p state world
      have later := ih (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1)
        (by rw [header.1]; exact different)
      simpa only [execute, done, ite_false, seen_append,
        candidate_unseen p state.phase world target different, Bool.false_or] using later

/-- Finalization cannot expose any structurally parsed scalar input. -/
theorem finalize_unseen (state : State) (world : World) (target : Input)
    (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view) :
    CausalStreamExposure.seen (finishExecute world state).2 target = false := by
  have inputEq := (ScalarChallengeInputView.parse_sound target view parsed state.phase.pending.profile).1
  have separated : NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ state.phase.consumed ≠ target := by
    rw [← inputEq, ScalarChallengeInputView.phase_input]
    exact NativeTranscript.receipt_not_frame_stream _ _
  by_cases done : state.remaining = 0
  · rw [finishExecute, ite_eq_left done]
    change CausalStreamExposure.seen
      [.start (NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ state.phase.consumed),
       .output (NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ state.phase.consumed) 0
         (InputIndexedOracle.bytes world (NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ state.phase.consumed) 0 64)] target = false
    simp [CausalStreamExposure.seen, CausalStreamExposure.touches, separated]
  · simp [finishExecute, done, CausalStreamExposure.seen]

/-- Collection and its actual receipt preserve nonexposure of a later parsed
input. No rejection count or successful-completion assumption is needed. -/
theorem drive_unseen (p fuel : ℕ) (state : State) (world : World) (target : Input)
    (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view)
    (different : state.phase.pending.input ≠ target) :
    CausalStreamExposure.seen (driveExecute p fuel state world).2 target = false := by
  simp only [driveExecute, seen_append,
    collect_unseen p fuel state world target different,
    finalize_unseen (execute p fuel state world).1 world target view parsed, Bool.false_or]

/-- Successful finalization strictly extends the original reader's input,
regardless of the number of rejected candidates or receipt digest bytes. -/
theorem finished_input_growth (p fuel : ℕ) (state completed : State) (world : World) (next : Transcript)
    (finished : (driveExecute p fuel state world).1 = .finished completed next) :
    state.phase.pending.input.length < next.input.length := by
  have header := header_preserved p fuel state world
  unfold driveExecute finishExecute at finished
  dsimp only at finished
  split at finished
  next done =>
    cases finished
    change state.phase.pending.input.length <
      ((execute p fuel state world).1.phase.pending.input ++
        TranscriptFrame.encode ⟨5, (execute p fuel state world).1.phase.label,
          (NativeTranscript.receipt world (execute p fuel state world).1.phase.consumed).run.1⟩).length
    rw [List.length_append, TranscriptFrame.encode_length, header.1]
    omega
  next => contradiction

end FormalProof4FHE.HasteBoots.ScalarAncestorExposure
