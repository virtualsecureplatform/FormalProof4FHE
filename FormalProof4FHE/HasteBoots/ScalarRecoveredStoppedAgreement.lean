module
public import FormalProof4FHE.HasteBoots.ScalarStoppedPrior
@[expose] public section

/-! Stopped replay from recovered input retains the original active sampler's
prior. Statement, proof, parent and prior associations are derived from the
original initialized execution, including partially consumed requests. -/
namespace FormalProof4FHE.HasteBoots.ScalarRecoveredStoppedAgreement
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)

theorem stopped_eq (target : Input) (statement : Statement) (original reconstructed : Proof)
    (fuel : ℕ) (machine : Machine) (world : World)
    (agree : ∀ index < fuel,
      (NativeScalarBatchVerifier.execute statement original index machine world).1.control = .ready →
        ScalarProofPrefixExecution.AgreeAt original reconstructed
          (NativeScalarBatchVerifier.execute statement original index machine world).1.state.round) :
    ScalarStoppedReplay.execute target statement original fuel machine world =
      ScalarStoppedReplay.execute target statement reconstructed fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    by_cases stop : ScalarStoppedReplay.blocked target machine = true
    · simp only [ScalarStoppedReplay.execute,stop,ite_true]
    · have allowed : ScalarStoppedReplay.blocked target machine = false := Bool.eq_false_iff.mpr stop
      have first := ScalarProofPrefixExecution.tick_eq statement original reconstructed machine world
        (agree 0 (Nat.zero_lt_succ fuel))
      have later : ∀ index < fuel,
          (NativeScalarBatchVerifier.execute statement original index
            (NativeScalarBatchVerifier.tickExecute statement original machine world).1 world).1.control = .ready →
          ScalarProofPrefixExecution.AgreeAt original reconstructed
            (NativeScalarBatchVerifier.execute statement original index
              (NativeScalarBatchVerifier.tickExecute statement original machine world).1 world).1.state.round := by
        intro index bound
        simpa only [NativeScalarBatchVerifier.execute] using agree (index + 1) (by omega)
      simp only [ScalarStoppedReplay.execute,allowed,Bool.false_eq_true,ite_false]
      rw [← first,ih _ later]

theorem from_rows (target : Input) (view : ScalarTranscriptPrefix.View) (original reconstructed : Proof)
    (built : ScalarPrefixProof.reconstruct view = some reconstructed)
    (first : NativeScalarBatchWire.Info) (head : view.history.statement.infos.val.head? = some first)
    (previous : ∀ pair ∈ view.history.rounds, NativeScalarBatchRoundPacket.packet pair.1.round original = some pair.1)
    (current : NativeScalarBatchRoundPacket.packet view.packet.round original = some view.packet)
    (fuel : ℕ) (machine : Machine) (world : World)
    (lastRound : (NativeScalarBatchVerifier.execute view.history.statement original fuel machine world).1.state.round ≤ view.packet.round.val) :
    ScalarStoppedReplay.execute target view.history.statement original fuel machine world =
      ScalarStoppedReplay.execute target view.history.statement reconstructed fuel machine world := by
  apply stopped_eq
  intro index bound _ round sameRound
  have ordered := ScalarExecutionPrefixAgreement.earlier_round view.history.statement original index fuel (Nat.le_of_lt bound) machine world
  exact ScalarExecutionPrefixAgreement.getters view original reconstructed built first head previous current round
    (by rw [sameRound]; exact ordered.trans lastRound)

/-- The entire stopped result and log of the recovered native program equal
the original stopped result and log. No per-tick association is a premise. -/
theorem sampling (transcript result : Transcript) (before : List TranscriptFrame.Frame) (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (fuel : ℕ) (world : World) (packet : RoundPacket) (field : NativeFieldVector.State)
    (active : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling packet field) :
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover field.phase.pending.input = some configuration ∧
      configuration.view.history.statement = statement ∧ configuration.view.packet = packet ∧
      ScalarStoppedReplay.execute field.phase.pending.input statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world =
      ScalarStoppedReplay.execute field.phase.pending.input statement configuration.proof fuel
        (configuration.initial transcript.profile) world := by
  obtain ⟨rounds,reconstructed,found,_,previous,current⟩ := ScalarExecutionRecovery.sampling
    transcript result before statement proof decoded accepted statementFits domain fuel world packet field active
  let configuration : ScalarRecoveredReplay.Configuration := ⟨⟨ScalarExecutionTranscript.history before statement rounds,packet⟩,reconstructed⟩
  have recoverFound : ScalarRecoveredReplay.recover field.phase.pending.input = some configuration := found
  have built := (ScalarRecoveredReplay.recover_sound _ configuration recoverFound).2
  have preflight := (NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mp accepted
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success statement preflight.2.1
  have lastRound := ScalarStoppedPrior.active_round transcript result statement proof accepted fuel world packet field active
  have stopped := from_rows field.phase.pending.input configuration.view proof reconstructed built first head previous current fuel
    (NativeScalarBatchVerifier.initial transcript statement proof) world (le_of_eq lastRound)
  have parentEq : configuration.parent transcript.profile = transcript :=
    ScalarChallengeInputView.rebuild_transcript transcript before decoded
  have reconstructedOk := ScalarRecoveredReplay.initialized _ configuration recoverFound transcript.profile
  change NativeScalarBatchPreflight.beginVerify (configuration.parent transcript.profile) statement reconstructed =
    .ok (NativeScalarBatchWire.bindStatement (configuration.parent transcript.profile) statement) at reconstructedOk
  rw [parentEq,← preflight.2.2] at reconstructedOk
  have startEq : configuration.initial transcript.profile = NativeScalarBatchVerifier.initial transcript statement proof := by
    change NativeScalarBatchVerifier.initial (configuration.parent transcript.profile) statement reconstructed = _
    rw [parentEq]
    exact (ScalarProofPrefixExecution.initial_eq transcript result statement proof reconstructed accepted reconstructedOk).symm
  exact ⟨configuration,recoverFound,rfl,rfl,by rw [startEq]; exact stopped⟩

/-- Actual expected values, common point and completed records are now fixed
by causal recovered replay. They are not supplied fiberwise witnesses. -/
theorem sampler_prior (transcript result : Transcript) (before : List TranscriptFrame.Frame) (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (fuel : ℕ) (world : World) (packet : RoundPacket) (field : NativeFieldVector.State)
    (active : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling packet field) :
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover field.phase.pending.input = some configuration ∧
      configuration.view.history.statement = statement ∧ configuration.view.packet = packet ∧
      (ScalarStoppedReplay.execute field.phase.pending.input statement configuration.proof fuel
        (configuration.initial transcript.profile) world).1.1 = true ∧
      ScalarPriorStability.prior (ScalarStoppedReplay.execute field.phase.pending.input statement configuration.proof fuel
        (configuration.initial transcript.profile) world).1.2 =
        ScalarPriorStability.prior (NativeScalarBatchVerifier.execute statement proof fuel
          (NativeScalarBatchVerifier.initial transcript statement proof) world).1 := by
  obtain ⟨configuration,found,statementEq,packetEq,stopped⟩ := sampling transcript result before statement proof
    decoded accepted statementFits domain fuel world packet field active
  have original := ScalarStoppedPrior.original_prior transcript result before statement proof
    decoded accepted statementFits domain fuel world packet field active
  rw [stopped] at original
  exact ⟨configuration,found,statementEq,packetEq,original⟩

end FormalProof4FHE.HasteBoots.ScalarRecoveredStoppedAgreement
