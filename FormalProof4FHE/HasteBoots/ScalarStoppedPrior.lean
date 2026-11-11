module
public import FormalProof4FHE.HasteBoots.ScalarFirstMatch
@[expose] public section

/-! Stopping before a selected scalar reader preserves the original active
round's prior expected vector, common point and completed records. Input
identity is related to original round identity by strict execution recovery. -/
namespace FormalProof4FHE.HasteBoots.ScalarStoppedPrior
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)

/-- The native active packet's ordinal is the actual machine round. -/
theorem active_round (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (fuel : ℕ) (world : World) (packet : RoundPacket) (field : NativeFieldVector.State)
    (active : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling packet field) :
    (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.round = packet.round.val := by
  have preflight := (NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mp accepted
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success statement preflight.2.1
  have valid := NativeScalarBatchVerifierInvariant.execute_valid statement proof first preflight.1 preflight.2.1 head fuel _ world
    (NativeScalarBatchVerifierInvariant.initial_valid transcript result statement proof first accepted)
  have phase := valid.2.2.2.2
  rw [active] at phase
  exact phase.2.1.symm

/-- Two actual requests on the same full input have the same original round.
No receipt-inversion or challenge-collision assumption is introduced. -/
theorem same_input_round (transcript result : Transcript) (before : List TranscriptFrame.Frame)
    (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (first later : ℕ) (world : World) (firstPacket laterPacket : RoundPacket) (firstField laterField : NativeFieldVector.State)
    (firstActive : (NativeScalarBatchVerifier.execute statement proof first
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling firstPacket firstField)
    (laterActive : (NativeScalarBatchVerifier.execute statement proof later
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling laterPacket laterField)
    (same : firstField.phase.pending.input = laterField.phase.pending.input) :
    (NativeScalarBatchVerifier.execute statement proof first (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.round =
      (NativeScalarBatchVerifier.execute statement proof later (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.round := by
  obtain ⟨firstRounds,firstProof,firstFound,_,_,_⟩ := ScalarExecutionRecovery.sampling transcript result before statement proof
    decoded accepted statementFits domain first world firstPacket firstField firstActive
  obtain ⟨laterRounds,laterProof,laterFound,_,_,_⟩ := ScalarExecutionRecovery.sampling transcript result before statement proof
    decoded accepted statementFits domain later world laterPacket laterField laterActive
  rw [same] at firstFound
  have configurations := Option.some.inj (firstFound.symm.trans laterFound)
  have packets := congrArg (fun config : ScalarRecoveredReplay.Configuration => config.view.packet) configurations
  rw [active_round transcript result statement proof accepted first world firstPacket firstField firstActive,
    active_round transcript result statement proof accepted later world laterPacket laterField laterActive]
  exact congrArg (fun packet : RoundPacket => packet.round.val) packets

/-- A blocked state in the original initialized run is an active request with
the same round counter as the selected original sampler. -/
theorem blocked_round (transcript result : Transcript) (before : List TranscriptFrame.Frame)
    (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (first later : ℕ) (world : World) (packet : RoundPacket) (field : NativeFieldVector.State)
    (active : (NativeScalarBatchVerifier.execute statement proof later
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling packet field)
    (blocked : ScalarStoppedReplay.blocked field.phase.pending.input
      (NativeScalarBatchVerifier.execute statement proof first (NativeScalarBatchVerifier.initial transcript statement proof) world).1 = true) :
    (NativeScalarBatchVerifier.execute statement proof first (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.round =
      (NativeScalarBatchVerifier.execute statement proof later (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.round := by
  cases control : (NativeScalarBatchVerifier.execute statement proof first
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control with
  | ready => simp only [ScalarStoppedReplay.blocked,control,Bool.false_eq_true] at blocked
  | finished claims => simp only [ScalarStoppedReplay.blocked,control,Bool.false_eq_true] at blocked
  | failed error => simp only [ScalarStoppedReplay.blocked,control,Bool.false_eq_true] at blocked
  | sampling previous previousField =>
    have same : previousField.phase.pending.input = field.phase.pending.input := by
      simpa only [ScalarStoppedReplay.blocked,control,decide_eq_true_eq] using blocked
    exact same_input_round transcript result before statement proof decoded accepted statementFits domain
      first later world previous packet previousField field control active same

/-- The first stopped original state retains the exact prior used by a later
active instance of that input, even after rejected and accepted partial reads. -/
theorem original_prior (transcript result : Transcript) (before : List TranscriptFrame.Frame)
    (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (fuel : ℕ) (world : World) (packet : RoundPacket) (field : NativeFieldVector.State)
    (active : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling packet field) :
    (ScalarStoppedReplay.execute field.phase.pending.input statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.1 = true ∧
    ScalarPriorStability.prior (ScalarStoppedReplay.execute field.phase.pending.input statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.2 =
      ScalarPriorStability.prior (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1 := by
  have matched : ScalarStoppedReplay.blocked field.phase.pending.input
      (NativeScalarBatchVerifier.execute statement proof fuel (NativeScalarBatchVerifier.initial transcript statement proof) world).1 = true := by
    simp only [ScalarStoppedReplay.blocked,active,decide_true]
  obtain ⟨used,bound,hit,_,stopped⟩ := ScalarFirstMatch.exists_first field.phase.pending.input statement proof fuel
    (NativeScalarBatchVerifier.initial transcript statement proof) world matched
  rw [stopped]
  refine ⟨rfl,?_⟩
  have sameRound := blocked_round transcript result before statement proof decoded accepted statementFits domain
    used fuel world packet field active hit
  exact (ScalarPriorStability.earlier statement proof used fuel bound
    (NativeScalarBatchVerifier.initial transcript statement proof) world sameRound.symm).symm

end FormalProof4FHE.HasteBoots.ScalarStoppedPrior
