module
public import FormalProof4FHE.HasteBoots.ScalarCompletedOrigin
@[expose] public section

/-! Literal completed native round challenges satisfy the same eventual
collector event used by the causal all-budget law. Collector correspondence
and a producing original prefix are derived from actual execution records. -/
namespace FormalProof4FHE.HasteBoots.ScalarCompletedChallenge
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeRootMessage (Digest)
open NativeScalarBatchWire (Statement challengeLabel)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (CompletedRound)

private theorem transcript_eq (left right : Transcript) (input : left.input = right.input) (profile : left.profile = right.profile) : left = right := by
  cases left
  cases right
  cases input
  cases profile
  rfl

/-- The recovered phase is the original reader with its cursor reset to zero,
not a freshly sampled or canonicalized challenge value. -/
theorem phase_eq_start (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration) (profile : Digest)
    (field : NativeFieldVector.State) (sameInput : field.phase.pending.input = input)
    (sameProfile : field.phase.pending.profile = profile) :
    configuration.phase profile = ScalarCollectorTrace.start field := by
  have pending := transcript_eq (configuration.phase profile).pending field.phase.pending
    ((ScalarRecoveredReplay.phase_input input configuration found profile).trans sameInput.symm)
    (by change profile = field.phase.pending.profile; exact sameProfile.symm)
  calc
    configuration.phase profile = ⟨(configuration.phase profile).pending,challengeLabel,[]⟩ := rfl
    _ = ScalarCollectorTrace.start field := by rw [pending]; rfl

/-- A retained completed record's literal decoded word is the value of its
original native collector at some candidate-analysis prefix. -/
theorem value (transcript : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World)
    (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed) :
    ∃ collected, GoldScalarChallengeLaw.values collected (ScalarCollectorTrace.start entry.coefficients) world =
      some (NativeFieldWire.goldExtensionValue entry.challenge) := by
  have traced := ScalarCollectorTrace.initialized transcript statement proof fuel world
  obtain ⟨source,complete,decoded⟩ := traced.2 entry member
  exact ScalarCollectorTrace.decoded_value entry.coefficients world source complete entry.challenge decoded

/-- Retained source profiles are inherited from the original transcript. -/
theorem profile (transcript : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed) :
    entry.coefficients.phase.pending.profile = transcript.profile := by
  have preserved := NativeScalarTranscriptExtension.execute transcript statement proof fuel _ world domain
    (NativeScalarTranscriptExtension.initial transcript statement proof statementFits)
  obtain ⟨_,_,_,inherited⟩ := (preserved.2.2 entry member).1
  exact inherited

/-- Collector completion at the recovered phase follows from original native
completion. No supplied equality to an ideal or independently sampled value. -/
theorem recovered_value (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration)
    (transcript : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed)
    (sameInput : entry.coefficients.phase.pending.input = input) :
    ∃ collected, GoldScalarChallengeLaw.values collected (configuration.phase transcript.profile) world =
      some (NativeFieldWire.goldExtensionValue entry.challenge) := by
  rw [phase_eq_start input configuration found transcript.profile entry.coefficients sameInput
    (profile transcript statement proof fuel world statementFits domain entry member)]
  exact value transcript statement proof fuel world entry member

/-- Actual completion also guarantees successful causal input classification,
with the original statement, packet and collected challenge value. -/
theorem recover_completed (transcript result : Transcript) (before : List TranscriptFrame.Frame)
    (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (fuel : ℕ) (world : World) (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed) :
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
      configuration.view.history.statement = statement ∧ configuration.view.packet = entry.packet ∧
      ∃ collected, GoldScalarChallengeLaw.values collected (configuration.phase transcript.profile) world =
        some (NativeFieldWire.goldExtensionValue entry.challenge) := by
  obtain ⟨index,_,produced⟩ := ScalarCompletedOrigin.initialized transcript statement proof fuel world entry member
  obtain ⟨field,next,active,finished,_,_,_⟩ := produced
  obtain ⟨configuration,found,statementEq,packetEq,_⟩ := ScalarExecutionPrefixAgreement.sampling
    transcript result before statement proof decoded accepted statementFits domain index world entry.packet field active
  have header := ScalarExecutionTranscript.drive_header NativeFields.goldilocksModulus 1 field world
  rw [finished] at header
  have sameInput := congrArg Transcript.input header.1
  rw [← sameInput] at found
  exact ⟨configuration,found,statementEq,packetEq,recovered_value _ configuration found transcript statement proof fuel world
    statementFits domain entry member rfl⟩

/-- Every actual completed record supplies its original producing sampler
and a transfer from that sampler's actual prior test to the all-budget event.
The collector-value premise of the earlier active-sampler transfer is derived. -/
theorem completed_witness (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration)
    (transcript result : Transcript) (before : List TranscriptFrame.Frame) (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (fuel : ℕ) (world : World) (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed)
    (sameInput : entry.coefficients.phase.pending.input = input)
    (bad : ScalarRecoveredUnboundedLaw.Prior → NativeExtensionFields.Goldilocks3 → Prop) :
    ∃ index < fuel,
      ScalarCompletedOrigin.Produced (NativeScalarBatchVerifier.execute statement proof index
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1 world entry ∧
      (bad (ScalarPriorStability.prior (NativeScalarBatchVerifier.execute statement proof index
          (NativeScalarBatchVerifier.initial transcript statement proof) world).1)
        (NativeFieldWire.goldExtensionValue entry.challenge) →
          ScalarRecoveredUnboundedLaw.event input configuration transcript.profile bad world) := by
  obtain ⟨index,bound,produced⟩ := ScalarCompletedOrigin.initialized transcript statement proof fuel world entry member
  have originalProduced := produced
  obtain ⟨field,next,active,finished,_,_,_⟩ := produced
  have header := ScalarExecutionTranscript.drive_header NativeFields.goldilocksModulus 1 field world
  rw [finished] at header
  have originalInput : field.phase.pending.input = input := by rw [← header.1]; exact sameInput
  obtain ⟨collected,values⟩ := recovered_value input configuration found transcript statement proof fuel world
    statementFits domain entry member sameInput
  refine ⟨index,bound,originalProduced,?_⟩
  intro failed
  exact ScalarRecoveredUnboundedLaw.original_witness input configuration found transcript result before statement proof
    decoded accepted statementFits domain index world entry.packet field active originalInput collected
    (NativeFieldWire.goldExtensionValue entry.challenge) values bad failed

end FormalProof4FHE.HasteBoots.ScalarCompletedChallenge
