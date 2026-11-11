module
public import FormalProof4FHE.HasteBoots.ScalarReconstructionCompleteness
public import FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension
import all Init.Data.String.Defs
@[expose] public section

/-! Coverage of strict scalar-input recovery by original initialized native
executions. Frame-size premises are the existing explicit allocation domains;
packet associations and reconstruction success are derived from execution. -/
namespace FormalProof4FHE.HasteBoots.ScalarExecutionRecovery
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)
open TranscriptFrame (Frame)
open ScalarExecutionTranscript (Rounds history Records)

theorem history_valid (before : List Frame) (statement : Statement) (rounds : Rounds)
    (prior : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (packetFits : ∀ pair ∈ rounds, (NativeScalarBatchWire.roundCodec.encode pair.1).length < TranscriptFrame.lengthLimit)
    (lengths : ∀ pair ∈ rounds, pair.2.length = 80) :
    ∀ frame ∈ (history before statement rounds).frames, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [history,ScalarTranscriptPrefix.History.frames,List.mem_append,List.mem_singleton] at member
  rcases member with (old | same) | later
  · exact prior frame old
  · subst frame
    exact ⟨by change NativeScalarBatchWire.statementLabel.length < _; decide +kernel,statementFits⟩
  · obtain ⟨pair,inRounds,inBlock⟩ := List.mem_flatMap.mp later
    have blockEq : ScalarTranscriptPrefix.block pair.1 pair.2 =
        (ScalarChallengeInputView.View.mk [] pair.1).frames ++ [ScalarTranscriptPrefix.receiptFrame pair.2] := rfl
    rw [blockEq] at inBlock
    rcases List.mem_append.mp inBlock with scalar | receipt
    · exact ScalarChallengeInputView.frames_valid [] pair.1 (by simp) (packetFits pair inRounds) frame scalar
    · cases List.mem_singleton.mp receipt
      exact ⟨by change NativeScalarBatchWire.challengeLabel.length < _; decide +kernel,
        by change pair.2.length < _; rw [lengths pair inRounds]; decide +kernel⟩

/-- Operational invariant form of recovery coverage. -/
theorem sampling_of_invariants (before : List Frame) (statement : Statement) (proof : Proof)
    (profile : NativeRootMessage.Digest) (machine : Machine) (first : NativeScalarBatchWire.Info)
    (head : statement.infos.val.head? = some first) (admitted : NativeScalarBatchPreflight.dimensions statement = true)
    (prior : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (packet : RoundPacket) (field : NativeFieldVector.State) (active : machine.control = .sampling packet field)
    (aligned : ScalarExecutionTranscript.Aligned before statement profile machine)
    (linked : NativeScalarBatchHistory.Linked statement proof machine)
    (valid : NativeScalarBatchVerifierInvariant.Valid statement first machine) :
    ∃ rounds : Rounds, ∃ reconstructed : Proof,
      ScalarRecoveredReplay.recover field.phase.pending.input =
        some ⟨⟨history before statement rounds,packet⟩,reconstructed⟩ ∧ Records rounds machine ∧
      (∀ pair ∈ rounds, NativeScalarBatchRoundPacket.packet pair.1.round proof = some pair.1) ∧
      NativeScalarBatchRoundPacket.packet packet.round proof = some packet := by
  rw [ScalarExecutionTranscript.Aligned,active] at aligned
  obtain ⟨rounds,records,_,pending,_⟩ := aligned
  have source := linked.2
  rw [active] at source
  have originals : ∀ pair ∈ rounds, NativeScalarBatchRoundPacket.packet pair.1.round proof = some pair.1 := by
    intro pair member
    have packetMember : pair.1 ∈ machine.completed.map (fun entry => entry.packet) := by
      rw [← records.1]
      exact List.mem_map.mpr ⟨pair,member,rfl⟩
    obtain ⟨entry,inCompleted,same⟩ := List.mem_map.mp packetMember
    rw [← same]
    exact (NativeScalarBatchHistory.chain_all linked.1 entry inCompleted).2
  have counts := congrArg List.length records.1
  simp only [List.length_map] at counts
  have completedCount := valid.2.2.2.1
  have phase := valid.2.2.2.2
  rw [active] at phase
  have ordinal : packet.round.val = rounds.length := phase.2.1.trans (completedCount.symm.trans counts.symm)
  have ordinals : rounds.map (fun pair => pair.1.round.val) = List.range rounds.length := by
    have mapped := congrArg (List.map (fun p : RoundPacket => p.round.val)) records.1
    simp only [List.map_map,Function.comp_def] at mapped
    rw [mapped,NativeScalarBatchHistory.chain_ordinals linked.1,counts]
  have rows : ∀ p ∈ rounds.map Prod.fst ++ [packet],
      List.Forall₂ (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1)
        statement.infos.val p.messages.val := by
    intro p member
    rcases List.mem_append.mp member with old | current
    · rw [records.1] at old
      obtain ⟨entry,inCompleted,same⟩ := List.mem_map.mp old
      rw [← same]
      exact (NativeScalarBatchHistory.chain_all linked.1 entry inCompleted).1.1
    · cases List.mem_singleton.mp current
      exact phase.2.2.1
  obtain ⟨reconstructed,built⟩ := ScalarReconstructionCompleteness.reconstruct
    ⟨history before statement rounds,packet⟩ first head admitted ordinals ordinal (by rw [phase.2.1]; exact phase.1) rows
  have framed := history_valid before statement rounds prior statementFits
    (fun pair member => domain _ _ (originals pair member)) records.2
  have native := ScalarRecoveredReplay.recover_native ⟨history before statement rounds,packet⟩ profile
    (ScalarChallengeInputView.frames_valid _ packet framed (domain _ _ source)) records.2 reconstructed built
  have inputEq : field.phase.pending.input =
      TranscriptFrame.encodeMany (ScalarChallengeInputView.View.mk (history before statement rounds).frames packet).frames := by
    rw [pending]
    exact ScalarChallengeInputView.phase_input (ScalarChallengeInputView.View.mk (history before statement rounds).frames packet) profile
  exact ⟨rounds,reconstructed,by rw [inputEq]; exact native,records,originals,source⟩

/-- Every active original scalar request has a strictly parseable complete
history, a successfully reconstructed native proof, and derived original
packet associations. Rejected candidates and suspended prefixes are included. -/
theorem sampling (transcript result : Transcript) (before : List Frame) (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (fuel : ℕ) (world : World) (packet : RoundPacket) (field : NativeFieldVector.State)
    (active : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling packet field) :
    ∃ rounds : Rounds, ∃ reconstructed : Proof,
      ScalarRecoveredReplay.recover field.phase.pending.input =
        some ⟨⟨history before statement rounds,packet⟩,reconstructed⟩ ∧
      Records rounds (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1 ∧
      (∀ pair ∈ rounds, NativeScalarBatchRoundPacket.packet pair.1.round proof = some pair.1) ∧
      NativeScalarBatchRoundPacket.packet packet.round proof = some packet := by
  have preflight := (NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mp accepted
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success statement preflight.2.1
  exact sampling_of_invariants before statement proof transcript.profile _ first head preflight.2.1
    (TranscriptFrame.decodeAll_sound _ _ decoded).1 statementFits domain packet field active
    (ScalarExecutionTranscript.initialized transcript result before statement proof decoded accepted fuel world)
    (NativeScalarBatchHistory.initialized_linked transcript result statement proof accepted fuel world)
    (NativeScalarBatchVerifierInvariant.execute_valid statement proof first preflight.1 preflight.2.1 head fuel _ world
      (NativeScalarBatchVerifierInvariant.initial_valid transcript result statement proof first accepted))

end FormalProof4FHE.HasteBoots.ScalarExecutionRecovery
