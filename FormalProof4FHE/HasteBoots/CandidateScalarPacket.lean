module
public import FormalProof4FHE.HasteBoots.CandidateIdentityTables
public import FormalProof4FHE.HasteBoots.ChildHeaderProfile
@[expose] public section

/-! Literal scalar inputs bind the actual native statement and round packet
of attainable candidates. Recovery and equation-slot lookup use the original
completed reader retained by the candidate, rather than a chosen packet. -/
namespace FormalProof4FHE.HasteBoots.CandidateScalarPacket
open InputIndexedOracle (World)
open OracleProgram (Program)
open JobReferenceCandidate (Candidate)
noncomputable section

abbrev reader {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) := candidate.compression.value.view.reader

theorem recovered {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover candidate.selection.family.input = some configuration ∧
      TranscriptFrame.encodeMany configuration.view.history.before = candidate.selection.origin.ready.equality.transcript.input ∧
      configuration.view.history.statement = candidate.selection.origin.ready.statement ∧
      configuration.view.packet = (reader candidate).entry.packet := by
  obtain ⟨configuration,found,parent,statement,packet⟩ := ScalarParentRecovery.recover (reader candidate)
  rw [candidate.compression.input_eq] at found
  exact ⟨configuration,found,parent.trans (congrArg NativeTranscript.Transcript.input candidate.reader_transcript),
    statement.trans candidate.reader_statement,packet⟩

theorem of_found {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover candidate.selection.family.input = some configuration) :
    TranscriptFrame.encodeMany configuration.view.history.before = candidate.selection.origin.ready.equality.transcript.input ∧
      configuration.view.history.statement = candidate.selection.origin.ready.statement ∧
      configuration.view.packet = (reader candidate).entry.packet := by
  obtain ⟨actual,recoverFound,parent,statement,packet⟩ := recovered candidate
  have same := Option.some.inj (recoverFound.symm.trans found)
  cases same
  exact ⟨parent,statement,packet⟩


theorem same_recovery {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.selection.family.input = right.selection.family.input)
    (lc rc : ScalarRecoveredReplay.Configuration)
    (lf : ScalarRecoveredReplay.recover left.selection.family.input = some lc)
    (rf : ScalarRecoveredReplay.recover right.selection.family.input = some rc) : lc = rc := by
  rw [input] at lf
  exact Option.some.inj (lf.symm.trans rf)

theorem compare {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.selection.family.input = right.selection.family.input) :
    left.selection.origin.ready.equality.transcript.input = right.selection.origin.ready.equality.transcript.input ∧
      left.selection.origin.ready.statement = right.selection.origin.ready.statement ∧
      (reader left).entry.packet = (reader right).entry.packet := by
  have same := left.compression.input_eq.trans (input.trans right.compression.input_eq.symm)
  obtain ⟨parent,statement,packet⟩ := ScalarParentRecovery.compare (reader left) (reader right) same
  exact ⟨(congrArg NativeTranscript.Transcript.input left.reader_transcript).symm.trans
    (parent.trans (congrArg NativeTranscript.Transcript.input right.reader_transcript)),
    left.reader_statement.symm.trans (statement.trans right.reader_statement),packet⟩

theorem message {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.selection.family.input = right.selection.family.input)
    (ordinal : left.selection.index.val = right.selection.index.val) :
    (reader left).entry.packet.messages.val[2*left.selection.index.val+1]? =
      (reader right).entry.packet.messages.val[2*right.selection.index.val+1]? := by
  rw [(compare left right input).2.2,ordinal]

/-- The slot is the original job's odd identity equation, including repetitions. -/
theorem identity_info {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    candidate.selection.origin.ready.statement.infos.val[2*candidate.selection.index.val+1]? =
      some (LookupScalarGrammar.identityInfo candidate.selection.origin.geometry.geometry.1
        (candidate.selection.origin.ready.jobs.get candidate.selection.index).tag.request) := by
  exact (LookupScalarGrammar.protocol_pair candidate.selection.ctx.requests.property.le
    (NativeSharedLookupParent.models candidate.selection.ctx.requests) candidate.selection.origin.geometry.geometry.1
    candidate.selection.ctx.proof.values.multiplicities candidate.selection.ctx.proof.values.roots
    candidate.selection.ctx.proof.roots.property 7 candidate.selection.ctx.lookupFuel candidate.selection.ctx.equalityFuel
    (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row candidate.selection.ctx.registry
      candidate.selection.ctx.helper candidate.selection.ctx.parent candidate.selection.ctx.requests candidate.selection.ctx.proof world)
    world candidate.selection.origin.ready candidate.selection.origin.prepared candidate.selection.index.val candidate.selection.index.isLt).2.1

theorem same_identity_info {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.selection.family.input = right.selection.family.input)
    (ordinal : left.selection.index.val = right.selection.index.val) :
    LookupScalarGrammar.identityInfo left.selection.origin.geometry.geometry.1
      (left.selection.origin.ready.jobs.get left.selection.index).tag.request =
    LookupScalarGrammar.identityInfo right.selection.origin.geometry.geometry.1
      (right.selection.origin.ready.jobs.get right.selection.index).tag.request := by
  have info := identity_info left
  rw [(compare left right input).2.1,ordinal,identity_info right] at info
  exact Option.some.inj info.symm


theorem header {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    ∃ label context seed, NativeChildSeedView.HasHeader candidate.selection.origin.ready.equality.transcript
      candidate.selection.origin.ready.equality.transcript.profile label context seed := by
  let parent := (OracleProgram.run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row
    candidate.selection.ctx.registry candidate.selection.ctx.helper candidate.selection.ctx.parent candidate.selection.ctx.requests) world).run.1.1
  have extension := NativeLookupTranscriptExtension.ready_extends candidate.selection.ctx.requests.property.le
    (NativeSharedLookupParent.models candidate.selection.ctx.requests) candidate.selection.origin.geometry.geometry.1
    candidate.selection.ctx.proof.values.multiplicities candidate.selection.ctx.proof.values.roots candidate.selection.ctx.proof.roots.property
    7 candidate.selection.ctx.lookupFuel candidate.selection.ctx.equalityFuel
    (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row candidate.selection.ctx.registry candidate.selection.ctx.helper
      candidate.selection.ctx.parent candidate.selection.ctx.requests candidate.selection.ctx.proof world)
    world candidate.selection.origin.ready candidate.selection.origin.prepared (by decide +kernel) candidate.roots_fit
  have start := NativeForkAncestry.start_header world parent candidate.selection.ctx.proof.multiplicities
  have childProfile : (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row candidate.selection.ctx.registry candidate.selection.ctx.helper
      candidate.selection.ctx.parent candidate.selection.ctx.requests candidate.selection.ctx.proof world).profile = parent.profile := rfl
  have profile := extension.choose_spec.2.2.trans childProfile
  rw [← profile] at start
  exact ⟨_,_,_,extension.header start⟩

theorem profile {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.selection.family.input = right.selection.family.input) :
    left.selection.origin.ready.equality.transcript.profile = right.selection.origin.ready.equality.transcript.profile := by
  obtain ⟨ll,lc,ls,lh⟩ := header left
  obtain ⟨rl,rc,rs,rh⟩ := header right
  exact ChildHeaderProfile.compare lh rh (compare left right input).1

end
end FormalProof4FHE.HasteBoots.CandidateScalarPacket
