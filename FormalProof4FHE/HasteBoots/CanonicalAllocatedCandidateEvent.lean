module
public import FormalProof4FHE.HasteBoots.CanonicalAttainableEvent
@[expose] public section

/-! Actual native source-healing tests transport to attainable candidates
through exact original job provenance and complete function equality. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedCandidateEvent
open InputIndexedOracle (World)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open NativeFieldWire (goldExtensionValue)
open NativeScalarQueryShape (laneBits)
open JobReferenceCandidate (Candidate)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open MatrixFold (Cube)
open AllocatedCandidateEvent (nativeTest)
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

theorem native_eq {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (dummy : Digest) (message : NativeScalarBatchWire.Message) :
    CanonicalCandidateTest.test candidate dummy message = nativeTest candidate.selection.origin candidate.selection.index candidate.selection.job
      (CanonicalCandidateFixation.sources candidate dummy) (CanonicalCandidateFixation.helpers candidate dummy) message := by
  by_cases branch : (candidate.selection.origin.ready.jobs.get candidate.selection.index).tag.request.terminal.logicalLength.val =
      2^candidate.selection.origin.geometry.geometry.1.val
  · rw [CanonicalCandidateTest.full_branch candidate dummy message branch]
    simp only [nativeTest,branch,ite_true]
    rfl
  · rw [CanonicalCandidateTest.partial_branch candidate dummy message branch]
    simp only [nativeTest,branch,ite_false]
    rfl

theorem correspondence {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube body.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)
    (dummy : Digest) (message : NativeScalarBatchWire.Message)
    (ctxEq : candidate.selection.ctx = ctx) (bodyEq : candidate.selection.body = body)
    (originEq : HEq candidate.selection.origin origin) (ordinal : candidate.selection.index.val = index.val)
    (jobEq : HEq candidate.selection.job job)
    (sourcesEq : HEq (CanonicalCandidateFixation.sources candidate dummy) sources)
    (helpersEq : HEq (CanonicalCandidateFixation.helpers candidate dummy) helpers) :
    candidate.selection.origin.ready.equality.transcript = origin.ready.equality.transcript ∧
      CanonicalCandidateTest.test candidate dummy message = nativeTest origin index job sources helpers message := by
  subst ctx
  subst body
  have actualOrigin := eq_of_heq originEq
  subst origin
  have actualIndex : candidate.selection.index = index := Fin.ext ordinal
  subst index
  have actualJob := eq_of_heq jobEq
  subst job
  have actualSources := eq_of_heq sourcesEq
  subst sources
  have actualHelpers := eq_of_heq helpersEq
  subst helpers
  exact ⟨rfl,native_eq candidate dummy message⟩

theorem of_witness {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube body.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)
    (dummy : Digest) (entry : NativeScalarBatchVerifier.CompletedRound)
    (ctxEq : candidate.selection.ctx = ctx) (bodyEq : candidate.selection.body = body)
    (originEq : HEq candidate.selection.origin origin) (ordinal : candidate.selection.index.val = index.val)
    (jobEq : HEq candidate.selection.job job)
    (sourcesEq : HEq (CanonicalCandidateFixation.sources candidate dummy) sources)
    (helpersEq : HEq (CanonicalCandidateFixation.helpers candidate dummy) helpers)
    (inputEq : candidate.selection.family.input = entry.coefficients.phase.pending.input)
    (entryEq : (CandidateScalarPacket.reader candidate).entry = entry)
    (message : NativeScalarBatchWire.Message) (messageAt : entry.packet.messages.val[2*index.val+1]? = some message)
    (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration)
    (healing : ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration origin.ready.equality.transcript.profile
      (nativeTest origin index job sources helpers message) world) :
    CanonicalAttainableEvent.Event program position entry.coefficients.phase.pending.input index.val dummy world := by
  have linked := correspondence candidate origin index job sources helpers dummy message ctxEq bodyEq originEq ordinal jobEq sourcesEq helpersEq
  let packet : CanonicalAttainableEvent.Packet program position entry.coefficients.phase.pending.input index.val world :=
    ⟨⟨candidate,inputEq,ordinal⟩,message,by rw [entryEq,ordinal]; exact messageAt,configuration,by rw [inputEq]; exact found⟩
  refine ⟨packet,?_⟩
  change ScalarRecoveredUnboundedLaw.event candidate.selection.family.input configuration candidate.selection.origin.ready.equality.transcript.profile
    (CanonicalCandidateTest.test candidate dummy message) world
  rw [inputEq,linked.1,linked.2]
  exact healing

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedCandidateEvent
