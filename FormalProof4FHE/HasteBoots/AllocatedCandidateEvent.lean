module
public import FormalProof4FHE.HasteBoots.AttainableIdentityEvent
@[expose] public section

/-! Actual native source-healing tests transport to attainable candidates
through exact original job provenance and complete function equality. -/
namespace FormalProof4FHE.HasteBoots.AllocatedCandidateEvent
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
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

def nativeTest (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube body.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)
    (message : NativeScalarBatchWire.Message) :=
  if (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val = 2^origin.geometry.geometry.1.val then
    ScalarSourceChallengeBound.test (LookupScalarGrammar.identityInfo origin.geometry.geometry.1 (origin.ready.jobs.get index).tag.request)
      message ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
      (laneBits (3+origin.padding)+body.sourceVariables) (LookupIdentityCausalReduction.fullTables job.view sources helpers)
  else
    ScalarSourceChallengeBound.test (LookupScalarGrammar.identityInfo origin.geometry.geometry.1 (origin.ready.jobs.get index).tag.request)
      message ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (origin.ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
      (laneBits (3+origin.padding)+body.sourceVariables) (LookupIdentityCausalReduction.partialTables job.view sources helpers)

theorem native_eq {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (dummy : Digest) (radius : ℕ) (message : NativeScalarBatchWire.Message) :
    CandidateIdentityTest.test candidate dummy radius message = nativeTest candidate.selection.origin candidate.selection.index candidate.selection.job
      (candidate.selection.sources dummy radius) (candidate.selection.helpers dummy radius) message := by
  by_cases branch : (candidate.selection.origin.ready.jobs.get candidate.selection.index).tag.request.terminal.logicalLength.val =
      2^candidate.selection.origin.geometry.geometry.1.val
  · rw [CandidateIdentityTest.full_branch candidate dummy radius message branch]
    simp only [nativeTest,branch,ite_true]
    rfl
  · rw [CandidateIdentityTest.partial_branch candidate dummy radius message branch]
    simp only [nativeTest,branch,ite_false]
    rfl

theorem correspondence {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube body.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)
    (dummy : Digest) (radius : ℕ) (message : NativeScalarBatchWire.Message)
    (ctxEq : candidate.selection.ctx = ctx) (bodyEq : candidate.selection.body = body)
    (originEq : HEq candidate.selection.origin origin) (ordinal : candidate.selection.index.val = index.val)
    (jobEq : HEq candidate.selection.job job)
    (sourcesEq : HEq (candidate.selection.sources dummy radius) sources)
    (helpersEq : HEq (candidate.selection.helpers dummy radius) helpers) :
    candidate.selection.origin.ready.equality.transcript = origin.ready.equality.transcript ∧
      CandidateIdentityTest.test candidate dummy radius message = nativeTest origin index job sources helpers message := by
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
  exact ⟨rfl,native_eq candidate dummy radius message⟩

theorem of_witness {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube body.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)
    (dummy : Digest) (radius : ℕ) (entry : NativeScalarBatchVerifier.CompletedRound)
    (ctxEq : candidate.selection.ctx = ctx) (bodyEq : candidate.selection.body = body)
    (originEq : HEq candidate.selection.origin origin) (ordinal : candidate.selection.index.val = index.val)
    (jobEq : HEq candidate.selection.job job)
    (sourcesEq : HEq (candidate.selection.sources dummy radius) sources)
    (helpersEq : HEq (candidate.selection.helpers dummy radius) helpers)
    (inputEq : candidate.selection.family.input = entry.coefficients.phase.pending.input)
    (entryEq : (CandidateScalarPacket.reader candidate).entry = entry)
    (message : NativeScalarBatchWire.Message) (messageAt : entry.packet.messages.val[2*index.val+1]? = some message)
    (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration)
    (healing : ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration origin.ready.equality.transcript.profile
      (nativeTest origin index job sources helpers message) world) :
    AttainableIdentityEvent.Event program position entry.coefficients.phase.pending.input index.val dummy radius world := by
  have linked := correspondence candidate origin index job sources helpers dummy radius message ctxEq bodyEq originEq ordinal jobEq sourcesEq helpersEq
  let packet : AttainableIdentityEvent.Packet program position entry.coefficients.phase.pending.input index.val world :=
    ⟨⟨candidate,inputEq,ordinal⟩,message,by rw [entryEq,ordinal]; exact messageAt,configuration,by rw [inputEq]; exact found⟩
  refine ⟨packet,?_⟩
  change ScalarRecoveredUnboundedLaw.event candidate.selection.family.input configuration candidate.selection.origin.ready.equality.transcript.profile
    (CandidateIdentityTest.test candidate dummy radius message) world
  rw [inputEq,linked.1,linked.2]
  exact healing

end
end FormalProof4FHE.HasteBoots.AllocatedCandidateEvent
