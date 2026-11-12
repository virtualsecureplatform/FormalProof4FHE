module
public import FormalProof4FHE.HasteBoots.CanonicalSumAttainableEvent
public import FormalProof4FHE.HasteBoots.AllocatedSumAlternatives
@[expose] public section

/-! Original even-slot healing reaches the attained canonical sum test by
exact native origin, reader, message and complete helper-family equality. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedSumEvent
open InputIndexedOracle (World)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open NativeScalarQueryShape (laneBits)
open JobReferenceCandidate (Candidate)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open MatrixFold (Cube)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

def nativeTest (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)
    (message : NativeScalarBatchWire.Message) :=
  ScalarSourceChallengeBound.test (LookupScalarGrammar.sumInfo origin.geometry.geometry.1) message ScalarLookupExpression.sumArity
    ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices (laneBits (3+origin.padding)+body.sourceVariables)
    (LookupViewSumReduction.tables helpers)

theorem native_eq {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (dummy : Digest) (message : NativeScalarBatchWire.Message) :
    CanonicalSumCandidate.test candidate dummy message = nativeTest candidate.selection.origin
      (CanonicalCandidateFixation.helpers candidate dummy) message := rfl

theorem correspondence {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)
    (dummy : Digest) (message : NativeScalarBatchWire.Message)
    (ctxEq : candidate.selection.ctx = ctx) (bodyEq : candidate.selection.body = body)
    (originEq : HEq candidate.selection.origin origin)
    (helpersEq : HEq (CanonicalCandidateFixation.helpers candidate dummy) helpers) :
    candidate.selection.origin.ready.equality.transcript = origin.ready.equality.transcript ∧
      CanonicalSumCandidate.test candidate dummy message = nativeTest origin helpers message := by
  subst ctx body
  have sameOrigin := eq_of_heq originEq
  subst origin
  have sameHelpers := eq_of_heq helpersEq
  subst helpers
  exact ⟨rfl,native_eq candidate dummy message⟩

theorem of_witness {A : Type} {program : Program A} {position : ℕ}
    (candidate : Candidate program position world) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)
    (dummy : Digest) (entry : NativeScalarBatchVerifier.CompletedRound)
    (ctxEq : candidate.selection.ctx = ctx) (bodyEq : candidate.selection.body = body)
    (originEq : HEq candidate.selection.origin origin) (ordinal : candidate.selection.index.val = index.val)
    (helpersEq : HEq (CanonicalCandidateFixation.helpers candidate dummy) helpers)
    (inputEq : candidate.selection.family.input = entry.coefficients.phase.pending.input)
    (entryEq : (CandidateScalarPacket.reader candidate).entry = entry)
    (message : NativeScalarBatchWire.Message) (messageAt : entry.packet.messages.val[2*index.val]? = some message)
    (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration)
    (healing : ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration origin.ready.equality.transcript.profile
      (nativeTest origin helpers message) world) :
    CanonicalSumAttainableEvent.Event program position entry.coefficients.phase.pending.input index.val dummy world := by
  have linked := correspondence candidate origin helpers dummy message ctxEq bodyEq originEq helpersEq
  let packet : CanonicalSumAttainableEvent.Packet program position entry.coefficients.phase.pending.input index.val world :=
    ⟨⟨candidate,inputEq,ordinal⟩,message,by rw [entryEq,ordinal]; exact messageAt,configuration,by rw [inputEq]; exact found⟩
  refine ⟨packet,?_⟩
  change ScalarRecoveredUnboundedLaw.event candidate.selection.family.input configuration candidate.selection.origin.ready.equality.transcript.profile
    (CanonicalSumCandidate.test candidate dummy message) world
  rw [inputEq,linked.1,linked.2]
  exact healing

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedSumEvent
