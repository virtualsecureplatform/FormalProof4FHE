module
public import FormalProof4FHE.HasteBoots.CanonicalCandidateTables
@[expose] public section

/-! Jointly fixed native families and factors identify the entire healing
test for each native prior. The info and message come from the original odd
identity slot of the input-bound statement and completed round packet. -/
namespace FormalProof4FHE.HasteBoots.CanonicalCandidateScalarTest
open InputIndexedOracle (World)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open NativeFieldWire (goldExtensionValue)
open JobReferenceCandidate (Candidate)
open CanonicalCandidateFixation (Fixed)
open CanonicalCandidateTables (partialTables fullTables)
noncomputable section

abbrev info {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :=
  LookupScalarGrammar.identityInfo candidate.selection.origin.geometry.geometry.1
    (candidate.selection.origin.ready.jobs.get candidate.selection.index).tag.request

abbrev dimension {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :=
  NativeScalarQueryShape.laneBits (3+candidate.selection.origin.padding)+candidate.selection.body.sourceVariables

abbrev partialTest {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (message : NativeScalarBatchWire.Message) :=
  ScalarSourceChallengeBound.test (info candidate) message ExtensionLookupIdentity.partialArity
    (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (candidate.selection.origin.ready.jobs.get candidate.selection.index).output.r))
    ExtensionLookupIdentity.partialIndices (dimension candidate) (partialTables candidate dummy)

abbrev fullTest {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (message : NativeScalarBatchWire.Message) :=
  ScalarSourceChallengeBound.test (info candidate) message ExtensionLookupIdentity.fullArity
    ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices (dimension candidate) (fullTables candidate dummy)

theorem same_message {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.selection.family.input = right.selection.family.input)
    (ordinal : left.selection.index.val = right.selection.index.val)
    (lm rm : NativeScalarBatchWire.Message)
    (leftAt : (CandidateScalarPacket.reader left).entry.packet.messages.val[2*left.selection.index.val+1]? = some lm)
    (rightAt : (CandidateScalarPacket.reader right).entry.packet.messages.val[2*right.selection.index.val+1]? = some rm) : lm = rm := by
  exact Option.some.inj (leftAt.symm.trans ((CandidateScalarPacket.message left right input ordinal).trans rightAt))

theorem partial_test {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.selection.family.input = right.selection.family.input)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy)
    (lm rm : NativeScalarBatchWire.Message)
    (leftAt : (CandidateScalarPacket.reader left).entry.packet.messages.val[2*left.selection.index.val+1]? = some lm)
    (rightAt : (CandidateScalarPacket.reader right).entry.packet.messages.val[2*right.selection.index.val+1]? = some rm) :
    partialTest left dummy lm = partialTest right dummy rm := by
  have metadata := CandidateScalarPacket.same_identity_info left right input ordinal
  have message := same_message left right input ordinal lm rm leftAt rightAt
  funext prior value
  unfold partialTest ScalarSourceChallengeBound.test ScalarSourceChallengeBound.Eligible ScalarSourceChallengeBound.correct
  rw [show info left = info right from metadata,message,
    CanonicalCandidateTables.partial_honest left right dummy ordinal fixed prior.2.1]

theorem full_test {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.selection.family.input = right.selection.family.input)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy)
    (lm rm : NativeScalarBatchWire.Message)
    (leftAt : (CandidateScalarPacket.reader left).entry.packet.messages.val[2*left.selection.index.val+1]? = some lm)
    (rightAt : (CandidateScalarPacket.reader right).entry.packet.messages.val[2*right.selection.index.val+1]? = some rm) :
    fullTest left dummy lm = fullTest right dummy rm := by
  have metadata := CandidateScalarPacket.same_identity_info left right input ordinal
  have message := same_message left right input ordinal lm rm leftAt rightAt
  funext prior value
  unfold fullTest ScalarSourceChallengeBound.test ScalarSourceChallengeBound.Eligible ScalarSourceChallengeBound.correct
  rw [show info left = info right from metadata,message,
    CanonicalCandidateTables.full_honest left right dummy ordinal fixed prior.2.1]


/-- The actual native trusted profiles agree by their canonical child headers. -/
theorem partial_event {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.selection.family.input = right.selection.family.input)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy)
    (lm rm : NativeScalarBatchWire.Message)
    (leftAt : (CandidateScalarPacket.reader left).entry.packet.messages.val[2*left.selection.index.val+1]? = some lm)
    (rightAt : (CandidateScalarPacket.reader right).entry.packet.messages.val[2*right.selection.index.val+1]? = some rm)
    (configuration : ScalarRecoveredReplay.Configuration) (target : World) :
    ScalarRecoveredUnboundedLaw.event left.selection.family.input configuration left.selection.origin.ready.equality.transcript.profile (partialTest left dummy lm) target ↔
    ScalarRecoveredUnboundedLaw.event right.selection.family.input configuration right.selection.origin.ready.equality.transcript.profile (partialTest right dummy rm) target := by
  rw [input,CandidateScalarPacket.profile left right input,partial_test left right dummy input ordinal fixed lm rm leftAt rightAt]

theorem full_event {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.selection.family.input = right.selection.family.input)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy)
    (lm rm : NativeScalarBatchWire.Message)
    (leftAt : (CandidateScalarPacket.reader left).entry.packet.messages.val[2*left.selection.index.val+1]? = some lm)
    (rightAt : (CandidateScalarPacket.reader right).entry.packet.messages.val[2*right.selection.index.val+1]? = some rm)
    (configuration : ScalarRecoveredReplay.Configuration) (target : World) :
    ScalarRecoveredUnboundedLaw.event left.selection.family.input configuration left.selection.origin.ready.equality.transcript.profile (fullTest left dummy lm) target ↔
    ScalarRecoveredUnboundedLaw.event right.selection.family.input configuration right.selection.origin.ready.equality.transcript.profile (fullTest right dummy rm) target := by
  rw [input,CandidateScalarPacket.profile left right input,full_test left right dummy input ordinal fixed lm rm leftAt rightAt]

open MeasureTheory ProbabilityTheory

theorem partial_bound {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy profile : Digest)
    (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover candidate.selection.family.input = some configuration)
    (message : NativeScalarBatchWire.Message) :
    (InputIndexedOracle.law[|{other | (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run}])
      {other | ScalarRecoveredUnboundedLaw.event candidate.selection.family.input configuration profile
        (partialTest candidate dummy message) other} ≤
          ((info candidate).maxMultiplicands.val : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  RefinedScalarSourceKernel.source_bound program position world candidate dummy profile configuration found
    (info candidate) message _ _ _ _ (partialTables candidate dummy)

theorem full_bound {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy profile : Digest)
    (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover candidate.selection.family.input = some configuration)
    (message : NativeScalarBatchWire.Message) :
    (InputIndexedOracle.law[|{other | (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run}])
      {other | ScalarRecoveredUnboundedLaw.event candidate.selection.family.input configuration profile
        (fullTest candidate dummy message) other} ≤
          ((info candidate).maxMultiplicands.val : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  RefinedScalarSourceKernel.source_bound program position world candidate dummy profile configuration found
    (info candidate) message _ _ _ _ (fullTables candidate dummy)

end
end FormalProof4FHE.HasteBoots.CanonicalCandidateScalarTest
