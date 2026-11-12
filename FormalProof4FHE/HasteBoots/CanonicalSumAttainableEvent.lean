module
public import FormalProof4FHE.HasteBoots.CanonicalSumCandidate
@[expose] public section

/-! Attained original sum messages carry a degree-one canonical helper test.
Transport uses the same original candidate/reference fiber and global bad ledger. -/
namespace FormalProof4FHE.HasteBoots.CanonicalSumAttainableEvent
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
noncomputable section

structure Packet {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world : World) where
  classed : JobReferenceSelection.Class program position input ordinal world
  message : NativeScalarBatchWire.Message
  messageAt : (CandidateScalarPacket.reader classed.val).entry.packet.messages.val[2*classed.val.selection.index.val]? = some message
  configuration : ScalarRecoveredReplay.Configuration
  found : ScalarRecoveredReplay.recover classed.val.selection.family.input = some configuration

def occurs {A : Type} {program : Program A} {position : ℕ} {input : Input} {ordinal : ℕ} {world : World}
    (packet : Packet program position input ordinal world) (dummy : Digest) (target : World) : Prop :=
  ScalarRecoveredUnboundedLaw.event packet.classed.val.selection.family.input packet.configuration
    packet.classed.val.selection.origin.ready.equality.transcript.profile
    (CanonicalSumCandidate.test packet.classed.val dummy packet.message) target

def Event {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (dummy : Digest) (world : World) : Prop :=
  ∃ packet : Packet program position input ordinal world, occurs packet dummy world

theorem transport {A : Type} {program : Program A} {position : ℕ} {input : Input} {ordinal : ℕ} {world other : World}
    (left : Packet program position input ordinal world) (right : Packet program position input ordinal other)
    (dummy : Digest)
    (fixed : CanonicalCandidateFixation.Fixed left.classed.val right.classed.val dummy) (target : World) :
    occurs left dummy target ↔ occurs right dummy target := by
  have inputEq := left.classed.property.1.trans right.classed.property.1.symm
  have ordinalEq := left.classed.property.2.trans right.classed.property.2.symm
  have configuration := CandidateScalarPacket.same_recovery left.classed.val right.classed.val inputEq
    left.configuration right.configuration left.found right.found
  unfold occurs
  rw [inputEq,configuration,CandidateScalarPacket.profile left.classed.val right.classed.val inputEq,
    CanonicalSumCandidate.test_fixed left.classed.val right.classed.val dummy inputEq ordinalEq fixed
      left.message right.message left.messageAt right.messageAt]

theorem kernel_bound {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (packet : Packet program position input ordinal world) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | occurs packet dummy other} ≤
      (1 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  CanonicalSumCandidate.bound program position world packet.classed.val dummy
    packet.classed.val.selection.origin.ready.equality.transcript.profile packet.configuration packet.found packet.message


end
end FormalProof4FHE.HasteBoots.CanonicalSumAttainableEvent
