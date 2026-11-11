module
public import FormalProof4FHE.HasteBoots.CandidateIdentityTest
@[expose] public section

/-! Native identity-healing witnesses on one literal input/original job
class admit a conditional bound. The attained reference retains the actual
message and recovered replay. Empty good classes retain their bad mass. -/
namespace FormalProof4FHE.HasteBoots.AttainableIdentityEvent
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open JobReferenceFixation (Good)
open JobReferenceSelection (Class Bad)
open MeasureTheory ProbabilityTheory
noncomputable section

structure Packet {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world : World) where
  classed : Class program position input ordinal world
  message : NativeScalarBatchWire.Message
  messageAt : (CandidateScalarPacket.reader classed.val).entry.packet.messages.val[2*classed.val.selection.index.val+1]? = some message
  configuration : ScalarRecoveredReplay.Configuration
  found : ScalarRecoveredReplay.recover classed.val.selection.family.input = some configuration

def occurs {A : Type} {program : Program A} {position : ℕ} {input : Input} {ordinal : ℕ} {world : World}
    (packet : Packet program position input ordinal world) (dummy : Digest) (radius : ℕ) (target : World) : Prop :=
  ScalarRecoveredUnboundedLaw.event packet.classed.val.selection.family.input packet.configuration
    packet.classed.val.selection.origin.ready.equality.transcript.profile
    (CandidateIdentityTest.test packet.classed.val dummy radius packet.message) target

def Event {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (dummy : Digest) (radius : ℕ) (world : World) : Prop :=
  ∃ packet : Packet program position input ordinal world, occurs packet dummy radius world

theorem transport {A : Type} {program : Program A} {position : ℕ} {input : Input} {ordinal : ℕ} {world other : World}
    (left : Packet program position input ordinal world) (right : Packet program position input ordinal other)
    (dummy : Digest) (radius : ℕ)
    (fixed : JobReferenceFixation.Fixed left.classed.val right.classed.val dummy radius) (target : World) :
    occurs left dummy radius target ↔ occurs right dummy radius target := by
  have inputEq := left.classed.property.1.trans right.classed.property.1.symm
  have ordinalEq := left.classed.property.2.trans right.classed.property.2.symm
  have configuration := CandidateScalarPacket.same_recovery left.classed.val right.classed.val inputEq
    left.configuration right.configuration left.found right.found
  unfold occurs
  rw [inputEq,configuration,CandidateScalarPacket.profile left.classed.val right.classed.val inputEq,
    CandidateIdentityTest.test_eq left.classed.val right.classed.val dummy radius inputEq ordinalEq fixed
      left.message right.message left.messageAt right.messageAt]

theorem kernel_bound {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (packet : Packet program position input ordinal world) (dummy : Digest) (radius : ℕ) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | occurs packet dummy radius other} ≤
      (4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  CandidateIdentityTest.bound program position world packet.classed.val dummy
    packet.classed.val.selection.origin.ready.equality.transcript.profile radius packet.configuration packet.found packet.message

/-- This closes the reference-witness, fixed-test coverage and kernel
obligations for the candidate-level event. No successful-class denominator
or independent reference-selection charge occurs. -/
theorem covered_conditional_le {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (dummy : Digest) (radius : ℕ) (event : Set World)
    (witness : ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event →
      ¬Bad program position dummy other → Event program position input ordinal dummy radius other) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Bad program position dummy other} +
      (4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  let region := {other | (ParentFactorFiber.extend (runPrefix position program) other).run =
    (ParentFactorFiber.extend (runPrefix position program) world).run}
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  have choice := AttainableReferenceBound.choose_or_cover region
    event {other | Bad program position dummy other}
    (Packet program position input ordinal) (fun reference _ => Good program position reference dummy)
    (fun other fiber occurred safe => let ⟨packet,_⟩ := witness other fiber occurred safe; ⟨packet⟩)
    (fun _ _ safe _ => Classical.not_not.mp safe)
  rcases choice with ⟨reference,same,packet,good⟩ | allBad
  · have included := FactorPosteriorMismatch.conditional_mono replay world
      (fun other => other ∈ event)
      (fun other => Bad program position dummy other ∨ occurs packet dummy radius other) (by
        intro other fiber occurred
        by_cases bad : Bad program position dummy other
        · exact Or.inl bad
        · obtain ⟨otherPacket,healing⟩ := witness other fiber occurred bad
          have fixed := JobReferenceSelection.class_fixed program position input ordinal world reference other
            packet.classed otherPacket.classed same fiber dummy radius good bad
          exact Or.inr ((transport packet otherPacket dummy radius fixed other).mpr healing))
    have bounded := kernel_bound program position input ordinal reference packet dummy radius
    have fiberEq : {other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) reference).run} = region := by
      ext other
      rw [same]
    rw [fiberEq] at bounded
    exact included.trans ((measure_union_le _ _).trans (add_le_add le_rfl bounded))
  · have included := FactorPosteriorMismatch.conditional_mono replay world
      (fun other => other ∈ event) (Bad program position dummy)
      (fun other fiber occurred => allBad ⟨fiber,occurred⟩)
    exact included.trans (le_add_of_nonneg_right (by exact zero_le))


theorem conditional_le {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (dummy : Digest) (radius : ℕ) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Event program position input ordinal dummy radius other} ≤
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Bad program position dummy other} +
      (4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  covered_conditional_le program position input ordinal world dummy radius _ (fun _ _ occurred _ => occurred)

/-- A measurable native event covered by these witnesses outside the existing
bad ledger has an unconditional bound at this fixed analysis position. -/
theorem covered_event_le {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (dummy : Digest) (radius : ℕ) (event : Set World) (measurable : MeasurableSet event)
    (witness : ∀ other ∈ event, ¬Bad program position dummy other → Event program position input ordinal dummy radius other) :
    law event ≤ (4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) + ReferenceBadLedger.charge program position dummy :=
  ReferenceBadLedger.event_le program position dummy event measurable _
    (fun world => covered_conditional_le program position input ordinal world dummy radius event
      (fun other _ occurred safe => witness other occurred safe))

end
end FormalProof4FHE.HasteBoots.AttainableIdentityEvent
