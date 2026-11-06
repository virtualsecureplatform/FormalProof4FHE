module
import all FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeTranscriptExtension (Extends)
open OracleProgram (run)
open HasteBootsSamplerAncestrySmoke (child header profile seed parent worldOne worldZero worldReject)
namespace HasteBootsScalarFinishAncestrySmoke
noncomputable section

def usize (value : ℕ) : NativeUsizeMessage.Usize := ⟨value % 2^64,Nat.mod_lt _ (by decide)⟩
def zero : NativeFieldWire.GoldExtension := fun _ => usize 0
def one : NativeFieldWire.GoldExtension := ![usize 1,usize 0,usize 0]
def info : NativeScalarBatchWire.Info := ⟨usize 1,usize 1⟩
def statement : NativeScalarBatchWire.Statement := ⟨⟨[info],by decide⟩,⟨[zero],by decide⟩⟩
def message : NativeScalarBatchWire.Message := ⟨⟨[zero,zero],by decide⟩⟩
def singleProof (message : NativeScalarBatchWire.Message) : NativeScalarBatchPreflight.Proof := ⟨[⟨[message],by change 1 < 2^64; decide⟩],by change 1 < 2^64; decide⟩
def firstPacket (message : NativeScalarBatchWire.Message) : NativeScalarBatchWire.RoundPacket := ⟨usize 0,⟨[message],by change 1 < 2^64; decide⟩⟩
private theorem single_domain (message : NativeScalarBatchWire.Message)
    (fits : (NativeScalarBatchWire.roundCodec.encode (firstPacket message)).length < TranscriptFrame.lengthLimit) :
    NativeScalarTranscriptExtension.RoundDomain (singleProof message) := by
  intro round packet computed
  obtain ⟨round,bounded⟩ := round
  cases round with
  | zero =>
    have same : firstPacket message = packet := Option.some.inj computed
    rw [← same]
    exact fits
  | succ round =>
    change none = some packet at computed
    contradiction
private theorem domain : NativeScalarTranscriptExtension.RoundDomain (singleProof message) := single_domain message (by decide +kernel)
private theorem statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit := by decide +kernel

def scalar (world : World) (fuel : ℕ) := (run (NativeScalarBatchVerifier.verifyPrefix fuel child statement (singleProof message)) world).run
private theorem scalar_good (world : World) (fuel : ℕ) : NativeScalarTranscriptExtension.Preserves child (scalar world fuel).1 :=
  NativeScalarTranscriptExtension.verify child statement (singleProof message) fuel world statementFits domain

example : (scalar worldZero 8).1.state.round = 1 ∧ (scalar worldZero 8).1.completed.length = 1 := by decide +kernel
example : (match (scalar worldZero 8).1.control with | .finished claims => claims.length == 1 | _ => false) = true := by decide +kernel
example : (scalar worldZero 3).1.completed = [] := by decide +kernel
example : (match (scalar worldZero 3).1.control with | .sampling _ field => field.remaining == 1 | _ => false) = true := by decide +kernel
example : (match (scalar worldReject 4).1.control with | .sampling _ field => field.remaining == 3 && field.phase.consumed.length == 24 | _ => false) = true := by decide +kernel
example : (scalar worldReject 4).2.length = 4 := by decide +kernel
example (world : World) (fuel : ℕ) : NativeChildSeedView.HasHeader (scalar world fuel).1.state.transcript profile [] [] seed :=
  (scalar_good world fuel).1.header header
example (world : World) (fuel : ℕ) (record : NativeScalarBatchVerifier.CompletedRound) (member : record ∈ (scalar world fuel).1.completed) :
    NativeChildSeedView.HasHeader record.coefficients.phase.pending profile [] [] seed :=
  ((scalar_good world fuel).2.2 record member).1.header header
example (world : World) (fuel : ℕ) (packet : NativeScalarBatchWire.RoundPacket) (field : NativeFieldVector.State)
    (active : (scalar world fuel).1.control = .sampling packet field) :
    NativeChildSeedView.HasHeader field.phase.pending profile [] [] seed := by
  have good := (scalar_good world fuel).2.1
  rw [active] at good
  exact good.1.header header

def malformed : NativeScalarBatchPreflight.Proof := ⟨[],by decide⟩
example : (run (NativeScalarBatchVerifier.verifyPrefix 30 child statement malformed) worldZero).run.2 = [] := by decide +kernel
example : (run (NativeScalarBatchVerifier.verifyPrefix 30 child statement malformed) worldZero).run.1.state.transcript = child := rfl

def badMessage : NativeScalarBatchWire.Message := ⟨⟨[zero,one],by decide⟩⟩
def rejected := (run (NativeScalarBatchVerifier.verifyPrefix 30 child statement (singleProof badMessage)) worldZero).run
example : (match rejected.1.control with | .failed (.reject .recurrence) => true | _ => false) = true ∧ rejected.2 = [] := by decide +kernel
example : NativeChildSeedView.HasHeader rejected.1.state.transcript profile [] [] seed :=
  (NativeScalarTranscriptExtension.verify child statement (singleProof badMessage) 30 worldZero statementFits
    (single_domain badMessage (by decide +kernel))).1.header header

def binding : TypedTranscriptChild.Binding := ⟨profile,(NativeTranscript.checkpoint worldOne parent).run.1,[]⟩
def finished := (run (TypedTranscriptChild.finish (some parent) ⟨some child,some binding⟩) worldOne).run
example : (match finished.1.outcome with | .ok () => true | _ => false) = true ∧ finished.1.child.binding.isNone = true ∧ finished.2.length = 4 := by decide +kernel
example : ∃ after, finished.1.child.bytes = some after ∧ NativeChildSeedView.HasHeader after profile [] [] seed := by
  obtain ⟨after,same,extension⟩ := NativeFinishedChildAncestry.typed_finish_child worldOne (some parent) child (some binding)
  exact ⟨after,same,extension.header header⟩
example : ∃ after, finished.1.parent = some after ∧ Extends parent after :=
  NativeFinishedChildAncestry.typed_finish_parent worldOne parent ⟨some child,some binding⟩
    (by intro stored same; have equal := Option.some.inj same; subst stored; decide)
example : (run (TypedTranscriptChild.finish finished.1.parent finished.1.child) worldOne).run.2 = [] := by decide +kernel
example : (run (TypedTranscriptChild.finish (some parent) ⟨some child,none⟩) worldOne).run.1.child.bytes = some child := rfl
example : (run (TypedTranscriptChild.finish none ⟨some child,some binding⟩) worldOne).run.2 = [] := rfl

def wrongCheckpoint : TypedTranscriptChild.Binding := {binding with checkpoint := []}
def mismatched := (run (TypedTranscriptChild.finish (some parent) ⟨some child,some wrongCheckpoint⟩) worldOne).run
example : (match mismatched.1.outcome with | .error .parentMismatch => true | _ => false) = true ∧ mismatched.1.child.bytes = some child ∧ mismatched.2.length = 2 :=
  ⟨by decide +kernel,rfl,by decide +kernel⟩

def wrongProfile : TypedTranscriptChild.Binding := {binding with profile := fun _ => 7}
example : (run (TypedTranscriptChild.finish (some parent) ⟨some child,some wrongProfile⟩) worldOne).run.2 = [] := by decide +kernel
end
end HasteBootsScalarFinishAncestrySmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.bind_statement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.bind_statement

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.bind_round' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.bind_round

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.initial

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.fail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.fail

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.prepare

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.after_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.after_field

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.tick

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.execute

/-- info: 'FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension.verify

/-- info: 'FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.challenge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.challenge

/-- info: 'FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.linked_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.linked_child

/-- info: 'FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.typed_finish_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.typed_finish_child

/-- info: 'FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.typed_finish_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.typed_finish_parent

/-- info: 'FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.terminal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.terminal

/-- info: 'FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.body_bound_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.body_bound_child

/-- info: 'FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.body_bound_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry.body_bound_parent
