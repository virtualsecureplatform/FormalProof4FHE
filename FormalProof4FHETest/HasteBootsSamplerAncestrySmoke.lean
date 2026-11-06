module
import all FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends StateExtends StatusExtends)
open OracleProgram (run)
namespace HasteBootsSamplerAncestrySmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

def worldOne : World := fun _ => 1
def worldZero : World := fun _ => 0
def worldReject : World := fun _ => 255
def profile : Digest := fun _ => 0
def seed : Digest := fun _ => 1
def parent := NativeTranscript.new [] profile
def child := (NativeTranscript.forkChild worldOne parent [] []).run.1.2
private theorem header : NativeChildSeedView.HasHeader child profile [] [] seed :=
  NativeChildSeedView.forkChild_header worldOne parent [] [] (by decide) (by decide)
def requested (world : World) (count fuel : ℕ) := (run (NativeFieldVector.request 17 fuel child [] count) world).run
private theorem request_good (world : World) (count fuel : ℕ) : StatusExtends child (requested world count fuel).1 :=
  NativeTranscriptExtension.request_status 17 fuel child [] count world (by decide)

example : (NativeFieldVector.stateOf (requested worldReject 1 7).1).remaining = 1 := by decide +kernel
example : (NativeFieldVector.stateOf (requested worldReject 1 7).1).phase.consumed.length = 7 := by decide +kernel
example : (requested worldReject 1 7).2.length = 8 := by decide +kernel
example : NativeChildSeedView.quote (NativeFieldVector.stateOf (requested worldReject 1 7).1).phase.pending.input = some seed := by
  have same := NativeTranscriptExtension.execute_fields 17 7
    (NativeFieldVector.initial (NativeTranscript.beginField child [] 17 1).run.1 1) worldReject
  simp only [requested,NativeFieldVector.run_request,NativeFieldVector.driveExecute,NativeFieldVector.finish_state]
  rw [same.1]
  exact header.beginField [] 17 1 (by decide)
def resumed := (run (NativeFieldVector.resume 17 3 (requested worldReject 1 7).1) worldReject).run
example : (NativeFieldVector.stateOf resumed.1).phase.consumed.length = 10 := by decide +kernel
example : resumed.2.length = 3 := by decide +kernel
example : StatusExtends child resumed.1 :=
  NativeTranscriptExtension.resume_status child 17 3 _ worldReject (request_good worldReject 1 7)
example : (requested worldOne 0 0).2.length = 3 := by decide +kernel
example : (run (NativeFieldVector.resume 17 100 (requested worldOne 0 0).1) worldOne).run = ((requested worldOne 0 0).1,[]) := rfl
example : StatusExtends child (run (TypedFieldRequest.extension 17 1 1 2 child .scalar [] 1) worldOne).run.1 :=
  NativeTranscriptExtension.typed_request_status 17 1 1 2 child .scalar [] 1 worldOne (by decide) (by decide +kernel)

def roots : List Digest := [fun _ => 7,fun _ => 8]
theorem rootsFits : roots.length < 2^64 := by decide
private theorem payloadFits : (NativeRootMessage.encode roots rootsFits).length < TranscriptFrame.lengthLimit := by decide +kernel
def bound := NativeLookupEquality.bindRoots child roots rootsFits
private theorem bound_header : NativeChildSeedView.HasHeader bound profile [] [] seed :=
  (NativeLookupTranscriptExtension.bind_roots child roots rootsFits payloadFits).header header
def basis : Module.Basis (Fin 1) (ZMod 17) (ZMod 17) := Module.Basis.singleton (Fin 1) (ZMod 17)
def equality := (run (NativeLookupEquality.request basis 1 2 10 child roots rootsFits) worldOne).run
private theorem equality_good : NativeLookupTranscriptExtension.Equality bound equality.1 :=
  NativeLookupTranscriptExtension.equality_request basis 1 2 10 child roots rootsFits worldOne (by decide +kernel)
example : equality.1.remaining = 0 ∧ equality.1.active = none ∧ equality.1.draws.length = 2 := by decide +kernel
example : NativeChildSeedView.HasHeader equality.1.transcript profile [] [] seed := equality_good.1.header bound_header
example (draw : NativeLookupEquality.Draw 2 (ZMod 17)) (member : draw ∈ equality.1.draws) :
    NativeChildSeedView.quote draw.coefficients.phase.pending.input = some seed :=
  ((equality_good.2.2 draw member).1.header bound_header).quote
private theorem bound_roots : (fun _ => (7 : InputIndexedOracle.Byte)) ∈ NativeParentLedger.roots bound.input := by decide +kernel
example (draw : NativeLookupEquality.Draw 2 (ZMod 17)) (member : draw ∈ equality.1.draws) :
    (fun _ => (7 : InputIndexedOracle.Byte)) ∈ NativeParentLedger.roots draw.coefficients.phase.pending.input := by
  obtain ⟨suffix,valid,bytes⟩ := bound_header
  have decoded : TranscriptFrame.decodeAll bound.input = some (NativeChildSeedView.seededFrames profile [] [] seed ++ suffix) := by
    rw [bytes]
    exact TranscriptFrame.decodeAll_encodeMany _ valid
  exact ((equality_good.2.2 draw member).1.roots _ decoded).subset bound_roots

def selection := (NativeLookupChallenge.execute basis 1 4 [[0]] 10
  (NativeLookupChallenge.initialExecute (K := ZMod 17) 17 1 1 child).1 worldZero).1
example : selection.rejected = 9 ∧ selection.draws.length = 10 := by decide +kernel
private theorem selection_good : NativeLookupTranscriptExtension.Selection child selection :=
  NativeLookupTranscriptExtension.selection_execute child basis 1 4 10 [[0]] _ worldZero (by decide +kernel)
    (NativeLookupTranscriptExtension.selection_initial child child (Extends.refl child) 17 1 1 (by decide +kernel))
example (draw : NativeLookupChallenge.Draw (ZMod 17)) (member : draw ∈ selection.draws) :
    NativeChildSeedView.HasHeader draw.coefficients.phase.pending profile [] [] seed :=
  (selection_good.2 draw member).1.header header

def req : NativeLookupBatch.Request 17 := ⟨4,[[0]],1⟩
def actions := NativeLookupBatch.schedule (count := 2) (by decide) (fun _ => req)
def batch := (NativeLookupBatch.execute basis 1 30 (NativeLookupBatch.initial actions child) worldOne).1
private theorem batch_good : NativeLookupTranscriptExtension.Batch child batch :=
  NativeLookupTranscriptExtension.batch_execute child basis 1 30 _ worldOne (by decide +kernel)
    (NativeLookupTranscriptExtension.batch_initial child actions)
example : batch.completed.length = 2 := by decide +kernel
example : (match batch.control with | .finished _ => true | _ => false) = true := by decide +kernel
example (completed : NativeLookupBatch.Completed 17 (ZMod 17)) (member : completed ∈ batch.completed)
    (draw : NativeLookupChallenge.Draw (ZMod 17)) (drawn : draw ∈ completed.selection.draws) :
    NativeChildSeedView.HasHeader draw.coefficients.phase.pending profile [] [] seed :=
  ((batch_good.2 completed member).2 draw drawn).1.header header

end
end HasteBootsSamplerAncestrySmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.refl

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.trans

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.absorb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.absorb

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.header

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.beginField' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.beginField

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.finishField' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.finishField

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.execute_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.execute_fields

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.execute_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.execute_state

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.finish_status' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.finish_status

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.drive_status' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.drive_status

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.resume_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.resume_status

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.request_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.request_status

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.extension_prepare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.extension_prepare

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.typed_prepare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.typed_prepare

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.scalar_begin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.scalar_begin

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.vector_begin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.vector_begin

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.StateExtends.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.StateExtends.trans

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.StatusExtends.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.StatusExtends.trans

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.typed_request_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.typed_request_status

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.frames

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptExtension.Extends.roots

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.selection_initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.selection_initial

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.selection_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.selection_tick

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.selection_execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.selection_execute

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.batch_initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.batch_initial

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.after_sample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.after_sample

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.batch_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.batch_tick

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.batch_execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.batch_execute

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.bind_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.bind_roots

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.equality_initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.equality_initial

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.equality_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.equality_tick

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.equality_execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.equality_execute

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.equality_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.equality_request

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.ready_origins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.ready_origins

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.ready_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.ready_extends

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.ready_draw_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.ready_draw_header

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.launch_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.launch_header

/-- info: 'FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.launch_draw_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension.launch_draw_header
