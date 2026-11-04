module

public import FormalProof4FHE.HasteBoots.OracleProgram

@[expose] public section

/-!
# Online programs for the native framed transcript model

Interpretation is proved equal to the previously specified native transition
model, including ordered observations. This connects those transitions to
prefix replay. It is not Rust extraction/refinement or the lookup compiler.
-/

namespace FormalProof4FHE.HasteBoots.NativeTranscriptProgram

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript FieldPhase absorb appendBytes new utf8)
open OracleProgram (Program bind run)

def query (input : Input) (count : ℕ) : Program Input :=
  .start input (.read input 0 count .pure)

def challengeBytes (state : Transcript) (label : Input) (count : ℕ) : Program (Input × Transcript) :=
  let requested := absorb state 2 label (TranscriptFrame.littleEndian 8 count)
  bind (query requested.input count) (fun output => .pure (output, absorb requested 3 label output))

def checkpoint (state : Transcript) : Program Input :=
  query (absorb state 8 (utf8 "parent checkpoint") []).input 64

def beginField (state : Transcript) (label : Input) (modulus count : ℕ) : Program FieldPhase :=
  let pending := absorb state 4 label
    (TranscriptFrame.littleEndian 16 modulus ++ TranscriptFrame.littleEndian 8 count)
  .start pending.input (.pure ⟨pending, label, []⟩)

def drawField (phase : FieldPhase) (count : ℕ) : Program (Input × FieldPhase) :=
  .read phase.pending.input phase.consumed.length count
    (fun output => .pure (output, { phase with consumed := phase.consumed ++ output }))

def receipt (consumed : Input) : Program Input :=
  bind (query (utf8 "HasteBoots consumed field bytes v1" ++ consumed) 64)
    (fun digest => .pure (TranscriptFrame.littleEndian 16 consumed.length ++ digest))

def finishField (phase : FieldPhase) : Program Transcript :=
  bind (receipt phase.consumed) (fun output => .pure (absorb phase.pending 5 phase.label output))

def forkChild (parent : Transcript) (label context : Input) : Program (Transcript × Transcript) :=
  bind (challengeBytes (absorb parent 6 label context) (utf8 "classical child seed") 64)
    (fun (seed, parent) =>
      let child := new (utf8 "HasteBoots framed SHAKE256 child v1") parent.profile
      let child := appendBytes child (utf8 "child label") label
      let child := appendBytes child (utf8 "child context") context
      let child := appendBytes child (utf8 "parent seed") seed
      .pure (parent, child))

def finishLinkedChild (parent child : Transcript) (label : Input) : Program (Transcript × Transcript) :=
  bind (challengeBytes child (utf8 "classical child finish") 64)
    (fun (fingerprint, child) => .pure (absorb parent 7 label fingerprint, child))

theorem run_query (world : World) (input : Input) (count : ℕ) :
    run (query input count) world = NativeTranscript.query world input count := rfl

theorem run_challengeBytes (world : World) (state : Transcript) (label : Input) (count : ℕ) :
    run (challengeBytes state label count) world = NativeTranscript.challengeBytes world state label count := rfl

theorem run_checkpoint (world : World) (state : Transcript) :
    run (checkpoint state) world = NativeTranscript.checkpoint world state := rfl

theorem run_beginField (world : World) (state : Transcript) (label : Input) (modulus count : ℕ) :
    run (beginField state label modulus count) world = NativeTranscript.beginField state label modulus count := rfl

theorem run_drawField (world : World) (phase : FieldPhase) (count : ℕ) :
    run (drawField phase count) world = NativeTranscript.drawField world phase count := rfl

theorem run_receipt (world : World) (consumed : Input) :
    run (receipt consumed) world = NativeTranscript.receipt world consumed := rfl

theorem run_finishField (world : World) (phase : FieldPhase) :
    run (finishField phase) world = NativeTranscript.finishField world phase := rfl

theorem run_forkChild (world : World) (parent : Transcript) (label context : Input) :
    run (forkChild parent label context) world = NativeTranscript.forkChild world parent label context := rfl

theorem run_finishLinkedChild (world : World) (parent child : Transcript) (label : Input) :
    run (finishLinkedChild parent child label) world =
      NativeTranscript.finishLinkedChild world parent child label := rfl

/-- A program-level linked-child interface. Its body is still a parameter;
the actual typed lookup protocol must be compiled into that body later. -/
def linkedChild {R : Type} (parent : Transcript) (label context : Input)
    (body : Transcript → Program (R × Transcript)) : Program (R × Transcript) :=
  bind (forkChild parent label context) (fun (parent, child) =>
    bind (body child) (fun (result, child) =>
      bind (finishLinkedChild parent child label) (fun (parent, _) => .pure (result, parent))))

theorem run_linkedChild {R : Type} (world : World) (parent : Transcript) (label context : Input)
    (body : Transcript → Program (R × Transcript)) :
    run (linkedChild parent label context body) world = (do
      let (parent, child) ← NativeTranscript.forkChild world parent label context
      let (result, child) ← run (body child) world
      let (parent, _) ← NativeTranscript.finishLinkedChild world parent child label
      pure (result, parent)) := by
  simp only [linkedChild, OracleProgram.run_bind, run_forkChild, run_finishLinkedChild, OracleProgram.run]

theorem native_fork_replay (parent : Transcript) (label context : Input) :
    ObservationReplay.Replayable (fun world => NativeTranscript.forkChild world parent label context) := by
  have same : run (forkChild parent label context) =
      (fun world => NativeTranscript.forkChild world parent label context) :=
    funext (fun world => run_forkChild world parent label context)
  rw [← same]
  exact OracleProgram.run_replay _

theorem linked_child_prefix_replay {R : Type} (fuel : ℕ) (parent : Transcript) (label context : Input)
    (body : Transcript → Program (R × Transcript)) :
    ObservationReplay.Replayable (OracleProgram.runPrefix fuel (linkedChild parent label context body)) :=
  OracleProgram.prefix_replay _ _

end FormalProof4FHE.HasteBoots.NativeTranscriptProgram
