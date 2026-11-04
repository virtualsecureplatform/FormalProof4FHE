module

public import FormalProof4FHE.HasteBoots.NativeExtensionRequest

@[expose] public section

/-!
# Typed detached extension children and parent-lineage checks

This models the classical-state projection of `transcript.rs` detached
fork/finish wrappers. The order is raw fork, parent checkpoint, zero-count
extension identity. Finish short-circuits missing modes/profiles before
querying the checkpoint and spends the binding only on success. Checkpoint
equality is byte equality, not an assumed collision-free parent identity.
Trusted field/cache success, protocol flags and checked Rust refinement
remain separate obligations; scoped owned children are a separate API.
-/

namespace FormalProof4FHE.HasteBoots.TypedTranscriptChild

open InputIndexedOracle (Byte Input World)
open NativeTranscript (Transcript Execution utf8)
open OracleProgram (Program bind run)

structure Binding where
  profile : Fin 64 → Byte
  checkpoint : Input
  label : Input

structure Child where
  bytes : Option Transcript
  binding : Option Binding

inductive Error where
  | missingBinding
  | classicalParentRequired
  | classicalChildRequired
  | parentMismatch
  deriving DecidableEq

structure FinishResult where
  outcome : Except Error Unit
  parent : Option Transcript
  child : Child

def failure (error : Error) (parent : Option Transcript) (child : Child) : FinishResult :=
  ⟨.error error, parent, child⟩

/-- Zero coefficients finish immediately, while retaining the field's reader
start and empty-prefix receipt. No sampler-analysis budget is needed. -/
def identity (p degree w : ℕ) (child : Transcript) : Program Transcript :=
  bind (NativeTranscriptProgram.beginField (NativeExtensionRequest.prepare child degree w)
    (utf8 "typed extension identity") p 0) NativeTranscriptProgram.finishField

def identityExecute (p degree w : ℕ) (world : World) (child : Transcript) : Transcript × List NativeTranscript.Observation :=
  let phase := (NativeTranscript.beginField (NativeExtensionRequest.prepare child degree w)
    (utf8 "typed extension identity") p 0).run
  let finished := (NativeTranscript.finishField world phase.1).run
  (finished.1, phase.2 ++ finished.2)

theorem run_identity (p degree w : ℕ) (world : World) (child : Transcript) :
    (run (identity p degree w child) world).run = identityExecute p degree w world child := by
  simp only [identity, identityExecute, OracleProgram.run_bind, ObservationReplay.run_bind,
    NativeTranscriptProgram.run_beginField, NativeTranscriptProgram.run_finishField]

theorem identity_profile (p degree w : ℕ) (world : World) (child : Transcript) :
    (identityExecute p degree w world child).1.profile = child.profile := rfl

/-- The specialized identity program is exactly the zero-count extension
request, with its finished collector state erased. -/
theorem identity_request_zero (p degree w fuel : ℕ) (world : World) (child : Transcript) :
    (run (NativeExtensionRequest.request p degree w fuel child (utf8 "typed extension identity") 0) world).run =
      let phase := (NativeTranscript.beginField (NativeExtensionRequest.prepare child degree w)
        (utf8 "typed extension identity") p 0).run.1
      (.finished (NativeFieldVector.initial phase 0) (identityExecute p degree w world child).1,
        (identityExecute p degree w world child).2) := by
  rw [NativeExtensionRequest.request_zero]
  rfl

/-- Classical-parent core of the detached typed extension fork. -/
def forkCore (p degree w : ℕ) (parent : Transcript) (label context : Input) : Program (Transcript × Child) :=
  bind (NativeTranscriptProgram.forkChild parent label context) (fun (parent, child) =>
    bind (NativeTranscriptProgram.checkpoint parent) (fun checkpoint =>
      bind (identity p degree w child) (fun bytes =>
        .pure (parent, ⟨some bytes, some ⟨parent.profile, checkpoint, label⟩⟩))))

def fork (p degree w : ℕ) (parent : Option Transcript) (label context : Input) :
    Program (Except Error (Transcript × Child)) :=
  match parent with
  | none => .pure (.error .classicalParentRequired)
  | some parent => bind (forkCore p degree w parent label context) (fun result => .pure (.ok result))

def forkCoreExecute (p degree w : ℕ) (world : World) (parent : Transcript) (label context : Input) :
    (Transcript × Child) × List NativeTranscript.Observation :=
  let seeded := (NativeTranscript.forkChild world parent label context).run
  let parent := seeded.1.1
  let checkpoint := (NativeTranscript.checkpoint world parent).run
  let child := identityExecute p degree w world seeded.1.2
  ((parent, ⟨some child.1, some ⟨parent.profile, checkpoint.1, label⟩⟩), seeded.2 ++ checkpoint.2 ++ child.2)

theorem run_forkCore (p degree w : ℕ) (world : World) (parent : Transcript) (label context : Input) :
    (run (forkCore p degree w parent label context) world).run =
      forkCoreExecute p degree w world parent label context := by
  simp only [forkCore, forkCoreExecute, OracleProgram.run_bind, ObservationReplay.run_bind,
    NativeTranscriptProgram.run_forkChild, NativeTranscriptProgram.run_checkpoint, run_identity,
    OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil, List.append_assoc]

theorem run_fork (p degree w : ℕ) (world : World) (parent : Option Transcript) (label context : Input) :
    (run (fork p degree w parent label context) world).run =
      match parent with
      | none => (.error .classicalParentRequired, [])
      | some parent =>
        let result := forkCoreExecute p degree w world parent label context
        (.ok result.1, result.2) := by
  cases parent with
  | none => rfl
  | some parent =>
    simp only [fork, OracleProgram.run_bind, ObservationReplay.run_bind, run_forkCore,
      OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]

theorem fork_legacy (p degree w : ℕ) (world : World) (label context : Input) :
    (run (fork p degree w none label context) world).run = (.error .classicalParentRequired, []) := rfl

/-- Exactly the checkpoint stored by the native detached wrapper, taken
from the post-fork parent before the child identity phase. -/
theorem fork_binding (p degree w : ℕ) (world : World) (parent : Transcript) (label context : Input) :
    (forkCoreExecute p degree w world parent label context).1.2.binding =
      some ⟨(forkCoreExecute p degree w world parent label context).1.1.profile,
        (NativeTranscript.checkpoint world (forkCoreExecute p degree w world parent label context).1.1).run.1, label⟩ := rfl

theorem fork_binding_length (p degree w : ℕ) (world : World) (parent : Transcript) (label context : Input) :
    ((forkCoreExecute p degree w world parent label context).1.2.binding.map
      (fun binding => binding.checkpoint.length)) = some 64 := by
  simp only [forkCoreExecute, NativeTranscript.checkpoint, NativeTranscript.query,
    WriterT.run_mk, InputIndexedOracle.bytes_length, Option.map_some]

theorem fork_profiles (p degree w : ℕ) (world : World) (parent : Transcript) (label context : Input) :
    (forkCoreExecute p degree w world parent label context).1.1.profile = parent.profile ∧
    ((forkCoreExecute p degree w world parent label context).1.2.bytes.map Transcript.profile) = some parent.profile :=
  ⟨rfl, rfl⟩

/-- Missing/spent binding, missing modes, and profile mismatches are checked
before checkpoint evaluation. A checkpoint mismatch leaves both states intact. -/
def finish (parent : Option Transcript) (child : Child) : Program FinishResult :=
  match child.binding with
  | none => .pure (failure .missingBinding parent child)
  | some binding => match parent with
    | none => .pure (failure .classicalParentRequired parent child)
    | some parentBytes => match child.bytes with
      | none => .pure (failure .classicalChildRequired parent child)
      | some childBytes =>
        if parentBytes.profile = binding.profile then
          if childBytes.profile = binding.profile then
            bind (NativeTranscriptProgram.checkpoint parentBytes) (fun checkpoint =>
              if checkpoint = binding.checkpoint then
                bind (NativeTranscriptProgram.finishLinkedChild parentBytes childBytes binding.label)
                  (fun (parentBytes, childBytes) =>
                    .pure ⟨.ok (), some parentBytes, ⟨some childBytes, none⟩⟩)
              else .pure (failure .parentMismatch parent child))
          else .pure (failure .parentMismatch parent child)
        else .pure (failure .parentMismatch parent child)

def finishExecute (world : World) (parent : Option Transcript) (child : Child) :
    FinishResult × List NativeTranscript.Observation :=
  match child.binding with
  | none => (failure .missingBinding parent child, [])
  | some binding => match parent with
    | none => (failure .classicalParentRequired parent child, [])
    | some parentBytes => match child.bytes with
      | none => (failure .classicalChildRequired parent child, [])
      | some childBytes =>
        if parentBytes.profile = binding.profile then
          if childBytes.profile = binding.profile then
            let checkpoint := (NativeTranscript.checkpoint world parentBytes).run
            if checkpoint.1 = binding.checkpoint then
              let linked := (NativeTranscript.finishLinkedChild world parentBytes childBytes binding.label).run
              (⟨.ok (), some linked.1.1, ⟨some linked.1.2, none⟩⟩, checkpoint.2 ++ linked.2)
            else (failure .parentMismatch parent child, checkpoint.2)
          else (failure .parentMismatch parent child, [])
        else (failure .parentMismatch parent child, [])

theorem run_finish (world : World) (parent : Option Transcript) (child : Child) :
    (run (finish parent child) world).run = finishExecute world parent child := by
  rcases child with ⟨bytes, binding⟩
  cases binding with
  | none => rfl
  | some binding =>
    cases parent with
    | none => rfl
    | some parent =>
      cases bytes with
      | none => rfl
      | some bytes =>
        by_cases parentProfile : parent.profile = binding.profile
        · by_cases childProfile : bytes.profile = binding.profile
          · simp only [finish, finishExecute, parentProfile, childProfile, ite_true,
              OracleProgram.run_bind, ObservationReplay.run_bind, NativeTranscriptProgram.run_checkpoint]
            split <;> simp only [OracleProgram.run_bind, ObservationReplay.run_bind,
              NativeTranscriptProgram.run_finishLinkedChild, OracleProgram.run,
              CanonicalTranscriptSampler.run_pure, List.append_nil]
          · simp only [finish, finishExecute, parentProfile, childProfile, ite_true, ite_false,
              OracleProgram.run, CanonicalTranscriptSampler.run_pure]
        · simp only [finish, finishExecute, parentProfile, ite_false, OracleProgram.run,
            CanonicalTranscriptSampler.run_pure]

theorem identity_log_length (p degree w : ℕ) (world : World) (child : Transcript) :
    (identityExecute p degree w world child).2.length = 3 := rfl

theorem fork_log_length (p degree w : ℕ) (world : World) (parent : Transcript) (label context : Input) :
    (forkCoreExecute p degree w world parent label context).2.length = 7 := rfl

theorem missing_binding (world : World) (parent : Option Transcript) (child : Child)
    (missing : child.binding = none) :
    finishExecute world parent child = (failure .missingBinding parent child, []) := by
  simp only [finishExecute, missing]

theorem missing_parent (world : World) (child : Child) (binding : Binding)
    (bound : child.binding = some binding) :
    finishExecute world none child = (failure .classicalParentRequired none child, []) := by
  simp only [finishExecute, bound]

theorem missing_child (world : World) (parent : Transcript) (binding : Binding) :
    finishExecute world (some parent) ⟨none, some binding⟩ =
      (failure .classicalChildRequired (some parent) ⟨none, some binding⟩, []) := rfl

theorem parent_profile_rejected (world : World) (parent bytes : Transcript) (binding : Binding)
    (mismatch : parent.profile ≠ binding.profile) :
    finishExecute world (some parent) ⟨some bytes, some binding⟩ =
      (failure .parentMismatch (some parent) ⟨some bytes, some binding⟩, []) := by
  simp only [finishExecute, mismatch, ite_false]

theorem child_profile_rejected (world : World) (parent bytes : Transcript) (binding : Binding)
    (same : parent.profile = binding.profile) (mismatch : bytes.profile ≠ binding.profile) :
    finishExecute world (some parent) ⟨some bytes, some binding⟩ =
      (failure .parentMismatch (some parent) ⟨some bytes, some binding⟩, []) := by
  simp only [finishExecute, same, mismatch, ite_true, ite_false]

/-- Only the checkpoint's actual start/output are observed on this mismatch;
no finish fingerprint is queried and both input states are retained. -/
theorem checkpoint_rejected (world : World) (parent bytes : Transcript) (binding : Binding)
    (parentProfile : parent.profile = binding.profile) (childProfile : bytes.profile = binding.profile)
    (mismatch : (NativeTranscript.checkpoint world parent).run.1 ≠ binding.checkpoint) :
    finishExecute world (some parent) ⟨some bytes, some binding⟩ =
      (failure .parentMismatch (some parent) ⟨some bytes, some binding⟩,
        (NativeTranscript.checkpoint world parent).run.2) := by
  simp only [finishExecute, parentProfile, childProfile, mismatch, ite_true, ite_false]

/-- The wrapper checks profiles and checkpoint bytes, without assuming those
bytes uniquely determine a parent state. -/
theorem finish_accepts_iff (world : World) (parent bytes : Transcript) (binding : Binding) :
    (finishExecute world (some parent) ⟨some bytes, some binding⟩).1.outcome = .ok () ↔
      parent.profile = binding.profile ∧ bytes.profile = binding.profile ∧
      (NativeTranscript.checkpoint world parent).run.1 = binding.checkpoint := by
  simp only [finishExecute]
  split_ifs <;> simp_all [failure]

/-- On the accepting path, the log includes both checkpoint and fingerprint
queries. A completed binding is cleared only after linking the child. -/
theorem finish_success (world : World) (parent bytes : Transcript) (binding : Binding)
    (parentProfile : parent.profile = binding.profile) (childProfile : bytes.profile = binding.profile)
    (checkpoint : (NativeTranscript.checkpoint world parent).run.1 = binding.checkpoint) :
    finishExecute world (some parent) ⟨some bytes, some binding⟩ =
      let linked := (NativeTranscript.finishLinkedChild world parent bytes binding.label).run
      (⟨.ok (), some linked.1.1, ⟨some linked.1.2, none⟩⟩,
        (NativeTranscript.checkpoint world parent).run.2 ++ linked.2) := by
  simp only [finishExecute, parentProfile, childProfile, checkpoint, ite_true]

theorem finish_success_log_length (world : World) (parent bytes : Transcript) (binding : Binding)
    (parentProfile : parent.profile = binding.profile) (childProfile : bytes.profile = binding.profile)
    (checkpoint : (NativeTranscript.checkpoint world parent).run.1 = binding.checkpoint) :
    (finishExecute world (some parent) ⟨some bytes, some binding⟩).2.length = 4 := by
  rw [finish_success world parent bytes binding parentProfile childProfile checkpoint]
  rfl

/-- Exhaustive state-effect contract, including all early rejection modes. -/
theorem finish_state_cases (world : World) (parent : Option Transcript) (child : Child) :
    let result := (finishExecute world parent child).1
    (result.outcome = .ok () ∧ result.child.binding = none) ∨
      (∃ error, result.outcome = .error error ∧ result.parent = parent ∧ result.child = child) := by
  rcases child with ⟨bytes, binding⟩
  cases binding with
  | none => simp [finishExecute, failure]
  | some binding =>
    cases parent with
    | none => simp [finishExecute, failure]
    | some parent =>
      cases bytes with
      | none => simp [finishExecute, failure]
      | some bytes =>
        simp only [finishExecute]
        split_ifs <;> simp [failure]

theorem accepted_binding_spent (world : World) (parent : Option Transcript) (child : Child)
    (accepted : (finishExecute world parent child).1.outcome = .ok ()) :
    (finishExecute world parent child).1.child.binding = none := by
  rcases finish_state_cases world parent child with success | ⟨error, failed, _⟩
  · exact success.2
  · rw [accepted] at failed
    contradiction

theorem rejected_states_retained (world : World) (parent : Option Transcript) (child : Child) (error : Error)
    (rejected : (finishExecute world parent child).1.outcome = .error error) :
    (finishExecute world parent child).1.parent = parent ∧ (finishExecute world parent child).1.child = child := by
  rcases finish_state_cases world parent child with success | ⟨_, _, retained⟩
  · have wrong := success.1
    rw [rejected] at wrong
    contradiction
  · exact retained

/-- Finishing the returned spent child again emits no observations, even if
the next oracle world differs. This is per stored child, not a global clone ban. -/
theorem spent_second_finish (world nextWorld : World) (parent : Option Transcript) (child : Child)
    (accepted : (finishExecute world parent child).1.outcome = .ok ()) :
    let result := (finishExecute world parent child).1
    finishExecute nextWorld result.parent result.child = (failure .missingBinding result.parent result.child, []) := by
  exact missing_binding nextWorld _ _ (accepted_binding_spent world parent child accepted)

theorem fork_finish_accepts (p degree w : ℕ) (world : World) (parent : Transcript) (label context : Input) :
    let forked := (forkCoreExecute p degree w world parent label context).1
    (finishExecute world (some forked.1) forked.2).1.outcome = .ok () := by
  dsimp only [forkCoreExecute]
  apply (finish_accepts_iff world _ _ _).2
  exact ⟨rfl, rfl, rfl⟩

/-- Both full and partially executed wrappers obey whole-observation replay;
no checkpoint-injectivity or fresh-oracle assumption is used. -/
theorem finish_replay (parent : Option Transcript) (child : Child) :
    ObservationReplay.Replayable (run (finish parent child)) := OracleProgram.run_replay _

theorem fork_prefix_replay (p degree w fuel : ℕ) (parent : Option Transcript) (label context : Input) :
    ObservationReplay.Replayable (OracleProgram.runPrefix fuel (fork p degree w parent label context)) :=
  OracleProgram.prefix_replay _ _

theorem finish_prefix_replay (fuel : ℕ) (parent : Option Transcript) (child : Child) :
    ObservationReplay.Replayable (OracleProgram.runPrefix fuel (finish parent child)) :=
  OracleProgram.prefix_replay _ _

end FormalProof4FHE.HasteBoots.TypedTranscriptChild
